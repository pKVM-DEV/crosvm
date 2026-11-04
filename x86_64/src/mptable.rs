// Copyright 2017 The ChromiumOS Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use std::collections::BTreeSet;
use std::convert::TryFrom;
use std::mem;
use std::result;

use devices::PciAddress;
use devices::PciInterruptPin;
use remain::sorted;
use thiserror::Error;
use vm_memory::GuestAddress;
use vm_memory::GuestMemory;
use zerocopy::AsBytes;

use crate::mpspec::*;

#[sorted]
#[derive(Error, Debug)]
pub enum Error {
    /// The MP table has too little address space to be stored.
    #[error("The MP table has too little address space to be stored")]
    AddressOverflow,
    /// Failure while zeroing out the memory for the MP table.
    #[error("Failure while zeroing out the memory for the MP table")]
    Clear,
    #[error("all 256 PCI bus IDs are used; no MP bus ID remains for ISA")]
    NoFreeIsaBusId,
    /// There was too little guest memory to store the entire MP table.
    #[error("There was too little guest memory to store the MP table")]
    NotEnoughMemory,
    /// Failure to write MP bus entry.
    #[error("Failure to write MP bus entry")]
    WriteMpcBus,
    /// Failure to write MP CPU entry.
    #[error("Failure to write MP CPU entry")]
    WriteMpcCpu,
    /// Failure to write MP interrupt source entry.
    #[error("Failure to write MP interrupt source entry")]
    WriteMpcIntsrc,
    /// Failure to write MP ioapic entry.
    #[error("Failure to write MP ioapic entry")]
    WriteMpcIoapic,
    /// Failure to write MP local interrupt source entry.
    #[error("Failure to write MP local interrupt source entry")]
    WriteMpcLintsrc,
    /// Failure to write MP table header.
    #[error("Failure to write MP table header")]
    WriteMpcTable,
    /// Failure to write the MP floating pointer.
    #[error("Failure to write the MP floating pointer")]
    WriteMpfIntel,
}

pub type Result<T> = result::Result<T, Error>;

// Most of these variables are sourced from the Intel MP Spec 1.4.
const SMP_MAGIC_IDENT: [u8; 4] = *b"_MP_";
const MPC_SIGNATURE: [u8; 4] = *b"PCMP";
const MPC_SPEC: i8 = 4;
const MPC_OEM: [u8; 8] = *b"CROSVM  ";
const MPC_PRODUCT_ID: [u8; 12] = *b"000000000000";
const BUS_TYPE_ISA: [u8; 6] = *b"ISA   ";
const BUS_TYPE_PCI: [u8; 6] = *b"PCI   ";
// source: linux/arch/x86/include/asm/apicdef.h
pub const IO_APIC_DEFAULT_PHYS_BASE: u32 = 0xfec00000;
// source: linux/arch/x86/include/asm/apicdef.h
pub const APIC_DEFAULT_PHYS_BASE: u32 = 0xfee00000;
const APIC_VERSION: u8 = 0x14;
const CPU_STEPPING: u32 = 0x600;
const CPU_FEATURE_APIC: u32 = 0x200;
const CPU_FEATURE_FPU: u32 = 0x001;
const MPTABLE_START: u64 = 0x400 * 639; // Last 1k of Linux's 640k base RAM.
const MPTABLE_END: u64 = super::LOW_MEMORY_END; // Exclusive end of low RAM.

fn compute_checksum<T: AsBytes>(v: &T) -> u8 {
    let mut checksum: u8 = 0;
    for i in v.as_bytes() {
        checksum = checksum.wrapping_add(*i);
    }
    checksum
}

fn mpf_intel_compute_checksum(v: &mpf_intel) -> u8 {
    let checksum = compute_checksum(v).wrapping_sub(v.checksum);
    (!checksum).wrapping_add(1)
}

fn compute_mp_size(
    num_cpus: u8,
    pci_bus_count: usize,
    pci_irq_count: usize,
    isa_irq_count: usize,
) -> usize {
    mem::size_of::<mpf_intel>()
        + mem::size_of::<mpc_table>()
        + mem::size_of::<mpc_cpu>() * (num_cpus as usize)
        + mem::size_of::<mpc_ioapic>()
        + mem::size_of::<mpc_bus>() * (pci_bus_count + 1)
        + mem::size_of::<mpc_intsrc>()
        + mem::size_of::<mpc_intsrc>()
            * (super::X86_64_SCI_IRQ as usize + 2 + pci_irq_count + isa_irq_count)
        + mem::size_of::<mpc_lintsrc>() * 2
}

/// Allocate an MP bus ID without changing the original max+1 fast path.
fn select_isa_bus_id(buses: &BTreeSet<u8>) -> Result<u8> {
    // Root bus zero is inserted by setup_mptable before calling this helper.
    let max_bus = *buses.iter().next_back().ok_or(Error::NoFreeIsaBusId)?;
    match max_bus.checked_add(1) {
        Some(id) => Ok(id),
        None => (0..=u8::MAX)
            .rev()
            .find(|id| !buses.contains(id))
            .ok_or(Error::NoFreeIsaBusId),
    }
}

/// Performs setup of the MP table for the given `num_cpus`.
pub fn setup_mptable(
    mem: &GuestMemory,
    num_cpus: u8,
    pci_irqs: &[(PciAddress, u32, PciInterruptPin)],
) -> Result<()> {
    // Used to keep track of the next base pointer into the MP table.
    let mut base_mp = GuestAddress(MPTABLE_START);

    // Keep the original source of bus information: PCI interrupt routes.
    // Bus zero is always reported, even when there are no PCI interrupt routes.
    let mut buses: BTreeSet<u8> = pci_irqs.iter().map(|irq| irq.0.bus).collect();
    buses.insert(0);
    // Preserve the original max+1 policy. Only scan when max is ff.
    let isa_bus_id = select_isa_bus_id(&buses)?;
    // Use the same IRQ range for sizing and emission; avoid truncation to u8.
    let starting_isa_irq_num = pci_irqs
        .iter()
        .map(|(_, irq, _)| u64::from(*irq) + 1)
        .fold(u64::from(super::X86_64_IRQ_BASE), u64::max);
    let isa_irq_count = 16u64.saturating_sub(starting_isa_irq_num) as usize;
    let mp_size = compute_mp_size(num_cpus, buses.len(), pci_irqs.len(), isa_irq_count);
    base::debug!(
        "MP table: cpus={}, pci_buses={:?}, isa_bus_id={}, start={:#x}, size={}, capacity={}",
        num_cpus,
        buses,
        isa_bus_id,
        MPTABLE_START,
        mp_size,
        MPTABLE_END - MPTABLE_START
    );

    // The checked_add here ensures the all of the following base_mp.unchecked_add's will be without
    // overflow.
    if let Some(end_mp) = base_mp.checked_add(mp_size as u64 - 1) {
        if end_mp.offset() >= MPTABLE_END || !mem.address_in_range(end_mp) {
            base::error!(
                "MP table does not fit original low-memory range: start={:#x}, size={}, end_limit={:#x}",
                MPTABLE_START, mp_size, MPTABLE_END
            );
            return Err(Error::NotEnoughMemory);
        }
    } else {
        return Err(Error::AddressOverflow);
    }

    mem.get_slice_at_addr(base_mp, mp_size)
        .map_err(|_| Error::Clear)?
        .write_bytes(0);

    {
        let size = mem::size_of::<mpf_intel>();
        let mut mpf_intel = mpf_intel::default();
        mpf_intel.signature = SMP_MAGIC_IDENT;
        mpf_intel.length = 1;
        mpf_intel.specification = 4;
        mpf_intel.physptr = (base_mp.offset() + mem::size_of::<mpf_intel>() as u64) as u32;
        mpf_intel.checksum = mpf_intel_compute_checksum(&mpf_intel);
        mem.write_obj_at_addr(mpf_intel, base_mp)
            .map_err(|_| Error::WriteMpfIntel)?;
        base_mp = base_mp.unchecked_add(size as u64);
    }

    // We set the location of the mpc_table here but we can't fill it out until we have the length
    // of the entire table later.
    let table_base = base_mp;
    base_mp = base_mp.unchecked_add(mem::size_of::<mpc_table>() as u64);

    let mut checksum: u8 = 0;
    let ioapicid = num_cpus.checked_add(1).ok_or(Error::AddressOverflow)?;

    for cpu_id in 0..num_cpus {
        let size = mem::size_of::<mpc_cpu>();
        let mpc_cpu = mpc_cpu {
            type_: MP_PROCESSOR as u8,
            apicid: cpu_id,
            apicver: APIC_VERSION,
            cpuflag: CPU_ENABLED as u8
                | if cpu_id == 0 {
                    CPU_BOOTPROCESSOR as u8
                } else {
                    0
                },
            cpufeature: CPU_STEPPING,
            featureflag: CPU_FEATURE_APIC | CPU_FEATURE_FPU,
            ..Default::default()
        };
        mem.write_obj_at_addr(mpc_cpu, base_mp)
            .map_err(|_| Error::WriteMpcCpu)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_cpu));
    }
    {
        let size = mem::size_of::<mpc_ioapic>();
        let mpc_ioapic = mpc_ioapic {
            type_: MP_IOAPIC as u8,
            apicid: ioapicid,
            apicver: APIC_VERSION,
            flags: MPC_APIC_USABLE as u8,
            apicaddr: IO_APIC_DEFAULT_PHYS_BASE,
        };
        mem.write_obj_at_addr(mpc_ioapic, base_mp)
            .map_err(|_| Error::WriteMpcIoapic)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_ioapic));
    }
    for pci_bus_id in buses {
        let size = mem::size_of::<mpc_bus>();
        let mpc_bus = mpc_bus {
            type_: MP_BUS as u8,
            busid: pci_bus_id,
            bustype: BUS_TYPE_PCI,
        };
        mem.write_obj_at_addr(mpc_bus, base_mp)
            .map_err(|_| Error::WriteMpcBus)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_bus));
    }
    {
        let size = mem::size_of::<mpc_bus>();
        let mpc_bus = mpc_bus {
            type_: MP_BUS as u8,
            busid: isa_bus_id,
            bustype: BUS_TYPE_ISA,
        };
        mem.write_obj_at_addr(mpc_bus, base_mp)
            .map_err(|_| Error::WriteMpcBus)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_bus));
    }
    {
        let size = mem::size_of::<mpc_intsrc>();
        let mpc_intsrc = mpc_intsrc {
            type_: MP_LINTSRC as u8,
            irqtype: mp_irq_source_types_mp_INT as u8,
            irqflag: MP_IRQDIR_DEFAULT as u16,
            srcbus: isa_bus_id,
            srcbusirq: 0,
            dstapic: 0,
            dstirq: 0,
        };
        mem.write_obj_at_addr(mpc_intsrc, base_mp)
            .map_err(|_| Error::WriteMpcIntsrc)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_intsrc));
    }
    let sci_irq = super::X86_64_SCI_IRQ as u8;
    // Per kvm_setup_default_irq_routing() in kernel
    for i in (0..sci_irq).chain(std::iter::once(devices::cmos::RTC_IRQ)) {
        let size = mem::size_of::<mpc_intsrc>();
        let mpc_intsrc = mpc_intsrc {
            type_: MP_INTSRC as u8,
            irqtype: mp_irq_source_types_mp_INT as u8,
            irqflag: MP_IRQDIR_DEFAULT as u16,
            srcbus: isa_bus_id,
            srcbusirq: i,
            dstapic: ioapicid,
            dstirq: i,
        };
        mem.write_obj_at_addr(mpc_intsrc, base_mp)
            .map_err(|_| Error::WriteMpcIntsrc)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_intsrc));
    }
    // Insert SCI interrupt before PCI interrupts. Set the SCI interrupt
    // to be the default trigger/polarity of PCI bus, which is level/low.
    // This setting can be changed in future if necessary.
    {
        let size = mem::size_of::<mpc_intsrc>();
        let mpc_intsrc = mpc_intsrc {
            type_: MP_INTSRC as u8,
            irqtype: mp_irq_source_types_mp_INT as u8,
            irqflag: (MP_IRQDIR_HIGH | MP_LEVEL_TRIGGER) as u16,
            srcbus: isa_bus_id,
            srcbusirq: sci_irq,
            dstapic: ioapicid,
            dstirq: sci_irq,
        };
        mem.write_obj_at_addr(mpc_intsrc, base_mp)
            .map_err(|_| Error::WriteMpcIntsrc)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_intsrc));
    }

    // Insert PCI interrupts after platform IRQs.
    for (address, irq_num, irq_pin) in pci_irqs.iter() {
        let size = mem::size_of::<mpc_intsrc>();
        let mpc_intsrc = mpc_intsrc {
            type_: MP_INTSRC as u8,
            irqtype: mp_irq_source_types_mp_INT as u8,
            irqflag: MP_IRQDIR_DEFAULT as u16,
            srcbus: address.bus,
            srcbusirq: address.dev << 2 | irq_pin.to_mask() as u8,
            dstapic: ioapicid,
            dstirq: u8::try_from(*irq_num).map_err(|_| Error::WriteMpcIntsrc)?,
        };
        mem.write_obj_at_addr(mpc_intsrc, base_mp)
            .map_err(|_| Error::WriteMpcIntsrc)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_intsrc));
    }

    // Finally insert ISA interrupts.
    for i in starting_isa_irq_num..16 {
        let size = mem::size_of::<mpc_intsrc>();
        let mpc_intsrc = mpc_intsrc {
            type_: MP_INTSRC as u8,
            irqtype: mp_irq_source_types_mp_INT as u8,
            irqflag: MP_IRQDIR_DEFAULT as u16,
            srcbus: isa_bus_id,
            srcbusirq: i as u8,
            dstapic: ioapicid,
            dstirq: i as u8,
        };
        mem.write_obj_at_addr(mpc_intsrc, base_mp)
            .map_err(|_| Error::WriteMpcIntsrc)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_intsrc));
    }
    {
        let size = mem::size_of::<mpc_lintsrc>();
        let mpc_lintsrc = mpc_lintsrc {
            type_: MP_LINTSRC as u8,
            irqtype: mp_irq_source_types_mp_ExtINT as u8,
            irqflag: MP_IRQDIR_DEFAULT as u16,
            srcbusid: isa_bus_id,
            srcbusirq: 0,
            destapic: 0,
            destapiclint: 0,
        };
        mem.write_obj_at_addr(mpc_lintsrc, base_mp)
            .map_err(|_| Error::WriteMpcLintsrc)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_lintsrc));
    }
    {
        let size = mem::size_of::<mpc_lintsrc>();
        let mpc_lintsrc = mpc_lintsrc {
            type_: MP_LINTSRC as u8,
            irqtype: mp_irq_source_types_mp_NMI as u8,
            irqflag: MP_IRQDIR_DEFAULT as u16,
            srcbusid: isa_bus_id,
            srcbusirq: 0,
            destapic: 0xFF, // Per SeaBIOS
            destapiclint: 1,
        };
        mem.write_obj_at_addr(mpc_lintsrc, base_mp)
            .map_err(|_| Error::WriteMpcLintsrc)?;
        base_mp = base_mp.unchecked_add(size as u64);
        checksum = checksum.wrapping_add(compute_checksum(&mpc_lintsrc));
    }

    // At this point we know the size of the mp_table.
    let table_end = base_mp;

    {
        let mut mpc_table = mpc_table {
            signature: MPC_SIGNATURE,
            length: table_end.offset_from(table_base) as u16,
            spec: MPC_SPEC,
            oem: MPC_OEM,
            productid: MPC_PRODUCT_ID,
            lapic: APIC_DEFAULT_PHYS_BASE,
            ..Default::default()
        };
        checksum = checksum.wrapping_add(compute_checksum(&mpc_table));
        mpc_table.checksum = (!checksum).wrapping_add(1) as i8;
        mem.write_obj_at_addr(mpc_table, table_base)
            .map_err(|_| Error::WriteMpcTable)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use base::pagesize;

    use super::*;

    fn compute_page_aligned_mp_size(num_cpus: u8) -> u64 {
        let mp_size = compute_mp_size(num_cpus, 1, 0, 7);
        let pg_size = pagesize();
        (mp_size + pg_size - (mp_size % pg_size)) as u64
    }

    fn table_entry_size(type_: u8) -> usize {
        match type_ as u32 {
            MP_PROCESSOR => mem::size_of::<mpc_cpu>(),
            MP_BUS => mem::size_of::<mpc_bus>(),
            MP_IOAPIC => mem::size_of::<mpc_ioapic>(),
            MP_INTSRC => mem::size_of::<mpc_intsrc>(),
            MP_LINTSRC => mem::size_of::<mpc_lintsrc>(),
            _ => panic!("unrecognized mpc table entry type: {}", type_),
        }
    }

    #[test]
    fn bounds_check() {
        let num_cpus = 4;
        let mem = GuestMemory::new(&[(
            GuestAddress(MPTABLE_START),
            compute_page_aligned_mp_size(num_cpus),
        )])
        .unwrap();

        setup_mptable(&mem, num_cpus, &[]).unwrap();
    }

    #[test]
    fn sparse_bus_policy_and_original_layout() {
        let mem = GuestMemory::new(&[(GuestAddress(0), 0xa0000)]).unwrap();
        for (route_buses, expected_isa) in [
            (vec![0, 0x80, 0xe5, 0xe5], 0xe6),
            (vec![0, 0x80, 0xfe, 0xff], 0xfd),
        ] {
            let irqs: Vec<_> = route_buses
                .iter()
                .map(|bus| {
                    (
                        PciAddress::new(0, u32::from(*bus), 1, 0).unwrap(),
                        10,
                        PciInterruptPin::IntA,
                    )
                })
                .collect();
            for cpus in [1, 2] {
                setup_mptable(&mem, cpus, &irqs).unwrap();
                let mpf: mpf_intel = mem.read_obj_from_addr(GuestAddress(MPTABLE_START)).unwrap();
                assert_eq!(
                    mpf.physptr as u64,
                    MPTABLE_START + mem::size_of::<mpf_intel>() as u64
                );
                assert_eq!(mpf_intel_compute_checksum(&mpf), mpf.checksum);
                let base = GuestAddress(u64::from(mpf.physptr));
                let header: mpc_table = mem.read_obj_from_addr(base).unwrap();
                let end = base.unchecked_add(u64::from(header.length));
                assert!(end.offset() <= MPTABLE_END);
                let mut bytes = vec![0; header.length as usize];
                mem.read_at_addr(&mut bytes, base).unwrap();
                assert_eq!(
                    bytes.iter().fold(0u8, |sum, byte| sum.wrapping_add(*byte)),
                    0
                );
                let mut cursor = base.unchecked_add(mem::size_of::<mpc_table>() as u64);
                let mut pci_ids = Vec::new();
                let mut isa = None;
                while cursor < end {
                    let kind: u8 = mem.read_obj_from_addr(cursor).unwrap();
                    if kind == MP_BUS as u8 {
                        let bus: mpc_bus = mem.read_obj_from_addr(cursor).unwrap();
                        if bus.bustype == BUS_TYPE_PCI {
                            pci_ids.push(bus.busid);
                        } else {
                            assert_eq!(bus.bustype, BUS_TYPE_ISA);
                            isa = Some(bus.busid);
                        }
                    } else if kind == MP_INTSRC as u8 {
                        let irq: mpc_intsrc = mem.read_obj_from_addr(cursor).unwrap();
                        assert!(irq.srcbus == expected_isa || route_buses.contains(&irq.srcbus));
                    } else if kind == MP_LINTSRC as u8 {
                        let irq: mpc_lintsrc = mem.read_obj_from_addr(cursor).unwrap();
                        assert_eq!(irq.srcbusid, expected_isa);
                    }
                    cursor = cursor.unchecked_add(table_entry_size(kind) as u64);
                }
                let expected: BTreeSet<u8> = route_buses.iter().copied().collect();
                assert_eq!(pci_ids, expected.into_iter().collect::<Vec<_>>());
                assert_eq!(isa, Some(expected_isa));
                assert_eq!(cursor, end);
                let expected_size = compute_mp_size(cpus, pci_ids.len(), irqs.len(), 5);
                assert_eq!(
                    mem::size_of::<mpf_intel>() + header.length as usize,
                    expected_size
                );
            }
        }
    }

    #[test]
    fn all_bus_ids_used_is_explicit_error() {
        let mem = GuestMemory::new(&[(GuestAddress(0), 0xa0000)]).unwrap();
        let irqs: Vec<_> = (0..=u8::MAX)
            .map(|bus| {
                (
                    PciAddress::new(0, u32::from(bus), 1, 0).unwrap(),
                    10,
                    PciInterruptPin::IntA,
                )
            })
            .collect();
        assert!(matches!(
            setup_mptable(&mem, 2, &irqs),
            Err(Error::NoFreeIsaBusId)
        ));
    }

    #[test]
    fn isa_id_uses_max_plus_one_or_highest_hole() {
        let buses: BTreeSet<u8> = [0, 0x80, 0xe5].iter().copied().collect();
        assert_eq!(select_isa_bus_id(&buses).unwrap(), 0xe6);
        for hole in [1, 127, 254, 255] {
            let buses: BTreeSet<u8> = (0..=u8::MAX).filter(|id| *id != hole).collect();
            assert_eq!(select_isa_bus_id(&buses).unwrap(), hole);
        }
    }

    #[test]
    fn oversized_table_does_not_write_guest_memory() {
        let mem = GuestMemory::new(&[(GuestAddress(0), 0xa0000)]).unwrap();
        mem.write_obj_at_addr(0xa5u8, GuestAddress(MPTABLE_START))
            .unwrap();
        let irqs: Vec<_> = (0..=254u8)
            .map(|bus| {
                (
                    PciAddress::new(0, u32::from(bus), 1, 0).unwrap(),
                    10,
                    PciInterruptPin::IntA,
                )
            })
            .collect();
        assert!(matches!(
            setup_mptable(&mem, 2, &irqs),
            Err(Error::NotEnoughMemory)
        ));
        assert_eq!(
            mem.read_obj_from_addr::<u8>(GuestAddress(MPTABLE_START))
                .unwrap(),
            0xa5
        );
    }

    #[test]
    fn bounds_check_fails() {
        let num_cpus = 255;
        let mem = GuestMemory::new(&[(GuestAddress(MPTABLE_START), 0x1000)]).unwrap();

        assert!(setup_mptable(&mem, num_cpus, &[]).is_err());
    }

    #[test]
    fn mpf_intel_checksum() {
        let num_cpus = 1;
        let mem = GuestMemory::new(&[(
            GuestAddress(MPTABLE_START),
            compute_page_aligned_mp_size(num_cpus),
        )])
        .unwrap();

        setup_mptable(&mem, num_cpus, &[]).unwrap();

        let mpf_intel = mem.read_obj_from_addr(GuestAddress(MPTABLE_START)).unwrap();

        assert_eq!(mpf_intel_compute_checksum(&mpf_intel), mpf_intel.checksum);
    }

    #[test]
    fn mpc_table_checksum() {
        let num_cpus = 4;
        let mem = GuestMemory::new(&[(
            GuestAddress(MPTABLE_START),
            compute_page_aligned_mp_size(num_cpus),
        )])
        .unwrap();

        setup_mptable(&mem, num_cpus, &[]).unwrap();

        let mpf_intel: mpf_intel = mem.read_obj_from_addr(GuestAddress(MPTABLE_START)).unwrap();
        let mpc_offset = GuestAddress(mpf_intel.physptr as u64);
        let mpc_table: mpc_table = mem.read_obj_from_addr(mpc_offset).unwrap();

        let mut buf = vec![0; mpc_table.length as usize];
        mem.read_at_addr(&mut buf[..], mpc_offset).unwrap();
        let mut sum: u8 = 0;
        for &v in &buf {
            sum = sum.wrapping_add(v);
        }

        assert_eq!(sum, 0);
    }

    #[test]
    fn cpu_entry_count() {
        const MAX_CPUS: u8 = 0xff;
        let mem = GuestMemory::new(&[(
            GuestAddress(MPTABLE_START),
            compute_page_aligned_mp_size(MAX_CPUS),
        )])
        .unwrap();

        for i in 0..MAX_CPUS {
            if compute_mp_size(i, 1, 0, 7) > (MPTABLE_END - MPTABLE_START) as usize {
                assert!(matches!(
                    setup_mptable(&mem, i, &[]),
                    Err(Error::NotEnoughMemory)
                ));
                continue;
            }
            setup_mptable(&mem, i, &[]).unwrap();

            let mpf_intel: mpf_intel = mem.read_obj_from_addr(GuestAddress(MPTABLE_START)).unwrap();
            let mpc_offset = GuestAddress(mpf_intel.physptr as u64);
            let mpc_table: mpc_table = mem.read_obj_from_addr(mpc_offset).unwrap();
            let mpc_end = mpc_offset.checked_add(mpc_table.length as u64).unwrap();

            let mut entry_offset = mpc_offset
                .checked_add(mem::size_of::<mpc_table>() as u64)
                .unwrap();
            let mut cpu_count = 0;
            while entry_offset < mpc_end {
                let entry_type: u8 = mem.read_obj_from_addr(entry_offset).unwrap();
                entry_offset = entry_offset
                    .checked_add(table_entry_size(entry_type) as u64)
                    .unwrap();
                assert!(entry_offset <= mpc_end);
                if entry_type as u32 == MP_PROCESSOR {
                    cpu_count += 1;
                }
            }
            assert_eq!(cpu_count, i);
        }
    }
}
