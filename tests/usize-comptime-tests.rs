// Copyright (c) 2025 Joshua Seaton
//
// Use of this source code is governed by a MIT-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/MIT

// Compile-time assertions for usize layouts with target_pointer_width cfg'd
// fields. Cross-checked for 32-bit via test.nu.

use bitfld::layout;

layout!({
    struct Mcause(usize);
    {
        #[cfg(target_pointer_width = "64")]
        let interrupt: Bit<63>;
        #[cfg(target_pointer_width = "32")]
        let interrupt: Bit<31>;
        #[cfg(target_pointer_width = "64")]
        let code: Bits<62, 0>;
        #[cfg(target_pointer_width = "32")]
        let code: Bits<30, 0>;
    }
});

#[cfg(target_pointer_width = "64")]
const _: () = {
    assert!(Mcause::INTERRUPT_BIT == 63);
    assert!(Mcause::CODE_MASK == 0x7fff_ffff_ffff_ffff);
    assert!(Mcause::CODE_SHIFT == 0);
    assert!(Mcause::NUM_FIELDS == 2);
};

#[cfg(target_pointer_width = "32")]
const _: () = {
    assert!(Mcause::INTERRUPT_BIT == 31);
    assert!(Mcause::CODE_MASK == 0x7fff_ffff);
    assert!(Mcause::CODE_SHIFT == 0);
    assert!(Mcause::NUM_FIELDS == 2);
};

const _: () = {
    assert!(Mcause::RSVD1_MASK == 0);
    assert!(Mcause::RSVD0_MASK == 0);
    assert!(Mcause::DEFAULT == 0);
};

layout!({
    struct Mstatus(usize);
    {
        #[cfg(target_pointer_width = "64")]
        let sd: Bit<63>;
        #[cfg(target_pointer_width = "32")]
        let sd: Bit<31>;
        let tsr: Bit<22>;
        let tw: Bit<21>;
        let tvm: Bit<20>;
        let mxr: Bit<19>;
        let sum: Bit<18>;
        let mprv: Bit<17>;
        let mpp: Bits<12, 11>;
        let mpie: Bit<7>;
        let mie: Bit<3>;
    }
});

#[cfg(target_pointer_width = "64")]
const _: () = assert!(Mstatus::SD_BIT == 63);
#[cfg(target_pointer_width = "32")]
const _: () = assert!(Mstatus::SD_BIT == 31);
const _: () = assert!(Mstatus::MPP_MASK == 0x3);
const _: () = assert!(Mstatus::MPP_SHIFT == 11);

#[test]
fn compile_time_test() {}
