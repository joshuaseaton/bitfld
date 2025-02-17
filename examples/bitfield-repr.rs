// Copyright (c) 2025 Joshua Seaton
//
// Use of this source code is governed by a MIT-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/MIT

use bitfld::{bitfield_repr, layout};

// Options for satp.MODE.
#[bitfield_repr(u8)]
pub enum RiscvSatpMode {
    Bare = 0, // No translation or protection.
    // 1-7 are reserved for standard use.
    Sv39 = 8,
    Sv48 = 9,
    Sv57 = 10,
    Sv64 = 11,
    // 12-13 are reserved for standard use.
    // 14-15 are reserved for custom use.
}

// Models the RISC-V satp (Supervisor Address Translation and Protection)
// system register.
layout!({
    pub struct RiscvSatp(u64);
    {
        let mode: Bits<63, 60, RiscvSatpMode>; // Virtual addressing mode
        let asid: Bits<59, 44>; // Address Space IDentifier
        let ppn: Bits<43, 0>; // Physical Page Number
    }
});

fn main() {
    let satp = *RiscvSatp::new()
        .set_asid(1)
        .set_ppn(0xffff)
        .set_mode(RiscvSatpMode::Sv39);
    println!("{satp:#}");
}
