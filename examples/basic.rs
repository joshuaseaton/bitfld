// Copyright (c) 2025 Joshua Seaton
//
// Use of this source code is governed by a MIT-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/MIT

use bitfld::layout;

layout!({
    pub struct Example(u64);
    {
        let _: Bits<63, 32> = 0;
        let foo: Bits<18, 11>;
        let bar: Bits<10, 9> = 0b11;
        let baz: Bit<8>;
        let frob: Bits<7, 4>;
        let _: Bits<3, 2> = 1;
        let _: Bits<1, 0>;
    }
});

fn main() {
    macro_rules! print_formatted {
        ($obj:ident) => {
            let obj_name = stringify!($obj);
            println!("{obj_name}: debug: {:?}", $obj);
            println!("{obj_name}: lower hex: {:x}", $obj);
            println!("{obj_name}: upper hex: {:X}", $obj);
            println!("{obj_name}: octal: {:o}", $obj);
        };
    }

    let new = Example::new();
    let default = Example::default();
    let custom = *Example::new()
        .set_foo(0x1a)
        .set_bar(0b01)
        .set_baz(true)
        .set_frob(0xb);

    print_formatted!(new);
    print_formatted!(default);
    print_formatted!(custom);
}
