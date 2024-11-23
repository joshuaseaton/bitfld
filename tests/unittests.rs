// Copyright (c) 2025 Joshua Seaton
//
// Use of this source code is governed by a MIT-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/MIT

#[cfg(test)]
mod tests {
    use bitfld::{bitfield_repr, layout, FieldMetadata};

    layout!({
        struct EmptyU8(u8);
        {}
    });

    layout!({
        struct OneFieldU16(u16);
        {
            let a: Bits<15, 0>;
        }
    });

    layout!({
        struct TwoFieldsU32(u32);
        {
            let a: Bits<31, 16>;
            let b: Bits<15, 0>;
        }
    });

    layout!({
        struct ThreeFieldsU64(u64);
        {
            let a: Bits<63, 32>;
            let b: Bits<31, 16>;
            let c: Bits<15, 0>;
        }
    });

    layout!({
        struct FourFieldsU128(u128);
        {
            let a: Bits<127, 96>;
            let b: Bits<95, 64>;
            let c: Bits<63, 32>;
            let d: Bits<31, 0>;
        }
    });

    #[test]
    fn size_and_alignment() {
        assert_eq!(size_of::<EmptyU8>(), size_of::<u8>());
        assert_eq!(align_of::<EmptyU8>(), align_of::<u8>());

        assert_eq!(size_of::<OneFieldU16>(), size_of::<u16>());
        assert_eq!(align_of::<OneFieldU16>(), align_of::<u16>());

        assert_eq!(size_of::<TwoFieldsU32>(), size_of::<u32>());
        assert_eq!(align_of::<TwoFieldsU32>(), align_of::<u32>());

        assert_eq!(size_of::<ThreeFieldsU64>(), size_of::<u64>());
        assert_eq!(align_of::<ThreeFieldsU64>(), align_of::<u64>());

        assert_eq!(size_of::<FourFieldsU128>(), size_of::<u128>());
        assert_eq!(align_of::<FourFieldsU128>(), align_of::<u128>());
    }

    #[bitfield_repr(u8)]
    pub enum CustomFieldRepr {
        Option1 = 0xa,
        Option2 = 0xf,
    }

    layout!({
        pub struct Example(u64);
        {
            let u32_repr: Bits<44, 27>;
            let custom: Bits<26, 23, CustomFieldRepr>;
            let custom_with_default: Bits<22, 19, CustomFieldRepr> =
                CustomFieldRepr::Option1;
            let _: Bits<18, 11> = 0xef;
            let with_default: Bits<10, 9> = 0b11;
            let bit: Bit<8>;
            let u8_repr: Bits<7, 4>;
            let _: Bits<3, 2> = 1;
            let _: Bits<1, 0>;
        }
    });

    #[test]
    fn constants() {
        assert_eq!(Example::RSVD1_MASK, (0xef << 11) | (0b01 << 2));
        assert_eq!(Example::RSVD0_MASK, (0x10 << 11) | (0b10 << 2));

        assert_eq!(
            Example::DEFAULT,
            (0xef << 11)
                | (0b01 << 2)
                | ((CustomFieldRepr::Option1 as u64) << 19)
                | (0b11 << 9)
        );

        assert_eq!(Example::U32_REPR_MASK, 0x3ffff);
        assert_eq!(Example::U32_REPR_SHIFT, 27usize,);

        assert_eq!(Example::CUSTOM_MASK, 0xf);
        assert_eq!(Example::CUSTOM_SHIFT, 23usize);

        assert_eq!(Example::CUSTOM_WITH_DEFAULT_MASK, 0xf);
        assert_eq!(Example::CUSTOM_WITH_DEFAULT_SHIFT, 19usize);

        assert_eq!(Example::RSVD_18_11, 0xef << 11);

        assert_eq!(Example::WITH_DEFAULT_MASK, 0x3);
        assert_eq!(Example::WITH_DEFAULT_SHIFT, 9usize);

        assert_eq!(Example::BIT_BIT, 8usize);

        assert_eq!(Example::U8_REPR_MASK, 0xf);
        assert_eq!(Example::U8_REPR_SHIFT, 4usize);

        assert_eq!(Example::RSVD_3_2, 1 << 2);
    }

    // new() should return a value with only reserved-as values set.
    #[test]
    fn new() {
        assert_eq!(*Example::new(), Example::RSVD1_MASK);
    }

    // default() should return a value with only defaults and reserved-as
    // values set.
    #[test]
    fn default() {
        assert_eq!(*Example::default(), Example::DEFAULT);
    }

    #[test]
    fn from() {
        assert_eq!(
            *Example::from(0 | Example::RSVD1_MASK),
            0 | Example::RSVD1_MASK
        );
        assert_eq!(
            *Example::from(1 | Example::RSVD1_MASK),
            1 | Example::RSVD1_MASK
        );
        assert_eq!(
            *Example::from(0xffff_0000_0000_0000 | Example::RSVD1_MASK),
            0xffff_0000_0000_0000 | Example::RSVD1_MASK
        );
    }

    #[test]
    fn derefmut_does_not_respect_reserved() {
        let mut example = Example::from(Example::RSVD1_MASK);
        *example &= !Example::RSVD1_MASK;
        assert_eq!(*example, 0);
    }

    #[test]
    fn from_then_get() {
        let example = Example::from(
            0xabcd << 27
                | (CustomFieldRepr::Option1 as u64) << 23
                | (CustomFieldRepr::Option2 as u64) << 19
                | 0b10 << 9
                | 1 << 8
                | 0xc << 4
                | Example::RSVD1_MASK,
        );
        assert_eq!(example.u32_repr(), 0xabcd);
        assert_eq!(example.custom().unwrap(), CustomFieldRepr::Option1);
        assert_eq!(
            example.custom_with_default().unwrap(),
            CustomFieldRepr::Option2
        );
        assert_eq!(example.with_default(), 0b10);
        assert!(example.bit());
        assert_eq!(example.u8_repr(), 0xc);
    }

    #[test]
    fn set_then_get() {
        let example = *Example::new()
            .set_u32_repr(0xabcd)
            .set_custom(CustomFieldRepr::Option1)
            .set_custom_with_default(CustomFieldRepr::Option2)
            .set_with_default(0b10)
            .set_bit(true)
            .set_u8_repr(0xc);
        assert_eq!(example.u32_repr(), 0xabcd);
        assert_eq!(example.custom().unwrap(), CustomFieldRepr::Option1);
        assert_eq!(
            example.custom_with_default().unwrap(),
            CustomFieldRepr::Option2
        );
        assert_eq!(example.with_default(), 0b10);
        assert!(example.bit());
        assert_eq!(example.u8_repr(), 0xc);
    }

    #[test]
    fn iter() {
        type Metadata = FieldMetadata<u64>;

        let example = *Example::new()
            .set_u32_repr(0xabcd)
            .set_custom(CustomFieldRepr::Option1)
            .set_custom_with_default(CustomFieldRepr::Option2)
            .set_with_default(0b10)
            .set_bit(true)
            .set_u8_repr(0xc);

        const EXPECTED: [(u64, Metadata); 6] = [
            (
                0xabcd,
                Metadata {
                    name: "u32_repr",
                    high_bit: 44,
                    low_bit: 27,
                    default: 0,
                },
            ),
            (
                0xa,
                Metadata {
                    name: "custom",
                    high_bit: 26,
                    low_bit: 23,
                    default: 0,
                },
            ),
            (
                0xf,
                Metadata {
                    name: "custom_with_default",
                    high_bit: 22,
                    low_bit: 19,
                    default: 0xa,
                },
            ),
            (
                0b10,
                Metadata {
                    name: "with_default",
                    high_bit: 10,
                    low_bit: 9,
                    default: 0b11,
                },
            ),
            (
                0b1,
                Metadata {
                    name: "bit",
                    high_bit: 8,
                    low_bit: 8,
                    default: 0,
                },
            ),
            (
                0xc,
                Metadata {
                    name: "u8_repr",
                    high_bit: 7,
                    low_bit: 4,
                    default: 0,
                },
            ),
        ];

        let actual: Vec<(u64, &'static Metadata)> =
            example.into_iter().collect();

        assert_eq!(actual.len(), EXPECTED.len());
        for i in 0..EXPECTED.len() {
            let (expected_val, expected_metadata) = &EXPECTED[i];
            let (actual_val, actual_metadata) = &actual[i];
            assert_eq!(actual_val, expected_val, "{i}");
            assert_eq!(actual_metadata.name, expected_metadata.name, "{i}");
            assert_eq!(
                actual_metadata.high_bit, expected_metadata.high_bit,
                "{i}"
            );
            assert_eq!(
                actual_metadata.low_bit, expected_metadata.low_bit,
                "{i}"
            );
            assert_eq!(
                actual_metadata.default, expected_metadata.default,
                "{i}"
            );
        }
    }
}
