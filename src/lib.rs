// Copyright (c) 2025 Joshua Seaton
//
// Use of this source code is governed by a MIT-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/MIT

#![no_std]

//! `bitfld` is a no-std crate for ergonomically specifying layouts of bitfields
//! over integral types. While the aim is to be general-purpose, the imagined user
//! is a systems programmer uncomfortably hunched over an architectural manual or
//! hardware spec, looking to transcribe register layouts into Rust with minimal
//! fuss.
//!
//! The heavy lifting is done by the [`layout!`] procedural macro. Care
//! is taken to generate readable and efficient code. The [`zerocopy`][zerocopy]
//! crate is further leveraged for safe and efficient transmutation between integral
//! values and custom bitfield representations.
//!
//! ## Features
//!
//! * Generation of a simple, extensible wrapper type around the given integral base
//!   type;
//! * Simple, const-friendly builder pattern for constructing layout instances;
//! * Automatic implementations of the basic, convenient traits one would expect out
//!   of a thin integral wrapper type:
//!     * [`Copy`], [`Clone`]
//!     * [`Eq`], [`PartialEq`]
//!     * [`Default`]
//!     * [`From`] over the base type
//!     * [`Deref`][`core::ops::Deref`] and [`DerefMut`][`core::ops::DerefMut`],
//!       with a target of the underlying base type
//!     * [`Debug`], [`Display`][`core::fmt::Display`],
//!       [`Binary`][`core::fmt::Binary`], [`LowerHex`][`core::fmt::LowerHex`],
//!       [`UpperHex`][`core::fmt::UpperHex`], [`Octal`][`core::fmt::Octal`]
//! * Specification of default and "reserved-as" values, with `new()` respecting
//!   reserved-as values and `default()` respecting both;
//! * Custom bitfield representation types without any boilerplate;
//! * Iteration over individual bitfield values and metadata;
//! * Associated constants around masks and shifts for use in inline assembly.
//!
//! For more detail, see [`layout!`].
//!
//! ## Example
//!
//! ```rust
//! use bitfld::{bitfield_repr, layout};
//!
//! #[bitfield_repr(u8)]
//! pub enum CustomFieldRepr {
//!     Option1 = 0xa,
//!     Option2 = 0xf,
//! }
//!
//! layout!({
//!     pub struct Example(u32);
//!     {
//!         let foo: Bits<21, 14>;
//!         let custom: Bits<13, 10, CustomFieldRepr>;
//!         let bar: Bits<9, 8> = 0b11;
//!         let baz: Bit<7>;
//!         let frob: Bits<6, 4>;
//!         let _: Bits<3, 2> = 1;
//!         let _: Bits<1, 0>;
//!     }
//! });
//!
//!
//! let example = *Example::default()
//!     .set_custom(CustomFieldRepr::Option2)
//!     .set_frob(0x7);
//! assert_eq!(example.foo(), 0);
//! assert_eq!(example.custom().unwrap(), CustomFieldRepr::Option2);
//! assert_eq!(example.bar(), 0b11);
//! assert_eq!(example.baz(), false);
//! assert_eq!(example.frob(), 0x7);
//! assert_eq!(*example & 0b1100, 0b0100);
//!
//! // Will print: `Example { custom: Option2, foo: 0x0, bar: 0x3, baz: false, frob: 0xa }`
//! println!("{example}");
//!
//! // Or iterate over all fields and and print them individually.
//! for (value, metadata) in example {
//!   println!("{}: {:x}", metadata.name, value);
//! }
//! ```
//!
//! [`bitfield_repr`] is an attribute that is syntactic sugar for deriving
//! `repr(X)` and the handful of traits expected of a custom field representation.
//!
//! ## Why another crate for bitfields?
//!
//! There are already a handful out there, so why this one too? It is the author's
//! opinion that none of those at the time of writing this offer _all_ of the above
//! features (e.g., around reserved semantics or boilerplate-free, custom field
//! representations) or the author's desired ergonomics around register modeling.
//! For example, some constrain field specification by bit width instead of by an
//! explicit bit range, which is not how registers are commonly described in
//! official references (plus, the author surely can't trust himself to do mental
//! math like that).
//!
//! [zerocopy]: https://docs.rs/zerocopy/latest/zerocopy/

use core::fmt;

/// Specifies a layout of bitfields.
///
/// # Syntax
///
/// To keep the DSL intuitive and formattable, we co-opt a few familiar Rust
/// syntax elements:
///
/// <blockquote>
///     <em>Layout</em>:
///     <br>
///     &nbsp;&nbsp;
///         <code>{</code>
///             <em>LayoutType</em>
///             <code>{</code>
///                 <em>Bitfield</em>
///                 <sup>*</sup>
///             <code>}</code>
///         <code>}</code>
///     <br>
///     <br>
///     <em>LayoutType</em>:
///     <br>
///     &nbsp;&nbsp;
///         <em>
///             <a href="https://doc.rust-lang.org/reference/attributes.html">OuterAttribute </a>
///         </em>
///         <sup>*</sup>
///     <br>
///     &nbsp;&nbsp;
///         <em>
///             <a href="https://doc.rust-lang.org/reference/visibility-and-privacy.html">Visibility </a>
///         </em>
///         <sup>?</sup>
///         <br>
///     &nbsp;&nbsp;
///         <code>struct</code>
///         <a href="https://doc.rust-lang.org/reference/identifiers.html">IDENTIFIER </a>
///         <code>(</code>
///             <em>UnsignedBaseType</em>
///         <code>)</code>
///         <code>;</code>
///     <br>
///     <br>
///     <em>Bitfield</em>:
///     <br>
///     &nbsp;&nbsp;&nbsp;&nbsp;
///         <em>NamedBitfield</em>
///         &nbsp;|&nbsp;
///         <em>ReservedBitfield</em>
///     <br>
///     <br>
///     <em>NamedBitfield</em>:
///     <br>
///     &nbsp;&nbsp;
///         <code>let</code>
///         <a href="https://doc.rust-lang.org/reference/identifiers.html">IDENTIFIER </a>
///         <code>:</code>
///         <em>BitRange</em>
///         (
///             <code>=</code>
///             <em>
///                 <a href="https://doc.rust-lang.org/reference/expressions.html">Expression </a>
///             </em>
///         )
///         <sup>?</sup>
///         <code>;</code>
///     <br>
///     <br>
///     <em>ReservedBitfield</em>:
///     <br>
///     &nbsp;&nbsp;
///         <code>let</code>
///         <code>_</code>
///         <code>:</code>
///         <em>BitRange</em>
///         (
///             <code>=</code>
///             <em>
///                 <a href="https://doc.rust-lang.org/reference/expressions.html">Expression </a>
///             </em>
///         )
///         <sup>?</sup>
///         <code>;</code>
///     <br>
///     <br>
///     <em>BitRange</em>:
///     <br>
///     &nbsp;&nbsp;&nbsp;&nbsp;
///         <code>Bit<</code>
///         <a href="https://doc.rust-lang.org/reference/tokens.html#integer-literals">INTEGER_LITERAL </a>
///         <code>></code>
///     <br>
///     &nbsp;&nbsp;|&nbsp;
///         <code>Bits<</code>
///         <a href="https://doc.rust-lang.org/reference/tokens.html#integer-literals">INTEGER_LITERAL </a>
///         <code>,</code>
///         <a href="https://doc.rust-lang.org/reference/tokens.html#integer-literals">INTEGER_LITERAL </a>
///         (
///             <code>,</code>
///             <a href="https://doc.rust-lang.org/reference/identifiers.html">IDENTIFIER </a>
///         )
///         <sup>?</sup>
///         <code>></code><br>
///     <br>
///     <em>UnsignedBaseType</em>:<br>
///     &nbsp;&nbsp;
///             <code>u8</code> |
///             <code>u16</code> |
///             <code>u32</code> |
///             <code>u64</code> |
///             <code>u128</code>
///     <br>
///     <br>
/// </blockquote>
///
/// # Guiding example
///
/// Consider the following:
/// ```rust
/// use bitfld::{bitfield_repr, layout};
///
/// #[bitfield_repr(u8)]
/// pub enum CustomFieldRepr {
///     Option1 = 0xa,
///     Option2 = 0xf,
/// }
///
/// layout!({
///     pub struct Example(u32);
///     {
///         let foo: Bits<21, 14>;
///         let custom: Bits<13, 10, CustomFieldRepr>;
///         let bar: Bits<9, 8> = 0b11;
///         let baz: Bit<7>;
///         let frob: Bits<6, 4>;
///         let _: Bits<3, 2> = 1;
///         let _: Bits<1, 0>;
///    }
/// });
/// ```
///
/// This translates to the following:
///
/// ## Layout type
///
/// The layout type is always a tuple struct wrapping an unsigned integral type,
/// giving a layout of bitfields over such an integer. The underlying integral
/// type is referred to as the "base type". In particular, `Example` defines a
/// 32-bit layout.
///
/// ## Trait implementations
///
/// The basic, convenient traits one might expect of a thinly-wrapped integral
/// type are implemented for the layout type:
/// * [`Copy`], [`Clone`]
/// * [`Eq`], [`PartialEq`]
/// * [`Default`] (see [below](#new-and-default-default-and-reserved-as-values))
/// * [`From`] over the base type
/// * [`Deref`][`core::ops::Deref`] and [`DerefMut`][`core::ops::DerefMut`],
///   with a target of the base type
/// * [`Debug`], [`Display`][`core::fmt::Display`],
///   [`Binary`][`core::fmt::Binary`], [`LowerHex`][`core::fmt::LowerHex`],
///   [`UpperHex`][`core::fmt::UpperHex`], [`Octal`][`core::fmt::Octal`]
///
/// [`IntoIterator`] is also implemented to [iterate](#iteration) over
/// individual field values and metadata.
///
/// ## Layout type attributes
///
/// Though none are given on `Example`, all attributes annotating the layout
/// type in the macro are forwarded verbatim to the definition. However, any
/// derivations that conflict with the above implemented traits will result in a
/// compilation error. If no `repr` attribute is provided (as with `Example`), a
/// default of `repr(transparent)` is given.
///
/// ## Visibility
///
/// To keep things simple and practical, only the visibility of the layout type
/// may be specified; it too is forwarded verbatim from the definition in the
/// macro. All methods are generated as public. The associated iterator type is
/// also given the same visibility as the layout type.
///
/// ## Const-ness
///
/// All methods are const where possible. This is limited only by the current
/// unavailability of const traits, the exceptions being trait methods and the
/// getters and setters of [fields with custom representations](#fields-with-custom-representations).
///
/// ## Named and reserved fields
///
/// Bitfields are defined in the block following the layout type definition, and
/// each is defined with a let statement of one of the following forms:
///
/// * `let $name: Bit<$bit> (= $default)?;`
/// * `let $name: Bits<$high, $low (, $repr)?> (= $default)?;`
/// * `let _: Bit<$bit> (= $value)?;`
/// * `let _: Bits<$high, $low> (= $value)?;`
///
/// Reserved fields naturally correspond to the wildcard identifier, and will
/// yield no accessors. The psuedo-types of `Bit<$bit>` and `Bits<$high, $low>`
/// indicate the inclusive range of bits covered by the field. Fields that span
/// a single bit are referred to as _width-1_ fields.
///
/// A width-1 field named `foo` will yield a getter and setter of that bit's
/// content of the forms
/// ```ignore
/// const pub fn foo(&self) -> bool;
///
/// const pub fn set_foo(&mut self, value: bool) -> &mut Self;
/// ```
///
/// Otherwise, a named field `foo` that does not specify a
/// [custom represention][#fields-with-custom-representations] (given by `$repr`
/// above) yields a getter and setter over its range
///
/// ```ignore
/// const pub fn foo(&self) -> MinWidth<$high, $low>;
///
/// const pub fn set_foo(&mut self, value: MinWidth<$high, $low>) -> &mut Self;
/// ```
///
/// where `MinWidth<$high, $low>` is the smallest unsigned integral type of
/// bit size at least `$high - $low + 1`.
///
/// If an expression is given on the right-hand side of a field declaration,
/// this indicates a _default_ value in the case of a named field or a
/// _reserved-as_ value in the case of a reserved value. More on that
/// [below](#new-and-default-default-and-reserved-as-values).
///
/// Note that a reserved field with no reserved-as value has no semantic meaning
/// and is purely for documentation's sake.
///
/// ## Fields with custom representations
///
/// Fields (of width > 1) can be given more structure with a _custom
/// representation_, which is a type specified as `$repr` above. The
/// corresponding getter and setter are of the forms
///
/// ```ignore
/// const fn foo(&self) -> Result<$repr, bitfld::InvalidBits<MinWidth<$high, $low>>
/// where
///     $repr: zerocopy::TryFromBytes;
///
/// const fn set_foo(&mut self, value: $repr)
/// where
///     $repr: zerocopy::IntoBytes + zerocopy::Immutable;
/// ```
///
/// Not all bit patterns are necessarily valid with a custom representation;
/// for such cases, the getter returns a [`InvalidBits`] error type wrapping the
/// invalid pattern.
///
/// A custom representation must - definitionally - satisfy the three zerocopy
/// traits above, which are leveraged for safe and efficient transmutation
/// between `MinWidth<$high, $low>` and `$repr`. They are all derivable.
///
/// Another requirement of a custom representation is that it implements
/// [`Debug`], which is used in the formatting of the layout type.
///
/// For brevity and readability, the [`bitfield_repr`] attribute may be used to
/// define a custom representation.
///
/// ## `new()` and `default()`; default and reserved-as values
///
/// Reserved-as field values reflect values that fields _must_ have, modeling
/// hardware requirements in the case of registers. Given that, `new()` will
/// yield an otherwise-zeroed base value with the reserved-as values set.
///
/// Default field values reflect desired defaults, possibly modeling reset
/// values in the case of registers. `default()` will yield an otherwise-zeroed
/// base value with _both_ the default and reserved-as values set.
///
/// ## Associated constants
///
/// In C, one would accomplish bitfield manipulation through manual masking and
/// shifting, usually with an equivalent set of `FOO_MASK` and `FOO_SHIFT`
/// preprocessor variables. Even though we have more structure at our disposal
/// in this context, it can sometimes be convenient to have these raw masks and
/// shifts on hand. One example is when building up a register value in inline
/// assembly. Accordingly, the layout type will have the associated constants of
/// `FOO_MASK: $base` and `FOO_SHIFT: usize` for each named field `foo` of
/// width > 1; for a width-1 field named `foo` only a `FOO_BIT: usize` constant
/// will be defined, representing the shift. Further, `RSVD1_MASK: $base` and
/// `RSVD0_MASK: $base` are defined, giving the mask of reserved-as bits that
/// should be set or unset, as well as `DEFAULT: $base` giving the default
/// layout value.
///
/// ## Iteration
///
/// The layout type admits iterators over field values and metadata. An iterator
/// can be accessed via `iter()`, and [`IntoIterator`] is implemented by the
/// layout type and references to it. Its item type is
/// `($base, &'static bitfld::FieldMetadata<$base>)`. See [`FieldMetadata`] for
/// more info.
///
/// Iterators and iteration are both cheap, with the associated metadata being
/// defined as a static constant.
///
pub use bitfld_macro::layout;

/// Syntax sugar for defining a layout representation that also auto-derives the
/// traits required of a custom bitfield representation.
///
/// In particular, `#[bitfield_repr(...)]` translates to
/// ```text
/// #[repr(...)]
/// #[derive(
///     Debug,
///     Eq,
///     PartialEq,
///     ::zerocopy::Immutable,
///     ::zerocopy::IntoBytes,
///     ::zerocopy::TryFromBytes,
/// )]
/// ```
pub use bitfld_macro::bitfield_repr;

/// Implemented by unsigned integral type, this trait represents a valid base
/// type for a bitfield layout.
pub trait Unsigned: fmt::Debug + private::Sealed {}
impl Unsigned for u8 {}
impl Unsigned for u16 {}
impl Unsigned for u32 {}
impl Unsigned for u64 {}
impl Unsigned for u128 {}

// Ensures that no type outside of bitfld can implement this type.
mod private {
    pub trait Sealed {}
    impl Sealed for u8 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
    impl Sealed for u128 {}
}

/// Represents an invalid bit pattern for a field with a custom representation.
///
/// This is returned as the error type for the getters of such fields.
#[derive(Debug)]
pub struct InvalidBits<Base: Unsigned>(pub Base);

/// The metadata of a (non-reserved) bitfield.
///
/// The iterator of a [`layout!`] type will have an associated item type of
/// `(Base, &'static FieldMetadata<Base>)`.
#[derive(Debug)]
pub struct FieldMetadata<Base: Unsigned> {
    pub name: &'static str,
    pub high_bit: usize,
    pub low_bit: usize,
    pub default: Base,
}

// Implemented by types defined by `layout!` and aids in the definition of
// its associated iterator type.
//
// TODO(https://github.com/rust-lang/rust/issues/60551): Make NUM_FIELDS an
// associated constant when possible.
#[doc(hidden)]
pub trait LayoutMetadata<const NUM_FIELDS: usize> {
    type Base: Unsigned;

    const FIELDS: [FieldMetadata<Self::Base>; NUM_FIELDS];
}
