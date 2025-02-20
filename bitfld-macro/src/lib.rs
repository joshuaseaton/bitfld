// Copyright (c) 2025 Joshua Seaton
//
// Use of this source code is governed by a MIT-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/MIT#

use std::str::FromStr;

use proc_macro::TokenStream;
use proc_macro2::{Literal, Span, TokenStream as TokenStream2};
use quote::{ToTokens, format_ident, quote};
use syn::parse::{Error, Parse, ParseStream, Result};
use syn::spanned::Spanned;
use syn::{
    Expr, ExprLit, Fields, GenericArgument, Ident, ItemStruct, Lit, Pat, Path,
    PathArguments, Stmt, Type, braced, parse_macro_input, parse_quote,
};

#[proc_macro_attribute]
pub fn bitfield_repr(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr: TokenStream2 = attr.into();
    let item: TokenStream2 = item.into();
    quote! {
        #[repr(#attr)]
        #[derive(
            Debug,
            Eq,
            PartialEq,
            ::zerocopy::Immutable,
            ::zerocopy::IntoBytes,
            ::zerocopy::TryFromBytes,
        )]
        #item
    }
    .into()
}

#[proc_macro]
pub fn layout(item: TokenStream) -> TokenStream {
    parse_macro_input!(item as Bitfields)
        .to_token_stream()
        .into()
}

//
// Parsing of the bitfld type.
//

enum BaseType {
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl BaseType {
    const fn high_bit(&self) -> usize {
        match *self {
            Self::U8 => 7,
            Self::U16 => 15,
            Self::U32 => 31,
            Self::U64 => 63,
            Self::U128 => 127,
        }
    }
}

struct BaseTypeDef {
    def: Type,
    ty: BaseType,
}

impl TryFrom<Type> for BaseTypeDef {
    type Error = Error;

    fn try_from(type_def: Type) -> Result<Self> {
        const INVALID_BASE_TYPE: &str =
            "base type must be an unsigned integral type";
        let Type::Path(ref path_ty) = type_def else {
            return Err(Error::new_spanned(type_def, INVALID_BASE_TYPE));
        };
        let path = &path_ty.path;
        let ty = if path.is_ident("u8") {
            BaseType::U8
        } else if path.is_ident("u16") {
            BaseType::U16
        } else if path.is_ident("u32") {
            BaseType::U32
        } else if path.is_ident("u64") {
            BaseType::U64
        } else if path.is_ident("u128") {
            BaseType::U128
        } else {
            return Err(Error::new_spanned(path, INVALID_BASE_TYPE));
        };
        Ok(Self { def: type_def, ty })
    }
}

struct TypeDef {
    def: ItemStruct,
    base: BaseTypeDef,
}

impl Parse for TypeDef {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut strct: ItemStruct = input.parse()?;

        // Check for any redundant derives; all other derives are forwarded. If
        // no repr is specified, then we default to repr(transparent).
        let mut repr = false;
        for attr in &strct.attrs {
            if attr.path().is_ident("derive") {
                attr.parse_nested_meta(|meta| {
                    for t in &[
                        "Copy",
                        "Clone",
                        "Debug",
                        "Default",
                        "Eq",
                        "PartialEq",
                    ] {
                        if meta.path.is_ident(t) {
                            return Err(Error::new_spanned(
                                meta.path,
                                format!("layout! already derives {t}"),
                            ));
                        }
                    }
                    Ok(())
                })?;
                continue;
            }

            if attr.path().is_ident("repr") {
                repr = true;
                continue;
            }
        }
        if !repr {
            strct.attrs.push(parse_quote!(#[repr(transparent)]));
        }

        //
        let base_type = if let Fields::Unnamed(fields) = &strct.fields {
            if fields.unnamed.is_empty() {
                return Err(Error::new_spanned(
                    &fields.unnamed,
                    "no base type provided",
                ));
            }
            if fields.unnamed.len() > 1 {
                return Err(Error::new_spanned(
                    &fields.unnamed,
                    "too many tuple fields; only the base type should be provided",
                ));
            }
            BaseTypeDef::try_from(fields.unnamed.first().unwrap().ty.clone())?
        } else {
            return Err(Error::new_spanned(
                &strct.fields,
                "bitfld type must be defined as a tuple struct",
            ));
        };

        Ok(Self {
            def: strct,
            base: base_type,
        })
    }
}

//
// Parsing and binding for an individual bitfield.
//

struct Bitfield {
    span: Span,
    name: Option<Ident>,
    high_bit: usize,
    low_bit: usize,
    repr: Option<Type>,

    //
    default: Option<Box<Expr>>,

    //
    shifted_mask: TokenStream2,
}

impl Bitfield {
    fn new(
        span: Span,
        name: Option<Ident>,
        high_bit: usize,
        low_bit: usize,
        repr: Option<Type>,
        default: Option<Box<Expr>>,
    ) -> Self {
        let shifted_mask = {
            let num_ones = high_bit - low_bit + 1;
            let mut mask_str = "0x".to_string();

            // If the first hex digit is not 'f', write that out now. After that,
            // the remaining width will be a multiple of four, and the remaining
            // digits will be either f or 0.
            if num_ones % 4 != 0 {
                mask_str.push(match num_ones % 4 {
                    1 => '1',
                    2 => '3',
                    3 => '7',
                    _ => unreachable!(),
                });
            }

            let mut remaining = num_ones / 4;
            while remaining > 0 {
                if mask_str.len() > 2 && remaining % 4 == 0 {
                    mask_str.push('_');
                }
                mask_str.push('f');
                remaining -= 1;
            }
            TokenStream2::from_str(&mask_str).unwrap()
        };

        Self {
            span,
            name,
            high_bit,
            low_bit,
            repr,
            default,
            shifted_mask,
        }
    }

    const fn is_reserved(&self) -> bool {
        self.name.is_none()
    }

    const fn bit_width(&self) -> usize {
        self.high_bit - self.low_bit + 1
    }

    fn minimum_width_integral_type(&self) -> TokenStream2 {
        match self.bit_width() {
            2..=8 => quote! {u8},
            9..=16 => quote! {u16},
            17..=32 => quote! {u32},
            33..=64 => quote! {u64},
            65..=128 => quote! {u128},
            width => panic!("unexpected integral bit width: {width}"),
        }
    }

    fn getter_and_setter(&self, base: &BaseTypeDef) -> TokenStream2 {
        debug_assert!(!self.is_reserved());

        let name = self.name.as_ref().unwrap();
        let setter_name = format_ident!("set_{}", name);

        let base_type = &base.def;
        let low_bit = Literal::usize_unsuffixed(self.low_bit);
        let bit_width = self.bit_width();

        if bit_width == 1 {
            return quote! {
                #[inline]
                pub const fn #name(&self) -> bool {
                    (self.0 & (1 << #low_bit)) != 0
                }

                #[inline]
                pub const fn #setter_name(&mut self, value: bool) -> &mut Self {
                    if value {
                        self.0 |= (1 << #low_bit);
                    } else {
                        self.0 &= (1 << #low_bit);
                    }
                    self
                }
            };
        }

        let min_width = self.minimum_width_integral_type();
        let shifted_mask = &self.shifted_mask;
        let get_value =
            quote! { ((self.0 >> #low_bit) & #shifted_mask) as #min_width };
        let getter = if self.repr.is_some() {
            let repr = self.repr.as_ref().unwrap();
            quote! {
                #[inline]
                pub fn #name(&self)
                    -> ::core::result::Result<#repr, ::bitfld::InvalidBits<#min_width>>
                where
                    #repr: ::zerocopy::TryFromBytes,
                {
                    use ::zerocopy::IntoBytes;
                    use ::zerocopy::TryFromBytes;
                    let value = #get_value;
                    #repr::try_read_from_bytes(value.as_bytes())
                        .map_err(|_| ::bitfld::InvalidBits(value))
                }
            }
        } else {
            quote! {
                #[inline]
                pub const fn #name(&self) -> #min_width {
                    #get_value
                }
            }
        };

        let set_value = {
            let value_check = if bit_width >= 8 && bit_width.is_power_of_two() {
                quote! {}
            } else {
                quote! { debug_assert!((value & !#shifted_mask) == 0); }
            };
            quote! {
                #value_check
                self.0 &= !(#shifted_mask << #low_bit);
                self.0 |= ((value & #shifted_mask) as #base_type) << #low_bit;
            }
        };

        let setter = if self.repr.is_some() {
            let repr = self.repr.as_ref().unwrap();
            quote! {
                #[inline]
                pub fn #setter_name(&mut self, value: #repr) -> &mut Self
                where
                    #repr: ::zerocopy::IntoBytes + ::zerocopy::Immutable
                 {
                    use ::zerocopy::IntoBytes;
                    use ::zerocopy::FromBytes;
                    const { assert!(::core::mem::size_of::<#repr>() == ::core::mem::size_of::<#min_width>()) }
                    let value = #min_width::read_from_bytes(value.as_bytes()).unwrap();
                    #set_value
                    self
                }
            }
        } else {
            quote! {
                #[inline]
                pub const fn #setter_name(&mut self, value: #min_width) -> &mut Self {
                    #set_value
                    self
                }
            }
        };

        quote! {
            #getter
            #setter
        }
    }
}

impl Parse for Bitfield {
    fn parse(input: ParseStream) -> Result<Self> {
        const INVALID_BITFIELD_DECL_FORM: &str = "bitfield declaration should take one of the following forms:\n\
            * `let $name: Bit<$bit> (= $default)?;`\n\
            * `let $name: Bits<$high, $low (, $repr)?> (= $default)?;`\n\
            * `let _: Bit<$bit> (= $value)?;`\n\
            * `let _: Bits<$high, $low> (= $value)?;`";
        let err = |spanned: &dyn ToTokens| {
            Error::new_spanned(spanned, INVALID_BITFIELD_DECL_FORM)
        };

        let stmt = input.parse::<Stmt>()?;
        let Stmt::Local(ref local) = stmt else {
            return Err(err(&stmt));
        };
        let Pat::Type(ref pat_type) = local.pat else {
            return Err(err(&local));
        };

        let name: Option<Ident> = match *pat_type.pat {
            Pat::Ident(ref pat_ident) => {
                if pat_ident.by_ref.is_some() {
                    return Err(err(pat_ident.by_ref.as_ref().unwrap()));
                }
                if pat_ident.mutability.is_some() {
                    return Err(err(pat_ident.mutability.as_ref().unwrap()));
                }
                if pat_ident.subpat.is_some() {
                    return Err(err(&pat_ident.subpat.as_ref().unwrap().0));
                }
                Some(pat_ident.ident.clone())
            }
            Pat::Wild(_) => None,
            _ => return Err(err(&*pat_type.pat)),
        };

        let path: &Path = if let Type::Path(ref type_path) = *pat_type.ty {
            if type_path.qself.is_some() {
                return Err(err(&*pat_type.ty));
            }
            &type_path.path
        } else {
            return Err(err(&*pat_type.ty));
        };

        let get_bits_and_repr = |bits: &mut [usize]| -> Result<Option<Type>> {
            let args = &path.segments.first().unwrap().arguments;
            let args = if let PathArguments::AngleBracketed(bracketed) = args {
                &bracketed.args
            } else {
                return Err(err(&args));
            };
            if args.len() < bits.len() || args.len() > bits.len() + 1 {
                return Err(err(&args));
            }
            for (i, bit) in bits.iter_mut().enumerate() {
                let arg = args.get(i).unwrap();
                match arg {
                    GenericArgument::Const(Expr::Lit(ExprLit {
                        lit: Lit::Int(b),
                        ..
                    })) => {
                        *bit = b.base10_parse()?;
                    }
                    _ => return Err(err(&arg)),
                };
            }
            if args.len() == bits.len() + 1 {
                let arg = args.last().unwrap();
                if let GenericArgument::Type(repr) = arg {
                    Ok(Some(repr.clone()))
                } else {
                    Err(err(&arg))
                }
            } else {
                Ok(None)
            }
        };

        let type_ident = &path.segments.first().unwrap().ident;
        let (high, low, repr) = if type_ident == "Bits" {
            let mut bits = [0usize; 2];
            let repr = get_bits_and_repr(&mut bits)?;
            if bits[0] < bits[1] {
                Err(Error::new_spanned(
                    &path.segments,
                    "first high bit, then low",
                ))
            } else {
                Ok((bits[0], bits[1], repr))
            }
        } else if type_ident == "Bit" {
            let mut bit = [0usize; 1];
            let repr = get_bits_and_repr(&mut bit)?;
            Ok((bit[0], bit[0], repr))
        } else {
            Err(err(path))
        }?;

        let default_or_value = if let Some(ref init) = local.init {
            if init.diverge.is_some() {
                return Err(err(local));
            }
            Some(init.expr.clone())
        } else {
            None
        };

        if repr.is_some() {
            if name.is_none() {
                return Err(Error::new_spanned(
                    repr,
                    "custom representations are not permitted for reserved fields",
                ));
            }
            if high == low {
                return Err(Error::new_spanned(
                    repr,
                    "custom representations are not permitted for bits",
                ));
            }
        }

        Ok(Bitfield::new(
            stmt.span(),
            name,
            high,
            low,
            repr,
            default_or_value,
        ))
    }
}

struct Bitfields {
    ty: TypeDef,
    named: Vec<Bitfield>,
    reserved: Vec<Bitfield>,
}

impl Bitfields {
    fn constants(&self) -> TokenStream2 {
        let base = &self.ty.base.def;

        let mut field_constants = Vec::new();
        let mut checks = Vec::new();
        let mut default_values = vec![quote! {Self::RSVD1_MASK}];

        for field in &self.named {
            let field_name =
                field.name.as_ref().unwrap().to_string().to_uppercase();
            let low_bit = Literal::usize_unsuffixed(field.low_bit);
            let shifted_mask = &field.shifted_mask;

            if field.bit_width() == 1 {
                let bit_name = format_ident!("{field_name}_BIT");
                field_constants.push(quote! {
                    pub const #bit_name: usize = #low_bit;
                });
            } else {
                let mask_name = format_ident!("{field_name}_MASK");
                let shift_name = format_ident!("{field_name}_SHIFT");
                field_constants.push(quote! {
                    pub const #mask_name: #base = #shifted_mask;
                    pub const #shift_name: usize = #low_bit;
                });
            }

            if field.default.is_some() {
                let default = field.default.as_ref().unwrap();

                let default_name = format_ident!("{field_name}_DEFAULT");
                field_constants.push(quote! {
                    pub const #default_name: #base = ((#default) as #base) << #low_bit;
                });
                checks.push(quote! {
                    const { assert!(Self::#default_name & !(#shifted_mask << #low_bit) == 0) }
                });
                default_values.push(quote! { Self::#default_name });
            }
        }

        let mut rsvd1_values = Vec::new();
        let mut rsvd0_values = Vec::new();
        for rsvd in &self.reserved {
            let rsvd_value = rsvd.default.as_ref().unwrap();
            let low_bit = Literal::usize_unsuffixed(rsvd.low_bit);
            let shifted_mask = &rsvd.shifted_mask;
            let name = format_ident!("RSVD_{}_{}", rsvd.high_bit, rsvd.low_bit);

            field_constants.push(quote! {
                const #name: #base = (#rsvd_value as #base) << #low_bit;
            });
            checks.push(quote! {
                const { assert!(Self::#name & !(#shifted_mask << #low_bit) == 0) }
            });
            rsvd1_values.push(quote! { Self::#name });
            rsvd0_values.push(quote! {
                (!Self::#name & (#shifted_mask << #low_bit))
            });
        }

        let field_constants = field_constants.into_iter();

        let check_fn = if checks.is_empty() {
            quote! {}
        } else {
            let checks = checks.into_iter();
            quote! {
                #[forbid(overflowing_literals)]
                const fn check_defaults() -> () {
                    #(#checks)*
                }
            }
        };

        if self.reserved.is_empty() {
            rsvd1_values.push(quote! {0});
            rsvd0_values.push(quote! {0});
        }
        let rsvd1_values = rsvd1_values.into_iter();
        let rsvd0_values = rsvd0_values.into_iter();
        let default_values = default_values.into_iter();

        quote! {
            pub const RSVD1_MASK: #base = #(#rsvd1_values)|* ;
            pub const RSVD0_MASK: #base = #(#rsvd0_values)|* ;
            pub const DEFAULT: #base = #(#default_values)|* ;

            #(#field_constants)*

            #check_fn
        }
    }

    fn iter_impl(&self) -> TokenStream2 {
        let ty = &self.ty.def.ident;
        let base = &self.ty.base.def;
        let num_fields = Literal::usize_unsuffixed(self.named.len());

        let metadata = self.named.iter().map(|field| {
            let low_bit = Literal::usize_unsuffixed(field.low_bit);
            let high_bit = Literal::usize_unsuffixed(field.high_bit);
            let name = field.name.as_ref().unwrap().to_string();
            let default = if let Some(default) = &field.default {
                quote! { #default }
            } else {
                quote! { 0 }
            };
            quote! {
                ::bitfld::FieldMetadata::<#base>{
                    name: #name,
                    high_bit: #high_bit,
                    low_bit: #low_bit,
                    default: #default as #base,
                },
            }
        });

        let layout_metadata_impl = quote! {
            impl ::bitfld::LayoutMetadata<#num_fields> for #ty {
                type Base = #base;

                const FIELDS: [::bitfld::FieldMetadata::<#base>; #num_fields] = [
                    #(#metadata)*
                ];
            }
        };

        let iter_type = format_ident!("{}Iter", ty);
        let vis = &self.ty.def.vis;

        quote! {
            #layout_metadata_impl

            #[allow(dead_code)]
            #vis struct #iter_type(#base, usize);

            impl ::core::iter::Iterator for #iter_type {
                type Item = (#base, &'static ::bitfld::FieldMetadata<#base>);

                fn next(&mut self) -> Option<Self::Item> {
                    if self.1 >= #num_fields {
                        return None;
                    }
                    let metadata = &<#ty as ::bitfld::LayoutMetadata<#num_fields>>::FIELDS[self.1];
                    let shifted_mask = (1 << (metadata.high_bit - metadata.low_bit + 1)) - 1;
                    let value = (self.0 >> metadata.low_bit) & shifted_mask;
                    self.1 += 1;
                    Some((value, metadata))
                }
            }

            impl #ty {
                pub fn iter(&self) -> #iter_type {
                    #iter_type(self.0, 0)
                }
            }

            impl ::core::iter::IntoIterator for #ty {
                type Item = <#iter_type as ::core::iter::Iterator>::Item;
                type IntoIter = #iter_type;

                fn into_iter(self) -> Self::IntoIter { self.iter() }
            }

            impl<'a> ::core::iter::IntoIterator for &'a #ty {
                type Item = <#iter_type as ::core::iter::Iterator>::Item;
                type IntoIter = #iter_type;

                fn into_iter(self) -> Self::IntoIter { self.iter() }
            }
        }
    }

    fn getters_and_setters(&self) -> impl Iterator<Item = TokenStream2> + '_ {
        self.named
            .iter()
            .map(|field| field.getter_and_setter(&self.ty.base))
    }

    fn fmt_fn(&self, integral_specifier: &str) -> TokenStream2 {
        let ty_str = &self.ty.def.ident.to_string();

        let mut custom_repr_fields = self
            .named
            .iter()
            .filter(|field| field.repr.is_some())
            .peekable();

        let where_clause = if custom_repr_fields.peek().is_some() {
            let bounds = custom_repr_fields.map(|field| {
                let repr = field.repr.as_ref().unwrap();
                quote! {#repr: ::core::fmt::Debug,}
            });
            quote! {
                where
                    #(#bounds)*
            }
        } else {
            quote! {}
        };

        let fmt_fields = self.named.iter().enumerate().map(|(idx, field)| {
            let name = &field.name;
            let name_str = name.as_ref().unwrap().to_string();
            let default_specifier = if field.bit_width() == 1 {
                ""
            } else {
                integral_specifier
            };
            let comma = if idx < self.named.len() - 1 { "," } else { "" };
            if field.repr.is_some() {
                let ok_format_string = format!("{{indent}}{name_str}: {{:#?}}{comma}{{sep}}");
                let ok_format_string = Literal::string(&ok_format_string);
                let err_format_string = format!(
                    "{{indent}}{name_str}: InvalidBits({{{default_specifier}}}){comma}{{sep}}"
                );
                let err_format_string = Literal::string(&err_format_string);
                quote! {
                    match self.#name() {
                        Ok(value) => write!(f, #ok_format_string, value),
                        Err(invalid) => write!(f, #err_format_string, invalid.0),
                    }?;
                }
            } else {
                let format_string =
                    format!("{{indent}}{name_str}: {{{default_specifier}}}{comma}{{sep}}");
                let format_string = Literal::string(&format_string);
                quote! {write!(f, #format_string, self.#name())?;}
            }
        });

        quote! {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result
            #where_clause
            {
                let (sep, indent) = if f.alternate() {
                    ('\n', "    ")
                } else {
                    (' ', "")
                };
                write!(f, "{} {{{sep}", #ty_str)?;
                #(#fmt_fields)*
                write!(f, "}}")
            }
        }
    }

    fn fmt_impls(&self) -> TokenStream2 {
        let ty = &self.ty.def.ident;
        let lower_hex_fmt = self.fmt_fn(":#x");
        let upper_hex_fmt = self.fmt_fn(":#X");
        let binary_fmt = self.fmt_fn(":#b");
        let octal_fmt = self.fmt_fn(":#o");
        quote! {
            impl ::core::fmt::Display for #ty {
                fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                    ::core::fmt::LowerHex::fmt(self, f)
                }
            }

            impl ::core::fmt::Debug for #ty {
                fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                    ::core::fmt::LowerHex::fmt(self, f)
                }
            }

            impl ::core::fmt::Binary for #ty {
                #binary_fmt
            }

            impl ::core::fmt::LowerHex for #ty {
                #lower_hex_fmt
            }

            impl ::core::fmt::UpperHex for #ty {
                #upper_hex_fmt
            }

            impl ::core::fmt::Octal for #ty {
                #octal_fmt
            }
        }
    }
}

impl Parse for Bitfields {
    fn parse(input: ParseStream) -> Result<Self> {
        let input = {
            let content;
            braced!(content in input);
            content
        };

        let ty = input.parse::<TypeDef>()?;

        let input = {
            let content;
            braced!(content in input);
            content
        };

        let mut fields = Vec::new();
        while !input.is_empty() {
            fields.push(input.parse::<Bitfield>()?);
        }
        fields.sort_by_key(|field| field.low_bit);

        for i in 1..fields.len() {
            let prev = &fields[i - 1];
            let curr = &fields[i];
            if prev.high_bit >= curr.low_bit {
                // TODO(https://github.com/rust-lang/rust/issues/54725): It
                // would be nice to Span::join() the two spans, but that's still
                // experimental.
                return Err(Error::new(
                    curr.span,
                    format!(
                        "field overlaps with another: [{}:{}] vs. [{}:{}]",
                        prev.high_bit,
                        prev.low_bit,
                        curr.high_bit,
                        curr.low_bit
                    ),
                ));
            }
        }

        if let Some(highest) = fields.last() {
            let highest_possible = ty.base.ty.high_bit();
            if highest.high_bit > highest_possible {
                return Err(Error::new(
                    highest.span,
                    format!(
                        "high bit {} exceeds the highest possible value of {highest_possible}",
                        highest.high_bit
                    ),
                ));
            }
        }

        let mut bitfld = Self {
            ty,
            named: vec![],
            reserved: vec![],
        };

        while let Some(field) = fields.pop() {
            if field.is_reserved() {
                if field.default.is_some() {
                    bitfld.reserved.push(field);
                }
            } else {
                bitfld.named.push(field);
            }
        }

        Ok(bitfld)
    }
}

impl ToTokens for Bitfields {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        let type_def = &self.ty.def;
        let type_name = &type_def.ident;
        let base = &self.ty.base.def;

        let constants = self.constants();
        let getters_and_setters = self.getters_and_setters();
        let iter_impl = self.iter_impl();
        let fmt_impls = self.fmt_impls();
        quote! {
            #[derive(Copy, Clone, Eq, PartialEq)]
            #type_def

            impl #type_name {
                #constants

                pub const fn new() -> Self {
                    Self(Self::RSVD1_MASK)
                }

                #(#getters_and_setters)*
            }

            impl ::core::default::Default for #type_name {
                fn default() -> Self {
                    Self(Self::DEFAULT)
                }
            }

            impl ::core::convert::From<#base> for #type_name {
                // `RSVD{0,1}_MASK` may be zero, in which case the following
                // mask conditions might be trivially true.
                #[allow(clippy::bad_bit_mask)]
                fn from(value: #base) -> Self {
                    debug_assert!(
                        value & Self::RSVD1_MASK == Self::RSVD1_MASK,
                        "from(): Invalid base value ({value:#x}) has reserved-as-1 bits ({:#x}) unset",
                        Self::RSVD1_MASK,
                    );
                    debug_assert!(
                        !value & Self::RSVD0_MASK == Self::RSVD0_MASK,
                        "from(): Invalid base value ({value:#x}) has reserved-as-0 bits ({:#x}) set",
                        Self::RSVD0_MASK,
                    );
                    Self(value)
                }
            }

            impl ::core::ops::Deref for #type_name {
                type Target = #base;

                fn deref(&self) -> &Self::Target {
                    &self.0
                }
            }

            impl ::core::ops::DerefMut for #type_name {
                fn deref_mut(&mut self) -> &mut Self::Target {
                    &mut self.0
                }
            }

            #iter_impl

            #fmt_impls
        }
        .to_tokens(tokens);
    }
}
