//! Packed tagged-union generation for fixed-width integer representations.
//!
//! The [`bitsum`] attribute transforms an enum-like description into a compact
//! wrapper type with constructors, a tag enum, and local pattern-matching
//! macros.

#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use quote::{format_ident, quote};
use syn::{
    Attribute, Error, Fields, ItemEnum, LitInt, Result, Type, Variant, Visibility,
    parse_macro_input, spanned::Spanned,
};

/// Generates a packed tagged union from an enum declaration.
///
/// The attribute takes the integer representation type to use for the generated
/// wrapper, such as `u8`, `u16`, `u32`, `u64`, or `u128`.
#[proc_macro_attribute]
pub fn bitsum(attr: TokenStream, item: TokenStream) -> TokenStream {
    let repr = parse_macro_input!(attr as Type);
    let item = parse_macro_input!(item as ItemEnum);

    match expand_bitsum(repr, item) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.into_compile_error().into(),
    }
}

/// A supported fixed-width primitive integer kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrimitiveKind {
    /// Boolean values packed into a single bit.
    Bool,
    /// An unsigned integer with the given bit width.
    Unsigned(u32),
}

impl PrimitiveKind {
    /// Parses a supported primitive type.
    fn parse(ty: &Type, allow_bool: bool) -> Result<Self> {
        let ident = primitive_ident(ty)
            .ok_or_else(|| Error::new_spanned(ty, "expected a primitive unsigned integer type"))?;
        match ident.to_string().as_str() {
            "bool" if allow_bool => Ok(Self::Bool),
            "u8" => Ok(Self::Unsigned(8)),
            "u16" => Ok(Self::Unsigned(16)),
            "u32" => Ok(Self::Unsigned(32)),
            "u64" => Ok(Self::Unsigned(64)),
            "u128" => Ok(Self::Unsigned(128)),
            _ if allow_bool => Err(Error::new_spanned(
                ty,
                "expected `bool` or a primitive unsigned integer type",
            )),
            _ => Err(Error::new_spanned(
                ty,
                "expected a primitive unsigned integer type",
            )),
        }
    }

    /// Returns the bit width of the primitive type.
    fn bit_width(self) -> u32 {
        match self {
            Self::Bool => 1,
            Self::Unsigned(width) => width,
        }
    }

    /// Returns whether the type is `bool`.
    fn is_bool(self) -> bool {
        matches!(self, Self::Bool)
    }
}

/// A parsed field inside a generated variant payload.
#[derive(Clone)]
struct ParsedField {
    /// The source field identifier.
    ident: Ident,
    /// The source field type.
    ty: Type,
    /// The primitive type category.
    kind: PrimitiveKind,
    /// The number of packed bits reserved for this field.
    bit_width: u32,
    /// The bit offset within the encoded representation.
    offset: u32,
}

/// A parsed variant in the source enum.
#[derive(Clone)]
struct ParsedVariant {
    /// The source variant identifier.
    ident: Ident,
    /// The constructor method name.
    constructor_ident: Ident,
    /// The numeric tag value assigned to the variant.
    tag_value: u32,
    /// The fields carried by the variant.
    fields: Vec<ParsedField>,
    /// The mask of all bits that must be present for a valid encoding.
    valid_mask: u128,
    /// Documentation copied from the source variant.
    doc_attrs: Vec<Attribute>,
}

/// The fully parsed `bitsum` input.
struct ParsedBitsum {
    /// The source visibility.
    vis: Visibility,
    /// The generated wrapper type name.
    struct_ident: Ident,
    /// The generated tag enum name.
    tag_ident: Ident,
    /// The generated match macro name.
    match_macro_ident: Ident,
    /// The generated `if let`-style macro name.
    if_let_macro_ident: Ident,
    /// The generated `while let`-style macro name.
    while_let_macro_ident: Ident,
    /// The generated `matches!`-style macro name.
    matches_macro_ident: Ident,
    /// The representation type.
    repr_ty: Type,
    /// The representation width in bits.
    repr_width: u32,
    /// The number of bits reserved for tags.
    tag_width: u32,
    /// The mask of tag bits in the encoded representation.
    tag_mask: u128,
    /// The parsed variants.
    variants: Vec<ParsedVariant>,
    /// Documentation copied from the source enum.
    doc_attrs: Vec<Attribute>,
}

impl ParsedBitsum {
    /// Parses and validates a source enum.
    fn parse(repr_ty: Type, item: ItemEnum) -> Result<Self> {
        let repr_kind = PrimitiveKind::parse(&repr_ty, false)?;
        let repr_width = repr_kind.bit_width();
        if item.variants.is_empty() {
            return Err(Error::new_spanned(
                item,
                "`#[bitsum]` requires at least one enum variant",
            ));
        }

        let struct_ident = item.ident;
        let tag_ident = format_ident!("{struct_ident}Tag");
        let struct_snake = to_snake_case(&struct_ident.to_string());
        let match_macro_ident = format_ident!("match_{struct_snake}");
        let if_let_macro_ident = format_ident!("if_let_{struct_snake}");
        let while_let_macro_ident: Ident = format_ident!("while_let_{struct_snake}");
        let matches_macro_ident = format_ident!("matches_{struct_snake}");
        let tag_width = ceil_log2(item.variants.len());
        if tag_width > repr_width {
            return Err(Error::new(
                struct_ident.span(),
                "representation is too small to encode all variant tags",
            ));
        }

        let tag_mask = bits_mask(tag_width);
        let vis = item.vis;
        let doc_attrs = doc_attrs(&item.attrs);
        let mut variants = Vec::with_capacity(item.variants.len());

        for (tag_value, variant) in item.variants.into_iter().enumerate() {
            variants.push(parse_variant(
                repr_width,
                tag_width,
                tag_value as u32,
                variant,
            )?);
        }

        Ok(Self {
            vis,
            struct_ident,
            tag_ident,
            match_macro_ident,
            if_let_macro_ident,
            while_let_macro_ident,
            matches_macro_ident,
            repr_ty,
            repr_width,
            tag_width,
            tag_mask,
            variants,
            doc_attrs,
        })
    }

    /// Expands the parsed definition into Rust items.
    fn expand(&self) -> TokenStream2 {
        let struct_ident = &self.struct_ident;
        let tag_ident = &self.tag_ident;
        let match_macro_ident = &self.match_macro_ident;
        let if_let_macro_ident = &self.if_let_macro_ident;
        let while_let_macro_ident = &self.while_let_macro_ident;
        let matches_macro_ident = &self.matches_macro_ident;
        let vis = &self.vis;
        let repr_ty = &self.repr_ty;
        let repr_width = lit_u32(self.repr_width);
        let tag_mask = lit_u128(self.tag_mask);
        let tag_width = lit_u32(self.tag_width);
        let enum_doc_attrs = &self.doc_attrs;

        let tag_variants = self.variants.iter().map(|variant| {
            let ident = &variant.ident;
            let doc_attrs = &variant.doc_attrs;
            quote! {
                #(#doc_attrs)*
                #[doc = "Represents this tag for a valid packed value."]
                #ident,
            }
        });

        let constructor_methods = self.variants.iter().map(|variant| {
            let constructor_ident = &variant.constructor_ident;
            let doc_attrs = &variant.doc_attrs;
            let tag_value = lit_u32(variant.tag_value);

            if variant.fields.is_empty() {
                quote! {
                    #(#doc_attrs)*
                    #[doc = "Constructs this variant."]
                    pub const fn #constructor_ident() -> Self {
                        Self(#tag_value as #repr_ty)
                    }
                }
            } else {
                let params = variant.fields.iter().map(|field| {
                    let ident = &field.ident;
                    let ty = &field.ty;
                    quote!(#ident: #ty)
                });
                let checks = variant.fields.iter().filter_map(|field| {
                    if field.kind.is_bool() {
                        return None;
                    }
                    let ident = &field.ident;
                    let mask = lit_u128(bits_mask(field.bit_width));
                    let message = format!(
                        "field `{}` exceeds its declared width of {} bits",
                        ident, field.bit_width
                    );
                    Some(quote! {
                        assert!((#ident as u128) <= #mask, #message);
                    })
                });
                let encodes = variant.fields.iter().map(|field| {
                    let ident = &field.ident;
                    let mask = lit_u128(bits_mask(field.bit_width));
                    let offset = lit_u32(field.offset);
                    quote! {
                        bits |= (((#ident as #repr_ty) & (#mask as #repr_ty)) << #offset);
                    }
                });
                quote! {
                    #(#doc_attrs)*
                    #[doc = "Constructs this variant."]
                    pub const fn #constructor_ident(#(#params),*) -> Self {
                        #(#checks)*
                        let mut bits = #tag_value as #repr_ty;
                        #(#encodes)*
                        Self(bits)
                    }
                }
            }
        });

        let from_bits_match_arms = self.variants.iter().map(|variant| {
            let tag_value = lit_u32(variant.tag_value);
            let valid_mask = lit_u128(variant.valid_mask);
            quote! {
                #tag_value => {
                    if (bits & !((#valid_mask as #repr_ty))) == 0 {
                        Some(Self(bits))
                    } else {
                        None
                    }
                }
            }
        });

        let tag_match_arms = self.variants.iter().map(|variant| {
            let ident = &variant.ident;
            let tag_value = lit_u32(variant.tag_value);
            quote! {
                #tag_value => #tag_ident::#ident
            }
        });

        let match_macro_patterns = self.variants.iter().map(|variant| {
            let ident = &variant.ident;
            let body_ident = format_ident!(
                "__bitsum_body_{}",
                to_snake_case(&variant.ident.to_string())
            );
            if variant.fields.is_empty() {
                quote! {
                    #ident => $#body_ident:expr
                }
            } else {
                let field_patterns = variant.fields.iter().map(|field| {
                    let field_ident = &field.ident;
                    let pattern_ident = format_ident!(
                        "__bitsum_pat_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    );
                    quote!(#field_ident: $#pattern_ident:pat)
                });
                quote! {
                    #ident { #(#field_patterns),* $(,)? } => $#body_ident:expr
                }
            }
        });

        let match_macro_dispatch_arms = self.variants.iter().map(|variant| {
            let ident = &variant.ident;
            let body_ident = format_ident!(
                "__bitsum_body_{}",
                to_snake_case(&variant.ident.to_string())
            );
            if variant.fields.is_empty() {
                quote! {
                    #tag_ident::#ident => $#body_ident
                }
            } else {
                let pattern_idents = variant.fields.iter().map(|field| {
                    format_ident!(
                        "__bitsum_pat_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    )
                });
                let decoded_exprs = variant.fields.iter().map(|field| {
                    let offset = lit_u32(field.offset);
                    let mask = lit_u128(bits_mask(field.bit_width));
                    let ty = &field.ty;
                    if field.kind.is_bool() {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) != 0)
                        }
                    } else {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) as #ty)
                        }
                    }
                });
                quote! {
                    #tag_ident::#ident => {
                        let (#($#pattern_idents),*) = (#(#decoded_exprs),*);
                        $#body_ident
                    }
                }
            }
        });

        let if_let_rules = self.variants.iter().map(|variant| {
            let ident = &variant.ident;
            let tag_value = lit_u32(variant.tag_value);
            if variant.fields.is_empty() {
                quote! {
                    (let #ident = $instr:expr => $then:block else $else:block) => {{
                        let __bitsum_instr = $instr;
                        let __bitsum_bits = __bitsum_instr.bits();
                        if (__bitsum_bits & (#tag_mask as #repr_ty)) == (#tag_value as #repr_ty) {
                            $then
                        } else {
                            $else
                        }
                    }};
                    (let #ident = $instr:expr => $then:block) => {
                        #if_let_macro_ident!(let #ident = $instr => $then else {})
                    };
                }
            } else {
                let field_patterns: Vec<_> = variant.fields.iter().map(|field| {
                    let field_ident = &field.ident;
                    let pattern_ident = format_ident!(
                        "__bitsum_pat_if_let_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    );
                    quote!(#field_ident: $#pattern_ident:pat)
                }).collect();
                let pattern_idents: Vec<_> = variant.fields.iter().map(|field| {
                    format_ident!(
                        "__bitsum_pat_if_let_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    )
                }).collect();
                let decoded_exprs: Vec<_> = variant.fields.iter().map(|field| {
                    let offset = lit_u32(field.offset);
                    let mask = lit_u128(bits_mask(field.bit_width));
                    let ty = &field.ty;
                    if field.kind.is_bool() {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) != 0)
                        }
                    } else {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) as #ty)
                        }
                    }
                }).collect();
                quote! {
                    (let #ident { #(#field_patterns),* $(,)? } = $instr:expr => $then:block else $else:block) => {{
                        let __bitsum_instr = $instr;
                        let __bitsum_bits = __bitsum_instr.bits();
                        if (__bitsum_bits & (#tag_mask as #repr_ty)) == (#tag_value as #repr_ty) {
                            #[allow(irrefutable_let_patterns)]
                            if let (#($#pattern_idents),*) = (#(#decoded_exprs),*) {
                                $then
                            } else {
                                $else
                            }
                        } else {
                            $else
                        }
                    }};
                    (let #ident { #(#field_patterns),* $(,)? } = $instr:expr => $then:block) => {
                        #if_let_macro_ident!(let #ident { #(#field_patterns),* } = $instr => $then else {})
                    };
                }
            }
        });

        let while_let_rules = self.variants.iter().map(|variant| {
            let ident = &variant.ident;
            let tag_value = lit_u32(variant.tag_value);
            if variant.fields.is_empty() {
                quote! {
                    (let #ident = $instr:expr => $body:block) => {{
                        loop {
                            let __bitsum_instr = $instr;
                            let __bitsum_bits = __bitsum_instr.bits();
                            if (__bitsum_bits & (#tag_mask as #repr_ty)) == (#tag_value as #repr_ty) {
                                $body
                            } else {
                                break;
                            }
                        }
                    }};
                }
            } else {
                let field_patterns = variant.fields.iter().map(|field| {
                    let field_ident = &field.ident;
                    let pattern_ident = format_ident!(
                        "__bitsum_pat_while_let_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    );
                    quote!(#field_ident: $#pattern_ident:pat)
                });
                let pattern_idents = variant.fields.iter().map(|field| {
                    format_ident!(
                        "__bitsum_pat_while_let_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    )
                });
                let decoded_exprs = variant.fields.iter().map(|field| {
                    let offset = lit_u32(field.offset);
                    let mask = lit_u128(bits_mask(field.bit_width));
                    let ty = &field.ty;
                    if field.kind.is_bool() {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) != 0)
                        }
                    } else {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) as #ty)
                        }
                    }
                });
                quote! {
                    (let #ident { #(#field_patterns),* $(,)? } = $instr:expr => $body:block) => {{
                        loop {
                            let __bitsum_instr = $instr;
                            let __bitsum_bits = __bitsum_instr.bits();
                            if (__bitsum_bits & (#tag_mask as #repr_ty)) == (#tag_value as #repr_ty) {
                                #[allow(irrefutable_let_patterns)]
                                if let (#($#pattern_idents),*) = (#(#decoded_exprs),*) {
                                    $body
                                } else {
                                    break;
                                }
                            } else {
                                break;
                            }
                        }
                    }};
                }
            }
        });

        let matches_rules = self.variants.iter().map(|variant| {
            let ident = &variant.ident;
            let tag_value = lit_u32(variant.tag_value);
            if variant.fields.is_empty() {
                quote! {
                    ($instr:expr, #ident $(if $guard:expr)? $(,)?) => {{
                        let __bitsum_instr = $instr;
                        let __bitsum_bits = __bitsum_instr.bits();
                        if (__bitsum_bits & (#tag_mask as #repr_ty)) == (#tag_value as #repr_ty) {
                            ::core::matches!((), () $(if $guard)?)
                        } else {
                            false
                        }
                    }};
                }
            } else {
                let field_patterns = variant.fields.iter().map(|field| {
                    let field_ident = &field.ident;
                    let pattern_ident = format_ident!(
                        "__bitsum_pat_matches_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    );
                    quote!(#field_ident: $#pattern_ident:pat)
                });
                let pattern_idents = variant.fields.iter().map(|field| {
                    format_ident!(
                        "__bitsum_pat_matches_{}_{}",
                        to_snake_case(&variant.ident.to_string()),
                        field.ident
                    )
                });
                let decoded_exprs = variant.fields.iter().map(|field| {
                    let offset = lit_u32(field.offset);
                    let mask = lit_u128(bits_mask(field.bit_width));
                    let ty = &field.ty;
                    if field.kind.is_bool() {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) != 0)
                        }
                    } else {
                        quote! {
                            (((__bitsum_bits >> #offset) & (#mask as #repr_ty)) as #ty)
                        }
                    }
                });
                quote! {
                    ($instr:expr, #ident { #(#field_patterns),* $(,)? } $(if $guard:expr)? $(,)?) => {{
                        let __bitsum_instr = $instr;
                        let __bitsum_bits = __bitsum_instr.bits();
                        if (__bitsum_bits & (#tag_mask as #repr_ty)) == (#tag_value as #repr_ty) {
                            ::core::matches!((#(#decoded_exprs),*), (#($#pattern_idents),*) $(if $guard)?)
                        } else {
                            false
                        }
                    }};
                }
            }
        });

        quote! {
            #(#enum_doc_attrs)*
            #[doc = "Generated packed representation for the declared tagged union."]
            #[repr(transparent)]
            #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
            #vis struct #struct_ident(#repr_ty);

            #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
            #[doc = "The decoded tag of a packed bitsum value."]
            #vis enum #tag_ident {
                #(#tag_variants)*
            }

            impl #struct_ident {
                #[doc = "Validates a raw packed value and returns it when it encodes a declared variant."]
                #[doc = "Returns `None` when the tag is unknown or when unused payload bits are non-zero."]
                pub const fn from_bits(bits: #repr_ty) -> Option<Self> {
                    const _REPR_WIDTH_BITS: u32 = #repr_width;
                    const _TAG_WIDTH_BITS: u32 = #tag_width;
                    const _TAG_MASK: #repr_ty = #tag_mask as #repr_ty;
                    let _ = (_REPR_WIDTH_BITS, _TAG_WIDTH_BITS);
                    match bits & _TAG_MASK {
                        #(#from_bits_match_arms,)*
                        _ => None,
                    }
                }

                #[doc = "Wraps a raw packed value without validating it."]
                #[doc = ""]
                #[doc = "# Safety"]
                #[doc = "The caller must ensure `bits` encodes one of the declared variants and that all unused payload bits are zero."]
                pub const unsafe fn from_bits_unchecked(bits: #repr_ty) -> Self {
                    Self(bits)
                }

                #[doc = "Returns the raw packed representation."]
                pub const fn bits(self) -> #repr_ty {
                    self.0
                }

                #[doc = "Returns the decoded tag for this packed value."]
                #[doc = "This method assumes the value invariant established by the constructors and `from_bits`."]
                pub const fn tag(self) -> #tag_ident {
                    const _REPR_WIDTH_BITS: u32 = #repr_width;
                    const _TAG_WIDTH_BITS: u32 = #tag_width;
                    const _TAG_MASK: #repr_ty = #tag_mask as #repr_ty;
                    let _ = (_REPR_WIDTH_BITS, _TAG_WIDTH_BITS);
                    match self.0 & _TAG_MASK {
                        #(#tag_match_arms,)*
                        _ => {
                            // SAFETY: `#struct_ident` values are only constructed through
                            // validated constructors or `from_bits_unchecked`, which requires
                            // the caller to uphold the same invariant.
                            unsafe { core::hint::unreachable_unchecked() }
                        }
                    }
                }

                #(#constructor_methods)*
            }

            impl From<#struct_ident> for #repr_ty {
                fn from(bitsum: #struct_ident) -> Self {
                    bitsum.bits()
                }
            }

            #[allow(unused_macros)]
            #[doc = "Matches on the generated bitsum tag and binds decoded fields for each variant."]
            #[doc = "Named payload patterns use explicit field syntax such as `Variant { field: pat }`."]
            macro_rules! #match_macro_ident {
                (
                    $instr:expr,
                    {
                        #(#match_macro_patterns, )*
                    }
                ) => {{
                    let __bitsum_instr = $instr;
                    let __bitsum_bits = __bitsum_instr.bits();
                    match __bitsum_instr.tag() {
                        #(#match_macro_dispatch_arms,)*
                    }
                }};
            }

            #[allow(unused_macros)]
            #[doc = "Performs an `if let`-style match on one generated bitsum pattern."]
            #[doc = "The scrutinee expression is evaluated once and must be followed by `=>`."]
            macro_rules! #if_let_macro_ident {
                #(#if_let_rules)*
            }

            #[allow(unused_macros)]
            #[doc = "Performs a `while let`-style loop on one generated bitsum pattern."]
            #[doc = "The scrutinee expression is re-evaluated on each iteration and must be followed by `=>`."]
            macro_rules! #while_let_macro_ident {
                #(#while_let_rules)*
            }

            #[allow(unused_macros)]
            #[doc = "Returns whether a generated bitsum value matches one pattern, optionally with a guard."]
            macro_rules! #matches_macro_ident {
                #(#matches_rules)*
            }
        }
    }
}

/// Expands the attribute macro for one enum declaration.
fn expand_bitsum(repr_ty: Type, item: ItemEnum) -> Result<TokenStream2> {
    ParsedBitsum::parse(repr_ty, item).map(|bitsum| bitsum.expand())
}

/// Parses one enum variant.
fn parse_variant(
    repr_width: u32,
    tag_width: u32,
    tag_value: u32,
    variant: Variant,
) -> Result<ParsedVariant> {
    let ident = variant.ident;
    let constructor_ident = format_ident!("{}", to_snake_case(&ident.to_string()));
    let variant_doc_attrs = doc_attrs(&variant.attrs);
    let mut fields = Vec::new();
    let mut next_offset = tag_width;

    match variant.fields {
        Fields::Unit => {}
        Fields::Named(named) => {
            for field in named.named {
                let field_span = field.span();
                let field_ident = field
                    .ident
                    .ok_or_else(|| Error::new(field_span, "expected named fields"))?;
                let kind = PrimitiveKind::parse(&field.ty, true)?;
                let bit_width = parse_bits_attr(&field.attrs, &field.ty)?;
                if kind.is_bool() && bit_width != 1 {
                    return Err(Error::new_spanned(
                        &field.ty,
                        "`bool` fields must use exactly `#[bits(1)]`",
                    ));
                }
                if bit_width > kind.bit_width() {
                    return Err(Error::new_spanned(
                        &field.ty,
                        format!(
                            "field type is {} bits wide but `#[bits({bit_width})]` was requested",
                            kind.bit_width()
                        ),
                    ));
                }
                let end_offset = next_offset
                    .checked_add(bit_width)
                    .ok_or_else(|| Error::new_spanned(&field.ty, "field layout overflowed"))?;
                if end_offset > repr_width {
                    return Err(Error::new_spanned(
                        &field.ty,
                        "variant payload does not fit in the chosen representation",
                    ));
                }
                fields.push(ParsedField {
                    ident: field_ident,
                    ty: field.ty,
                    kind,
                    bit_width,
                    offset: next_offset,
                });
                next_offset = end_offset;
            }
        }
        Fields::Unnamed(unnamed) => {
            return Err(Error::new_spanned(
                unnamed,
                "`#[bitsum]` currently supports only unit variants and variants with named fields",
            ));
        }
    }

    let valid_mask = fields.iter().fold(bits_mask(tag_width), |mask, field| {
        mask | (bits_mask(field.bit_width) << field.offset)
    });

    Ok(ParsedVariant {
        ident,
        constructor_ident,
        tag_value,
        fields,
        valid_mask,
        doc_attrs: variant_doc_attrs,
    })
}

/// Extracts the `#[bits(N)]` width from one field.
fn parse_bits_attr(attrs: &[Attribute], ty: &Type) -> Result<u32> {
    let attr = attrs
        .iter()
        .find(|attr| attr.path().is_ident("bits"))
        .ok_or_else(|| Error::new_spanned(ty, "missing `#[bits(...)]` attribute"))?;
    let bits = attr.parse_args::<LitInt>()?.base10_parse::<u32>()?;
    if bits == 0 {
        return Err(Error::new_spanned(attr, "`#[bits(0)]` is not allowed"));
    }
    Ok(bits)
}

/// Returns only doc attributes from a source attribute list.
fn doc_attrs(attrs: &[Attribute]) -> Vec<Attribute> {
    attrs
        .iter()
        .filter(|attr| attr.path().is_ident("doc"))
        .cloned()
        .collect()
}

/// Returns the single-segment primitive identifier for a type if there is one.
fn primitive_ident(ty: &Type) -> Option<&Ident> {
    match ty {
        Type::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
            Some(&path.path.segments[0].ident)
        }
        _ => None,
    }
}

/// Converts a positive bit width into a bit mask.
fn bits_mask(width: u32) -> u128 {
    match width {
        0 => 0,
        128 => u128::MAX,
        _ => (1u128 << width) - 1,
    }
}

/// Computes `ceil(log2(value))`, with `0` for `value <= 1`.
fn ceil_log2(value: usize) -> u32 {
    match value {
        0 | 1 => 0,
        _ => usize::BITS - (value - 1).leading_zeros(),
    }
}

/// Builds a literal `u32` token.
fn lit_u32(value: u32) -> LitInt {
    LitInt::new(&value.to_string(), Span::call_site())
}

/// Builds a literal `u128` token.
fn lit_u128(value: u128) -> LitInt {
    LitInt::new(&value.to_string(), Span::call_site())
}

/// Converts a Rust-style identifier to snake case for generated method names.
fn to_snake_case(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut chars = name.chars().peekable();
    while let Some(ch) = chars.next() {
        let next_is_lower = chars.peek().is_some_and(|next| next.is_ascii_lowercase());
        if ch.is_ascii_uppercase() {
            if !out.is_empty()
                && (out.ends_with(|prev: char| prev.is_ascii_lowercase()) || next_is_lower)
            {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}
