//! Parsing and validation for source `bitsum` declarations.

use std::collections::BTreeMap;

use proc_macro2::Ident;
use quote::format_ident;
use syn::{Attribute, Error, Fields, ItemEnum, LitInt, Result, Type, Variant, spanned::Spanned};

use crate::ir::{
    BitsumDefinition, FieldLayout, GeneratedApi, PrimitiveKind, ReprLayout, VariantLayout,
};
use crate::support::{bits_mask, ceil_log2, to_snake_case};

/// Parses and validates one source enum into the internal `bitsum` IR.
pub(crate) fn parse_bitsum(repr_ty: Type, item: ItemEnum) -> Result<BitsumDefinition> {
    let repr_kind = parse_primitive_kind(&repr_ty, false)?;
    let repr_width = repr_kind.bit_width();
    if item.variants.is_empty() {
        return Err(Error::new_spanned(
            item,
            "`#[bitsum]` requires at least one enum variant",
        ));
    }

    let struct_ident = item.ident;
    let api = build_generated_api(&struct_ident);
    let tag_width = ceil_log2(item.variants.len());
    if tag_width > repr_width {
        return Err(Error::new(
            struct_ident.span(),
            "representation is too small to encode all variant tags",
        ));
    }

    let repr = ReprLayout {
        ty: repr_ty,
        width: repr_width,
        tag_width,
        tag_mask: bits_mask(tag_width),
    };
    let vis = item.vis;
    let doc_attrs = doc_attrs(&item.attrs);
    let mut variants = Vec::with_capacity(item.variants.len());
    let mut helper_names = BTreeMap::<String, Ident>::new();

    for (tag_value, variant) in item.variants.into_iter().enumerate() {
        let variant = parse_variant(&repr, tag_value as u32, variant)?;
        if let Some(previous_ident) =
            helper_names.insert(variant.helper_name.to_string(), variant.ident.clone())
        {
            return Err(Error::new_spanned(
                &variant.ident,
                format!(
                    "variants `{previous_ident}` and `{}` both normalize to helper name `{}`; rename one variant to avoid generated API collisions",
                    variant.ident, variant.helper_name
                ),
            ));
        }
        variants.push(variant);
    }

    Ok(BitsumDefinition {
        vis,
        struct_ident,
        api,
        repr,
        variants: variants.into_boxed_slice(),
        doc_attrs,
    })
}

/// Parses one enum variant and assigns its payload layout.
fn parse_variant(repr: &ReprLayout, tag_value: u32, variant: Variant) -> Result<VariantLayout> {
    let ident = variant.ident;
    let helper_name = to_snake_case(&ident.to_string());
    let constructor_ident = format_ident!("{helper_name}");
    let doc_attrs = doc_attrs(&variant.attrs);
    let mut fields = Vec::new();
    let mut next_offset = repr.tag_width;

    match variant.fields {
        Fields::Unit => {}
        Fields::Named(named) => {
            for field in named.named {
                let parsed = parse_field(repr, next_offset, field)?;
                next_offset = parsed.offset + parsed.bit_width;
                fields.push(parsed);
            }
        }
        Fields::Unnamed(unnamed) => {
            return Err(Error::new_spanned(
                unnamed,
                "`#[bitsum]` currently supports only unit variants and variants with named fields",
            ));
        }
    }

    let valid_mask = fields
        .iter()
        .fold(bits_mask(repr.tag_width), |mask, field| {
            mask | (bits_mask(field.bit_width) << field.offset)
        });

    Ok(VariantLayout {
        ident,
        helper_name,
        constructor_ident,
        tag_value,
        fields: fields.into_boxed_slice(),
        valid_mask,
        doc_attrs,
    })
}

/// Parses one named payload field and validates its requested bit width.
fn parse_field(repr: &ReprLayout, next_offset: u32, field: syn::Field) -> Result<FieldLayout> {
    let field_span = field.span();
    let field_ident = field
        .ident
        .ok_or_else(|| Error::new(field_span, "expected named fields"))?;
    let kind = parse_primitive_kind(&field.ty, true)?;
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
    if end_offset > repr.width {
        return Err(Error::new_spanned(
            &field.ty,
            "variant payload does not fit in the chosen representation",
        ));
    }

    Ok(FieldLayout {
        ident: field_ident,
        ty: field.ty,
        kind,
        bit_width,
        offset: next_offset,
    })
}

/// Extracts the generated helper identifiers derived from the source enum.
fn build_generated_api(struct_ident: &Ident) -> GeneratedApi {
    let struct_snake = to_snake_case(&struct_ident.to_string());
    GeneratedApi {
        tag_ident: format_ident!("{struct_ident}Tag"),
        match_macro_ident: format_ident!("match_{struct_snake}"),
        if_let_macro_ident: format_ident!("if_let_{struct_snake}"),
        while_let_macro_ident: format_ident!("while_let_{struct_snake}"),
        matches_macro_ident: format_ident!("matches_{struct_snake}"),
    }
}

/// Parses one supported primitive type reference.
fn parse_primitive_kind(ty: &Type, allow_bool: bool) -> Result<PrimitiveKind> {
    let ident = primitive_ident(ty)
        .ok_or_else(|| Error::new_spanned(ty, "expected a primitive unsigned integer type"))?;

    match ident.to_string().as_str() {
        "bool" if allow_bool => Ok(PrimitiveKind::Bool),
        "u8" => Ok(PrimitiveKind::Unsigned(8)),
        "u16" => Ok(PrimitiveKind::Unsigned(16)),
        "u32" => Ok(PrimitiveKind::Unsigned(32)),
        "u64" => Ok(PrimitiveKind::Unsigned(64)),
        "u128" => Ok(PrimitiveKind::Unsigned(128)),
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

/// Extracts the `#[bits(N)]` width from one field.
fn parse_bits_attr(attrs: &[Attribute], ty: &Type) -> Result<u32> {
    let mut bits_attrs = attrs.iter().filter(|attr| attr.path().is_ident("bits"));
    let attr = bits_attrs
        .next()
        .ok_or_else(|| Error::new_spanned(ty, "missing `#[bits(...)]` attribute"))?;
    if let Some(duplicate_attr) = bits_attrs.next() {
        return Err(Error::new_spanned(
            duplicate_attr,
            "duplicate `#[bits(...)]` attribute",
        ));
    }

    let bits = attr.parse_args::<LitInt>()?.base10_parse::<u32>()?;
    if bits == 0 {
        return Err(Error::new_spanned(attr, "`#[bits(0)]` is not allowed"));
    }
    Ok(bits)
}

/// Returns only documentation attributes from a source attribute list.
fn doc_attrs(attrs: &[Attribute]) -> Box<[Attribute]> {
    attrs
        .iter()
        .filter(|attr| attr.path().is_ident("doc"))
        .cloned()
        .collect::<Vec<_>>()
        .into_boxed_slice()
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
