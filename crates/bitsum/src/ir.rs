//! Semantic intermediate representation for validated `bitsum` declarations.

use proc_macro2::Ident;
use syn::{Attribute, Type, Visibility};

/// A supported fixed-width primitive integer kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PrimitiveKind {
    /// Boolean values packed into a single bit.
    Bool,
    /// An unsigned integer with the given bit width.
    Unsigned(u32),
}

impl PrimitiveKind {
    /// Returns the bit width of the primitive kind.
    pub(crate) const fn bit_width(self) -> u32 {
        match self {
            Self::Bool => 1,
            Self::Unsigned(width) => width,
        }
    }

    /// Returns whether the primitive kind is `bool`.
    pub(crate) const fn is_bool(self) -> bool {
        matches!(self, Self::Bool)
    }
}

/// Generated helper identifiers derived from the source enum name.
#[derive(Clone)]
pub(crate) struct GeneratedApi {
    /// The generated tag enum identifier.
    pub(crate) tag_ident: Ident,
    /// The generated `match`-style helper macro identifier.
    pub(crate) match_macro_ident: Ident,
    /// The generated `if let`-style helper macro identifier.
    pub(crate) if_let_macro_ident: Ident,
    /// The generated `while let`-style helper macro identifier.
    pub(crate) while_let_macro_ident: Ident,
    /// The generated `matches!`-style helper macro identifier.
    pub(crate) matches_macro_ident: Ident,
}

/// The validated representation-wide layout configuration.
#[derive(Clone)]
pub(crate) struct ReprLayout {
    /// The integer representation type used by the generated wrapper.
    pub(crate) ty: Type,
    /// The total representation width in bits.
    pub(crate) width: u32,
    /// The number of low bits reserved for variant tags.
    pub(crate) tag_width: u32,
    /// The mask that extracts the tag bits from the representation.
    pub(crate) tag_mask: u128,
}

/// A single validated field inside one variant payload.
#[derive(Clone)]
pub(crate) struct FieldLayout {
    /// The field identifier from the source enum.
    pub(crate) ident: Ident,
    /// The declared field type from the source enum.
    pub(crate) ty: Type,
    /// The normalized primitive kind used for layout validation.
    pub(crate) kind: PrimitiveKind,
    /// The number of bits reserved for the encoded field.
    pub(crate) bit_width: u32,
    /// The bit offset of the field inside the packed representation.
    pub(crate) offset: u32,
}

/// A single validated source variant together with its generated metadata.
#[derive(Clone)]
pub(crate) struct VariantLayout {
    /// The source variant identifier.
    pub(crate) ident: Ident,
    /// The normalized helper stem used for generated method and binding names.
    pub(crate) helper_name: Box<str>,
    /// The generated constructor method name.
    pub(crate) constructor_ident: Ident,
    /// The numeric tag assigned to this variant.
    pub(crate) tag_value: u32,
    /// The validated payload fields in declaration order.
    pub(crate) fields: Box<[FieldLayout]>,
    /// The mask of all bits that may be non-zero for this variant.
    pub(crate) valid_mask: u128,
    /// Documentation copied from the source variant.
    pub(crate) doc_attrs: Box<[Attribute]>,
}

/// A fully validated `bitsum` definition ready for code generation.
#[derive(Clone)]
pub(crate) struct BitsumDefinition {
    /// The original visibility of the source enum.
    pub(crate) vis: Visibility,
    /// The generated wrapper type identifier.
    pub(crate) struct_ident: Ident,
    /// All generated helper identifiers derived from the source enum name.
    pub(crate) api: GeneratedApi,
    /// The validated representation-wide layout configuration.
    pub(crate) repr: ReprLayout,
    /// The validated variants in tag order.
    pub(crate) variants: Box<[VariantLayout]>,
    /// Documentation copied from the source enum.
    pub(crate) doc_attrs: Box<[Attribute]>,
}
