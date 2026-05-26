//! Code generation from validated `bitsum` IR into Rust tokens.

use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::{format_ident, quote};
use syn::Visibility;

use crate::ir::{BitsumDefinition, FieldLayout, VariantLayout};
use crate::support::{bits_mask, lit_u32, lit_u128};

/// Generates the final Rust items for one validated `bitsum` definition.
pub(crate) fn generate_bitsum(definition: &BitsumDefinition) -> TokenStream2 {
    Generator { definition }.generate()
}

/// Stateful code generator for one validated definition.
struct Generator<'a> {
    /// The validated definition being rendered.
    definition: &'a BitsumDefinition,
}

impl<'a> Generator<'a> {
    /// Generates every item emitted by the macro expansion.
    fn generate(&self) -> TokenStream2 {
        let struct_ident = &self.definition.struct_ident;
        let tag_ident = &self.definition.api.tag_ident;
        let match_macro_ident = &self.definition.api.match_macro_ident;
        let if_let_macro_ident = &self.definition.api.if_let_macro_ident;
        let while_let_macro_ident = &self.definition.api.while_let_macro_ident;
        let matches_macro_ident = &self.definition.api.matches_macro_ident;
        let vis = &self.definition.vis;
        let repr_ty = &self.definition.repr.ty;
        let repr_width = lit_u32(self.definition.repr.width);
        let tag_mask = lit_u128(self.definition.repr.tag_mask);
        let tag_width = lit_u32(self.definition.repr.tag_width);
        let enum_doc_attrs = &self.definition.doc_attrs;

        let macro_reexports = self.macro_reexports();
        let tag_variants = self.tag_variants();
        let constructor_methods = self.constructor_methods();
        let validated_bit_arms = self.validated_bit_arms();
        let tag_match_arms = self.tag_match_arms();
        let match_macro_patterns = self.match_macro_patterns();
        let match_macro_dispatch_arms = self.match_macro_dispatch_arms();
        let if_let_rules = self.if_let_rules();
        let while_let_rules = self.while_let_rules();
        let matches_rules = self.matches_rules();

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
                        #(#validated_bit_arms,)*
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
                        #(#match_macro_patterns),* $(,)?
                    }
                ) => {{
                    let __bitsum_instr = $instr;
                    let __bitsum_bits = __bitsum_instr.bits();
                    match __bitsum_bits & (#tag_mask as #repr_ty) {
                        #(#match_macro_dispatch_arms,)*
                        _ => {
                            // SAFETY: generated constructors and `from_bits` only admit declared
                            // tags, and the macro accepts the same invariant as `bits()`.
                            unsafe { ::core::hint::unreachable_unchecked() }
                        }
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

            #(#macro_reexports)*
        }
    }

    /// Generates macro re-exports with the widest safe visibility for local helper macros.
    fn macro_reexports(&self) -> Vec<TokenStream2> {
        let match_macro_ident = &self.definition.api.match_macro_ident;
        let if_let_macro_ident = &self.definition.api.if_let_macro_ident;
        let while_let_macro_ident = &self.definition.api.while_let_macro_ident;
        let matches_macro_ident = &self.definition.api.matches_macro_ident;

        macro_reexport_vis(&self.definition.vis)
            .into_iter()
            .map(|macro_vis| {
                quote! {
                    #[doc(hidden)]
                    #macro_vis use #match_macro_ident;
                    #[doc(hidden)]
                    #macro_vis use #if_let_macro_ident;
                    #[doc(hidden)]
                    #macro_vis use #while_let_macro_ident;
                    #[doc(hidden)]
                    #macro_vis use #matches_macro_ident;
                }
            })
            .collect()
    }

    /// Generates the tag enum variants.
    fn tag_variants(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| {
                let ident = &variant.ident;
                let doc_attrs = &variant.doc_attrs;
                quote! {
                    #(#doc_attrs)*
                    #[doc = "Represents this tag for a valid packed value."]
                    #ident,
                }
            })
            .collect()
    }

    /// Generates all variant constructor methods.
    fn constructor_methods(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| self.constructor_method(variant))
            .collect()
    }

    /// Generates one constructor method.
    fn constructor_method(&self, variant: &VariantLayout) -> TokenStream2 {
        let constructor_ident = &variant.constructor_ident;
        let doc_attrs = &variant.doc_attrs;
        let tag_value = lit_u32(variant.tag_value);
        let repr_ty = &self.definition.repr.ty;

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
            let checks = variant
                .fields
                .iter()
                .filter_map(|field| self.constructor_width_check(field));
            let encodes = variant.fields.iter().map(|field| self.encode_field(field));
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
    }

    /// Generates one width assertion for constructor input, when the field needs one.
    fn constructor_width_check(&self, field: &FieldLayout) -> Option<TokenStream2> {
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
    }

    /// Generates one field-encoding statement for constructor bodies.
    fn encode_field(&self, field: &FieldLayout) -> TokenStream2 {
        let ident = &field.ident;
        let repr_ty = &self.definition.repr.ty;
        let mask = lit_u128(bits_mask(field.bit_width));
        let offset = lit_u32(field.offset);
        quote! {
            bits |= (((#ident as #repr_ty) & (#mask as #repr_ty)) << #offset);
        }
    }

    /// Generates the validation match arms for `from_bits`.
    fn validated_bit_arms(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| {
                let tag_value = lit_u32(variant.tag_value);
                let valid_mask = lit_u128(variant.valid_mask);
                let repr_ty = &self.definition.repr.ty;
                quote! {
                    #tag_value => {
                        if (bits & !((#valid_mask as #repr_ty))) == 0 {
                            Some(Self(bits))
                        } else {
                            None
                        }
                    }
                }
            })
            .collect()
    }

    /// Generates the match arms used by `tag()`.
    fn tag_match_arms(&self) -> Vec<TokenStream2> {
        let tag_ident = &self.definition.api.tag_ident;
        self.definition
            .variants
            .iter()
            .map(|variant| {
                let ident = &variant.ident;
                let tag_value = lit_u32(variant.tag_value);
                quote! {
                    #tag_value => #tag_ident::#ident
                }
            })
            .collect()
    }

    /// Generates the pattern side of the `match_*` helper macro.
    fn match_macro_patterns(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| {
                let ident = &variant.ident;
                let body_ident = self.body_ident(variant);
                if variant.fields.is_empty() {
                    quote! {
                        #ident => $#body_ident:expr
                    }
                } else {
                    let field_patterns = self.pattern_fields("pat", variant);
                    quote! {
                        #ident { #(#field_patterns),* $(,)? } => $#body_ident:expr
                    }
                }
            })
            .collect()
    }

    /// Generates the dispatch side of the `match_*` helper macro.
    fn match_macro_dispatch_arms(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| self.match_macro_dispatch_arm(variant))
            .collect()
    }

    /// Generates one dispatch arm for the `match_*` helper macro.
    fn match_macro_dispatch_arm(&self, variant: &VariantLayout) -> TokenStream2 {
        let tag_value = lit_u32(variant.tag_value);
        let body_ident = self.body_ident(variant);

        if variant.fields.is_empty() {
            quote! {
                #tag_value => $#body_ident
            }
        } else {
            let pattern_idents = self.binding_idents("pat", variant);
            let decoded_exprs = self.decoded_exprs(variant, &format_ident!("__bitsum_bits"));
            quote! {
                #tag_value => {
                    let (#($#pattern_idents),*) = (#(#decoded_exprs),*);
                    $#body_ident
                }
            }
        }
    }

    /// Generates all `if let` helper macro rules.
    fn if_let_rules(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| self.if_let_rule(variant))
            .collect()
    }

    /// Generates one `if let` helper rule pair.
    fn if_let_rule(&self, variant: &VariantLayout) -> TokenStream2 {
        let ident = &variant.ident;
        let tag_value = lit_u32(variant.tag_value);
        let repr_ty = &self.definition.repr.ty;
        let if_let_macro_ident = &self.definition.api.if_let_macro_ident;
        let tag_mask = lit_u128(self.definition.repr.tag_mask);

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
            let field_patterns = self.pattern_fields("if_let", variant);
            let pattern_idents = self.binding_idents("if_let", variant);
            let decoded_exprs = self.decoded_exprs(variant, &format_ident!("__bitsum_bits"));
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
    }

    /// Generates all `while let` helper macro rules.
    fn while_let_rules(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| self.while_let_rule(variant))
            .collect()
    }

    /// Generates one `while let` helper rule.
    fn while_let_rule(&self, variant: &VariantLayout) -> TokenStream2 {
        let ident = &variant.ident;
        let tag_value = lit_u32(variant.tag_value);
        let repr_ty = &self.definition.repr.ty;
        let tag_mask = lit_u128(self.definition.repr.tag_mask);

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
            let field_patterns = self.pattern_fields("while_let", variant);
            let pattern_idents = self.binding_idents("while_let", variant);
            let decoded_exprs = self.decoded_exprs(variant, &format_ident!("__bitsum_bits"));
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
    }

    /// Generates all `matches_*` helper macro rules.
    fn matches_rules(&self) -> Vec<TokenStream2> {
        self.definition
            .variants
            .iter()
            .map(|variant| self.matches_rule(variant))
            .collect()
    }

    /// Generates one `matches_*` helper rule.
    fn matches_rule(&self, variant: &VariantLayout) -> TokenStream2 {
        let ident = &variant.ident;
        let tag_value = lit_u32(variant.tag_value);
        let repr_ty = &self.definition.repr.ty;
        let tag_mask = lit_u128(self.definition.repr.tag_mask);

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
            let field_patterns = self.pattern_fields("matches", variant);
            let pattern_idents = self.binding_idents("matches", variant);
            let decoded_exprs = self.decoded_exprs(variant, &format_ident!("__bitsum_bits"));
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
    }

    /// Generates the helper body binding identifier used by `match_*`.
    fn body_ident(&self, variant: &VariantLayout) -> Ident {
        let helper_name = variant.helper_name.as_ref();
        format_ident!("__bitsum_body_{helper_name}")
    }

    /// Generates the field-pattern entries used by one helper macro rule.
    fn pattern_fields(&self, prefix: &str, variant: &VariantLayout) -> Vec<TokenStream2> {
        variant
            .fields
            .iter()
            .map(|field| {
                let field_ident = &field.ident;
                let pattern_ident = self.binding_ident(prefix, variant, field);
                quote!(#field_ident: $#pattern_ident:pat)
            })
            .collect()
    }

    /// Generates the binding identifiers used by one helper macro rule.
    fn binding_idents(&self, prefix: &str, variant: &VariantLayout) -> Vec<Ident> {
        variant
            .fields
            .iter()
            .map(|field| self.binding_ident(prefix, variant, field))
            .collect()
    }

    /// Generates the binding identifier for one decoded field pattern.
    fn binding_ident(&self, prefix: &str, variant: &VariantLayout, field: &FieldLayout) -> Ident {
        let helper_name = variant.helper_name.as_ref();
        let field_ident = &field.ident;
        format_ident!("__bitsum_pat_{prefix}_{helper_name}_{field_ident}")
    }

    /// Generates the decoded field expressions for one variant.
    fn decoded_exprs(&self, variant: &VariantLayout, bits_ident: &Ident) -> Vec<TokenStream2> {
        variant
            .fields
            .iter()
            .map(|field| self.decode_field_expr(field, bits_ident))
            .collect()
    }

    /// Generates the decoding expression for one packed field.
    fn decode_field_expr(&self, field: &FieldLayout, bits_ident: &Ident) -> TokenStream2 {
        let repr_ty = &self.definition.repr.ty;
        let offset = lit_u32(field.offset);
        let mask = lit_u128(bits_mask(field.bit_width));
        let ty = &field.ty;

        if field.kind.is_bool() {
            quote! {
                (((#bits_ident >> #offset) & (#mask as #repr_ty)) != 0)
            }
        } else {
            quote! {
                (((#bits_ident >> #offset) & (#mask as #repr_ty)) as #ty)
            }
        }
    }
}

/// Returns the widest stable visibility that can be used to re-export a local macro.
fn macro_reexport_vis(vis: &Visibility) -> Option<TokenStream2> {
    match vis {
        Visibility::Public(_) => Some(quote!(pub(crate))),
        Visibility::Restricted(_) => Some(quote!(#vis)),
        Visibility::Inherited => None,
    }
}
