//! Shared low-level helpers used by parsing and code generation.

use proc_macro2::Span;
use syn::LitInt;

/// Converts a positive bit width into a bit mask.
pub(crate) const fn bits_mask(width: u32) -> u128 {
    match width {
        0 => 0,
        128 => u128::MAX,
        _ => (1u128 << width) - 1,
    }
}

/// Computes `ceil(log2(value))`, with `0` for `value <= 1`.
pub(crate) const fn ceil_log2(value: usize) -> u32 {
    match value {
        0 | 1 => 0,
        _ => usize::BITS - (value - 1).leading_zeros(),
    }
}

/// Builds a literal `u32` token.
pub(crate) fn lit_u32(value: u32) -> LitInt {
    LitInt::new(&value.to_string(), Span::call_site())
}

/// Builds a literal `u128` token.
pub(crate) fn lit_u128(value: u128) -> LitInt {
    LitInt::new(&value.to_string(), Span::call_site())
}

/// Converts a Rust-style identifier to snake case for generated helper names.
pub(crate) fn to_snake_case(name: &str) -> Box<str> {
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

    out.into_boxed_str()
}
