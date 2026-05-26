//! Packed tagged-union generation for fixed-width integer representations.
//!
//! The [`bitsum`] attribute transforms an enum-like description into a compact
//! wrapper type with constructors, a tag enum, and local pattern-matching
//! macros.

#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

mod codegen;
mod ir;
mod parse;
mod support;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use syn::{ItemEnum, Result, Type, parse_macro_input};

/// Generates a packed tagged union from an enum declaration.
///
/// The attribute takes the integer representation type to use for the generated
/// wrapper, such as `u8`, `u16`, `u32`, `u64`, or `u128`.
#[proc_macro_attribute]
pub fn bitsum(attr: TokenStream, item: TokenStream) -> TokenStream {
    let repr = parse_macro_input!(attr as Type);
    let item = parse_macro_input!(item as ItemEnum);

    match compile_bitsum(repr, item) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.into_compile_error().into(),
    }
}

/// Compiles one `#[bitsum(...)]` declaration into generated Rust items.
fn compile_bitsum(repr_ty: Type, item: ItemEnum) -> Result<TokenStream2> {
    let definition = parse::parse_bitsum(repr_ty, item)?;
    Ok(codegen::generate_bitsum(&definition))
}
