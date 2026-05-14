//! Integration tests for the generated packed tagged-union API.

use bitsum::bitsum;

#[bitsum(u32)]
pub enum Instr {
    /// A no-op instruction.
    Nop,

    /// Loads an immediate.
    Imm {
        /// The destination register.
        #[bits(5)]
        dst: u8,

        /// The immediate byte.
        #[bits(8)]
        value: u8,
    },

    /// Adds two registers.
    Add {
        /// The destination register.
        #[bits(5)]
        dst: u8,

        /// The left operand register.
        #[bits(5)]
        lhs: u8,

        /// The right operand register.
        #[bits(5)]
        rhs: u8,
    },
}

#[test]
fn constructors_pack_expected_bits() {
    assert_eq!(Instr::nop().bits(), 0);
    assert_eq!(Instr::imm(3, 0xaa).bits(), 1 | (3 << 2) | (0xaa << 7));
    assert_eq!(
        Instr::add(1, 2, 3).bits(),
        2 | (1 << 2) | (2 << 7) | (3 << 12)
    );
}

#[test]
fn accessors_decode_payload_fields() {
    let instr = Instr::add(17, 9, 4);
    assert_eq!(instr.add_dst(), 17);
    assert_eq!(instr.add_lhs(), 9);
    assert_eq!(instr.add_rhs(), 4);
}

#[test]
fn from_bits_accepts_valid_encoding() {
    let instr = Instr::from_bits(1 | (3 << 2) | (0xaa << 7));
    assert_eq!(instr, Some(Instr::imm(3, 0xaa)));
}

#[test]
fn from_bits_rejects_unknown_tag_values() {
    assert_eq!(Instr::from_bits(3), None);
}

#[test]
fn from_bits_rejects_reserved_payload_bits() {
    assert_eq!(Instr::from_bits(1 << 2), None);
}

#[test]
fn from_bits_unchecked_preserves_valid_encoding() {
    let instr = unsafe { Instr::from_bits_unchecked(2 | (1 << 2) | (2 << 7) | (3 << 12)) };
    assert_eq!(instr.tag(), InstrTag::Add);
}

#[test]
fn constructors_reject_values_that_do_not_fit() {
    let panic = std::panic::catch_unwind(|| Instr::imm(32, 0));
    assert!(panic.is_err());
}

#[test]
fn match_macro_dispatches_and_binds_fields() {
    let decoded = match_instr!(Instr::imm(7, 9), {
        Nop => { 0 },
        Imm { dst, value } => { dst as u32 + value as u32 },
        Add { dst, lhs, rhs } => { dst as u32 + lhs as u32 + rhs as u32 },
    });
    assert_eq!(decoded, 16);
}
