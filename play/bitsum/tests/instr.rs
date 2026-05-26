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
        Nop => 0,
        Imm { dst: dst, value: value } => dst as u32 + value as u32,
        Add { dst: dst, lhs: lhs, rhs: rhs } => dst as u32 + lhs as u32 + rhs as u32,
    });
    assert_eq!(decoded, 16);
}

#[test]
fn if_let_macro_matches_and_binds_fields() {
    let decoded;

    if_let_instr!( let Imm { dst: dst, value: value } = Instr::imm(4, 6) => {
            decoded = dst as u32 + value as u32;
        } else {
            decoded = u32::MAX;
        }
    );

    assert_eq!(decoded, 10);
}

#[test]
fn if_let_macro_runs_else_for_tag_mismatch() {
    let matched;

    if_let_instr!(
        let Add {
            dst: _dst,
            lhs: _lhs,
            rhs: _rhs,
        } = Instr::nop() => {
            matched = true;
        } else {
            matched = false;
        }
    );

    assert!(!matched);
}

#[test]
fn while_let_macro_rechecks_the_scrutinee() {
    let values = [Instr::imm(1, 10), Instr::imm(2, 11), Instr::nop()];
    let mut index = 0usize;
    let mut sum = 0u32;

    while_let_instr!(
        let Imm {
            dst: dst,
            value: value,
        } = values[index] => {
            sum += dst as u32 + value as u32;
            index += 1;
        }
    );

    assert_eq!(sum, 24);
    assert_eq!(index, 2);
}

#[test]
fn matches_macro_supports_patterns_and_guards() {
    assert!(matches_instr!(
        Instr::add(3, 3, 7),
        Add {
            dst: 3,
            lhs: lhs,
            rhs: _,
        } if lhs == 3,
    ));
    assert!(!matches_instr!(
        Instr::imm(2, 9),
        Add {
            dst: _,
            lhs: _,
            rhs: _,
        },
    ));
}

#[test]
fn generated_macros_are_hygienic() {
    let __bitsum_instr = 100u32;
    let __bitsum_bits = 200u32;
    let __bitsum_pat_imm_dst = 300u32;
    let __bitsum_pat_imm_value = 400u32;

    let total = match_instr!(Instr::imm(5, 6), {
        Nop => 0,
        Imm {
            dst: __bitsum_bits,
            value: __bitsum_pat_imm_value,
        } => __bitsum_instr + __bitsum_bits as u32 + __bitsum_pat_imm_value as u32,
        Add {
            dst: dst,
            lhs: lhs,
            rhs: rhs,
        } => dst as u32 + lhs as u32 + rhs as u32,
    });

    assert_eq!(total, 111);
    assert_eq!(__bitsum_bits, 200);
    assert_eq!(__bitsum_pat_imm_dst, 300);
}
