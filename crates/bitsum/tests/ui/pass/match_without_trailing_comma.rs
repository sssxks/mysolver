use bitsum::bitsum;

#[bitsum(u32)]
enum Instr {
    A,
}

fn main() {
    let decoded = match_instr!(Instr::a(), { A => 7u32 });
    assert_eq!(decoded, 7);
}
