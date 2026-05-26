use bitsum::bitsum;

mod inner {
    use super::bitsum;

    #[bitsum(u32)]
    pub enum Instr {
        A,
    }
}

fn main() {
    let decoded = inner::match_instr!(inner::Instr::a(), { A => 11u32 });
    assert_eq!(decoded, 11);
}
