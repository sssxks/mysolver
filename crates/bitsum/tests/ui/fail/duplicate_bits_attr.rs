use bitsum::bitsum;

#[bitsum(u32)]
enum Instr {
    Imm {
        #[bits(3)]
        #[bits(4)]
        value: u8,
    },
}

fn main() {}
