import Aiur.Library.Blake3

namespace AiurBlake3Tests
open Aiur

def benchmark : Modules.Program Nat := aiur_library% Library.Blake3.templates "
module Benchmark {
    fn generate(length: Field, byte: UInt8::U8) -> Blake3::ByteStream {
        match length {
            0 => &Lists::Node::Nil,
            _ => {
                let (next, _) = UInt8::split_sum(UInt8::to_field(byte) + 1);
                let tail = generate(length - 1, next);
                &Lists::Node::Cons(byte, tail)
            },
        }
    }
    fn main() -> Blake3::Digest { Blake3::hash(generate(1025, UInt8::BYTE_0)) }
    fn hash(length: Field) -> [Field; 32] {
        Blake3::address_to_fields(Blake3::digest_bytes(Blake3::hash(generate(length, UInt8::BYTE_0))))
    }
}"

end AiurBlake3Tests
