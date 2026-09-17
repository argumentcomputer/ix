//! Untrusted scalar advice. Inverses keep using the existing gate evaluator.
use crate::{
  extension::goldilocks_ext2_mul,
  goldilocks::{GOLDILOCKS_MODULUS as P, goldilocks_add},
  ixby::ixbf::Primitive,
};
use flock_prover::field::F128;

pub(super) fn primitive(header: F128, args: &[F128]) -> Option<Primitive> {
  let p = Primitive::from_opcode((header.lo >> 24) as u8)?;
  if args.len() != 6
    || (header.lo >> 8) as u8 != 0
    || (header.lo >> 16) as u8 != 1
    || (header.lo >> 32) as u8 as usize != p.arity()
    || (header.lo >> 40) as u8 as usize != p.arity()
    || args[2 * p.arity()..].iter().any(|&v| v != F128::ZERO)
  {
    return None;
  }
  Some(p)
}
pub(super) fn scalar(p: Primitive, args: &[F128]) -> Option<[F128; 2]> {
  use Primitive::*;
  let tag = match p {
    Word32Add | Word32Sub | Word32Mul | Word32And | Word32Or | Word32Xor
    | Word32Shl | Word32Shr | Word32Rotr | Word32Eq | Word32Lt
    | Word32ToField => 2,
    FieldAdd | FieldSub | FieldMul | FieldEq | ExtensionPack => 3,
    ExtensionAdd | ExtensionSub | ExtensionMul | ExtensionEq
    | ExtensionFirst | ExtensionSecond => 4,
    _ => return None,
  };
  for value in args[..2 * p.arity()].as_chunks::<2>().0 {
    if value[0] != F128::new(tag, 0)
      || match tag {
        2 => value[1].hi != 0 || value[1].lo > u64::from(u32::MAX),
        3 => value[1].hi != 0 || value[1].lo >= P,
        4 => value[1].lo >= P || value[1].hi >= P,
        _ => unreachable!(),
      }
    {
      return None;
    }
  }
  let a = args[1];
  let b = args[3];
  let word = |n: u32| [F128::new(2, 0), F128::new(u64::from(n), 0)];
  let boolean = |b: bool| [F128::ONE, F128::new(u64::from(b), 0)];
  let (wa, wb) = (a.lo as u32, b.lo as u32);
  let neg = |n| if n == 0 { 0 } else { P - n };
  Some(match p {
    Word32Add => word(wa.wrapping_add(wb)),
    Word32Sub => word(wa.wrapping_sub(wb)),
    Word32Mul => word(wa.wrapping_mul(wb)),
    Word32And => word(wa & wb),
    Word32Or => word(wa | wb),
    Word32Xor => word(wa ^ wb),
    Word32Shl => word(wa.checked_shl(wb).unwrap_or(0)),
    Word32Shr => word(wa.checked_shr(wb).unwrap_or(0)),
    Word32Rotr => word(wa.rotate_right(wb)),
    Word32Eq | FieldEq | ExtensionEq => boolean(a == b),
    Word32Lt => boolean(wa < wb),
    Word32ToField => [F128::new(3, 0), a],
    FieldAdd | ExtensionAdd => [
      F128::new(tag, 0),
      F128::new(goldilocks_add(a.lo, b.lo), goldilocks_add(a.hi, b.hi)),
    ],
    FieldSub | ExtensionSub => [
      F128::new(tag, 0),
      F128::new(
        goldilocks_add(a.lo, neg(b.lo)),
        goldilocks_add(a.hi, neg(b.hi)),
      ),
    ],
    FieldMul | ExtensionMul => [F128::new(tag, 0), goldilocks_ext2_mul(a, b)],
    ExtensionPack => [F128::new(4, 0), F128::new(a.lo, b.lo)],
    ExtensionFirst => [F128::new(3, 0), F128::new(a.lo, 0)],
    ExtensionSecond => [F128::new(3, 0), F128::new(a.hi, 0)],
    _ => return None,
  })
}
