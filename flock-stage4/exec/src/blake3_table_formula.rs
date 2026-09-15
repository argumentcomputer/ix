//! Compact linear formulas for the PINNED Option-F BLAKE3 base matrices.
//!
//! The reference is Flock b310f35f's r1cs_hashes/blake3.rs (SHA-256
//! 47dc4afcfca3d8f19f5ced5696d7ab192dde8902f94280a93bceed037d9f648f).
//! This ports only its public layout and linear row construction, not the
//! hash witness generator or a new Stage 3 table. The parent must check every
//! resulting coefficient against the approved registry before exposing it.

use flock_prover::r1cs_hashes::blake3 as b;
use ix_stage4_trace::{
  BinaryLinearMapError, BinaryLinearMapLimitsV0, BinaryLinearMapV0,
  BinaryLinearReferenceV0 as Ref,
};
use std::collections::HashMap;

type Word = [Ref; b::WORD_BITS];
type Result<T> = std::result::Result<T, BinaryLinearMapError>;

fn input(index: usize) -> Ref {
  Ref::Input(u32::try_from(index).expect("fixed BLAKE3 layout fits u32"))
}
fn word(base: usize) -> Word {
  core::array::from_fn(|i| input(base + i))
}
fn constant(value: u32) -> Word {
  core::array::from_fn(|i| {
    if value >> i & 1 != 0 { input(b::Z_CONST_POS) } else { Ref::Zero }
  })
}
fn rotate(word: &Word, rotation: usize) -> Word {
  core::array::from_fn(|i| word[(i + rotation) % b::WORD_BITS])
}

struct Builder {
  xors: Vec<(Ref, Ref)>,
  pairs: HashMap<(Ref, Ref), u32>,
  a: Vec<Ref>,
  b: Vec<Ref>,
  limit: u32,
}

impl Builder {
  fn xor(&mut self, a: Ref, b: Ref) -> Result<Ref> {
    if a == b {
      return Ok(Ref::Zero);
    }
    if a == Ref::Zero {
      return Ok(b);
    }
    if b == Ref::Zero {
      return Ok(a);
    }
    let pair = (a.min(b), a.max(b));
    if let Some(&i) = self.pairs.get(&pair) {
      return Ok(Ref::Xor(i));
    }
    if self.xors.len() as u64 >= u64::from(self.limit) {
      return Err(BinaryLinearMapError::SizeLimit);
    }
    let i = u32::try_from(self.xors.len())
      .map_err(|_| BinaryLinearMapError::SizeLimit)?;
    self.xors.push(pair);
    self.pairs.insert(pair, i);
    Ok(Ref::Xor(i))
  }
  fn xor_word(&mut self, a: &Word, b: &Word) -> Result<Word> {
    let mut result = [Ref::Zero; b::WORD_BITS];
    for i in 0..b::WORD_BITS {
      result[i] = self.xor(a[i], b[i])?;
    }
    Ok(result)
  }
  fn row(&mut self, row: usize, a: Ref, b: Ref) {
    self.a[row] = a;
    self.b[row] = b;
  }

  /// Carry-only two-operand sum: product_i=(x_i+carry_i)(y_i+carry_i),
  /// sum_i=x_i+y_i+carry_i, carry_i=sum_{j<i} product_j.
  fn add(&mut self, x: &Word, y: &Word, base: usize) -> Result<Word> {
    let mut result = [Ref::Zero; b::WORD_BITS];
    let mut carry = Ref::Zero;
    for i in 0..b::WORD_BITS {
      let a = self.xor(x[i], carry)?;
      result[i] = self.xor(a, y[i])?;
      if i < b::CARRY_BITS_PER_ADD {
        let right = self.xor(y[i], carry)?;
        self.row(base + i, a, right);
        carry = self.xor(carry, input(base + i))?;
      }
    }
    Ok(result)
  }

  /// Fused carry-save/ripple sum, retaining shared partial sums and prefixes
  /// as XOR nodes instead of expanding the cascade at every use.
  fn fused(
    &mut self,
    x: &Word,
    y: &Word,
    m: &Word,
    maj: usize,
    rip: usize,
  ) -> Result<Word> {
    let mut result = [Ref::Zero; b::WORD_BITS];
    let mut carry = Ref::Zero;
    for i in 0..b::WORD_BITS {
      let left = self.xor(x[i], m[i])?;
      let partial = self.xor(left, y[i])?;
      if i < b::CARRY_BITS_PER_ADD {
        let right = self.xor(y[i], m[i])?;
        self.row(maj + i, left, right);
      }
      if i == 0 {
        result[i] = partial;
      } else {
        let shifted = self.xor(input(maj + i - 1), m[i - 1])?;
        let left = self.xor(partial, carry)?;
        result[i] = self.xor(left, shifted)?;
        if i <= b::RIPPLE_BITS_PER_FADD {
          let right = self.xor(shifted, carry)?;
          self.row(rip + i - 1, left, right);
          carry = self.xor(carry, input(rip + i - 1))?;
        }
      }
    }
    Ok(result)
  }

  /// The first four column Gs use an IV-word constant. Its set bits are
  /// coefficients of the table's z_const INPUT, never a literal field one.
  fn constant_add(
    &mut self,
    k: u32,
    y: &Word,
    base: usize,
    rows: usize,
  ) -> Result<Word> {
    let first = b::CARRY_BITS_PER_ADD - rows;
    debug_assert!(first > 0 && k.trailing_zeros() as usize == first - 1);
    let k = constant(k);
    let mut carry = Ref::Zero;
    let mut result = [Ref::Zero; b::WORD_BITS];
    for i in 0..b::WORD_BITS {
      if i == first {
        carry = y[first - 1];
      }
      let left = self.xor(k[i], carry)?;
      result[i] = self.xor(left, y[i])?;
      if i >= first && i < b::CARRY_BITS_PER_ADD {
        let right = self.xor(y[i], carry)?;
        self.row(base + i - first, left, right);
        carry = self.xor(carry, input(base + i - first))?;
      }
    }
    Ok(result)
  }
}

pub(super) fn compile(
  limits: BinaryLinearMapLimitsV0,
) -> Result<[BinaryLinearMapV0; 2]> {
  let inputs =
    u32::try_from(b::K).map_err(|_| BinaryLinearMapError::SizeLimit)?;
  if u64::from(limits.inputs) < b::K as u64
    || u64::from(limits.outputs) < b::K as u64
  {
    return Err(BinaryLinearMapError::SizeLimit);
  }
  let mut build = Builder {
    xors: Vec::new(),
    pairs: HashMap::new(),
    a: vec![Ref::Zero; b::K],
    b: vec![Ref::Zero; b::K],
    limit: limits.xors,
  };
  build.row(b::Z_CONST_POS, input(b::Z_CONST_POS), input(b::Z_CONST_POS));
  for (base, count) in
    [(b::CV_BASE, 256), (b::M_BASE, 512), (b::T_LO_BASE, 128)]
  {
    for i in base..base + count {
      build.row(i, input(i), input(b::Z_CONST_POS));
    }
  }
  let mut state = core::array::from_fn::<_, 16, _>(|lane| match lane {
    0..=7 => word(b::CV_BASE + 32 * lane),
    8..=11 => constant(b::BLAKE3_IV[lane - 8]),
    _ => word(b::T_LO_BASE + 32 * (lane - 12)),
  });
  let mut permutation = core::array::from_fn::<_, 16, _>(|i| i);
  for round in 0..b::N_ROUNDS {
    for local in 0..b::N_G_PER_ROUND {
      let g = round * b::N_G_PER_ROUND + local;
      let base = b::G_BASE[g];
      let c1_rows = b::g_c1_rows(g);
      let [la, lb, lc, ld] = b::G_LANES[local];
      let [mx, my] = b::G_MSG_IDX[local];
      let mx = word(b::M_BASE + 32 * permutation[mx]);
      let my = word(b::M_BASE + 32 * permutation[my]);
      let [a, bv, c, d] = [state[la], state[lb], state[lc], state[ld]];
      let a1 = build.fused(&a, &bv, &mx, base, base + 31)?;
      let d1 = rotate(&build.xor_word(&d, &a1)?, 16);
      let c1 = if g < 4 {
        build.constant_add(b::BLAKE3_IV[g], &d1, base + 61, c1_rows)?
      } else {
        build.add(&c, &d1, base + 61)?
      };
      let b1 = rotate(&build.xor_word(&bv, &c1)?, 12);
      let a2 =
        build.fused(&a1, &b1, &my, base + 61 + c1_rows, base + 92 + c1_rows)?;
      let d2 = rotate(&build.xor_word(&d1, &a2)?, 8);
      let c2 = build.add(&c1, &d2, base + 122 + c1_rows)?;
      let b2 = rotate(&build.xor_word(&b1, &c2)?, 7);
      state[la] = a2;
      state[lb] = b2;
      state[lc] = c2;
      state[ld] = d2;
    }
    permutation = core::array::from_fn(|i| permutation[b::MSG_PERMUTATION[i]]);
  }
  for i in 0..8 {
    let low = build.xor_word(&state[i], &state[i + 8])?;
    let high = build.xor_word(&state[i + 8], &word(b::CV_BASE + 32 * i))?;
    for bit in 0..32 {
      build.row(b::OUT_LO_BASE + 32 * i + bit, low[bit], input(b::Z_CONST_POS));
      build.row(
        b::OUT_HI_BASE + 32 * i + bit,
        high[bit],
        input(b::Z_CONST_POS),
      );
    }
  }
  Ok([
    BinaryLinearMapV0::compile(inputs, build.xors.clone(), build.a, limits)?,
    BinaryLinearMapV0::compile(inputs, build.xors, build.b, limits)?,
  ])
}
