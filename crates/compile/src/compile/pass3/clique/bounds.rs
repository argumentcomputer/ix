//! Every fuel and depth bound of the clique transport, named once (a port of
//! `Ix/Compile/Pass/Clique/Bounds.lean`).
//!
//! The transport is total: a walk that is not structural recursion on the
//! term runs on an explicit bound and reports its exhaustion as an error (a
//! refusal), never as a result. Each bound is defined here and read by name;
//! no walker spells a literal. [`bounds`] lists them for the Lean/Rust parity
//! test.

/// The recursion bound of the transport's term walks (term depth plus the
/// nesting of the encodings), generous for any input Lean produces.
pub const TRANSPORT_FUEL: usize = 1_000_000;

/// The step bound of the weak-head reducer (`whnf`), which only unfolds
/// `below` types.
pub const WHNF_FUEL: usize = 256;

/// The bound of the definitional-equality conversions that check the
/// structural equation lemmas (`StructuralEq`).
pub const EQ_DEF_CONVERSION_FUEL: usize = 256;

/// The depth bound of the recovery's search through a `below` dictionary
/// (`Recover`).
pub const SEARCH_DEPTH: usize = 64;

/// The depth bound of the well-founded equation transport's `PSigma` split
/// and leaf reduction (`WFConjugation`).
pub const WF_DEPTH: usize = 64;

/// The bound on `k` when the clique table reads a member's equation lemmas
/// `m.eq_k` (`member_eq_lemmas`): they are read while present, for `k` below
/// it.
pub const EQ_LEMMA_BOUND: usize = 1_000_000;

/// The number of names `encoding_owner` looks up: the name itself and its
/// nearest prefixes.
pub const ENCODING_OWNER_DEPTH: usize = 64;

/// Every bound by its Lean name, in the order of Lean's `bounds`, for the
/// Lean/Rust parity test.
pub fn bounds() -> [(&'static str, usize); 7] {
  [
    ("transportFuel", TRANSPORT_FUEL),
    ("whnfFuel", WHNF_FUEL),
    ("eqDefConversionFuel", EQ_DEF_CONVERSION_FUEL),
    ("searchDepth", SEARCH_DEPTH),
    ("wfDepth", WF_DEPTH),
    ("eqLemmaBound", EQ_LEMMA_BOUND),
    ("encodingOwnerDepth", ENCODING_OWNER_DEPTH),
  ]
}

#[cfg(test)]
mod tests {
  use super::bounds;

  #[test]
  fn bounds_table_matches_lean() {
    assert_eq!(
      bounds(),
      [
        ("transportFuel", 1_000_000),
        ("whnfFuel", 256),
        ("eqDefConversionFuel", 256),
        ("searchDepth", 64),
        ("wfDepth", 64),
        ("eqLemmaBound", 1_000_000),
        ("encodingOwnerDepth", 64),
      ]
    );
  }
}
