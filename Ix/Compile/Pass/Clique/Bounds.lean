/-
  Ix.Compile.Pass.Clique.Bounds: every fuel and depth bound of the clique
  transport, named once.

  The transport is total: a walk that is not structural recursion on the
  term runs on an explicit bound and reports its exhaustion as an error (a
  refusal), never as a result. Each bound is defined here and read by name;
  no walker spells a literal. The Rust transport mirrors this table, and
  `bounds` lists it for the Lean/Rust parity test.
-/
module
@[expose] public section

namespace Ix.Compile.Pass.Clique

/-- The recursion bound of the transport's term walks (term depth plus the
nesting of the encodings), generous for any input Lean produces. -/
def transportFuel : Nat := 1000000

/-- The step bound of the weak-head reducer (`whnf`), which only unfolds
`below` types. -/
def whnfFuel : Nat := 256

/-- The bound of the definitional-equality conversions that check the
structural equation lemmas (`StructuralEq`). -/
def eqDefConversionFuel : Nat := 256

/-- The depth bound of the recovery's search through a `below` dictionary
(`Recover`). -/
def searchDepth : Nat := 64

/-- The depth bound of the well-founded equation transport's `PSigma` split
and leaf reduction (`WFConjugation`). -/
def wfDepth : Nat := 64

/-- Every bound by name, for the Lean/Rust parity test. -/
def bounds : List (String × Nat) :=
  [("transportFuel", transportFuel), ("whnfFuel", whnfFuel),
   ("eqDefConversionFuel", eqDefConversionFuel), ("searchDepth", searchDepth),
   ("wfDepth", wfDepth)]

end Ix.Compile.Pass.Clique

end
