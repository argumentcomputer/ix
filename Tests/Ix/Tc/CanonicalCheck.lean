module

public import LSpec
public import Ix.Tc

/-!
Unit tests for the kernel's primary-block canonicity gate
(`Ix.Tc.validateCanonicalBlockSinglePass`), mirroring the Rust tests in
`crates/kernel/src/canonical_check.rs`:

- the BELOW-ORDER shape (A6f, `Tests/Ix/Compile/ValidateLeanSwap.lean`):
  `SA.mk : SB → X → SA`, `SB.mk : SA → Y → SB`, whose cross references compare
  weakly `gt` under the singleton partition in *both* stored orders. The
  refinement's order is accepted (the weak `gt` falls back to the full check);
  the other order is rejected by the full check;
- a strong `gt` (wrong order decided without the partition) is rejected at the
  single pass.
-/

public section

namespace Tests.Tc.CanonicalCheck

open LSpec
open Ix.Tc

abbrev AE := KExpr .anon

def aId (s : String) : KId .anon := ⟨Address.blake3 s.toUTF8, ()⟩

def cnst (s : String) : AE := KExpr.mkConst (aId s) #[]

def arrow (a b : AE) : AE := KExpr.mkAll () () a b

def sort0 : AE := .mkSort .mkZero

def indc (_s : String) (params : UInt64) (ctors : Array String) : KConst .anon :=
  .indc () () 0 params 0 false (aId "blk") 0 sort0 (ctors.map aId) ()

def ctor (ind : String) (fields : UInt64) (ty : AE) : KConst .anon :=
  .ctor () () false 0 (aId ind) 0 0 fields ty

/-- The swap pair's constructors. -/
def swapResolve : ResolveCtor .anon := fun id =>
  if id == aId "SA.mk" then some (ctor "SA" 2 (arrow (cnst "SB") (arrow (cnst "X") (cnst "SA"))))
  else if id == aId "SB.mk" then some (ctor "SB" 2 (arrow (cnst "SA") (arrow (cnst "Y") (cnst "SB"))))
  else none

def sa : KId .anon × KConst .anon := (aId "SA", indc "SA" 0 #["SA.mk"])
def sb : KId .anon × KConst .anon := (aId "SB", indc "SB" 0 #["SB.mk"])

/-- The swap pair in the full refinement's order. -/
def swapCanonical : Except String (Array (KId .anon × KConst .anon)) :=
  match sortKConstsWithSeedKey swapResolve (fun id _ => defaultSeedKey id) #[sa, sb] with
  | .ok classes =>
    if classes.size != 2 then .error "the swap pair collapsed"
    else .ok (classes.map (·[0]!))
  | .error _ => .error "refinement failed"

/-- The singleton-partition comparison of a stored order's first pair. -/
def firstPair (ms : Array (KId .anon × KConst .anon)) : Option SOrd :=
  match compareKConst (KMutCtx.fromIdPairs ms) swapResolve ms[0]!.2 ms[1]!.2 with
  | .ok so => some so
  | .error _ => none

def accepts (ms : Array (KId .anon × KConst .anon)) (r : ResolveCtor .anon) : Bool :=
  match validateCanonicalBlockSinglePass (Address.blake3 "blk".toUTF8) r ms with
  | .ok () => true
  | .error _ => false

/-- Require the intended rejection, rather than accepting an unrelated error. -/
def rejectsAs (ms : Array (KId .anon × KConst .anon)) (r : ResolveCtor .anon)
    (ord : Ordering) : Bool :=
  match validateCanonicalBlockSinglePass (Address.blake3 "blk".toUTF8) r ms with
  | .error (.nonCanonicalBlock _ 0 actual) => actual == ord
  | _ => false

/-- Cross references alone are alpha-equivalent under full refinement. -/
def equalCrossResolve : ResolveCtor .anon := fun id =>
  if id == aId "SA.mk" then some (ctor "SA" 1 (arrow (cnst "SB") (cnst "SA")))
  else if id == aId "SB.mk" then some (ctor "SB" 1 (arrow (cnst "SA") (cnst "SB")))
  else none

def suite : List TestSeq :=
  match swapCanonical with
  | .error e => [test s!"swap pair refinement: {e}" false]
  | .ok can =>
    let rev := can.reverse
    [ test "canonical swap pair: weak gt under its singleton partition"
        (firstPair can == some ⟨false, .gt⟩)
      ++ test "canonical swap pair accepted (weak gt falls back to the full check)"
        (accepts can swapResolve)
      ++ test "reversed swap pair: weak gt too"
        (firstPair rev == some ⟨false, .gt⟩)
      ++ test "reversed swap pair rejected by the full check"
        (rejectsAs rev swapResolve .gt)
      ++ test "strong gt (params 2 before 1) rejected"
        (rejectsAs #[(aId "A", indc "A" 2 #[]), (aId "B", indc "B" 1 #[])] (fun _ => none) .gt)
      ++ test "uncollapsed equal members rejected"
        (rejectsAs #[(aId "A", indc "A" 1 #[]), (aId "B", indc "B" 1 #[])] (fun _ => none) .eq)
      ++ test "weak gt cross references still reject an uncollapsed equal class"
        (rejectsAs #[sa, sb] equalCrossResolve .eq)
      ++ test "strong lt (params 1 before 2) accepted"
        (accepts #[(aId "A", indc "A" 1 #[]), (aId "B", indc "B" 2 #[])] (fun _ => none)) ]

end Tests.Tc.CanonicalCheck

end
