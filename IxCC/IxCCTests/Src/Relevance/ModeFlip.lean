import IxCCTests.Src.Support
import IxCC.Src.Relevance.Check

/-! The relevance checks under application-mode flips, at the one place they compare modes.

`Relevance.Proof.ModeEq.check_modeEq` proves that `check` gives the same result on two programs equal
up to application modes (`Program.ModeEq`, which is what `Src.Lazify` changes), and `canonical_modeEq`
that `checkCanonical`'s facts transport. One comparison in the checks reads modes: `applyPis`'s loop
test `whnfType p 4 ty == ty`. On two such programs the tests disagree only when a four-step reduction
returns its input up to modes, a definition whose unfolding cycles, and then neither side reaches a
sort or a Π (`applyPis_cycle`). This part plants that cycle (engineer PE's probe):
`H : Nat → Type := λ y. H y`, `K : (x : H 0) → x 7 → Nat` (an axiom) and the root
`main := λ (x : H 0). λ (y : x 7). 1`. The classifier types `x 7` through `applyPis` at `x`'s type
`H 0`; one whnf step gives `H 0` back with the mode of `H`'s value. Flipping the modes of `H`'s
value, of `main`'s, or of both, it asserts that the loop test disagrees on the two programs, and
that `applyPis`, the classification of `K`'s type, `checkTermBinders` on `main`, `check` and
`checkCanonical` give the same results on both. -/

namespace IxCCTests.Src.Relevance.ModeFlip

open IxCC IxCC.Src IxCC.Src.Relevance IxCCTests.Src
open IxCC.Src.Relevance.Check.Canonical

def nat : Term := .const 0 []
def ty1 : Term := .sort (.succ .zero)
/-- `H 0`, applied with mode `m`. -/
def H0 (m : Mode) : Term := .app (.const 1 []) (.natLit 0) m .rel

/-- `main`'s value with its two application nodes at mode `m`. -/
def mainValue (m : Mode) : Term :=
  .lam {} (H0 m) (.lam {} (.app (.var 0) (.natLit 7) m .rel) (.natLit 1))

/-- `Nat`, `H` (its value's application at `mH`), `K`, and `main` (its applications at `mMain`). -/
def cycleProgram (mH mMain : Mode) : Program :=
  let e : Decl → ConstEntry := fun decl => { ref := default, addr := default, decl }
  { Program.ofConsts
      [ e (.induct true 0 0 0 ty1 []),
        e (.defn .defn .safe 0 (.pi {} default nat ty1) (.lam {} nat (.app (.const 1 []) (.var 0) mH .rel))),
        e (.axio true 0 (.pi {} default (H0 .strict) (.pi {} default (.app (.var 0) (.natLit 7) .strict .rel) nat))),
        e (.defn .defn .safe 0 nat (mainValue mMain)) ]
    with roots := [(default, 3)] }

/-- Canonical constant records (the classifier's telescope), and the runtime terms' node tags. -/
def cycleAnn (p : Program) : Ann :=
  let canon : CId → ConstRel := fun c =>
    match p.decl? c with
    | some d =>
      let (ps, res) := classifyTelescope p [] (d.type.piCount + 1) d.type
      { result := res.getD .rel
        params := ps.map fun (b, r?) =>
          if b.contract.uses == .erased then
            match r? with
            | some r => if r.alwaysIrr then r else Rel.prf
            | none => Rel.prf
          else r?.getD .rel }
    | none => { result := .rel, params := [] }
  { consts := NatMap.ofList ((List.range 4).map fun c => (c, canon c))
    nodes := [TermKey.value 1, TermKey.value 3].filterMap fun k => (p.termOf k).map fun t => (k, t.tagOrder) }

def checkStr (p : Program) : Except (Array RelError) Checked → String
  | .ok ch => s!"accepted; reached {ch.reached}; instances {ch.instances.length}"
  | .error es => s!"refused: {es.toList.map (·.render p)}"

def loopTest (q : Program) (t : Term) : Bool := whnfType q 4 t == t

def run (a : Assert) : IO Unit := do
  let p₀ := cycleProgram .strict .strict
  let ann := cycleAnn p₀
  let kTy := ((p₀.decl? 2).map (·.type)).getD nat
  let n := kTy.piCount + 1
  -- The unflipped program is accepted by both checks.
  let r₀ := check p₀ ann
  match r₀ with
  | .error _ => expect a false s!"cycle program: {checkStr p₀ r₀}"
  | .ok ch₀ =>
    expect a (checkCanonical p₀ ann ch₀).isEmpty
      s!"cycle program: checkCanonical {(checkCanonical p₀ ann ch₀).map (·.render p₀)}"
    for (name, mH, mMain) in [("H's value", Mode.byName, Mode.strict), ("main's value", .strict, .byName),
        ("both", .byName, .byName)] do
      let p := cycleProgram mH mMain
      let what := s!"cycle, {name} flipped"
      -- The loop test disagrees at `K`'s domain (its mode fixed by `K`'s type) or at `main`'s.
      let atK := loopTest p₀ (H0 .strict) != loopTest p (H0 .strict)
      let atMain := loopTest p₀ (H0 .strict) != loopTest p (H0 mMain)
      expect a (atK || atMain) s!"{what}: the loop test agrees at both inputs"
      expectEq a (applyPis p 16 (H0 .strict) [(.natLit 7, .strict, .rel)] == none) true
        s!"{what}: applyPis at K's input on the flipped program"
      expectEq a (applyPis p₀ 16 (H0 .strict) [(.natLit 7, .strict, .rel)] ==
          applyPis p 16 (H0 .strict) [(.natLit 7, .strict, .rel)]) true
        s!"{what}: applyPis at K's input"
      expectEq a (applyPis p₀ 16 (H0 .strict) [(.natLit 7, .strict, .rel)] ==
          applyPis p 16 (H0 mMain) [(.natLit 7, mMain, .rel)]) true
        s!"{what}: applyPis at main's input"
      expectEq a (classifyTelescope p₀ [] n kTy == classifyTelescope p [] n kTy) true
        s!"{what}: K's telescope"
      expectEq a (checkTermBinders p₀ ann [] (mainValue .strict) [] ==
          checkTermBinders p ann [] (mainValue mMain) []) true
        s!"{what}: checkTermBinders on main"
      let r := check p ann
      expectEq a (checkStr p r) (checkStr p₀ r₀) s!"{what}: check"
      expectEq a ((checkCanonical p ann ch₀).map (·.render p)) ((checkCanonical p₀ ann ch₀).map (·.render p₀))
        s!"{what}: checkCanonical"

end IxCCTests.Src.Relevance.ModeFlip
