import CompilatrixTests.Src.Rules
import Compilatrix.Src.Admit

/-! `Src.Admit` diagnostics (design note 01 §5, §10 part 5) on synthetic
roots: each rejection code, its reference path from the root, the decline
codes, and the accepted opaque-by-value case. -/

namespace CompilatrixTests.Src.Diagnostics

open Compilatrix Compilatrix.Src CompilatrixTests.Src CompilatrixTests.Src.Rules

/-- A root `λ x. f x` referencing `f` relevantly. -/
def rootCalling (w : World) (f : CId) : Program × CId :=
  pushConst w.p (.defn .defn .safe 0 ty (lam (app (.const f []) [.var 0]))) 5000 (root := true)

def codes : Except (Array Diag) Admitted → List String
  | .ok _ => []
  | .error ds => ds.toList.map (·.code)

def run (a : Assert) : IO Unit := do
  let w := world
  for (f, code) in [(w.thm, "relevant-theorem"), (w.ax, "relevant-axiom"), (w.unsafeDef, "unsafe"),
      (w.partialDef, "partial"), (w.opaq, "opaque"), (w.b.nat, "relevant-type"),
      (w.b.quotInd, "relevant-type")] do
    let (p, root) := rootCalling w f
    let got := codes (admit p)
    expect a (got == [code]) s!"admit: expected [{code}], got {got}"
    match admit p with
    | .error ds =>
      expect a (ds[0]!.path == [p.addr root, p.addr f]) s!"admit: {code} path from the root"
      expect a (isRejection code) s!"admit: {code} is a rejection"
    | .ok _ => pure ()
  -- An allowlisted opaque is admitted, and the closure records it.
  let (p, root) := rootCalling w w.opaqOk
  match admit p with
  | .ok ad =>
    expect a (ad.reached.contains w.opaqOk && ad.reached.contains root) "admit: opaque by value"
  | .error ds => expect a false s!"admit: opaque by value rejected: {ds.map toString}"
  -- A string literal in a relevant position is declined.
  let (p, _) := pushConst w.p (.defn .defn .safe 0 ty (.strLit "hello")) 6000 (root := true)
  expect a (codes (admit p) == ["unsupported"]) s!"admit: string declined, got {codes (admit p)}"
  expect a (!isRejection "unsupported" && !isRejection "budget") "admit: decline codes"
  -- An irrelevant reference to a theorem is not reached.
  let (p, _) := pushConst w.p (.defn .defn .safe 0 ty (.app (lam (.natLit 1)) (.const w.thm []) .irr))
    7000 (root := true)
  expect a (codes (admit p) == []) "admit: an irrelevant theorem is not reached"
  -- The size budget declines.
  let (p, _) := rootCalling w w.ident
  expect a (codes (admit p (cfg := { maxConsts := 1 })) == ["budget"]) "admit: budget"

/-- The ix-compiled diagnostics fixture (`fixtures/ixon-v3/src-diag/`): each
root, loaded alone, gets its expected outcome through the whole pipeline. -/
def ixFixture (a : Assert) : IO (Array String) := do
  let dir := fixtures / "src-diag"
  let bytes ← IO.FS.readBinFile (dir / "diag.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "diag.equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let mut out := #[]
  for (name, expected) in [("SrcDiag.rootPartial", "opaque"), ("SrcDiag.rootMixHash", "opaque"),
      ("SrcDiag.rootFloat", ""), ("SrcDiag.rootClassical", "relevant-axiom"),
      ("SrcDiag.rootSorry", "relevant-axiom"), ("SrcDiag.rootOpaqueId", "")] do
    let roots := hints.roots.filter (·.2 == some name)
    expect a (roots.size == 1) s!"diag: root {name} recorded"
    match loadEnv { typecheck := false } env { hints with roots } with
    | .error d =>
      expect a (d.code == expected) s!"diag: {name} gave {d.code}, expected {expected}: {d.message}"
      out := out.push s!"{name}: {d.code} ({d.message.take 120})"
    | .ok l =>
      let kinds := l.admitted.reached.toList.map fun c =>
        s!"{l.program.short c}:{((l.program.decl? c).map Decl.kindName).getD "?"}"
      expect a expected.isEmpty s!"diag: {name} admitted, expected {expected}; closure {kinds}"
      if name == "SrcDiag.rootOpaqueId" then
        let some root := l.root? | throw (IO.userError s!"{name}: no root")
        let r ← runRoot l.program 1000 root [41]
        expect a (natOf r == some 42) s!"diag: {name} 41 gave {outcome r}"
        out := out.push s!"{name}: admitted; 41 ↦ 42"
      else out := out.push s!"{name}: admitted (closure of {l.admitted.reached.size} constants)"
  return out

end CompilatrixTests.Src.Diagnostics
