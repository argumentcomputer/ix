import IxCCTests.Src.StuckEval
import IxCCTests.Fixtures.SortPoly

/-! Level-exact relevance (D18) on ix-compiled sort-polymorphic code
(`fixtures/ixon-v4/src-sortpoly`): every covered root loads through the whole front end and
evaluates without getting stuck, matching the same Lean source compiled
natively (the test module `IxCCTests.Fixtures.SortPoly`); the level-blind
annotation the annotator once produced (a proof under a universe condition
counted as relevant)
is rejected by the checker and makes the unchecked run stuck, as it did
before D18; and the one case level-exact relevance does not cover, a *type*
reaching a relevant parameter (`typeArg`), is rejected by C2 and stays a
stuck run with a relevance cause when unchecked. -/

namespace IxCCTests.Src.SortPoly

open IxCC IxCC.Src IxCC.Src.Relevance IxCCTests.Src
open IxCCTests.Src.StuckEval (Cause Stop)

/-- `PUnit.rec` has no compiled code, so its value comes from the kernel:
this is checked by definitional unfolding when the test is built. -/
theorem punitRec_eq (n : Nat) : _root_.SortPoly.punitRec n = n + 5 := rfl

def dir : System.FilePath := fixtures / "src-sortpoly"

/-- The root that level-exact relevance does not cover: a type reaches a
relevant parameter of a type-polymorphic callee. -/
def typeRoot : String := "SortPoly.typeArg"

/-- The pack's environment and sidecar. -/
def pack : IO (IxCC.Ixon.V3.Env × Hints) := do
  let bytes ← IO.FS.readBinFile (dir / "sortpoly.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "sortpoly.equations.json")))
  return (← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes), ← IO.ofExcept (Hints.ofK1Json json))

/-- The native value of each root. -/
def native : String → Option (Nat → Nat)
  | "SortPoly.comp" => some _root_.SortPoly.comp
  | "SortPoly.throughRoot" => some _root_.SortPoly.throughRoot
  | "SortPoly.punitCases" => some _root_.SortPoly.punitCases
  | "SortPoly.punitCasesType" => some _root_.SortPoly.punitCasesType
  | "SortPoly.punitRec" => some (· + 5)
  | "SortPoly.unitBoth" => some _root_.SortPoly.unitBoth
  | "SortPoly.sigmaRoot" => some _root_.SortPoly.sigmaRoot
  | _ => none

def clock : Nat := 10000

/-- The level-blind annotation: a proof under a proper universe condition is
relevant (the annotator's `isPropType` answered false for `Sort u`). -/
def blindRel : Rel → Rel
  | .proof (.allZero []) => Rel.prf
  | .proof _ => .rel
  | r => r

def blindField : FieldClass → FieldClass
  | .proof (.allZero []) => FieldClass.prf
  | .proof _ => .keep
  | c => c

def blindTag : Tag → Tag
  | .lam r pw => .lam (blindRel r) pw
  | .arg r => .arg (blindRel r)
  | .letE r => .letE (blindRel r)

def blindAnn (ann : Ann) : Ann :=
  { consts := ann.consts.map fun c =>
      { result := blindRel c.result, params := c.params.map blindRel }
    ctors := ann.ctors.map fun c => { fields := c.fields.map blindField }
    nodes := ann.nodes.map fun (k, tags) => (k, tags.map blindTag) }

/-- The level-blind `RecKind`: subsingleton only for a family literally in `Prop`. -/
def blindProgram (p : Program) : Program :=
  { p with table := { p.table with recKind := p.table.recKind.map fun
      | .subsingleton (.allZero []) fs => .subsingleton .always fs
      | .subsingleton .. => .ordinary
      | k => k } }

def run (a : Assert) : IO (Array String) := do
  let mut out := #[]
  let (env, hints) ← pack
  let cfg : LoadConfig := {}
  let covered := hints.roots.filter (·.2 != some typeRoot)
  let l ← match loadEnv cfg env { hints with roots := covered } with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"src-sortpoly: {d}")
  let p := l.program
  -- Every covered root evaluates and matches native Lean.
  for (addr, c) in p.roots do
    let name := (Loaded.names l.hints addr).getD (p.short c)
    let some f := native name | throw (IO.userError s!"src-sortpoly: no native twin for {name}")
    for n in List.range 21 do
      let r ← runRoot p clock c [n]
      expect a (natOf r == some (f n)) s!"{name} {n}: SrcEval {outcome r}, Lean {f n}"
    out := out.push s!"{name}: matches native Lean on 0–20"
  -- The type case: C2 rejects it (a type for a parameter relevant at the
  -- instance), and unchecked it is stuck applying `irr`.
  let typeOnly := hints.roots.filter (·.2 == some typeRoot)
  match loadEnv cfg env { hints with roots := typeOnly } with
  | .error d => expect a (d.code == "relevance-C2") s!"{typeRoot}: rejected with {d.code}"
  | .ok _ => expect a false s!"{typeRoot}: accepted, but no universe condition covers it"
  let (p0, k0, _, _) ← IO.ofExcept ((prepare cfg env { hints with roots := typeOnly }).mapError toString)
  let ann ← IO.ofExcept (k0.annotateChecked p0)
  let pT := Lazify.run (← IO.ofExcept (install p0 ann)) (ann.nodes.map (·.1))
  let some (_, tc) := p0.roots[0]? | throw (IO.userError s!"{typeRoot}: no root")
  for n in List.range 3 do
    let s := StuckEval.run pT clock tc [.lit n]
    expect a (s matches .error (.stuck .irrApplied))
      s!"{typeRoot} {n}: expected the type-in-a-relevant-position stuck run, got {s.outcome}"
  out := out.push s!"{typeRoot}: rejected by C2 (Lean gives {_root_.SortPoly.typeArg 0} at 0); \
    unchecked, stuck applying irr"
  -- The subsingleton recursor instance and the two-profile constant.
  let subsingletons := l.admitted.recursors.filter fun (_, k) => k matches .subsingleton ..
  expect a (subsingletons.size ≥ 1) "PUnit.rec is reached as a subsingleton eliminator at u = 0"
  let conditional := subsingletons.filter fun (r, _) =>
    match p.table.recKindOf r with
    | some (.subsingleton (.allZero ps) _) => !ps.isEmpty
    | _ => false
  expect a (conditional.size ≥ 1) "its kind is subsingleton only where u = 0"
  let split := l.checked.profileSplit
  expect a (split.length ≥ 2) s!"constants at two profiles (unitCase and PUnit.casesOn): {split.length}"
  out := out.push s!"{l.checked.instances.length} instances of {l.checked.reached.length} constants; \
    at two profiles: {split.map p.short}"
  -- The level-blind annotation: rejected by the checker, stuck when unchecked.
  let (p0, k0, _, _) ← IO.ofExcept ((prepare cfg env l.hints).mapError toString)
  let ann ← IO.ofExcept (k0.annotateChecked p0)
  let blind := blindAnn ann
  let pb := blindProgram p0
  let mut rejected := #[]
  for (addr, c) in p0.roots do
    let name := (Loaded.names l.hints addr).getD (p0.short c)
    let pr := { pb with roots := [(addr, c)] }
    match finish cfg l.hints pr blind with
    | .error d => rejected := rejected.push s!"{(name.drop 9).toString} {d.code}"
    | .ok _ => pure ()
  expect a (rejected.size ≥ 4) s!"the level-blind annotation is rejected: {rejected}"
  let pI ← IO.ofExcept (install pb blind)
  let pI := Lazify.run pI (blind.nodes.map (·.1))
  let mut stuck := #[]
  for (addr, c) in p0.roots do
    let name := (Loaded.names l.hints addr).getD (p0.short c)
    match StuckEval.run pI clock c [.lit 3] with
    | .error (.stuck cause) =>
      expect a (cause.group == "relevance") s!"level-blind {name}: {cause.name}"
      stuck := stuck.push s!"{(name.drop 9).toString} ({cause.name})"
    | _ => pure ()
  expect a (["SortPoly.comp", "SortPoly.throughRoot", "SortPoly.unitBoth"].all fun n =>
      stuck.any (·.startsWith (n.drop 9).toString))
    s!"the level-blind run is stuck on the sort-polymorphic roots: {stuck}"
  out := out.push s!"level-blind annotation: rejected {rejected.toList}; unchecked runs stuck \
    {stuck.toList}"
  return out

end IxCCTests.Src.SortPoly
