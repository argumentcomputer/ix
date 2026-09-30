import CompilatrixTests.Src.StuckEval
import SortPoly

/-! Level-exact relevance (D18) on ix-compiled sort-polymorphic code
(`fixtures/ixon-v3/src-sortpoly`, research note `relevance-checker.md`
§2.4, §4.7): every root loads through the whole front end and evaluates
without getting stuck, matching the same Lean source compiled natively (the
test-only `SortPolyFixture` library); the level-blind annotation of M1.F2
(a proof under a universe condition counted as relevant) is rejected by the
checker and makes the unchecked run stuck, as it did before D18; and the
one case level-exact relevance does not cover, a *type* reaching a relevant
position, stays a stuck run with a relevance cause. -/

namespace CompilatrixTests.Src.SortPoly

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance CompilatrixTests.Src
open CompilatrixTests.Src.StuckEval (Cause Stop)

/-- `PUnit.rec` has no compiled code, so its value comes from the kernel:
this is checked by definitional unfolding when the test is built. -/
theorem punitRec_eq (n : Nat) : _root_.SortPoly.punitRec n = n + 5 := rfl

def dir : System.FilePath := fixtures / "src-sortpoly"

def loadSortPoly (oracle : RelOracle := Relevance.annotate) : IO Loaded :=
  loadPack (dir / "sortpoly.ixe") (dir / "sortpoly.equations.json") (oracle := oracle)

/-- The native value of each root (`none`: the level-exact limit). -/
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

/-- The M1.F2 annotation: a proof under a proper universe condition is
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
  { consts := ann.consts.map (·.map fun c =>
      { result := blindRel c.result, params := c.params.map blindRel })
    ctors := ann.ctors.map (·.map fun c => { fields := c.fields.map blindField })
    nodes := ann.nodes.map fun (k, tags) => (k, tags.map blindTag) }

/-- The M1.F2 `RecKind`: subsingleton only for a family literally in `Prop`. -/
def blindProgram (p : Program) : Program :=
  { p with table := { p.table with recKind := p.table.recKind.map (·.map fun
      | .subsingleton (.allZero []) fs => .subsingleton .always fs
      | .subsingleton .. => .ordinary
      | k => k) } }

def run (a : Assert) : IO (Array String) := do
  let mut out := #[]
  let l ← loadSortPoly
  let p := l.program
  -- Every root evaluates and matches native Lean, except the type case.
  for (addr, c) in p.roots do
    let name := (Loaded.names l.hints addr).getD (p.short c)
    for n in List.range 21 do
      let r ← runRoot p clock c [n]
      match native name with
      | some f =>
        expect a (natOf r == some (f n)) s!"{name} {n}: SrcEval {outcome r}, Lean {f n}"
      | none =>
        let s := StuckEval.run p clock c [.lit n]
        expect a (s matches .error (.stuck .irrApplied))
          s!"{name} {n}: expected the type-in-a-relevant-position stuck run, got {s.outcome}"
    out := out.push s!"{name}: {if (native name).isSome then "matches native Lean on 0–20"
      else s!"stuck (irr applied; Lean gives {_root_.SortPoly.typeArg 0} at 0), as documented"}"
  -- The subsingleton recursor instance and the two-profile constant.
  let subsingletons := l.admitted.recursors.filter fun (_, k) => k matches .subsingleton ..
  expect a (subsingletons.size ≥ 1) "PUnit.rec is reached as a subsingleton eliminator at u = 0"
  let conditional := subsingletons.filter fun (r, _) =>
    match p.table.recKindOf r with
    | some (.subsingleton (.allZero ps) _) => !ps.isEmpty
    | _ => false
  expect a (conditional.size ≥ 1) "its kind is subsingleton only where u = 0"
  let split := l.checked.profileSplit
  expect a (split.size ≥ 2) s!"constants at two profiles (unitCase and PUnit.casesOn): {split.size}"
  out := out.push s!"{l.checked.instances.size} instances of {l.checked.reached.size} constants; \
    at two profiles: {split.toList.map p.short}"
  -- The level-blind annotation: rejected by the checker, stuck when unchecked.
  let cfg : LoadConfig := { typecheck := false }
  let (p0, _, _) ← IO.ofExcept ((prepare cfg l.env l.hints).mapError toString)
  let ann ← IO.ofExcept (annotate l.env p0)
  let blind := blindAnn ann
  let pb := blindProgram p0
  let mut rejected := #[]
  for (addr, c) in p0.roots do
    let name := (Loaded.names l.hints addr).getD (p0.short c)
    let pr := { pb with roots := #[(addr, c)] }
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

end CompilatrixTests.Src.SortPoly
