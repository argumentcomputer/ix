import IxCCTests.Recheck.Hostile
import IxCC.Recheck.Proof.RootShape
import IxCC.Lam.Erase.Proof.Correct

/-! The root result shapes (`IxCC.Recheck.ResultShape`) on committed roots.

For every root of the ABI fixture (`Nat`, pinned-`Bool` and
enumeration results, compiled together; two of them also alone) and the
pin-free three-constructor enumeration of `Hostile`: the root passes
`checkImmortalRoot`; every observation of its result shape is accepted by the
view as a `ViewShape` observation that reads back from its word (the
executable side of `Recheck.tagify_resultShape`; on the pinned-`Bool` route
only when `boolRows?` holds); SrcEval's results on sample inputs are of the
shape (so the shape is not vacuous); and an observation of another kind is
not of the shape and is rejected by the view. The decision procedures are also
evaluated by `decide` on a two-constant program. -/

namespace IxCCTests.Recheck.RootShape

open IxCC IxCC.Recheck
open IxCC.Sem (Obs Lang)
open IxCCTests.Src (Assert expect)

/-- The observations of root `c`'s result shape the test enumerates: some
natural numbers at the pinned `Nat`; the pinned `Bool` constructors; every
constructor of another result inductive. -/
def candidates (p : Src.Program) (c : Src.CId) : List Obs :=
  match resultType? p c with
  | some t =>
    match t.spine.1 with
    | .const I _ =>
      if p.known.nat == some I then [.nat 0, .nat 1, .nat 42, .nat (2 ^ 63 - 1)]
      else if p.known.bool == some I then
        [p.known.boolFalse, p.known.boolTrue].filterMap fun k => k.map (Obs.ctor · [])
      else
        match p.decl? I with
        | some (.induct _ _ _ _ _ keys) => keys.map (Obs.ctor · [])
        | _ => []
    | _ => []
  | none => []

/-- Whether root `c` returns the pinned `Bool` (`BoolResult`). -/
def boolResult (p : Src.Program) (c : Src.CId) : Bool :=
  match p.known.bool, resultType? p c with
  | some B, some (.const B' []) => B == B' && p.known.nat != some B
  | _, _ => false

/-- The word of an immediate observation, as the runtime represents it. -/
def word? : Obs → Option Lir.Word
  | .nat n => Rt.natWord n
  | .ctor t [] => if t < Rt.natLimit then some (Rt.ctor0Word t) else none
  | _ => none

def memory : X86.Memory := ⟨fun _ => 0, fun _ => false, fun _ => false⟩

/-- Check root `i` of an artifact (which must pass `checkImmortalRoot` unless `mustAccept` is false). -/
def checkRoot (a : Assert) (label : String) (art : Recheck.Artifact) (i : Nat) (inputs : List (List Nat))
    (mustAccept : Bool := true) :
    IO String := do
  let some root := art.roots[i]? | do expect a false s!"{label}: no root"; return label
  if !mustAccept && !CompileClaim.checkImmortalRoot art.src root then
    return s!"{label}: checkImmortalRoot refuses the root (readback type {(root.ty.map (·.2)).isSome})"
  expect a (CompileClaim.checkImmortalRoot art.src root) s!"{label}: checkImmortalRoot refused the root"
  let some (sig, ty) := root.ty | do expect a false s!"{label}: no readback type"; return label
  let c := root.const
  let cands := candidates art.src c
  expect a (!cands.isEmpty) s!"{label}: no candidate observations"
  let route := if boolResult art.src c then "Bool" else if ty == .nat then "Nat" else "enumeration"
  let rows := boolRows? art.src art.cfg
  let mut accepted := 0
  let mut rejected := 0
  for o in cands do
    expect a (resultShape? art.src c o) s!"{label}: {repr o} is not of the root's shape"
    match art.front.view i (some o) with
    | some (some w) =>
      accepted := accepted + 1
      expect a (decide (ViewShape sig ty w)) s!"{label}: the view's {repr w} is not a ViewShape"
      match word? w with
      | some word =>
        expect a (Rt.readback sig 16 memory ty word == some w) s!"{label}: {repr w} does not read back"
      | none => expect a false s!"{label}: {repr w} has no word"
    | _ =>
      rejected := rejected + 1
      -- only allowed on the pinned-`Bool` route without both rows
      expect a (boolResult art.src c && !rows) s!"{label}: the view rejects {repr o}, of the shape"
  -- SrcEval's results are of the shape
  let mut results := 0
  for ns in inputs do
    match Lang.run (⟨art.src, art.checked⟩ : Lam.Erase.Proof.CheckedProgram) (i, ns) 1000000 with
    | .ok v =>
      match Lang.obs v with
      | some o =>
        results := results + 1
        expect a (resultShape? art.src c o) s!"{label} {ns}: SrcEval's {repr o} is not of the shape"
        expect a (art.front.view i (some o)).isSome s!"{label} {ns}: the view rejects SrcEval's {repr o}"
      | none => expect a false s!"{label} {ns}: SrcEval's result observes nothing"
    | r => expect a false s!"{label} {ns}: SrcEval did not return ({match r with
        | .timeout => "timeout" | .stuck => "stuck" | .trap => "trap" | _ => "resource"})"
  -- an observation of another kind: off the shape, and the view rejects it
  let other : Obs := if ty == .nat then .ctor 0 [] else .nat 7
  expect a (!resultShape? art.src c other) s!"{label}: {repr other} is of the shape"
  expect a ((art.front.view i (some other)) == none) s!"{label}: the view accepts {repr other}"
  return s!"{label} ({route} route{if route == "Bool" then s!", Bool rows {rows}" else ""}): \
    {cands.length} shape observations, {accepted} accepted by the view and read back, {rejected} \
    rejected; {results} SrcEval results of the shape"

/-- The ABI fixture's roots of arity 0–5 (a root of arity 6 is declined, and
with it the whole program). -/
def abiRoots : List String :=
  (List.range 6).flatMap fun k => [s!"Abi.nat{k}", s!"Abi.bool{k}", s!"Abi.tri{k}"]

def compile (bytes : ByteArray) (json : Lean.Json) (roots : List String) : IO Recheck.Artifact := do
  let inp ← Hostile.ofErr s!"{roots}: ingress" (Recheck.ingress bytes json roots)
  let cfg := Recheck.Config.forInput {} inp
  let cert ← Hostile.ofErr s!"{roots}: produce" (Recheck.produce cfg inp)
  Hostile.ofErr s!"{roots}: Recheck.run" (Recheck.run cfg inp.program cert)

/-- Every root of the ABI fixture, compiled together (each is accepted); and
two roots compiled alone, where the program's constructor table lacks some of
the result type's constructors: `Abi.bool0 := true` (no row for `Bool.false`,
so the pinned-`Bool` route's totality needs `boolRows?`, which fails) and
`Abi.tri0 := .hi` (discovery needs every constructor in the table, so the root
has no readback type and `checkImmortalRoot` refuses it). -/
def abi (a : Assert) : IO (Array String) := do
  let bytes ← IO.FS.readBinFile "fixtures/corpus/phase1-abi/abi.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "fixtures/corpus/phase1-abi/abi.equations.json"))
  let art ← compile bytes json abiRoots
  let mut lines := #[]
  for (root, i) in art.roots.zipIdx do
    let inputs := [0, 1, 2, 5, 1000].map fun x => List.replicate root.params x
    lines := lines.push (← checkRoot a root.name art i inputs)
  let bool0 ← compile bytes json ["Abi.bool0"]
  expect a (!boolRows? bool0.src bool0.cfg) "Abi.bool0 alone: both Bool constructors have a row"
  lines := lines.push (← checkRoot a "Abi.bool0 alone" bool0 0 [[]])
  let tri0 ← compile bytes json ["Abi.tri0"]
  lines := lines.push (← checkRoot a "Abi.tri0 alone" tri0 0 [[]] (mustAccept := false))
  return lines

def pinFree (a : Assert) : IO String := do
  let c ← Hostile.mkCase 3
  let art ← Hostile.ofErr "enum-3: Recheck.run" (Recheck.run c.cfg c.inp.program c.honest)
  checkRoot a "enum-3 (nothing pinned)" art 0 [[]]

/-! ## The decision procedures in the kernel -/

/-- Two constants: `0` is the pinned `Nat`, `1 : Nat → Nat` the root. -/
def tiny : Src.Program :=
  { consts := Src.NatMap.ofDense
      [ { ref := default, addr := default, decl := .induct true 0 0 0 (.sort .zero) [] },
        { ref := default, addr := default
          decl := .defn .defn .safe 0 (.pi {} default (.const 0 []) (.const 0 [])) (.lam {} (.const 0 []) (.var 0)) } ]
    size := 2
    known := { nat := some 0 } }

example : ResultShape tiny 1 (.nat 3) := by decide
example : ¬ ResultShape tiny 1 (.ctor 0 []) := by decide
example : ViewShape {} .nat (.nat 3) := by decide
example : ¬ ViewShape { inds := [[[], [.nat]]] } (.ind 0) (.ctor 1 []) := by decide

end IxCCTests.Recheck.RootShape
