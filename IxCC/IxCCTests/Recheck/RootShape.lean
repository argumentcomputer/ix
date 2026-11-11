import IxCCTests.Recheck.Hostile
import IxCCTests.Recheck.Rc.Fixtures
import IxCCTests.Rt.Native
import IxCC.Recheck.Rc.Produce
import IxCC.Recheck.Proof.RootShape
import IxCC.Lam.Erase.Proof.Correct

/-! The root result shapes (`IxCC.Recheck.ResultShape`) on committed roots.

For every root of the ABI fixture (`Nat`, pinned-`Bool` and enumeration
results, compiled together; two of them also alone), for each root `rⱼ := cⱼ`
of the pin-free programs with two (`Bool`-pinned) and three constructors,
compiled alone, and for the pin-free three-constructor enumeration of
`Hostile`: the root passes `checkImmortalRoot`; every observation of its
result shape is accepted by the view, and by the shape view alike, as a
`ViewShape` observation that reads back from its word (the executable side of
`Recheck.Front.view_resultShape`); SrcEval's results on sample inputs are of
the shape (so the shape is not vacuous); and an observation of another kind is
not of the shape and is rejected by both views. A root compiled alone used to
have no row for the constructors of its result type that it never builds
(`Abi.bool0 := true` had no `Bool.false` row, `Abi.tri0 := .hi` no readback
type); erasure now registers them (`Lam.Erase.resultCtors`).

Each root compiled alone also returns its constructor from the x86 model of
its linked object, and a claim naming it is accepted by `verifyBytes`
(`aloneCase`); `tests-corpus` runs the same objects natively as test
executables (`nativeAlone`).

The hostile case for the shape view (`illTyped`): an erased-typing program
whose root `main : E := F.c₁` returns a constructor of another enumeration.
The view relabels it by its table tag, as `E`'s middle constructor, which the
object returns; the shape view rejects it, so the source goes wrong for the
shape view; typed ingress refuses the program. The decision procedures are
also evaluated by `decide` on a two-constant program. -/

namespace IxCCTests.Recheck.RootShape

open IxCC IxCC.Recheck
open IxCC.Sem (Obs Lang)
open IxCCTests.Src (Assert expect)
open IxCCTests.IxonV3.TypingFixtures (store block bytes)

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

/-- Check root `i` of an artifact, which must pass `checkImmortalRoot`. -/
def checkRoot (a : Assert) (label : String) (art : Recheck.Artifact) (i : Nat) (inputs : List (List Nat)) :
    IO String := do
  let some root := art.roots[i]? | do expect a false s!"{label}: no root"; return label
  expect a (CompileClaim.checkImmortalRoot art.src root) s!"{label}: checkImmortalRoot refused the root"
  let some (sig, ty) := root.ty | do expect a false s!"{label}: no readback type"; return label
  let c := root.const
  let cands := candidates art.src c
  expect a (!cands.isEmpty) s!"{label}: no candidate observations"
  let route := if boolResult art.src c then "Bool" else if ty == .nat then "Nat" else "enumeration"
  if boolResult art.src c then
    expect a (boolRows? art.src art.cfg) s!"{label}: a pinned Bool constructor has no row"
  for o in cands do
    expect a (resultShape? art.src c o) s!"{label}: {repr o} is not of the root's shape"
    expect a (art.front.shapeView i (some o) == art.front.view i (some o))
      s!"{label}: the shape view and the view differ on {repr o}, of the shape"
    match art.front.view i (some o) with
    | some (some w) =>
      expect a (decide (ViewShape sig ty w)) s!"{label}: the view's {repr w} is not a ViewShape"
      match word? w with
      | some word =>
        expect a (Rt.readback sig 16 memory ty word == some w) s!"{label}: {repr w} does not read back"
      | none => expect a false s!"{label}: {repr w} has no word"
    | _ => expect a false s!"{label}: the view rejects {repr o}, of the shape"
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
        expect a (art.front.shapeView i (some o)).isSome
          s!"{label} {ns}: the shape view rejects SrcEval's {repr o}"
      | none => expect a false s!"{label} {ns}: SrcEval's result observes nothing"
    | r => expect a false s!"{label} {ns}: SrcEval did not return ({match r with
        | .timeout => "timeout" | .stuck => "stuck" | .trap => "trap" | _ => "resource"})"
  -- an observation of another kind: off the shape, and both views reject it
  let other : Obs := if ty == .nat then .ctor 0 [] else .nat 7
  expect a (!resultShape? art.src c other) s!"{label}: {repr other} is of the shape"
  expect a ((art.front.view i (some other)) == none) s!"{label}: the view accepts {repr other}"
  expect a ((art.front.shapeView i (some other)) == none) s!"{label}: the shape view accepts {repr other}"
  expect a ((art.front.shapeView i none) == none) s!"{label}: the shape view accepts no observation"
  return s!"{label} ({route} route): {cands.length} shape observations, each accepted by both views \
    and read back; {results} SrcEval results of the shape"

/-- The ABI fixture's roots of arity 0–5 (a root of arity 6 is declined, and
with it the whole program). -/
def abiRoots : List String :=
  (List.range 6).flatMap fun k => [s!"Abi.nat{k}", s!"Abi.bool{k}", s!"Abi.tri{k}"]

/-- Ingress, produce and run on the roots named `roots`. -/
def compileAll (bytes : ByteArray) (json : Lean.Json) (roots : List String) (typecheck : Bool := true) :
    IO (Recheck.Input × Recheck.Config × Recheck.Cert × Recheck.Artifact) := do
  let inp ← Hostile.ofErr s!"{roots}: ingress" (Recheck.ingress bytes json roots typecheck)
  let cfg := Recheck.Config.forInput {} inp
  let cert ← Hostile.ofErr s!"{roots}: produce" (Recheck.produce cfg inp)
  let art ← Hostile.ofErr s!"{roots}: Recheck.run" (Recheck.run cfg inp.program cert)
  return (inp, cfg, cert, art)

def compile (bytes : ByteArray) (json : Lean.Json) (roots : List String) : IO Recheck.Artifact :=
  return (← compileAll bytes json roots).2.2.2

/-- Every root of the ABI fixture, compiled together (each is accepted); and
two roots compiled alone, which never build some constructors of their result
type: `Abi.bool0 := true` (both pinned `Bool` constructors have a row) and
`Abi.tri0 := .hi` (discovery finds every constructor in the table, so the root
has a readback type). -/
def abi (a : Assert) : IO (Array String) := do
  let bytes ← IO.FS.readBinFile "fixtures/corpus/phase1-abi/abi.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "fixtures/corpus/phase1-abi/abi.equations.json"))
  let art ← compile bytes json abiRoots
  let mut lines := #[]
  for (root, i) in art.roots.zipIdx do
    let inputs := [0, 1, 2, 5, 1000].map fun x => List.replicate root.params x
    lines := lines.push (← checkRoot a root.name art i inputs)
  let bool0 ← compile bytes json ["Abi.bool0"]
  expect a (boolRows? bool0.src bool0.cfg) "Abi.bool0 alone: a pinned Bool constructor has no row"
  lines := lines.push (← checkRoot a "Abi.bool0 alone" bool0 0 [[]])
  let tri0 ← compile bytes json ["Abi.tri0"]
  expect a (tri0.roots.head?.bind (·.ty) == some ({ inds := [[[], [], []]] }, .ind 0))
    "Abi.tri0 alone: not the readback type of three field-less constructors"
  lines := lines.push (← checkRoot a "Abi.tri0 alone" tri0 0 [[]])
  return lines

def pinFree (a : Assert) : IO String := do
  let c ← Hostile.mkCase 3
  let art ← Hostile.ofErr "enum-3: Recheck.run" (Recheck.run c.cfg c.inp.program c.honest)
  checkRoot a "enum-3 (nothing pinned)" art 0 [[]]

/-! ## Roots compiled alone -/

/-- Root `rⱼ := cⱼ` of the pin-free program with `n` constructors (`Bool`'s
content for `n = 2`), compiled alone, with its bytes, sidecar and address. -/
def alone (n j : Nat) :
    IO (ByteArray × Lean.Json × Recheck.Input × Recheck.Config × Recheck.Cert × Recheck.Artifact ×
      Ixon.Address) := do
  let (env, _, roots) := Hostile.pinFreeEnv n
  let bs := bytes env
  let json := Hostile.sidecar roots
  let name := s!"r{j}"
  let some (_, target) := roots.find? (·.1 == name) | throw (IO.userError s!"enum-{n}: no root {name}")
  let (inp, cfg, cert, art) ← compileAll bs json [name]
  return (bs, json, inp, cfg, cert, art, target)

/-- Each root of the pin-free programs with two and three constructors, alone:
the checks of `checkRoot`; its object returns constructor `j` in the x86
model; and a claim naming it is accepted by `verifyBytes`. -/
def aloneCases (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  for n in [2, 3] do
    for j in List.range n do
      let label := s!"enum-{n} r{j} alone"
      let (bs, json, inp, cfg, cert, art, target) ← alone n j
      lines := lines.push (← checkRoot a label art 0 [[]])
      match (art.linked Hostile.driver).run (0, []) 1000000 with
      | .ok (some o) => expect a (o == .ctor j []) s!"{label}: the object returns {repr o}"
      | _ => expect a false s!"{label}: the object returns no observation"
      let claim : CompileClaim :=
        { env := inp.env.root, roleTable := inp.env.bindingAddress, target, policy := .immortal
          abiArity := 0
          elfHash := Ixon.Address.blake3Pure art.object }
      expect a (CompileClaim.verifyBytes cfg bs json claim cert.toText)
        s!"{label}: verifyBytes refused the claim"
  return lines

/-- `nativeAlone` for `tests-corpus`: each root of `aloneCases`, as a test
executable, returns constructor `j` natively; the independent decoder prints
`#j` and `Rt.readback` of the native word gives the same. -/
def nativeAlone (a : Assert) (nt : IxCCTests.Rt.Native.Tools) : IO (Array String) := do
  let mut lines := #[]
  for n in [2, 3] do
    for j in List.range n do
      let label := s!"enum-{n} r{j} alone"
      let (_, _, _, _, _, art, _) ← alone n j
      let some root := art.roots.head? | do expect a false s!"{label}: no root"; continue
      let some (sig, ty) := root.ty | do expect a false s!"{label}: no readback type"; continue
      let exe ← IxCCTests.Rt.Native.link nt s!"alone_{n}_{j}" art.object root.symbol
      let opts : IxCCTests.Rt.Native.Options := { ty := root.ty, dump := true }
      match ← IxCCTests.Rt.Native.run exe opts [[]] with
      | [ln] =>
        expect a (ln.ok && ln.status == 0) s!"{label}: status {ln.status}, registers restored {ln.ok}"
        expect a (ln.obs == some s!"#{j}") s!"{label}: the independent decoder prints {ln.obs}"
        expect a (ln.readback opts.region sig ty == some (.ctor j []))
          s!"{label}: Rt.readback of the native word differs from the independent decoder"
        lines := lines.push s!"{label}: natively #{j}, as Rt.readback reads it"
      | _ => expect a false s!"{label}: not one result line"
  return lines

/-! ## A constructor of another type, under the shape view -/

/-- An erased-typing program: `E` with three constructors, `F` with four, and
`main : E := F.c₁` (ill-typed). -/
def illTypedEnv : Ixon.V3.Env × Ixon.Address := Id.run do
  let (e, blkE) := block {} ⟨.muts #[.indc (Hostile.enumInd 3)], #[], #[], #[.succ .zero]⟩
  let (e, blkF) := block e ⟨.muts #[.indc (Hostile.enumInd 4)], #[], #[], #[.succ .zero]⟩
  let enumE := Ixon.V3.Tc.indcProjAddr blkE 0
  let f1 := Ixon.V3.Tc.ctorProjAddr blkF 0 1
  store e ⟨Hostile.defn (.ref 0 #[]) (.ref 1 #[]), #[], #[enumE, f1], #[]⟩

/-- The view relabels `F.c₁` by its table tag as `E`'s constructor 1, which
the object returns; the shape view rejects it (it is not of `main`'s result
shape), so the source goes wrong for the shape view; typed ingress refuses
the program, and erased-typing `verifyBytes` accepts the claim. -/
def illTyped (a : Assert) : IO String := do
  let (env, main) := illTypedEnv
  let bs := bytes env
  let json := Hostile.sidecar [("main", main)]
  expect a (Recheck.ingress bs json ["main"]).toOption.isNone "ill-typed: typed ingress accepts the program"
  let (inp, cfg, cert, art) ← compileAll bs json ["main"] (typecheck := false)
  let some root := art.roots.head? | do expect a false "ill-typed: no root"; return "ill-typed"
  expect a (CompileClaim.checkImmortalRoot art.src root) "ill-typed: checkImmortalRoot refused the root"
  let c := root.const
  match Lang.run (⟨art.src, art.checked⟩ : Lam.Erase.Proof.CheckedProgram) (0, []) 1000000 with
  | .ok v =>
    match Lang.obs v with
    | some o@(.ctor k []) =>
      expect a (!resultShape? art.src c o) "ill-typed: F.c₁ is of E's shape"
      expect a (art.front.view 0 (some o) == some (some (.ctor 1 [])))
        s!"ill-typed: the view gives {repr (art.front.view 0 (some o))}, not E's constructor 1"
      expect a (art.front.shapeView 0 (some o) == none) "ill-typed: the shape view accepts F.c₁"
      expect a (art.src.decl? k matches some (.ctor _ _ _ 1 _ _ _)) "ill-typed: not constructor 1 of F"
    | o => expect a false s!"ill-typed: SrcEval's result is {repr o}"
  | _ => expect a false "ill-typed: SrcEval did not return"
  match (art.linked Hostile.driver).run (0, []) 1000000 with
  | .ok (some o) => expect a (o == .ctor 1 []) s!"ill-typed: the object returns {repr o}"
  | _ => expect a false "ill-typed: the object returns no observation"
  let claim : CompileClaim :=
    { env := inp.env.root, roleTable := inp.env.bindingAddress, target := main
      policy := .immortal, abiArity := 0
      elfHash := Ixon.Address.blake3Pure art.object }
  expect a (CompileClaim.verifyBytes cfg bs json claim cert.toText (typecheck := false))
    "ill-typed: erased-typing verifyBytes refused the claim"
  expect a (!CompileClaim.verifyBytes cfg bs json claim cert.toText (typecheck := true))
    "ill-typed: typed verifyBytes accepted the claim"
  return "ill-typed main : E := F.c₁: the view relabels it as E's constructor 1, which the object \
    returns; the shape view rejects it; typed ingress and typed verifyBytes refuse the program, \
    erased-typing verifyBytes accepts the claim"

/-! ## Plain-RC roots: constructor trees -/

/-- Whether `o` is an observation of the ground first-order shape `s`
(`Recheck.TreeShape`, decided to depth `fuel`). -/
def treeShape? (p : Src.Program) : Nat → Readback.Shape → Obs → Bool
  | 0, _, _ => false
  | _ + 1, .nat, .nat _ => true
  | fuel + 1, s@(.ind ind _ _), .ctor k fs =>
    match p.decl? ind with
    | some (.induct true _ _ 0 _ keys) =>
      match Readback.fieldShapes p s k with
      | .ok (tag, fields) =>
        keys[tag]? == some k && fields.length == fs.length &&
          (fields.zip fs).all fun (f, o) => treeShape? p fuel f o
      | .error _ => false
    | _ => false
  | _, _, _ => false

/-- Some observations of shape `s`, with source constructor ids: two numbers
at `Nat`, and each constructor over samples of its fields (to depth `fuel`,
at most four per constructor). -/
def samples (p : Src.Program) : Nat → Readback.Shape → List Obs
  | 0, _ => []
  | _ + 1, .nat => [.nat 0, .nat 9]
  | fuel + 1, s@(.ind ind _ _) =>
    match p.decl? ind with
    | some (.induct true _ _ 0 _ keys) =>
      keys.flatMap fun k =>
        match Readback.fieldShapes p s k with
        | .ok (_, fields) =>
          ((fields.foldr (fun f acc => (samples p fuel f).flatMap fun o => acc.map (o :: ·)) [[]]).map
            (Obs.ctor k ·)).take 4
        | .error _ => []
    | _ => []

/-- The shape of root `c`'s declared result type, as discovery reads it. -/
def rootShape? (p : Src.Program) (c : Src.CId) : Option Readback.Shape := do
  let d ← p.decl? c
  Readback.shape? p 128 [] [] d.type.pis.2

/-- Each plain-RC fixture root (lists, and a pair of lists): it passes
`checkPlainRcRoot`; sample constructor trees of its declared result type are
of the shape and accepted by the plain-RC view (`RcReplay.Front.view`, the
executable side of `Recheck.RcReplay.Front.view_plainShape`); SrcEval's
results on sample inputs are of the shape and accepted; a number is not of
the shape, and the view rejects it. -/
def plainRc (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  for name in IxCCTests.Recheck.Rc.Fixtures.roots do
    let label := s!"plain-RC {name}"
    let input ← IxCCTests.Recheck.Rc.Fixtures.source name
    let cfg : Recheck.Config := { names := [name] }
    let (_, art) ← Hostile.ofErr s!"{label}: produce" (Recheck.RcReplay.produce cfg input)
    let some root := art.roots.head? | do expect a false s!"{label}: no root"; continue
    expect a (CompileClaim.checkPlainRcRoot art.front.src root) s!"{label}: checkPlainRcRoot refused the root"
    let p := art.front.src
    let c := root.const
    expect a (resultTy p c == none) s!"{label}: the root returns the pinned Nat or Bool"
    let some s := rootShape? p c | do expect a false s!"{label}: no result shape"; continue
    let cands := samples p 5 s
    expect a (cands.length ≥ 3) s!"{label}: {cands.length} sample trees"
    for o in cands do
      expect a (treeShape? p 64 s o) s!"{label}: the sample {repr o} is not of the shape"
      expect a (art.front.view 0 (some o)).isSome s!"{label}: the view rejects {repr o}, of the shape"
    let mut results := 0
    for (n, seed) in [(0, 7), (1, 42), (3, 5)] do
      match Lang.run (⟨p, art.front.checked⟩ : Lam.Erase.Proof.CheckedProgram) (0, [n, seed]) 100000 with
      | .ok v =>
        match Lang.obs v with
        | some o =>
          results := results + 1
          expect a (treeShape? p 64 s o) s!"{label} {[n, seed]}: SrcEval's {repr o} is not of the shape"
          expect a (art.front.view 0 (some o)).isSome
            s!"{label} {[n, seed]}: the view rejects SrcEval's {repr o}"
        | none => expect a false s!"{label} {[n, seed]}: SrcEval's result observes nothing"
      | _ => expect a false s!"{label} {[n, seed]}: SrcEval did not return"
    expect a (!treeShape? p 64 s (.nat 7)) s!"{label}: a number is of the shape"
    expect a (art.front.view 0 (some (.nat 7)) == none) s!"{label}: the view accepts a number"
    lines := lines.push s!"{label}: {cands.length} sample trees of the declared type and {results} SrcEval \
      results, each of the shape and accepted by the view"
  return lines

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
