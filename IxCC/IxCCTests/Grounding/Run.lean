import IxCC.Src.KernelFront.Front
import IxCC.Src.Readback
import IxCCGrounding.Check
import IxCCTests.Src.Support

/-! # `tests-grounding`: the grounding check on committed closures

The grounding library's theorems (`IxCCGrounding`) take one Boolean check
(`IxCC.Grounding.groundCheck`) as their hypothesis on the program, the kernel's reading and the
certificate's annotation. This suite runs it on the committed closures of the grounding subjects:

* `fib` (`fixtures/ixon-v4/bench-k1/fib`, role-bound, root `entry` at `10`);
* `decide (fib 10 = 55)` (`fixtures/corpus/grounding/decide`, root `Grounding.decideFib10`).

For each: the kernel accepts the closure (`KernelFront.ingress`, the tiered entry), the front end
builds the program SrcEval runs and the kernel annotator its annotation, and the key map, the
level parameters and the set `Sl` (the root's closure under the terms SrcEval runs, with the
pinned `Bool` constructors) are computed as the theorems take them. Every conjunct of the check is
asserted true by name; SrcEval runs the root and reads back the expected observation.

Then the negative controls, on `fib`: each mutation makes exactly the conjunct it targets false
(the list of false conjuncts is asserted equal to that one name):

| Mutation | Conjunct |
| --- | --- |
| the root's stored value replaced by a literal | `valueCorr` |
| the equation theorem's right-hand side replaced by a literal | `eqnCorr` |
| the annotation's class of a constant the root unfolds made a type | `okClosed` |
| `Nat.succ`'s stored binder datum changed | `natBasis` |
-/

namespace IxCCTests.Grounding

open IxCC IxCC.Src IxCC.Sem IxCC.Grounding
open IxCCTests.Src (Assert expect)

/-- A grounding subject: a committed closure and sidecar, its root, the root's arguments and
the observation SrcEval reads back. -/
structure Subject where
  label : String
  stem : String
  root : String
  args : List Value
  expected : Obs

def subjects : List Subject :=
  [{ label := "fib", stem := "fixtures/ixon-v4/bench-k1/fib", root := "entry", args := [.lit 10],
     expected := .nat 55 },
   { label := "decide", stem := "fixtures/corpus/grounding/decide",
     root := "Grounding.decideFib10", args := [], expected := .ctor 1 [] }]

/-- What the check runs on. -/
structure Input where
  src : Program
  env : KEnv
  κ : CId → KKey
  lpsOf : CId → List Nat
  ann : Relevance.Ann
  Sl : List CId
  rootId : CId
  /-- the constants of `Sl` the kernel's reading has no key for -/
  keyless : List CId

/-- The kernel's acceptance, the program SrcEval runs, its annotation, the key map, the level
parameters and the root's closure. -/
def load (s : Subject) : IO Input := do
  let bytes ← IO.FS.readBinFile s!"{s.stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{s.stem}.equations.json"))
  let k ← match KernelFront.ingress bytes json [s.root] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"{s.label}: ingress: {e.render}")
  let cfg : Recheck.Config := { names := [s.root] }
  let cfg := cfg.forInput k.inp
  let P := k.inp.program
  let (table, _, _) := Src.Table.build cfg.table P k.inp.hints.proposals
  let p0 := { P with table }
  let ann ← IO.ofExcept (KernelFront.annotateChecked k p0)
  let (src, _) ← match Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error _ => throw (IO.userError s!"{s.label}: the annotation was refused")
  let some (_, rootId) := src.roots.head? | throw (IO.userError s!"{s.label}: no root")
  let env := k.acc.env
  let κ : CId → KKey := fun c => (k.rd.key? c).getD Ix.Kernel.natName
  let lpsOf : CId → List Nat := fun c =>
    match env.find? (κ c) with
    | some ci => ci.toConstantVal.levelParams
    | none => []
  let pins := [src.known.boolTrue, src.known.boolFalse].filterMap id
  let mut sl : List CId := rootId :: pins
  let mut todo : List CId := sl
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    for t in runTerms src c do
      for d in constsOf t do
        if !sl.contains d then
          sl := sl ++ [d]
          todo := todo ++ [d]
  let keyless := sl.filter fun c => (k.rd.key? c).isNone
  return { src, env, κ, lpsOf, ann, Sl := sl, rootId, keyless }

/-- The conjuncts of the check that are false. -/
def failing (i : Input) : List String :=
  (checkParts i.src i.env i.κ i.lpsOf i.ann i.Sl).filterMap fun (n, b) => if b then none else some n

/-- Replace the stored constant at `k`. -/
def mapConst (env : KEnv) (k : KKey)
    (f : Ix.Kernel.ConstantInfo .anon → Ix.Kernel.ConstantInfo .anon) : KEnv :=
  { env with consts := env.consts.map fun ci => if ci.name == k then f ci else ci }

/-- The root's stored value replaced by the literal `0`. -/
def mutateValue (i : Input) : Input :=
  { i with env := mapConst i.env (i.κ i.rootId) fun
      | .defnInfo cv _ h => .defnInfo cv (litE 0) h
      | ci => ci }

/-- The first `eqn` entry of `Sl` whose theorem's right-hand side is replaced by the literal `0`,
and the entry's name. -/
def mutateEqn (i : Input) : Option (Input × CId) := do
  let (c, thm) ← i.Sl.findSome? fun c =>
    match i.src.table.resolveOf c with
    | some (.eqn thm _) => some (c, thm)
    | _ => none
  let env := mapConst i.env (i.κ thm) fun
    | .thmInfo cv pf =>
      match splitAll cv.type with
      | (Ds, .app X _) => .thmInfo { cv with type := piTele Ds (.app X (litE 0)) } pf
      | _ => .thmInfo cv pf
    | ci => ci
  return ({ i with env }, c)

/-- The annotation's class of the first constant the root's run term may unfold made a type, and
that constant. -/
def mutateClass (i : Input) : Option (Input × CId) := do
  let t ← (runTerms i.src i.rootId).head?
  let (d, _) ← (evalConsts [] t).head?
  let r ← i.ann.constRel? d
  return ({ i with ann := { i.ann with consts := i.ann.consts.insert d { r with result := .type } } }, d)

/-- `Nat.succ`'s stored binder datum made "a proposition where parameter `0` is zero". -/
def mutateSucc (i : Input) : Input :=
  { i with env := mapConst i.env Ix.Kernel.natSuccName fun
      | .ctorInfo cv np nf => .ctorInfo { cv with type := .forallE natK natK bmZ } np nf
      | ci => ci }

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let mut fib? : Option Input := none
    for s in subjects do
      let i ← load s
      expect a i.keyless.isEmpty s!"{s.label}: constants of Sl without a kernel key: {i.keyless}"
      let bad := failing i
      expect a bad.isEmpty s!"{s.label}: the check's conjuncts {bad} are false"
      expect a (groundCheck i.src i.env i.κ i.lpsOf i.ann i.Sl)
        s!"{s.label}: groundCheck is false"
      let out := match Src.run i.src 100000 i.rootId s.args with
        | .ok v => readbackAll i.src v
        | _ => none
      expect a (out == some s.expected) s!"{s.label}: SrcEval read back {repr out}"
      IO.println s!"{s.label}: {i.Sl.length} constants, every conjunct of the check true; \
        SrcEval reads back {repr out}"
      if s.label == "fib" then fib? := some i
    let some i := fib? | throw (IO.userError "no fib subject")
    -- negative controls
    let v := failing (mutateValue i)
    expect a (v == ["valueCorr"]) s!"mutated root value: false conjuncts {v}, expected [valueCorr]"
    let some (ie, c) := mutateEqn i | throw (IO.userError "fib: no eqn entry to mutate")
    let e := failing ie
    expect a (e == ["eqnCorr"]) s!"mutated equation theorem of c{c}: false conjuncts {e}, expected [eqnCorr]"
    let some (ic, d) := mutateClass i | throw (IO.userError "fib: no constant to reclassify")
    let o := failing ic
    expect a (o == ["okClosed"]) s!"reclassified c{d}: false conjuncts {o}, expected [okClosed]"
    let n := failing (mutateSucc i)
    expect a (n == ["natBasis"]) s!"mutated Nat.succ: false conjuncts {n}, expected [natBasis]"
    IO.println "negative controls: each mutation falsifies exactly its conjunct \
      (valueCorr, eqnCorr, okClosed, natBasis)"
    IO.println s!"tests-grounding: {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding: {error}"
    return false

end IxCCTests.Grounding
