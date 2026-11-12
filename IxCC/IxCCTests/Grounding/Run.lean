import IxCC.Recheck.Produce
import IxCC.Src.Readback
import IxCCGrounding.Check
import IxCCGrounding.RootCheck
import IxCCGrounding.Direct.Check
import IxCCTests.Grounding.Oracle
import IxCCTests.Src.Support

/-! # `tests-grounding`: the grounding check on committed closures

The grounding library's theorems (`IxCCGrounding`) take one Boolean check
(`IxCC.Grounding.groundCheck`) as their hypothesis on the program, the kernel's reading and the
certificate's annotation. This suite runs it on the committed closures of the grounding subjects:

* `fib` (`fixtures/ixon-v4/bench-k1/fib`, role-bound, root `entry` at `10`);
* `decide (fib 10 = 55)` (`fixtures/corpus/grounding/decide`, root `Grounding.decideFib10`).

For each: the kernel accepts the closure (`Recheck.ingress`, the tiered entry), the front end
builds the program SrcEval runs and the kernel annotator its annotation, and the key map, the
level parameters and the set `Sl` (the root's closure under the terms SrcEval runs, with the
pinned `Bool` constructors) are computed as the theorems take them. Every conjunct of the check is
asserted true by name; SrcEval runs the root and reads back the expected observation; the
root's checks (`rootParts`, `foArgsB`, `resultTagB` at the observed result, and for the `Bool`
root `boolListedB`) are asserted true.

Then the negative controls, on `fib`: each mutation makes exactly the conjunct it targets false
(the list of false conjuncts is asserted equal to that one name):

| Mutation | Conjunct |
| --- | --- |
| the root's stored value replaced by a literal | `valueCorr` |
| the equation theorem's right-hand side replaced by a literal | `eqnCorr` |
| the annotation's class of a constant the root unfolds made a type | `okClosed` |
| `Nat.succ`'s stored binder datum made "always a proposition" | `natBasis` |
| the first `case` entry's `casesOn` value hands its recursor the last two minors swapped | `caseShape` |
| `Nat`'s stored sort made `Prop` (its `case` entry is then over a family of propositions) | `caseShape` |
| a structure of `Sl` with fields, its constructor in `Sl`, made a family of propositions | `proj` |

The direct route (`IxCCGrounding.Direct.Check`, a Boolean beside `groundCheck`): `sitesDirectB`
refuses no application site of either subject; two controls on `fib` each make it false and leave
`groundCheck` true: (a) the stored type of a constant passed as an argument made `Nat`; (h) a head
constant's first binder datum (`never`) made "always a proposition".

The kernel as an oracle (`IxCCTests.Grounding.Oracle`), on both subjects: at every site-profile
instance the direct route accepts, the kernel's own typing core (the front end's, over the
closure) types the site in the graph regime (the function part's inferred type reduces to a `∀`
whose domain is definitionally equal to the argument's inferred type, its binder datum not a
proposition at that profile); every accepted site whose kernel binder datum is a proposition at
some other profile is refused by the walk at that profile; the walk's refused positions are
`runRefused`'s. The counts (sites, site-profile instances, site-profile pairs where the kernel's
datum holds) are asserted per subject.

And, for the root's checks, on `decide`: the observation `false` (tag `0`) fails `resultTagB`
(`PUnit.unit` is a field-less constructor at index `0` in `Sl` beside `Bool.false`, so the check
rejects it, as documented); an enumeration argument that is not its type's listed constructor
fails `foArgsB`; the pinned `Bool` re-pinned at `Nat` fails `boolListedB` and nothing in
`groundCheck`.

Recursors (G3): with no recursor class admitted the check is the landed one, true on `fib`. On
`tak` (`fixtures/ixon-v4/bench-k1/tak`), whose one recursor in `Sl` is `Eq.rec` (run by
`Eq.ndrec`), of class `eqRec`, admitted since part C: every conjunct true (with only the class
`empty` admitted, as parts A and B landed, exactly `declOk` false); and six controls, each making
exactly `recShape` false there: `Eq.rec`'s stored rule given the right-hand side `0`, its stored
type cut by one binder (fewer than the arguments SrcEval takes), `Eq.refl`'s first binder datum
made `never`; and for `EqRecBasis` (`RecStored` still true, `EqRecBasis` alone false): `Eq.rec`'s
rule made `λ α a motive refl. a` in the kernel's reading and the program alike, its major
premise's domain made `@Eq α b a`; and its level-parameter list reversed (refused by `RecStored`,
since its rule's levels no longer correspond to the program's; `EqRecBasis` does not read the
list).
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
  /-- the root's first-order argument types; its result type is `Nat`, or the pinned `Bool` -/
  argTys : List FoTy
  boolResult : Bool
  /-- the kernel oracle's counts: site positions the direct route walks, their site-profile
  instances, and pairs of an accepted site and a profile at which the kernel's binder datum is a
  proposition -/
  oracle : Nat × Nat × Nat

def subjects : List Subject :=
  [{ label := "fib", stem := "fixtures/ixon-v4/bench-k1/fib", root := "entry", args := [.lit 10],
     expected := .nat 55, argTys := [.nat], boolResult := false, oracle := (60, 68, 11) },
   { label := "decide", stem := "fixtures/corpus/grounding/decide",
     root := "Grounding.decideFib10", args := [], expected := .ctor 1 [], argTys := [],
     boolResult := true, oracle := (93, 101, 17) }]

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
parameters and the root's closure; and the kernel's typing core over the closure (the oracle's). -/
def load (s : Subject) : IO (Input × Oracle.Core) := do
  let bytes ← IO.FS.readBinFile s!"{s.stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{s.stem}.equations.json"))
  let k ← match Recheck.ingress bytes json [s.root] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"{s.label}: ingress: {e.render}")
  let cfg : Recheck.Config := { names := [s.root] }
  let cfg := cfg.forInput k
  let P := k.program
  let (table, _, _) := Src.Table.build cfg.table P k.hints.proposals
  let p0 := { P with table }
  let ann ← IO.ofExcept (k.kernel.annotateChecked p0)
  let (src, _) ← match Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error _ => throw (IO.userError s!"{s.label}: the annotation was refused")
  let some (_, rootId) := src.roots.head? | throw (IO.userError s!"{s.label}: no root")
  let env := k.kernel.acc.env
  let κ : CId → KKey := fun c => (k.kernel.rd.key? c).getD Ix.Kernel.natName
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
  let keyless := sl.filter fun c => (k.kernel.rd.key? c).isNone
  return ({ src, env, κ, lpsOf, ann, Sl := sl, rootId, keyless }, KernelFront.coreOf k.kernel.fe)

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
      | .ctorInfo cv np nf =>
        .ctorInfo { cv with type := .forallE natK natK { pw := .ifAllZero [] } } np nf
      | ci => ci }

/-- The last two minors a `casesOn` value hands its recursor, swapped (under its λs). -/
def swapLastMinors : KExpr → KExpr
  | .lam d b m => .lam d (swapLastMinors b) m
  | e =>
    let args := e.getAppArgs
    let n := args.length
    match args[n - 3]?, args[n - 2]? with
    | some a, some b => Ix.Kernel.Expr.mkAppN e.getAppFn ((args.set (n - 3) b).set (n - 2) a)
    | _, _ => e

/-- The first `case` entry of `Sl` whose `casesOn` value has its last two minors swapped, and the
entry's name. -/
def mutateCase (i : Input) : Option (Input × CId) := do
  let c ← i.Sl.find? fun c =>
    match i.src.table.resolveOf c with
    | some (.case _) => true
    | _ => false
  let env := mapConst i.env (i.κ c) fun
    | .defnInfo cv val h => .defnInfo cv (swapLastMinors val) h
    | ci => ci
  return ({ i with env }, c)

/-- A stored type whose final sort is made `Prop`. -/
def toProp : KExpr → KExpr
  | .forallE d b m => .forallE d (toProp b) m
  | .sort _ => .sort .zero
  | e => e

/-- The stored inductive at `k` made a family of propositions (its type's final sort `Prop`). -/
def mutateIndSort (i : Input) (k : KKey) : Input :=
  { i with env := mapConst i.env k fun
      | .indInfo cv caps => .indInfo { cv with type := toProp cv.type } caps
      | ci => ci }

/-- A one-constructor inductive of `Sl` whose constructor is in `Sl` and has fields (what the
`proj` conjunct asks to be never a proposition). -/
def projectedStruct (i : Input) : Option CId :=
  i.Sl.find? fun s =>
    match i.src.decl? s with
    | some (.induct _ _ _ _ _ [c]) =>
      i.Sl.contains c && match i.env.find? (i.κ c) with
        | some (.ctorInfo _ _ nf) => nf > 0
        | _ => false
    | _ => false

/-- Every application site of `Sl`'s run terms (relevant or not), with its constant. -/
def allRunSites (i : Input) : List (CId × Site) :=
  i.Sl.flatMap fun c => (runPairsB i.src i.env i.κ c).flatMap fun (t, e) =>
    (allSites [] t e).map fun s => (c, s)

/-- The refused sites of `Sl`'s run terms (`runRefused`, with the reading's table built once). -/
def refusedSites (i : Input) : List (CId × Site) :=
  let tab := KTab.of i.env
  i.Sl.flatMap fun c => (runPairsB i.src i.env i.κ c).flatMap fun (t, e) =>
    (runRefusedT tab i.src i.lpsOf i.ann c t e).map fun s => (c, s)

def directOk (i : Input) : Bool := sitesDirectB i.src i.env i.κ i.lpsOf i.ann i.Sl

/-- `expect` with its failure message computed only when the assertion fails (several messages
count refused sites, a walk of the closure). -/
def expectL (a : Assert) (cond : Bool) (msg : Unit → String) : IO Unit := do
  unless cond do throw (IO.userError (msg ()))
  a.modify (· + 1)

/-- (a) The stored type of a constant passed as an argument made `Nat`. -/
def mutateArgType (i : Input) : Option (Input × KKey) := do
  let k ← (allRunSites i).findSome? fun (_, _, _, a) =>
    match a with
    | .const k _ => match i.env.find? k with
      | some (.defnInfo cv _ _) => if cv.type != natK then some k else none
      | _ => none
    | _ => none
  return ({ i with env := mapConst i.env k fun
      | .defnInfo cv v h => .defnInfo { cv with type := natK } v h
      | ci => ci }, k)

/-- (h) A head constant's first binder datum (`never`) made "always a proposition". -/
def mutateHeadDatum (i : Input) : Option (Input × KKey) := do
  let (k, T) ← (allRunSites i).findSome? fun (_, _, f, _) =>
    match f with
    | .const k _ => match i.env.find? k with
      | some ci => match ci.toConstantVal.type with
        | .forallE d b m =>
          if m.pw == .never && ci.toConstantVal.levelParams.isEmpty && k != Ix.Kernel.natSuccName then
            some (k, (.forallE d b { m with pw := .ifAllZero [] } : KExpr))
          else none
        | _ => none
      | none => none
    | _ => none
  return ({ i with env := mapConst i.env k fun
      | .defnInfo cv v h => .defnInfo { cv with type := T } v h
      | .ctorInfo cv np nf => .ctorInfo { cv with type := T } np nf
      | .axiomInfo cv => .axiomInfo { cv with type := T }
      | .thmInfo cv v => .thmInfo { cv with type := T } v
      | ci => ci }, k)

/-! ## G2b: the widened direct route and the renaming-tolerant `case` shape -/

/-- A closure of the corpus with all its roots (`Sl` the roots' closure), as the corpus
measurement loads it; the kernel's typing core over it. -/
def loadClosure (label stem : String) (roots : List String) : IO (Input × Oracle.Core) := do
  let bytes ← IO.FS.readBinFile s!"{stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  let k ← match Recheck.ingress bytes json roots with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"{label}: ingress: {e.render}")
  let cfg : Recheck.Config := { names := k.names }
  let cfg := cfg.forInput k
  let P := k.program
  let (table, _, _) := Src.Table.build cfg.table P k.hints.proposals
  let p0 := { P with table }
  let ann ← IO.ofExcept (k.kernel.annotateChecked p0)
  let (src, _) ← match Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error _ => throw (IO.userError s!"{label}: the annotation was refused")
  let rootIds := src.roots.map (·.2)
  let some rootId := rootIds.head? | throw (IO.userError s!"{label}: no root")
  let env := k.kernel.acc.env
  let κ : CId → KKey := fun c => (k.kernel.rd.key? c).getD Ix.Kernel.natName
  let lpsOf : CId → List Nat := fun c =>
    match env.find? (κ c) with
    | some ci => ci.toConstantVal.levelParams
    | none => []
  let pins := [src.known.boolTrue, src.known.boolFalse].filterMap id
  let mut sl : List CId := rootIds ++ pins.filter (fun c => !rootIds.contains c)
  let mut todo : List CId := sl
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    for t in runTerms src c do
      for d in constsOf t do
        if !sl.contains d then
          sl := sl ++ [d]
          todo := todo ++ [d]
  let keyless := sl.filter fun c => (k.kernel.rd.key? c).isNone
  return ({ src, env, κ, lpsOf, ann, Sl := sl, rootId, keyless }, KernelFront.coreOf k.kernel.fe)

/-- The stored recursor whose two rules are `Bool.false`'s and `Bool.true`'s. -/
def boolRec? (env : KEnv) : Option KKey :=
  env.consts.findSome? fun ci =>
    match ci with
    | .recInfo cv _ _ [r0, r1] =>
      if r0.ctor == Ix.Kernel.boolFalseName && r1.ctor == Ix.Kernel.boolTrueName then some cv.name
      else none
    | _ => none

/-- A recursor's second rule given its first rule's right-hand side (for `Bool.rec`: `true` reduces
as `false` does). Swapping the two right-hand sides is no control here: the sites ι clears read
`Bool.noConfusionType` at two different constructors, which is the same under the swap. -/
def mutateRecRules (i : Input) (k : KKey) : Input :=
  { i with env := mapConst i.env k fun
      | .recInfo cv mI rP (r0 :: r1 :: rest) =>
        .recInfo cv mI rP (r0 :: { r1 with rhs := r0.rhs } :: rest)
      | ci => ci }

/-- `String.ofList`'s stored type with its codomain made `Nat`. -/
def mutateStringOfList (i : Input) : Input :=
  let retype : KExpr → KExpr
    | .forallE d _ m => .forallE d natK m
    | T => T
  { i with env := mapConst i.env Ix.Kernel.stringOfListName fun
      | .defnInfo cv v h => .defnInfo { cv with type := retype cv.type } v h
      | .ctorInfo cv np nf => .ctorInfo { cv with type := retype cv.type } np nf
      | .axiomInfo cv => .axiomInfo { cv with type := retype cv.type }
      | ci => ci }

/-- A `casesOn` value with the levels at which it calls the recursor `kr` reversed (under its λs). -/
def revRecLevels (kr : KKey) : KExpr → KExpr
  | .lam d b m => .lam d (revRecLevels kr b) m
  | e =>
    match e.getAppFn with
    | .const k us => if k == kr then Ix.Kernel.Expr.mkAppN (.const k us.reverse) e.getAppArgs else e
    | _ => e

/-- A `case` entry of `Sl` whose recursor names its level parameters apart from `casesOn`'s (it
passes `caseShape` only because the shape compares the recursor at the levels `casesOn`'s body
calls it at), with levels that reversing changes. -/
def renamedCase? (i : Input) : Option (CId × CId) :=
  i.Sl.findSome? fun c =>
    match i.src.table.resolveOf c with
    | some (.case r) =>
      match caseShape? i.env (i.κ c) (i.κ r), i.env.find? (i.κ r) with
      | some sh, some (.recInfo cvr _ _ _) =>
        if cvr.levelParams.map Ix.Kernel.Level.param != sh.recLevels &&
            sh.recLevels.reverse != sh.recLevels && caseStoredB i.env (i.κ c) (i.κ r) sh then
          some (c, r)
        else none
      | _, _ => none
    | _ => none

/-! ## G3: recursors in the checked set -/

/-- The conjuncts of the check that are false with the recursor classes `adm` admitted. -/
def failingWith (adm : List RecClass) (i : Input) : List String :=
  (checkPartsWith adm i.src i.env i.κ i.lpsOf i.ann i.Sl).filterMap fun (n, b) =>
    if b then none else some n

/-- Every recursor class. -/
def allClasses : List RecClass := [.empty, .eqRec, .flat, .ordinary]

/-- The recursor of `Sl` the kernel stores under `Eq.rec`'s key. -/
def eqRecOf? (i : Input) : Option CId :=
  i.Sl.find? fun c => i.κ c == Ix.Kernel.eqRecName &&
    match i.src.decl? c with
    | some (.recr ..) => true
    | _ => false

/-- `Eq.rec`'s stored rule given the right-hand side `0`. -/
def mutateEqRecRule (i : Input) : Input :=
  { i with env := mapConst i.env Ix.Kernel.eqRecName fun
      | .recInfo cv mI rP (r0 :: rest) => .recInfo cv mI rP ({ r0 with rhs := litE 0 } :: rest)
      | ci => ci }

/-- `Eq.rec`'s stored type without its first binder: one `∀` fewer than the arguments SrcEval
takes. -/
def mutateEqRecArity (i : Input) : Input :=
  { i with env := mapConst i.env Ix.Kernel.eqRecName fun
      | .recInfo cv mI rP rules => .recInfo { cv with type := piBody 1 cv.type } mI rP rules
      | ci => ci }

/-- `Eq.refl`'s stored type with its first binder datum made `never` (its telescope unchanged, so
the `ctor` conjunct, which reads its length, is not affected). -/
def mutateEqRefl (i : Input) : Input :=
  let redatum : KExpr → KExpr
    | .forallE d b _ => .forallE d b { pw := .never }
    | T => T
  { i with env := mapConst i.env Ix.Kernel.eqReflName fun
      | .ctorInfo cv np nf => .ctorInfo { cv with type := redatum cv.type } np nf
      | ci => ci }

/-- A Src term's body under `n` λs replaced by `new`. -/
def setLamBody : Nat → Term → Term → Term
  | 0, _, new => new
  | n + 1, .lam b d t, new => .lam b d (setLamBody n t new)
  | _ + 1, t, _ => t

/-- `Eq.rec`'s rule made `λ α a motive refl. a`, in the kernel's reading and in the program alike:
the Src rule still corresponds to the stored one (`RecStored` holds), and only `EqRecBasis`
refuses it. -/
def mutateEqRecRhsA (i : Input) (er : CId) : Input :=
  let env := mapConst i.env Ix.Kernel.eqRecName fun
    | .recInfo cv mI rP (r0 :: rest) =>
      .recInfo cv mI rP ({ r0 with rhs := lamTele eqRecPrefix (.bvar 2) } :: rest)
    | ci => ci
  let src := match i.src.entry? er with
    | some e =>
      match e.decl with
      | .recr sf kk lv np nmot nmin ni ind (rl :: rest) ty =>
        let rl' := { rl with rhs := setLamBody 4 rl.rhs (.var 2) }
        let e' := { e with decl := .recr sf kk lv np nmot nmin ni ind (rl' :: rest) ty }
        { i.src with consts := i.src.consts.insert er e' }
      | _ => i.src
    | none => i.src
  { i with env, src }

/-- `Eq.rec`'s stored type with its major premise's domain made `@Eq α b a` (the arity unchanged,
so `RecStored` holds). -/
def mutateEqRecType (i : Input) : Input :=
  let ty := piTele (eqRecPrefix ++ [(.bvar 3, bmR), (eqAppK (.bvar 4) (.bvar 0) (.bvar 3), bmR)])
    eqRecBody
  { i with env := mapConst i.env Ix.Kernel.eqRecName fun
      | .recInfo cv mI rP rules => .recInfo { cv with type := ty } mI rP rules
      | ci => ci }

/-- `Eq.rec`'s level-parameter list reversed (`[1, 0]` to `[0, 1]`), the names inside its type and
rule unchanged; the level parameters `lpsOf` read off the mutated reading, as `load` computes them. -/
def mutateEqRecLevels (i : Input) : Input :=
  let env := mapConst i.env Ix.Kernel.eqRecName fun
    | .recInfo cv mI rP rules => .recInfo { cv with levelParams := cv.levelParams.reverse } mI rP rules
    | ci => ci
  let lpsOf : CId → List Nat := fun c =>
    match env.find? (i.κ c) with
    | some ci => ci.toConstantVal.levelParams
    | none => []
  { i with env, lpsOf }

/-! ## G3, part D: flat recursors -/

/-- The first flat recursor of `Sl`. -/
def flatRecOf? (i : Input) : Option CId :=
  i.Sl.find? fun c => recClassB i.src i.env i.κ c == some .flat

/-- A kernel term with the domain of its `n`-th leading λ replaced by `new`. -/
def setLamDomK : Nat → KExpr → KExpr → KExpr
  | 0, .lam _ b m, new => .lam new b m
  | n + 1, .lam d b m, new => .lam d (setLamDomK n b new) m
  | _, e, _ => e

/-- A Src term with the domain of its `n`-th leading λ replaced by `new`. -/
def setLamDomS : Nat → Term → Term → Term
  | 0, .lam b _ t, new => .lam b new t
  | n + 1, .lam b d t, new => .lam b d (setLamDomS n t new)
  | _, t, _ => t

/-- A kernel term's body under `n` λs replaced by `new`. -/
def setLamBodyK : Nat → KExpr → KExpr → KExpr
  | 0, _, new => new
  | k + 1, .lam d b m, new => .lam d (setLamBodyK k b new) m
  | _ + 1, e, _ => e

/-- A recursor's stored rules and its Src rules mapped alike (`f` on the kernel's list, `g` on the
program's). -/
def mapRecRules (i : Input) (r : CId)
    (f : List (Ix.Kernel.RecRule .anon) → List (Ix.Kernel.RecRule .anon))
    (g : List Src.Rule → List Src.Rule) : Input :=
  let env := mapConst i.env (i.κ r) fun
    | .recInfo cv mI rP rules => .recInfo cv mI rP (f rules)
    | ci => ci
  let src := match i.src.entry? r with
    | some e =>
      match e.decl with
      | .recr sf kk lv np nmot nmin ni ind rules ty =>
        let e' := { e with decl := .recr sf kk lv np nmot nmin ni ind (g rules) ty }
        { i.src with consts := i.src.consts.insert r e' }
      | _ => i.src
    | none => i.src
  { i with env, src }

/-- The first rule's second λ-domain (the first minor premise's) made the variable `0`, in the
kernel's reading and the program alike: the rule still corresponds (`RecStored`), its domains are
no longer the type's (`RecTele`). -/
def mutateRecTele (i : Input) (r : CId) : Input :=
  mapRecRules i r
    (fun | r0 :: rest => { r0 with rhs := setLamDomK 1 r0.rhs (.bvar 0) } :: rest | rs => rs)
    (fun | r0 :: rest => { r0 with rhs := setLamDomS 1 r0.rhs (.var 0) } :: rest | rs => rs)

/-- The first two rules swapped, in the kernel's reading and the program alike: they still
correspond position by position (`RecStored`), but the rule at a constructor's index is no longer
its own (`RecProg`). -/
def mutateRecProg (i : Input) (r : CId) : Input :=
  mapRecRules i r (fun | r0 :: r1 :: rest => r1 :: r0 :: rest | rs => rs)
    (fun | r0 :: r1 :: rest => r1 :: r0 :: rest | rs => rs)

/-- The major premise's domain (after `n` binders) at one more level. -/
def majorMoreLevels : Nat → KExpr → KExpr
  | 0, .forallE d b m =>
    match d.getAppFn with
    | .const k ls => .forallE (Ix.Kernel.Expr.mkAppN (.const k (ls ++ [.zero])) d.getAppArgs) b m
    | _ => .forallE d b m
  | n + 1, .forallE d b m => .forallE d (majorMoreLevels n b) m
  | _, e => e

/-- The recursor's stored type with its major premise's domain at one more level: no longer at as
many levels as the rules' constructors have level parameters (`RecCtorsRaw`). -/
def mutateRecMajor (i : Input) (r : CId) : Input :=
  { i with env := mapConst i.env (i.κ r) fun
      | .recInfo cv mI rP rules => .recInfo { cv with type := majorMoreLevels mI cv.type } mI rP rules
      | ci => ci }

/-- The first rule's body (under `n` λs) made the literal `0`, in the kernel's reading and the
program alike: it still corresponds (`RecStored`), but the body is not a variable, so the
recursor is not flat. -/
def mutateRecBody (i : Input) (r : CId) (n : Nat) : Input :=
  mapRecRules i r
    (fun | r0 :: rest => { r0 with rhs := setLamBodyK n r0.rhs (.lit (.natVal 0)) } :: rest
         | rs => rs)
    (fun | r0 :: rest => { r0 with rhs := setLamBody n r0.rhs (.natLit 0) } :: rest | rs => rs)

/-- `n` nested `Nat.succ`s around `Nat.zero`. -/
def succs (n : Nat) : KExpr := (List.range n).foldl (fun e _ => .app succK e) zeroK

/-- The kernel as an oracle on a widening closure: every accepted site typed in the graph regime,
refused where the datum holds, the walk's refusals `runRefused`'s; the counts. -/
def oracleOn (a : Assert) (label : String) (core : Oracle.Core) (i : Input) : IO Oracle.Tally := do
  let t := Oracle.tally core i.src i.env i.κ i.lpsOf i.ann i.Sl
  expect a (t.selfCheckBad == 0 && t.declined == 0)
    s!"{label}: the walk's verdicts differ from runRefused: {repr t}"
  expect a (t.agree == t.acceptedInstances && t.disagree == 0 && t.errors == 0)
    s!"{label}: the kernel does not type an accepted site in the graph regime: {repr t}"
  expect a (t.refusedThere == t.datumHolds)
    s!"{label}: a site is accepted at a profile where the kernel's datum holds: {repr t}"
  return t

/-- The root's result type: `Nat`, or the pinned `Bool`. -/
def resTy (s : Subject) (i : Input) : Option FoTy :=
  if s.boolResult then i.src.known.bool.map .enum else some .nat

/-- The arguments' kernel terms. -/
def argTerms (i : Input) : List Value → List KExpr
  | [] => []
  | .lit n :: xs => litE n :: argTerms i xs
  | .con c _ _ _ :: xs => .const (i.κ c) [] :: argTerms i xs
  | _ :: xs => litE 0 :: argTerms i xs

def run : IO Bool := do
  let a : Assert ← IO.mkRef 0
  try
    let mut fib? : Option Input := none
    let mut fcore? : Option Oracle.Core := none
    let mut dec? : Option (Input × CId) := none
    for s in subjects do
      let (i, core) ← load s
      expect a i.keyless.isEmpty s!"{s.label}: constants of Sl without a kernel key: {i.keyless}"
      let bad := failing i
      expect a bad.isEmpty s!"{s.label}: the check's conjuncts {bad} are false"
      expect a (groundCheck i.src i.env i.κ i.lpsOf i.ann i.Sl)
        s!"{s.label}: groundCheck is false"
      let out := match Src.run i.src 100000 i.rootId s.args with
        | .ok v => readbackAll i.src v
        | _ => none
      expect a (out == some s.expected) s!"{s.label}: SrcEval read back {repr out}"
      -- the root's checks
      let some res := resTy s i | throw (IO.userError s!"{s.label}: no pinned Bool")
      let rbad := (rootParts i.src i.env i.κ i.Sl i.ann i.rootId s.argTys res).filterMap
        fun (n, b) => if b then none else some n
      expect a rbad.isEmpty s!"{s.label}: the root's conjuncts {rbad} are false"
      expect a (foArgsB i.src i.κ s.argTys s.args (argTerms i s.args))
        s!"{s.label}: the arguments are not first-order"
      expect a (resultTagB i.src i.env i.κ i.Sl res s.expected)
        s!"{s.label}: the observed tag does not name one constructor"
      if s.boolResult then
        let some boolD := i.src.known.bool | throw (IO.userError "decide: no pinned Bool")
        expect a (boolListedB i.src boolD) "decide: Bool's listed constructor 1 is not Bool.true"
        dec? := some (i, boolD)
      IO.println s!"{s.label}: {i.Sl.length} constants, every conjunct of the check and of the \
        root's checks true; SrcEval reads back {repr out}"
      -- the direct route (G2a): no site refused
      expectL a (directOk i) fun _ =>
        s!"{s.label}: sitesDirect is false: {(refusedSites i).length} sites refused"
      IO.println s!"{s.label}: sitesDirect true: none of {(allRunSites i).length} application sites \
        of the run terms refused"
      -- the kernel as an oracle at every site the direct route accepts
      let t := Oracle.tally core i.src i.env i.κ i.lpsOf i.ann i.Sl
      expect a (t.selfCheckBad == 0 && t.declined == 0 && t.accepted == t.sites)
        s!"{s.label}: the walk's verdicts differ from runRefused, or refuse: {repr t}"
      expect a (t.agree == t.acceptedInstances && t.disagree == 0 && t.errors == 0)
        s!"{s.label}: the kernel does not type an accepted site in the graph regime: {repr t}"
      expect a (t.refusedThere == t.datumHolds)
        s!"{s.label}: a site is accepted at a profile where the kernel's datum holds: {repr t}"
      expect a ((t.sites, t.instances, t.datumHolds) == s.oracle)
        s!"{s.label}: oracle counts {(t.sites, t.instances, t.datumHolds)}, expected {s.oracle}"
      IO.println s!"{s.label}: the kernel types all {t.acceptedInstances} site-profile instances the \
        direct route accepts ({t.accepted} sites) in the graph regime; at the {t.datumHolds} \
        site-profile pairs where its datum is a proposition, the walk refuses"
      if s.label == "fib" then
        fib? := some i
        fcore? := some core
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
    let some (icase, cc) := mutateCase i | throw (IO.userError "fib: no case entry to mutate")
    let cs := failing icase
    expect a (cs == ["caseShape"]) s!"swapped minors of c{cc}: false conjuncts {cs}, expected [caseShape]"
    -- the restricted laws: a `case` over a family that can be a proposition is refused by
    -- `caseShape`, a projection out of such a structure by `proj`
    let ns := failing (mutateIndSort i Ix.Kernel.natName)
    expect a (ns == ["caseShape"])
      s!"Nat made a family of propositions: false conjuncts {ns}, expected [caseShape]"
    let pcands : List Input := i :: (dec?.map (·.1)).toList
    let some (pj, ps) := pcands.findSome? (fun j => (projectedStruct j).map fun s => (j, s))
      | throw (IO.userError "no structure with fields and its constructor in Sl in either subject")
    let pp := failing (mutateIndSort pj (pj.κ ps))
    expect a (pp == ["proj"])
      s!"structure c{ps} made a family of propositions: false conjuncts {pp}, expected [proj]"
    -- the direct route's controls: each makes `sitesDirect` false and leaves `groundCheck` true
    let some (ia, ka) := mutateArgType i | throw (IO.userError "fib: no constant argument")
    expectL a (!directOk ia && (failing ia).isEmpty) fun _ =>
      s!"argument {ka}'s stored type made Nat: sitesDirect {directOk ia}, false conjuncts {failing ia}"
    let some (ih, kh) := mutateHeadDatum i | throw (IO.userError "fib: no head with a `never` binder")
    expectL a (!directOk ih && (failing ih).isEmpty) fun _ =>
      s!"head {kh}'s first binder datum made always: sitesDirect {directOk ih}, false conjuncts {failing ih}"
    IO.println s!"direct-route controls: argument {ka}'s type made Nat, head {kh}'s datum made \
      always a proposition: sitesDirect false, groundCheck true"
    IO.println s!"negative controls: each mutation falsifies exactly its conjunct \
      (valueCorr, eqnCorr, okClosed, natBasis, caseShape at c{cc}; Nat made Prop: caseShape; \
      structure c{ps} made Prop: proj)"
    -- the root's checks, on `decide`
    let some (di, boolD) := dec? | throw (IO.userError "no decide subject")
    expect a (!resultTagB di.src di.env di.κ di.Sl (.enum boolD) (.ctor 0 []))
      "decide: the observation `false` passes resultTag (expected the documented rejection)"
    let some natZ := di.src.known.natZero | throw (IO.userError "decide: no pinned Nat.zero")
    let some tru := di.src.known.boolTrue | throw (IO.userError "decide: no pinned Bool.true")
    expect a (foArgsB di.src di.κ [.enum boolD] [.con tru [] [] []] [.const (di.κ tru) []])
      "decide: Bool.true is not a first-order Bool argument"
    expect a (!foArgsB di.src di.κ [.enum boolD] [.con natZ [] [] []] [.const (di.κ natZ) []])
      "decide: Nat.zero passes as a Bool argument"
    let some natD := di.src.known.nat | throw (IO.userError "decide: no pinned Nat")
    let dm := { di with src := { di.src with known := { di.src.known with bool := some natD } } }
    expect a (!boolListedB dm.src natD) "decide: Bool re-pinned at Nat passes boolListed"
    expect a (failing dm).isEmpty s!"decide: Bool re-pinned at Nat falsifies {failing dm}"
    IO.println "root controls on decide: resultTag rejects `false` (PUnit.unit at index 0); \
      foArgs rejects Nat.zero as a Bool argument; boolListed rejects Bool re-pinned at Nat, \
      groundCheck unaffected"
    -- G2b. Levels: `imax a a` against `a`, and controls that differ at some assignment
    let u : Ix.Kernel.Level := .param 0
    let w : Ix.Kernel.Level := .param 1
    expect a (lvlEq (.imax u u) u && lvlEq (.imax (.imax .zero u) u) u &&
        lvlEq (.max (.imax u u) w) (.max u w) && lvlEq (.imax (.imax u w) (.imax u w)) (.imax u w))
      "lvlEq misses `imax a a` against `a`"
    expect a (!lvlEq (.imax u w) u && !lvlEq (.imax u u) w && !lvlEq (.imax u .zero) u)
      "lvlEq equates two levels that differ at some assignment"
    -- the fuel: a nested argument costs two levels, so 31 nested `Nat.succ`s are typed at the
    -- check's fuel and 32 are not
    let xf : DCtx := { tab := KTab.of i.env, lps := [], profs := [[]] }
    expect a (dInfer xf directFuel [] (succs 31) == some natK && (dInfer xf directFuel [] (succs 32)).isNone)
      s!"the fuel: 31 nested Nat.succ typed {dInfer xf directFuel [] (succs 31) |>.isSome}, \
        32 typed {dInfer xf directFuel [] (succs 32) |>.isSome}"
    -- `Nat` primitives on literals: the direct route's head reduction gives `eval2`'s value, and
    -- so does the kernel's (fib's reading holds `Nat.add` and `Nat.ble`)
    let some fcore := fcore? | throw (IO.userError "no fib subject")
    for (op, x, y) in [(Src.PrimOp.add, 3, 5), (.add, 0, 0), (.ble, 3, 5), (.ble, 5, 3), (.ble, 4, 4)] do
      let t : KExpr := primApp op x y
      let exp : KExpr := primResultE (op.eval2 x y)
      expect a (whnfD xf directFuel false [] t == some exp)
        s!"{op.name} {x} {y}: the direct route's head reduction gives {repr (whnfD xf directFuel false [] t)}"
      expect a (match Oracle.kernelWhnf fcore t with | .ok r => r == exp | .error _ => false)
        s!"{op.name} {x} {y}: the kernel's head normal form is not eval2's value"
    IO.println "G2b levels, fuel and Nat primitives: lvlEq takes imax a a for a and refuses three \
      different pairs; 31 nested Nat.succ typed, 32 not; Nat.add and Nat.ble on literals reduce to \
      eval2's value, as in the kernel"
    -- ι, `Nat` arithmetic on literals and `imax u u`, on `tags16`: the landed route refused 36 of
    -- its 200 sites, the widened one none
    let (ti, tcore) ← loadClosure "tags16" "fixtures/corpus/phase1-boundary/tags16" ["Limits.tags16"]
    expectL a (directOk ti) fun _ => s!"tags16: sitesDirect is false: {(refusedSites ti).length} sites refused"
    let tt ← oracleOn a "tags16" tcore ti
    expect a ((tt.sites, tt.instances, tt.datumHolds) == (200, 214, 76))
      s!"tags16: oracle counts {(tt.sites, tt.instances, tt.datumHolds)}, expected (200, 214, 76)"
    let some br := boolRec? ti.env | throw (IO.userError "tags16: no Bool.rec in the reading")
    let tm := mutateRecRules ti br
    expect a (!directOk tm) "tags16: Bool.rec's `true` rule given the `false` rule's right-hand side, and sitesDirect is still true"
    IO.println s!"tags16: sitesDirect true, the kernel agrees at all {tt.acceptedInstances} accepted \
      site-profile instances; Bool.rec's `true` rule given `false`'s right-hand side: sitesDirect false ({(refusedSites tm).length} \
      sites refused)"
    -- string literals, on `panic`: the landed route refused 34 of its 762 sites (25 at string
    -- literals), the widened one 1 (a `Char` validity proof), none since G3's cost fix (a
    -- telescope's width costs no fuel), the kernel agreeing
    let (pa, pcore) ← loadClosure "panic" "fixtures/corpus/phase1-decline/panic" ["Decline.withPanic"]
    let pt ← oracleOn a "panic" pcore pa
    expect a ((pt.sites, pt.accepted) == (762, 762))
      s!"panic: {pt.accepted} of {pt.sites} sites accepted, expected 762 of 762"
    let pm := mutateStringOfList pa
    let npm := (refusedSites pm).length
    expect a (npm > (refusedSites pa).length)
      s!"panic: String.ofList's codomain made Nat, and no more site is refused"
    IO.println s!"panic: {pt.accepted} of {pt.sites} sites accepted, the kernel agrees at all \
      {pt.acceptedInstances} accepted instances; String.ofList's codomain made Nat: \
      {npm} refused"
    -- the renaming-tolerant `case` shape, on `OS16-plain`: `List.casesOn`'s recursor names its
    -- level parameters apart; the landed check refused the closure at `caseShape` alone
    let (oi, _) ← loadClosure "OS16-plain" "fixtures/ownership/OS16-plain" []
    expect a (failing oi).isEmpty s!"OS16-plain: the check's conjuncts {failing oi} are false"
    let some (rc, rr) := renamedCase? oi | throw (IO.userError "OS16-plain: no case entry named apart")
    let om := { oi with env := mapConst oi.env (oi.κ rc) fun
      | .defnInfo cv val h => .defnInfo cv (revRecLevels (oi.κ rr) val) h
      | ci => ci }
    expect a (failing om == ["caseShape"])
      s!"OS16-plain: c{rc}'s recursor called at its levels reversed: false conjuncts {failing om}"
    IO.println s!"OS16-plain: every conjunct of the check true (c{rc}'s recursor named apart); its \
      levels reversed in casesOn's body: exactly caseShape false"
    -- G3: recursors. As first landed, `declOk` admitted no class; with none admitted the check
    -- is the landed one, true on `fib`
    expect a (failingWith [] i).isEmpty
      s!"fib: with no recursor class admitted, false conjuncts {failingWith [] i}"
    -- `tak`: `Eq.rec` (run by `Eq.ndrec`) is its only recursor; since G3's part C its class is
    -- admitted (F3 proved), and every conjunct of the check is true
    let (ki, _) ← loadClosure "tak" "fixtures/ixon-v4/bench-k1/tak" ["entry"]
    let some er := eqRecOf? ki | throw (IO.userError "tak: no Eq.rec in Sl")
    expect a (recClassB ki.src ki.env ki.κ er == some .eqRec && admittedClasses.contains .eqRec &&
        eqRecBasisB ki.env && (failing ki).isEmpty)
      s!"tak: Eq.rec c{er} class {repr (recClassB ki.src ki.env ki.κ er)}, EqRecBasis {eqRecBasisB ki.env}, false conjuncts {failing ki}, expected none"
    expect a (failingWith [.empty] ki == ["declOk"])
      s!"tak: with only the class empty admitted (parts A and B), false conjuncts {failingWith [.empty] ki}, expected [declOk]"
    -- controls: each makes exactly `recShape` false
    let kr := failing (mutateEqRecRule ki)
    expect a (kr == ["recShape"]) s!"tak: Eq.rec's rule rhs made 0: false conjuncts {kr}, expected [recShape]"
    let ka := failing (mutateEqRecArity ki)
    expect a (ka == ["recShape"]) s!"tak: Eq.rec's type cut by one binder: false conjuncts {ka}, expected [recShape]"
    let kf := failing (mutateEqRefl ki)
    expect a (kf == ["recShape"]) s!"tak: Eq.refl's first binder datum made never: false conjuncts {kf}, expected [recShape]"
    -- `EqRecBasis`' own controls: `RecStored` still holds, `EqRecBasis` alone is false
    let mA := mutateEqRecRhsA ki er
    let kA := failing mA
    expect a (kA == ["recShape"] && recStoredB mA.src mA.env mA.κ mA.lpsOf er && !eqRecBasisB mA.env)
      s!"tak: Eq.rec's rule made λ α a motive refl. a (kernel and program): false conjuncts {kA}, RecStored {recStoredB mA.src mA.env mA.κ mA.lpsOf er}, EqRecBasis {eqRecBasisB mA.env}"
    let mT := mutateEqRecType ki
    let kT := failing mT
    expect a (kT == ["recShape"] && recStoredB mT.src mT.env mT.κ mT.lpsOf er && !eqRecBasisB mT.env)
      s!"tak: Eq.rec's major domain made @Eq α b a: false conjuncts {kT}, RecStored {recStoredB mT.src mT.env mT.κ mT.lpsOf er}, EqRecBasis {eqRecBasisB mT.env}"
    -- the level parameters permuted: `EqRecBasis` does not read them; `RecStored` refuses it, since
    -- the rule's levels no longer correspond to the program's
    let mL := mutateEqRecLevels ki
    let kL := failing mL
    expect a (kL == ["recShape"] && !recStoredB mL.src mL.env mL.κ mL.lpsOf er && eqRecBasisB mL.env)
      s!"tak: Eq.rec's level parameters reversed: false conjuncts {kL}, RecStored {recStoredB mL.src mL.env mL.κ mL.lpsOf er}, EqRecBasis {eqRecBasisB mL.env}"
    IO.println s!"tak: Eq.rec c{er} of class eqRec, admitted; every conjunct true (with only the \
      class empty admitted, declOk false); Eq.rec's rule rhs made 0, its type cut by one binder, \
      Eq.refl's first binder datum changed, its rule made λ α a motive refl. a (EqRecBasis), its \
      major domain swapped (EqRecBasis), its level parameters reversed (RecStored): exactly recShape false"
    -- G3, part D: flat recursors (no parameter, no field, rule bodies variables). `strictAndOr`:
    -- its recursor `Bool.rec` (run by `Bool.and`, `Bool.or`) is flat, admitted since part D, and
    -- every conjunct is true; with the classes part C admitted, `declOk` alone is false
    let (si, _) ← loadClosure "strictAndOr" "fixtures/corpus/phase1-scalar/strictAndOr"
      ["entryStrictOr", "entryStrictAnd"]
    let some fr := flatRecOf? si | throw (IO.userError "strictAndOr: no flat recursor in Sl")
    expect a ((failing si).isEmpty && admittedClasses.contains .flat)
      s!"strictAndOr: false conjuncts {failing si}, expected none"
    expect a (failingWith [.empty, .eqRec] si == ["declOk"])
      s!"strictAndOr: with the classes of part C, false conjuncts {failingWith [.empty, .eqRec] si}, expected [declOk]"
    -- controls, on `Sl` cut to the flat recursor and `Bool`'s constructors: the closure's
    -- `Bool.casesOn` reads the same stored recursor, so on the whole `Sl` a control on it also
    -- falsifies `caseShape`. Each makes exactly `recShape` false (or, for the class, `declOk`),
    -- and the suite asserts which part refuses
    let ri := { si with Sl := fr :: [si.src.known.boolFalse, si.src.known.boolTrue].filterMap id }
    expect a (failing ri).isEmpty
      s!"strictAndOr cut to c{fr} and Bool's constructors: false conjuncts {failing ri}, expected none"
    let parts (j : Input) : List Bool :=
      [recStoredB j.src j.env j.κ j.lpsOf fr, recTeleB j.env (j.κ fr), recProgB j.src j.κ j.Sl fr,
        recCtorsRawB j.src j.env j.κ fr]
    let mT := mutateRecTele ri fr
    expect a (failing mT == ["recShape"] && parts mT == [true, false, true, true])
      s!"strictAndOr: Bool.rec's first rule's second λ-domain made #0 (kernel and program): false conjuncts {failing mT}, parts (RecStored, RecTele, RecProg, RecCtorsRaw) {parts mT}"
    let mP := mutateRecProg ri fr
    expect a (failing mP == ["recShape"] && parts mP == [true, true, false, true])
      s!"strictAndOr: Bool.rec's two rules swapped (kernel and program): false conjuncts {failing mP}, parts {parts mP}"
    let mC := mutateRecMajor ri fr
    expect a (failing mC == ["recShape"] && parts mC == [true, true, true, false])
      s!"strictAndOr: Bool.rec's major domain at one more level: false conjuncts {failing mC}, parts {parts mC}"
    let nPre := match si.src.decl? fr with
      | some (.recr _ _ _ np nmot nmin _ _ _ _) => np + nmot + nmin
      | _ => 0
    let mB := mutateRecBody ri fr nPre
    expect a (failing mB == ["declOk"] && recClassB mB.src mB.env mB.κ fr == some .ordinary)
      s!"strictAndOr: Bool.rec's first rule's body made 0 (kernel and program): false conjuncts {failing mB}, class {repr (recClassB mB.src mB.env mB.κ fr)}"
    IO.println s!"strictAndOr: Bool.rec c{fr} of class flat, admitted; every conjunct true (with the \
      classes of part C, declOk false); cut to c{fr} and Bool's constructors: a rule's λ-domain \
      changed (RecTele), its rules swapped (RecProg), its major domain at one more level \
      (RecCtorsRaw): exactly recShape false; a rule's body made 0: not flat, exactly declOk false"
    IO.println s!"tests-grounding: {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding: {error}"
    return false

end IxCCTests.Grounding
