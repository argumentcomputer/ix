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

/-- The refused sites of `Sl`'s run terms. -/
def refusedSites (i : Input) : List (CId × Site) :=
  i.Sl.flatMap fun c => (runPairsB i.src i.env i.κ c).flatMap fun (t, e) =>
    (runRefused i.src i.env i.lpsOf i.ann c t e).map fun s => (c, s)

def directOk (i : Input) : Bool := sitesDirectB i.src i.env i.κ i.lpsOf i.ann i.Sl

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
      expect a (directOk i)
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
    expect a (!directOk ia && (failing ia).isEmpty)
      s!"argument {ka}'s stored type made Nat: sitesDirect {directOk ia}, false conjuncts {failing ia}"
    let some (ih, kh) := mutateHeadDatum i | throw (IO.userError "fib: no head with a `never` binder")
    expect a (!directOk ih && (failing ih).isEmpty)
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
    IO.println s!"tests-grounding: {← a.get} assertions passed"
    return true
  catch error =>
    IO.eprintln s!"FAIL: grounding: {error}"
    return false

end IxCCTests.Grounding
