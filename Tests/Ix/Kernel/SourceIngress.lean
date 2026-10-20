import LSpec
import Ix.Meta
import Ix.LeanIngress.Theorems
import Tests.Ix.Kernel.SourceIngressStep
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.ReaderFidelityDefs
import Tests.Ix.Kernel.SourceIngressDefs
import Tests.Ix.Kernel.SourceIngressReducedDefs

/-! # The Source-mode check on compiled Lean declarations (`lake test -- kernel-source-ingress`)

The declarations of `Tests.Ix.Kernel.ReaderFidelityDefs` (the Ixon reader's
fidelity fixtures: structures, nested, mutual, indexed and reflexive
inductives, projections, quotients, literals, theorems, opaques, axioms, and
the `partial`/`unsafe` definitions the reader declines) and everything in
`Init` they reach are canonicalized (`Ix.CanonM`), condensed (`Ix.GraphM`,
`Ix.CondenseM`) and checked in Source mode (`Ix.LeanIngress`) at Source mode's
evidence (`Ix.LeanIngress.sourceEvidence`: the certificate theorems of
`IxC.Kernel.PinGen.Certs`, loaded and checked with the fixtures):

* group by group (`Tests.Ix.Kernel.SourceIngressStep`), where every fixture
  declaration must get its expected verdict;
* all at once (`checkSource`), on the closure of the fixtures that are
  expected to be accepted, which must be accepted; and the tiered check
  (`checkSourceTiered`) on that closure with the partial companion
  `spin._unsafe_rec`, which must accept it with the companion typed;
* on hand-built terms: a free variable, a metavariable and a level
  metavariable are refused, `mdata` is erased, a binder carries the Lean
  fragment's contracts unless a contract frame (`ix.contract`) wraps it,
  whose contract it then carries (a `let` frame's is erased, and a frame
  the compiler refuses is refused), level parameters become positions (a
  large eliminator's elimination level after its block's), and the
  conversion of a shared DAG is the tree conversion. -/

namespace Tests.Ix.Kernel.SourceIngress

open LSpec
open Ix.LeanIngress
open Tests.Ix.Kernel.SourceIngressStep

def defsModule : Lean.Name := `Tests.Ix.Kernel.ReaderFidelityDefs

def defs (n : String) : Lean.Name := defsModule ++ n.toName

def ownModule : Lean.Name := `Tests.Ix.Kernel.SourceIngressDefs

def own (n : String) : Lean.Name := ownModule ++ n.toName

def reducedModule : Lean.Name := `Tests.Ix.Kernel.SourceIngressReducedDefs

def reduced (n : String) : Lean.Name := reducedModule ++ n.toName

/-- The prelude's constants, so that the environment declares its own copy of
each (the check then runs on them, not on the committed prelude). -/
def preludeNames : Array Lean.Name := #[`Eq, `Nat, `PUnit, `Empty, `False, `Quot, `Quot.mk,
  `Quot.lift, `Quot.ind, `Quot.sound, `And, `Bool]

/-- The closure of `seeds` and the prelude in the fixture module's
environment, canonicalized. -/
def envOf (leanEnv : Lean.Environment) (seeds : Array Lean.Name) : IO Ix.Environment := do
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv (seeds ++ preludeNames))
  return canon closed.toArray

/-- The verdict each fixture declaration must get. -/
def expected : List (Lean.Name × String) := [
  -- inductives: a structure, an extension, indexed, reflexive, nested,
  -- mutual, propositional and universe-polymorphic blocks
  (defs "Color", "accept"), (defs "Color.rec", "accept"),
  (defs "Point", "accept"), (defs "Point.mk", "accept"), (defs "Point.x", "accept"),
  (defs "Point3", "accept"), (defs "Point3.toPoint", "accept"),
  (defs "Vec", "accept"), (defs "Vec.cons", "accept"),
  (defs "WTree", "accept"), (defs "WTree.rec", "accept"),
  (defs "Rose", "accept"), (defs "Rose.rec_1", "accept"),
  (defs "ATree", "accept"), (defs "ATree.rec_2", "accept"),
  (defs "Node", "accept"), (defs "Node.val", "accept"), (defs "Node.kids", "accept"),
  (defs "Even", "accept"), (defs "Odd.succ", "accept"), (defs "Even.rec", "accept"),
  (defs "Tm", "accept"), (defs "Args.rec", "accept"),
  (defs "Trivial", "accept"), (defs "Both", "accept"), (defs "Both.left", "accept"),
  (defs "Pair", "accept"), (defs "Pair.mk", "accept"),
  -- definitions: projections in a value, structural, nested, mutual and
  -- reflexive recursion, quotient use
  (defs "twice", "accept"), (defs "NatPair", "accept"), (defs "sumPoint", "accept"),
  (defs "Vec.length", "accept"), (defs "Rose.size", "accept"),
  (defs "isEven", "accept"), (defs "isOdd", "accept"), (defs "Tm.size", "accept"),
  (defs "WTree.depthAt", "accept"),
  (own "BoolQ", "accept"), (own "BoolQ.mk", "accept"), (own "BoolQ.const", "accept"),
  -- fields whose occurrence of the block whnf removes (CQX.8; Lean's kernel
  -- tests positivity after whnf): nested (`V`, `W`), mutual (`A`, `B`) and
  -- single (`S`); `T` (lane P's reproducer) and `U`, the nested shapes at
  -- `Sort u`, get past that test and are declined by the modeller's residual
  -- for a non-`Prop` nested block with a small eliminator
  (reduced "V", "accept"), (reduced "V.mk", "accept"), (reduced "V.rec", "accept"),
  (reduced "V.rec_1", "accept"), (reduced "v_rec", "accept"),
  (reduced "W", "accept"), (reduced "W.mk", "accept"), (reduced "W.rec_1", "accept"),
  (reduced "A", "accept"), (reduced "A.mk", "accept"), (reduced "B.rec", "accept"),
  (reduced "a_rec", "accept"),
  (reduced "S", "accept"), (reduced "S.mk", "accept"), (reduced "s_rec", "accept"),
  (reduced "T", "decline"), (reduced "T.rec_1", "decline"), (reduced "t_rec", "blocked"),
  (reduced "U", "decline"), (reduced "U.mk", "decline"),
  -- the reader's fixture quotient divides (`parity`): `Nat.mod` is accepted
  -- on its certificate theorems' evidence, so the quotient is too
  (defs "ParityQ", "accept"), (defs "ParityQ.toBool", "accept"),
  (defs "ParityQ.toBool_mk", "accept"),
  -- literals
  (defs "smallNat", "accept"), (defs "bigNat", "accept"),
  -- theorems, opaques, axioms
  (own "BoolQ.mk_eq", "accept"), (own "BoolQ.const_eq", "accept"), (defs "bigNat_pos", "accept"),
  (defs "twice_id", "accept"), (defs "isEven_two", "accept"), (defs "even_two", "accept"),
  (defs "secret", "accept"),
  -- the checker admits the standard axioms only
  (defs "fidelityAxiom", "decline"),
  (defs "levelMax", "accept"), (defs "levelImax", "accept"),
  -- a `partial` definition's compiled companion and an `unsafe` definition
  -- are typed by the typing tier (`checkSourceTiered`)
  (defs "spin._unsafe_rec", "typed"), (defs "unsafeId", "typed"),
  -- `Nat.div` is a certified operation, accepted on the proof evidence of
  -- the certificate theorems the environment carries
  -- (`IxC.Kernel.PinGen.Certs`, Source mode's evidence); the well-founded
  -- `log2` divides
  (`Nat.div, "accept"), (defs "log2", "accept"),
  -- the prelude, checked on the environment's own copies
  (`Eq, "accept"), (`Eq.rec, "accept"), (`Nat, "accept"), (`Quot, "accept"),
  (`Quot.lift, "accept"), (`Quot.sound, "accept"), (`Bool, "accept"), (`And, "accept")]

/-- Seeds whose closure is accepted as a whole by `checkSource`. -/
def acceptedSeeds : Array Lean.Name := #[defs "Color", defs "Point3", defs "Vec.length",
  defs "WTree.depthAt", defs "Rose.size", defs "ATree", defs "Node", defs "Even", defs "Tm.size",
  defs "Trivial", defs "Both", defs "NatPair", defs "sumPoint", defs "isEven_two", defs "even_two",
  own "BoolQ.mk_eq", own "BoolQ.const_eq", defs "smallNat", defs "bigNat", defs "twice_id",
  defs "secret", defs "levelMax", defs "levelImax"]

/-- Seeds of the reduced-field fixtures (CQX.8) whose closure is accepted as a
whole by `checkSource`, apart from `acceptedSeeds`, which `cert-statement`
also compiles. -/
def reducedSeeds : Array Lean.Name := #[reduced "v_rec", reduced "W", reduced "a_rec",
  reduced "s_rec"]

/-! ## Terms -/

def anon : Ix.Name := .mkAnon
def nm (s : String) : Ix.Name := .mkStr anon s

/-- The numbering of a constant with no level parameters. -/
def noParams : Numbering := ⟨#[], false⟩

def refusals : TestSeq :=
  let fv := Ix.Expr.mkFVar (nm "x")
  let mv := Ix.Expr.mkMVar (nm "m")
  let lv := Ix.Expr.mkSort (Ix.Level.mkMvar (nm "u"))
  let refused (e : Ix.Expr) (k : ExprError → Bool) : Bool :=
    match ingressExprs noParams.pos [Ix.Expr.mkApp (Ix.Expr.mkBVar 0) e] with
    | .error err => k err
    | .ok _ => false
  test "free variable refused" (refused fv fun | .fvar _ => true | _ => false) ++
  test "metavariable refused" (refused mv fun | .mvar _ => true | _ => false) ++
  test "level metavariable refused" (refused lv fun | .levelMVar _ => true | _ => false)

def sameResult : Except ExprError (List KExpr) → Except ExprError (List KExpr) → Bool
  | .ok a, .ok b => a == b
  | _, _ => false

def lamDropped : Except ExprError (List KExpr) → Bool
  | .ok [.lam (.const n []) (.bvar 0) m] => n == Ix.Kernel.roleKey .nat && m == { pw := .never }
  | _ => false

def erasure : TestSeq :=
  let body := Ix.Expr.mkConst (nm "Nat") #[]
  let withData := Ix.Expr.mkMData #[(nm "k", .ofBool true)] body
  let lam := Ix.Expr.mkLam (nm "x") body (.mkBVar 0) .implicit
  test "mdata erased"
    (sameResult (ingressExprs noParams.pos [withData]) (ingressExprs noParams.pos [body])) ++
  test "binder name and info dropped, pw never" (lamDropped (ingressExprs noParams.pos [lam]))

/-- `e` under the contract frame of `c`, as `Ix.Compile.CompileInput.prepare`
writes it and `Ix.CanonM` keeps it. -/
def framed (c : Ix.SemanticContract.Contract) (e : Ix.Expr) : Ix.Expr :=
  Ix.Expr.mkMData c.ixMetadata e

def binderOf : Except ExprError (List KExpr) → Option Ix.Kernel.BinderMeta
  | .ok [.lam _ _ m] | .ok [.forallE _ _ m] => some m
  | _ => none

def frameRefused : Except ExprError (List KExpr) → Bool
  | .error (.contract _) => true
  | _ => false

def letOf : Except ExprError (List KExpr) → Option Ix.Kernel.LetMeta
  | .ok [.letE _ _ _ l] => some l
  | _ => none

def sameTree : Except ExprError (List KExpr) → Except ExprError KExpr → Bool
  | .ok [a], .ok b => decide (a = b)
  | _, _ => false

/-- Binder contracts: a plain binder carries the Lean fragment's, and a
contract frame puts its contract on the binder it wraps, as the compiler
lowers it; a plain `let` carries Lean's let contract and a `let` frame puts
its binder contract and kind on the let it wraps; a frame the compiler
refuses is refused. -/
def contractFrames : TestSeq :=
  let nat := Ix.Expr.mkConst (nm "Nat") #[]
  let lam := Ix.Expr.mkLam (nm "x") nat (.mkBVar 0) .default
  let pi := Ix.Expr.mkForallE (nm "x") nat nat .default
  let letE := Ix.Expr.mkLetE (nm "y") nat (Ix.Expr.mkConst (nm "Nat.zero") #[]) (.mkBVar 0) false
  let plain (e : Ix.Expr) := Ix.Expr.mkMData #[(nm "k", .ofBool true)] e
  let conv (e : Ix.Expr) := ingressExprs noParams.pos [e]
  let lamC : Ix.SemanticContract.Contract := { kind := .lam, binder := .linear }
  let allC : Ix.SemanticContract.Contract :=
    { kind := .all, binder := .erased, result := .localUnique }
  let letC : Ix.SemanticContract.Contract := { kind := .letE, binder := .affine }
  let key := Ix.Name.mkStr (nm "ix") "contract"
  let dag := Ix.Expr.mkApp (framed allC pi) (plain (framed lamC lam))
  test "a plain binder carries the Lean fragment's contracts"
    (binderOf (conv lam) == some { pw := .never, contract := .many, result := .shared }) ++
  test "a lam frame's contract is the binder's"
    (binderOf (conv (framed lamC lam)) == some { pw := .never, contract := .linear }) ++
  test "an all frame's input and result contracts are the binder's"
    (binderOf (conv (framed allC pi)) ==
      some { pw := .never, contract := .erased, result := .localUnique }) ++
  test "a plain let carries Lean's let contract"
    (letOf (conv letE) == some { contract := .lean false }) ++
  test "a let frame's contract is the let's"
    (letOf (conv (framed letC letE)) ==
      some { contract := { nonDep := false, kind := letC.letKind, binder := .affine } }) ++
  test "plain metadata around a frame is erased"
    (binderOf (conv (plain (framed lamC lam))) == some { pw := .never, contract := .linear }) ++
  test "a frame not directly around a binder of its kind is refused"
    (frameRefused (conv (framed lamC (plain lam))) && frameRefused (conv (framed lamC pi)) &&
      frameRefused (conv (framed allC nat))) ++
  test "a malformed frame is refused"
    (frameRefused (conv (Ix.Expr.mkMData #[(key, .ofNat 3)] lam)) &&
      frameRefused (conv (Ix.Expr.mkMData #[(key, .ofNat 2), (Ix.Name.mkStr key "kind", .ofNat 0),
        (Ix.Name.mkStr key "code", .ofNat 1)] lam))) ++
  test "the DAG walk is the tree walk on frames"
    (sameTree (ingressExprsShared noParams.pos [dag]) (ingressExpr noParams.pos dag))

def sortOf : Except ExprError (List KExpr) → Option Ix.Kernel.Level
  | .ok [.sort l] => some l
  | _ => none

/-- Level parameters are positions: a constant's `i`-th is `i`, and a large
eliminator's first, its elimination level, follows its block's. -/
def numbering : TestSeq :=
  let u := nm "u"
  let v := nm "v"
  let ty := Ix.Expr.mkSort (Ix.Level.mkMax (Ix.Level.mkParam u) (Ix.Level.mkParam v))
  let large : Numbering := ⟨#[v, u], true⟩
  test "the i-th level parameter is position i"
    (sortOf (ingressExprs (Numbering.mk #[u, v] false).pos [ty]) ==
      some (.max (.param 0) (.param 1))) ++
  test "a large eliminator's elimination level follows its block's parameters"
    (sortOf (ingressExprs large.pos [ty]) == some (.max (.param 0) (.param 1)) &&
      large.params == [1, 0])

/-- Levels in the compiler's canonical form (`canonLevel`), read as the
reader reads a compiled universe: `Ixon.canonUniv` over the Lean index order
(variable `i` is the constant's `i`-th Lean level parameter), back through
`Reader.convUniv` (at a large eliminator through `Reader.recParam`, the
elimination level first). -/
def canonical : TestSeq :=
  let u := nm "u"
  let v := nm "v"
  let plain : Numbering := ⟨#[u, v], false⟩
  -- a large eliminator of a block with one parameter `u`: Lean's list is
  -- `[v, u]`, `v` the elimination level (position 1, index 0)
  let large : Numbering := ⟨#[v, u], true⟩
  let read (param : Nat → Ix.Kernel.LevelParam) (w : Ixon.Univ) : KLevel :=
    Ix.Kernel.Reader.convUniv param (Ixon.canonUniv w)
  let recP := Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps true [0])
  let cases : List (KLevel × Ixon.Univ) := [
    (.max (.param 1) (.param 0), .max (.var 1) (.var 0)),
    (.max (.param 0) (.succ (.param 0)), .max (.var 0) (.succ (.var 0))),
    (.imax (.param 1) (.max (.param 0) (.param 1)), .imax (.var 1) (.max (.var 0) (.var 1))),
    (.succ (.max (.zero) (.param 1)), .succ (.max .zero (.var 1)))]
  test "a member's level is the reader's reading of its compiled universe"
    (cases.all fun (l, w) => canonLevel plain l == read (fun i => i) w) ++
  test "at a large eliminator the index order puts the elimination level first"
    -- Source `max u v` is positions `max 0 1`; compiled, `u` is variable 1
    (canonLevel large (.max (.param 0) (.param 1)) == read recP (.max (.var 1) (.var 0)) &&
      canonLevel large (.imax (.param 1) (.param 0)) == read recP (.imax (.var 0) (.var 1))) ++
  test "canonical forms do not depend on the order of a max"
    (canonLevel plain (.max (.param 0) (.param 1)) == canonLevel plain (.max (.param 1) (.param 0))) ++
  test "canonicalizing is idempotent"
    (cases.all fun (l, _) => canonLevel plain (canonLevel plain l) == canonLevel plain l) ++
  test "mapLevels' executed walk is the structural map"
    (let e : KExpr := .app (.sort (.max (.param 1) (.param 0)))
        (.const (ingressKey (nm "f")) [.max (.param 1) (.param 0)])
     mapLevelsList (canonLevel plain) [e, e] ==
      [e, e].map (mapLevels (canonLevel plain)))

/-- A DAG of depth `n` whose tree has `2^n` leaves: the shared conversion
finishes, and agrees with the tree conversion at a depth the tree walk still
manages. -/
def sharedDag (n : Nat) : Ix.Expr := Id.run do
  let mut e := Ix.Expr.mkConst (nm "Nat") #[]
  for _ in [0:n] do e := Ix.Expr.mkApp e e
  return e

def treeSize : Ix.Kernel.Expr .source → Nat
  | .app f a => treeSize f + treeSize a + 1
  | _ => 1

def agrees : Except ExprError (List KExpr) → Except ExprError KExpr → Bool
  | .ok [a], .ok b => decide (a = b) && treeSize b == 2 ^ 13 - 1
  | _, _ => false

def sharing : TestSeq :=
  test "a 2^64-leaf DAG converts" ((ingressExprs noParams.pos [sharedDag 64]).isOk) ++
  test "the DAG walk is the tree walk at depth 12"
    (agrees (ingressExprsShared noParams.pos [sharedDag 12]) (ingressExpr noParams.pos (sharedDag 12)))

/-! ## The fixtures -/

/-- The run on the fixture closure, its expected verdicts, and `checkSource` on
the accepted closure: failures as messages, and lines for the report. -/
def evaluate : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[defsModule, ownModule, reducedModule, `IxC.Kernel.PinGen.Certs]
  let some idx := leanEnv.getModuleIdx? defsModule | throw (IO.userError "fixture module not loaded")
  let some idx' := leanEnv.getModuleIdx? ownModule | throw (IO.userError "fixture module not loaded")
  let some idx'' := leanEnv.getModuleIdx? reducedModule | throw (IO.userError "fixture module not loaded")
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    let m := leanEnv.getModuleIdxFor? n
    if m == some idx || m == some idx' || m == some idx'' then some n else none
  let certs := (Ix.RoleEvidence.certTheorems.flatMap (·.2)).toArray
  let env ← envOf leanEnv (seeds ++ #[`Nat.div] ++ certs)
  let blocks := condense env
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let r ← run pre env blocks
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  for (n, want) in expected do
    match r.rowOf (Ix.Kernel.Key.ofName (Ix.Kernel.Name.ofLeanName n)) with
    | none => errors := errors.push s!"{n}: no verdict"
    | some row =>
      lines := lines.push s!"{n}: {row.outcome} {row.reason}"
      unless row.outcome == want do
        errors := errors.push s!"{n}: expected {want}, got {row.outcome} ({row.reason})"
  let c := r.counts
  lines := lines.push s!"fixture closure: {env.consts.size} constants, {r.rows.size} groups, \
    {r.decls} declarations ({r.generated} generated, {r.projRewrites} projection rewrites); \
    constants by outcome {c.constants.toList}"
  for ((o, why), k) in c.reasons.toList do lines := lines.push s!"  {o} ({k}): {why}"
  -- all at once, on the accepted closure
  let accEnv ← envOf leanEnv acceptedSeeds
  match checkSource accEnv (condense accEnv) with
  | .ok kenv => lines := lines.push s!"checkSource: accepted, {kenv.consts.length} kernel constants \
      from {accEnv.consts.size} Lean constants"
  | .error e => errors := errors.push s!"checkSource on the accepted closure: {e}"
  -- all at once, on the reduced-field fixtures' closure (CQX.8)
  let redEnv ← envOf leanEnv reducedSeeds
  match checkSource redEnv (condense redEnv) with
  | .ok kenv => lines := lines.push s!"checkSource (reduced fields): accepted, \
      {kenv.consts.length} kernel constants from {redEnv.consts.size} Lean constants"
  | .error e => errors := errors.push s!"checkSource on the reduced-field closure: {e}"
  -- the tiered check: the accepted closure with the partial companion, whose
  -- logical part is accepted and whose tier constant is typed
  let tierEnv ← envOf leanEnv (acceptedSeeds.push (defs "spin._unsafe_rec"))
  match checkSourceTiered tierEnv (condense tierEnv) with
  | .ok (kenv, ts) =>
    let spin := ingressKey (Ix.Name.fromLeanName (defs "spin._unsafe_rec"))
    if ts.any (·.cv.name == spin) && !kenv.consts.any (·.name == spin) then
      lines := lines.push s!"checkSourceTiered: accepted, {kenv.consts.length} kernel constants, \
        {ts.length} typed"
    else errors := errors.push s!"checkSourceTiered: {spin} is not typed apart from the logical \
      environment ({ts.length} typed)"
  | .error e => errors := errors.push s!"checkSourceTiered on the accepted closure and spin: {e}"
  return (errors, lines)

def fixtures : TestSeq :=
  .individualIO "source mode: fixture closure, group by group and all at once" none (do
    let (errors, lines) ← evaluate
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, expected.length, 0, msg)) .done

/-! ## Quotient Source (`ALPHA-COLLAPSE.md` §8.4)

Hand-made fiber maps over the module's alias fixtures: an α-equal pair is
collapsed to its first member and the result accepted, with exactly the alias's
declaration dropped; a map identifying unequal declarations is refused; and a
`Bool`-shaped inductive mapped onto `Bool`'s role keys is that role's alias. -/

def kname (n : Lean.Name) : Ix.Kernel.Name := Ix.Kernel.Name.ofLeanName n

def kkey (n : Lean.Name) : Ix.Kernel.Key .source := ingressKey (Ix.Name.fromLeanName n)

def mapOf (pairs : List (Lean.Name × Ix.Kernel.Key .source)) : FiberMap :=
  pairs.foldl (fun m (n, k) => m.insert (kname n) k) {}

def evaluateQuotient : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[ownModule]
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  -- an α-equal pair
  let env ← envOf leanEnv #[own "aliasOne", own "aliasTwo", own "aliasUser"]
  let blocks := condense env
  let ρ := mapOf [(own "aliasTwo", kkey (own "aliasOne"))]
  match leanIngress env blocks pre.state with
  | .error e => errors := errors.push s!"quotient: ingress: {e}"
  | .ok ds =>
    match collapseDecls ρ ds with
    | .error e => errors := errors.push s!"quotient: the α-equal pair: {e}"
    | .ok c =>
      lines := lines.push s!"quotient: {ds.size} declarations, {c.decls.size} kept, dropped \
        {c.dropped.toList}"
      unless c.decls.size + 1 == ds.size && c.dropped.size == 1 do
        errors := errors.push s!"quotient: expected exactly one declaration dropped, got {c.dropped.toList}"
  match checkSourceCollapsedUsing Ix.Kernel.Reader.builtinPrelude ρ (fun _ => none) env blocks with
  | .ok kenv =>
    lines := lines.push s!"quotient: checkSourceCollapsed accepted, {kenv.consts.length} kernel constants"
    if kenv.consts.any (·.name == kkey (own "aliasTwo")) then
      errors := errors.push "quotient: the dropped alias is installed"
  | .error e => errors := errors.push s!"quotient: checkSourceCollapsed on the α-equal pair: {e}"
  -- unequal declarations identified
  let env2 ← envOf leanEnv #[own "aliasOne", own "aliasOther"]
  let ρ2 := mapOf [(own "aliasOther", kkey (own "aliasOne"))]
  match checkSourceCollapsedUsing Ix.Kernel.Reader.builtinPrelude ρ2 (fun _ => none) env2
      (condense env2) with
  | .error (.collapse e) => lines := lines.push s!"quotient: unequal declarations refused: {e}"
  | .error e => errors := errors.push s!"quotient: unequal declarations: another failure: {e}"
  | .ok _ => errors := errors.push "quotient: unequal declarations collapsed"
  -- a role alias: `Flag` onto `Bool`'s role keys
  let env3 ← envOf leanEnv #[own "Flag", `Bool]
  let ρ3 := mapOf [(own "Flag", .role .bool), (own "Flag.off", .role .boolFalse),
    (own "Flag.on", .role .boolTrue), (own "Flag.rec", .role .boolRec)]
  match leanIngress env3 (condense env3) pre.state with
  | .error e => errors := errors.push s!"quotient: role alias: ingress: {e}"
  | .ok ds =>
    match collapseDecls ρ3 ds with
    | .error e => errors := errors.push s!"quotient: role alias: {e}"
    | .ok c =>
      lines := lines.push s!"quotient: role alias: {ds.size} declarations, {c.decls.size} kept"
      unless c.decls.size + 1 == ds.size do
        errors := errors.push s!"quotient: role alias: expected Flag's block dropped"
  match checkSourceCollapsedUsing Ix.Kernel.Reader.builtinPrelude ρ3 (fun _ => none) env3
      (condense env3) with
  | .ok kenv => lines := lines.push s!"quotient: role alias accepted, {kenv.consts.length} kernel constants"
  | .error e => errors := errors.push s!"quotient: role alias: {e}"
  return (errors, lines)

def quotient : TestSeq :=
  .individualIO "quotient source: alias fibers collapsed, mismatches refused, role aliases" none (do
    let (errors, lines) ← evaluateQuotient
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, 3, 0, msg)) .done


/-! ## The `.indDecl` shape guard

`indShapeOk` on synthetic blocks (the guard is syntactic: a declared type
here is any term, only its constants matter), then the fold on a lowered
mutual block (`Tm`/`Args`, the modeled route) whose constructor `Args.cons`
has a declared type naming the earlier constructor `Tm.var`: the modeled
route checks a member against the environment and the earlier members, so
before the guard that name resolved there; the guard refuses it first, with
`checkConstantVal`'s own message. -/

def skey (s : String) : Ix.Kernel.Key .source := .id (Ix.Kernel.Name.ofLeanName s.toName)

def sconst (s : String) : Ix.Kernel.Expr .source := .const (skey s) []

def scv (s : String) (t : Ix.Kernel.Expr .source) : Ix.Kernel.ConstantVal .source :=
  { name := skey s, levelParams := [], type := t }

def sind (s : String) (t : Ix.Kernel.Expr .source) : Ix.Kernel.ConstantInfo .source :=
  .indInfo (scv s t) {}

def sctor (s : String) (t : Ix.Kernel.Expr .source) : Ix.Kernel.ConstantInfo .source :=
  .ctorInfo (scv s t) 0 0

def sty : Ix.Kernel.Expr .source := .sort default

/-- An environment holding `U` only. -/
def withU : Ix.Kernel.Key .source → Option (Ix.Kernel.ConstantInfo .source) := fun n =>
  if n == skey "U" then some (.axiomInfo (scv "U" sty)) else none

def noneEnv : Ix.Kernel.Key .source → Option (Ix.Kernel.ConstantInfo .source) := fun _ => none

def shapeUnits : TestSeq :=
  test "a block naming only its formers passes"
    (Ix.Kernel.indShapeOk noneEnv [sind "T" sty, sctor "T.a" (sconst "T"), sctor "T.b" (.app (sconst "T") (sconst "T"))]) $
  test "a mutual block's constructor may name another former"
    (Ix.Kernel.indShapeOk noneEnv [sind "A" sty, sind "B" sty, sctor "A.a" (.app (sconst "A") (sconst "B"))]) $
  test "a constructor naming an earlier constructor is refused"
    (!Ix.Kernel.indShapeOk noneEnv [sind "T" sty, sctor "T.a" (sconst "T"), sctor "T.b" (.app (sconst "T") (sconst "T.a"))]) $
  test "a constructor naming a later constructor is refused"
    (!Ix.Kernel.indShapeOk noneEnv [sind "T" sty, sctor "T.a" (.app (sconst "T") (sconst "T.b")), sctor "T.b" (sconst "T")]) $
  test "a former naming an unknown constant is refused, and passes once it is declared"
    (!Ix.Kernel.indShapeOk noneEnv [sind "T" (sconst "U")] && Ix.Kernel.indShapeOk withU [sind "T" (sconst "U")]) $
  test "a constructor name already declared is refused"
    (!Ix.Kernel.indShapeOk withU [sind "T" sty, sctor "U" (sconst "T")]) $
  test "a constructor named as a former is refused"
    (!Ix.Kernel.indShapeOk noneEnv [sind "T" sty, sctor "T" (sconst "T")]) $
  test "a constructor name declared twice is refused"
    (!Ix.Kernel.indShapeOk noneEnv [sind "T" sty, sctor "T.a" (sconst "T"), sctor "T.a" (sconst "T")]) $
  test "a literal needs its support"
    (!Ix.Kernel.indShapeOk noneEnv [sind "T" sty, sctor "T.a" (.app (sconst "T") (.lit (.natVal 0)))])

/-- The lowered declarations with `Args.cons`'s declared type naming `Tm.var`. -/
def withCtorNamingCtor (ds : Array (Ix.Kernel.Declaration .source)) :
    Array (Ix.Kernel.Declaration .source) :=
  ds.map fun d => match d with
    | .indDecl block nP => .indDecl (block.map fun ci => match ci with
        | .ctorInfo cv nP' nF =>
          if cv.name == kkey (defs "Args.cons") then
            .ctorInfo { cv with type := .app (.const (kkey (defs "Tm.var")) []) cv.type } nP' nF
          else ci
        | ci => ci) nP
    | d => d

def evaluateShape : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[defsModule]
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let env ← envOf leanEnv #[defs "Tm"]
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  match prepareSource pre env (condense env) with
  | .error e => errors := errors.push s!"shape: ingress: {e}"
  | .ok ds =>
    match Ix.Kernel.Cached.checkDecls .verified (sourceEvidence ds) ds with
    | .ok _ => lines := lines.push "shape: Tm/Args as lowered: accepted"
    | .error (e, _) => errors := errors.push s!"shape: Tm/Args as lowered: {e}"
    let ds' := withCtorNamingCtor ds
    if ds' == ds then errors := errors.push "shape: Args.cons not found"
    match Ix.Kernel.Cached.checkDecls .verified (sourceEvidence ds') ds' with
    | .ok _ => errors := errors.push "shape: a constructor naming an earlier constructor was accepted"
    | .error (e, _) =>
      let msg := toString e
      lines := lines.push s!"shape: Args.cons naming Tm.var: {msg}"
      unless (msg.splitOn "unknown constant in type of").length > 1 do
        errors := errors.push s!"shape: refused, but not by the shape guard: {msg}"
  return (errors, lines)

def shapeGuard : TestSeq :=
  .individualIO "the shape guard refuses a modeled block's constructor naming an earlier one" none (do
    let (errors, lines) ← evaluateShape
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, 2, 0, msg)) .done

def suite : List TestSeq := [refusals, erasure, contractFrames, numbering, canonical, sharing, fixtures,
  quotient, shapeUnits, shapeGuard]

end Tests.Ix.Kernel.SourceIngress
