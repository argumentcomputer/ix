import LSpec
import Ix.Meta
import Ix.LeanIngress.Theorems
import Tests.Ix.Kernel.SourceIngressStep
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.ReaderFidelityDefs
import Tests.Ix.Kernel.SourceIngressDefs

/-! # The Source-mode check on compiled Lean declarations (`lake test -- kernel-source-ingress`)

The declarations of `Tests.Ix.Kernel.ReaderFidelityDefs` (the Ixon reader's
fidelity fixtures: structures, nested, mutual, indexed and reflexive
inductives, projections, quotients, literals, theorems, opaques, axioms, and
the `partial`/`unsafe` definitions the reader declines) and everything in
`Init` they reach are canonicalized (`Ix.CanonM`), condensed (`Ix.GraphM`,
`Ix.CondenseM`) and checked in Source mode (`Ix.LeanIngress`) at the empty
`Nat`-operation pin list:

* group by group (`Tests.Ix.Kernel.SourceIngressStep`), where every fixture
  declaration must get its expected verdict;
* all at once (`checkSource`), on the closure of the fixtures that are
  expected to be accepted, which must be accepted;
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
  -- the reader's fixture quotient divides (`parity`), and `Nat.mod` declines
  -- at the empty pin list
  (defs "ParityQ", "blocked"), (defs "ParityQ.toBool", "blocked"),
  (defs "ParityQ.toBool_mk", "blocked"),
  -- literals
  (defs "smallNat", "accept"), (defs "bigNat", "accept"),
  -- theorems, opaques, axioms
  (own "BoolQ.mk_eq", "accept"), (own "BoolQ.const_eq", "accept"), (defs "bigNat_pos", "accept"),
  (defs "twice_id", "accept"), (defs "isEven_two", "accept"), (defs "even_two", "accept"),
  (defs "secret", "accept"),
  -- the checker admits the standard axioms only
  (defs "fidelityAxiom", "decline"),
  (defs "levelMax", "accept"), (defs "levelImax", "accept"),
  -- declined: a `partial` definition's compiled companion and an `unsafe` one
  (defs "spin._unsafe_rec", "decline"), (defs "unsafeId", "decline"),
  -- `Nat.div` is a pinned operation and declines at the empty pin list;
  -- the well-founded `log2` divides
  (`Nat.div, "decline"), (defs "log2", "blocked"),
  -- the prelude, checked on the environment's own copies
  (`Eq, "accept"), (`Eq.rec, "accept"), (`Nat, "accept"), (`Quot, "accept"),
  (`Quot.lift, "accept"), (`Quot.sound, "accept"), (`Bool, "accept"), (`And, "accept")]

/-- Seeds whose closure is accepted as a whole by `checkSource`. -/
def acceptedSeeds : Array Lean.Name := #[defs "Color", defs "Point3", defs "Vec.length",
  defs "WTree.depthAt", defs "Rose.size", defs "ATree", defs "Node", defs "Even", defs "Tm.size",
  defs "Trivial", defs "Both", defs "NatPair", defs "sumPoint", defs "isEven_two", defs "even_two",
  own "BoolQ.mk_eq", own "BoolQ.const_eq", defs "smallNat", defs "bigNat", defs "twice_id",
  defs "secret", defs "levelMax", defs "levelImax"]

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
  | .ok [.lam (.const n []) (.bvar 0) m] => n == .str .anonymous "Nat" && m == { pw := .never }
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

def sameTree : Except ExprError (List KExpr) → Except ExprError KExpr → Bool
  | .ok [a], .ok b => decide (a = b)
  | _, _ => false

/-- Binder contracts: a plain binder carries the Lean fragment's, and a
contract frame puts its contract on the binder it wraps, as the compiler
lowers it; a `let` frame's contract is erased; a frame the compiler refuses
is refused. -/
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
  test "a let frame's contract is erased" (sameResult (conv (framed letC letE)) (conv letE)) ++
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

/-- A DAG of depth `n` whose tree has `2^n` leaves: the shared conversion
finishes, and agrees with the tree conversion at a depth the tree walk still
manages. -/
def sharedDag (n : Nat) : Ix.Expr := Id.run do
  let mut e := Ix.Expr.mkConst (nm "Nat") #[]
  for _ in [0:n] do e := Ix.Expr.mkApp e e
  return e

def treeSize : Ix.Kernel.Expr → Nat
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
  let leanEnv ← getCompileEnv #[defsModule, ownModule]
  let some idx := leanEnv.getModuleIdx? defsModule | throw (IO.userError "fixture module not loaded")
  let some idx' := leanEnv.getModuleIdx? ownModule | throw (IO.userError "fixture module not loaded")
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    let m := leanEnv.getModuleIdxFor? n
    if m == some idx || m == some idx' then some n else none
  let env ← envOf leanEnv (seeds ++ #[`Nat.div])
  let blocks := condense env
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let r ← run pre [] env blocks
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  for (n, want) in expected do
    match r.rowOf (Ix.Kernel.Name.ofLeanName n) with
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
  return (errors, lines)

def fixtures : TestSeq :=
  .individualIO "source mode: fixture closure, group by group and all at once" none (do
    let (errors, lines) ← evaluate
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, expected.length, 0, msg)) .done

def suite : List TestSeq := [refusals, erasure, contractFrames, numbering, sharing, fixtures]

end Tests.Ix.Kernel.SourceIngress
