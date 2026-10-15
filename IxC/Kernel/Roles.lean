module

public import IxC.Kernel.TrustAxioms
public import Std.Data.HashSet

@[expose] public section

/-!
# The role specifications

The checker's fixed, versioned specification set (IXC-PLAN §8.1,
PRIMITIVES-DESIGN §6.2): for every `Role`, what a constant bound to it must
be. A specification is a closed term over role keys (`roleKey r`), positional
levels and bound or free variables; it mentions no address and no input key,
so the same terms serve every mode and every toolchain. A toolchain bump
regenerates the role table and its evidence (`RoleTable`,
`IxC/Kernel/Ixon/RoleTable.lean`) and leaves this file, `specVersion` and the
specification digest (`Ix.SpecDigest.specDigest`, `Ix/SpecDigest.lean`, root library) unchanged; a
change here is a change to the specification set and bumps both.

**These are today's specifications, respelled**, not new ones. Each role's
specification is the data the checker already validates its constant against,
taken from where it lives (`Role.spec_*` below are `rfl`):

| Kind | Roles | The checker's comparison |
| --- | --- | --- |
| `block` | the basis blocks `Eq`, `Nat`, `PUnit`, `Empty`, `False`, `Quot` (every member) | `basisPinHit`/`quotPinHit`: the stream's declarations equal these up to `ConstantInfo.canon`; the block installed is their annotation (`BasisKind.declsA`) |
| `anchor` | the literal support (`String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`), the standard axioms' families (`Iff`, `Nonempty` and their constructors and recursors), `True`, `True.intro`, `Bool`, `Bool.false`, `Bool.true` | the constant's type, up to binder data and level-parameter names (`listTyOk` …, `ConstantVal.matchesPin`) |
| `ops` | the certified `Nat` operations | the type (`natOpTyPinned`) and the characterizing equations (`natOpEquations`, `divModCertStmts`), each certified by its evidence in the pre-insertion environment with the operation's self-references replaced by its value |
| `axiom` | `propext`, `Classical.choice`, `Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`; `sorryAx` (inert) | the axiom's exact type (`ConstantVal.matchesPin`); an inert axiom installs nothing and has no type constraint |
| `identity` | `Lean.reduceBool`, `Lean.reduceNat` | the stored type, and the value certified to be the identity, `value x ≡ x` |

Four anchors are recorded but not validated by today's checker: `Bool.rec`,
`And`, `And.intro` and `And.rec` (the `And` rescue relies on `And`'s
projection table and proof irrelevance at use, `andRescueSlots`). They are
listed so that the set is complete; validating them would add a decline
condition and is an owner's decision (`roles.md`).

**Evidence.** An operation's equations are certified by evidence the role
table supplies, one entry per equation (`Evidence`): an unconditional
equation by `.defeq` (definitional equality after opening, `certifyNatEqs`),
a conditional one (with hypotheses) by `.proof thm` (a theorem whose proof is
checked against the equation, `checkDivModCerts`). The kinds are fixed by the
specification (`Spec.evidenceKinds`): the model consumes the definitional runs
of the structural operations and the certificate runs of the well-founded
ones, and nothing else (`Model/NatEqs.lean`, `Model/DivModCert.lean`).

**Dependencies.** `Role.deps r` are the roles `r`'s specification mentions and
its validation needs (today's implicit edges: `natOpDeps`, `Eq` for the
quotient and the axioms, the literal support); `Role.block r` are the roles
bound together with `r` (a block's members). A role table must be closed
under both (`RoleTable.wf`).
-/

namespace Ix.Kernel

open BasisDSL

/-! ## Specifications -/

/-- One role's specification (IXC-PLAN §8.1). -/
inductive Spec where
  /-- The exact declarations, up to `ConstantInfo.canon` (a basis block; every
  member of the block has the same specification). -/
  | block (decls : List ConstantInfo)
  /-- An exact type, up to binder data and level-parameter names. -/
  | anchor (levels : Nat) (type : Expr)
  /-- The type and the characterizing equations: per equation its hypotheses,
  left and right sides, over `fvar 0`, `fvar 1` (the hypotheses are `fvar 2`,
  `fvar 3` in the certificate's telescope); the operation's self-reference is
  `.const (roleKey r) []`. -/
  | ops (type : Expr) (eqs : List (List Expr × Expr × Expr))
  /-- An axiom of the given type; `none` is an inert axiom (`sorryAx`): it is
  tolerated as a declaration, installs nothing, and any use declines. -/
  | axiom (levels : Nat) (type : Option Expr)
  /-- An opaque whose value is the identity, `value x ≡ x`, at this type. -/
  | identity (type : Expr)
  deriving Repr, Inhabited

/-- The specification kinds, for summaries and the table's checks. -/
inductive SpecKind where
  | block | anchor | ops | axiom | identity
  deriving DecidableEq, Repr, Inhabited

def Spec.kind : Spec → SpecKind
  | .block _ => .block
  | .anchor .. => .anchor
  | .ops .. => .ops
  | .axiom .. => .axiom
  | .identity _ => .identity

/-- The evidence an operation's equations take, in order: `true` for an
unconditional equation (definitional equality), `false` for a conditional one
(a proof). Every other kind takes none. -/
def Spec.evidenceKinds : Spec → List Bool
  | .ops _ eqs => eqs.map (·.1.isEmpty)
  | _ => []

/-! ## Evidence -/

/-- One equation's evidence: `defeq`, checked by `isDefEq` after opening (the
structural operations), or `proof thm`, a theorem whose proof is checked
against the equation (the well-founded operations). The role table carries it
at addresses (`Evidence Address`); the fold receives it at keys with the proof
term the front end resolved for it (`Evidence (Key × Expr)`). -/
inductive Evidence (K : Type) where
  | defeq
  | proof (thm : K)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Does this entry have the kind `defeq?` (`true` for definitional
equality)? -/
def Evidence.isDefeqKind {K : Type} : Evidence K → Bool → Bool
  | .defeq, b => b
  | .proof _, b => !b

/-- **What the fold is given of a role table**: per role, its evidence, a
proof entry carrying the theorem's key and its proof term (a theorem's value,
resolved by the front end). Soundness holds for every value
(`Ix.Kernel.model_exists`): the evidence decides which operations' fast
paths are enabled, nothing else. -/
abbrev Evidences := List (Role × List (Evidence (Key × Expr)))

/-- The evidence of role `r` (none when the role has no entry). -/
def Evidences.of (ev : Evidences) (r : Role) : List (Evidence (Key × Expr)) :=
  match ev.find? (·.1 == r) with
  | some (_, es) => es
  | none => []

/-! ## The certificate statements of the well-founded operations -/

/-- The certificate statements of a proof-certified well-founded `Nat`
operation, in *open* form over `x := fvar 0`, `y := fvar 1` (the
hypotheses become `fvar 2, fvar 3`): per certificate, the list of
hypothesis types and the characteristic equation `Eq Nat lhs rhs`.
The guards are spelled with the already-certified `Nat.ble` (never the
`Nat.le`/`Nat.lt` `Prop` inductives) and the numeral `1` as
`Nat.succ Nat.zero`, so the model side consumes them through the
existing `NatOpsOk` literal semantics for `ble`/`sub`.  The op's
self-reference is `.const c []`, substituted with the stored annotated
value before checking (all statement components are application
spines, so `Expr.substConst0` applies). These are the equations of the
operations' `ops` specifications (`Role.spec`). -/
def divModCertStmts (c : Key) : List (List Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar 0 natTy
  let y : Expr := .fvar 1 natTy
  let one : Expr := .app (.const natSuccName []) (.const natZeroName [])
  let ble2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natBleName []) a) b
  let eqB : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) (.const boolName [])) a) b
  let eqN : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) natTy) a) b
  let op2 : Expr → Expr → Expr := fun a b => .app (.app (.const c []) a) b
  let sub2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natSubName []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  let z : Expr := .const natZeroName []
  let two : Expr := .app (.const natSuccName []) one
  let mod2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natModName []) a) b
  let div2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natDivName []) a) b
  let add2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natAddName []) a) b
  let mul2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natMulName []) a) b
  if c = natGcdName then
    -- `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`
    [([eqB (ble2 one x) bT], eqN (op2 x y) (op2 (mod2 y x) x)),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natShiftLeftName then
    -- `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (op2 (mul2 two x) (sub2 y one))),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natShiftRightName then
    -- `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (div2 (op2 x (sub2 y one)) two)),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natLandName then
    -- `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`,
    -- `x = 0 → x &&& y = 0`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two)))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) z)]
  else if c = natLorName then
    -- `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
    -- `x = 0 → x ||| y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two))))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natXorName then
    -- `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
    -- `x = 0 → x ^^^ y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else
  let recRhs : Expr :=
    if c = natDivName then .app (.const natSuccName []) (op2 (sub2 x y) y)
    else op2 (sub2 x y) y
  let baseRhs : Expr := if c = natDivName then .const natZeroName [] else x
  [([eqB (ble2 y x) bT, eqB (ble2 one y) bT], eqN (op2 x y) recRhs),
   ([eqB (ble2 y x) bF], eqN (op2 x y) baseRhs),
   ([eqB (ble2 one y) bF], eqN (op2 x y) baseRhs)]

/-- The sides of a certificate statement `Eq Nat lhs rhs`. -/
def eqSides : Expr → Expr × Expr
  | .app (.app (.app (.const _ _) _) a) b => (a, b)
  | e => (e, e)

/-- A certificate statement `Eq Nat lhs rhs` from its sides. -/
def eqNatOf (a b : Expr) : Expr :=
  .app (.app (.app (.const eqName [.succ .zero]) (.const natName [])) a) b

/-! ## The specification terms that have no other home

The literal-support anchors (`CoreDefs.lean`'s `stringTyOk` … `charOfNatTyOk`
check exactly these shapes), the operations' types (`natOpTyPinned`), and the
anchors of the four roles today's checker does not validate. -/

/-- `List.{u} : Type u → Type u`. -/
def listSpecTy : Expr := piA (srt (.succ u)) (srt (.succ u))

/-- `List.nil.{u} : (α : Type u) → List.{u} α`. -/
def listNilSpecTy : Expr := pi "α" (srt (.succ u)) (.app (cnst listName [u]) (bv 0))

/-- `List.cons.{u} : (α : Type u) → α → List.{u} α → List.{u} α`. -/
def listConsSpecTy : Expr :=
  pi "α" (srt (.succ u)) <|
  pi "head" (bv 0) <|
  pi "tail" (.app (cnst listName [u]) (bv 1)) <|
  .app (cnst listName [u]) (bv 2)

/-- `Char.ofNat : Nat → Char`. -/
def charOfNatSpecTy : Expr := pi "n" (cnst natName) (cnst charName)

/-- `String.ofList : List.{0} Char → String`. -/
def stringOfListSpecTy : Expr :=
  pi "data" (.app (cnst listName [.zero]) (cnst charName)) (cnst stringName)

/-- `Bool.rec.{u} {motive : Bool → Sort u} (false : motive false)
(true : motive true) (t : Bool) : motive t`. -/
def boolRecSpecTy : Expr :=
  piI "motive" (pi "t" (cnst boolName) (srt u)) <|
  pi "false" (.app (bv 0) (cnst boolFalseName)) <|
  pi "true" (.app (bv 1) (cnst boolTrueName)) <|
  pi "t" (cnst boolName) (.app (bv 3) (bv 0))

/-- `And (a b : Prop) : Prop`. -/
def andSpecTy : Expr := pi "a" prop <| pi "b" prop prop

/-- `And.intro {a b : Prop} (left : a) (right : b) : And a b`. -/
def andIntroSpecTy : Expr :=
  piI "a" prop <| piI "b" prop <| pi "left" (bv 1) <| pi "right" (bv 1) <|
  ap2 (cnst andName) (bv 3) (bv 2)

/-- `And.rec.{u} {a b : Prop} {motive : And a b → Sort u}
(intro : (left : a) → (right : b) → motive (And.intro left right))
(t : And a b) : motive t`. -/
def andRecSpecTy : Expr :=
  piI "a" prop <|
  piI "b" prop <|
  piI "motive" (pi "t" (ap2 (cnst andName) (bv 1) (bv 0)) (srt u)) <|
  pi "intro"
    (pi "left" (bv 2) <| pi "right" (bv 2) <|
      .app (bv 2) (ap4 (cnst andIntroName) (bv 4) (bv 3) (bv 1) (bv 0))) <|
  pi "t" (ap2 (cnst andName) (bv 3) (bv 2)) (.app (bv 2) (bv 0))

/-- `Nat → Nat`. -/
def natUnSpecTy : Expr := pi "n" (cnst natName) (cnst natName)

/-- `Nat → Nat → Nat`. -/
def natBinSpecTy : Expr := pi "n" (cnst natName) <| pi "m" (cnst natName) (cnst natName)

/-- `Nat → Nat → Bool`. -/
def natCmpSpecTy : Expr := pi "n" (cnst natName) <| pi "m" (cnst natName) (cnst boolName)

/-- An `ops` specification from the structural recurrences (`natOpEquations`,
unconditional) at the variables `fvar 0`, `fvar 1`. -/
def natOpsSpec (ty : Expr) (c : Key) : Spec :=
  .ops ty ((natOpEquations 0 c).map fun (l, r) => ([], l, r))

/-- An `ops` specification from the certificate statements
(`divModCertStmts`, conditional). -/
def divModSpec (c : Key) : Spec :=
  .ops natBinSpecTy ((divModCertStmts c).map fun (hs, e) => (hs, (eqSides e).1, (eqSides e).2))

/-! ## The specification of every role -/

/-- **The specification set.** -/
def Role.spec : Role → Spec
  | .nat | .natZero | .natSucc | .natRec => .block natBasis
  | .eq | .eqRefl | .eqRec => .block eqBasis
  | .punit | .punitUnit | .punitRec => .block punitBasis
  | .empty | .emptyRec => .block emptyBasis
  | .false | .falseRec => .block falseBasis
  | .quot | .quotMk | .quotLift | .quotInd | .quotSound => .block quotBasis
  | .bool => .anchor 0 boolCvA.type
  | .boolFalse => .anchor 0 (cnst boolName)
  | .boolTrue => .anchor 0 (cnst boolName)
  | .boolRec => .anchor 1 boolRecSpecTy
  | .true => .anchor 0 trueCvA.type
  | .trueIntro => .anchor 0 trueIntroCvA.type
  | .and => .anchor 0 andSpecTy
  | .andIntro => .anchor 0 andIntroSpecTy
  | .andRec => .anchor 1 andRecSpecTy
  | .iff => .anchor 0 iffRaw.toConstantVal.type
  | .iffIntro => .anchor 0 iffIntroRaw.toConstantVal.type
  | .iffRec => .anchor 1 iffRecRaw.toConstantVal.type
  | .nonempty => .anchor 1 nonemptyRaw.toConstantVal.type
  | .nonemptyIntro => .anchor 1 nonemptyIntroRaw.toConstantVal.type
  | .nonemptyRec => .anchor 1 nonemptyRecRaw.toConstantVal.type
  | .list => .anchor 1 listSpecTy
  | .listNil => .anchor 1 listNilSpecTy
  | .listCons => .anchor 1 listConsSpecTy
  | .string => .anchor 0 type1
  | .stringOfList => .anchor 0 stringOfListSpecTy
  | .char => .anchor 0 type1
  | .charOfNat => .anchor 0 charOfNatSpecTy
  | .natPred => natOpsSpec natUnSpecTy natPredName
  | .natAdd => natOpsSpec natBinSpecTy natAddName
  | .natSub => natOpsSpec natBinSpecTy natSubName
  | .natMul => natOpsSpec natBinSpecTy natMulName
  | .natPow => natOpsSpec natBinSpecTy natPowName
  | .natBeq => natOpsSpec natCmpSpecTy natBeqName
  | .natBle => natOpsSpec natCmpSpecTy natBleName
  | .natDiv => divModSpec natDivName
  | .natMod => divModSpec natModName
  | .natGcd => divModSpec natGcdName
  | .natLand => divModSpec natLandName
  | .natLor => divModSpec natLorName
  | .natXor => divModSpec natXorName
  | .natShiftLeft => divModSpec natShiftLeftName
  | .natShiftRight => divModSpec natShiftRightName
  | .propext => .axiom 0 (some propextRaw.type)
  | .choice => .axiom 1 (some choiceRaw.type)
  | .sorryAx => .axiom 1 none
  | .trustCompiler => .axiom 0 (some trustCompilerA.type)
  | .ofReduceBoolAx => .axiom 0 (some (ofReduceRaw ofReduceBoolName).type)
  | .ofReduceNatAx => .axiom 0 (some (ofReduceRaw ofReduceNatName).type)
  | .reduceBool => .identity (reduceOpRaw reduceBoolName).type
  | .reduceNat => .identity (reduceOpRaw reduceNatName).type

/-- **The roles bound together with `r`**: the members of its block (itself
included), in the block's order. A role table binds all of them or none. -/
def Role.block : Role → List Role
  | .nat | .natZero | .natSucc | .natRec => [.nat, .natZero, .natSucc, .natRec]
  | .bool | .boolFalse | .boolTrue | .boolRec => [.bool, .boolFalse, .boolTrue, .boolRec]
  | .eq | .eqRefl | .eqRec => [.eq, .eqRefl, .eqRec]
  | .punit | .punitUnit | .punitRec => [.punit, .punitUnit, .punitRec]
  | .empty | .emptyRec => [.empty, .emptyRec]
  | .false | .falseRec => [.false, .falseRec]
  | .true | .trueIntro => [.true, .trueIntro]
  | .and | .andIntro | .andRec => [.and, .andIntro, .andRec]
  | .iff | .iffIntro | .iffRec => [.iff, .iffIntro, .iffRec]
  | .nonempty | .nonemptyIntro | .nonemptyRec => [.nonempty, .nonemptyIntro, .nonemptyRec]
  | .list | .listNil | .listCons => [.list, .listNil, .listCons]
  | .quot | .quotMk | .quotLift | .quotInd | .quotSound =>
    [.quot, .quotMk, .quotLift, .quotInd, .quotSound]
  | r => [r]

/-- **The roles `r`'s specification mentions and its validation needs**,
outside its own block. A role table that binds `r` binds these (and their
blocks). -/
def Role.deps : Role → List Role
  | .quot | .quotMk | .quotLift | .quotInd | .quotSound => [.eq]
  | .stringOfList => [.list, .char, .string]
  | .charOfNat => [.nat, .char]
  | .natPred => [.nat]
  | .natAdd => [.nat]
  | .natSub => [.nat, .natPred]
  | .natMul => [.nat, .natAdd]
  | .natPow => [.nat, .natAdd, .natMul]
  | .natBeq => [.nat, .bool]
  | .natBle => [.nat, .bool]
  | .natDiv => [.nat, .natPred, .natSub, .natBle, .bool, .eq]
  | .natMod => [.nat, .natPred, .natSub, .natBle, .bool, .eq]
  | .natGcd => [.nat, .natBle, .natMod, .bool, .eq]
  | .natLand => [.nat, .natAdd, .natMul, .natBle, .natDiv, .natMod, .bool, .eq]
  | .natLor => [.nat, .natAdd, .natSub, .natMul, .natBle, .natDiv, .natMod, .bool, .eq]
  | .natXor => [.nat, .natAdd, .natMul, .natBle, .natDiv, .natMod, .bool, .eq]
  | .natShiftLeft => [.nat, .natSub, .natMul, .natBle, .bool, .eq]
  | .natShiftRight => [.nat, .natSub, .natBle, .natDiv, .bool, .eq]
  | .propext => [.iff, .eq]
  | .choice => [.nonempty]
  | .trustCompiler => [.true]
  | .reduceBool => [.bool]
  | .reduceNat => [.nat]
  | .ofReduceBoolAx => [.reduceBool, .bool, .eq]
  | .ofReduceNatAx => [.reduceNat, .nat, .eq]
  | _ => []

/-- **The version of the specification set.** It changes exactly when
`Role`, `Role.spec`, `Role.block` or `Role.deps` change, together with the
specification digest (`Ix.SpecDigest.specDigest`), which the root library
freezes (`Ix/SpecDigest.lean`). -/
def specVersion : Nat := 1

/-! ## The evidence of an operation, as the fold reads it -/

/-- The operation role at a key (the certified `Nat` operations). -/
def opRole? (c : Key) : Option Role :=
  if c = natPredName then some .natPred
  else if c = natAddName then some .natAdd
  else if c = natSubName then some .natSub
  else if c = natMulName then some .natMul
  else if c = natPowName then some .natPow
  else if c = natBeqName then some .natBeq
  else if c = natBleName then some .natBle
  else if c = natDivName then some .natDiv
  else if c = natModName then some .natMod
  else if c = natGcdName then some .natGcd
  else if c = natLandName then some .natLand
  else if c = natLorName then some .natLor
  else if c = natXorName then some .natXor
  else if c = natShiftLeftName then some .natShiftLeft
  else if c = natShiftRightName then some .natShiftRight
  else none

/-- **A structural operation's evidence is in order**: one `.defeq` entry per
recurrence equation (`natOpEquations`), and nothing else. -/
def evidenceDefeqOk (ev : Evidences) (c : Key) : Bool :=
  match opRole? c with
  | some r =>
    let es := ev.of r
    es.length == (natOpEquations 0 c).length && es.all (·.isDefeqKind true)
  | none => false

/-- **A well-founded operation's proof terms**: one `.proof` entry per
certificate statement (`divModCertStmts`), their proof terms in order; `none`
when the evidence has another shape. -/
def evidenceProofs (ev : Evidences) (c : Key) : Option (List Expr) :=
  match opRole? c with
  | some r =>
    let es := ev.of r
    if es.length == (divModCertStmts c).length then
      es.mapM fun
        | .proof (_, v) => some v
        | .defeq => none
    else none
  | none => none

/-! ## The evidence closure condition

The certificate check's guard used to read the stream's order: a proof's
constants had to be installed before the operation (`constsResolve` in the
pre-insertion environment), so what a certificate could use depended on what
the stream happened to declare earlier. The condition is now restated as a
closure condition (IXC-PLAN §8.4, PRIMITIVES-DESIGN §6.5): every constant of a
proof, after the operation's self-references are replaced by its value, lies
in the dependency closure of that value and of the operation's dependencies'
roles (`Role.deps`, with their blocks). The validation then reads only the
operation's own dependency closure (LOCALITY), and the fast path the evidence
justifies stays out of the evidence's own check.

The closure follows a stored constant's type, its value (a definition's, a
theorem's stored one), its recursor rules (their constructors and right-hand
sides) and its projection table (`ConstantInfo.refExprs`, `refKeys`); a
literal references the constants its unfolding names, as `Expr.constsResolve`
reads it. The condition only ever refuses: nothing in the model reads it. -/

/-- A bound on the walks below (they visit each key and subterm once; the
bound only makes them total). -/
def walkFuel : Nat := 1 <<< 40

/-- The keys a `Nat` literal references implicitly. -/
def litNatKeys : List Key := [natName, natZeroName, natSuccName]

/-- The keys a `String` literal references implicitly. -/
def litStrKeys : List Key :=
  litNatKeys ++ [stringName, stringOfListName, listName, listNilName, listConsName, charName,
    charOfNatName]

/-- The keys the expressions of `todo` reference, added to `acc`: a walk over
their distinct subterms (`seen`), each visited once. -/
def constKeysGo : Nat → List Expr → Std.HashSet Expr → Std.HashSet Key → Std.HashSet Key
  | 0, _, _, acc => acc
  | _, [], _, acc => acc
  | n + 1, e :: todo, seen, acc =>
    if seen.contains e then constKeysGo n todo seen acc
    else
      let seen := seen.insert e
      match e with
      | .const k _ => constKeysGo n todo seen (acc.insert k)
      | .proj s _ x => constKeysGo n (x :: todo) seen (acc.insert s)
      | .fvar _ t => constKeysGo n (t :: todo) seen acc
      | .app f a => constKeysGo n (f :: a :: todo) seen acc
      | .lam t b _ => constKeysGo n (t :: b :: todo) seen acc
      | .forallE t b _ => constKeysGo n (t :: b :: todo) seen acc
      | .letE t v b _ => constKeysGo n (t :: v :: b :: todo) seen acc
      | .lit (.natVal _) => constKeysGo n todo seen (litNatKeys.foldl (·.insert ·) acc)
      | .lit (.strVal _) => constKeysGo n todo seen (litStrKeys.foldl (·.insert ·) acc)
      | _ => constKeysGo n todo seen acc

/-- The keys an expression references. -/
def Expr.constKeys (e : Expr) : Std.HashSet Key := constKeysGo walkFuel [e] {} {}

/-- The expressions of a stored constant the closure follows. -/
def ConstantInfo.refExprs : ConstantInfo → List Expr
  | .axiomInfo cv => [cv.type]
  | .defnInfo cv v _ => [cv.type, v]
  | .thmInfo cv v => [cv.type, v]
  | .indInfo cv _ => [cv.type]
  | .ctorInfo cv _ _ => [cv.type]
  | .recInfo cv _ _ rules => cv.type :: rules.flatMap fun rl =>
      rl.rhs :: match rl.fire with
        | .nested _ ps => ps
        | _ => []
  | .projInfo tbl => tbl.bodies.toList

/-- The keys of a stored constant the closure follows besides its
expressions': a structure's η constructor, a recursor's rule constructors, a
projection table's structure and constructor. -/
def ConstantInfo.refKeys : ConstantInfo → List Key
  | .indInfo _ caps => caps.etaCtor.toList
  | .recInfo _ _ _ rules => rules.map (·.ctor)
  | .projInfo tbl => [tbl.structName, tbl.ctor]
  | _ => []

/-- The keys reachable from `todo` through the constants `look` finds. -/
def refClosureGo (look : Key → Option ConstantInfo) :
    Nat → List Key → Std.HashSet Key → Std.HashSet Key
  | 0, _, seen => seen
  | _, [], seen => seen
  | n + 1, k :: todo, seen =>
    if seen.contains k then refClosureGo look n todo seen
    else
      let seen := seen.insert k
      match look k with
      | none => refClosureGo look n todo seen
      | some ci =>
        let ks := constKeysGo walkFuel ci.refExprs {} {}
        refClosureGo look n (ci.refKeys ++ ks.toList ++ todo) seen

/-- The roots of an operation's evidence closure besides its value: its
dependencies' roles, with their blocks. -/
def evidenceDepKeys (c : Key) : List Key :=
  match opRole? c with
  | some r => (r.deps.flatMap Role.block).map roleKey
  | none => []

/-- **The evidence closure condition** for operation `c` with annotated value
`annVal`: every constant of every proof, with `c`'s self-references replaced
by `annVal`, is in the dependency closure of `annVal` and of `c`'s
dependencies (`evidenceDepKeys`), through `look`. -/
def evidenceLocal (look : Key → Option ConstantInfo) (c : Key) (annVal : Expr)
    (proofs : List Expr) : Bool :=
  let cl := refClosureGo look walkFuel (annVal.constKeys.toList ++ evidenceDepKeys c) {}
  proofs.all fun p => (Expr.substConstAll c annVal p).constKeys.toList.all cl.contains

/-! ## Facts -/

theorem Role.spec_nat : Role.spec .nat = .block (BasisKind.decls .natK) := rfl
theorem Role.spec_eq : Role.spec .eq = .block (BasisKind.decls .eqK) := rfl
theorem Role.spec_punit : Role.spec .punit = .block (BasisKind.decls .punitK) := rfl
theorem Role.spec_empty : Role.spec .empty = .block (BasisKind.decls .emptyK) := rfl
theorem Role.spec_false : Role.spec .false = .block (BasisKind.decls .falseK) := rfl
theorem Role.spec_quot : Role.spec .quot = .block (BasisKind.decls .quotK) := rfl
theorem Role.spec_propext : Role.spec .propext = .axiom 0 (some propextRaw.type) := rfl
theorem Role.spec_choice : Role.spec .choice = .axiom 1 (some choiceRaw.type) := rfl

/-- Every role's block contains it. -/
theorem Role.mem_block (r : Role) : r ∈ r.block := by cases r <;> decide

/-- A block's members have the block's members as their block. -/
theorem Role.block_block (r : Role) : ∀ s ∈ r.block, s.block = r.block := by
  cases r <;> decide

/-- The operations, and only they, take evidence: one entry per equation, a
definitional one exactly for an unconditional equation. -/
theorem Role.evidenceKinds_natAdd :
    (Role.spec .natAdd).evidenceKinds = [Bool.true, Bool.true] := by decide

theorem Role.evidenceKinds_natDiv :
    (Role.spec .natDiv).evidenceKinds = [Bool.false, Bool.false, Bool.false] := by decide

/-- Every operation role is found at its key. -/
theorem opRole?_roleKey (r : Role)
    (h : (Role.spec r).kind = .ops) : opRole? (roleKey r) = some r := by
  cases r <;> first | rfl | (exact absurd h (by decide))

/-- The certificate statements are the `ops` specifications' equations: the
spec's sides rebuild each statement. -/
theorem divModSpec_stmts (c : Key)
    (hc : c ∈ [natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
      natShiftLeftName, natShiftRightName]) :
    (match divModSpec c with
     | .ops _ eqs => eqs.map fun (hs, l, r) => (hs, eqNatOf l r)
     | _ => []) = divModCertStmts c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Ix.Kernel
