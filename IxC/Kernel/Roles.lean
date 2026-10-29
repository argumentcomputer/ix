module

public import IxC.Kernel.StdAxioms
public import IxC.Kernel.Core
public import Std.Data.HashSet

@[expose] public section

/-!
# The role specifications

The checker's fixed, versioned specification set: for every `Role`, what a constant bound to it must
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
| `block` | the standard axioms' families `Iff` and `Nonempty` (every member: the inductive, its constructor and its recursor) | `stdAxiomOk` (`stdAxiomOkF`), before `propext` or `Classical.choice` is installed: each member is stored as a kernel-checked inductive, constructor or recursor with these parameter, field and binder counts and this type, up to binder data and level-parameter names (`ConstantVal.matchesPin`); the constructors and the recursor's rules are then the kernel's own for that inductive |
| `anchor` | the literal support (`String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`), `True`, `True.intro`, `Bool`, `Bool.false`, `Bool.true`, `Bool.rec`, `And`, `And.intro`, `And.rec` | the constant's type, up to binder data and level-parameter names (`listTyOk` …, `ConstantVal.matchesPin`) |
| `ops` | the certified `Nat` operations | the type (`natOpTyPinned`) and the characterizing equations (`natOpEquations`, `divModCertStmts`), each certified by its evidence in the pre-insertion environment with the operation's self-references replaced by its value |
| `axiom` | `propext`, `Classical.choice`; `sorryAx` (inert) | the axiom's exact type (`ConstantVal.matchesPin`); the inert `sorryAx` is matched at install, installs nothing, and any use of it declines |

**The standard axioms' families are blocks, never anchors.** Every role that
occurs in a standard axiom's type, transitively, is a `block` role: an
admitted axiom is true only of the declarations its type quantifies over, so
those declarations must be pinned whole, not by type. A type alone does not
pin a family's meaning: with `Nonempty := fun _ => True` (a definition of
`Nonempty`'s type) the axiom `Classical.choice` of the specified type over it
proves `False` (`choice False True.intro`), and `Iff := fun _ _ => True` does
the same for `propext`. `propext` mentions `Iff` and `Eq`, `Classical.choice`
mentions `Nonempty`, and those blocks mention only their own members
(`Role.stdAxiom_deps_blocks`). The quotient package is a basis block, so
`Quot.sound` is covered as well.

**The anchors, and why a type suffices for each.** An anchor is trusted for
nothing beyond its type: no admitted axiom mentions one, and every native rule
over one is certified against the bound constants themselves.
- `Bool`, `Bool.false`, `Bool.true`: the results of `Nat.beq` and `Nat.ble`.
  Their fast paths are admitted only with their equations, which are checked
  by definitional equality against the bound `Bool.true`/`Bool.false` and the
  bound operation's value, so a fast-path answer is the definition's.
- The literal support: a literal denotes its unfolding through the bound
  constants (`String.ofList [Char.ofNat …]`, `Nat.succ`/`Nat.zero`), and no
  rule asserts that two literals' unfoldings differ.
- `Bool.rec`, `And`, `And.intro`, `And.rec`: validated at install (below);
  the `And` rescue reads `And`'s projection table and proof irrelevance at
  use, not `And`'s meaning.
- `True`, `True.intro`: nothing in the checker reads them, so nothing
  validates them either; a table may bind them to anything of their types.
- `sorryAx`'s type mentions `Bool`. `sorryAx` is inert, never installed and
  never usable, so its type only fixes which declaration is tolerated.

**`sorryAx` in the fold.** The record at `sorryAx`'s key installs nothing,
and every use of the key declines (`unknownConstError`,
`unresolvedConstsError`), so consistency never depends on its type. Its type
is still matched at install (below): otherwise a table that binds `sorryAx`
to another axiom (`axiom evil : False`) would let that one record pass as the
tolerated declaration, and an accepted stream would no longer declare only
the standard axioms and Lean's `sorryAx`. IxVM's binding validation and the
Rust kernel's group admission compare the bound axiom with this type too.

Five roles have no use site that validates them: the anchors `Bool.rec`,
`And`, `And.intro` and `And.rec` (the `And` rescue relies on `And`'s
projection table and proof irrelevance at use, `andRescueSlots`, and needs
nothing of `And`'s type), and the inert `sorryAx`. The fold's step validates
them at install (owner, 2026-10-15; `installAnchors`,
`Cached.annotDeclStep`): a declaration that declares one whose type is not
its specification's, up to binder data and level-parameter names
(`matchesPin`), declines.

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

/-- **One equation of a definition's specification** (`Spec.eqns`): over the variables
`vars` (`fvar i` is the `i`-th; its type, `vars[i]`, may mention the earlier ones),
under the hypotheses `hyps`, `@Eq.{level} carrier lhs rhs`. -/
structure Equation (md : Mode) where
  vars : List (Expr md)
  hyps : List (Expr md)
  level : Level
  carrier : Expr md
  lhs : Expr md
  rhs : Expr md
  deriving Repr, Inhabited

/-- One role's specification. -/
inductive Spec (md : Mode) where
  /-- The exact declarations, up to `ConstantInfo.canon` (a basis block; every
  member of the block has the same specification). -/
  | block (decls : List (ConstantInfo md))
  /-- An exact type, up to binder data and level-parameter names. -/
  | anchor (levels : Nat) (type : Expr md)
  /-- The type and the characterizing equations: per equation its hypotheses,
  left and right sides, over `fvar 0`, `fvar 1` (the hypotheses are `fvar 2`,
  `fvar 3` in the certificate's telescope); the operation's self-reference is
  `.const (roleKey r) []`. -/
  | ops (type : Expr md) (eqs : List (List (Expr md) × Expr md × Expr md))
  /-- An axiom of the given type (`none`: of any type, which no role has since
  version 3). Whether it is installed is the role's: `propext` and
  `Classical.choice` are, while `sorryAx` is inert: tolerated as a
  declaration, it installs nothing, and any use declines. -/
  | axiom (levels : Nat) (type : Option (Expr md))
  /-- A definition of `levels` universe parameters whose type is `type` up to
  definitional equality, and whose equations hold: an unconditional one by
  definition or by a proof, a conditional one by a proof. Its self-reference is
  `.const (roleKey r) us`. -/
  | eqns (levels : Nat) (type : Expr md) (eqs : List (Equation md))
  deriving Repr, Inhabited

/-- The specification kinds, for summaries and the table's checks. -/
inductive SpecKind where
  | block | anchor | ops | axiom | eqns
  deriving DecidableEq, Repr, Inhabited

def Spec.kind : Spec md → SpecKind
  | .block _ => .block
  | .anchor .. => .anchor
  | .ops .. => .ops
  | .axiom .. => .axiom
  | .eqns .. => .eqns

/-- The evidence an operation's equations take, in order: `true` for an
unconditional equation (definitional equality), `false` for a conditional one
(a proof). Every other kind takes none. -/
def Spec.evidenceKinds : Spec md → List Bool
  | .ops _ eqs => eqs.map (·.1.isEmpty)
  | _ => []

/-- The evidence each equation may take, in order: `some true` a definitional entry
only, `some false` a proof only, `none` either. An operation's kinds are fixed
(`evidenceKinds`); a definition's unconditional equation takes either kind, so
that each toolchain uses definitional evidence where it holds, and a conditional
one takes a proof. Every other kind takes none. -/
def Spec.evidenceAllowed : Spec md → List (Option Bool)
  | .ops _ eqs => eqs.map fun e => some e.1.isEmpty
  | .eqns _ _ eqs => eqs.map fun e => if e.hyps.isEmpty then none else some false
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

/-- Does this entry take an allowed kind (`Spec.evidenceAllowed`)? -/
def Evidence.allowedBy {K : Type} (e : Evidence K) : Option Bool → Bool
  | none => true
  | some b => e.isDefeqKind b

/-- **What the fold is given of a role table**: per role, its evidence, a
proof entry carrying the theorem's key and its proof term (a theorem's value,
resolved by the front end). Soundness holds for every value
(`Ix.Kernel.model_exists`): the evidence decides which operations' fast
paths are enabled, nothing else. -/
abbrev Evidences (md : Mode) := List (Role × List (Evidence (Key md × Expr md)))

/-- The evidence of role `r` (none when the role has no entry). -/
def Evidences.of (ev : Evidences md) (r : Role) : List (Evidence (Key md × Expr md)) :=
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
def divModCertStmts (c : Key md) : List (List (Expr md) × Expr md) :=
  let natTy : Expr md := .const natName []
  let x : Expr md := .fvar 0 natTy
  let y : Expr md := .fvar 1 natTy
  let one : Expr md := .app (.const natSuccName []) (.const natZeroName [])
  let ble2 : Expr md → Expr md → Expr md := fun a b =>
    .app (.app (.const natBleName []) a) b
  let eqB : Expr md → Expr md → Expr md := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) (.const boolName [])) a) b
  let eqN : Expr md → Expr md → Expr md := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) natTy) a) b
  let op2 : Expr md → Expr md → Expr md := fun a b => .app (.app (.const c []) a) b
  let sub2 : Expr md → Expr md → Expr md := fun a b =>
    .app (.app (.const natSubName []) a) b
  let bT : Expr md := .const boolTrueName []
  let bF : Expr md := .const boolFalseName []
  let z : Expr md := .const natZeroName []
  let two : Expr md := .app (.const natSuccName []) one
  let mod2 : Expr md → Expr md → Expr md := fun a b =>
    .app (.app (.const natModName []) a) b
  let div2 : Expr md → Expr md → Expr md := fun a b =>
    .app (.app (.const natDivName []) a) b
  let add2 : Expr md → Expr md → Expr md := fun a b =>
    .app (.app (.const natAddName []) a) b
  let mul2 : Expr md → Expr md → Expr md := fun a b =>
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
  let recRhs : Expr md :=
    if c = natDivName then .app (.const natSuccName []) (op2 (sub2 x y) y)
    else op2 (sub2 x y) y
  let baseRhs : Expr md := if c = natDivName then .const natZeroName [] else x
  [([eqB (ble2 y x) bT, eqB (ble2 one y) bT], eqN (op2 x y) recRhs),
   ([eqB (ble2 y x) bF], eqN (op2 x y) baseRhs),
   ([eqB (ble2 one y) bF], eqN (op2 x y) baseRhs)]

/-- The sides of a certificate statement `Eq Nat lhs rhs`. -/
def eqSides : Expr md → Expr md × Expr md
  | .app (.app (.app (.const _ _) _) a) b => (a, b)
  | e => (e, e)

/-- A certificate statement `Eq Nat lhs rhs` from its sides. -/
def eqNatOf (a b : Expr md) : Expr md :=
  .app (.app (.app (.const eqName [.succ .zero]) (.const natName [])) a) b

/-! ## The specification terms that have no other home

The literal-support anchors (`CoreDefs.lean`'s `stringTyOk` … `charOfNatTyOk`
check exactly these shapes), the operations' types (`natOpTyPinned`), and the
anchors of the four roles today's checker does not validate. -/

/-- `List.{u} : Type u → Type u`. -/
def listSpecTy : Expr md := piA (srt (.succ u)) (srt (.succ u))

/-- `List.nil.{u} : (α : Type u) → List.{u} α`. -/
def listNilSpecTy : Expr md := pi "α" (srt (.succ u)) (.app (cnst listName [u]) (bv 0))

/-- `List.cons.{u} : (α : Type u) → α → List.{u} α → List.{u} α`. -/
def listConsSpecTy : Expr md :=
  pi "α" (srt (.succ u)) <|
  pi "head" (bv 0) <|
  pi "tail" (.app (cnst listName [u]) (bv 1)) <|
  .app (cnst listName [u]) (bv 2)

/-- `Char.ofNat : Nat → Char`. -/
def charOfNatSpecTy : Expr md := pi "n" (cnst natName) (cnst charName)

/-- `String.ofList : List.{0} Char → String`. -/
def stringOfListSpecTy : Expr md :=
  pi "data" (.app (cnst listName [.zero]) (cnst charName)) (cnst stringName)

/-- `Bool.rec.{u} {motive : Bool → Sort u} (false : motive false)
(true : motive true) (t : Bool) : motive t`. -/
def boolRecSpecTy : Expr md :=
  piI "motive" (pi "t" (cnst boolName) (srt u)) <|
  pi "false" (.app (bv 0) (cnst boolFalseName)) <|
  pi "true" (.app (bv 1) (cnst boolTrueName)) <|
  pi "t" (cnst boolName) (.app (bv 3) (bv 0))

/-- `And (a b : Prop) : Prop`. -/
def andSpecTy : Expr md := pi "a" prop <| pi "b" prop prop

/-- `And.intro {a b : Prop} (left : a) (right : b) : And a b`. -/
def andIntroSpecTy : Expr md :=
  piI "a" prop <| piI "b" prop <| pi "left" (bv 1) <| pi "right" (bv 1) <|
  ap2 (cnst andName) (bv 3) (bv 2)

/-- `And.rec.{u} {a b : Prop} {motive : And a b → Sort u}
(intro : (left : a) → (right : b) → motive (And.intro left right))
(t : And a b) : motive t`. -/
def andRecSpecTy : Expr md :=
  piI "a" prop <|
  piI "b" prop <|
  piI "motive" (pi "t" (ap2 (cnst andName) (bv 1) (bv 0)) (srt u)) <|
  pi "intro"
    (pi "left" (bv 2) <| pi "right" (bv 2) <|
      .app (bv 2) (ap4 (cnst andIntroName) (bv 4) (bv 3) (bv 1) (bv 0))) <|
  pi "t" (ap2 (cnst andName) (bv 3) (bv 2)) (.app (bv 2) (bv 0))

/-- `Nat → Nat`. -/
def natUnSpecTy : Expr md := pi "n" (cnst natName) (cnst natName)

/-- `Nat → Nat → Nat`. -/
def natBinSpecTy : Expr md := pi "n" (cnst natName) <| pi "m" (cnst natName) (cnst natName)

/-- `Nat → Nat → Bool`. -/
def natCmpSpecTy : Expr md := pi "n" (cnst natName) <| pi "m" (cnst natName) (cnst boolName)

/-- An `ops` specification from the structural recurrences (`natOpEquations`,
unconditional) at the variables `fvar 0`, `fvar 1`. -/
def natOpsSpec (ty : Expr md) (c : Key md) : Spec md :=
  .ops ty ((natOpEquations 0 c).map fun (l, r) => ([], l, r))

/-- An `ops` specification from the certificate statements
(`divModCertStmts`, conditional). -/
def divModSpec (c : Key md) : Spec md :=
  .ops natBinSpecTy ((divModCertStmts c).map fun (hs, e) => (hs, (eqSides e).1, (eqSides e).2))

/-- The name `True`. -/
abbrev trueName : Key md := roleKey .true

/-- The name `True.intro`. -/
abbrev trueIntroName : Key md := roleKey .trueIntro

/-- `True : Prop` (shape only; capabilities are not specified). -/
def trueCvA : ConstantVal md := ⟨trueName, [], .sort .zero⟩

/-- `True.intro : True`. -/
def trueIntroCvA : ConstantVal md := ⟨trueIntroName, [], .const trueName []⟩

/-- `Bool : Type` (shape only). -/
def boolCvA : ConstantVal md := ⟨boolName, [], .sort (.succ .zero)⟩

/-- `sorryAx.{u} (α : Sort u) (synthetic : Bool) : α`. -/
def sorryAxSpecTy : Expr md := pi "α" (srt u) <| pi "synthetic" (cnst boolName) (bv 1)

/-! ## The definitions specified by their equations (version 3)

The decision procedures, `Int`, `BitVec` and the `String` operations that
IxVM evaluates natively. Each is a definition specified by its type and by
equations at constructor patterns (`Spec.eqns`); the types the equations need
and the constants results are built from are type-only anchors. A native rule
that fires on one of these roles computes an instance of an equation its
bound constant was validated against, so its result is the definitional
unfolding's. `Decidable` is never specified by its shape: a decision
procedure is specified through `Decidable.decide`, whose two computation
equations and extensionality determine a `Decidable p` value by its `decide`.
Specifications contain no literals: `2` is `succ (succ zero)`. -/

/-- A role's constant. -/
def specC (r : Role) (us : List Level := []) : Expr md := .const (roleKey r) us

/-- `Eq.{1} α a b`. -/
def specEq1 (α a b : Expr md) : Expr md := ap3 (cnst eqName [.succ .zero]) α a b

/-- `Nat`, `Bool`, `true`, `false`, `Nat.zero`, `Nat.succ n` and `2`. -/
def specNat : Expr md := cnst natName
def specBool : Expr md := cnst boolName
def specTrue : Expr md := cnst boolTrueName
def specFalse : Expr md := cnst boolFalseName
def specZero : Expr md := cnst natZeroName
def specSucc (n : Expr md) : Expr md := .app (cnst natSuccName) n
def specTwo : Expr md := specSucc (specSucc specZero)

/-- `Decidable p`, `Decidable.decide p inst` and `Not p`. -/
def specDec (p : Expr md) : Expr md := .app (specC .decidable) p
def specDecide (p inst : Expr md) : Expr md := ap2 (specC .decidableDecide) p inst
def specNot (p : Expr md) : Expr md := .app (specC .notProp) p

/-- `Int`, `Int.ofNat n`, `Int.negSucc n`. -/
def specInt : Expr md := specC .int
def specOfNat (n : Expr md) : Expr md := .app (specC .intOfNat) n
def specNegSucc (n : Expr md) : Expr md := .app (specC .intNegSucc) n

/-- A binary `Nat` operation's application. -/
def specNatOp (r : Role) (a b : Expr md) : Expr md := ap2 (specC r) a b

/-- An unconditional equation in `Type` over `vars`. -/
def specEqn (vars : List (Expr md)) (carrier lhs rhs : Expr md) : Equation md :=
  { vars, hyps := [], level := .succ .zero, carrier, lhs, rhs }

/-- A conditional equation in `Type` over `vars`. -/
def specCert (vars hyps : List (Expr md)) (carrier lhs rhs : Expr md) : Equation md :=
  { vars, hyps, level := .succ .zero, carrier, lhs, rhs }

/-- Variable `i` of an equation, of type `ty`. -/
def specVar (i : Nat) (ty : Expr md) : Expr md := .fvar i ty

/-- `Decidable : Prop → Type`. -/
def decidableSpecTy : Expr md := piA prop type1

/-- `Decidable.isTrue {p : Prop} (h : p) : Decidable p`. -/
def decidableIsTrueSpecTy : Expr md := piI "p" prop <| pi "h" (bv 0) (specDec (bv 1))

/-- `Decidable.isFalse {p : Prop} (h : Not p) : Decidable p`. -/
def decidableIsFalseSpecTy : Expr md :=
  piI "p" prop <| pi "h" (specNot (bv 0)) (specDec (bv 1))

/-- `Not : Prop → Prop`. -/
def notSpecTy : Expr md := piA prop prop

/-- `Decidable.decide (p : Prop) [h : Decidable p] : Bool`. -/
def decideSpecTy : Expr md := pi "p" prop <| piI "h" (specDec (bv 0)) specBool

/-- `of_decide_eq_true {p : Prop} [inst : Decidable p] : decide p = true → p`. -/
def ofDecideEqTrueSpecTy : Expr md :=
  piI "p" prop <| piI "inst" (specDec (bv 0)) <|
  piA (specEq1 specBool (specDecide (bv 1) (bv 0)) specTrue) (bv 2)

/-- `of_decide_eq_false {p : Prop} [inst : Decidable p] : decide p = false → Not p`. -/
def ofDecideEqFalseSpecTy : Expr md :=
  piI "p" prop <| piI "inst" (specDec (bv 0)) <|
  piA (specEq1 specBool (specDecide (bv 1) (bv 0)) specFalse) (specNot (bv 2))

/-- `decide`'s equations: `decide p (isTrue h) = true`, `decide p (isFalse h) = false`,
and extensionality, `decide p a = decide p b → a = b`. -/
def decideEqns : List (Equation md) :=
  let p : Expr md := specVar 0 prop
  let a : Expr md := specVar 1 (specDec p)
  let b : Expr md := specVar 2 (specDec p)
  [specEqn [prop, p] specBool (specDecide p (ap2 (specC .decidableIsTrue) p (specVar 1 p))) specTrue,
   specEqn [prop, specNot p] specBool
     (specDecide p (ap2 (specC .decidableIsFalse) p (specVar 1 (specNot p)))) specFalse,
   specCert [prop, specDec p, specDec p] [specEq1 specBool (specDecide p a) (specDecide p b)]
     (specDec p) a b]

/-- `Nat → Nat → Prop`. -/
def natRelSpecTy : Expr md := piA specNat (piA specNat prop)

/-- `(n m : Nat) → Decidable (P n m)`. -/
def natDecSpecTy (P : Expr md → Expr md → Expr md) : Expr md :=
  pi "n" specNat <| pi "m" specNat (specDec (P (bv 1) (bv 0)))

/-- A `Nat` decision procedure `d` for `P`, whose `decide` is the `Bool` operation `b`. -/
def natDecEqns (d : Role) (P : Expr md → Expr md → Expr md) (b : Role) : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  let y : Expr md := specVar 1 specNat
  [specEqn [specNat, specNat] specBool (specDecide (P x y) (specNatOp d x y)) (specNatOp b x y)]

/-- `n = m` and `Nat.le n m`. -/
def natEqP (a b : Expr md) : Expr md := specEq1 specNat a b
def natLeP (a b : Expr md) : Expr md := specNatOp .natLe a b

/-- `Nat.decLt x y = Nat.decLe (succ x) y`. -/
def natDecLtEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  let y : Expr md := specVar 1 specNat
  [specEqn [specNat, specNat] (specDec (natLeP (specSucc x) y)) (specNatOp .natDecLt x y)
    (specNatOp .natDecLe (specSucc x) y)]

/-- `Nat → Int`, `Int → Int`, `Int → Int → Int`, `Nat → Nat → Int`. -/
def natIntSpecTy : Expr md := piA specNat specInt
def intUnSpecTy : Expr md := piA specInt specInt
def intBinSpecTy : Expr md := piA specInt (piA specInt specInt)
def natNatIntSpecTy : Expr md := piA specNat (piA specNat specInt)

/-- Equations over `x y : Nat` (`f x y`), unconditional. -/
def natNatEqns (carrier : Expr md) (sides : List ((Expr md → Expr md → Expr md) × (Expr md → Expr md → Expr md))) :
    List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  let y : Expr md := specVar 1 specNat
  sides.map fun (l, r) => specEqn [specNat, specNat] carrier (l x y) (r x y)

/-- `Int.negOfNat`: `negOfNat 0 = ofNat 0`, `negOfNat (succ x) = negSucc x`. -/
def intNegOfNatEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  [specEqn [] specInt (.app (specC .intNegOfNat) specZero) (specOfNat specZero),
   specEqn [specNat] specInt (.app (specC .intNegOfNat) (specSucc x)) (specNegSucc x)]

/-- `Int.subNatNat x y`: `ofNat (x - y)` when `y ≤ x`, else `negSucc (pred (y - x))`. -/
def intSubNatNatEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  let y : Expr md := specVar 1 specNat
  let lhs : Expr md := specNatOp .intSubNatNat x y
  let guard (v : Expr md) : Expr md := specEq1 specBool (specNatOp .natBle y x) v
  [specCert [specNat, specNat] [guard specTrue] specInt lhs (specOfNat (specNatOp .natSub x y)),
   specCert [specNat, specNat] [guard specFalse] specInt lhs
     (specNegSucc (.app (specC .natPred) (specNatOp .natSub y x)))]

/-- `Int.neg` at the two constructors. -/
def intNegEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  [specEqn [specNat] specInt (.app (specC .intNeg) (specOfNat x)) (.app (specC .intNegOfNat) x),
   specEqn [specNat] specInt (.app (specC .intNeg) (specNegSucc x)) (specOfNat (specSucc x))]

/-- `Int.natAbs` at the two constructors. -/
def intNatAbsEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  [specEqn [specNat] specNat (.app (specC .intNatAbs) (specOfNat x)) x,
   specEqn [specNat] specNat (.app (specC .intNatAbs) (specNegSucc x)) (specSucc x)]

/-- `Int.sub a b = Int.add a (Int.neg b)`. -/
def intSubEqns : List (Equation md) :=
  let a : Expr md := specVar 0 specInt
  let b : Expr md := specVar 1 specInt
  [specEqn [specInt, specInt] specInt (specNatOp .intSub a b)
    (specNatOp .intAdd a (.app (specC .intNeg) b))]

/-- A binary `Int` operation `op` at constructor patterns. -/
def intOp (op : Role) (a b : Expr md) : Expr md := specNatOp op a b

/-- `Int.add`, `Int.mul`, `Int.ediv` and `Int.emod` at constructor patterns. -/
def intAddEqns : List (Equation md) :=
  natNatEqns specInt
    [(fun x y => intOp .intAdd (specOfNat x) (specOfNat y), fun x y => specOfNat (specNatOp .natAdd x y)),
     (fun x y => intOp .intAdd (specOfNat x) (specNegSucc y),
       fun x y => specNatOp .intSubNatNat x (specSucc y)),
     (fun x y => intOp .intAdd (specNegSucc x) (specOfNat y),
       fun x y => specNatOp .intSubNatNat y (specSucc x)),
     (fun x y => intOp .intAdd (specNegSucc x) (specNegSucc y),
       fun x y => specNegSucc (specSucc (specNatOp .natAdd x y)))]

def intMulEqns : List (Equation md) :=
  natNatEqns specInt
    [(fun x y => intOp .intMul (specOfNat x) (specOfNat y), fun x y => specOfNat (specNatOp .natMul x y)),
     (fun x y => intOp .intMul (specOfNat x) (specNegSucc y),
       fun x y => .app (specC .intNegOfNat) (specNatOp .natMul x (specSucc y))),
     (fun x y => intOp .intMul (specNegSucc x) (specOfNat y),
       fun x y => .app (specC .intNegOfNat) (specNatOp .natMul (specSucc x) y)),
     (fun x y => intOp .intMul (specNegSucc x) (specNegSucc y),
       fun x y => specOfNat (specNatOp .natMul (specSucc x) (specSucc y)))]

def intEdivEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  natNatEqns specInt
    [(fun x y => intOp .intEdiv (specOfNat x) (specOfNat y), fun x y => specOfNat (specNatOp .natDiv x y)),
     (fun x y => intOp .intEdiv (specOfNat x) (specNegSucc y),
       fun x y => .app (specC .intNeg) (specOfNat (specNatOp .natDiv x (specSucc y))))] ++
  [specEqn [specNat] specInt (intOp .intEdiv (specNegSucc x) (specOfNat specZero)) (specOfNat specZero)] ++
  natNatEqns specInt
    [(fun x y => intOp .intEdiv (specNegSucc x) (specOfNat (specSucc y)),
       fun x y => specNegSucc (specNatOp .natDiv x (specSucc y))),
     (fun x y => intOp .intEdiv (specNegSucc x) (specNegSucc y),
       fun x y => specOfNat (specSucc (specNatOp .natDiv x (specSucc y))))]

def intEmodEqns : List (Equation md) :=
  natNatEqns specInt
    [(fun x y => intOp .intEmod (specOfNat x) (specOfNat y), fun x y => specOfNat (specNatOp .natMod x y)),
     (fun x y => intOp .intEmod (specOfNat x) (specNegSucc y),
       fun x y => specOfNat (specNatOp .natMod x (specSucc y))),
     (fun x y => intOp .intEmod (specNegSucc x) (specOfNat y),
       fun x y => specNatOp .intSubNatNat y (specSucc (specNatOp .natMod x y))),
     (fun x y => intOp .intEmod (specNegSucc x) (specNegSucc y),
       fun x y => specNatOp .intSubNatNat (specSucc y) (specSucc (specNatOp .natMod x (specSucc y))))]

/-- `Int.pow`: `ofNat x ^ y = ofNat (x ^ y)`; `negSucc x ^ y` by the parity of `y`. -/
def intPowEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specNat
  let y : Expr md := specVar 1 specNat
  let pow (a : Expr md) : Expr md := ap2 (specC .intPow) a y
  let mag : Expr md := specNatOp .natPow (specSucc x) y
  let parity (v : Expr md) : Expr md :=
    specEq1 specBool (specNatOp .natBeq (specNatOp .natMod y specTwo) specZero) v
  [specEqn [specNat, specNat] specInt (pow (specOfNat x)) (specOfNat (specNatOp .natPow x y)),
   specCert [specNat, specNat] [parity specTrue] specInt (pow (specNegSucc x)) (specOfNat mag),
   specCert [specNat, specNat] [parity specFalse] specInt (pow (specNegSucc x))
     (.app (specC .intNeg) (specOfNat mag))]

/-- `BitVec : Nat → Type`, `BitVec.ofNat (n : Nat) (i : Nat) : BitVec n`. -/
def bitVecSpecTy : Expr md := piA specNat type1
def bitVecOfNatSpecTy : Expr md := pi "n" specNat <| piA specNat (.app (specC .bitVec) (bv 1))

/-- `BitVec.toNat {w : Nat} (x : BitVec w) : Nat`. -/
def bitVecToNatSpecTy : Expr md := piI "w" specNat <| piA (.app (specC .bitVec) (bv 0)) specNat

/-- `BitVec.ult {n : Nat} (x y : BitVec n) : Bool`. -/
def bitVecUltSpecTy : Expr md :=
  piI "n" specNat <| piA (.app (specC .bitVec) (bv 0)) <| piA (.app (specC .bitVec) (bv 1)) specBool

/-- `x % 2 ^ w`. -/
def specMod2Pow (x w : Expr md) : Expr md := specNatOp .natMod x (specNatOp .natPow specTwo w)

/-- `toNat (ofNat w x) = x % 2 ^ w`. -/
def bitVecToNatEqns : List (Equation md) :=
  let w : Expr md := specVar 0 specNat
  let x : Expr md := specVar 1 specNat
  [specEqn [specNat, specNat] specNat (ap2 (specC .bitVecToNat) w (ap2 (specC .bitVecOfNat) w x))
    (specMod2Pow x w)]

/-- `ult (ofNat w x) (ofNat w y) = ble (succ (x % 2 ^ w)) (y % 2 ^ w)`. -/
def bitVecUltEqns : List (Equation md) :=
  let w : Expr md := specVar 0 specNat
  let x : Expr md := specVar 1 specNat
  let y : Expr md := specVar 2 specNat
  [specEqn [specNat, specNat, specNat] specBool
    (ap3 (specC .bitVecUlt) w (ap2 (specC .bitVecOfNat) w x) (ap2 (specC .bitVecOfNat) w y))
    (specNatOp .natBle (specSucc (specMod2Pow x w)) (specMod2Pow y w))]

/-- `String`, `List.{0} Char`, `String.ofList l`. -/
def specString : Expr md := cnst stringName
def specCharList : Expr md := .app (cnst listName [.zero]) (cnst charName)
def specOfList (l : Expr md) : Expr md := .app (cnst stringOfListName) l

/-- `String.decEq (a b : String) : Decidable (a = b)`. -/
def stringDecEqSpecTy : Expr md :=
  pi "a" specString <| pi "b" specString (specDec (specEq1 specString (bv 1) (bv 0)))

/-- `decide (String.decEq s s) = true`. -/
def stringDecEqEqns : List (Equation md) :=
  let s : Expr md := specVar 0 specString
  [specEqn [specString] specBool (specDecide (specEq1 specString s s) (ap2 (specC .stringDecEq) s s))
    specTrue]

/-- `String.toByteArray : String → ByteArray`, and its value at `""`. -/
def stringToByteArraySpecTy : Expr md := piA specString (specC .byteArray)
def stringToByteArrayEqns : List (Equation md) :=
  [specEqn [] (specC .byteArray)
    (.app (specC .stringToByteArray) (specOfList (.app (cnst listNilName [.zero]) (cnst charName))))
    (specC .byteArrayEmpty)]

/-- `List.append.{u} {α : Type u} (xs ys : List α) : List α`. -/
def listAppendSpecTy : Expr md :=
  piI "α" (srt (.succ u)) <|
  piA (.app (cnst listName [u]) (bv 0)) <|
  piA (.app (cnst listName [u]) (bv 1)) (.app (cnst listName [u]) (bv 2))

/-- `[] ++ ys = ys`, `(a :: as) ++ ys = a :: (as ++ ys)`. -/
def listAppendEqns : List (Equation md) :=
  let ty : Expr md := srt (.succ u)
  let α : Expr md := specVar 0 ty
  let L : Expr md := .app (cnst listName [u]) α
  let app (a b : Expr md) : Expr md := ap3 (specC .listAppend [u]) α a b
  let nil : Expr md := .app (cnst listNilName [u]) α
  let cons (h t : Expr md) : Expr md := ap3 (cnst listConsName [u]) α h t
  let ys1 : Expr md := specVar 1 L
  let a : Expr md := specVar 1 α
  let as : Expr md := specVar 2 L
  let ys3 : Expr md := specVar 3 L
  [{ vars := [ty, L], hyps := [], level := .succ u, carrier := L, lhs := app nil ys1, rhs := ys1 },
   { vars := [ty, α, L, L], hyps := [], level := .succ u, carrier := L,
     lhs := app (cons a as) ys3, rhs := cons a (app as ys3) }]

/-- `String.append (ofList xs) (ofList ys) = ofList (xs ++ ys)`. -/
def stringAppendEqns : List (Equation md) :=
  let xs : Expr md := specVar 0 specCharList
  let ys : Expr md := specVar 1 specCharList
  [specEqn [specCharList, specCharList] specString
    (ap2 (specC .stringAppend) (specOfList xs) (specOfList ys))
    (specOfList (ap3 (specC .listAppend [.zero]) (cnst charName) xs ys))]

/-! ### `ite`, the `Int` decision procedures, `Int.bmod`, `Int.bdiv` and the
`String` size and last character

`ite` is specified by its two computation equations, so a native rule may
choose a branch by the condition's decision. The `Int` decision procedures are
specified, like the `Nat` ones, by `decide` at the four constructor pairs.
`Int.bmod` and `Int.bdiv` are specified by their definitional unfoldings,
through `ite` and those decisions. A string's size and last character are
specified over `String.ofList`, `Char.utf8Size` over the ranges of Unicode
scalar values (IxVM's literals are exactly the encodings of `Char` lists). -/

/-- `n` as `Nat.zero`, `Nat.succ` and doubling (`Nat.mul 2`), within `fuel` steps:
a short term for a large bound. -/
def specNumGo : Nat → Nat → Expr md
  | 0, _ => specZero
  | fuel + 1, n =>
    if n == 0 then specZero
    else if n % 2 == 0 then specNatOp .natMul specTwo (specNumGo fuel (n / 2))
    else specSucc (specNumGo fuel (n - 1))

/-- A numeral below `2 ^ 32` (`specNumGo` with enough fuel). -/
def specNum (n : Nat) : Expr md := specNumGo 64 n

/-- `ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α`. -/
def iteSpecTy : Expr md :=
  piI "α" (srt u) <| pi "c" prop <| piI "h" (specDec (bv 0)) <| piA (bv 2) <| piA (bv 3) (bv 4)

/-- `ite c (isTrue h) t e = t`, `ite c (isFalse h) t e = e`. -/
def iteEqns : List (Equation md) :=
  let α : Expr md := specVar 0 (srt u)
  let c : Expr md := specVar 1 prop
  let t : Expr md := specVar 3 α
  let e : Expr md := specVar 4 α
  let ite (h : Expr md) : Expr md := ap3 (ap2 (specC .ifThenElse [u]) α c) h t e
  [{ vars := [srt u, prop, c, α, α], hyps := [], level := u, carrier := α,
     lhs := ite (ap2 (specC .decidableIsTrue) c (specVar 2 c)), rhs := t },
   { vars := [srt u, prop, specNot c, α, α], hyps := [], level := u, carrier := α,
     lhs := ite (ap2 (specC .decidableIsFalse) c (specVar 2 (specNot c))), rhs := e }]

/-- `1`, `a = b` and `a < b` (`Int.lt a b` is `Int.le (a + 1) b`) over `Int`. -/
def specOne : Expr md := specSucc specZero
def intEqP (a b : Expr md) : Expr md := specEq1 specInt a b
def intLeP (a b : Expr md) : Expr md := ap2 (specC .intLe) a b
def intLtP (a b : Expr md) : Expr md := intLeP (specNatOp .intAdd a (specOfNat specOne)) b

/-- `(a b : Int) → Decidable (P a b)`. -/
def intDecSpecTy (P : Expr md → Expr md → Expr md) : Expr md :=
  pi "a" specInt <| pi "b" specInt (specDec (P (bv 1) (bv 0)))

/-- An `Int` decision procedure `d` for `P` at the four constructor pairs
(`ofNat`/`negSucc` of `x`, then of `y`): `decide (d A B)` is the given `Bool`. -/
def intDecEqns (d : Role) (P : Expr md → Expr md → Expr md)
    (oo on no nn : Expr md → Expr md → Expr md) : List (Equation md) :=
  let side (A B : Expr md) : Expr md := specDecide (P A B) (specNatOp d A B)
  natNatEqns specBool
    [(fun x y => side (specOfNat x) (specOfNat y), oo),
     (fun x y => side (specOfNat x) (specNegSucc y), on),
     (fun x y => side (specNegSucc x) (specOfNat y), no),
     (fun x y => side (specNegSucc x) (specNegSucc y), nn)]

/-- `Int.decLt a b = Int.decLe (a + 1) b`. -/
def intDecLtEqns : List (Equation md) :=
  let a : Expr md := specVar 0 specInt
  let b : Expr md := specVar 1 specInt
  [specEqn [specInt, specInt] (specDec (intLtP a b)) (specNatOp .intDecLt a b)
    (specNatOp .intDecLe (specNatOp .intAdd a (specOfNat specOne)) b)]

/-- `let r := x % m; if r < (m + 1) / 2 then t else e`, over `Int`. -/
def bmodIte (x m t e : Expr md) : Expr md :=
  let r : Expr md := specNatOp .intEmod x (specOfNat m)
  let q : Expr md :=
    specNatOp .intEdiv (specNatOp .intAdd (specOfNat m) (specOfNat specOne)) (specOfNat specTwo)
  ap3 (ap2 (specC .ifThenElse [.succ .zero]) specInt (intLtP r q)) (specNatOp .intDecLt r q) t e

/-- `Int.bmod x m`, by definition. -/
def intBmodEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specInt
  let m : Expr md := specVar 1 specNat
  let r : Expr md := specNatOp .intEmod x (specOfNat m)
  [specEqn [specInt, specNat] specInt (specNatOp .intBmod x m)
    (bmodIte x m r (specNatOp .intSub r (specOfNat m)))]

/-- `Int.bdiv x m`, by definition. -/
def intBdivEqns : List (Equation md) :=
  let x : Expr md := specVar 0 specInt
  let m : Expr md := specVar 1 specNat
  let q : Expr md := specNatOp .intEdiv x (specOfNat m)
  [specEqn [specInt, specNat] specInt (specNatOp .intBdiv x m)
    (ap3 (ap2 (specC .ifThenElse [.succ .zero]) specInt (specEq1 specNat m specZero))
      (specNatOp .natDecEq m specZero) (specOfNat specZero)
      (bmodIte x m q (specNatOp .intAdd q (specOfNat specOne))))]

/-- `Char`, `[] : List Char`, `c :: l`, `Char.ofNat n`. -/
def specChar : Expr md := cnst charName
def specCharNil : Expr md := .app (cnst listNilName [.zero]) specChar
def specCharCons (c l : Expr md) : Expr md := ap3 (cnst listConsName [.zero]) specChar c l
def specCharOfNat (n : Expr md) : Expr md := .app (cnst charOfNatName) n

/-- `Char.utf8Size (Char.ofNat n)` over the ranges of scalar values: 1 below
`0x80`, 2 below `0x800`, 3 below `0xD800` and in `[0xE000, 0x10000)`, 4 below
`0x110000`. -/
def charUtf8SizeEqns : List (Equation md) :=
  let n : Expr md := specVar 0 specNat
  let size : Expr md := .app (specC .charUtf8Size) (specCharOfNat n)
  let lt (b : Nat) : Expr md := specEq1 specBool (specNatOp .natBle (specSucc n) (specNum b)) specTrue
  let ge (b : Nat) : Expr md := specEq1 specBool (specNatOp .natBle (specNum b) n) specTrue
  [specCert [specNat] [lt 0x80] specNat size (specNum 1),
   specCert [specNat] [ge 0x80, lt 0x800] specNat size (specNum 2),
   specCert [specNat] [ge 0x800, lt 0xD800] specNat size (specNum 3),
   specCert [specNat] [ge 0xE000, lt 0x10000] specNat size (specNum 3),
   specCert [specNat] [ge 0x10000, lt 0x110000] specNat size (specNum 4)]

/-- `utf8ByteSize (ofList []) = 0`, `utf8ByteSize (ofList (c :: cs)) = c.utf8Size + utf8ByteSize (ofList cs)`. -/
def stringUtf8ByteSizeEqns : List (Equation md) :=
  let c : Expr md := specVar 0 specChar
  let cs : Expr md := specVar 1 specCharList
  let size (l : Expr md) : Expr md := .app (specC .stringUtf8ByteSize) (specOfList l)
  [specEqn [] specNat (size specCharNil) specZero,
   specEqn [specChar, specCharList] specNat (size (specCharCons c cs))
     (specNatOp .natAdd (.app (specC .charUtf8Size) c) (size cs))]

/-- `back (ofList []) = Char.ofNat 65` (the default `Char`), `back (ofList [c]) = c`,
`back (ofList (c :: d :: ds)) = back (ofList (d :: ds))`. -/
def stringBackEqns : List (Equation md) :=
  let c : Expr md := specVar 0 specChar
  let d : Expr md := specVar 1 specChar
  let ds : Expr md := specVar 2 specCharList
  let back (l : Expr md) : Expr md := .app (specC .stringBack) (specOfList l)
  [specEqn [] specChar (back specCharNil) (specCharOfNat (specNum 65)),
   specEqn [specChar] specChar (back (specCharCons c specCharNil)) c,
   specEqn [specChar, specChar, specCharList] specChar
     (back (specCharCons c (specCharCons d ds))) (back (specCharCons d ds))]

/-! ## The specification of every role -/

/-- **The specification set.** -/
def Role.spec : Role → Spec md
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
  | .iff | .iffIntro | .iffRec => .block iffFamily
  | .nonempty | .nonemptyIntro | .nonemptyRec => .block nonemptyFamily
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
  | .sorryAx => .axiom 1 (some sorryAxSpecTy)
  | .decidable => .anchor 0 decidableSpecTy
  | .decidableIsTrue => .anchor 0 decidableIsTrueSpecTy
  | .decidableIsFalse => .anchor 0 decidableIsFalseSpecTy
  | .notProp => .anchor 0 notSpecTy
  | .ofDecideEqTrue => .anchor 0 ofDecideEqTrueSpecTy
  | .ofDecideEqFalse => .anchor 0 ofDecideEqFalseSpecTy
  | .decidableDecide => .eqns 0 decideSpecTy decideEqns
  | .natLe => .anchor 0 natRelSpecTy
  | .natDecEq => .eqns 0 (natDecSpecTy natEqP) (natDecEqns .natDecEq natEqP .natBeq)
  | .natDecLe => .eqns 0 (natDecSpecTy natLeP) (natDecEqns .natDecLe natLeP .natBle)
  | .natDecLt => .eqns 0 (natDecSpecTy fun a b => natLeP (specSucc a) b) natDecLtEqns
  | .int => .anchor 0 type1
  | .intOfNat => .anchor 0 natIntSpecTy
  | .intNegSucc => .anchor 0 natIntSpecTy
  | .intNegOfNat => .eqns 0 natIntSpecTy intNegOfNatEqns
  | .intSubNatNat => .eqns 0 natNatIntSpecTy intSubNatNatEqns
  | .intNeg => .eqns 0 intUnSpecTy intNegEqns
  | .intAdd => .eqns 0 intBinSpecTy intAddEqns
  | .intSub => .eqns 0 intBinSpecTy intSubEqns
  | .intMul => .eqns 0 intBinSpecTy intMulEqns
  | .intNatAbs => .eqns 0 (piA specInt specNat) intNatAbsEqns
  | .intEdiv => .eqns 0 intBinSpecTy intEdivEqns
  | .intEmod => .eqns 0 intBinSpecTy intEmodEqns
  | .intPow => .eqns 0 (piA specInt (piA specNat specInt)) intPowEqns
  | .bitVec => .anchor 0 bitVecSpecTy
  | .bitVecOfNat => .anchor 0 bitVecOfNatSpecTy
  | .bitVecToNat => .eqns 0 bitVecToNatSpecTy bitVecToNatEqns
  | .bitVecUlt => .eqns 0 bitVecUltSpecTy bitVecUltEqns
  | .stringDecEq => .eqns 0 stringDecEqSpecTy stringDecEqEqns
  | .byteArray => .anchor 0 type1
  | .byteArrayEmpty => .anchor 0 (specC .byteArray)
  | .stringToByteArray => .eqns 0 stringToByteArraySpecTy stringToByteArrayEqns
  | .listAppend => .eqns 1 listAppendSpecTy listAppendEqns
  | .stringAppend => .eqns 0 (piA specString (piA specString specString)) stringAppendEqns
  | .ifThenElse => .eqns 1 iteSpecTy iteEqns
  | .intLe => .anchor 0 (piA specInt (piA specInt prop))
  | .intDecEq => .eqns 0 (intDecSpecTy intEqP)
      (intDecEqns .intDecEq intEqP (specNatOp .natBeq) (fun _ _ => specFalse) (fun _ _ => specFalse)
        (specNatOp .natBeq))
  | .intDecLe => .eqns 0 (intDecSpecTy intLeP)
      (intDecEqns .intDecLe intLeP (specNatOp .natBle) (fun _ _ => specFalse) (fun _ _ => specTrue)
        (fun x y => specNatOp .natBle y x))
  | .intDecLt => .eqns 0 (intDecSpecTy intLtP) intDecLtEqns
  | .intBmod => .eqns 0 (piA specInt (piA specNat specInt)) intBmodEqns
  | .intBdiv => .eqns 0 (piA specInt (piA specNat specInt)) intBdivEqns
  | .charUtf8Size => .eqns 0 (piA specChar specNat) charUtf8SizeEqns
  | .stringUtf8ByteSize => .eqns 0 (piA specString specNat) stringUtf8ByteSizeEqns
  | .stringBack => .eqns 0 (piA specString specChar) stringBackEqns

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
  | .decidable | .decidableIsTrue | .decidableIsFalse =>
    [.decidable, .decidableIsTrue, .decidableIsFalse]
  | .int | .intOfNat | .intNegSucc => [.int, .intOfNat, .intNegSucc]
  | .bitVec | .bitVecOfNat => [.bitVec, .bitVecOfNat]
  | .byteArray | .byteArrayEmpty => [.byteArray, .byteArrayEmpty]
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
  | .sorryAx => [.bool]
  | .decidableIsFalse => [.notProp]
  | .ofDecideEqTrue => [.decidable, .decidableDecide, .bool, .eq]
  | .ofDecideEqFalse => [.decidable, .decidableDecide, .notProp, .bool, .eq]
  | .decidableDecide => [.decidable, .notProp, .bool, .eq]
  | .natLe => [.nat]
  | .natDecEq => [.nat, .bool, .eq, .decidable, .decidableDecide, .natBeq]
  | .natDecLe => [.nat, .bool, .eq, .decidable, .decidableDecide, .natLe, .natBle]
  | .natDecLt => [.nat, .eq, .decidable, .natLe, .natDecLe]
  | .intOfNat | .intNegSucc => [.nat]
  | .intNegOfNat => [.nat, .int, .eq]
  | .intSubNatNat => [.nat, .int, .bool, .eq, .natPred, .natSub, .natBle]
  | .intNeg => [.nat, .int, .eq, .intNegOfNat]
  | .intAdd => [.nat, .int, .eq, .natAdd, .intSubNatNat]
  | .intSub => [.int, .eq, .intAdd, .intNeg]
  | .intMul => [.nat, .int, .eq, .natMul, .intNegOfNat]
  | .intNatAbs => [.nat, .int, .eq]
  | .intEdiv => [.nat, .int, .eq, .natDiv, .intNeg]
  | .intEmod => [.nat, .int, .eq, .natMod, .intSubNatNat]
  | .intPow => [.nat, .int, .bool, .eq, .natPow, .natMod, .natBeq, .intNeg]
  | .bitVec | .bitVecOfNat => [.nat]
  | .bitVecToNat => [.nat, .eq, .bitVec, .natMod, .natPow]
  | .bitVecUlt => [.nat, .bool, .eq, .bitVec, .natMod, .natPow, .natBle]
  | .stringDecEq => [.string, .bool, .eq, .decidable, .decidableDecide]
  | .stringToByteArray => [.string, .list, .char, .stringOfList, .eq, .byteArray]
  | .listAppend => [.list, .eq]
  | .stringAppend => [.string, .list, .char, .stringOfList, .eq, .listAppend]
  | .ifThenElse => [.decidable, .notProp, .eq]
  | .intLe => [.int]
  | .intDecEq => [.nat, .int, .bool, .eq, .decidable, .decidableDecide, .natBeq]
  | .intDecLe => [.nat, .int, .bool, .eq, .decidable, .decidableDecide, .intLe, .natBle]
  | .intDecLt => [.nat, .int, .eq, .decidable, .intLe, .intAdd, .intDecLe]
  | .intBmod => [.nat, .int, .eq, .ifThenElse, .intLe, .intAdd, .intSub, .intEdiv, .intEmod, .intDecLt]
  | .intBdiv => [.nat, .int, .eq, .ifThenElse, .intLe, .intAdd, .intEdiv, .intEmod, .intDecLt,
      .natDecEq]
  | .charUtf8Size => [.nat, .char, .charOfNat, .bool, .eq, .natMul, .natBle]
  | .stringUtf8ByteSize => [.nat, .string, .list, .char, .stringOfList, .eq, .natAdd, .charUtf8Size]
  | .stringBack => [.nat, .string, .list, .char, .charOfNat, .stringOfList, .eq, .natMul]
  | _ => []

/-- **The version of the specification set.** It changes exactly when
`Role`, `Role.spec`, `Role.block`, `Role.deps` or `Role.usedImplicitly` change,
together with the specification digest (`Ix.SpecDigest.specDigest`), which the
root library freezes (`Ix/SpecDigest.lean`). Version 2 (2026-10-20, `ALPHA-COLLAPSE.md` §8.2):
the five compiler-trust roles (`Lean.trustCompiler`, `Lean.reduceBool`,
`Lean.reduceNat`, `Lean.ofReduceBool`, `Lean.ofReduceNat`) and the `identity`
specification kind are gone; the certified theory is Lean with its three
standard axioms. Version 3 specifies the standard axioms' families `Iff` and
`Nonempty` as blocks, gives the inert `sorryAx` its type over `Bool`, and adds
the definitions IxVM evaluates natively
(`ite`; the `Nat`, `Int` and `String` decision procedures; the `Int` operations
with `Int.bmod` and `Int.bdiv`; `BitVec.toNat` and `BitVec.ult`; and `String.append`,
`String.toByteArray`, `String.utf8ByteSize` with `Char.utf8Size`, and `String.back`)
are roles, specified by their equations (`Spec.eqns`), with the anchors those
equations need; and each role records whether the checker uses
it implicitly (`Role.usedImplicitly`). -/
def specVersion : Nat := 3

/-- **The roles the checker uses implicitly**: those it introduces into a term
with no referenced constant that determines them. They are the literals' types
and constructor forms (`Nat`, `Nat.zero`, `Nat.succ`; a string literal's expansion
over `String.ofList`, `List`, `List.nil`, `List.cons`, `Char` and `Char.ofNat`,
with `String`) and the standard axioms recognized through the binding (`propext`,
`Classical.choice`). Every other role enters a term only through a native rule
that fires on a referenced head bound to a validated role, whose equations cover
the rule's result, so the result is that head's definitional unfolding under
any binding. These roles are what a claim proved under one binding must share
with another binding to discharge its assumptions (the literal class). -/
def Role.usedImplicitly : Role → Bool
  | .nat | .natZero | .natSucc | .string | .stringOfList | .list | .listNil | .listCons
  | .char | .charOfNat | .propext | .choice => Bool.true
  | _ => Bool.false

/-! ## The evidence of an operation, as the fold reads it -/

/-- The operation role at a key (the certified `Nat` operations). -/
def opRole? (c : Key md) : Option Role :=
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
def evidenceDefeqOk (ev : Evidences md) (c : Key md) : Bool :=
  match opRole? c with
  | some r =>
    let es := ev.of r
    es.length == (natOpEquations 0 c).length && es.all (·.isDefeqKind true)
  | none => false

/-- **A well-founded operation's proof terms**: one `.proof` entry per
certificate statement (`divModCertStmts`), their proof terms in order; `none`
when the evidence has another shape. -/
def evidenceProofs (ev : Evidences md) (c : Key md) : Option (List (Expr md)) :=
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
closure condition: every constant of a
proof, after the operation's self-references are replaced by its value, lies
in the dependency closure of that value and of the operation's dependencies'
roles (`Role.deps`, with their blocks). The validation then reads only the
operation's own dependency closure (LOCALITY), and the fast path the evidence
justifies stays out of the evidence's own check.

The closure follows a stored constant's type, its value (a definition's, a
theorem's stored one), its recursor rules (their constructors and right-hand
sides) and its projection table (`ConstantInfo.refExprs`, `refKeys`); a
literal references the constants its unfolding names, as `Expr.constsResolve`
reads it. The condition only ever refuses: nothing in the model reads it. The
walks visit keys in the terms' order, never a hash order (`constKeysGo`), so
the verdict does not depend on how keys hash. -/

/-- A bound on the walks below (they visit each key and subterm once; the
bound only makes them total). -/
def walkFuel : Nat := 1 <<< 40

/-- The keys a `Nat` literal references implicitly. -/
def litNatKeys : List (Key md) := [natName, natZeroName, natSuccName]

/-- The keys a `String` literal references implicitly. -/
def litStrKeys : List (Key md) :=
  litNatKeys ++ [stringName, stringOfListName, listName, listNilName, listConsName, charName,
    charOfNatName]

/-- The keys a walk has found: a set, for the membership test, and beside it
the same keys as a list, each once, newest first. -/
abbrev KeysAcc (md : Mode) := Std.HashSet (Key md) × List (Key md)

/-- A key the walk meets, kept once, at its first meeting. -/
def KeysAcc.add (acc : KeysAcc md) (k : Key md) : KeysAcc md :=
  if acc.1.contains k then acc else (acc.1.insert k, k :: acc.2)

/-- The keys the expressions of `todo` reference, added to `acc`: a walk over
their distinct subterms (`seen`), each visited once.

The keys are kept as a set and, beside it, as a list in the order the walk
first meets them, so that the closure walk below visits keys in the terms'
order and not in a set's hash order. The closure walk is bounded
(`walkFuel`), and where the bound is reached its result depends on the order
it visited keys in; a hash order is not preserved when the keys are renamed,
and the term order is, so with the list the condition's verdict is the same
for renamed inputs (the renaming lemma, step 7.3). Within the bound the
closure is the same set in either order, so no verdict changes. -/
def constKeysGo : Nat → List (Expr md) → Std.HashSet (Expr md) → KeysAcc md → KeysAcc md
  | 0, _, _, acc => acc
  | _, [], _, acc => acc
  | n + 1, e :: todo, seen, acc =>
    if seen.contains e then constKeysGo n todo seen acc
    else
      let seen := seen.insert e
      match e with
      | .const k _ => constKeysGo n todo seen (acc.add k)
      | .proj s _ x => constKeysGo n (x :: todo) seen (acc.add s)
      | .fvar _ t => constKeysGo n (t :: todo) seen acc
      | .app f a => constKeysGo n (f :: a :: todo) seen acc
      | .lam t b _ => constKeysGo n (t :: b :: todo) seen acc
      | .forallE t b _ => constKeysGo n (t :: b :: todo) seen acc
      | .letE t v b _ => constKeysGo n (t :: v :: b :: todo) seen acc
      | .lit (.natVal _) => constKeysGo n todo seen (litNatKeys.foldl KeysAcc.add acc)
      | .lit (.strVal _) => constKeysGo n todo seen (litStrKeys.foldl KeysAcc.add acc)
      | _ => constKeysGo n todo seen acc

/-- The keys an expression references. -/
def Expr.constKeys (e : Expr md) : Std.HashSet (Key md) := (constKeysGo walkFuel [e] {} ({}, [])).1

/-- The keys expressions reference, each once, in the order the walk first
meets them. -/
def constKeysOf (es : List (Expr md)) : List (Key md) :=
  (constKeysGo walkFuel es {} ({}, [])).2.reverse

/-- The keys an expression references, each once, in the order the walk first
meets them (`Expr.constKeys`, as a list in the term's order). -/
def Expr.constKeyList (e : Expr md) : List (Key md) := constKeysOf [e]

/-- The expressions of a stored constant the closure follows. -/
def ConstantInfo.refExprs : ConstantInfo md → List (Expr md)
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
def ConstantInfo.refKeys : ConstantInfo md → List (Key md)
  | .indInfo _ caps => caps.etaCtor.toList
  | .recInfo _ _ _ rules => rules.map (·.ctor)
  | .projInfo tbl => [tbl.structName, tbl.ctor]
  | _ => []

/-- The keys reachable from `todo` through the constants `look` finds. -/
def refClosureGo (look : Key md → Option (ConstantInfo md)) :
    Nat → List (Key md) → Std.HashSet (Key md) → Std.HashSet (Key md)
  | 0, _, seen => seen
  | _, [], seen => seen
  | n + 1, k :: todo, seen =>
    if seen.contains k then refClosureGo look n todo seen
    else
      let seen := seen.insert k
      match look k with
      | none => refClosureGo look n todo seen
      | some ci => refClosureGo look n (ci.refKeys ++ constKeysOf ci.refExprs ++ todo) seen

/-- The roots of an operation's evidence closure besides its value: its
dependencies' roles, with their blocks. -/
def evidenceDepKeys (c : Key md) : List (Key md) :=
  match opRole? c with
  | some r => (r.deps.flatMap Role.block).map roleKey
  | none => []

/-- **The evidence closure condition** for operation `c` with annotated value
`annVal`: every constant of every proof, with `c`'s self-references replaced
by `annVal`, is in the dependency closure of `annVal` and of `c`'s
dependencies (`evidenceDepKeys`), through `look`. -/
def evidenceLocal (look : Key md → Option (ConstantInfo md)) (c : Key md) (annVal : Expr md)
    (proofs : List (Expr md)) : Bool :=
  let cl := refClosureGo look walkFuel (annVal.constKeyList ++ evidenceDepKeys c) {}
  proofs.all fun p => (Expr.substConstAll c annVal p).constKeyList.all cl.contains

/-! ## Facts -/

theorem Role.spec_nat : (Role.spec (md := md)) .nat = .block (BasisKind.decls .natK) := rfl
theorem Role.spec_eq : (Role.spec (md := md)) .eq = .block (BasisKind.decls .eqK) := rfl
theorem Role.spec_punit : (Role.spec (md := md)) .punit = .block (BasisKind.decls .punitK) := rfl
theorem Role.spec_empty : (Role.spec (md := md)) .empty = .block (BasisKind.decls .emptyK) := rfl
theorem Role.spec_false : (Role.spec (md := md)) .false = .block (BasisKind.decls .falseK) := rfl
theorem Role.spec_quot : (Role.spec (md := md)) .quot = .block (BasisKind.decls .quotK) := rfl
theorem Role.spec_propext : (Role.spec (md := md)) .propext = .axiom 0 (some propextRaw.type) := rfl
theorem Role.spec_choice : (Role.spec (md := md)) .choice = .axiom 1 (some choiceRaw.type) := rfl
theorem Role.spec_iff : (Role.spec (md := md)) .iff = .block iffFamily := rfl
theorem Role.spec_nonempty : (Role.spec (md := md)) .nonempty = .block nonemptyFamily := rfl
theorem Role.spec_sorryAx : (Role.spec (md := md)) .sorryAx = .axiom 1 (some sorryAxSpecTy) := rfl

/-- **No standard axiom is specified over an anchor**: the roles the types of
`propext`, `Classical.choice` and `Quot.sound` mention are `block` roles, and
so are the roles those blocks mention, which mention no others. -/
theorem Role.stdAxiom_deps_blocks :
    [Role.propext, .choice, .quotSound].all (fun r => r.deps.all fun s =>
      ((Role.spec (md := md)) s).kind == .block &&
        s.deps.all fun t => ((Role.spec (md := md)) t).kind == .block && t.deps.isEmpty) =
      Bool.true := by
  cases md <;> decide

/-- Every role's block contains it. -/
theorem Role.mem_block (r : Role) : r ∈ r.block := by cases r <;> decide

/-- A block's members have the block's members as their block. -/
theorem Role.block_block (r : Role) : ∀ s ∈ r.block, s.block = r.block := by
  cases r <;> decide

/-- The operations, and only they, take evidence: one entry per equation, a
definitional one exactly for an unconditional equation. -/
theorem Role.evidenceKinds_natAdd :
    ((Role.spec (md := md)) .natAdd).evidenceKinds = [Bool.true, Bool.true] := by (cases md <;> decide)

theorem Role.evidenceKinds_natDiv :
    ((Role.spec (md := md)) .natDiv).evidenceKinds = [Bool.false, Bool.false, Bool.false] := by (cases md <;> decide)

/-- Every operation role is found at its key. -/
theorem opRole?_roleKey (r : Role)
    (h : ((Role.spec (md := md)) r).kind = .ops) : (opRole? (md := md)) (roleKey r) = some r := by
  cases r <;> first | rfl | (exact absurd h (by (cases md <;> decide)))

/-- The certificate statements are the `ops` specifications' equations: the
spec's sides rebuild each statement. -/
theorem divModSpec_stmts (c : Key md)
    (hc : c ∈ [natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
      natShiftLeftName, natShiftRightName]) :
    (match divModSpec c with
     | .ops _ eqs => eqs.map fun (hs, l, r) => (hs, eqNatOf l r)
     | _ => []) = divModCertStmts c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (cases md <;> decide)
/-! ## The anchors validated at install (owner, 2026-10-15)

`Bool.rec`, `And`, `And.intro` and `And.rec` have `anchor` specifications
that no use site validates (`Bool.rec` has no use site; the `And` rescue
relies on `And`'s projection table and on proof irrelevance at use,
`andRescueSlots`). The fold's step validates them when it installs them
(`Cached.annotDeclStep`): a constant bound to one of them must have its
specification's type up to binder data and level-parameter names
(`ConstantVal.matchesPin`, as the standard axioms' families are matched,
`stdAxiomOkF`), or the declaration declines.

The inert `sorryAx` is validated the same way: it installs nothing and every
use of it declines, so no use site reads it, but a constant bound to it must
have its specification's type, or a table could make any one axiom (`axiom
evil : False`) the tolerated declaration. -/

/-- The roles whose constants the fold's step matches against their
specifications at install. -/
def installAnchors : List Role := [.boolRec, .and, .andIntro, .andRec, .sorryAx]

/-- **The pin of an anchor validated at install**: the role's key, its
specification's level count (positional) and type. Spelled out rather than
read from `Role.spec`, so that the fold's code reaches these terms and not
the whole specification set; `installAnchorPin?_role` relates the two. -/
def installAnchorPin? : Key md → Option (ConstantVal md)
  | .role .boolRec => some { name := .role .boolRec, levelParams := [0], type := boolRecSpecTy }
  | .role .and => some { name := .role .and, levelParams := [], type := andSpecTy }
  | .role .andIntro => some { name := .role .andIntro, levelParams := [], type := andIntroSpecTy }
  | .role .andRec => some { name := .role .andRec, levelParams := [0], type := andRecSpecTy }
  | .role .sorryAx =>
    some { name := .role .sorryAx, levelParams := [0], type := sorryAxSpecTy }
  | _ => none

/-- The pins are the specifications: at a role of `installAnchors` the pin is
the role's `anchor` or typed `axiom` specification (its level count
positional, its type); at any other role there is none. -/
theorem installAnchorPin?_role (r : Role) :
    (installAnchorPin? (md := md) (.role r)) =
      if r ∈ installAnchors then
        match (Role.spec (md := md)) r with
        | .anchor n ty | .axiom n (some ty) =>
          some { name := .role r, levelParams := List.range n, type := ty }
        | _ => none
      else none := by
  cases r <;> rfl

/-- A constant's key, when it is bound to an anchor validated at install and
its type is not the specification's (`ConstantVal.matchesPin`). -/
def anchorMismatch? (cv : ConstantVal md) : Option (Key md) :=
  match installAnchorPin? cv.name with
  | some pin => if cv.matchesPin pin then none else some cv.name
  | none => none

/-- **The first constant a declaration declares whose anchor does not
match**, if any (`anchorMismatch?`). -/
def Declaration.anchorMismatch? : Declaration md → Option (Key md)
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv =>
    Ix.Kernel.anchorMismatch? cv
  | .indDecl block _ => block.findSome? (Ix.Kernel.anchorMismatch? ·.toConstantVal)
  | .basisDecl _ => none

end Ix.Kernel
