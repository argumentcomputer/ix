module

public import IxC.Kernel.Roles
public import IxC.Ixon.Codec
public import Ix.Address.Pure
public import Ix.SpecDigest.Schedule

@[expose] public section

/-! # The specification digest

The specification set (`Ix.Kernel.Role.spec`, `Role.block`, `Role.deps`,
`Role.usedImplicitly`, `specVersion`; `IxC/Kernel/Roles.lean`) is identified
by a digest: BLAKE3 (`Blake3.Pure.hash`) of its canonical encoding
(`specBytes`). The kernel admits no hasher
(`Ix.Kernel.Audit.kernelImportAllowlist`), so the digest is computed here, in
the root library. A claim commits to it beside the binding hash (the role
table's section hash, `Ix.Kernel.Admission.Binding`); the
`Ix.SpecDigest.Audit` freezes its value, so it changes only on purpose,
together with `specVersion` or `encodingVersion`.

## What the digest commits to

IxVM holds the digest as a literal (`KernelRoleSpec::spec_digest`) beside the
tables `IxVM.RoleSpecGen` renders from the specifications
(`IxVM/IxVM/Source/KernelRoleSpec.lean`). The renderer reads nothing but
`specBytes`, read back by `Committed.ofBytes` (`Ix/SpecDigest/Decode.lean`),
so every value those tables hold is a function of the bytes, a circuit that
validates roles in another way carries another digest, and `ix codegen
--check` fails when the rendered file and the digest drift apart. Beyond the
specifications, the encoding therefore holds what the circuit reads off a
role's identity, and the order it validates the roles in:

- each role's name (`Role.leanName`), so the index of every role the
  circuit names (`role_nat`, …) is fixed;
- whether the role is inert (`inert`: `sorryAx` and Lean's compiler-trust
  axioms, which the circuit validates as axioms no constant may use), its
  kind if it is a quotient primitive (`quotKind`), and the native rule IxVM
  fires on its constant (`nativeOp`);
- the validation schedule (`Schedule.current`): the groups in validation
  order, each as its roles, and the two boundaries the circuit validates them
  under (`Ix/SpecDigest/Schedule.lean`).

`specVersion` versions the specifications, which role tables are made for
(`RoleTable.version`); `encodingVersion` versions what this encoding adds to
them. Neither the schedule nor the per-role data above changes a role table.

## The encoding

Integers are TagN codes with no flag (`Ixon.putTagN 0`, `N0(n)` in
`docs/Ixon.md`), constructor tags single bytes. A key is a role's index in
`Role.all`: the specifications are closed over role keys, and the encoder
refuses any other key (`specBytes` fails), so the encoding checks the
closedness it relies on. Level parameters are positions; binder data are the
`PropWhen` datum and the two contracts' bits, a let's data its contract.
`specBytes` encodes the current schedule only once it is checked
(`Schedule.ofGroups`).

    specs     := N0(specVersion) N0(encodingVersion) N0(#roles) role* schedule
    role      := index name spec N0(#block) index* N0(#deps) index*
                 bool(implicit) bool(inert) N0(quotKind) N0(family) N0(op)
                                                             (in `Role.all` order)
    index     := N0(the role's index in `Role.all`)
    name      := N0(#parts) str*                             `Role.leanName`, outermost first
    str       := N0(#bytes) byte*                            UTF-8
    schedule  := N0(#groups) (N0(#roles) index*)* N0(firstWellFounded) N0(firstEquation)
    spec      := 00 N0(#decls) info*                         block
               | 01 N0(levels) expr                          anchor
               | 02 expr N0(#eqs) (N0(#hyps) expr* expr expr)*   ops
               | 03 N0(levels) (00 | 01 expr)                axiom (any type | typed)
               | 04 N0(levels) expr N0(#eqs) eqn*              eqns
    eqn       := N0(#vars) expr* N0(#hyps) expr* level expr expr expr
    info      := 00 val | 01 val expr hint | 02 val expr | 03 val caps
               | 04 val N0 N0 | 05 val N0 N0 N0(#rules) rule* | 06 table
    val       := key N0(#lps) N0* expr
    expr      := 00 N0 | 01 N0 expr | 02 level | 03 key N0(#us) level*
               | 04 expr expr | 05 expr expr binder | 06 expr expr binder
               | 07 expr expr expr let | 08 N0 | 09 str | 0A key N0 expr
    level     := 00 | 01 level | 02 level level | 03 level level | 04 N0
    binder    := pw contract result
    let       := bool(nonDep) (00 | 01)(value | borrowShared) contract
    pw        := 00 | 01 N0(#ps) N0*                          never | ifAllZero ps

`caps`, `rule`, `hint` and `table` spell their fields in declaration order
(`encInfo`). -/

namespace Ix.SpecDigest

open Ix.Kernel

/-- **The version of this encoding.** Version 1, which had no such field,
encoded the specifications alone. Version 2 adds this field, each role's
name, inertness, quotient kind and native rule, and the validation schedule. -/
def encodingVersion : Nat := 2

/-! ## What the circuit reads off a role's identity -/

/-- **The inert axioms** (`Role.inert`): `sorryAx` and Lean's compiler-trust
axioms (`Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`),
tolerated as declarations and never usable. IxVM validates each against its
type (`validate_inert_axiom`), refuses every constant that uses one
(`KernelRoles::assert_ref_allowed`) and refuses each as a claim's seed
(`KernelClaim::assert_claimable`). IxC's checker installs nothing for
`sorryAx` and declines any use of it; it declines the compiler-trust axioms'
declarations themselves. -/
def inert (r : Role) : Bool := r.inert

/-- **A quotient primitive's kind**, in Lean's `QuotKind` order: 1 the type,
2 the constructor, 3 the lift, 4 the induction principle; 0 for every other
role. The quotient basis block declares them as axioms
(`BasisKind.quotK`); the checker and IxVM reduce them by kind. -/
def quotKind : Role → Nat
  | .quot => 1
  | .quotMk => 2
  | .quotLift => 3
  | .quotInd => 4
  | _ => 0

/-- **The native rule IxVM fires on a role's constant**: its family (1 `Nat`
operations, 2 `String`, 3 `BitVec`, 5 decision procedures, 6 `Int`; 0 none)
and the operation's index within that family. The rule must compute what the
role's specification states; this table is IxVM's, and the digest commits to
it so that a circuit dispatching another way carries another digest. -/
def nativeOp : Role → Nat × Nat
  | .natSucc => (1, 1)
  | .natPred => (1, 2)
  | .natAdd => (1, 3)
  | .natSub => (1, 4)
  | .natMul => (1, 5)
  | .natDiv => (1, 6)
  | .natMod => (1, 7)
  | .natGcd => (1, 8)
  | .natPow => (1, 9)
  | .natLand => (1, 10)
  | .natLor => (1, 11)
  | .natXor => (1, 12)
  | .natShiftLeft => (1, 13)
  | .natShiftRight => (1, 14)
  | .natBeq => (1, 15)
  | .natBle => (1, 16)
  | .stringOfList => (2, 1)
  | .stringUtf8ByteSize => (2, 2)
  | .stringBack => (2, 3)
  | .stringToByteArray => (2, 4)
  | .stringDecEq => (2, 5)
  | .stringAppend => (2, 6)
  | .bitVecToNat => (3, 1)
  | .bitVecUlt => (3, 2)
  | .natDecLt => (5, 1)
  | .natDecLe => (5, 2)
  | .natDecEq => (5, 3)
  | .intDecLt => (5, 4)
  | .intDecLe => (5, 5)
  | .intDecEq => (5, 6)
  | .intNeg => (6, 1)
  | .intNatAbs => (6, 2)
  | .intBmod => (6, 3)
  | .intBdiv => (6, 4)
  | .intPow => (6, 5)
  | .intAdd => (6, 6)
  | .intSub => (6, 7)
  | .intMul => (6, 8)
  | .intEmod => (6, 9)
  | .intEdiv => (6, 10)
  | _ => (0, 0)

/-! ## The encoder -/

abbrev EncM := StateT ByteArray (Except String)

def byte (b : UInt8) : EncM Unit := modify (·.push b)

def nat (n : Nat) : EncM Unit := do
  if n ≥ 2 ^ 64 then throw s!"integer {n} out of range"
  let bytes := Ixon.runPut (Ixon.putTagN 0 0 n.toUInt64)
  modify (· ++ bytes)

def bool (b : Bool) : EncM Unit := byte (if b then 1 else 0)

def list {α : Type} (xs : List α) (f : α → EncM Unit) : EncM Unit := do
  nat xs.length
  for x in xs do f x

/-- A string, as its UTF-8 bytes. -/
def str (s : String) : EncM Unit := list s.toUTF8.toList byte

/-- A role, by its index in `Role.all`. -/
def index (r : Role) : EncM Unit := nat (Role.all.idxOf r)

/-- A name's components, outermost first. A role's name has only string
components. -/
def nameParts : Ix.Kernel.Name → Except String (List String)
  | .anonymous => pure []
  | .str p s => return (← nameParts p) ++ [s]
  | .num .. => throw "a role name with a numeric component"

/-- A role key, by the role's index; any other key is refused. -/
def key : Key md → EncM Unit
  | .role r => index r
  | k => throw s!"the specification mentions {k}, which is not a role key"

def level : Level → EncM Unit
  | .zero => byte 0
  | .succ u => do byte 1; level u
  | .max u v => do byte 2; level u; level v
  | .imax u v => do byte 3; level u; level v
  | .param i => do byte 4; nat i

def propWhen (pw : PropWhen) : EncM Unit :=
  match pw.toList? with
  | none => byte 0
  | some ps => do byte 1; list ps nat

def binder (m : BinderMeta) : EncM Unit := do
  propWhen m.pw
  byte m.contract.toBits
  byte m.result.toBits

def expr : Expr md → EncM Unit
  | .bvar i => do byte 0; nat i
  | .fvar i t => do byte 1; nat i; expr t
  | .sort u => do byte 2; level u
  | .const k us => do byte 3; key k; list us level
  | .app f a => do byte 4; expr f; expr a
  | .lam t b m => do byte 5; expr t; expr b; binder m
  | .forallE t b m => do byte 6; expr t; expr b; binder m
  | .letE t v b l => do
    byte 7; expr t; expr v; expr b
    bool l.contract.nonDep
    byte (match l.contract.kind with | .value => 0 | .borrowShared => 1)
    byte l.contract.binder.toBits
  | .lit (.natVal n) => do byte 8; nat n
  | .lit (.strVal s) => do byte 9; str s
  | .proj s i e => do byte 10; key s; nat i; expr e

def val (cv : ConstantVal md) : EncM Unit := do
  key cv.name
  list cv.levelParams nat
  expr cv.type

def hint : ReducibilityHint → EncM Unit
  | .opaque => byte 0
  | .abbrev => byte 1
  | .regular h => do byte 2; nat h

def caps (c : IndCaps md) : EncM Unit := do
  bool c.eta
  match c.etaCtor with
  | none => byte 0
  | some k => do byte 1; key k
  nat c.etaParams
  nat c.etaFields
  bool c.unitlike
  nat c.unitParams
  bool c.ruleK
  propWhen c.sortZ

def fire : RecRuleFire md → EncM Unit
  | .inert => byte 0
  | .plain => byte 1
  | .nested lvls pins => do byte 2; list lvls level; list pins expr

def rule (r : RecRule md) : EncM Unit := do
  key r.ctor
  nat r.nfields
  nat r.ctorParams
  fire r.fire
  expr r.rhs
  bool r.k
  bool r.eta
  bool r.paramsBlind

def encInfo : ConstantInfo md → EncM Unit
  | .axiomInfo cv => do byte 0; val cv
  | .defnInfo cv v h => do byte 1; val cv; expr v; hint h
  | .thmInfo cv v => do byte 2; val cv; expr v
  | .indInfo cv c => do byte 3; val cv; caps c
  | .ctorInfo cv nP nF => do byte 4; val cv; nat nP; nat nF
  | .recInfo cv m p rules => do byte 5; val cv; nat m; nat p; list rules rule
  | .projInfo _ => throw "a projection table in a specification"

def spec : Spec md → EncM Unit
  | .block decls => do byte 0; list decls encInfo
  | .anchor levels type => do byte 1; nat levels; expr type
  | .ops type eqs => do
    byte 2
    expr type
    list eqs fun (hyps, l, r) => do list hyps expr; expr l; expr r
  | .axiom levels type => do
    byte 3
    nat levels
    match type with
    | none => byte 0
    | some t => do byte 1; expr t
  | .eqns levels type eqs => do
    byte 4
    nat levels
    expr type
    list eqs fun e => do
      list e.vars expr; list e.hyps expr; level e.level; expr e.carrier; expr e.lhs; expr e.rhs

/-! ## The committed data -/

/-- **One role's row**: what the digest commits to about the role at index `i`
of `Role.all`. A decoded row (`Ix.SpecDigest.Decode`) holds `Role.all[j]` for
every index `j` it reads. -/
structure Row where
  /-- `Role.leanName`'s components, outermost first. -/
  name : List String
  spec : Spec .anon
  block : List Role
  deps : List Role
  implicit : Bool
  inert : Bool
  quotKind : Nat
  /-- The native rule's family and operation (`nativeOp`). -/
  native : Nat × Nat
  deriving Inhabited

/-- **What the digest commits to**: the two versions, every role's row in
`Role.all` order, and the validation schedule. `encode` writes it, and
`Committed.ofBytes` (`Ix/SpecDigest/Decode.lean`) reads it back. -/
structure Committed where
  specVersion : Nat
  encodingVersion : Nat
  rows : List Row
  schedule : Schedule
  deriving Inhabited

/-- Role `r`'s row, from IxC's specification set and the tables above. -/
def Row.ofRole (r : Role) : Except String Row := do
  return { name := ← nameParts r.leanName, spec := r.spec (md := .anon), block := r.block,
           deps := r.deps, implicit := r.usedImplicitly, inert := Ix.SpecDigest.inert r,
           quotKind := Ix.SpecDigest.quotKind r, native := Ix.SpecDigest.nativeOp r }

/-- The specification set, validated under the schedule `s`. -/
def Committed.withSchedule (s : Schedule) : Except String Committed := do
  return { specVersion := Ix.Kernel.specVersion, encodingVersion := Ix.SpecDigest.encodingVersion,
           rows := ← Role.all.mapM Row.ofRole, schedule := s }

/-- **The data the digest commits to today**: the specification set under the
current schedule (`Schedule.current`, checked). -/
def Committed.current : Except String Committed := do
  Committed.withSchedule (← Schedule.current)

/-! ## The bytes -/

/-- One role's row, at its index. -/
def row (i : Nat) (w : Row) : EncM Unit := do
  nat i
  list w.name str
  spec w.spec
  list w.block index
  list w.deps index
  bool w.implicit
  bool w.inert
  nat w.quotKind
  nat w.native.1
  nat w.native.2

/-- A validation schedule: each group as its roles, then the boundaries. -/
def schedule (s : Schedule) : EncM Unit := do
  list s.groups fun g => list g index
  nat s.firstWellFounded
  nat s.firstEquation

/-- **The canonical bytes of `c`.** -/
def encode (c : Committed) : Except String ByteArray := do
  let act : EncM Unit := do
    nat c.specVersion
    nat c.encodingVersion
    nat c.rows.length
    for (w, i) in c.rows.zipIdx do row i w
    schedule c.schedule
  let ((), bytes) ← act.run .empty
  pure bytes

/-- The canonical bytes of the specification set validated under `s`.
`specBytes` takes the current, checked schedule; any other schedule gives
other bytes. -/
def specBytesWith (s : Schedule) : Except String ByteArray := do
  encode (← Committed.withSchedule s)

/-- **The specification set's canonical bytes**: `Committed.current`,
encoded. -/
def specBytes : Except String ByteArray := do
  encode (← Committed.current)

/-- **The specification digest**: BLAKE3 of `specBytes`. -/
def specDigest : Except String Address := do
  pure (Address.blake3Pure (← specBytes))

end Ix.SpecDigest
