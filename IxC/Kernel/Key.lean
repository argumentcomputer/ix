module

public import IxC.Kernel.Name
public import IxC.Address.Core
/- `withPtrEq` is `public` but not `@[expose]`, and its whole point here
is that it is *definitionally* `k ()`, which is what `Key.beqPtr_eq`
proves. `import all` makes that body visible **in this module only**, as in
`IxC/Kernel/Name.lean`; the executed `Key.beq` stays the plain
`decide (· = ·)` that the kernel can still reduce. -/
import all Init.Util

@[expose] public section

/-!
# Constant keys

What the checker knows a constant by, and the two vocabularies in which it
names constants itself:

* `Key`, the identity of a constant: an input constant's identifier
  (`Key.id`: Lean's own name in Source mode, the address its references use
  in the Ixon modes), a constant bound to a role
  (`Key.role`), or a constant the checker or the front ends' shared back half
  generates from another key (`Key.aux`);
* `Role`, the closed set of constants the checker names (the basis blocks,
  the standard and trust axioms, the literal support, the certified `Nat`
  operations), each at `roleKey r = .role r`;
* `Derived`, the shapes of the generated constants, each at
  `auxKey k d = .aux k d`.

Every fabrication of a role or derived key goes through `roleKey` and
`auxKey`, and every inspection of a derived shape (`Key.isModelSuffix`,
`Key.isProjFnShape`, `Key.isProjIota`) is a test of `Key.aux`'s shape. An
input is always `.id` or `.role`, never `.aux`: the front ends make no
derived keys, so no input name can collide with, or be refused for, a
generated shape.

Proofs reason about keys through the lemmas here, which are constructor
injectivity and disjointness: `auxKey` is injective in its base and shape
together (`auxKey_inj₂`); a derived key differs from its base
(`auxKey_ne_self`), from every role key (`auxKey_ne_roleKey`) and from every
input key (`auxKey_ne_id`); `roleKey` is injective (`roleKey_inj`), so a
`decide` between role keys is a `decide` between roles.

**Rendering.** `Key.toName` spells a key for display, each mode its own way:
an input key as its id (`Mode.idName`: an address as `#` and its first twelve
hexadecimal digits, a name as itself), `.role r` as `r.leanName`, and
`.aux k d` as `k`'s spelling with `d`'s suffix (`Derived.spell`). `ToString`
and `Repr` print that name. The checker never reads a key's spelling; the
front ends read it for their name maps only.
-/

namespace Ix.Kernel

/-! ## Roles -/

/-- The constants the checker names: the pinned basis blocks and their
recursors, the standard and trust axioms with the families they quantify
over, the literal support and the certified `Nat` operations. Closed: a
constant outside it is an input or a derived key. `ofReduceBoolAx` and
`ofReduceNatAx` are `Lean.ofReduceBool` and `Lean.ofReduceNat`: the trust-surface
fence (`Tests/Ix/Kernel/TrustSurface.lean`) reserves the bare words for uses
of those axioms. -/
inductive Role where
  | nat | natZero | natSucc | natRec | bool | boolFalse | boolTrue | boolRec
  | eq | eqRefl | eqRec | punit | punitUnit | punitRec | empty | emptyRec | false | falseRec
  | true | trueIntro | and | andIntro | andRec | iff | iffIntro | iffRec
  | nonempty | nonemptyIntro | nonemptyRec | list | listNil | listCons
  | quot | quotMk | quotLift | quotInd | quotSound
  | string | stringOfList | char | charOfNat
  | natPred | natAdd | natSub | natMul | natPow | natBeq | natBle
  | natDiv | natMod | natGcd | natLand | natLor | natXor | natShiftLeft | natShiftRight
  | propext | choice | sorryAx
  | trustCompiler | reduceBool | reduceNat | ofReduceBoolAx | ofReduceNatAx
  deriving DecidableEq, Hashable, Ord, Repr, Inhabited

namespace Role

/-- A top-level Lean name. -/
@[inline] def topName (s : String) : Name := .str .anonymous s

/-- A two-component Lean name. -/
@[inline] def subName (a b : String) : Name := .str (.str .anonymous a) b

/-- The Lean name of a role's constant: Source mode's fixed binding, and the
role key's rendering. -/
@[inline] def leanName : Role → Name
  | .nat => topName "Nat"
  | .natZero => subName "Nat" "zero"
  | .natSucc => subName "Nat" "succ"
  | .natRec => subName "Nat" "rec"
  | .bool => topName "Bool"
  | .boolFalse => subName "Bool" "false"
  | .boolTrue => subName "Bool" "true"
  | .boolRec => subName "Bool" "rec"
  | .eq => topName "Eq"
  | .eqRefl => subName "Eq" "refl"
  | .eqRec => subName "Eq" "rec"
  | .punit => topName "PUnit"
  | .punitUnit => subName "PUnit" "unit"
  | .punitRec => subName "PUnit" "rec"
  | .empty => topName "Empty"
  | .emptyRec => subName "Empty" "rec"
  | .false => topName "False"
  | .falseRec => subName "False" "rec"
  | .true => topName "True"
  | .trueIntro => subName "True" "intro"
  | .and => topName "And"
  | .andIntro => subName "And" "intro"
  | .andRec => subName "And" "rec"
  | .iff => topName "Iff"
  | .iffIntro => subName "Iff" "intro"
  | .iffRec => subName "Iff" "rec"
  | .nonempty => topName "Nonempty"
  | .nonemptyIntro => subName "Nonempty" "intro"
  | .nonemptyRec => subName "Nonempty" "rec"
  | .list => topName "List"
  | .listNil => subName "List" "nil"
  | .listCons => subName "List" "cons"
  | .quot => topName "Quot"
  | .quotMk => subName "Quot" "mk"
  | .quotLift => subName "Quot" "lift"
  | .quotInd => subName "Quot" "ind"
  | .quotSound => subName "Quot" "sound"
  | .string => topName "String"
  | .stringOfList => subName "String" "ofList"
  | .char => topName "Char"
  | .charOfNat => subName "Char" "ofNat"
  | .natPred => subName "Nat" "pred"
  | .natAdd => subName "Nat" "add"
  | .natSub => subName "Nat" "sub"
  | .natMul => subName "Nat" "mul"
  | .natPow => subName "Nat" "pow"
  | .natBeq => subName "Nat" "beq"
  | .natBle => subName "Nat" "ble"
  | .natDiv => subName "Nat" "div"
  | .natMod => subName "Nat" "mod"
  | .natGcd => subName "Nat" "gcd"
  | .natLand => subName "Nat" "land"
  | .natLor => subName "Nat" "lor"
  | .natXor => subName "Nat" "xor"
  | .natShiftLeft => subName "Nat" "shiftLeft"
  | .natShiftRight => subName "Nat" "shiftRight"
  | .propext => topName "propext"
  | .choice => subName "Classical" "choice"
  | .sorryAx => topName "sorryAx"
  | .trustCompiler => subName "Lean" "trustCompiler"
  | .reduceBool => subName "Lean" "reduceBool"
  | .reduceNat => subName "Lean" "reduceNat"
  | .ofReduceBoolAx => subName "Lean" "ofReduceBool"
  | .ofReduceNatAx => subName "Lean" "ofReduceNat"

/-- Every role, in declaration order. -/
def all : List Role :=
  [.nat, .natZero, .natSucc, .natRec, .bool, .boolFalse, .boolTrue, .boolRec,
   .eq, .eqRefl, .eqRec, .punit, .punitUnit, .punitRec, .empty, .emptyRec, .false, .falseRec,
   .true, .trueIntro, .and, .andIntro, .andRec, .iff, .iffIntro, .iffRec,
   .nonempty, .nonemptyIntro, .nonemptyRec, .list, .listNil, .listCons,
   .quot, .quotMk, .quotLift, .quotInd, .quotSound, .string, .stringOfList, .char, .charOfNat,
   .natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq, .natBle,
   .natDiv, .natMod, .natGcd, .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight,
   .propext, .choice, .sorryAx,
   .trustCompiler, .reduceBool, .reduceNat, .ofReduceBoolAx, .ofReduceNatAx]

theorem mem_all (r : Role) : r ∈ all := by cases r <;> decide

/-- The role whose Lean name is `n`, if any. -/
def ofLeanName? (n : Name) : Option Role := all.find? (decide <| ·.leanName = n)

theorem ofLeanName?_leanName (r : Role) : ofLeanName? r.leanName = some r := by
  cases r <;> decide

theorem leanName_inj {r s : Role} : r.leanName = s.leanName ↔ r = s := by
  constructor
  · intro h
    have h' := ofLeanName?_leanName r
    rw [h, ofLeanName?_leanName] at h'
    exact (Option.some.inj h').symm
  · intro h; rw [h]

/-- **The recursor of a basis inductive role**: the role of `T.rec` for the
inductive `T`, for the roles whose recursor is itself a role. -/
def recOf : Role → Option Role
  | .nat => some .natRec
  | .bool => some .boolRec
  | .eq => some .eqRec
  | .punit => some .punitRec
  | .empty => some .emptyRec
  | .false => some .falseRec
  | .and => some .andRec
  | .iff => some .iffRec
  | .nonempty => some .nonemptyRec
  | _ => none

/-- `recOf`, case by case. -/
theorem recOf_eq_some {r r' : Role} :
    r.recOf = some r' ↔
      (r = .nat ∧ r' = .natRec) ∨ (r = .bool ∧ r' = .boolRec) ∨ (r = .eq ∧ r' = .eqRec) ∨
      (r = .punit ∧ r' = .punitRec) ∨ (r = .empty ∧ r' = .emptyRec) ∨
      (r = .false ∧ r' = .falseRec) ∨ (r = .and ∧ r' = .andRec) ∨
      (r = .iff ∧ r' = .iffRec) ∨ (r = .nonempty ∧ r' = .nonemptyRec) := by
  cases r <;> simp [recOf, eq_comm]

end Role

/-! ## Derived shapes -/

/-- **The shapes of generated constants.** At a base key `k`:
* `model`: the model companion of a block member, constructor or recursor;
  `impl` (under `model`): the modeller's namespace, never declared;
* `tag`, `auxFamily` (under `impl`): the tag family and the auxiliary family;
  `member k` (under either): its constructor for member `k`; `ctor j` (under
  the auxiliary family's `member k`): its constructor for member `k`'s
  constructor `j`; `recursor`: their recursors;
* `iota j` (under a recursor's `model`): the iota theorem of rule `j`;
  `eta`, `unitlike` (under `model`): the capability theorems;
* `projModel i` (under `model`): field `i`'s model projection; `projIota`
  (under it): its constructor-reduction theorem;
* `projFn i`: field `i`'s installed projection function; `projTable`: the
  structure's projection table;
* `pack j`, `unpack j`, `unpackPack j`, `packUnpack j`, `congrPack j`,
  `unpackAll`, `packUnpackAll`, `implRec` (under `impl`): the nested
  modeller's transport definitions.

An input recursor (`T.rec`, `T.rec_j`) is never derived: it is an input key. -/
inductive Derived where
  | model | impl | tag | auxFamily | member (k : Nat) | ctor (j : Nat) | recursor
  | iota (j : Nat) | eta | unitlike | projModel (i : Nat) | projIota
  | projFn (i : Nat) | projTable
  | pack (j : Nat) | unpack (j : Nat) | unpackPack (j : Nat) | packUnpack (j : Nat)
  | congrPack (j : Nat) | unpackAll | packUnpackAll | implRec
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- `s` followed by the decimal digits of `j`. -/
def indexedStr (s : String) (j : Nat) : String := s ++ toString j

/-- **The spelling of shape `d` at a base spelled `n`**: the name the
generated constant had while keys were names. Display only (`Key.toName`). -/
def Derived.spell (n : Name) : Derived → Name
  | .model => n.str "_model"
  | .impl => n.str "_impl"
  | .tag => n.str "tag"
  | .auxFamily => n.str "aux"
  | .member i => n.num i
  | .ctor j => n.str (indexedStr "ctor_" j)
  | .recursor => n.str "rec"
  | .iota j => n.str (indexedStr "iota_" j)
  | .eta => n.str "eta"
  | .unitlike => n.str "unitlike"
  | .projModel i => n.str (indexedStr "proj_" i)
  | .projIota => n.str "iota"
  | .projFn i => (n.str "proj").num i
  | .projTable => (n.str "projTable").num 0
  | .pack j => n.str (indexedStr "pack_" j)
  | .unpack j => n.str (indexedStr "unpack_" j)
  | .unpackPack j => n.str (indexedStr "unpackPack_" j)
  | .packUnpack j => n.str (indexedStr "packUnpack_" j)
  | .congrPack j => n.str (indexedStr "congrPack_" j)
  | .unpackAll => n.str "unpack"
  | .packUnpackAll => n.str "packUnpack"
  | .implRec => n.str "rec"

/-! ## Modes -/

/-- **The checker's modes** (IXC-PLAN §3): what identifies an input constant,
and what display data a term carries.
* `anon`: Ixon, anonymous: identity by address, no names;
* `meta`: Ixon with its metadata: identity by address, names for display;
* `source`: Lean through `CanonM`, unhashed: identity by Lean name.

The checker is generic in the mode. Its theorems hold in every mode while no
term carries display data (`Mode.D` is used from step 6 on); they are stated
at `.anon` (the Ixon entry) and `.source` (the Lean ingress). -/
inductive Mode where
  | anon | «meta» | source
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Mode

/-- What identifies an input constant: its address in the Ixon modes (the
address in a record's `refs` table: a singleton's own, a block member's
projection record's), its name in Source mode. -/
@[reducible] def Id : Mode → Type
  | .anon | .meta => Address
  | .source => Name

/-- Display data: present only in `.meta`, and never read by the checker. -/
@[reducible] def D : Mode → Type → Type
  | .meta, α => α
  | .anon, _ | .source, _ => Unit

/-- The modes the theorems are stated at: no display data. -/
class Certified (md : Mode) : Prop where
  noDisplay : ∀ α, md.D α = Unit

instance : Certified .anon := ⟨fun _ => rfl⟩
instance : Certified .source := ⟨fun _ => rfl⟩

/-- Input ids compare as addresses or as names. -/
def decEqId : (md : Mode) → DecidableEq md.Id
  | .anon | .meta => inferInstanceAs (DecidableEq Address)
  | .source => inferInstanceAs (DecidableEq Name)

instance {md : Mode} : DecidableEq md.Id := decEqId md

/-- An input id's share of its key's hash: an address's leading eight bytes
(`Hashable Address`), a name's cached hash. -/
def idHash : {md : Mode} → md.Id → UInt64
  | .anon, a | .meta, a => hash a
  | .source, n => n.hashData

/-- An input id for display: an address as its first twelve hexadecimal
digits after `#`, a name as itself. -/
def idName : {md : Mode} → md.Id → Name
  | .anon, a | .meta, a => .str .anonymous ("#" ++ (hexOfBytes a.hash).take 12)
  | .source, n => n

/-- The id an Ixon address gives an input constant: the address itself in the
modes keyed by address; none in Source mode (its ids are names, and its one
reading of Ixon records, the prelude's, names every constant by its role). -/
def addressId? : (md : Mode) → Address → Option md.Id
  | .anon, a | .meta, a => some a
  | .source, _ => none

end Mode

/-! ## Keys -/

/-- **What identifies a constant.**
* `id i`: an input constant, by its identifier (`md.Id`);
* `role r`: the constant bound to role `r` (the front ends rename a bound
  constant to its role);
* `aux k d`: the constant of shape `d` that the checker or the front ends'
  shared back half generates from `k`. No input is ever `aux`. -/
inductive Key (md : Mode) where
  | id (i : md.Id)
  | role (r : Role)
  | aux (base : Key md) (d : Derived)
with
  /-- The cached hash of a key: an input key's is its id's
  (`Mode.idHash`), a role key and a derived key mix their role's or shape's
  hash. -/
  @[computed_field] hashData : (md : Mode) → Key md → UInt64
    | _, .id i => Mode.idHash i
    | _, .role r => mixHash 1741 (hash r)
    | _, .aux k d => mixHash k.hashData (hash d)
deriving DecidableEq

instance : Inhabited (Key md) := ⟨.role default⟩

/-- Hashing a key is an `O(1)` field read. -/
instance : Hashable (Key md) := ⟨Key.hashData md⟩

/-- Key equality in `Name`'s shape: **pointer**, then the **cached hash**,
then the structural comparison. The implementation of `Key.beq`;
`Key.beqPtr_eq` proves both guards redundant. -/
@[inline] def Key.beqPtr (a b : Key md) : Bool :=
  withPtrEq a b (fun _ => a.hashData == b.hashData && decide (a = b))
    (fun h => by subst h; simp)

/-- Both guards are redundant: `withPtrEq a b k h` is *defined* as `k ()`,
and `hashData` is a function of the value. -/
theorem Key.beqPtr_eq (a b : Key md) : Key.beqPtr a b = decide (a = b) := by
  show (a.hashData == b.hashData && decide (a = b)) = decide (a = b)
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- The executed key equality: definitionally `decide (a = b)`, so the
kernel, `by decide` and `#guard` see structural equality, with `beqPtr`
substituted by the compiler on the `@[csimp]` equation below (as
`Name.beq_eq_beqPtr`). -/
def Key.beq (a b : Key md) : Bool := decide (a = b)

/-- The `Key` twin of `Name.beq_eq_beqPtr`: `@[csimp]`, not
`@[implemented_by]`, on a kernel-checked equality. -/
@[csimp] theorem Key.beq_eq_beqPtr : @Key.beq = @Key.beqPtr := by
  funext md a b; exact (Key.beqPtr_eq a b).symm

instance : BEq (Key md) := ⟨Key.beq⟩

/-- `Key.beq` is lawful: it *is* `decide (· = ·)`. -/
instance : LawfulBEq (Key md) where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Key.beq]

/-! ## Renaming -/

/-- **A renaming of input keys** (IXC-PLAN §12): `.id i` becomes `.id (f i)`, a
role key is fixed, and a derived key is renamed through its base. The bridge
from Source to Ixon renames by `Key.map f` with `f` a Lean name's compiled
address (`Ix.Cert.RenamingLemma`). -/
def Key.map {md md' : Mode} (f : md.Id → md'.Id) : Key md → Key md'
  | .id i => .id (f i)
  | .role r => .role r
  | .aux k d => .aux (k.map f) d

/-! ## Rendering -/

/-- **A key's spelling**: an input key's id as `Mode.idName` shows it,
`.role r` as `r.leanName`, `.aux k d` as `k`'s spelling with `d`'s suffix. For
messages, rows and the front ends' name maps only. -/
def Key.toName : Key md → Name
  | .id i => Mode.idName i
  | .role r => r.leanName
  | .aux k d => d.spell k.toName

instance : ToString (Key md) := ⟨fun k => k.toName.toString⟩

/-- A key prints as its spelling's `Repr`. -/
instance : Repr (Key md) := ⟨fun k prec => reprPrec k.toName prec⟩

/-! ## Source mode's naming -/

/-- The roles by their Lean names. -/
def Role.byLeanName : Std.HashMap Name Role :=
  all.foldl (fun m r => m.insert r.leanName r) {}

/-- **The key of the constant Lean names `n`**, under Source mode's fixed
binding: the role whose Lean name `n` is, otherwise the input key `n`. For
the front ends and their tests; the checker never reads a key's name. -/
def Key.ofName (n : Name) : Key .source :=
  match Role.byLeanName[n]? with
  | some r => .role r
  | none => .id n

/-! ## Role and derived keys -/

/-- **The key of a role's constant.** -/
@[reducible, inline] def roleKey (r : Role) : Key md := .role r

/-- **The key of a generated constant**: shape `d` at base `k`. -/
@[inline] def auxKey (k : Key md) (d : Derived) : Key md := .aux k d

/-- Role keys are distinct exactly when their roles are. -/
@[simp] theorem roleKey_inj {r s : Role} : (roleKey r : Key md) = roleKey s ↔ r = s := by
  simp [roleKey]

theorem roleKey_ne {r s : Role} (h : r ≠ s) : (roleKey r : Key md) ≠ roleKey s :=
  fun e => h (roleKey_inj.mp e)

/-- A role key is not an input key. -/
@[simp] theorem roleKey_ne_id (r : Role) (n : md.Id) : (roleKey r : Key md) ≠ .id n := nofun

/-- A derived key is larger than its base. -/
theorem sizeOf_lt_auxKey (k : Key md) (d : Derived) : sizeOf k < sizeOf (auxKey k d) := by
  simp [auxKey]; omega

/-- A derived key is not its base. -/
theorem auxKey_ne_self (k : Key md) (d : Derived) : auxKey k d ≠ k := fun h =>
  absurd (h ▸ sizeOf_lt_auxKey k d) (Nat.lt_irrefl _)

/-- A key derived twice is not its base. -/
theorem auxKey_auxKey_ne_self (k : Key md) (d d' : Derived) : auxKey (auxKey k d) d' ≠ k :=
  fun h => absurd (h ▸ Nat.lt_trans (sizeOf_lt_auxKey k d) (sizeOf_lt_auxKey _ d'))
    (Nat.lt_irrefl _)

/-- **`auxKey` is injective in its base.** -/
@[simp] theorem auxKey_inj {k k' : Key md} {d : Derived} : auxKey k d = auxKey k' d ↔ k = k' := by
  simp [auxKey]

/-- **`auxKey` is injective in its base and its shape together.** -/
theorem auxKey_inj₂ {k k' : Key md} {d d' : Derived} (h : auxKey k d = auxKey k' d') :
    k = k' ∧ d = d' := by
  simpa [auxKey] using h

/-- **Distinct shapes at one base are distinct keys.** -/
theorem auxKey_derived_eq {k : Key md} {d d' : Derived} (h : auxKey k d = auxKey k d') : d = d' :=
  (auxKey_inj₂ h).2

/-- **Different shapes are different keys**, at any bases. -/
theorem auxKey_ne_auxKey {k k' : Key md} {d d' : Derived} (hne : d ≠ d') :
    auxKey k d ≠ auxKey k' d' := fun h => hne (auxKey_inj₂ h).2

/-- The shapes whose spelling ends in a number: a member's constructor, a
projection function, a projection table. -/
def Derived.endsNum : Derived → Bool
  | .member _ | .projFn _ | .projTable => true
  | _ => false

/-- **Shapes of different ends are different keys**, at any bases. -/
theorem auxKey_ne_of_endsNum {k k' : Key md} {d d' : Derived} (h : d.endsNum ≠ d'.endsNum) :
    auxKey k d ≠ auxKey k' d' :=
  auxKey_ne_auxKey fun e => h (e ▸ rfl)

/-- **A derived key is not a role key.** -/
@[simp] theorem auxKey_ne_roleKey (k : Key md) (d : Derived) (r : Role) : auxKey k d ≠ roleKey r :=
  nofun

/-- **A derived key is not an input key.** -/
@[simp] theorem auxKey_ne_id (k : Key md) (d : Derived) (n : md.Id) : auxKey k d ≠ .id n := nofun

/-! ## Views of derived shapes

The inspections of a key's shape, each a test of `Key.aux`'s constructor. No
input key (`.id`, `.role`) has a derived shape. -/

namespace Key

/-- Is `k` a model companion, `auxKey _ .model`? -/
def isModelSuffix : Key md → Bool
  | .aux _ .model => true
  | _ => false

/-- Is `k` an installed projection function `auxKey _ (.projFn i)` or a
projection table `auxKey _ .projTable`? Both shapes are reserved for the
checker's own installs. -/
def isProjFnShape : Key md → Bool
  | .aux _ (.projFn _) => true
  | .aux _ .projTable => true
  | _ => false

/-- Is `k` a projection's constructor-reduction theorem, `auxKey _ .projIota`? -/
def isProjIota : Key md → Bool
  | .aux _ .projIota => true
  | _ => false

@[simp] theorem isModelSuffix_id (n : md.Id) : (Key.id (md := md) n).isModelSuffix = false := rfl
@[simp] theorem isModelSuffix_role (r : Role) : (Key.role (md := md) r).isModelSuffix = false := rfl
@[simp] theorem isProjFnShape_id (n : md.Id) : (Key.id (md := md) n).isProjFnShape = false := rfl
@[simp] theorem isProjFnShape_role (r : Role) : (Key.role (md := md) r).isProjFnShape = false := rfl

end Key

theorem isModelSuffix_iff {k : Key md} : k.isModelSuffix = true ↔ ∃ b, k = auxKey b .model := by
  constructor
  · intro h
    match k, h with
    | .aux b .model, _ => exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩; rfl

theorem isModelSuffix_auxKey (k : Key md) (d : Derived) :
    (auxKey k d).isModelSuffix = (d == .model) := by
  cases d <;> rfl

@[simp] theorem isProjFnShape_auxKey_projFn (k : Key md) (i : Nat) :
    (auxKey k (.projFn i)).isProjFnShape = true := rfl

@[simp] theorem isProjFnShape_auxKey_projTable (k : Key md) :
    (auxKey k .projTable).isProjFnShape = true := rfl

/-- A derived key has the projection shape exactly at the projection shapes. -/
theorem isProjFnShape_auxKey (k : Key md) (d : Derived) :
    (auxKey k d).isProjFnShape = (d matches .projFn _ | .projTable) := by
  cases d <;> rfl

theorem isProjIota_auxKey (k : Key md) (d : Derived) :
    (auxKey k d).isProjIota = (d == .projIota) := by
  cases d <;> rfl

/-- A model companion is not a key of another shape. -/
theorem auxKey_model_ne {n m : Key md} (hm : m.isModelSuffix = false) : auxKey n .model ≠ m := by
  intro h
  subst h
  exact absurd hm (by rw [isModelSuffix_auxKey]; decide)

/-- A projection function is not a key of another shape. -/
theorem auxKey_projFn_ne {T n : Key md} {j : Nat} (h : n.isProjFnShape = false) :
    auxKey T (.projFn j) ≠ n := by
  intro he
  subst he
  exact absurd h (by rw [isProjFnShape_auxKey_projFn]; decide)

end Ix.Kernel
