module

public import IxC.Kernel.Name
import Std.Data.String.ToNat

@[expose] public section

/-!
# Constant keys

What the checker knows a constant by, and the two vocabularies in which it
names constants itself:

* `Key`, the identity of a constant: Lean's own name in Source mode, the
  reader's `ix.<hex>` encoding of a record address in Ixon mode;
* `Role`, the closed set of constants the checker names (the basis blocks,
  the standard and trust axioms, the literal support, the certified `Nat`
  operations), each at `roleKey r`;
* `Derived`, the shapes of the constants the checker and the front ends'
  shared back half generate from another key `k`, each at `auxKey k d`.

`roleKey r` is `r`'s Lean name and `auxKey k d` is the spelling the
generated constant has always had, so keys, generated declarations and
verdicts are Lean's. Every fabrication of a role or derived key goes through
these two functions, and every inspection of a derived shape
(`Key.isModelSuffix`, `Key.isProjFnShape`, `Key.isProjIota`,
`Key.isRecSpelling`) is a view of `auxKey`'s spelling.

Proofs reason about keys through the lemmas here, not through `Name`'s
structure: `auxKey` is injective in its base (`auxKey_inj`) and, at one
derived shape, in its base and index together (`auxKey_inj₂`); two shapes at
one base differ (`auxKey_derived_eq`, with the one exception that the
modeller's `.implRec` and `.recursor` are both spelled `rec`); a derived key
differs from its base (`auxKey_ne_self`) and from every role key except a
recursor's (`auxKey_ne_roleKey`); `roleKey` is injective (`roleKey_inj`), so a
`decide` between role keys is a `decide` between roles.
-/

namespace Ix.Kernel

/-- What identifies a constant. -/
abbrev Key := Name

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

/-- The Lean name of a role's constant. -/
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

/-- The last components of the roles' Lean names. -/
def lastNames : List String :=
  ["Nat", "zero", "succ", "rec", "Bool", "false", "true", "Eq", "refl", "PUnit", "unit",
   "Empty", "False", "True", "intro", "And", "Iff", "Nonempty", "List", "nil", "cons",
   "Quot", "mk", "lift", "ind", "sound", "String", "ofList", "Char", "ofNat",
   "pred", "add", "sub", "mul", "pow", "beq", "ble", "div", "mod", "gcd", "land", "lor",
   "xor", "shiftLeft", "shiftRight", "propext", "choice", "sorryAx", "trustCompiler",
   "reduceBool", "reduceNat", "ofReduceBool", "ofReduceNat"]

/-- Every role's Lean name is a string component under a prefix. -/
theorem leanName_str (r : Role) : ∃ p s, r.leanName = .str p s ∧ s ∈ lastNames := by
  cases r <;> exact ⟨_, _, rfl, by decide⟩

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

/-- **The key of a role's constant.** -/
@[inline] def roleKey (r : Role) : Key := r.leanName

/-- Role keys are distinct exactly when their roles are. -/
@[simp] theorem roleKey_inj {r s : Role} : roleKey r = roleKey s ↔ r = s := Role.leanName_inj

theorem roleKey_ne {r s : Role} (h : r ≠ s) : roleKey r ≠ roleKey s :=
  fun e => h (roleKey_inj.mp e)

/-! ## Derived keys -/

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

/-- **The key of a generated constant**: shape `d` at base `k`. -/
@[inline] def auxKey (k : Key) : Derived → Key
  | .model => k.str "_model"
  | .impl => k.str "_impl"
  | .tag => k.str "tag"
  | .auxFamily => k.str "aux"
  | .member i => k.num i
  | .ctor j => k.str (indexedStr "ctor_" j)
  | .recursor => k.str "rec"
  | .iota j => k.str (indexedStr "iota_" j)
  | .eta => k.str "eta"
  | .unitlike => k.str "unitlike"
  | .projModel i => k.str (indexedStr "proj_" i)
  | .projIota => k.str "iota"
  | .projFn i => (k.str "proj").num i
  | .projTable => (k.str "projTable").num 0
  | .pack j => k.str (indexedStr "pack_" j)
  | .unpack j => k.str (indexedStr "unpack_" j)
  | .unpackPack j => k.str (indexedStr "unpackPack_" j)
  | .packUnpack j => k.str (indexedStr "packUnpack_" j)
  | .congrPack j => k.str (indexedStr "congrPack_" j)
  | .unpackAll => k.str "unpack"
  | .packUnpackAll => k.str "packUnpack"
  | .implRec => k.str "rec"

/-! ### Spelling facts (private: proofs elsewhere use the lemmas below) -/

private theorem indexedStr_inj {s : String} {i j : Nat} :
    indexedStr s i = indexedStr s j ↔ i = j := by
  unfold indexedStr
  rw [String.append_right_inj]
  exact Nat.repr_inj

private theorem lit_ne_indexedStr {a p : String} {i : Nat}
    (h : p.toList.isPrefixOf a.toList = false) : a ≠ indexedStr p i := by
  intro e
  have : p.toList.isPrefixOf a.toList = true := by
    rw [List.isPrefixOf_iff_prefix, e, indexedStr, String.toList_append]
    exact List.prefix_append _ _
  simp_all

private theorem indexedStr_ne {p q : String} {i j : Nat}
    (h : p.toList.isPrefixOf q.toList = false ∧ q.toList.isPrefixOf p.toList = false) :
    indexedStr p i ≠ indexedStr q j := by
  intro e
  have e' := congrArg String.toList e
  simp only [indexedStr, String.toList_append] at e'
  rcases List.prefix_or_prefix_of_prefix (List.prefix_append p.toList (toString i).toList)
    (e' ▸ List.prefix_append q.toList (toString j).toList) with hp | hp
  · have : p.toList.isPrefixOf q.toList = true := List.isPrefixOf_iff_prefix.mpr hp
    simp_all
  · have : q.toList.isPrefixOf p.toList = true := List.isPrefixOf_iff_prefix.mpr hp
    simp_all

private theorem str_ne_self (n : Name) (s : String) : n.str s ≠ n := by
  intro h; have := congrArg sizeOf h; simp at this; omega

private theorem lastNames_ne_indexedStr {p s : String} {j : Nat} (hs : s ∈ Role.lastNames)
    (hp : Role.lastNames.all (fun a => !p.toList.isPrefixOf a.toList) = true) :
    s ≠ indexedStr p j :=
  lit_ne_indexedStr (by have := List.all_eq_true.mp hp s hs; simpa using this)

/-! ### The lemmas -/

/-- A derived key is larger than its base. -/
theorem sizeOf_lt_auxKey (k : Key) (d : Derived) : sizeOf k < sizeOf (auxKey k d) := by
  cases d <;> simp [auxKey] <;> omega

/-- A derived key is not its base. -/
theorem auxKey_ne_self (k : Key) (d : Derived) : auxKey k d ≠ k := fun h =>
  absurd (h ▸ sizeOf_lt_auxKey k d) (Nat.lt_irrefl _)

/-- A key derived twice is not its base. -/
theorem auxKey_auxKey_ne_self (k : Key) (d d' : Derived) : auxKey (auxKey k d) d' ≠ k :=
  fun h => absurd (h ▸ Nat.lt_trans (sizeOf_lt_auxKey k d) (sizeOf_lt_auxKey _ d'))
    (Nat.lt_irrefl _)

/-- **`auxKey` is injective in its base.** -/
@[simp] theorem auxKey_inj {k k' : Key} {d : Derived} : auxKey k d = auxKey k' d ↔ k = k' := by
  constructor
  · intro h; cases d <;> simp_all [auxKey]
  · rintro rfl; rfl

/-- **At one derived shape, `auxKey` is injective in its base and its index
together.** -/
theorem auxKey_inj₂ {k k' : Key} {d d' : Derived} (hd : d.ctorIdx = d'.ctorIdx)
    (h : auxKey k d = auxKey k' d') : k = k' ∧ d = d' := by
  cases d <;> cases d' <;> first
    | exact absurd hd (by simp only [Derived.ctorIdx]; decide)
    | simp_all [auxKey, indexedStr_inj]

/-- **Distinct shapes at one base are distinct keys**, except that the
nested modeller's `implRec` is spelled as a recursor. -/
theorem auxKey_derived_eq {k : Key} {d d' : Derived} (h : auxKey k d = auxKey k d') :
    d = d' ∨ (d = .recursor ∧ d' = .implRec) ∨ (d = .implRec ∧ d' = .recursor) := by
  cases d <;> cases d' <;>
    simp only [auxKey, Name.str.injEq, Name.num.injEq, true_and, reduceCtorEq] at h <;>
    first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | exact Or.inl (congrArg _ h)
    | exact Or.inl (congrArg _ (indexedStr_inj.mp h))
    | exact absurd h (by decide)
    | exact absurd h.1 (by decide)
    | exact absurd h (lit_ne_indexedStr (by decide))
    | exact absurd h.symm (lit_ne_indexedStr (by decide))
    | exact absurd h (indexedStr_ne (by decide))
    | exact absurd h.1 (str_ne_self _ _)
    | exact absurd h.1.symm (str_ne_self _ _)

/-- Two different shapes at one base, neither of them the modeller's
recursors, are different keys. -/
theorem auxKey_ne_auxKey {k : Key} {d d' : Derived} (hne : d ≠ d')
    (hr : d ≠ .implRec ∨ d' ≠ .recursor) (hr' : d ≠ .recursor ∨ d' ≠ .implRec) :
    auxKey k d ≠ auxKey k d' := fun h => by
  rcases auxKey_derived_eq h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne h
  · exact hr'.elim (· h1) (· h2)
  · exact hr.elim (· h1) (· h2)

/-- The shapes whose key ends in a number: a member's constructor, a
projection function, a projection table. -/
def Derived.endsNum : Derived → Bool
  | .member _ | .projFn _ | .projTable => true
  | _ => false

/-- **Shapes of different ends are different keys**, at any bases. -/
theorem auxKey_ne_of_endsNum {k k' : Key} {d d' : Derived} (h : d.endsNum ≠ d'.endsNum) :
    auxKey k d ≠ auxKey k' d' := by
  cases d <;> cases d' <;> first
    | exact absurd rfl h
    | (simp only [auxKey]; exact fun e => Name.noConfusion e)

/-- **A derived key is not a role key**, except at the recursor spelling,
which a basis recursor shares with its inductive's `.recursor` shape. -/
theorem auxKey_ne_roleKey {k : Key} {d : Derived} (r : Role) (hd : d ≠ .recursor)
    (hd' : d ≠ .implRec) : auxKey k d ≠ roleKey r := by
  intro h
  obtain ⟨p, s, hr, hs⟩ := Role.leanName_str r
  rw [roleKey, hr] at h
  cases d <;> simp only [auxKey, Name.str.injEq, reduceCtorEq] at h <;>
    first
    | exact absurd rfl hd
    | exact absurd rfl hd'
    | (obtain ⟨-, rfl⟩ := h; revert hs; decide)
    | (obtain ⟨-, hx⟩ := h; exact lastNames_ne_indexedStr hs (by decide) hx.symm)

/-! ## Views of derived shapes

The inspections of a key's shape, each a test on `auxKey`'s spelling. -/

namespace Key

/-- Is `k` a model companion, `auxKey _ .model`? -/
def isModelSuffix : Key → Bool
  | .str _ "_model" => true
  | _ => false

/-- Is `k` spelled as an installed projection function `auxKey _ (.projFn i)`
or a projection table `auxKey _ .projTable` (at any index)?  Both shapes are
reserved for the checker's own installs. -/
def isProjFnShape : Key → Bool
  | .num (.str _ "proj") _ => true
  | .num (.str _ "projTable") _ => true
  | _ => false

/-- Is `k` a projection's constructor-reduction theorem, `auxKey _ .projIota`? -/
def isProjIota : Key → Bool
  | .str _ "iota" => true
  | _ => false

/-- Is `k` spelled as an input recursor (`T.rec`, the spelling of
`auxKey _ .recursor`, or `T.rec_j`)? -/
def isRecSpelling : Key → Bool
  | .str _ s => s == "rec" || s.startsWith "rec_"
  | _ => false

end Key

theorem isModelSuffix_iff {k : Key} : k.isModelSuffix = true ↔ ∃ b, k = auxKey b .model := by
  constructor
  · intro h
    cases k with
    | anonymous => exact absurd h (by decide)
    | num p i => exact absurd h (by simp [Key.isModelSuffix])
    | str b s =>
      by_cases hs : s = "_model"
      · subst hs; exact ⟨b, rfl⟩
      · exact absurd h (by simp [Key.isModelSuffix, hs])
  · rintro ⟨b, rfl⟩; rfl

theorem isModelSuffix_auxKey (k : Key) (d : Derived) :
    (auxKey k d).isModelSuffix = (d == .model) := by
  cases d <;> first
    | rfl
    | (simp only [auxKey, Key.isModelSuffix]
       rw [if_neg (Ne.symm (lit_ne_indexedStr (by decide)))]
       rfl)

@[simp] theorem isProjFnShape_auxKey_projFn (k : Key) (i : Nat) :
    (auxKey k (.projFn i)).isProjFnShape = true := rfl

@[simp] theorem isProjFnShape_auxKey_projTable (k : Key) :
    (auxKey k .projTable).isProjFnShape = true := rfl

/-- Off the member constructors (`k.num i`, whose shape depends on `k`), a
derived key has the projection shape exactly at the projection shapes. -/
theorem isProjFnShape_auxKey (k : Key) {d : Derived} (hd : ∀ i, d ≠ .member i) :
    (auxKey k d).isProjFnShape = (d matches .projFn _ | .projTable) := by
  cases d <;> first | rfl | exact absurd rfl (hd _)

theorem isProjIota_auxKey (k : Key) (d : Derived) :
    (auxKey k d).isProjIota = (d == .projIota) := by
  cases d <;> first
    | rfl
    | (simp only [auxKey, Key.isProjIota]
       rw [if_neg (Ne.symm (lit_ne_indexedStr (by decide)))]
       rfl)

/-- A model companion is not a key of another shape. -/
theorem auxKey_model_ne {n m : Key} (hm : m.isModelSuffix = false) : auxKey n .model ≠ m := by
  intro h
  subst h
  exact absurd hm (by rw [isModelSuffix_auxKey]; decide)

/-- A projection function is not a key of another shape. -/
theorem auxKey_projFn_ne {T n : Key} {j : Nat} (h : n.isProjFnShape = false) :
    auxKey T (.projFn j) ≠ n := by
  intro he
  subst he
  exact absurd h (by rw [isProjFnShape_auxKey_projFn]; decide)

end Ix.Kernel
