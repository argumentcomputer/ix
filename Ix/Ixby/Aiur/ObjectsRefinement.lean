module
public import Ix.Ixby.Aiur.Refinement
public import Ix.Aiur.Goldilocks
import all Ix.Aiur.Goldilocks

/-! Conditional representation contract for `Objects.lean`.

Unlike a finite logical tree assumption, `Ref` contains an arbitrary physical
field-list pointer. `Heap` is a functional typed-memory view and may contain
cycles. Bounded list reads and the local computed-rank rule imply a finite
IxBy value for every member of a closed collection of live references. Sharing
is permitted; physical pointer identity never becomes constructor identity.

The remaining bridge must establish this memory view, canonical scalar/u32
interpretation, declaration table, and closed local constraints from actual
Aiur traces/AIR. Neither compiler correctness nor cryptographic soundness is
assumed as an axiom or claimed here. This module imports no Aiur FFI. -/

public section
@[expose] section

namespace Ix.Ixby.AiurBackend.ObjectsRefinement

private theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem except_map_ok {ε α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) := rfl

attribute [local simp] except_bind_ok except_map_ok

/-- First numeric bridge to Aiur's field-valued metadata: canonical bounded
integers embed without truncation or modular aliasing. This is about the pure
field model; the AIR range gadget still has to be shown to implement it. -/
theorem field_of_nat_exact (n : Nat) (bound : n < goldilocksModulus) :
    (Aiur.G.ofNat n).n = n := by
  have modulus : Aiur.gSize.toNat = goldilocksModulus := by decide
  have narrow : n < 2 ^ 64 := Nat.lt_trans bound (by decide)
  have toNat : n.toUInt64.toNat = n := by
    simp [Nat.mod_eq_of_lt narrow]
  have range : n.toUInt64 < Aiur.gSize := by
    simpa [UInt64.lt_iff_toNat_lt, toNat, modulus] using bound
  simp only [Aiur.G.ofNat, modulus, Nat.mod_eq_of_lt bound, dif_pos range]
  exact toNat

theorem field_comparison_exact (a b : Aiur.G) :
    Aiur.G.u32LessThan a b = 1 ↔ a.n < b.n := by
  by_cases less : a.n < b.n
  · simp [Aiur.G.u32LessThan, less]
  · simp [Aiur.G.u32LessThan, less]
    decide

/-- `is_make` adds one to a checked maximum child rank. Even the largest
intermediate bound cannot wrap in Goldilocks. -/
theorem field_rank_successor (rank : Aiur.G)
    (bound : rank.n ≤ objectsProfile.valueDepth + objectsProfile.maxSteps) :
    (rank + 1).n = rank.n + 1 := by
  change (Aiur.G.ofNat (rank.n + (1 : Aiur.G).n)).n = rank.n + 1
  have one : (1 : Aiur.G).n = 1 := by decide
  rw [one]
  apply field_of_nat_exact
  change rank.n ≤ 288 at bound
  change rank.n + 1 < 18446744069414584321
  omega

theorem checked_rank_equation (parent maximum : Aiur.G)
    (bound : maximum.n ≤ objectsProfile.valueDepth + objectsProfile.maxSteps)
    (computed : parent = maximum + 1) : parent.n = maximum.n + 1 := by
  rw [computed]
  exact field_rank_successor maximum bound

inductive Atom where
  | bool (value : Bool)
  | word (value : UInt32)
  | field (value : Goldilocks)
  | ext (value : ExtGoldilocks)
  | erased
  deriving BEq, DecidableEq, Repr, Inhabited

def Atom.decode : Atom → Value
  | .bool b => .scalar (.bool b)
  | .word w => .scalar (.word32 w)
  | .field f => .scalar (.field f)
  | .ext f => .scalar (.extField f)
  | .erased => .erased

/-- Natural views of the circuit's bounded metadata. `pointer` is physical;
`index` is a logical index into the authenticated constructor table. -/
inductive Ref where
  | atom (value : Atom)
  | ctor (index pointer count rank : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

def Ref.rank : Ref → Nat
  | .atom _ => 1
  | .ctor _ _ _ rank => rank

inductive Cell where
  | nil
  | cons (value : Ref) (tail : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Functional memory consistency, not allocation order or injective stores.
Different addresses may contain equal cells. Unreachable cells are unrestricted. -/
abbrev Heap := Nat → Option Cell

/-- Exactly `count` cons cells followed by Nil, matching `is_fields_rank` and
the bounded field-list walkers. Even an adversarial cyclic spine is bounded. -/
def readFields (heap : Heap) : Nat → Nat → Option (List Ref)
  | 0, pointer => match heap pointer with
    | some .nil => some []
    | _ => none
  | count + 1, pointer => match heap pointer with
    | some (.cons value tail) => (value :: ·) <$> readFields heap count tail
    | _ => none

theorem read_fields_length {heap : Heap} {count pointer : Nat} {fields : List Ref}
    (read : readFields heap count pointer = some fields) : fields.length = count := by
  induction count generalizing pointer fields with
  | zero =>
    cases h : heap pointer with
    | none => simp [readFields, h] at read
    | some cell => cases cell <;> simp_all [readFields]
  | succ count ih =>
    cases h : heap pointer with
    | none => simp [readFields, h] at read
    | some cell =>
      cases cell with
      | nil => simp [readFields, h] at read
      | cons value tail =>
        cases hr : readFields heap count tail with
        | none => simp [readFields, h, hr] at read
        | some rest =>
          simp [readFields, h, hr] at read
          subst fields
          simp [ih hr]

def maxRank : List Ref → Nat
  | [] => 0
  | value :: rest => max value.rank (maxRank rest)

theorem rank_le_max {value : Ref} {fields : List Ref} (mem : value ∈ fields) :
    value.rank ≤ maxRank fields := by
  induction fields with
  | nil => simp at mem
  | cons head tail ih =>
    rcases List.mem_cons.mp mem with rfl | mem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih mem) (Nat.le_max_right _ _)

theorem max_rank_le {fields : List Ref} {bound : Nat}
    (bounded : ∀ value ∈ fields, value.rank ≤ bound) : maxRank fields ≤ bound := by
  induction fields with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    exact Nat.max_le.mpr ⟨bounded head (by simp), ih (fun v h => bounded v (by simp [h]))⟩

/-- Pointwise relation, kept local so no external proof library is needed. -/
inductive All₂ {α β : Type} (relation : α → β → Prop) : List α → List β → Prop
  | nil : All₂ relation [] []
  | cons : relation a b → All₂ relation as bs → All₂ relation (a :: as) (b :: bs)

theorem all₂_length {α β : Type} {relation : α → β → Prop} {as : List α} {bs : List β}
    (related : All₂ relation as bs) : as.length = bs.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem all₂_exists {α β : Type} {relation : α → β → Prop} {as : List α}
    (each : ∀ a ∈ as, ∃ b, relation a b) : ∃ bs, All₂ relation as bs := by
  induction as with
  | nil => exact ⟨[], .nil⟩
  | cons a as ih =>
    obtain ⟨b, hb⟩ := each a (by simp)
    obtain ⟨bs, hbs⟩ := ih (fun a h => each a (by simp [h]))
    exact ⟨b :: bs, .cons hb hbs⟩

theorem all₂_lookup {α β : Type} {relation : α → β → Prop} {as : List α} {bs : List β}
    (related : All₂ relation as bs) (index : Nat) (a : α)
    (found : as[index]? = some a) : ∃ b, bs[index]? = some b ∧ relation a b := by
  induction related generalizing index with
  | nil => simp at found
  | @cons head value as bs rel rest ih =>
    cases index with
    | zero => simp at found; subst a; exact ⟨value, rfl, rel⟩
    | succ index => exact ih index (by simpa using found)

/-- Finite logical meaning is the conclusion of `ranked_heap_represents`, not
a condition imposed on the raw pointer graph. Fields are reversed exactly once. -/
inductive Represents (heap : Heap) (table : Array CtorDecl) : Ref → Value → Prop
  | atom (value : Atom) : Represents heap table (.atom value) value.decode
  | ctor {index pointer count rank : Nat} {decl : CtorDecl}
      {fields : List Ref} {values : List Value}
      (declaration : table[index]? = some decl)
      (arity : count = decl.fields)
      (read : readFields heap count pointer = some fields)
      (ranked : rank = maxRank fields + 1)
      (children : All₂ (Represents heap table) fields values) :
      Represents heap table (.ctor index pointer count rank) (.ctor decl.id values.reverse.toArray)

/-- The local checks that every live constructor must satisfy. Closure includes
children, but says nothing about unrelated cells that happen to share a width. -/
def ClosedRanked (heap : Heap) (table : Array CtorDecl) (live : Ref → Prop) : Prop :=
  ∀ index pointer count rank, live (.ctor index pointer count rank) →
    ∃ decl fields, table[index]? = some decl ∧ count = decl.fields ∧
      readFields heap count pointer = some fields ∧ rank = maxRank fields + 1 ∧
      ∀ child ∈ fields, live child

theorem ranked_heap_represents {heap : Heap} {table : Array CtorDecl} {live : Ref → Prop}
    (closed : ClosedRanked heap table live) (ref : Ref) (valid : live ref) :
    ∃ value, Represents heap table ref value := by
  have go : ∀ n ref, ref.rank = n → live ref → ∃ value, Represents heap table ref value := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ref hr hv
      cases ref with
      | atom atom => exact ⟨atom.decode, .atom atom⟩
      | ctor index pointer count rank =>
        obtain ⟨decl, fields, declaration, arity, read, ranked, children⟩ :=
          closed index pointer count rank hv
        have each : ∀ child ∈ fields, ∃ value, Represents heap table child value := by
          intro child mem
          have lt : child.rank < n := by
            have le := rank_le_max mem
            simp only [Ref.rank] at hr
            omega
          exact ih child.rank lt child rfl (children child mem)
        obtain ⟨values, related⟩ := all₂_exists each
        exact ⟨.ctor decl.id values.reverse.toArray, .ctor declaration arity read ranked related⟩
  exact go ref.rank ref rfl valid

def Child (heap : Heap) (child parent : Ref) : Prop :=
  ∃ index pointer count rank fields, parent = .ctor index pointer count rank ∧
    readFields heap count pointer = some fields ∧ child ∈ fields

def RankedEdge (heap : Heap) (live : Ref → Prop) (child parent : Ref) : Prop :=
  live parent ∧ Child heap child parent

theorem child_rank_lt {heap : Heap} {table : Array CtorDecl} {live : Ref → Prop}
    (closed : ClosedRanked heap table live) {child parent : Ref}
    (edge : RankedEdge heap live child parent) : child.rank < parent.rank := by
  obtain ⟨valid, index, pointer, count, rank, fields, rfl, read, mem⟩ := edge
  obtain ⟨decl, other, _, _, same, ranked, _⟩ := closed index pointer count rank valid
  have eq : fields = other := Option.some.inj (read.symm.trans same)
  subst other
  have le := rank_le_max mem
  change child.rank < rank
  omega

/-- The actual child relation is well-founded even if the heap itself has
unreachable cycles or duplicate cells. No pointer allocation order is assumed. -/
theorem ranked_edges_well_founded {heap : Heap} {table : Array CtorDecl} {live : Ref → Prop}
    (closed : ClosedRanked heap table live) : WellFounded (RankedEdge heap live) :=
  Subrelation.wf (fun edge => child_rank_lt closed edge) (InvImage.wf Ref.rank Nat.lt_wfRel.wf)

theorem no_ranked_cycle {heap : Heap} {table : Array CtorDecl} {live : Ref → Prop}
    (closed : ClosedRanked heap table live) (ref : Ref) :
    ¬ Relation.TransGen (RankedEdge heap live) ref ref := by
  have strict : ∀ {a b}, Relation.TransGen (RankedEdge heap live) a b → a.rank < b.rank := by
    intro a b path
    induction path with
    | single edge => exact child_rank_lt closed edge
    | tail _ edge ih => exact Nat.lt_trans ih (child_rank_lt closed edge)
  intro cycle
  exact Nat.lt_irrefl _ (strict cycle)

def makeRef (index pointer : Nat) (fields : List Ref) : Ref :=
  .ctor index pointer fields.length (maxRank fields + 1)

theorem construct_represents {heap : Heap} {table : Array CtorDecl}
    {index pointer : Nat} {decl : CtorDecl} {fields : List Ref} {values : List Value}
    (declaration : table[index]? = some decl) (arity : fields.length = decl.fields)
    (read : readFields heap fields.length pointer = some fields)
    (children : All₂ (Represents heap table) fields values) :
    Represents heap table (makeRef index pointer fields) (.ctor decl.id values.reverse.toArray) :=
  .ctor declaration arity read rfl children

theorem construct_rank_le {fields : List Ref} {bound index pointer : Nat}
    (bounded : ∀ value ∈ fields, value.rank ≤ bound) :
    (makeRef index pointer fields).rank ≤ bound + 1 := by
  exact Nat.add_le_add_right (max_rank_le bounded) 1

/-- Derived rank bound: at most one level is added per transition. This is
not an extra I/O depth rule; traces must separately establish `growth`. -/
theorem rank_growth_bound (height : Nat → Nat) (inputDepth : Nat)
    (initial : height 0 ≤ inputDepth) (growth : ∀ n, height (n + 1) ≤ height n + 1) :
    ∀ steps, height steps ≤ inputDepth + steps := by
  intro steps
  induction steps with
  | zero => simpa using initial
  | succ n ih => have := growth n; omega

theorem reversed_projection {heap : Heap} {table : Array CtorDecl}
    {fields : List Ref} {values : List Value} (related : All₂ (Represents heap table) fields values)
    {index count : Nat} {child : Ref} (size : fields.length = count) (bound : index < count)
    (project : fields[count - (index + 1)]? = some child) :
    ∃ value, values.reverse.toArray[index]? = some value ∧ Represents heap table child value := by
  obtain ⟨value, found, rep⟩ := all₂_lookup related (count - (index + 1)) child project
  have length : values.length = count := (all₂_length related).symm.trans size
  refine ⟨value, ?_, rep⟩
  simp only [List.getElem?_toArray]
  rw [List.getElem?_reverse (by omega)]
  have index_eq : values.length - 1 - index = count - (index + 1) := by omega
  rw [index_eq]
  exact found

/-- Whole-table uniqueness is what permits the runtime case dispatcher to
compare logical indices instead of re-comparing 40-byte semantic names. -/
def UniqueIds (table : Array CtorDecl) : Prop :=
  ∀ (i j : Nat) (a b : CtorDecl), table[i]? = some a → table[j]? = some b → a.id = b.id → i = j

theorem constructor_identity_iff {table : Array CtorDecl} (unique : UniqueIds table)
    {i j : Nat} {a b : CtorDecl} (left : table[i]? = some a) (right : table[j]? = some b) :
    a.id = b.id ↔ i = j := by
  constructor
  · exact unique i j a b left right
  · intro same
    subst j
    have eq : a = b := Option.some.inj (left.symm.trans right)
    exact congrArg CtorDecl.id eq

private theorem ctor_id_beq_iff (a b : CtorId) : (a == b) = true ↔ a = b := by
  cases a
  cases b
  simp [BEq.beq, instBEqCtorId.beq, CtorId.mk.injEq, Bool.and_eq_true]

def selectIndex (id : CtorId) (index : Nat) : List Alternative → Except Error BlockId
  | [] => .error (.missingCase id)
  | alt :: rest => if alt.ctor == index then .ok alt.target else selectIndex id index rest

theorem case_selection (program : Program) (index : Nat) (decl : CtorDecl)
    (unique : UniqueIds program.constructors)
    (declaration : program.constructors[index]? = some decl) (alts : List Alternative)
    (admitted : ∀ alt ∈ alts, ∃ other, program.constructors[alt.ctor]? = some other) :
    selectCase program decl.id alts = selectIndex decl.id index alts := by
  induction alts with
  | nil => rfl
  | cons alt rest ih =>
    obtain ⟨other, found⟩ := admitted alt (by simp)
    have comparison : (other.id == decl.id) = (alt.ctor == index) := by
      apply Bool.eq_iff_iff.mpr
      simp only [ctor_id_beq_iff, beq_iff_eq]
      exact constructor_identity_iff unique found declaration
    have tail := ih (fun alt mem => admitted alt (by simp [mem]))
    simp [selectCase, Program.getConstructor, found, comparison, selectIndex, tail, Pure.pure, Except.pure]

open Refinement

def bindFields (frame : RevFrame) (target : BlockId) (reversed : List Value) : RevFrame :=
  { frame with block := target, locals := reversed ++ frame.locals }

@[simp] theorem decode_bind_fields (frame : RevFrame) (target : BlockId) (reversed : List Value) :
    (bindFields frame target reversed).decode =
      { frame.decode with block := target, locals := frame.decode.locals ++ reversed.reverse.toArray } := by
  cases frame
  simp [bindFields, RevFrame.decode, List.reverse_append]

theorem case_transfer (frame : RevFrame) (target : BlockId) (reversed : List Value)
    (limits : Limits) (program : Program) (block : Block)
    (checked : (bindFields frame target reversed).decode.check limits program = .ok block) :
    frame.decode.transfer limits program target reversed.reverse.toArray =
      .ok (bindFields frame target reversed).decode := by
  simp only [decode_bind_fields] at checked ⊢
  simp [Frame.transfer, checked]

theorem constructor_operation (limits : Limits) (program : Program) (frame : Frame)
    (index : Nat) (operands : List Operand) (fields : List Value) (decl : CtorDecl)
    (declaration : program.getConstructor index = .ok decl)
    (read : frame.readOperands operands = .ok fields) (arity : fields.length = decl.fields) :
    evalOp limits program frame (.construct index operands) = .ok (.value (.ctor decl.id fields.toArray)) := by
  simp [evalOp, declaration, read, arity, Pure.pure, Except.pure]

theorem erased_projection (limits : Limits) (program : Program) (frame : Frame)
    (operand : Operand) (index : Nat) (read : frame.read operand = .ok .erased) :
    evalOp limits program frame (.project operand index) = .ok (.value .erased) := by
  simp [evalOp, read, Pure.pure, Except.pure]

theorem case_transition (limits : Limits) (program : Program) (frame : RevFrame)
    (stack : List RevFrame) (operand : Operand) (alternatives : List Alternative)
    (id : CtorId) (reversed : List Value) (target declared : Nat) (next : Block)
    (checked : frame.decode.check limits program = .ok ⟨declared, .caseCtor operand alternatives⟩)
    (read : frame.decode.read operand = .ok (.ctor id reversed.reverse.toArray))
    (selected : selectCase program id alternatives = .ok target)
    (nextChecked : (bindFields frame target reversed).decode.check limits program = .ok next) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.eval (bindFields frame target reversed)) stack)) := by
  simp [step, stepEval, decodeState, RevControl.decode, checked, read, selected,
    case_transfer frame target reversed limits program next nextChecked]

end Ix.Ixby.AiurBackend.ObjectsRefinement
