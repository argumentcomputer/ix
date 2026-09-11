import Ix.Compiler.IxIR1.ReaddressAll
import Ix.Compiler.IxIR1.Eval
import Ix.Compiler.Ixon.Merkle

/-!
# Cached heap-points-to summary certificates for IxIR₁

This module introduces the first analysis-certificate boundary over the
content-addressed IxIR₁ program.  The untrusted input is a finite result-shape
summary for every declaration.  The checker interprets each function once
against the complete candidate environment and accepts only a post-fixpoint:
the locally inferred result shapes must be contained in the claimed summary.

The abstract domain distinguishes scalar results, constructor identities, and
partial applications with an exact target and supplied-argument count.
Constructor results may additionally carry finite recursive field facts:
allocation records argument facts, fetch re-roots a selected subtree, and
case alternatives recover the same refined binder facts. Function parameters
begin at `top`, so accepted summaries are valid without a caller-specific
precondition. Unknown dynamic heap values and identity-only constructor facts
still widen on fetch. Explicit depth and total-payload limits keep untrusted
trees finite before normalization, interpretation, or hashing.

Checked summaries are materialized at the same SCC granularity as
`ReaddressAll.Artifact`.  An ordinary summary cache key commits to the
declaration address and the already-checked dependency-summary addresses; all
members of a recursive SCC share one cache key committed to the mutual-block
address.  Thus recursive analysis facts have a finite spelling, while changes
outside a dependency cone do not perturb an unrelated cache key.
-/

namespace Ix.Compiler.IxIR1.HPT

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR

/-! ## Abstract result and constructor-field shapes -/

private def compareNat (left right : Nat) : Ordering :=
  compare left right

private def compareBool : Bool → Bool → Ordering
  | false, false | true, true => .eq
  | false, true => .lt
  | true, false => .gt

private def compareCtor (left right : CtorId) : Ordering :=
  match Ixon.Merkle.compareAddress left.block right.block with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
      match compareNat left.indIdx right.indIdx with
      | .lt => .lt
      | .gt => .gt
      | .eq => compareNat left.cidx right.cidx

private def compareList (compare : α → α → Ordering) :
    List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: lefts, right :: rights =>
      match compare left right with
      | .lt => .lt
      | .gt => .gt
      | .eq => compareList compare lefts rights

/- A recursively refined heap shape retained inside a constructor field.
`none` keeps only a constructor identity; `some fields` describes the exact
field vector and may itself contain further refined constructor shapes.  The
certificate preflight and cache decoder bound recursion depth and total
payload before normalization or interpretation. -/
mutual

inductive FieldShape where
  | ctor (identity : CtorId) (fields : Option (List FieldFact))
  | pap (function : Address) (supplied : Nat)
  deriving Repr, Inhabited

/-- A finite recursive fact for one constructor field. -/
structure FieldFact where
  mayScalar : Bool
  unknownHeap : Bool
  shapes : List FieldShape
  deriving Repr, Inhabited

end


/-! `deriving LawfulBEq` does not support mutually recursive inductives.  Keep
the executable equality explicit and prove its reflection below, so recursive
facts remain usable by canonicalization without introducing an axiom. -/

mutual

def FieldShape.compare : FieldShape → FieldShape → Ordering
  | .ctor left leftFields, .ctor right rightFields =>
      match compareCtor left right with
      | .lt => .lt
      | .gt => .gt
      | .eq => FieldFact.compareOptions leftFields rightFields
  | .ctor _ _, .pap _ _ => .lt
  | .pap _ _, .ctor _ _ => .gt
  | .pap leftFunction leftSupplied, .pap rightFunction rightSupplied =>
      match Ixon.Merkle.compareAddress leftFunction rightFunction with
      | .lt => .lt
      | .gt => .gt
      | .eq => compareNat leftSupplied rightSupplied
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldFact.compare (left right : FieldFact) : Ordering :=
  match compareBool left.mayScalar right.mayScalar with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
      match compareBool left.unknownHeap right.unknownHeap with
      | .lt => .lt
      | .gt => .gt
      | .eq => FieldShape.compareLists left.shapes right.shapes
termination_by sizeOf left + sizeOf right
decreasing_by
  cases left
  cases right
  simp_wf
  omega

def FieldShape.compareLists : List FieldShape → List FieldShape → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: lefts, right :: rights =>
      match left.compare right with
      | .lt => .lt
      | .gt => .gt
      | .eq => FieldShape.compareLists lefts rights
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldFact.compareLists : List FieldFact → List FieldFact → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: lefts, right :: rights =>
      match left.compare right with
      | .lt => .lt
      | .gt => .gt
      | .eq => FieldFact.compareLists lefts rights
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldFact.compareOptions : Option (List FieldFact) →
    Option (List FieldFact) → Ordering
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some left, some right => FieldFact.compareLists left right
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

end


mutual

def FieldShape.beq : FieldShape → FieldShape → Bool
  | .ctor left leftFields, .ctor right rightFields =>
      left == right && FieldFact.beqOptions leftFields rightFields
  | .pap leftFunction leftSupplied, .pap rightFunction rightSupplied =>
      leftFunction == rightFunction && leftSupplied == rightSupplied
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldFact.beq (left right : FieldFact) : Bool :=
  left.mayScalar == right.mayScalar &&
    left.unknownHeap == right.unknownHeap &&
      FieldShape.beqLists left.shapes right.shapes
termination_by sizeOf left + sizeOf right
decreasing_by
  cases left
  cases right
  simp_wf
  omega

def FieldShape.beqLists : List FieldShape → List FieldShape → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.beq right && FieldShape.beqLists lefts rights
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldFact.beqLists : List FieldFact → List FieldFact → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.beq right && FieldFact.beqLists lefts rights
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldFact.beqOptions : Option (List FieldFact) →
    Option (List FieldFact) → Bool
  | none, none => true
  | some left, some right => FieldFact.beqLists left right
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

end


mutual

theorem FieldShape.eq_of_beq {left right : FieldShape}
    (h : left.beq right = true) : left = right :=
  match left, right with
  | .ctor identity fields, .ctor identity' fields' => by
      simp only [FieldShape.beq, Bool.and_eq_true] at h
      have hidentity : identity = identity' := beq_iff_eq.mp h.1
      have hfields : fields = fields' := FieldFact.options_eq_of_beq h.2
      subst identity'
      subst fields'
      rfl
  | .pap function supplied, .pap function' supplied' => by
      simp only [FieldShape.beq, Bool.and_eq_true] at h
      have hfunction : function = function' := beq_iff_eq.mp h.1
      have hsupplied : supplied = supplied' := beq_iff_eq.mp h.2
      subst function'
      subst supplied'
      rfl
  | .ctor _ _, .pap _ _ | .pap _ _, .ctor _ _ => by
      simp [FieldShape.beq] at h
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

theorem FieldFact.eq_of_beq {left right : FieldFact}
    (h : left.beq right = true) : left = right :=
  match left, right with
  | ⟨leftScalar, leftUnknown, leftShapes⟩,
      ⟨rightScalar, rightUnknown, rightShapes⟩ => by
      simp only [FieldFact.beq, Bool.and_eq_true] at h
      have hscalar : leftScalar = rightScalar := beq_iff_eq.mp h.1.1
      have hunknown : leftUnknown = rightUnknown := beq_iff_eq.mp h.1.2
      have hshapes : leftShapes = rightShapes :=
        FieldShape.lists_eq_of_beq h.2
      subst rightScalar
      subst rightUnknown
      subst rightShapes
      rfl
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

theorem FieldShape.lists_eq_of_beq {left right : List FieldShape}
    (h : FieldShape.beqLists left right = true) : left = right :=
  match left, right with
  | [], [] => rfl
  | left :: lefts, right :: rights => by
      simp only [FieldShape.beqLists, Bool.and_eq_true] at h
      have hhead := FieldShape.eq_of_beq h.1
      have htail := FieldShape.lists_eq_of_beq h.2
      subst right
      subst rights
      rfl
  | [], _ :: _ | _ :: _, [] => by simp [FieldShape.beqLists] at h
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

theorem FieldFact.lists_eq_of_beq {left right : List FieldFact}
    (h : FieldFact.beqLists left right = true) : left = right :=
  match left, right with
  | [], [] => rfl
  | left :: lefts, right :: rights => by
      simp only [FieldFact.beqLists, Bool.and_eq_true] at h
      have hhead := FieldFact.eq_of_beq h.1
      have htail := FieldFact.lists_eq_of_beq h.2
      subst right
      subst rights
      rfl
  | [], _ :: _ | _ :: _, [] => by simp [FieldFact.beqLists] at h
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

theorem FieldFact.options_eq_of_beq
    {left right : Option (List FieldFact)}
    (h : FieldFact.beqOptions left right = true) : left = right :=
  match left, right with
  | none, none => rfl
  | some left, some right =>
      congrArg some (FieldFact.lists_eq_of_beq
        (by simpa [FieldFact.beqOptions] using h))
  | none, some _ | some _, none => by simp [FieldFact.beqOptions] at h
termination_by sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

end


mutual

theorem FieldShape.beq_refl (shape : FieldShape) : shape.beq shape = true := by
  cases shape with
  | ctor identity fields =>
      simp only [FieldShape.beq, beq_iff_eq.mpr rfl]
      exact FieldFact.beqOptions_refl fields
  | pap function supplied => simp [FieldShape.beq]
termination_by sizeOf shape
decreasing_by all_goals simp_wf <;> omega

theorem FieldFact.beq_refl (fact : FieldFact) : fact.beq fact = true := by
  cases fact with
  | mk mayScalar unknownHeap shapes =>
      simp only [FieldFact.beq, beq_iff_eq.mpr rfl]
      exact FieldShape.beqLists_refl shapes
termination_by sizeOf fact
decreasing_by all_goals simp_wf <;> omega

theorem FieldShape.beqLists_refl (shapes : List FieldShape) :
    FieldShape.beqLists shapes shapes = true := by
  cases shapes with
  | nil => simp [FieldShape.beqLists]
  | cons head tail =>
      simp [FieldShape.beqLists, FieldShape.beq_refl head,
        FieldShape.beqLists_refl tail]
termination_by sizeOf shapes
decreasing_by all_goals simp_wf <;> omega

theorem FieldFact.beqLists_refl (facts : List FieldFact) :
    FieldFact.beqLists facts facts = true := by
  cases facts with
  | nil => simp [FieldFact.beqLists]
  | cons head tail =>
      simp [FieldFact.beqLists, FieldFact.beq_refl head,
        FieldFact.beqLists_refl tail]
termination_by sizeOf facts
decreasing_by all_goals simp_wf <;> omega

theorem FieldFact.beqOptions_refl (facts : Option (List FieldFact)) :
    FieldFact.beqOptions facts facts = true := by
  cases facts with
  | none => simp [FieldFact.beqOptions]
  | some facts => simpa [FieldFact.beqOptions] using
      FieldFact.beqLists_refl facts
termination_by sizeOf facts
decreasing_by all_goals simp_wf <;> omega

end


instance : BEq FieldShape := ⟨FieldShape.beq⟩

instance : ReflBEq FieldShape where
  rfl := by intro shape; exact FieldShape.beq_refl shape

instance : LawfulBEq FieldShape := ⟨FieldShape.eq_of_beq⟩

instance : DecidableEq FieldShape := instDecidableEqOfLawfulBEq

instance : BEq FieldFact := ⟨FieldFact.beq⟩

instance : ReflBEq FieldFact where
  rfl := by intro fact; exact FieldFact.beq_refl fact

instance : LawfulBEq FieldFact := ⟨FieldFact.eq_of_beq⟩

instance : DecidableEq FieldFact := instDecidableEqOfLawfulBEq

namespace FieldShape

private def insert (shape : FieldShape) : List FieldShape → List FieldShape
  | [] => [shape]
  | head :: tail =>
      match compare shape head with
      | .lt => shape :: head :: tail
      | .eq =>
          if shape == head then head :: tail
          else shape :: head :: tail
      | .gt => head :: insert shape tail

def normalize (shapes : List FieldShape) : List FieldShape :=
  shapes.foldr insert []

private theorem mem_insert_of_mem {needle shape : FieldShape}
    {shapes : List FieldShape} (h : needle ∈ shapes) :
    needle ∈ insert shape shapes := by
  induction shapes with
  | nil => contradiction
  | cons head tail ih =>
      cases hcompare : compare shape head with
      | lt =>
          rw [insert, hcompare]
          exact List.mem_cons.mpr (Or.inr h)
      | eq =>
          by_cases heq : shape = head
          · rw [insert, hcompare, if_pos ((beq_iff_eq).mpr heq)]
            exact h
          · rw [insert, hcompare, if_neg (by simpa using heq)]
            exact List.mem_cons.mpr (Or.inr h)
      | gt =>
          rw [insert, hcompare]
          rcases List.mem_cons.mp h with hhead | htail
          · exact List.mem_cons.mpr (Or.inl hhead)
          · exact List.mem_cons.mpr (Or.inr (ih htail))

private theorem mem_insert_self (shape : FieldShape)
    (shapes : List FieldShape) : shape ∈ insert shape shapes := by
  induction shapes with
  | nil => simp [insert]
  | cons head tail ih =>
      cases hcompare : compare shape head with
      | lt =>
          rw [insert, hcompare]
          exact List.mem_cons.mpr (Or.inl rfl)
      | eq =>
          by_cases heq : shape = head
          · rw [insert, hcompare, if_pos ((beq_iff_eq).mpr heq)]
            exact List.mem_cons.mpr (Or.inl heq)
          · rw [insert, hcompare, if_neg (by simpa using heq)]
            exact List.mem_cons.mpr (Or.inl rfl)
      | gt =>
          rw [insert, hcompare]
          exact List.mem_cons.mpr (Or.inr ih)

theorem mem_normalize_of_mem {shape : FieldShape} {shapes : List FieldShape}
    (h : shape ∈ shapes) : shape ∈ normalize shapes := by
  unfold normalize
  induction shapes with
  | nil => contradiction
  | cons head tail ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with hhead | htail
      · subst head
        exact mem_insert_self shape _
      · exact mem_insert_of_mem (ih htail)

end FieldShape

namespace FieldFact

def bottom : FieldFact := ⟨false, false, []⟩
def scalar : FieldFact := ⟨true, false, []⟩
def heap (shape : FieldShape) : FieldFact := ⟨false, false, [shape]⟩
def top : FieldFact := ⟨true, true, []⟩

def normalize (fact : FieldFact) : FieldFact :=
  if fact.unknownHeap then
    { fact with shapes := [] }
  else
    { fact with shapes := FieldShape.normalize fact.shapes }

end FieldFact

mutual

def FieldShape.canonical : FieldShape → Bool
  | .ctor _ none | .pap _ _ => true
  | .ctor _ (some fields) => FieldFact.allCanonical fields
termination_by shape => sizeOf shape
decreasing_by all_goals simp_wf <;> omega

def FieldFact.canonical (fact : FieldFact) : Bool :=
  fact == fact.normalize && FieldShape.allCanonical fact.shapes
termination_by sizeOf fact
decreasing_by
  cases fact
  simp_wf

def FieldShape.allCanonical : List FieldShape → Bool
  | [] => true
  | shape :: shapes => shape.canonical && FieldShape.allCanonical shapes
termination_by shapes => sizeOf shapes
decreasing_by all_goals simp_wf <;> omega

def FieldFact.allCanonical : List FieldFact → Bool
  | [] => true
  | fact :: facts => fact.canonical && FieldFact.allCanonical facts
termination_by facts => sizeOf facts
decreasing_by all_goals simp_wf <;> omega

end

mutual

def FieldShape.le : FieldShape → FieldShape → Bool
  | .ctor left leftFields, .ctor right rightFields =>
      left == right &&
        match rightFields with
        | none => true
        | some rightFacts =>
            match leftFields with
            | none => false
            | some leftFacts => FieldFact.listLe leftFacts rightFacts
  | .pap leftFunction leftSupplied, .pap rightFunction rightSupplied =>
      leftFunction == rightFunction && leftSupplied == rightSupplied
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldFact.le (left right : FieldFact) : Bool :=
  (!left.mayScalar || right.mayScalar) &&
    (right.unknownHeap ||
      (!left.unknownHeap && FieldShape.allLe left.shapes right.shapes))
termination_by sizeOf left + sizeOf right
decreasing_by
  cases left
  cases right
  simp_wf
  omega

def FieldShape.allLe : List FieldShape → List FieldShape → Bool
  | [], _ => true
  | left :: lefts, rights =>
      FieldShape.anyLe left rights && FieldShape.allLe lefts rights
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

def FieldShape.anyLe (left : FieldShape) : List FieldShape → Bool
  | [] => false
  | right :: rights => left.le right || FieldShape.anyLe left rights
termination_by rights => sizeOf left + sizeOf rights
decreasing_by all_goals simp_wf <;> omega

def FieldFact.listLe : List FieldFact → List FieldFact → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.le right && FieldFact.listLe lefts rights
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf <;> omega

end

namespace FieldFact

def join (left right : FieldFact) : FieldFact :=
  normalize
    { mayScalar := left.mayScalar || right.mayScalar
      unknownHeap := left.unknownHeap || right.unknownHeap
      shapes := left.shapes ++ right.shapes }

def forgetHeap (fact : FieldFact) : FieldFact :=
  if fact.unknownHeap || !fact.shapes.isEmpty then
    { mayScalar := fact.mayScalar, unknownHeap := true, shapes := [] }
  else
    fact

end FieldFact

mutual

def FieldShape.bytes : FieldShape → ByteArray
  | .ctor identity fields => Encoding.tag 0 ++
      Encoding.address identity.block ++ Encoding.nat identity.indIdx ++
        Encoding.nat identity.cidx ++ FieldFact.optionBytes fields
  | .pap function supplied => Encoding.tag 1 ++
      Encoding.address function ++ Encoding.nat supplied
termination_by shape => sizeOf shape
decreasing_by all_goals simp_wf <;> omega

def FieldFact.bytes (fact : FieldFact) : ByteArray :=
  Encoding.bool fact.mayScalar ++ Encoding.bool fact.unknownHeap ++
    Encoding.nat fact.shapes.length ++ FieldShape.payloadBytes fact.shapes
termination_by sizeOf fact
decreasing_by
  cases fact
  simp_wf

def FieldShape.payloadBytes : List FieldShape → ByteArray
  | [] => ByteArray.empty
  | shape :: shapes => shape.bytes ++ FieldShape.payloadBytes shapes
termination_by shapes => sizeOf shapes
decreasing_by all_goals simp_wf <;> omega

def FieldFact.payloadBytes : List FieldFact → ByteArray
  | [] => ByteArray.empty
  | fact :: facts => fact.bytes ++ FieldFact.payloadBytes facts
termination_by facts => sizeOf facts
decreasing_by all_goals simp_wf <;> omega

def FieldFact.optionBytes : Option (List FieldFact) → ByteArray
  | none => Encoding.tag 0
  | some facts => Encoding.tag 1 ++ Encoding.nat facts.length ++
      FieldFact.payloadBytes facts
termination_by facts => sizeOf facts
decreasing_by all_goals simp_wf <;> omega

end

/-- One result heap shape. A constructor may carry exact recursively refined
field facts; `none` retains only its identity and deliberately means unknown
contents. -/
inductive HeapShape where
  | ctor (identity : CtorId) (fields : Option (List FieldFact))
  | pap (function : Address) (supplied : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

namespace HeapShape

private def compareFields : Option (List FieldFact) →
    Option (List FieldFact) → Ordering
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some left, some right => compareList FieldFact.compare left right

def compare : HeapShape → HeapShape → Ordering
  | .ctor left leftFields, .ctor right rightFields =>
      match compareCtor left right with
      | .lt => .lt
      | .gt => .gt
      | .eq => compareFields leftFields rightFields
  | .ctor _ _, .pap _ _ => .lt
  | .pap _ _, .ctor _ _ => .gt
  | .pap leftFunction leftSupplied, .pap rightFunction rightSupplied =>
      match Ixon.Merkle.compareAddress leftFunction rightFunction with
      | .lt => .lt
      | .gt => .gt
      | .eq => compareNat leftSupplied rightSupplied

private def insert (shape : HeapShape) : List HeapShape → List HeapShape
  | [] => [shape]
  | head :: tail =>
      match compare shape head with
      | .lt => shape :: head :: tail
      | .eq =>
          if shape == head then head :: tail
          else shape :: head :: tail
      | .gt => head :: insert shape tail

def normalize (shapes : List HeapShape) : List HeapShape :=
  shapes.foldr insert []

private theorem mem_insert_of_mem {needle shape : HeapShape}
    {shapes : List HeapShape} (h : needle ∈ shapes) :
    needle ∈ insert shape shapes := by
  induction shapes with
  | nil => contradiction
  | cons head tail ih =>
      cases hcompare : compare shape head with
      | lt =>
          rw [insert, hcompare]
          exact List.mem_cons.mpr (Or.inr h)
      | eq =>
          by_cases heq : shape = head
          · rw [insert, hcompare, if_pos ((beq_iff_eq).mpr heq)]
            exact h
          · rw [insert, hcompare, if_neg (by simpa using heq)]
            exact List.mem_cons.mpr (Or.inr h)
      | gt =>
          rw [insert, hcompare]
          rcases List.mem_cons.mp h with hhead | htail
          · exact List.mem_cons.mpr (Or.inl hhead)
          · exact List.mem_cons.mpr (Or.inr (ih htail))

private theorem mem_insert_self (shape : HeapShape)
    (shapes : List HeapShape) : shape ∈ insert shape shapes := by
  induction shapes with
  | nil => simp [insert]
  | cons head tail ih =>
      cases hcompare : compare shape head with
      | lt =>
          rw [insert, hcompare]
          exact List.mem_cons.mpr (Or.inl rfl)
      | eq =>
          by_cases heq : shape = head
          · rw [insert, hcompare, if_pos ((beq_iff_eq).mpr heq)]
            exact List.mem_cons.mpr (Or.inl heq)
          · rw [insert, hcompare, if_neg (by simpa using heq)]
            exact List.mem_cons.mpr (Or.inl rfl)
      | gt =>
          rw [insert, hcompare]
          exact List.mem_cons.mpr (Or.inr ih)

theorem mem_normalize_of_mem {shape : HeapShape} {shapes : List HeapShape}
    (h : shape ∈ shapes) : shape ∈ normalize shapes := by
  unfold normalize
  induction shapes with
  | nil => contradiction
  | cons head tail ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with hhead | htail
      · subst head
        exact mem_insert_self shape _
      · exact mem_insert_of_mem (ih htail)

def fieldFactsLe : List FieldFact → List FieldFact → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.le right && fieldFactsLe lefts rights
  | _, _ => false

/-- One detailed constructor shape is below an identity-only shape; detailed
shapes compare field facts pointwise. -/
def le : HeapShape → HeapShape → Bool
  | .ctor left leftFields, .ctor right rightFields =>
      left == right &&
        match rightFields with
        | none => true
        | some rightFacts =>
            match leftFields with
            | none => false
            | some leftFacts => fieldFactsLe leftFacts rightFacts
  | .pap leftFunction leftSupplied, .pap rightFunction rightSupplied =>
      leftFunction == rightFunction && leftSupplied == rightSupplied
  | _, _ => false

def canonical : HeapShape → Bool
  | .ctor _ none | .pap _ _ => true
  | .ctor _ (some fields) => fields.all FieldFact.canonical

def bytes : HeapShape → ByteArray
  | .ctor identity fields => Encoding.tag 0 ++
      Encoding.address identity.block ++ Encoding.nat identity.indIdx ++
        Encoding.nat identity.cidx ++
          match fields with
          | none => Encoding.tag 0
          | some facts => Encoding.tag 1 ++ Encoding.list FieldFact.bytes facts
  | .pap function supplied => Encoding.tag 1 ++
      Encoding.address function ++ Encoding.nat supplied

def toFieldShape : HeapShape → FieldShape
  | .ctor identity fields => .ctor identity fields
  | .pap function supplied => .pap function supplied

end HeapShape

/-- A finite result-shape fact. `unknownHeap` means every constructor/PAP
shape is possible; canonical facts omit the then-redundant explicit list. -/
structure Fact where
  mayScalar : Bool
  unknownHeap : Bool
  shapes : List HeapShape
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

namespace Fact

def bottom : Fact := ⟨false, false, []⟩
def scalar : Fact := ⟨true, false, []⟩
def heap (shape : HeapShape) : Fact := ⟨false, false, [shape]⟩
def top : Fact := ⟨true, true, []⟩

/-- Recover a constructor identity only when the fact excludes scalars,
unknown heap values, PAPs, and every competing heap shape.  Field detail is
irrelevant to identity provenance, so both identity-only and recursively
refined constructor shapes qualify. -/
def exactConstructor? : Fact → Option CtorId
  | ⟨false, false, [.ctor identity _]⟩ => some identity
  | _ => none

theorem exactConstructor?_eq_some {fact : Fact} {identity : CtorId}
    (h : fact.exactConstructor? = some identity) :
    ∃ fields,
      fact = ⟨false, false, [.ctor identity fields]⟩ := by
  unfold exactConstructor? at h
  split at h <;> simp_all

def normalize (fact : Fact) : Fact :=
  if fact.unknownHeap then
    { fact with shapes := [] }
  else
    { fact with shapes := HeapShape.normalize fact.shapes }

def canonical (fact : Fact) : Bool :=
  fact == fact.normalize && fact.shapes.all HeapShape.canonical

/-- Executable subset on the abstract domain. -/
def le (left right : Fact) : Bool :=
  (!left.mayScalar || right.mayScalar) &&
    (right.unknownHeap ||
      (!left.unknownHeap &&
        left.shapes.all fun leftShape =>
          right.shapes.any (HeapShape.le leftShape)))

def join (left right : Fact) : Fact :=
  normalize
    { mayScalar := left.mayScalar || right.mayScalar
      unknownHeap := left.unknownHeap || right.unknownHeap
      shapes := left.shapes ++ right.shapes }

def joins : List Fact → Fact
  | [] => bottom
  | fact :: facts => fact.join (joins facts)

/-- Forget the current identity of any heap result while preserving exact
scalar-only information. Primitive operations may mutate or consume a
location still named by an older environment slot; without a separate alias
domain, retaining that slot's finite constructor/PAP set is unsound. -/
def forgetHeap (fact : Fact) : Fact :=
  if fact.unknownHeap || !fact.shapes.isEmpty then
    { mayScalar := fact.mayScalar, unknownHeap := true, shapes := [] }
  else
    fact

def bytes (fact : Fact) : ByteArray :=
  Encoding.bool fact.mayScalar ++ Encoding.bool fact.unknownHeap ++
    Encoding.list HeapShape.bytes fact.shapes

end Fact

namespace FieldFact

/-- Preserve a result fact as one recursively refined constructor field. -/
def ofFact (fact : Fact) : FieldFact :=
  normalize
    { mayScalar := fact.mayScalar
      unknownHeap := fact.unknownHeap
      shapes := fact.shapes.map HeapShape.toFieldShape }

end FieldFact

namespace FieldShape

def toHeapShape : FieldShape → HeapShape
  | .ctor identity fields => .ctor identity fields
  | .pap function supplied => .pap function supplied

end FieldShape

namespace FieldFact

/-- Re-root a fetched field, preserving every bounded nested refinement. -/
def toFact (fact : FieldFact) : Fact :=
  Fact.normalize
    { mayScalar := fact.mayScalar
      unknownHeap := fact.unknownHeap
      shapes := fact.shapes.map FieldShape.toHeapShape }

end FieldFact

namespace HeapShape

/-- Result fact for a successful fetch from this possible shape.  Missing
detail widens; a known out-of-range field and PAP nodes cannot produce a
successful concrete fetch. -/
def fetch (field : Nat) : HeapShape → Fact
  | .ctor _ none => Fact.top
  | .ctor _ (some fields) =>
      match fields[field]? with
      | some fact => fact.toFact
      | none => Fact.bottom
  | .pap _ _ => Fact.bottom

end HeapShape

namespace Fact

/-- Field-sensitive transfer for non-consuming constructor projection. -/
def fetch (fact : Fact) (field : Nat) : Fact :=
  if fact.unknownHeap then top
  else joins (fact.shapes.map (HeapShape.fetch field))

/-! ### Case-binder field recovery -/

end Fact

namespace HeapShape

/-- Abstract field vector contributed by one possible heap shape to a case
alternative.  Constructor tags are filtered before their fields participate;
identity-only shapes retain no field information, and detailed vectors with a
different arity cannot reach a successful execution of this alternative.  The
result is already reversed into the evaluator's de Bruijn binding order. -/
def caseFields (cidx fieldCount : Nat) : HeapShape → List Fact
  | .ctor identity none =>
      if identity.cidx == cidx then
        List.replicate fieldCount Fact.top
      else
        List.replicate fieldCount Fact.bottom
  | .ctor identity (some fields) =>
      if identity.cidx == cidx && fields.length == fieldCount then
        (fields.map FieldFact.toFact).reverse
      else
        List.replicate fieldCount Fact.bottom
  | .pap _ _ => List.replicate fieldCount Fact.bottom

end HeapShape

namespace Fact

/-- Heads of the nonempty vectors in a candidate family. -/
def vectorHeads : List (List Fact) → List Fact
  | [] => []
  | [] :: vectors => vectorHeads vectors
  | (fact :: _) :: vectors => fact :: vectorHeads vectors

/-- Tails of the nonempty vectors in a candidate family. -/
def vectorTails : List (List Fact) → List (List Fact)
  | [] => []
  | [] :: vectors => vectorTails vectors
  | (_ :: facts) :: vectors => facts :: vectorTails vectors

/-- Pointwise join of equally sized case-field candidates.  The explicit
length keeps the result arity exact even when the branch is abstractly
unreachable and the candidate family is empty. -/
def joinFieldVectors : Nat → List (List Fact) → List Fact
  | 0, _ => []
  | fieldCount + 1, vectors =>
      Fact.joins (vectorHeads vectors) ::
        joinFieldVectors fieldCount (vectorTails vectors)

/-- Scalar contribution to one case alternative.  Only unary tag `1` can bind
a value through Nat peeling, and that predecessor is exactly scalar. -/
def scalarCaseFields (peelNat : Bool) (cidx fieldCount : Nat) : List Fact :=
  if peelNat && cidx == 1 && fieldCount == 1 then
    [Fact.scalar]
  else
    List.replicate fieldCount Fact.bottom

/-- Facts installed for an alternative's field binders.  Finite constructor
shapes contribute only when their tag and detailed arity match; multiple
possible shapes join pointwise.  An identity-only matching constructor or an
unknown heap widens every binder, while a possible peeled successor joins its
precise scalar predecessor. -/
def caseFields (fact : Fact) (peelNat : Bool)
    (cidx fieldCount : Nat) : List Fact :=
  if fact.unknownHeap then
    List.replicate fieldCount Fact.top
  else
    let heapCandidates :=
      fact.shapes.map (HeapShape.caseFields cidx fieldCount)
    let candidates :=
      if fact.mayScalar then
        scalarCaseFields peelNat cidx fieldCount :: heapCandidates
      else
        heapCandidates
    joinFieldVectors fieldCount candidates

#guard (heap (.pap (Address.replicate 0x11) 1)).canonical
#guard (join scalar
  (heap (.ctor ⟨Address.replicate 0x22, 0, 1⟩ none))).canonical
#guard (join top (heap (.pap (Address.replicate 0x33) 2))) == top
#guard (heap (.pap (Address.replicate 0x44) 1)).le top
#guard !top.le scalar
#guard (heap (.ctor ⟨Address.replicate 0x55, 0, 0⟩
  (some [FieldFact.scalar]))).fetch 0 == scalar
#guard (heap (.ctor ⟨Address.replicate 0x55, 0, 0⟩ none)).fetch 0 == top
#guard (heap (.ctor ⟨Address.replicate 0x55, 0, 0⟩ none)).forgetHeap ==
  ⟨false, true, []⟩
#guard scalar.forgetHeap == scalar
#guard (heap (.ctor ⟨Address.replicate 0x56, 0, 3⟩
  (some [FieldFact.scalar]))).caseFields false 3 1 == [scalar]
#guard (heap (.ctor ⟨Address.replicate 0x56, 0, 3⟩
  (some [FieldFact.scalar]))).caseFields false 4 1 == [bottom]
#guard (heap (.ctor ⟨Address.replicate 0x56, 0, 3⟩ none)).caseFields
  false 3 2 == [top, top]
#guard scalar.caseFields true 1 1 == [scalar]
#guard scalar.caseFields false 1 1 == [bottom]

end Fact

/-! ## Untrusted certificate format -/

/-- Candidate facts for one stable/ordinary/mutual program artifact. Member
order is part of the certificate and must exactly match the program artifact. -/
structure CandidateArtifact where
  programIdentity : Address
  members : List (Address × Fact)
  deriving BEq, Repr, Inhabited

/-- The complete untrusted post-fixpoint claim. -/
structure Certificate where
  artifacts : List CandidateArtifact
  deriving BEq, Repr, Inhabited

/-- Deterministic admission limits for the already-addressed graph and the
untrusted fact claim. Per-fact shape limits apply independently to result and
recursive field facts because canonicalization currently sorts finite shape
sets by insertion. Depth, total-shape, and total-field limits bound later
interpretation and content-addressing work. -/
structure Limits where
  maxProgramArtifacts : Nat := 32 * 1024
  maxProgramMembers : Nat := 32 * 1024
  maxCertificateArtifacts : Nat := 32 * 1024
  maxCertificateMembers : Nat := 32 * 1024
  maxShapesPerFact : Nat := 256
  maxShapes : Nat := 64 * 1024
  maxFieldsPerShape : Nat := 256
  maxFields : Nat := 64 * 1024
  maxFieldDepth : Nat := 64
  /-- Inclusive bound on constructor coordinates and PAP fill counts.  The
  default includes the canonical-encoding fixture at `2^64` while preventing
  a candidate from forcing an effectively unbounded numeral encoding. -/
  maxShapeIndex : Nat := 2 ^ 64
  deriving BEq, Repr

def defaultLimits : Limits := {}

/-- Exact structural counts returned by successful HPT preflight. -/
structure Stats where
  programArtifacts : Nat := 0
  programMembers : Nat := 0
  certificateArtifacts : Nat := 0
  certificateMembers : Nat := 0
  shapes : Nat := 0
  fields : Nat := 0
  fieldDepth : Nat := 0
  deriving BEq, Repr

namespace Certificate

def summaries (certificate : Certificate) : List (Address × Fact) :=
  certificate.artifacts.flatMap fun artifact => artifact.members

end Certificate

/-! ## Abstract interpreter -/

abbrev DeclEnv := Address → Option Decl
abbrev SummaryEnv := Address → Option Fact

def resolveAtomFact (environment : List Fact) : Atom → Except String Fact
  | .var index =>
      match environment[index]? with
      | some fact => .ok fact
      | none => .error s!"HPT unbound variable {index}"
  | .lit _ | .erased => .ok Fact.scalar

def resolveAtomFacts (environment : List Fact)
    (atoms : Array Atom) : Except String (List Fact) :=
  atoms.foldlM (fun accumulated atom => do
    pure (accumulated ++ [← resolveAtomFact environment atom])) []

def callableResult (declarations : DeclEnv)
    (summaries : SummaryEnv) (function : Address) : Except String Fact :=
  match declarations function with
  | none => .error s!"HPT call target is absent: {Address.toHex function}"
  | some (.extern _) => .ok Fact.scalar
  | some (.fn _) =>
      match summaries function with
      | some fact => .ok fact
      | none => .error s!"HPT function summary is absent: {Address.toHex function}"

/-- Transfer one possible callable shape.  `recur` is the preceding-fuel
instance of `applyFact`; separating it makes the finite-shape fold transparent
to the semantic proof without changing the executable domain. -/
def applyShapeFact (declarations : DeclEnv) (summaries : SummaryEnv)
    (recur : Fact → Nat → Except String Fact) (argumentCount : Nat) :
    HeapShape → Except String Fact
  | .ctor _ _ => .ok Fact.bottom
  | .pap function supplied =>
      match declarations function with
      | none =>
          .error s!"HPT pap target is absent: {Address.toHex function}"
      | some declaration => do
          let arity := declArity declaration
          if supplied < arity then
            let total := supplied + argumentCount
            if total < arity then
              return Fact.heap (.pap function total)
            else
              let returned ← callableResult declarations summaries function
              if total == arity then
                return returned
              else
                recur returned (total - arity)
          else
            return Fact.bottom

/-- Join the transfers of a finite shape set. -/
def applyShapeFacts
    (step : HeapShape → Except String Fact) :
    List HeapShape → Except String Fact
  | [] => .ok Fact.bottom
  | shape :: shapes => do
      let head ← step shape
      let tail ← applyShapeFacts step shapes
      return head.join tail

/-- Conservative abstract execution of `applyGo`. Exact PAP fill counts make
under/exact/over-application finite; fuel is a fail-safe for junk over-approximate
facts and widens to `top` rather than rejecting a sound certificate. -/
def applyFact (declarations : DeclEnv) (summaries : SummaryEnv) :
    Nat → Fact → Nat → Except String Fact
  | 0, _, _ => .ok Fact.top
  | fuel + 1, functionFact, argumentCount => do
      if functionFact.unknownHeap then
        return Fact.top
      let scalar :=
        if functionFact.mayScalar then Fact.scalar else Fact.bottom
      let heap ← applyShapeFacts
        (applyShapeFact declarations summaries
          (applyFact declarations summaries fuel) argumentCount)
        functionFact.shapes
      return scalar.join heap

mutual

def analyzeCode (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) (environment : List Fact) :
    Code → Except String Fact
  | .ret atom => resolveAtomFact environment atom
  | .letOp operation rest => do
      let bound ← analyzeOp declarations summaries owner current environment
        operation
      analyzeCode declarations summaries owner current
        (bound :: environment.map Fact.forgetHeap) rest
  | .case scrutinee peelNat alternatives => do
      let scrutineeFact ← resolveAtomFact environment scrutinee
      analyzeAlternatives declarations summaries owner current scrutineeFact
        peelNat environment alternatives.toList

def analyzeAlternatives (declarations : DeclEnv)
    (summaries : SummaryEnv) (owner : Address) (current : FnDef)
    (scrutinee : Fact) (peelNat : Bool)
    (environment : List Fact) : List Alt → Except String Fact
  | [] => .ok Fact.bottom
  | .mk cidx fields body :: rest => do
      let branch ← analyzeCode declarations summaries owner current
        (scrutinee.caseFields peelNat cidx fields ++ environment) body
      let remaining ← analyzeAlternatives declarations summaries owner current
        scrutinee peelNat environment rest
      return branch.join remaining

def analyzeOp (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) (environment : List Fact) :
    Op → Except String Fact
  | .pure atom => resolveAtomFact environment atom
  | .alloc _ identity arguments => do
      let fields ← resolveAtomFacts environment arguments
      return Fact.heap (.ctor identity (some (fields.map FieldFact.ofFact)))
  | .reuse target identity arguments => do
      let fields ← resolveAtomFacts environment arguments
      let _ ← resolveAtomFact environment target
      return Fact.heap (.ctor identity
        (some (fields.map fun fact => FieldFact.ofFact fact.forgetHeap)))
  | .free target | .drop target | .dropU target => do
      let _ ← resolveAtomFact environment target
      return Fact.scalar
  | .dup target => do
      let _ ← resolveAtomFact environment target
      return Fact.top
  | .fetch target field => do
      let fact ← resolveAtomFact environment target
      return fact.fetch field
  | .call function arguments => do
      let _ ← resolveAtomFacts environment arguments
      match declarations function with
      | none => throw s!"HPT call target is absent: {Address.toHex function}"
      | some declaration =>
          if arguments.size != declArity declaration then
            throw s!"HPT call arity mismatch at {Address.toHex function}"
          callableResult declarations summaries function
  | .callSelf arguments => do
      let _ ← resolveAtomFacts environment arguments
      if arguments.size != current.arity then
        throw s!"HPT callSelf arity mismatch at {Address.toHex owner}"
      match summaries owner with
      | some fact => return fact
      | none => throw s!"HPT self summary is absent: {Address.toHex owner}"
  | .papp function arguments => do
      let _ ← resolveAtomFacts environment arguments
      match declarations function with
      | none => throw s!"HPT pap target is absent: {Address.toHex function}"
      | some declaration =>
          if arguments.size < declArity declaration then
            return Fact.heap (.pap function arguments.size)
          throw s!"HPT saturating papp at {Address.toHex function}"
  | .apply function arguments => do
      let functionFact ← resolveAtomFact environment function
      let _ ← resolveAtomFacts environment arguments
      applyFact declarations summaries (arguments.size + 1) functionFact
        arguments.size
  | .extern _ arguments => do
      let _ ← resolveAtomFacts environment arguments
      return Fact.scalar

end

def inferFunction (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (function : FnDef) : Except String Fact :=
  analyzeCode declarations summaries owner function
    (List.replicate function.arity Fact.top) function.body

/-! ## Executable post-fixpoint checker -/

private def allUnique (addresses : List Address) : Bool :=
  ((AddressEnv.build (addresses.map fun address => (address, ()))).size ==
    addresses.length)

def programIdentity : ReaddressAll.Artifact → Address
  | .stable address _ | .ordinary address _ => address
  | .mutual block => block.blockAddress

def programMembers (artifact : ReaddressAll.Artifact) :
    List (Address × Decl) :=
  artifact.declarations

/-- Flattened declaration rows used by both the checker and its semantic
interface. -/
def declarationEntries (program : List ReaddressAll.Artifact) :
    List (Address × Decl) :=
  program.flatMap programMembers

/-- Runtime declaration environment committed to by an addressed program. -/
def programDeclEnv (program : List ReaddressAll.Artifact) : DeclEnv :=
  AddressEnv.lookup (AddressEnv.build (declarationEntries program))

/-- Lookup form of the untrusted summary rows.  It becomes trusted only under
`Certificate.postFixpoint`. -/
def Certificate.summaryEnv (certificate : Certificate) : SummaryEnv :=
  AddressEnv.lookup (AddressEnv.build certificate.summaries)

private def enforce (label : String) (actual limit : Nat) :
    Except String Unit :=
  if actual ≤ limit then .ok ()
  else .error s!"HPT {label} budget exceeded: {actual} > {limit}"

private def enforceShapeIndex (label : String) (actual limit : Nat) :
    Except String Unit :=
  if actual ≤ limit then .ok ()
  else .error s!"HPT {label} exceeds the configured shape-index limit {limit}"

structure PayloadStats where
  shapes : Nat := 0
  fields : Nat := 0
  fieldDepth : Nat := 0
  deriving BEq, Repr, Inhabited

mutual

private def scanFieldFact (limits : Limits) (depth : Nat)
    (fact : FieldFact) (state : PayloadStats) : Except String PayloadStats := do
  enforce "field-depth" depth limits.maxFieldDepth
  let state := { state with fieldDepth := max state.fieldDepth depth }
  scanFieldShapes limits depth fact.shapes 0 state
termination_by sizeOf fact
decreasing_by
  cases fact
  simp_wf

private def scanFieldShapes (limits : Limits) (depth : Nat) :
    List FieldShape → Nat → PayloadStats → Except String PayloadStats
  | [], _, state => .ok state
  | shape :: shapes, localShapes, state => do
      let localShapes := localShapes + 1
      enforce "shapes-per-field-fact" localShapes limits.maxShapesPerFact
      let state := { state with shapes := state.shapes + 1 }
      enforce "total-shape" state.shapes limits.maxShapes
      let state ← scanFieldShape limits depth shape state
      scanFieldShapes limits depth shapes localShapes state
termination_by shapes _ _ => sizeOf shapes
decreasing_by all_goals simp_wf <;> omega

private def scanFieldShape (limits : Limits) (depth : Nat) :
    FieldShape → PayloadStats → Except String PayloadStats
  | .ctor identity fields, state => do
      enforceShapeIndex "field constructor inductive index" identity.indIdx
        limits.maxShapeIndex
      enforceShapeIndex "field constructor index" identity.cidx
        limits.maxShapeIndex
      match fields with
      | none => pure state
      | some fields => scanFieldVector limits (depth + 1) fields 0 state
  | .pap _ supplied, state => do
      enforceShapeIndex "field PAP supplied-argument count" supplied
        limits.maxShapeIndex
      pure state
termination_by shape _ => sizeOf shape
decreasing_by all_goals simp_wf <;> omega

private def scanFieldVector (limits : Limits) (depth : Nat) :
    List FieldFact → Nat → PayloadStats → Except String PayloadStats
  | [], _, state => .ok state
  | fact :: facts, localFields, state => do
      let localFields := localFields + 1
      enforce "fields-per-constructor-shape" localFields
        limits.maxFieldsPerShape
      let state := { state with fields := state.fields + 1 }
      enforce "total-constructor-field" state.fields limits.maxFields
      let state ← scanFieldFact limits depth fact state
      scanFieldVector limits depth facts localFields state
termination_by facts _ _ => sizeOf facts
decreasing_by all_goals simp_wf <;> omega

end


/-- Check and count one recursive result-fact payload independently of graph
coverage. The deterministic producer reuses this exact gate before accepting a
round, so producer widening and untrusted checker admission share one domain
boundary. -/
def checkFactPayload (limits : Limits) (fact : Fact) :
    Except String PayloadStats := do
  let mut state : PayloadStats := {}
  let mut factShapes := 0
  for shape in fact.shapes do
    factShapes := factShapes + 1
    enforce "shapes-per-fact" factShapes limits.maxShapesPerFact
    state := { state with shapes := state.shapes + 1 }
    enforce "total-shape" state.shapes limits.maxShapes
    match shape with
    | .ctor identity fieldFacts =>
        enforceShapeIndex "constructor inductive index" identity.indIdx
          limits.maxShapeIndex
        enforceShapeIndex "constructor index" identity.cidx
          limits.maxShapeIndex
        match fieldFacts with
        | none => pure ()
        | some fieldFacts =>
            state ← scanFieldVector limits 1 fieldFacts 0 state
    | .pap _ supplied =>
        enforceShapeIndex "PAP supplied-argument count" supplied
          limits.maxShapeIndex
  return state

/-- Linear, early-exit admission scan.  It runs before canonicalization,
post-fixpoint interpretation, uniqueness checks, or hashing. -/
def preflight (limits : Limits) (program : List ReaddressAll.Artifact)
    (certificate : Certificate) : Except String Stats := do
  let mut programArtifacts := 0
  let mut programMemberCount := 0
  for artifact in program do
    programArtifacts := programArtifacts + 1
    enforce "program-artifact" programArtifacts limits.maxProgramArtifacts
    for _ in programMembers artifact do
      programMemberCount := programMemberCount + 1
      enforce "program-member" programMemberCount limits.maxProgramMembers
  let mut certificateArtifacts := 0
  let mut certificateMembers := 0
  let mut shapes := 0
  let mut fields := 0
  let mut fieldDepth := 0
  for artifact in certificate.artifacts do
    certificateArtifacts := certificateArtifacts + 1
    enforce "certificate-artifact" certificateArtifacts
      limits.maxCertificateArtifacts
    for member in artifact.members do
      certificateMembers := certificateMembers + 1
      enforce "certificate-member" certificateMembers
        limits.maxCertificateMembers
      let payload ← checkFactPayload limits member.2
      shapes := shapes + payload.shapes
      fields := fields + payload.fields
      fieldDepth := max fieldDepth payload.fieldDepth
      enforce "total-shape" shapes limits.maxShapes
      enforce "total-constructor-field" fields limits.maxFields
  return { programArtifacts
           programMembers := programMemberCount
           certificateArtifacts
           certificateMembers
           shapes
           fields
           fieldDepth }

/-- Universal conservative candidate. It is useful as a fail-safe producer
and as a baseline for measuring whether an external analysis adds precision;
the ordinary checker still validates code well-formedness and coverage. -/
def Certificate.top (program : List ReaddressAll.Artifact) : Certificate :=
  ⟨program.map fun artifact =>
    { programIdentity := programIdentity artifact
      members := (programMembers artifact).map fun member =>
        (member.1, match member.2 with
          | .extern _ => Fact.scalar
          | .fn _ => Fact.top) }⟩

def checkMember (declarations : DeclEnv) (summaries : SummaryEnv) :
    (Address × Decl) → (Address × Fact) → Bool
  | (address, declaration), (claimedAddress, claimed) =>
      address == claimedAddress && claimed.canonical &&
        match declaration with
        | .extern _ => claimed == Fact.scalar
        | .fn function =>
            match inferFunction declarations summaries address function with
            | .ok inferred => inferred.le claimed
            | .error _ => false

private def checkMembers (declarations : DeclEnv) (summaries : SummaryEnv) :
    List (Address × Decl) → List (Address × Fact) → Bool
  | [], [] => true
  | declaration :: declarations', summary :: summaries' =>
      checkMember declarations summaries declaration summary &&
        checkMembers declarations summaries declarations' summaries'
  | _, _ => false

private def checkArtifacts (declarations : DeclEnv) (summaries : SummaryEnv) :
    List ReaddressAll.Artifact → List CandidateArtifact → Bool
  | [], [] => true
  | program :: programs, candidate :: candidates =>
      candidate.programIdentity == programIdentity program &&
        checkMembers declarations summaries (programMembers program)
          candidate.members &&
        checkArtifacts declarations summaries programs candidates
  | _, _ => false

namespace CandidateArtifact

/-- Artifact-local post-fixpoint check against a summary environment that
already contains this candidate's own rows and all prior dependencies. This is
the cache-ingress primitive; the whole-program checker remains the final
authority for global uniqueness, ordering, and coverage. -/
def localPostFixpoint (declarations : DeclEnv) (summaries : SummaryEnv)
    (program : ReaddressAll.Artifact) (candidate : CandidateArtifact) : Bool :=
  candidate.programIdentity == Ix.Compiler.IxIR1.HPT.programIdentity program &&
    checkMembers declarations summaries (programMembers program)
      candidate.members

end CandidateArtifact

/-- Redundant pointwise spelling of the local checks.  Artifact alignment is
still checked separately; this row-indexed form gives the semantic theorem a
direct elimination principle for any successful environment lookup. -/
def checkLocalRows (declarations : DeclEnv) (summaries : SummaryEnv) :
    List (Address × Decl) → Bool
  | [] => true
  | (address, declaration) :: entries =>
      (match summaries address with
      | none => false
      | some claimed =>
          checkMember declarations summaries (address, declaration)
            (address, claimed)) &&
        checkLocalRows declarations summaries entries

/-- The complete executable certificate condition. Besides the local
post-fixpoint inclusions it requires exact artifact/member coverage, canonical
facts, and globally unique producer and summary keys. -/
def Certificate.postFixpoint (program : List ReaddressAll.Artifact)
    (certificate : Certificate) : Bool :=
  let declarationsList := declarationEntries program
  let summariesList := certificate.summaries
  let declarations := programDeclEnv program
  let summaries := certificate.summaryEnv
  program.all ReaddressAll.Artifact.contentAddressed &&
    allUnique (program.map programIdentity) &&
    allUnique (declarationsList.map (·.1)) &&
    allUnique (summariesList.map (·.1)) &&
    checkLocalRows declarations summaries declarationsList &&
    checkArtifacts declarations summaries program certificate.artifacts

/-! ## Content-addressed checked summaries -/

inductive ArtifactKind where
  | stable
  | ordinary
  | mutual
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

namespace ArtifactKind

def tag : ArtifactKind → UInt8
  | .stable => 0
  | .ordinary => 1
  | .mutual => 2

def ofProgram : ReaddressAll.Artifact → ArtifactKind
  | .stable _ _ => .stable
  | .ordinary _ _ => .ordinary
  | .mutual _ => .mutual

end ArtifactKind

def normalizeAddresses (addresses : List Address) : List Address :=
  Ixon.Merkle.dedupSorted
    (Ixon.Merkle.sortAddresses addresses.toArray) |>.toList

/-- One checked, cache-addressed SCC summary. -/
structure Artifact where
  kind : ArtifactKind
  programIdentity : Address
  members : List (Address × Fact)
  /-- Sorted, deduplicated checked summary-artifact dependencies. -/
  dependencies : List Address
  cacheKey : Address
  address : Address
  deriving BEq, Repr, Inhabited

namespace Artifact

def cacheKeyDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/hpt-cache-key/3" ++ Encoding.tag 0

def summaryDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/hpt-summary/3" ++ Encoding.tag 0

private def memberBytes (member : Address × Fact) : ByteArray :=
  Encoding.address member.1 ++ member.2.bytes

def cacheKeyPreimage (kind : ArtifactKind) (programIdentity : Address)
    (dependencies : List Address) : ByteArray :=
  cacheKeyDomain ++ Encoding.tag kind.tag ++
    Encoding.address programIdentity ++
    Encoding.list Encoding.address dependencies

def summaryPreimage (cacheKey : Address)
    (members : List (Address × Fact)) : ByteArray :=
  summaryDomain ++ Encoding.address cacheKey ++
    Encoding.list memberBytes members

def expectedCacheKey (artifact : Artifact) : Address :=
  Address.blake3
    (cacheKeyPreimage artifact.kind artifact.programIdentity
      artifact.dependencies)

def expectedAddress (artifact : Artifact) : Address :=
  Address.blake3 (summaryPreimage artifact.cacheKey artifact.members)

def graphShapeAudit (artifact : Artifact) : Bool :=
  match artifact.kind, artifact.members with
  | .stable, [(address, _)] | .ordinary, [(address, _)] =>
      address == artifact.programIdentity
  | .mutual, _ =>
      !artifact.members.isEmpty &&
        !artifact.members.any fun member =>
          member.1 == artifact.programIdentity
  | _, _ => false

def semanticAudit (artifact : Artifact) : Bool :=
  artifact.graphShapeAudit &&
    artifact.dependencies == normalizeAddresses artifact.dependencies &&
    artifact.members.all (fun member => member.2.canonical) &&
    artifact.cacheKey == artifact.expectedCacheKey &&
    artifact.address == artifact.expectedAddress

end Artifact

/-- Cache query determined solely by one program artifact and the checked
addresses of its already available dependency summaries. -/
structure Query where
  kind : ArtifactKind
  programIdentity : Address
  dependencies : List Address
  cacheKey : Address
  deriving BEq, Repr, Inhabited

namespace Query

def agreesWith (query : Query) (artifact : Artifact) : Bool :=
  artifact.kind == query.kind &&
    artifact.programIdentity == query.programIdentity &&
    artifact.dependencies == query.dependencies &&
    artifact.cacheKey == query.cacheKey

end Query

namespace Artifact

/-- Materialize candidate members under an already-derived cache query. -/
def ofQuery (query : Query) (members : List (Address × Fact)) : Artifact :=
  { kind := query.kind
    programIdentity := query.programIdentity
    members
    dependencies := query.dependencies
    cacheKey := query.cacheKey
    address := Address.blake3 (summaryPreimage query.cacheKey members) }

end Artifact

/-- Checked summaries in dependency order. -/
structure Result where
  artifacts : List Artifact
  deriving BEq, Repr, Inhabited

namespace Result

def summaries (result : Result) : List (Address × Fact) :=
  result.artifacts.flatMap fun artifact => artifact.members

def cacheKeys (result : Result) : List Address :=
  result.artifacts.map (·.cacheKey)

def addresses (result : Result) : List Address :=
  result.artifacts.map (·.address)

private def dependencyOrderAudit : List Artifact → List Address → Bool
  | [], _ => true
  | artifact :: artifacts, available =>
      artifact.dependencies.all available.contains &&
        dependencyOrderAudit artifacts (artifact.address :: available)

def semanticAudit (result : Result) : Bool :=
  result.artifacts.all Artifact.semanticAudit &&
    allUnique (result.artifacts.map (·.programIdentity)) &&
    allUnique (result.summaries.map (·.1)) &&
    allUnique result.cacheKeys && allUnique result.addresses &&
    dependencyOrderAudit result.artifacts []

end Result

private def lookupOwner (owners : List (Address × Address))
    (address : Address) : Option Address :=
  (owners.find? fun entry => entry.1 == address).map (·.2)

def dependencyAddresses (declarations : DeclEnv)
    (owners : List (Address × Address))
    (members : List (Address × Decl)) : Except String (List Address) := do
  let localKeys := members.map (·.1)
  let references := members.flatMap fun member =>
    Readdress.Decl.references member.2
  let mut dependencies : List Address := []
  for reference in references do
    if !localKeys.contains reference then
      match declarations reference with
      | none => pure ()
      | some _ =>
          match lookupOwner owners reference with
          | some summary => dependencies := summary :: dependencies
          | none =>
              throw s!"HPT dependency summary is unavailable: {Address.toHex reference}"
  return normalizeAddresses dependencies

/-- Derive the exact persistent-cache lookup key for the next dependency-
ordered program artifact. `owners` maps already checked member identities to
their enclosing summary artifact address. -/
def Query.ofProgram (declarations : DeclEnv)
    (owners : List (Address × Address))
    (program : ReaddressAll.Artifact) : Except String Query := do
  let dependencies ← dependencyAddresses declarations owners
    (programMembers program)
  let kind := ArtifactKind.ofProgram program
  let identity := Ix.Compiler.IxIR1.HPT.programIdentity program
  pure (Query.mk kind identity dependencies
    (Address.blake3
      (Artifact.cacheKeyPreimage kind identity dependencies)))

private def sameCachePreimage (left right : Artifact) : Bool :=
  Artifact.cacheKeyPreimage left.kind left.programIdentity left.dependencies ==
    Artifact.cacheKeyPreimage right.kind right.programIdentity right.dependencies

private def sameSummaryPreimage (left right : Artifact) : Bool :=
  Artifact.summaryPreimage left.cacheKey left.members ==
    Artifact.summaryPreimage right.cacheKey right.members

def rejectCollision (built : List Artifact)
    (candidate : Artifact) : Except String Unit := do
  match built.find? fun artifact => artifact.cacheKey == candidate.cacheKey with
  | some existing =>
      unless sameCachePreimage existing candidate do
        throw s!"BLAKE3 collision between HPT cache keys {Address.toHex candidate.cacheKey}"
  | none => pure ()
  match built.find? fun artifact => artifact.address == candidate.address with
  | some existing =>
      unless sameSummaryPreimage existing candidate do
        throw s!"BLAKE3 collision between HPT summaries {Address.toHex candidate.address}"
  | none => pure ()

private structure BuildState where
  artifacts : List Artifact := []
  /-- Program member to checked summary-artifact address. -/
  owners : List (Address × Address) := []

private def materializeOne (declarations : DeclEnv) (state : BuildState)
    (program : ReaddressAll.Artifact) (candidate : CandidateArtifact) :
    Except String BuildState := do
  let query ← Query.ofProgram declarations state.owners program
  let artifact := Artifact.ofQuery query candidate.members
  let _ ← rejectCollision state.artifacts artifact
  return { artifacts := state.artifacts ++ [artifact]
           owners := state.owners ++ candidate.members.map (fun member =>
             (member.1, artifact.address)) }

private def materialize (declarations : DeclEnv) :
    List ReaddressAll.Artifact → List CandidateArtifact → BuildState →
      Except String BuildState
  | [], [], state => .ok state
  | program :: programs, candidate :: candidates, state => do
      let state ← materializeOne declarations state program candidate
      materialize declarations programs candidates state
  | _, _, _ => .error "internal: HPT certificate/program artifact arity drift"

/-- Check an untrusted whole-program result-shape post-fixpoint, then assign
granular cache and summary identities in dependency order. This is the
resource-configurable form of `run`. -/
def runWith (limits : Limits) (program : List ReaddressAll.Artifact)
    (certificate : Certificate) : Except String Result := do
  let _ ← preflight limits program certificate
  unless certificate.postFixpoint program do
    throw "HPT certificate is not a canonical whole-program post-fixpoint"
  let declarations := programDeclEnv program
  let state ← materialize declarations program certificate.artifacts {}
  let result : Result := ⟨state.artifacts⟩
  unless result.semanticAudit do
    throw "internal: checked HPT summaries failed their content-address audit"
  return result

/-- Check with the documented default structural limits. -/
def run (program : List ReaddressAll.Artifact)
    (certificate : Certificate) : Except String Result :=
  runWith defaultLimits program certificate

/-- Successful configurable materialization exposes the exact post-fixpoint
condition that gated it; no trust is placed in the producer of the candidate
facts. -/
theorem postFixpoint_of_runWith_eq_ok
    {limits : Limits} {program : List ReaddressAll.Artifact}
    {certificate : Certificate} {result : Result}
    (hrun : runWith limits program certificate = .ok result) :
    certificate.postFixpoint program = true := by
  unfold runWith at hrun
  simp only [bind, Except.bind] at hrun
  split at hrun
  · contradiction
  split at hrun
  · assumption
  · contradiction

/-- Every cache artifact returned under configurable limits passes the exact
content-address and dependency-order audit. -/
theorem semanticAudit_of_runWith_eq_ok
    {limits : Limits} {program : List ReaddressAll.Artifact}
    {certificate : Certificate} {result : Result}
    (hrun : runWith limits program certificate = .ok result) :
    result.semanticAudit = true := by
  unfold runWith at hrun
  simp only [bind, Except.bind] at hrun
  split at hrun
  · contradiction
  · split at hrun
    · next hpost =>
      split at hrun
      · contradiction
      · next state hmaterialize =>
        split at hrun
        · next haudit =>
          injection hrun with hresult
          subst result
          exact haudit
        · contradiction
    · contradiction

/-- Default-limit specialization of `postFixpoint_of_runWith_eq_ok`. -/
theorem postFixpoint_of_run_eq_ok
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {result : Result} (hrun : run program certificate = .ok result) :
    certificate.postFixpoint program = true := by
  apply postFixpoint_of_runWith_eq_ok (limits := defaultLimits)
  simpa [run] using hrun

/-- Default-limit specialization of `semanticAudit_of_runWith_eq_ok`. -/
theorem semanticAudit_of_run_eq_ok
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {result : Result} (hrun : run program certificate = .ok result) :
    result.semanticAudit = true := by
  apply semanticAudit_of_runWith_eq_ok (limits := defaultLimits)
  simpa [run] using hrun

end Ix.Compiler.IxIR1.HPT
