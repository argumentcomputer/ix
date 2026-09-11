import Ix.Compiler.IxIR1.HPT

/-!
# Semantic soundness of IxIR₁ heap-points-to facts

This module gives the executable HPT domain a concrete meaning over the
IxIR₁ evaluator's stores and runtime values. A finite constructor/PAP fact
describes a live node exactly; a detailed constructor additionally describes
its exact field vector recursively. `unknownHeap` deliberately accepts every
location, including a stale alias: primitive transfer forgets old finite heap
identities before interpreting the continuation, so store mutation cannot
invalidate an environment invariant.
-/

namespace Ix.Compiler.IxIR1.HPT

open Ix.Compiler.Ixon (Address)

mutual

/-- Recursive concrete interpretation of one field heap shape. -/
inductive FieldShape.Holds (declarations : DeclEnv) (store : Store) :
    FieldShape → RVal → Prop where
  | ctorIdentity
      (hget : store.get? location = some box)
      (hnode : box.node = .ctorN identity fields) :
      FieldShape.Holds declarations store (.ctor identity none) (.loc location)
  | ctorDetailed
      (hget : store.get? location = some box)
      (hnode : box.node = .ctorN identity fields)
      (hfields : FieldFactsHold declarations store facts fields.toList) :
      FieldShape.Holds declarations store
        (.ctor identity (some facts)) (.loc location)
  | pap
      (hget : store.get? location = some box)
      (hdeclaration : declarations function = some declaration)
      (hnode : box.node =
        .papN function (declArity declaration) arguments)
      (hsize : arguments.size = supplied)
      (hproper : supplied < declArity declaration) :
      FieldShape.Holds declarations store
        (.pap function supplied) (.loc location)

/-- Recursive fact interpretation. Scalar and unknown cases remain explicit;
finite heap evidence points to one recursively interpreted shape. -/
inductive FieldFact.Holds (declarations : DeclEnv) (store : Store) :
    FieldFact → RVal → Prop where
  | lit (hscalar : fact.mayScalar = true) :
      FieldFact.Holds declarations store fact (.lit literal)
  | erased (hscalar : fact.mayScalar = true) :
      FieldFact.Holds declarations store fact .erased
  | unknown (hunknown : fact.unknownHeap = true) :
      FieldFact.Holds declarations store fact (.loc location)
  | heap (hmember : shape ∈ fact.shapes)
      (hshape : FieldShape.Holds declarations store shape (.loc location)) :
      FieldFact.Holds declarations store fact (.loc location)

/-- Pointwise interpretation of an exact recursive field vector. -/
inductive FieldFactsHold (declarations : DeclEnv) (store : Store) :
    List FieldFact → List RVal → Prop where
  | nil : FieldFactsHold declarations store [] []
  | cons : fact.Holds declarations store value →
      FieldFactsHold declarations store facts values →
      FieldFactsHold declarations store (fact :: facts) (value :: values)

end

private theorem FieldFact.shape_size_lt {fact : FieldFact}
    {shape : FieldShape} (h : shape ∈ fact.shapes) :
    sizeOf shape < sizeOf fact := by
  have hlist := List.sizeOf_lt_of_mem h
  cases fact with
  | mk mayScalar unknownHeap shapes =>
      exact Nat.lt_trans (by simpa using hlist) (by simp_wf)

private theorem FieldShape.exists_le_of_anyLe {left : FieldShape}
    {rights : List FieldShape} (h : FieldShape.anyLe left rights = true) :
    ∃ right ∈ rights, left.le right = true := by
  induction rights with
  | nil => simp [FieldShape.anyLe] at h
  | cons right rights ih =>
      simp only [FieldShape.anyLe, Bool.or_eq_true] at h
      rcases h with hhead | htail
      · exact ⟨right, by simp, hhead⟩
      · obtain ⟨found, hmember, hle⟩ := ih htail
        exact ⟨found, by simp [hmember], hle⟩

private theorem FieldShape.exists_le_of_allLe
    {lefts rights : List FieldShape} {left : FieldShape}
    (hall : FieldShape.allLe lefts rights = true) (hleft : left ∈ lefts) :
    ∃ right ∈ rights, left.le right = true := by
  induction lefts with
  | nil => contradiction
  | cons head tail ih =>
      simp only [FieldShape.allLe, Bool.and_eq_true] at hall
      rcases List.mem_cons.mp hleft with rfl | htail
      · exact FieldShape.exists_le_of_anyLe hall.1
      · exact ih hall.2 htail

mutual

/-- Recursive field-shape subset preserves its full concrete tree. -/
theorem FieldShape.holds_of_le {declarations : DeclEnv} {store : Store}
    {left right : FieldShape} {value : RVal}
    (hle : left.le right = true)
    (hleft : left.Holds declarations store value) :
    right.Holds declarations store value := by
  cases hleft with
  | @ctorIdentity location box identity fields hget hnode =>
      cases right with
      | ctor rightIdentity rightFields =>
          cases rightFields with
          | none =>
              have hidentity : identity = rightIdentity := by
                simpa [FieldShape.le.eq_1] using hle
              subst rightIdentity
              exact .ctorIdentity hget hnode
          | some rightFacts =>
              simp [FieldShape.le.eq_2] at hle
      | pap _ _ => simp [FieldShape.le] at hle
  | @ctorDetailed location box identity fields facts hget hnode hfields =>
      cases right with
      | ctor rightIdentity rightFields =>
          cases rightFields with
          | none =>
              have hidentity : identity = rightIdentity := by
                simpa [FieldShape.le.eq_1] using hle
              subst rightIdentity
              exact .ctorIdentity hget hnode
          | some rightFacts =>
              simp only [FieldShape.le.eq_3, Bool.and_eq_true] at hle
              have hidentity : identity = rightIdentity :=
                beq_iff_eq.mp hle.1
              subst rightIdentity
              exact .ctorDetailed hget hnode
                (FieldFactsHold.holds_of_listLe hle.2 hfields)
      | pap _ _ => simp [FieldShape.le] at hle
  | @pap location box function declaration arguments supplied hget hdecl hnode
      hsize hproper =>
      cases right with
      | ctor _ _ => simp [FieldShape.le] at hle
      | pap rightFunction rightSupplied =>
          simp only [FieldShape.le, Bool.and_eq_true] at hle
          have hfunction : function = rightFunction := beq_iff_eq.mp hle.1
          have hsupplied : supplied = rightSupplied := beq_iff_eq.mp hle.2
          subst rightFunction
          subst rightSupplied
          exact .pap hget hdecl hnode hsize hproper
termination_by sizeOf left
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

/-- Recursive field-fact subset preserves scalar, unknown, and finite-shape
evidence. -/
theorem FieldFact.holds_of_le {declarations : DeclEnv} {store : Store}
    {left right : FieldFact} {value : RVal}
    (hle : left.le right = true)
    (hleft : left.Holds declarations store value) :
    right.Holds declarations store value := by
  cases hleft with
  | lit hscalar =>
      simp [FieldFact.le, hscalar] at hle
      exact .lit hle.1
  | erased hscalar =>
      simp [FieldFact.le, hscalar] at hle
      exact .erased hle.1
  | unknown hunknown =>
      simp [FieldFact.le, hunknown] at hle
      exact .unknown hle.2
  | heap hmember hshape =>
      simp only [FieldFact.le, Bool.and_eq_true] at hle
      by_cases hunknown : right.unknownHeap = true
      · exact .unknown hunknown
      · have hall : FieldShape.allLe left.shapes right.shapes = true := by
          have hbranch : left.unknownHeap = false ∧
              FieldShape.allLe left.shapes right.shapes = true := by
            simpa [hunknown] using hle.2
          exact hbranch.2
        obtain ⟨rightShape, hright, hshapeLe⟩ :=
          FieldShape.exists_le_of_allLe hall hmember
        exact .heap hright (FieldShape.holds_of_le hshapeLe hshape)
termination_by sizeOf left
decreasing_by
  all_goals subst_vars
  exact FieldFact.shape_size_lt hmember

/-- Pointwise recursive field-vector subset. -/
theorem FieldFactsHold.holds_of_listLe {declarations : DeclEnv} {store : Store}
    {left right : List FieldFact} {values : List RVal}
    (hle : FieldFact.listLe left right = true)
    (hleft : FieldFactsHold declarations store left values) :
    FieldFactsHold declarations store right values := by
  cases hleft with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons _ _ => simp [FieldFact.listLe] at hle
  | @cons leftFact value leftFacts values hhead htail =>
      cases right with
      | nil => simp [FieldFact.listLe] at hle
      | cons rightFact rightFacts =>
          simp only [FieldFact.listLe, Bool.and_eq_true] at hle
          exact .cons (FieldFact.holds_of_le hle.1 hhead)
            (FieldFactsHold.holds_of_listLe hle.2 htail)
termination_by sizeOf left
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

end

namespace FieldFactsHold

theorem length_eq {declarations : DeclEnv} {store : Store}
    {facts : List FieldFact} {values : List RVal}
    (h : FieldFactsHold declarations store facts values) :
    facts.length = values.length := by
  cases h with
  | nil => rfl
  | cons _ htail => simp [FieldFactsHold.length_eq htail]
termination_by sizeOf facts
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

theorem holds_of_le {declarations : DeclEnv} {store : Store}
    {left right : List FieldFact} {values : List RVal}
    (hle : HeapShape.fieldFactsLe left right = true)
    (hleft : FieldFactsHold declarations store left values) :
    FieldFactsHold declarations store right values := by
  cases hleft with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons _ _ => simp [HeapShape.fieldFactsLe] at hle
  | @cons leftFact value leftFacts values hhead htail =>
      cases right with
      | nil => simp [HeapShape.fieldFactsLe] at hle
      | cons rightFact rightFacts =>
          simp only [HeapShape.fieldFactsLe, Bool.and_eq_true] at hle
          exact .cons (FieldFact.holds_of_le hle.1 hhead)
            (FieldFactsHold.holds_of_le hle.2 htail)
termination_by sizeOf left
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

theorem getOfValue {declarations : DeclEnv} {store : Store}
    {facts : List FieldFact} {values : List RVal}
    (h : FieldFactsHold declarations store facts values)
    {index : Nat} {value : RVal} (hvalue : values[index]? = some value) :
    ∃ fact, facts[index]? = some fact ∧ fact.Holds declarations store value := by
  cases h with
  | nil => simp at hvalue
  | @cons tailFacts tailValues headFact headValue hhead htail =>
      cases index with
      | zero =>
          simp at hvalue
          subst value
          exact ⟨headFact, by simp, hhead⟩
      | succ index =>
          simp at hvalue
          obtain ⟨fact, hfact, hholds⟩ :=
            FieldFactsHold.getOfValue htail hvalue
          exact ⟨fact, by simpa, hholds⟩
termination_by sizeOf facts
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

end FieldFactsHold

namespace HeapShape

/-- Concrete interpretation of one result heap shape. Detailed constructor
facts additionally validate every stored field in source order. PAP facts bind
the saturation arity to the declaration environment. -/
def Holds (declarations : DeclEnv) (store : Store) (value : RVal) :
    HeapShape → Prop
  | .ctor identity fieldFacts =>
      match value with
      | .loc location =>
          ∃ box fields,
            store.get? location = some box ∧
              box.node = .ctorN identity fields ∧
              match fieldFacts with
              | none => True
              | some facts =>
                  FieldFactsHold declarations store facts fields.toList
      | _ => False
  | .pap function supplied =>
      match value with
      | .loc location =>
          ∃ box arguments declaration,
            store.get? location = some box ∧
              declarations function = some declaration ∧
              box.node = .papN function (declArity declaration) arguments ∧
              arguments.size = supplied ∧
              supplied < declArity declaration
      | _ => False

/-- Shape-level subset preserves the detailed concrete interpretation. -/
theorem holds_of_le {declarations : DeclEnv} {store : Store}
    {left right : HeapShape} {value : RVal}
    (hle : left.le right = true)
    (hleft : left.Holds declarations store value) :
    right.Holds declarations store value := by
  cases left <;> cases right <;> cases value <;>
    simp only [HeapShape.Holds] at hleft ⊢
  case ctor.ctor.loc leftIdentity leftFields rightIdentity rightFields location =>
    simp only [HeapShape.le, Bool.and_eq_true] at hle
    have hidentity : leftIdentity = rightIdentity := (beq_iff_eq).mp hle.1
    subst rightIdentity
    rcases hleft with ⟨box, values, hget, hnode, hfields⟩
    refine ⟨box, values, hget, hnode, ?_⟩
    cases rightFields with
    | none => trivial
    | some rightFacts =>
        cases leftFields with
        | none => simp at hle
        | some leftFacts =>
            exact FieldFactsHold.holds_of_le hle.2 hfields
  case pap.pap.loc leftFunction leftSupplied rightFunction rightSupplied
      location =>
    simp only [HeapShape.le, Bool.and_eq_true] at hle
    have hfunction : leftFunction = rightFunction := (beq_iff_eq).mp hle.1
    have hsupplied : leftSupplied = rightSupplied := (beq_iff_eq).mp hle.2
    subst rightFunction
    subst rightSupplied
    exact hleft
  all_goals simp [HeapShape.le] at hle

end HeapShape

namespace Fact

/-- Concrete interpretation of a result-shape fact.  Scalars are literals or
`erased`; a finite heap fact requires a matching live node. -/
def Holds (declarations : DeclEnv) (store : Store)
    (fact : Fact) (value : RVal) : Prop :=
  match value with
  | .loc _ =>
      fact.unknownHeap = true ∨
        ∃ shape ∈ fact.shapes, shape.Holds declarations store value
  | .lit _ | .erased => fact.mayScalar = true

@[simp] theorem top_holds (declarations : DeclEnv) (store : Store)
    (value : RVal) : Fact.top.Holds declarations store value := by
  cases value <;> simp [Fact.Holds, Fact.top]

@[simp] theorem scalar_holds_iff (declarations : DeclEnv) (store : Store)
    (value : RVal) :
    Fact.scalar.Holds declarations store value ↔ value.isScalar = true := by
  cases value <;> simp [Fact.Holds, Fact.scalar, RVal.isScalar]

theorem heap_holds {declarations : DeclEnv} {store : Store}
    {shape : HeapShape} {value : RVal}
    (h : shape.Holds declarations store value) :
    (Fact.heap shape).Holds declarations store value := by
  cases value with
  | loc location =>
      exact Or.inr ⟨shape, by simp [Fact.heap], h⟩
  | lit literal => cases shape <;> contradiction
  | erased => cases shape <;> contradiction

/-- An exact-constructor fact identifies the concrete constructor stored at
the held location.  This is the small provenance bridge used by consumers
whose emitted IxIR₂ instruction carries a concrete constructor identity. -/
theorem exactConstructor?_holds_loc {declarations : DeclEnv} {store : Store}
    {fact : Fact} {identity : CtorId} {location : Nat}
    (hexact : fact.exactConstructor? = some identity)
    (hholds : fact.Holds declarations store (.loc location)) :
    ∃ box fields,
      store.get? location = some box ∧
        box.node = .ctorN identity fields := by
  obtain ⟨fieldFacts, rfl⟩ := Fact.exactConstructor?_eq_some hexact
  simp only [Fact.Holds, Bool.false_eq_true, false_or] at hholds
  obtain ⟨shape, hshape, hholds⟩ := hholds
  simp only [List.mem_singleton] at hshape
  subst shape
  simp only [HeapShape.Holds] at hholds
  obtain ⟨box, fields, hget, hnode, _⟩ := hholds
  exact ⟨box, fields, hget, hnode⟩

/-- Executable subset is sound for the concrete interpretation. -/
theorem holds_of_le {declarations : DeclEnv} {store : Store}
    {left right : Fact} {value : RVal}
    (hle : left.le right = true)
    (hleft : left.Holds declarations store value) :
    right.Holds declarations store value := by
  cases value with
  | lit literal =>
      simp [Fact.Holds] at hleft ⊢
      simp [Fact.le] at hle
      exact hle.1.resolve_left (by simpa [hleft])
  | erased =>
      simp [Fact.Holds] at hleft ⊢
      simp [Fact.le] at hle
      exact hle.1.resolve_left (by simpa [hleft])
  | loc location =>
      simp only [Fact.Holds] at hleft ⊢
      simp [Fact.le] at hle
      rcases hleft with hunknown | ⟨shape, hshape, hholds⟩
      · exact Or.inl (hle.2.resolve_right (by simpa [hunknown]))
      · rcases hle.2 with hright | ⟨_, hall⟩
        · exact Or.inl hright
        · obtain ⟨rightShape, hrightShape, hshapeLe⟩ := hall shape hshape
          exact Or.inr ⟨rightShape, hrightShape,
            HeapShape.holds_of_le hshapeLe hholds⟩

private theorem holds_join_left {declarations : DeclEnv} {store : Store}
    {left right : Fact} {value : RVal}
    (hleft : left.Holds declarations store value) :
    (left.join right).Holds declarations store value := by
  cases value with
  | lit literal =>
      change left.mayScalar = true at hleft
      change (left.join right).mayScalar = true
      unfold Fact.join Fact.normalize
      split <;> simp [hleft]
  | erased =>
      change left.mayScalar = true at hleft
      change (left.join right).mayScalar = true
      unfold Fact.join Fact.normalize
      split <;> simp [hleft]
  | loc location =>
      simp only [Fact.Holds] at hleft ⊢
      cases hleftUnknown : left.unknownHeap with
      | true => simp [Fact.join, Fact.normalize, hleftUnknown]
      | false =>
          cases hrightUnknown : right.unknownHeap with
          | true => simp [Fact.join, Fact.normalize, hrightUnknown]
          | false =>
              rcases hleft with hunknown | ⟨shape, hmem, hholds⟩
              · simp [hleftUnknown] at hunknown
              · refine Or.inr ⟨shape, ?_, hholds⟩
                simpa [Fact.join, Fact.normalize, hleftUnknown,
                  hrightUnknown] using
                    HeapShape.mem_normalize_of_mem
                      (List.mem_append_left right.shapes hmem)

private theorem holds_join_right {declarations : DeclEnv} {store : Store}
    {left right : Fact} {value : RVal}
    (hright : right.Holds declarations store value) :
    (left.join right).Holds declarations store value := by
  cases value with
  | lit literal =>
      change right.mayScalar = true at hright
      change (left.join right).mayScalar = true
      unfold Fact.join Fact.normalize
      split <;> simp [hright]
  | erased =>
      change right.mayScalar = true at hright
      change (left.join right).mayScalar = true
      unfold Fact.join Fact.normalize
      split <;> simp [hright]
  | loc location =>
      simp only [Fact.Holds] at hright ⊢
      cases hleftUnknown : left.unknownHeap with
      | true => simp [Fact.join, Fact.normalize, hleftUnknown]
      | false =>
          cases hrightUnknown : right.unknownHeap with
          | true => simp [Fact.join, Fact.normalize, hrightUnknown]
          | false =>
              rcases hright with hunknown | ⟨shape, hmem, hholds⟩
              · simp [hrightUnknown] at hunknown
              · refine Or.inr ⟨shape, ?_, hholds⟩
                simpa [Fact.join, Fact.normalize, hleftUnknown,
                  hrightUnknown] using
                    HeapShape.mem_normalize_of_mem
                      (List.mem_append_right left.shapes hmem)

theorem holds_join {declarations : DeclEnv} {store : Store}
    {left right : Fact} {value : RVal} :
    left.Holds declarations store value ∨
      right.Holds declarations store value →
    (left.join right).Holds declarations store value
  | Or.inl h => holds_join_left h
  | Or.inr h => holds_join_right h

theorem holds_joins_of_mem {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {fact : Fact} {value : RVal}
    (hmember : fact ∈ facts)
    (hholds : fact.Holds declarations store value) :
    (Fact.joins facts).Holds declarations store value := by
  induction facts with
  | nil => contradiction
  | cons head tail ih =>
      simp only [Fact.joins]
      rcases List.mem_cons.mp hmember with hsame | hmember
      · subst head
        exact Fact.holds_join (Or.inl hholds)
      · exact Fact.holds_join (Or.inr (ih hmember))

/-- Forgetting heap identities transports a fact across an arbitrary store
change.  This is the key alias-safety lemma for primitive operations. -/
theorem forgetHeap_holds {declarations : DeclEnv} {before after : Store}
    {fact : Fact} {value : RVal}
    (h : fact.Holds declarations before value) :
    fact.forgetHeap.Holds declarations after value := by
  cases value with
  | lit literal =>
      change fact.mayScalar = true at h
      change fact.forgetHeap.mayScalar = true
      unfold Fact.forgetHeap
      split <;> simp [h]
  | erased =>
      change fact.mayScalar = true at h
      change fact.forgetHeap.mayScalar = true
      unfold Fact.forgetHeap
      split <;> simp [h]
  | loc location =>
      cases fact with
      | mk mayScalar unknownHeap shapes =>
          cases unknownHeap with
          | true => simp [Fact.Holds, Fact.forgetHeap]
          | false =>
              simp only [Fact.Holds, Bool.false_eq_true, false_or] at h
              rcases h with ⟨shape, hmem, hholds⟩
              cases shapes with
              | nil => contradiction
              | cons head tail => simp [Fact.Holds, Fact.forgetHeap]

end Fact

namespace HeapShape

/-- Converting a result heap shape into a field shape preserves every
recursive constructor refinement. -/
theorem toFieldShape_holds {declarations : DeclEnv} {store : Store}
    {shape : HeapShape} {value : RVal}
    (h : shape.Holds declarations store value) :
    shape.toFieldShape.Holds declarations store value := by
  cases shape with
  | ctor identity facts =>
      cases value with
      | loc location =>
          rcases h with ⟨box, fields, hget, hnode, hfields⟩
          cases facts with
          | none => exact .ctorIdentity hget hnode
          | some facts => exact .ctorDetailed hget hnode hfields
      | lit _ => contradiction
      | erased => contradiction
  | pap function supplied =>
      cases value with
      | loc location =>
          rcases h with
            ⟨box, arguments, declaration, hget, hdecl, hnode, hsize, hproper⟩
          exact .pap hget hdecl hnode hsize hproper
      | lit _ => contradiction
      | erased => contradiction

end HeapShape

namespace FieldShape

theorem toHeapShape_holds {declarations : DeclEnv} {store : Store}
    {shape : FieldShape} {value : RVal}
    (h : shape.Holds declarations store value) :
    shape.toHeapShape.Holds declarations store value := by
  cases h with
  | @ctorIdentity location box identity fields hget hnode =>
      exact ⟨box, fields, hget, hnode, trivial⟩
  | @ctorDetailed location box identity fields facts hget hnode hfields =>
      exact ⟨box, fields, hget, hnode, hfields⟩
  | @pap location box function declaration arguments supplied hget hdecl
      hnode hsize hproper =>
      exact ⟨box, arguments, declaration, hget, hdecl, hnode, hsize, hproper⟩

end FieldShape

namespace FieldFact

/-- Storing a result in one constructor field preserves every bounded nested
refinement. -/
theorem ofFact_holds {declarations : DeclEnv} {store : Store}
    {fact : Fact} {value : RVal}
    (h : fact.Holds declarations store value) :
    (FieldFact.ofFact fact).Holds declarations store value := by
  cases value with
  | lit literal =>
      change fact.mayScalar = true at h
      apply FieldFact.Holds.lit
      cases hunknown : fact.unknownHeap <;>
        simp [FieldFact.ofFact, FieldFact.normalize, h, hunknown]
  | erased =>
      change fact.mayScalar = true at h
      apply FieldFact.Holds.erased
      cases hunknown : fact.unknownHeap <;>
        simp [FieldFact.ofFact, FieldFact.normalize, h, hunknown]
  | loc location =>
      simp only [Fact.Holds] at h
      rcases h with hunknown | ⟨shape, hshape, hholds⟩
      · apply FieldFact.Holds.unknown
        simp [FieldFact.ofFact, FieldFact.normalize, hunknown]
      · cases hunknown : fact.unknownHeap with
        | true =>
            apply FieldFact.Holds.unknown
            simp [FieldFact.ofFact, FieldFact.normalize, hunknown]
        | false =>
            apply FieldFact.Holds.heap
                (shape := shape.toFieldShape)
            · have hmapped : shape.toFieldShape ∈
                  fact.shapes.map HeapShape.toFieldShape :=
                List.mem_map.mpr ⟨shape, hshape, rfl⟩
              simpa [FieldFact.ofFact, FieldFact.normalize, hunknown] using
                FieldShape.mem_normalize_of_mem hmapped
            · exact HeapShape.toFieldShape_holds hholds

/-- A fetched field fact soundly re-roots its value while preserving every
bounded nested constructor refinement. -/
theorem toFact_holds {declarations : DeclEnv} {store : Store}
    {fact : FieldFact} {value : RVal}
    (h : fact.Holds declarations store value) :
    fact.toFact.Holds declarations store value := by
  cases h with
  | lit hscalar =>
      change fact.toFact.mayScalar = true
      cases hunknown : fact.unknownHeap <;>
        simp [FieldFact.toFact, Fact.normalize, hscalar, hunknown]
  | erased hscalar =>
      change fact.toFact.mayScalar = true
      cases hunknown : fact.unknownHeap <;>
        simp [FieldFact.toFact, Fact.normalize, hscalar, hunknown]
  | unknown hunknown =>
      simp only [Fact.Holds]
      left
      simp [FieldFact.toFact, Fact.normalize, hunknown]
  | heap hmember hshape =>
      simp only [Fact.Holds]
      cases hunknown : fact.unknownHeap with
      | true =>
          left
          simp [FieldFact.toFact, Fact.normalize, hunknown]
      | false =>
          right
          refine ⟨_, ?_, FieldShape.toHeapShape_holds hshape⟩
          simpa [FieldFact.toFact, Fact.normalize, hunknown] using
            HeapShape.mem_normalize_of_mem
              (List.mem_map.mpr ⟨_, hmember, rfl⟩)

end FieldFact

namespace Fact

/-- A successful concrete constructor projection is covered by the executable
recursive-field fetch transfer. -/
theorem fetch_holds {declarations : DeclEnv} {store : Store}
    {fact : Fact} {location field : Nat} {box : NodeBox}
    {identity : CtorId} {fields : Array RVal} {value : RVal}
    (hfact : fact.Holds declarations store (.loc location))
    (hget : store.get? location = some box)
    (hnode : box.node = .ctorN identity fields)
    (hfield : fields[field]? = some value) :
    (fact.fetch field).Holds declarations store value := by
  cases hunknown : fact.unknownHeap with
  | true =>
      simp [Fact.fetch, hunknown]
  | false =>
      simp only [Fact.Holds, hunknown, Bool.false_eq_true, false_or] at hfact
      obtain ⟨shape, hmember, hshape⟩ := hfact
      have hmapped : shape.fetch field ∈
          fact.shapes.map (HeapShape.fetch field) :=
        List.mem_map.mpr ⟨shape, hmember, rfl⟩
      simp only [Fact.fetch, hunknown, Bool.false_eq_true, if_false]
      apply Fact.holds_joins_of_mem hmapped
      cases shape with
      | pap function supplied =>
          rcases hshape with
            ⟨shapeBox, arguments, declaration, hshapeGet, _, hshapeNode, _⟩
          have hboxEq : shapeBox = box := by
            exact Option.some.inj (hshapeGet.symm.trans hget)
          subst shapeBox
          rw [hnode] at hshapeNode
          contradiction
      | ctor shapeIdentity fieldFacts =>
          rcases hshape with
            ⟨shapeBox, shapeFields, hshapeGet, hshapeNode, hfields⟩
          have hboxEq : shapeBox = box := by
            exact Option.some.inj (hshapeGet.symm.trans hget)
          subst shapeBox
          rw [hnode] at hshapeNode
          injection hshapeNode with hidentity hshapeFields
          subst shapeIdentity
          subst shapeFields
          cases fieldFacts with
          | none => exact Fact.top_holds declarations store value
          | some fieldFacts =>
              have hfieldList : fields.toList[field]? = some value := by
                simpa using hfield
              obtain ⟨fieldFact, hfieldFact, hfieldHolds⟩ :=
                FieldFactsHold.getOfValue hfields hfieldList
              simp only [HeapShape.fetch, hfieldFact]
              exact FieldFact.toFact_holds hfieldHolds

end Fact

/-! ## Abstract/concrete environments -/

/-- Pointwise interpretation of an abstract de Bruijn environment. -/
inductive EnvironmentHolds (declarations : DeclEnv) (store : Store) :
    List Fact → List RVal → Prop where
  | nil : EnvironmentHolds declarations store [] []
  | cons : fact.Holds declarations store value →
      EnvironmentHolds declarations store facts values →
      EnvironmentHolds declarations store (fact :: facts) (value :: values)

namespace EnvironmentHolds

theorem top_replicate (declarations : DeclEnv) (store : Store)
    (values : List RVal) :
    EnvironmentHolds declarations store
      (List.replicate values.length Fact.top) values := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      simpa [List.replicate_succ] using EnvironmentHolds.cons
        (Fact.top_holds declarations store value) ih

theorem forgetHeap {declarations : DeclEnv} {before after : Store}
    {facts : List Fact} {values : List RVal}
    (h : EnvironmentHolds declarations before facts values) :
    EnvironmentHolds declarations after (facts.map Fact.forgetHeap) values := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      exact .cons (Fact.forgetHeap_holds hhead) ih

theorem get? {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal}
    (h : EnvironmentHolds declarations store facts values)
    {index : Nat} {fact : Fact} {value : RVal}
    (hfact : facts[index]? = some fact)
    (hvalue : values[index]? = some value) :
    fact.Holds declarations store value := by
  induction h generalizing index fact value with
  | nil => simp at hfact
  | @cons headFact headValue tailFacts tailValues hhead htail ih =>
      cases index with
      | zero =>
          simp at hfact hvalue
          subst fact
          subst value
          exact hhead
      | succ index =>
          simp at hfact hvalue
          exact ih hfact hvalue

theorem append_top {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal}
    (front : List RVal)
    (h : EnvironmentHolds declarations store facts values) :
    EnvironmentHolds declarations store
      (List.replicate front.length Fact.top ++ facts)
      (front ++ values) := by
  induction front with
  | nil => simpa using h
  | cons value tail ih =>
      change EnvironmentHolds declarations store
        (Fact.top :: (List.replicate tail.length Fact.top ++ facts))
        (value :: (tail ++ values))
      exact EnvironmentHolds.cons
        (Fact.top_holds declarations store value) ih

theorem append {declarations : DeclEnv} {store : Store}
    {leftFacts rightFacts : List Fact} {leftValues rightValues : List RVal}
    (left : EnvironmentHolds declarations store leftFacts leftValues)
    (right : EnvironmentHolds declarations store rightFacts rightValues) :
    EnvironmentHolds declarations store (leftFacts ++ rightFacts)
      (leftValues ++ rightValues) := by
  induction left with
  | nil => simpa using right
  | cons hhead htail ih =>
      exact .cons hhead ih

theorem length_eq {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal}
    (h : EnvironmentHolds declarations store facts values) :
    facts.length = values.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Reversing both sides preserves the pointwise environment relation. -/
theorem reverse {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal}
    (h : EnvironmentHolds declarations store facts values) :
    EnvironmentHolds declarations store facts.reverse values.reverse := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      simp only [List.reverse_cons]
      exact ih.append (.cons hhead .nil)

end EnvironmentHolds

namespace FieldFactsHold

/-- Re-root a detailed constructor's source-order field facts as ordinary
facts suitable for case binders. -/
theorem toEnvironment {declarations : DeclEnv} {store : Store}
    {facts : List FieldFact} {values : List RVal}
    (h : FieldFactsHold declarations store facts values) :
    EnvironmentHolds declarations store
      (facts.map FieldFact.toFact) values := by
  cases h with
  | nil => exact .nil
  | cons hhead htail =>
      exact .cons (FieldFact.toFact_holds hhead)
        (FieldFactsHold.toEnvironment htail)
termination_by sizeOf facts
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

end FieldFactsHold

namespace Fact

private theorem mem_vectorHeads {vectors : List (List Fact)}
    {fact : Fact} {facts : List Fact}
    (h : fact :: facts ∈ vectors) : fact ∈ vectorHeads vectors := by
  induction vectors with
  | nil => contradiction
  | cons vector vectors ih =>
      rcases List.mem_cons.mp h with hsame | htail
      · subst vector
        simp [vectorHeads]
      · cases vector with
        | nil => simpa [vectorHeads] using ih htail
        | cons head tail =>
            exact List.mem_cons.mpr (Or.inr (ih htail))

private theorem mem_vectorTails {vectors : List (List Fact)}
    {fact : Fact} {facts : List Fact}
    (h : fact :: facts ∈ vectors) : facts ∈ vectorTails vectors := by
  induction vectors with
  | nil => contradiction
  | cons vector vectors ih =>
      rcases List.mem_cons.mp h with hsame | htail
      · subst vector
        simp [vectorTails]
      · cases vector with
        | nil => simpa [vectorTails] using ih htail
        | cons head tail =>
            exact List.mem_cons.mpr (Or.inr (ih htail))

end Fact

namespace EnvironmentHolds

/-- Any concrete candidate vector is covered by the executable pointwise join
of its equally sized candidate family. -/
theorem joinFieldVectors_of_mem {declarations : DeclEnv} {store : Store}
    {fieldCount : Nat} {vectors : List (List Fact)}
    {facts : List Fact} {values : List RVal}
    (hmember : facts ∈ vectors) (hlength : facts.length = fieldCount)
    (hholds : EnvironmentHolds declarations store facts values) :
    EnvironmentHolds declarations store
      (Fact.joinFieldVectors fieldCount vectors) values := by
  induction hholds generalizing fieldCount vectors with
  | nil =>
      cases fieldCount with
      | zero => exact .nil
      | succ fieldCount => simp at hlength
  | @cons fact value facts values hhead htail ih =>
      cases fieldCount with
      | zero => simp at hlength
      | succ fieldCount =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          exact .cons
            (Fact.holds_joins_of_mem (Fact.mem_vectorHeads hmember) hhead)
            (ih (Fact.mem_vectorTails hmember) hlength)

end EnvironmentHolds

namespace Fact

/-- A successful constructor case receives the joined facts computed for its
actual field vector, in the evaluator's reversed binding order. -/
theorem caseFields_ctor_holds {declarations : DeclEnv} {store : Store}
    {fact : Fact} {location : Nat} {box : NodeBox}
    {identity : CtorId} {fields : Array RVal}
    (peelNat : Bool) (cidx fieldCount : Nat)
    (hfact : fact.Holds declarations store (.loc location))
    (hget : store.get? location = some box)
    (hnode : box.node = .ctorN identity fields)
    (hcidx : identity.cidx = cidx)
    (hfieldCount : fields.size = fieldCount) :
    EnvironmentHolds declarations store
      (fact.caseFields peelNat cidx fieldCount) fields.toList.reverse := by
  cases hunknown : fact.unknownHeap with
  | true =>
      have htop := EnvironmentHolds.top_replicate declarations store
        fields.toList.reverse
      have hlength : fields.toList.reverse.length = fieldCount := by
        simpa using hfieldCount
      simpa [Fact.caseFields, hunknown, hlength] using htop
  | false =>
      simp only [Fact.Holds, hunknown, Bool.false_eq_true, false_or] at hfact
      obtain ⟨shape, hshapeMember, hshapeHolds⟩ := hfact
      let vector := shape.caseFields cidx fieldCount
      have hvectorHolds : EnvironmentHolds declarations store vector
          fields.toList.reverse := by
        cases shape with
        | pap function supplied =>
            rcases hshapeHolds with
              ⟨shapeBox, arguments, declaration, hshapeGet, _, hshapeNode, _⟩
            have hboxEq : shapeBox = box :=
              Option.some.inj (hshapeGet.symm.trans hget)
            subst shapeBox
            rw [hnode] at hshapeNode
            contradiction
        | ctor shapeIdentity shapeFieldFacts =>
            rcases hshapeHolds with
              ⟨shapeBox, shapeFields, hshapeGet, hshapeNode, hshapeFacts⟩
            have hboxEq : shapeBox = box :=
              Option.some.inj (hshapeGet.symm.trans hget)
            subst shapeBox
            rw [hnode] at hshapeNode
            injection hshapeNode with hidentity hshapeFields
            subst shapeIdentity
            subst shapeFields
            have hcidxBool : identity.cidx == cidx :=
              (beq_iff_eq).mpr hcidx
            cases shapeFieldFacts with
            | none =>
                have htop := EnvironmentHolds.top_replicate declarations
                  store fields.toList.reverse
                have hlength : fields.toList.reverse.length = fieldCount := by
                  simpa using hfieldCount
                simpa [vector, HeapShape.caseFields, hcidxBool, hlength]
                  using htop
            | some fieldFacts =>
                have hfieldsLength : fields.toList.length = fieldCount := by
                  simpa using hfieldCount
                have hfactLength : fieldFacts.length = fieldCount :=
                  hshapeFacts.length_eq.trans hfieldsLength
                have hfieldsEnvironment := hshapeFacts.toEnvironment.reverse
                simpa [vector, HeapShape.caseFields, hcidxBool, hfactLength]
                  using hfieldsEnvironment
      let heapCandidates :=
        fact.shapes.map (HeapShape.caseFields cidx fieldCount)
      let candidates :=
        if fact.mayScalar then
          scalarCaseFields peelNat cidx fieldCount :: heapCandidates
        else
          heapCandidates
      have hheapMember : vector ∈ heapCandidates :=
        List.mem_map.mpr ⟨shape, hshapeMember, rfl⟩
      have hcandidate : vector ∈ candidates := by
        dsimp [candidates]
        split
        · exact List.mem_cons.mpr (Or.inr hheapMember)
        · exact hheapMember
      have hlength : vector.length = fieldCount := by
        rw [hvectorHolds.length_eq]
        simpa using hfieldCount
      have hjoined := EnvironmentHolds.joinFieldVectors_of_mem
        hcandidate hlength hvectorHolds
      simpa [Fact.caseFields, hunknown, heapCandidates, candidates]
        using hjoined

/-- A successfully peeled successor binds its predecessor as an exact scalar
even when heap shapes are also possible. -/
theorem caseFields_natSucc_holds {declarations : DeclEnv} {store : Store}
    {fact : Fact} {value : Nat}
    (hfact : fact.Holds declarations store (.lit (.nat (value + 1)))) :
    EnvironmentHolds declarations store
      (fact.caseFields true 1 1) [.lit (.nat value)] := by
  change fact.mayScalar = true at hfact
  cases hunknown : fact.unknownHeap with
  | true =>
      simpa [Fact.caseFields, hunknown] using
        (EnvironmentHolds.cons
          (Fact.top_holds declarations store (.lit (.nat value)))
          EnvironmentHolds.nil)
  | false =>
      have hscalar : EnvironmentHolds declarations store
          [Fact.scalar] [.lit (.nat value)] :=
        .cons (by simp [Fact.Holds, Fact.scalar]) .nil
      have hjoined := EnvironmentHolds.joinFieldVectors_of_mem
        (vectors := [Fact.scalar] ::
          fact.shapes.map (HeapShape.caseFields 1 1))
        (fieldCount := 1) (facts := [Fact.scalar])
        (by simp) (by simp) hscalar
      simpa [Fact.caseFields, hunknown, hfact, scalarCaseFields] using hjoined

end Fact

/-! ## Resolution and store primitives -/

theorem resolveAtom_sound {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal} {atom : Atom}
    {fact : Fact} {value : RVal}
    (henvironment : EnvironmentHolds declarations store facts values)
    (habstract : resolveAtomFact facts atom = .ok fact)
    (hconcrete : resolveAtom values atom = .ok value) :
    fact.Holds declarations store value := by
  cases atom with
  | var index =>
      unfold resolveAtomFact at habstract
      unfold resolveAtom at hconcrete
      cases hfact : facts[index]? with
      | none => simp [hfact] at habstract
      | some resolvedFact =>
          simp only [hfact] at habstract
          cases hvalue : values[index]? with
          | none => simp [hvalue] at hconcrete
          | some resolvedValue =>
              simp only [hvalue] at hconcrete
              injection habstract with hfactEq
              injection hconcrete with hvalueEq
              subst fact
              subst value
              exact henvironment.get? hfact hvalue
  | lit literal =>
      simp only [resolveAtomFact, Except.ok.injEq] at habstract
      simp only [resolveAtom, Except.ok.injEq] at hconcrete
      subst fact
      subst value
      simp [Fact.Holds, Fact.scalar]
  | erased =>
      simp only [resolveAtomFact, Except.ok.injEq] at habstract
      simp only [resolveAtom, Except.ok.injEq] at hconcrete
      subst fact
      subst value
      simp [Fact.Holds, Fact.scalar]

/-- A well-formed abstract environment cannot resolve an atom that the
pointwise concrete environment fails to resolve. -/
theorem resolveAtom_complete {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal} {atom : Atom} {fact : Fact}
    (henvironment : EnvironmentHolds declarations store facts values)
    (habstract : resolveAtomFact facts atom = .ok fact) :
    ∃ value, resolveAtom values atom = .ok value := by
  cases atom with
  | lit literal => exact ⟨.lit literal, rfl⟩
  | erased => exact ⟨.erased, rfl⟩
  | var index =>
      induction henvironment generalizing index fact with
      | nil => simp [resolveAtomFact] at habstract
      | @cons tailFacts tailValues headFact headValue hhead htail ih =>
          cases index with
          | zero => exact ⟨headValue, by simp [resolveAtom]⟩
          | succ index =>
              cases hfact : tailFacts[index]? with
              | none => simp [resolveAtomFact, hfact] at habstract
              | some resolved =>
                  obtain ⟨value, hvalue⟩ := ih (fact := resolved)
                    (index := index) (by simp [resolveAtomFact, hfact])
                  unfold resolveAtom at hvalue ⊢
                  cases hconcrete : tailValues[index]? with
                  | none => simp [hconcrete] at hvalue
                  | some resolvedValue =>
                      simp only [hconcrete, Except.ok.injEq] at hvalue
                      subst resolvedValue
                      exact ⟨value, by simp [hconcrete]⟩

private theorem List.resolveAtomFactsFrom_sound
    {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal}
    (henvironment : EnvironmentHolds declarations store facts values) :
    ∀ (atoms : List Atom) (factAccumulator : List Fact)
      (valueAccumulator : List RVal) (outputFacts : List Fact)
      (outputValues : List RVal),
      EnvironmentHolds declarations store factAccumulator valueAccumulator →
      atoms.foldlM
        (fun accumulated atom => do
          pure (accumulated ++ [← resolveAtomFact facts atom]))
        factAccumulator = .ok outputFacts →
      atoms.foldlM
        (fun accumulated atom => do
          pure (accumulated ++ [← resolveAtom values atom]))
        valueAccumulator = .ok outputValues →
      EnvironmentHolds declarations store outputFacts outputValues := by
  intro atoms
  induction atoms with
  | nil =>
      intro factAccumulator valueAccumulator outputFacts outputValues
        haccumulator habstract hconcrete
      simp only [List.foldlM_nil] at habstract hconcrete
      injection habstract with hfacts
      injection hconcrete with hvalues
      subst outputFacts
      subst outputValues
      exact haccumulator
  | cons atom atoms ih =>
      intro factAccumulator valueAccumulator outputFacts outputValues
        haccumulator habstract hconcrete
      simp only [List.foldlM_cons] at habstract hconcrete
      cases hafact : resolveAtomFact facts atom with
      | error error =>
          rw [hafact] at habstract
          simp only [bind, Except.bind] at habstract
          contradiction
      | ok atomFact =>
          rw [hafact] at habstract
          simp only [bind, Except.bind] at habstract
          cases havalue : resolveAtom values atom with
          | error error =>
              rw [havalue] at hconcrete
              simp only [bind, Except.bind] at hconcrete
              contradiction
          | ok atomValue =>
              rw [havalue] at hconcrete
              simp only [bind, Except.bind] at hconcrete
              apply ih (factAccumulator ++ [atomFact])
                (valueAccumulator ++ [atomValue]) outputFacts outputValues
              · exact haccumulator.append (.cons
                  (resolveAtom_sound henvironment hafact havalue) .nil)
              · exact habstract
              · exact hconcrete

theorem resolveAtomFacts_sound
    {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal} {atoms : Array Atom}
    {argumentFacts : List Fact} {argumentValues : List RVal}
    (henvironment : EnvironmentHolds declarations store facts values)
    (habstract : resolveAtomFacts facts atoms = .ok argumentFacts)
    (hconcrete : resolveAtoms values atoms = .ok argumentValues) :
    EnvironmentHolds declarations store argumentFacts argumentValues := by
  unfold resolveAtomFacts at habstract
  unfold resolveAtoms at hconcrete
  rw [← Array.foldlM_toList] at habstract hconcrete
  exact List.resolveAtomFactsFrom_sound henvironment atoms.toList [] []
    argumentFacts argumentValues .nil habstract hconcrete

private theorem List.resolveAtomsFrom_length (environment : List RVal) :
    ∀ (atoms : List Atom) (accumulator output : List RVal),
      atoms.foldlM
        (fun accumulated atom => do
          pure (accumulated ++ [← resolveAtom environment atom]))
        accumulator = .ok output →
      output.length = accumulator.length + atoms.length := by
  intro atoms
  induction atoms with
  | nil =>
      intro accumulator output h
      simp only [List.foldlM_nil] at h
      change Except.ok accumulator = Except.ok output at h
      injection h with houtput
      subst output
      simp
  | cons atom atoms ih =>
      intro accumulator output h
      simp only [List.foldlM_cons] at h
      cases hatom : resolveAtom environment atom with
      | error error =>
          rw [hatom] at h
          simp only [bind, Except.bind] at h
          contradiction
      | ok value =>
          rw [hatom] at h
          simp only [bind, Except.bind] at h
          have htail := ih (accumulator ++ [value]) output h
          simp only [List.length_append, List.length_singleton] at htail
          simp only [List.length_cons]
          omega

private theorem resolveAtoms_length {environment : List RVal}
    {atoms : Array Atom} {values : List RVal}
    (h : resolveAtoms environment atoms = .ok values) :
    values.length = atoms.size := by
  unfold resolveAtoms at h
  rw [← Array.foldlM_toList] at h
  have := List.resolveAtomsFrom_length environment atoms.toList [] values h
  simpa using this

private theorem get?_allocNode_new (store : Store)
    (world : Ixon.Owned) (node : Node) :
    (store.allocNode world node).1.get? (store.allocNode world node).2 =
      some ⟨world, 1, node⟩ := by
  simp [Store.allocNode, Store.get?]

private theorem get?_allocNode_old {store : Store} {world : Ixon.Owned}
    {node : Node} {location : Nat} {box : NodeBox}
    (h : store.get? location = some box) :
    (store.allocNode world node).1.get? location = some box := by
  have hne : location ≠ store.nodes.size := by
    intro heq
    subst location
    simp [Store.get?] at h
  simpa [Store.allocNode, Store.get?, Array.getElem?_push, hne] using h

mutual

theorem FieldShape.holds_allocNode {declarations : DeclEnv} {store : Store}
    {shape : FieldShape} {value : RVal} {world : Ixon.Owned} {node : Node}
    (h : shape.Holds declarations store value) :
    shape.Holds declarations (store.allocNode world node).1 value := by
  cases h with
  | ctorIdentity hget hnode =>
      exact .ctorIdentity (get?_allocNode_old hget) hnode
  | ctorDetailed hget hnode hfields =>
      exact .ctorDetailed (get?_allocNode_old hget) hnode
        (FieldFactsHold.allocNode hfields)
  | pap hget hdecl hnode hsize hproper =>
      exact .pap (get?_allocNode_old hget) hdecl hnode hsize hproper
termination_by sizeOf shape
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

theorem FieldFact.holds_allocNode {declarations : DeclEnv} {store : Store}
    {fact : FieldFact} {value : RVal} {world : Ixon.Owned} {node : Node}
    (h : fact.Holds declarations store value) :
    fact.Holds declarations (store.allocNode world node).1 value := by
  cases h with
  | lit hscalar => exact .lit hscalar
  | erased hscalar => exact .erased hscalar
  | unknown hunknown => exact .unknown hunknown
  | heap hmember hshape =>
      exact .heap hmember (FieldShape.holds_allocNode hshape)
termination_by sizeOf fact
decreasing_by
  all_goals subst_vars
  exact FieldFact.shape_size_lt hmember

theorem FieldFactsHold.allocNode {declarations : DeclEnv} {store : Store}
    {facts : List FieldFact} {values : List RVal}
    {world : Ixon.Owned} {node : Node}
    (h : FieldFactsHold declarations store facts values) :
    FieldFactsHold declarations (store.allocNode world node).1 facts values := by
  cases h with
  | nil => exact .nil
  | cons hhead htail =>
      exact .cons (FieldFact.holds_allocNode hhead)
        (FieldFactsHold.allocNode htail)
termination_by sizeOf facts
decreasing_by all_goals subst_vars <;> simp_wf <;> omega

end

namespace EnvironmentHolds

theorem toFieldFactsAllocNode {declarations : DeclEnv} {store : Store}
    {facts : List Fact} {values : List RVal}
    {world : Ixon.Owned} {node : Node}
    (h : EnvironmentHolds declarations store facts values) :
    FieldFactsHold declarations (store.allocNode world node).1
      (facts.map FieldFact.ofFact) values := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      exact .cons (FieldFact.holds_allocNode (FieldFact.ofFact_holds hhead)) ih

theorem toFieldFactsForget {declarations : DeclEnv} {before after : Store}
    {facts : List Fact} {values : List RVal}
    (h : EnvironmentHolds declarations before facts values) :
    FieldFactsHold declarations after
      (facts.map fun fact => FieldFact.ofFact fact.forgetHeap) values := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      exact .cons
        (FieldFact.ofFact_holds (Fact.forgetHeap_holds (after := after) hhead))
        ih

end EnvironmentHolds

private theorem nodes_get?_of_get? {store : Store} {location : Nat}
    {box : NodeBox} (h : store.get? location = some box) :
    store.nodes[location]? = some (some box) := by
  rw [Store.get?, Option.bind_eq_some_iff] at h
  obtain ⟨slot, hslot, hid⟩ := h
  change slot = some box at hid
  subst slot
  exact hslot

private theorem get?_setBox_same {store : Store} {location : Nat}
    {old new : NodeBox} (h : store.get? location = some old) :
    (store.setBox location new).get? location = some new := by
  have hnodes := nodes_get?_of_get? h
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simp [Store.setBox, Store.get?, Array.set!_eq_setIfInBounds, hlt]

private theorem scalar_of_callScalarOracle_eq_ok {ctx : Ctx} {function : Address}
    {arguments : List RVal} {value : RVal}
    (h : callScalarOracle ctx function arguments = .ok value) :
    value.isScalar = true := by
  unfold callScalarOracle at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · injection h
        subst value
        assumption
      · contradiction

private theorem eq_of_checkResultWorld_eq_ok {world : Ixon.Owned}
    {input output : Store × RVal}
    (h : checkResultWorld world input = .ok output) : input = output := by
  unfold checkResultWorld at h
  split at h
  · injection h
  · contradiction

private theorem List.foldl_cons_eq_reverse_append
    (values environment : List RVal) :
    values.foldl (fun current value => value :: current) environment =
      values.reverse ++ environment := by
  induction values generalizing environment with
  | nil => rfl
  | cons value values ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem Array.foldl_cons_eq_reverse_append
    (fields : Array RVal) (environment : List RVal) :
    fields.foldl (fun current field => field :: current) environment =
      fields.toList.reverse ++ environment := by
  rw [← Array.foldl_toList]
  exact List.foldl_cons_eq_reverse_append fields.toList environment

/-! ## Local certificate assumption -/

/-- Propositional reading of the function rows in a post-fixpoint.  Every
claimed function summary contains the result inferred with the same complete
summary environment. -/
def LocalPostFixpoint (declarations : DeclEnv) (summaries : SummaryEnv) : Prop :=
  ∀ address function claimed,
    declarations address = some (.fn function) →
    summaries address = some claimed →
    ∃ inferred,
      inferFunction declarations summaries address function = .ok inferred ∧
        inferred.le claimed = true

/-- An analysis owner is semantically usable either when it names the exact
dynamic current function, or when it has no summary and every attempted
`callSelf` transfer therefore fails closed.  The second form is the natural
contract for a top-level main, which has a current frame but no declaration
row. -/
def AnalysisOwnerCompatible (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (current : FnDef) : Prop :=
  declarations owner = some (.fn current) ∨ summaries owner = none

/-! ## Finite shape-fold coverage -/

theorem holds_of_applyShapeFacts_member
    {declarations : DeclEnv} {store : Store}
    {step : HeapShape → Except String Fact} {shapes : List HeapShape}
    {shape : HeapShape} {shapeFact result : Fact} {value : RVal}
    (hmember : shape ∈ shapes)
    (hshape : step shape = .ok shapeFact)
    (hresult : applyShapeFacts step shapes = .ok result)
    (hholds : shapeFact.Holds declarations store value) :
    result.Holds declarations store value := by
  induction shapes generalizing result with
  | nil => contradiction
  | cons head tail ih =>
      simp only [applyShapeFacts, bind, Except.bind] at hresult
      cases hhead : step head with
      | error error => simp [hhead, Except.map] at hresult
      | ok headFact =>
          cases htail : applyShapeFacts step tail with
          | error error => simp [hhead, htail, Except.map] at hresult
          | ok tailFact =>
              simp [hhead, htail, Except.map] at hresult
              change Except.ok (headFact.join tailFact) =
                Except.ok result at hresult
              injection hresult with hresultEq
              subst result
              rcases List.mem_cons.mp hmember with hsame | hmember
              · subst head
                have : headFact = shapeFact := by
                  rw [hhead] at hshape
                  injection hshape
                subst headFact
                exact Fact.holds_join (Or.inl hholds)
              · exact Fact.holds_join (Or.inr
                  (ih hmember htail))

theorem applyShapeFacts_ne_ok_of_member_error
    {step : HeapShape → Except String Fact} {shapes : List HeapShape}
    {shape : HeapShape} {error : String} {result : Fact}
    (hmember : shape ∈ shapes)
    (hshape : step shape = .error error)
    (hresult : applyShapeFacts step shapes = .ok result) : False := by
  induction shapes generalizing result with
  | nil => contradiction
  | cons head tail ih =>
      simp only [applyShapeFacts, bind, Except.bind] at hresult
      cases hhead : step head with
      | error headError => simp [hhead] at hresult
      | ok headFact =>
          rw [hhead] at hresult
          simp only [bind, Except.bind] at hresult
          rcases List.mem_cons.mp hmember with hsame | hmember
          · subst head
            rw [hhead] at hshape
            contradiction
          · cases htail : applyShapeFacts step tail with
            | error tailError => simp [htail] at hresult
            | ok tailFact => exact ih hmember htail

/-! ## Fuel-indexed semantic theorem -/

private def CodeSoundAt (declarations : DeclEnv) (summaries : SummaryEnv)
    (fuel : Nat) : Prop :=
  ∀ ctx owner current store facts values code outputStore outputValue inferred,
    ctx.decls = declarations →
    AnalysisOwnerCompatible declarations summaries owner current →
    EnvironmentHolds declarations store facts values →
    analyzeCode declarations summaries owner current facts code = .ok inferred →
    runCode ctx fuel current store values code =
      .ok (outputStore, outputValue) →
    inferred.Holds declarations outputStore outputValue

private theorem analyzeAlternatives_sound
    {declarations : DeclEnv} {summaries : SummaryEnv} {fuel : Nat}
    (hcode : CodeSoundAt declarations summaries fuel)
    {ctx : Ctx} {owner : Address} {current : FnDef} {store : Store}
    {scrutineeFact : Fact} {peelNat : Bool}
    {facts : List Fact} {values : List RVal} {alternatives : List Alt}
    {cidx fieldCount : Nat} {body : Code} {fieldValues : List RVal}
    {outputStore : Store} {outputValue : RVal} {inferred : Fact}
    (hctx : ctx.decls = declarations)
    (hcurrent : AnalysisOwnerCompatible declarations summaries owner current)
    (henvironment : EnvironmentHolds declarations store facts values)
    (hmember : Alt.mk cidx fieldCount body ∈ alternatives)
    (hbinders : EnvironmentHolds declarations store
      (scrutineeFact.caseFields peelNat cidx fieldCount) fieldValues)
    (habstract : analyzeAlternatives declarations summaries owner current
      scrutineeFact peelNat facts alternatives = .ok inferred)
    (hconcrete : runCode ctx fuel current store (fieldValues ++ values) body =
      .ok (outputStore, outputValue)) :
    inferred.Holds declarations outputStore outputValue := by
  induction alternatives generalizing inferred with
  | nil => contradiction
  | cons head tail ih =>
      cases head with
      | mk headCidx headFields headBody =>
          simp only [analyzeAlternatives, bind, Except.bind] at habstract
          cases hhead : analyzeCode declarations summaries owner current
              (scrutineeFact.caseFields peelNat headCidx headFields ++ facts)
              headBody with
          | error error => simp [hhead] at habstract
          | ok headFact =>
              rw [hhead] at habstract
              simp only [bind, Except.bind] at habstract
              cases htail : analyzeAlternatives declarations summaries owner
                  current scrutineeFact peelNat facts tail with
              | error error => simp [htail] at habstract
              | ok tailFact =>
                  rw [htail] at habstract
                  change Except.ok (headFact.join tailFact) =
                    Except.ok inferred at habstract
                  injection habstract with hinferred
                  subst inferred
                  rcases List.mem_cons.mp hmember with hsame | hmember
                  · injection hsame with hcidx hfields hbody
                    subst headCidx
                    subst headFields
                    subst headBody
                    have hfront := hbinders.append henvironment
                    exact Fact.holds_join (Or.inl
                      (hcode ctx owner current store
                        (scrutineeFact.caseFields peelNat cidx fieldCount ++ facts)
                        (fieldValues ++ values) body outputStore outputValue
                        headFact hctx hcurrent hfront hhead hconcrete))
                  · exact Fact.holds_join (Or.inr
                      (ih hmember htail))

private def SoundAt (declarations : DeclEnv) (summaries : SummaryEnv)
  (fuel : Nat) : Prop :=
  CodeSoundAt declarations summaries fuel ∧
  (∀ ctx owner current store facts values operation outputStore outputValue inferred,
    ctx.decls = declarations →
    AnalysisOwnerCompatible declarations summaries owner current →
    EnvironmentHolds declarations store facts values →
    analyzeOp declarations summaries owner current facts operation = .ok inferred →
    runOp ctx fuel current store values operation =
      .ok (outputStore, outputValue) →
    inferred.Holds declarations outputStore outputValue) ∧
  (∀ ctx address arguments store outputStore outputValue fact,
    ctx.decls = declarations →
    callableResult declarations summaries address = .ok fact →
    invoke ctx fuel address arguments store = .ok (outputStore, outputValue) →
    fact.Holds declarations outputStore outputValue) ∧
  (∀ ctx store function arguments outputStore outputValue functionFact
      resultFact abstractFuel,
    ctx.decls = declarations →
    functionFact.Holds declarations store function →
    applyFact declarations summaries abstractFuel functionFact
      arguments.length = .ok resultFact →
    applyGo ctx fuel store function arguments = .ok (outputStore, outputValue) →
    resultFact.Holds declarations outputStore outputValue)

private theorem soundAt {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries) :
    ∀ fuel, SoundAt declarations summaries fuel := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ctx owner current store facts values code outputStore outputValue
          inferred hctx hcurrent henvironment habstract hconcrete
        rw [runCode.eq_def] at hconcrete
        simp at hconcrete
      · intro ctx owner current store facts values operation outputStore
          outputValue inferred hctx hcurrent henvironment habstract hconcrete
        rw [runOp.eq_def] at hconcrete
        simp at hconcrete
      · intro ctx address arguments store outputStore outputValue fact hctx
          habstract hconcrete
        rw [invoke.eq_def] at hconcrete
        simp at hconcrete
      · intro ctx store function arguments outputStore outputValue functionFact
          resultFact abstractFuel hctx hfunction habstract hconcrete
        rw [applyGo.eq_def] at hconcrete
        simp at hconcrete
  | succ fuel ih =>
      obtain ⟨ihCode, ihOp, ihInvoke, ihApply⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ctx owner current store facts values code outputStore outputValue
          inferred hctx hcurrent henvironment habstract hconcrete
        cases code with
        | ret atom =>
            have habstract' : resolveAtomFact facts atom = .ok inferred := by
              simpa only [analyzeCode] using habstract
            rw [runCode.eq_def] at hconcrete
            dsimp only at hconcrete
            cases hresolve : resolveAtom values atom with
            | error error =>
                rw [hresolve] at hconcrete
                simp only [bind, Except.bind] at hconcrete
                contradiction
            | ok value =>
                rw [hresolve] at hconcrete
                simp only [bind, Except.bind] at hconcrete
                change Except.ok (store, value) =
                  Except.ok (outputStore, outputValue) at hconcrete
                injection hconcrete with houtput
                cases houtput
                exact resolveAtom_sound henvironment habstract' hresolve
        | letOp operation rest =>
            simp only [analyzeCode, bind, Except.bind] at habstract
            cases haop : analyzeOp declarations summaries owner current facts
                operation with
            | error error =>
                rw [haop] at habstract
                contradiction
            | ok bound =>
                rw [haop] at habstract
                simp only [bind, Except.bind] at habstract
                rw [runCode.eq_def] at hconcrete
                dsimp only at hconcrete
                cases hop : runOp ctx fuel current store values operation with
                | error error =>
                    rw [hop] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok operationOutput =>
                    rcases operationOutput with ⟨middleStore, middleValue⟩
                    rw [hop] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    have hbound := ihOp ctx owner current store facts values
                      operation middleStore middleValue bound hctx hcurrent
                      henvironment haop hop
                    have hold := EnvironmentHolds.forgetHeap
                      (after := middleStore) henvironment
                    exact ihCode ctx owner current middleStore
                      (bound :: facts.map Fact.forgetHeap)
                      (middleValue :: values) rest outputStore outputValue
                      inferred hctx hcurrent (.cons hbound hold) habstract
                      hconcrete
        | case scrutinee peelNat alternatives =>
            simp only [analyzeCode, bind, Except.bind] at habstract
            cases hascrut : resolveAtomFact facts scrutinee with
            | error error =>
                rw [hascrut] at habstract
                contradiction
            | ok scrutineeFact =>
                rw [hascrut] at habstract
                simp only [bind, Except.bind] at habstract
                rw [runCode.eq_def] at hconcrete
                dsimp only at hconcrete
                cases hscrut : resolveAtom values scrutinee with
                | error error =>
                    rw [hscrut] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok scrutineeValue =>
                    rw [hscrut] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    have hscrutineeHolds : scrutineeFact.Holds declarations
                        store scrutineeValue :=
                      resolveAtom_sound henvironment hascrut hscrut
                    cases scrutineeValue with
                    | loc location =>
                        dsimp only at hconcrete
                        cases hbox : store.get? location with
                        | none => simp [hbox] at hconcrete
                        | some box =>
                            simp only [hbox] at hconcrete
                            cases box with
                            | mk world rc node =>
                                cases node with
                                | papN function arity captured =>
                                    simp at hconcrete
                                | ctorN identity fields =>
                                    cases halt : alternatives.find?
                                        (fun alternative =>
                                          alternative.cidx == identity.cidx) with
                                    | none => simp [halt] at hconcrete
                                    | some alternative =>
                                        cases alternative with
                                        | mk cidx fieldCount body =>
                                            cases hsize : fields.size != fieldCount
                                            · simp only [halt, hsize,
                                                Bool.false_eq_true, if_false]
                                                at hconcrete
                                              rw [Array.foldl_cons_eq_reverse_append]
                                                at hconcrete
                                              have hmember : Alt.mk cidx fieldCount body ∈
                                                  alternatives.toList := by
                                                simpa using
                                                  Array.mem_of_find?_eq_some halt
                                              have hcidx : identity.cidx = cidx := by
                                                have hmatch := Array.find?_some
                                                  (p := fun alternative : Alt =>
                                                    alternative.cidx ==
                                                      identity.cidx)
                                                  (a := .mk cidx fieldCount body)
                                                  (xs := alternatives) halt
                                                exact (beq_iff_eq.mp hmatch).symm
                                              have hfieldCount :
                                                  fields.size = fieldCount := by
                                                simpa using hsize
                                              have hbinders :=
                                                Fact.caseFields_ctor_holds
                                                  peelNat cidx fieldCount
                                                  hscrutineeHolds hbox rfl hcidx
                                                  hfieldCount
                                              exact analyzeAlternatives_sound ihCode
                                                hctx hcurrent henvironment hmember
                                                hbinders habstract hconcrete
                                            · simp [halt, hsize] at hconcrete
                    | lit literal =>
                        cases literal with
                        | str string => simp at hconcrete
                        | nat value =>
                            cases hpeel : peelNat with
                            | false => simp [hpeel] at hconcrete
                            | true =>
                                cases value with
                                | zero =>
                                    cases halt : alternatives.find?
                                        (fun alternative =>
                                          alternative.cidx == 0) with
                                    | none => simp [hpeel, halt] at hconcrete
                                    | some alternative =>
                                        cases alternative with
                                        | mk cidx fieldCount body =>
                                            cases fieldCount with
                                            | zero =>
                                                simp only [hpeel, halt]
                                                  at hconcrete
                                                have hmember : Alt.mk cidx 0 body ∈
                                                    alternatives.toList := by
                                                  simpa using
                                                    Array.mem_of_find?_eq_some halt
                                                have hbinders :
                                                    EnvironmentHolds declarations
                                                      store
                                                      (scrutineeFact.caseFields
                                                        peelNat cidx 0) [] := by
                                                  simpa [Fact.caseFields,
                                                    Fact.joinFieldVectors] using
                                                    (EnvironmentHolds.nil :
                                                      EnvironmentHolds
                                                        declarations store [] [])
                                                exact analyzeAlternatives_sound ihCode
                                                  hctx hcurrent henvironment
                                                  (fieldValues := []) hmember
                                                  hbinders
                                                  habstract (by
                                                    simpa using hconcrete)
                                            | succ fieldCount =>
                                                simp [hpeel, halt] at hconcrete
                                | succ value =>
                                    cases halt : alternatives.find?
                                        (fun alternative =>
                                          alternative.cidx == 1) with
                                    | none => simp [hpeel, halt] at hconcrete
                                    | some alternative =>
                                        cases alternative with
                                        | mk cidx fieldCount body =>
                                            cases fieldCount with
                                            | zero =>
                                                simp [hpeel, halt] at hconcrete
                                            | succ fieldCount =>
                                                cases fieldCount with
                                                | zero =>
                                                    simp only [hpeel, halt]
                                                      at hconcrete
                                                    have hmember :
                                                        Alt.mk cidx 1 body ∈
                                                          alternatives.toList := by
                                                      simpa using
                                                        Array.mem_of_find?_eq_some halt
                                                    have hcidx : cidx = 1 := by
                                                      have hmatch := Array.find?_some
                                                        (p := fun alternative : Alt =>
                                                          alternative.cidx == 1)
                                                        (a := .mk cidx 1 body)
                                                        (xs := alternatives) halt
                                                      exact beq_iff_eq.mp hmatch
                                                    have hbinders :
                                                        EnvironmentHolds declarations
                                                          store
                                                          (scrutineeFact.caseFields
                                                            peelNat cidx 1)
                                                          [.lit (.nat value)] := by
                                                      simpa [hpeel, hcidx] using
                                                        (Fact.caseFields_natSucc_holds
                                                          hscrutineeHolds)
                                                    exact
                                                      analyzeAlternatives_sound ihCode
                                                        hctx hcurrent henvironment
                                                        (fieldValues :=
                                                          [.lit (.nat value)])
                                                        hmember hbinders habstract (by
                                                          simpa using hconcrete)
                                                | succ fieldCount =>
                                                    simp [hpeel, halt] at hconcrete
                    | erased => simp at hconcrete
      · intro ctx owner current store facts values operation outputStore
          outputValue inferred hctx hcurrent henvironment habstract hconcrete
        cases operation with
        | pure atom =>
            have habstract' : resolveAtomFact facts atom = .ok inferred := by
              simpa only [analyzeOp] using habstract
            rw [runOp.eq_def] at hconcrete
            dsimp only at hconcrete
            cases hresolve : resolveAtom values atom with
            | error error =>
                rw [hresolve] at hconcrete
                simp only [bind, Except.bind] at hconcrete
                contradiction
            | ok value =>
                rw [hresolve] at hconcrete
                simp only [bind, Except.bind] at hconcrete
                change Except.ok (store, value) =
                  Except.ok (outputStore, outputValue) at hconcrete
                injection hconcrete with houtput
                cases houtput
                exact resolveAtom_sound henvironment habstract' hresolve
        | alloc world identity arguments =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFacts facts arguments with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok argumentFacts =>
                rw [hvalid] at habstract
                change Except.ok (Fact.heap (.ctor identity
                  (some (argumentFacts.map FieldFact.ofFact)))) =
                  Except.ok inferred at habstract
                injection habstract with hinferred
                subst inferred
                rw [runOp.eq_def] at hconcrete
                dsimp only at hconcrete
                cases harguments : resolveAtoms values arguments with
                | error error =>
                    rw [harguments] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok resolved =>
                    rw [harguments] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    change Except.ok
                        ((store.allocNode world
                          (.ctorN identity resolved.toArray)).1,
                          .loc (store.allocNode world
                            (.ctorN identity resolved.toArray)).2) =
                      Except.ok (outputStore, outputValue) at hconcrete
                    injection hconcrete with houtput
                    cases houtput
                    have hfields := resolveAtomFacts_sound henvironment hvalid
                      harguments
                    apply Fact.heap_holds
                    exact ⟨⟨world, 1, .ctorN identity resolved.toArray⟩,
                      resolved.toArray,
                      get?_allocNode_new store world
                        (.ctorN identity resolved.toArray), rfl,
                      by simpa using
                        hfields.toFieldFactsAllocNode
                          (world := world)
                          (node := .ctorN identity resolved.toArray)⟩
        | reuse target identity arguments =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFacts facts arguments with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok argumentFacts =>
                rw [hvalid] at habstract
                cases htargetFact : resolveAtomFact facts target with
                | error error =>
                    rw [htargetFact] at habstract
                    contradiction
                | ok targetFact =>
                    rw [htargetFact] at habstract
                    change Except.ok (Fact.heap (.ctor identity
                      (some (argumentFacts.map fun fact =>
                        FieldFact.ofFact fact.forgetHeap)))) =
                      Except.ok inferred at habstract
                    injection habstract with hinferred
                    subst inferred
                    rw [runOp.eq_def] at hconcrete
                    dsimp only at hconcrete
                    cases harguments : resolveAtoms values arguments with
                    | error error =>
                        rw [harguments] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        contradiction
                    | ok resolved =>
                        rw [harguments] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        cases htarget : resolveAtom values target with
                        | error error =>
                            rw [htarget] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok targetValue =>
                            rw [htarget] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            cases targetValue with
                            | lit literal => simp at hconcrete
                            | erased => simp at hconcrete
                            | loc location =>
                                cases hbox : store.get? location with
                                | none => simp [hbox] at hconcrete
                                | some box =>
                                    simp only [hbox] at hconcrete
                                    cases box with
                                    | mk boxWorld rc node =>
                                        cases boxWorld with
                                        | shared => simp at hconcrete
                                        | unique =>
                                            change Except.ok
                                                ({ store.setBox location
                                                    ⟨.unique, 1,
                                                      .ctorN identity
                                                        resolved.toArray⟩ with
                                                  reuses :=
                                                    (store.setBox location
                                                      ⟨.unique, 1,
                                                        .ctorN identity
                                                          resolved.toArray⟩).reuses + 1 },
                                                  .loc location) =
                                              Except.ok
                                                (outputStore, outputValue)
                                              at hconcrete
                                            injection hconcrete with houtput
                                            cases houtput
                                            have hfields :=
                                              resolveAtomFacts_sound henvironment
                                                hvalid harguments
                                            apply Fact.heap_holds
                                            refine ⟨⟨.unique, 1,
                                                .ctorN identity resolved.toArray⟩,
                                              resolved.toArray, ?_, rfl, ?_⟩
                                            · simpa [Store.get?] using
                                                (get?_setBox_same
                                                  (new := ⟨.unique, 1,
                                                    .ctorN identity
                                                      resolved.toArray⟩)
                                                  hbox)
                                            · simpa using hfields.toFieldFactsForget
                                                (after :=
                                                  { store.setBox location
                                                      ⟨.unique, 1,
                                                        .ctorN identity
                                                          resolved.toArray⟩ with
                                                    reuses :=
                                                      (store.setBox location
                                                        ⟨.unique, 1,
                                                          .ctorN identity
                                                            resolved.toArray⟩).reuses + 1 })
        | free target =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFact facts target with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok fact =>
                rw [hvalid] at habstract
                change Except.ok Fact.scalar = Except.ok inferred at habstract
                injection habstract with hinferred
                subst inferred
                rw [runOp.eq_def] at hconcrete
                dsimp only at hconcrete
                cases htarget : resolveAtom values target with
                | error error =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok targetValue =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    cases targetValue with
                    | lit literal => simp at hconcrete
                    | erased => simp at hconcrete
                    | loc location =>
                        cases hbox : store.get? location with
                        | none => simp [hbox] at hconcrete
                        | some box =>
                            simp only [hbox] at hconcrete
                            cases box with
                            | mk boxWorld rc node =>
                                cases boxWorld with
                                | shared => simp at hconcrete
                                | unique =>
                                    injection hconcrete with houtput
                                    cases houtput
                                    simp [Fact.Holds, Fact.scalar]
        | dup target =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFact facts target with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok fact =>
                rw [hvalid] at habstract
                change Except.ok Fact.top = Except.ok inferred at habstract
                injection habstract with hinferred
                subst inferred
                exact Fact.top_holds declarations outputStore outputValue
        | drop target =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFact facts target with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok fact =>
                rw [hvalid] at habstract
                change Except.ok Fact.scalar = Except.ok inferred at habstract
                injection habstract with hinferred
                subst inferred
                rw [runOp.eq_def] at hconcrete
                dsimp only at hconcrete
                cases htarget : resolveAtom values target with
                | error error =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok targetValue =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    cases targetValue with
                    | lit literal =>
                        injection hconcrete with houtput
                        cases houtput
                        simp [Fact.Holds, Fact.scalar]
                    | erased =>
                        injection hconcrete with houtput
                        cases houtput
                        simp [Fact.Holds, Fact.scalar]
                    | loc location =>
                        dsimp only at hconcrete
                        cases hdrop : dropVal ctx fuel store (.loc location) with
                        | error error =>
                            rw [hdrop] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok dropped =>
                            rw [hdrop] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            injection hconcrete with houtput
                            cases houtput
                            simp [Fact.Holds, Fact.scalar]
        | dropU target =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFact facts target with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok fact =>
                rw [hvalid] at habstract
                change Except.ok Fact.scalar = Except.ok inferred at habstract
                injection habstract with hinferred
                subst inferred
                rw [runOp.eq_def] at hconcrete
                dsimp only at hconcrete
                cases htarget : resolveAtom values target with
                | error error =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok targetValue =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    cases targetValue with
                    | lit literal =>
                        injection hconcrete with houtput
                        cases houtput
                        simp [Fact.Holds, Fact.scalar]
                    | erased =>
                        injection hconcrete with houtput
                        cases houtput
                        simp [Fact.Holds, Fact.scalar]
                    | loc location =>
                        dsimp only at hconcrete
                        cases hdrop : dropUVal ctx fuel store (.loc location) with
                        | error error =>
                            rw [hdrop] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok dropped =>
                            rw [hdrop] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            injection hconcrete with houtput
                            cases houtput
                            simp [Fact.Holds, Fact.scalar]
        | fetch target field =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFact facts target with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok fact =>
                rw [hvalid] at habstract
                change Except.ok (fact.fetch field) = Except.ok inferred
                  at habstract
                injection habstract with hinferred
                subst inferred
                rw [runOp.eq_def] at hconcrete
                dsimp only at hconcrete
                cases htarget : resolveAtom values target with
                | error error =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok targetValue =>
                    rw [htarget] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    cases targetValue with
                    | lit literal => simp at hconcrete
                    | erased => simp at hconcrete
                    | loc location =>
                        cases hbox : store.get? location with
                        | none => simp [hbox] at hconcrete
                        | some box =>
                            simp only [hbox] at hconcrete
                            cases box with
                            | mk world rc node =>
                                cases node with
                                | papN function arity captured =>
                                    simp at hconcrete
                                | ctorN identity fields =>
                                    cases hfield : fields[field]? with
                                    | none => simp [hfield] at hconcrete
                                    | some value =>
                                        simp only [hfield] at hconcrete
                                        injection hconcrete with houtput
                                        cases houtput
                                        exact Fact.fetch_holds
                                          (resolveAtom_sound henvironment hvalid
                                            htarget)
                                          hbox rfl hfield
        | call address arguments =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFacts facts arguments with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok unit =>
                rw [hvalid] at habstract
                simp only [bind, Except.bind] at habstract
                cases hdecl : declarations address with
                | none => simp [hdecl] at habstract
                | some declaration =>
                    simp only [hdecl] at habstract
                    cases harity : arguments.size != declArity declaration
                    ·
                        simp only [harity, Bool.false_eq_true, if_false]
                          at habstract
                        rw [runOp.eq_def] at hconcrete
                        dsimp only at hconcrete
                        cases harguments : resolveAtoms values arguments with
                        | error error =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok resolved =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            exact ihInvoke ctx address resolved store outputStore
                              outputValue inferred hctx habstract hconcrete
                    · simp [harity] at habstract
        | callSelf arguments =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFacts facts arguments with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok unit =>
                rw [hvalid] at habstract
                simp only [bind, Except.bind] at habstract
                cases habstractArity : arguments.size != current.arity
                ·
                    simp only [habstractArity, Bool.false_eq_true, if_false]
                      at habstract
                    cases hsummary : summaries owner with
                    | none => simp [hsummary] at habstract
                    | some claimed =>
                        rw [hsummary] at habstract
                        change Except.ok claimed = Except.ok inferred at habstract
                        injection habstract with hinferred
                        subst inferred
                        have hcurrentDecl :
                            declarations owner = some (.fn current) := by
                          rcases hcurrent with hcurrent | hmissing
                          · exact hcurrent
                          · rw [hsummary] at hmissing
                            contradiction
                        obtain ⟨localFact, hlocal, hle⟩ :=
                          hpost owner current claimed hcurrentDecl hsummary
                        rw [runOp.eq_def] at hconcrete
                        dsimp only at hconcrete
                        cases harguments : resolveAtoms values arguments with
                        | error error =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok resolved =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            cases hconcreteArity : resolved.length != current.arity
                            ·
                                simp only [hconcreteArity, Bool.false_eq_true,
                                  if_false] at hconcrete
                                cases hbody : runCode ctx fuel current store
                                    resolved.reverse current.body with
                                | error error =>
                                    rw [hbody] at hconcrete
                                    simp only [bind, Except.bind] at hconcrete
                                    contradiction
                                | ok bodyOutput =>
                                    rw [hbody] at hconcrete
                                    simp only [bind, Except.bind] at hconcrete
                                    have houtput :=
                                      eq_of_checkResultWorld_eq_ok hconcrete
                                    rcases bodyOutput with
                                      ⟨bodyStore, bodyValue⟩
                                    cases houtput
                                    have hlength : resolved.length =
                                        current.arity := by
                                      simpa using hconcreteArity
                                    have henv :=
                                      EnvironmentHolds.top_replicate
                                        declarations store resolved.reverse
                                    rw [List.length_reverse, hlength] at henv
                                    have hbodySound := ihCode ctx owner current
                                      store
                                      (List.replicate current.arity Fact.top)
                                      resolved.reverse current.body outputStore
                                      outputValue localFact hctx hcurrent henv
                                      (by simpa [inferFunction] using hlocal)
                                      hbody
                                    exact Fact.holds_of_le hle hbodySound
                            · simp [hconcreteArity] at hconcrete
                · simp [habstractArity] at habstract
        | papp address arguments =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFacts facts arguments with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok unit =>
                rw [hvalid] at habstract
                simp only [bind, Except.bind] at habstract
                cases hdecl : declarations address with
                | none => simp [hdecl] at habstract
                | some declaration =>
                    simp only [hdecl] at habstract
                    by_cases hless : arguments.size < declArity declaration
                    ·
                        simp only [hless, if_true] at habstract
                        change Except.ok
                            (Fact.heap (.pap address arguments.size)) =
                          Except.ok inferred at habstract
                        injection habstract with hinferred
                        subst inferred
                        rw [runOp.eq_def] at hconcrete
                        dsimp only at hconcrete
                        cases harguments : resolveAtoms values arguments with
                        | error error =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok resolved =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            have hdeclConcrete : ctx.decls address =
                                some declaration := by
                              rw [hctx]
                              exact hdecl
                            simp only [hdeclConcrete] at hconcrete
                            have hlength := resolveAtoms_length harguments
                            have hlessConcrete : resolved.length <
                                declArity declaration := by
                              simpa [hlength] using hless
                            simp only [hlessConcrete, if_true] at hconcrete
                            change Except.ok
                                ((store.allocNode .shared
                                  (.papN address (declArity declaration)
                                    resolved.toArray)).1,
                                  .loc (store.allocNode .shared
                                    (.papN address (declArity declaration)
                                      resolved.toArray)).2) =
                              Except.ok (outputStore, outputValue) at hconcrete
                            injection hconcrete with houtput
                            cases houtput
                            apply Fact.heap_holds
                            refine ⟨⟨.shared, 1,
                                .papN address (declArity declaration)
                                  resolved.toArray⟩,
                              resolved.toArray, declaration,
                              get?_allocNode_new store .shared
                                (.papN address (declArity declaration)
                                  resolved.toArray), hdecl, rfl, ?_, ?_⟩
                            · simpa [hlength]
                            · exact hless
                    · simp [hless] at habstract
        | apply function arguments =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hfunctionAbstract : resolveAtomFact facts function with
            | error error =>
                rw [hfunctionAbstract] at habstract
                contradiction
            | ok functionFact =>
                rw [hfunctionAbstract] at habstract
                simp only [bind, Except.bind] at habstract
                cases hvalid : resolveAtomFacts facts arguments with
                | error error =>
                    rw [hvalid] at habstract
                    contradiction
                | ok unit =>
                    rw [hvalid] at habstract
                    simp only [bind, Except.bind] at habstract
                    rw [runOp.eq_def] at hconcrete
                    dsimp only at hconcrete
                    cases hfunctionConcrete : resolveAtom values function with
                    | error error =>
                        rw [hfunctionConcrete] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        contradiction
                    | ok functionValue =>
                        rw [hfunctionConcrete] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        cases harguments : resolveAtoms values arguments with
                        | error error =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok resolved =>
                            rw [harguments] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            have hlength := resolveAtoms_length harguments
                            have hfunctionHolds := resolveAtom_sound henvironment
                              hfunctionAbstract hfunctionConcrete
                            exact ihApply ctx store functionValue resolved
                              outputStore outputValue functionFact inferred
                              (arguments.size + 1) hctx hfunctionHolds
                              (by simpa [hlength] using habstract) hconcrete
        | extern address arguments =>
            simp only [analyzeOp, bind, Except.bind] at habstract
            cases hvalid : resolveAtomFacts facts arguments with
            | error error =>
                rw [hvalid] at habstract
                contradiction
            | ok unit =>
                rw [hvalid] at habstract
                change Except.ok Fact.scalar = Except.ok inferred at habstract
                injection habstract with hinferred
                subst inferred
                rw [runOp.eq_def] at hconcrete
                dsimp only at hconcrete
                cases harguments : resolveAtoms values arguments with
                | error error =>
                    rw [harguments] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    contradiction
                | ok resolved =>
                    rw [harguments] at hconcrete
                    simp only [bind, Except.bind] at hconcrete
                    cases horacle : callScalarOracle ctx address resolved with
                    | error error =>
                        rw [horacle] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        contradiction
                    | ok value =>
                        rw [horacle] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        change Except.ok (store, value) =
                          Except.ok (outputStore, outputValue) at hconcrete
                        injection hconcrete with houtput
                        cases houtput
                        rw [Fact.scalar_holds_iff]
                        exact scalar_of_callScalarOracle_eq_ok horacle
      · intro ctx address arguments store outputStore outputValue fact hctx
          habstract hconcrete
        rw [invoke.eq_def] at hconcrete
        dsimp only at hconcrete
        cases hdeclConcrete : ctx.decls address with
        | none => simp [hdeclConcrete] at hconcrete
        | some declaration =>
            simp only [hdeclConcrete] at hconcrete
            have hdecl : declarations address = some declaration := by
              rw [← hctx]
              exact hdeclConcrete
            cases declaration with
            | extern arity =>
                cases harity : arguments.length != arity
                ·
                    simp only [harity, Bool.false_eq_true, if_false]
                      at hconcrete
                    cases horacle : callScalarOracle ctx address arguments with
                    | error error => simp [horacle] at hconcrete
                    | ok value =>
                        simp only [horacle] at hconcrete
                        injection hconcrete with houtput
                        cases houtput
                        have hfact : fact = Fact.scalar := by
                          simpa [callableResult, hdecl] using habstract.symm
                        subst fact
                        rw [Fact.scalar_holds_iff]
                        exact scalar_of_callScalarOracle_eq_ok horacle
                · simp [harity] at hconcrete
            | fn function =>
                cases harity : arguments.length != function.arity
                ·
                    simp only [harity, Bool.false_eq_true, if_false]
                      at hconcrete
                    cases hbody : runCode ctx fuel function store
                        arguments.reverse function.body with
                    | error error =>
                        rw [hbody] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        contradiction
                    | ok bodyOutput =>
                        rw [hbody] at hconcrete
                        simp only [bind, Except.bind] at hconcrete
                        have houtput := eq_of_checkResultWorld_eq_ok hconcrete
                        rcases bodyOutput with ⟨bodyStore, bodyValue⟩
                        cases houtput
                        cases hsummary : summaries address with
                        | none => simp [callableResult, hdecl, hsummary]
                            at habstract
                        | some claimed =>
                            have hfact : claimed = fact := by
                              simpa [callableResult, hdecl, hsummary] using
                                habstract
                            subst fact
                            obtain ⟨localFact, hlocal, hle⟩ :=
                              hpost address function claimed hdecl hsummary
                            have hlength : arguments.length = function.arity := by
                              simpa using harity
                            have henvironment :=
                              EnvironmentHolds.top_replicate declarations store
                                arguments.reverse
                            rw [List.length_reverse, hlength] at henvironment
                            have hbodySound := ihCode ctx address function store
                              (List.replicate function.arity Fact.top)
                              arguments.reverse function.body outputStore
                              outputValue
                              localFact hctx (.inl hdecl) henvironment
                              (by simpa [inferFunction] using hlocal) hbody
                            exact Fact.holds_of_le hle hbodySound
                · simp [harity] at hconcrete
      · intro ctx store function arguments outputStore outputValue functionFact
          resultFact abstractFuel hctx hfunction habstract hconcrete
        cases abstractFuel with
        | zero =>
            simp only [applyFact, Except.ok.injEq] at habstract
            subst resultFact
            exact Fact.top_holds declarations outputStore outputValue
        | succ abstractFuel =>
            rw [applyFact] at habstract
            dsimp only at habstract
            cases hunknown : functionFact.unknownHeap with
            | true =>
                simp only [hunknown, if_true] at habstract
                change Except.ok Fact.top = Except.ok resultFact at habstract
                injection habstract with hresult
                subst resultFact
                exact Fact.top_holds declarations outputStore outputValue
            | false =>
                simp only [hunknown, Bool.false_eq_true, if_false]
                  at habstract
                cases hheap : applyShapeFacts
                    (applyShapeFact declarations summaries
                      (applyFact declarations summaries abstractFuel)
                      arguments.length) functionFact.shapes with
                | error error =>
                    rw [hheap] at habstract
                    simp only [bind, Except.bind] at habstract
                    contradiction
                | ok heapFact =>
                    rw [hheap] at habstract
                    change Except.ok
                        ((if functionFact.mayScalar then Fact.scalar
                          else Fact.bottom).join heapFact) =
                      Except.ok resultFact at habstract
                    injection habstract with hresult
                    subst resultFact
                    rw [applyGo.eq_def] at hconcrete
                    dsimp only at hconcrete
                    cases function with
                    | lit literal => simp at hconcrete
                    | erased =>
                        cases hdrop : dropMany ctx fuel store arguments with
                        | error error =>
                            rw [hdrop] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            contradiction
                        | ok dropped =>
                            rw [hdrop] at hconcrete
                            simp only [bind, Except.bind] at hconcrete
                            change Except.ok (dropped, RVal.erased) =
                              Except.ok (outputStore, outputValue) at hconcrete
                            injection hconcrete with houtput
                            cases houtput
                            change functionFact.mayScalar = true at hfunction
                            apply Fact.holds_join
                            apply Or.inl
                            simp [hfunction, Fact.Holds, Fact.scalar]
                    | loc location =>
                        cases hbox : store.get? location with
                        | none => simp [hbox] at hconcrete
                        | some box =>
                            simp only [hbox] at hconcrete
                            cases box with
                            | mk world rc node =>
                                cases node with
                                | ctorN identity fields => simp at hconcrete
                                | papN address arity captured =>
                                    simp only at hconcrete
                                    simp only [Fact.Holds] at hfunction
                                    rcases hfunction with hunknown' |
                                      ⟨shape, hmember, hshape⟩
                                    · simp [hunknown] at hunknown'
                                    · cases shape with
                                      | ctor shapeIdentity shapeFacts =>
                                          simp only [HeapShape.Holds] at hshape
                                          obtain ⟨shapeBox, shapeFields,
                                            hshapeBox, hshapeNode, _⟩ := hshape
                                          have : shapeBox =
                                              ⟨world, rc,
                                                .papN address arity captured⟩ := by
                                            injection hshapeBox.symm.trans hbox
                                          subst shapeBox
                                          simp at hshapeNode
                                      | pap shapeAddress supplied =>
                                          simp only [HeapShape.Holds] at hshape
                                          obtain ⟨shapeBox, shapeArguments,
                                            declaration, hshapeBox, hdecl,
                                            hshapeNode, hsupplied, hproper⟩ :=
                                            hshape
                                          have hboxEq : shapeBox =
                                              ⟨world, rc,
                                                .papN address arity captured⟩ := by
                                            injection hshapeBox.symm.trans hbox
                                          subst shapeBox
                                          simp only [NodeBox.node] at hshapeNode
                                          injection hshapeNode with haddress
                                            harity hcaptured
                                          subst shapeAddress
                                          subst arity
                                          subst shapeArguments
                                          cases hdup : dupVals store captured.toList with
                                          | error error =>
                                              rw [hdup] at hconcrete
                                              simp only [bind, Except.bind]
                                                at hconcrete
                                              contradiction
                                          | ok duplicated =>
                                              rw [hdup] at hconcrete
                                              simp only [bind, Except.bind]
                                                at hconcrete
                                              cases hdrop : dropVal ctx fuel
                                                  duplicated (.loc location) with
                                              | error error =>
                                                  rw [hdrop] at hconcrete
                                                  simp only [bind, Except.bind]
                                                    at hconcrete
                                                  contradiction
                                              | ok ready =>
                                                  rw [hdrop] at hconcrete
                                                  simp only [bind, Except.bind]
                                                    at hconcrete
                                                  have hcapturedLength :
                                                      captured.toList.length =
                                                        supplied := by
                                                    simpa using hsupplied
                                                  have htotalLength :
                                                      (captured.toList ++ arguments).length =
                                                        supplied + arguments.length := by
                                                    simp [hcapturedLength]
                                                  by_cases hunder :
                                                      (captured.toList ++
                                                        arguments).length <
                                                          declArity declaration
                                                  ·
                                                      simp only [hunder, if_true]
                                                        at hconcrete
                                                      change Except.ok
                                                          ((ready.allocNode .shared
                                                            (.papN address
                                                              (declArity declaration)
                                                              ((captured.toList ++
                                                                arguments).toArray))).1,
                                                            .loc
                                                              (ready.allocNode .shared
                                                                (.papN address
                                                                  (declArity declaration)
                                                                  ((captured.toList ++
                                                                    arguments).toArray))).2) =
                                                        Except.ok
                                                          (outputStore, outputValue)
                                                        at hconcrete
                                                      injection hconcrete with
                                                        houtput
                                                      cases houtput
                                                      have hunderAbstract :
                                                          supplied + arguments.length <
                                                            declArity declaration := by
                                                        simpa [htotalLength] using hunder
                                                      let shapeFact := Fact.heap
                                                        (.pap address
                                                          (supplied + arguments.length))
                                                      have hstep :
                                                          applyShapeFact declarations
                                                            summaries
                                                            (applyFact declarations summaries
                                                              abstractFuel)
                                                            arguments.length
                                                            (.pap address supplied) =
                                                              .ok shapeFact := by
                                                        simp [applyShapeFact, hdecl,
                                                          hproper, hunderAbstract,
                                                          shapeFact]
                                                        change Except.ok
                                                            (Fact.heap (.pap address
                                                              (supplied + arguments.length))) =
                                                          Except.ok
                                                            (Fact.heap (.pap address
                                                              (supplied + arguments.length)))
                                                        rfl
                                                      have hshapeFact :
                                                          shapeFact.Holds declarations
                                                            (ready.allocNode .shared
                                                              (.papN address
                                                                (declArity declaration)
                                                                ((captured.toList ++
                                                                  arguments).toArray))).1
                                                            (.loc
                                                              (ready.allocNode .shared
                                                                (.papN address
                                                                  (declArity declaration)
                                                                  ((captured.toList ++
                                                                    arguments).toArray))).2) := by
                                                        apply Fact.heap_holds
                                                        refine ⟨⟨.shared, 1,
                                                            .papN address
                                                              (declArity declaration)
                                                              ((captured.toList ++
                                                                arguments).toArray)⟩,
                                                          (captured.toList ++
                                                            arguments).toArray,
                                                          declaration,
                                                          get?_allocNode_new ready .shared
                                                            (.papN address
                                                              (declArity declaration)
                                                              ((captured.toList ++
                                                                arguments).toArray)),
                                                          hdecl, rfl, ?_,
                                                          hunderAbstract⟩
                                                        simpa [htotalLength]
                                                      apply Fact.holds_join
                                                      exact Or.inr
                                                        (holds_of_applyShapeFacts_member
                                                          hmember hstep hheap hshapeFact)
                                                  ·
                                                      simp only [hunder,
                                                        if_false]
                                                        at hconcrete
                                                      have hpapsafe :
                                                          declPapSafe declaration = true := by
                                                        cases hsafety :
                                                            declPapSafe declaration with
                                                        | false =>
                                                            simp [hctx, hdecl, hsafety]
                                                              at hconcrete
                                                        | true => rfl
                                                      simp only [hctx, hdecl, hpapsafe,
                                                        if_true] at hconcrete
                                                      by_cases hexactEq :
                                                          (((captured.toList ++
                                                            arguments).length ==
                                                              declArity declaration) = true)
                                                      · have hexact :
                                                            ((captured.toList ++
                                                              arguments).length ==
                                                                declArity declaration) = true :=
                                                          hexactEq
                                                        simp only [hexact, if_true]
                                                          at hconcrete
                                                        have hexactAbstract :
                                                              supplied + arguments.length =
                                                                declArity declaration := by
                                                            have := beq_iff_eq.mp hexact
                                                            omega
                                                        cases hreturned :
                                                              callableResult declarations
                                                                summaries address with
                                                          | error error =>
                                                              have hstepError :
                                                                  applyShapeFact declarations
                                                                    summaries
                                                                    (applyFact declarations
                                                                      summaries abstractFuel)
                                                                    arguments.length
                                                                    (.pap address supplied) =
                                                                      .error error := by
                                                                simp [applyShapeFact, hdecl,
                                                                  hproper, hexactAbstract,
                                                                  hreturned]
                                                              exact False.elim
                                                                (applyShapeFacts_ne_ok_of_member_error
                                                                  hmember hstepError hheap)
                                                          | ok returned =>
                                                              have hstep :
                                                                  applyShapeFact declarations
                                                                    summaries
                                                                    (applyFact declarations
                                                                      summaries abstractFuel)
                                                                    arguments.length
                                                                    (.pap address supplied) =
                                                                      .ok returned := by
                                                                simp [applyShapeFact, hdecl,
                                                                  hproper, hexactAbstract,
                                                                  hreturned]
                                                              have hreturnedHolds := ihInvoke
                                                                ctx address
                                                                (captured.toList ++ arguments)
                                                                ready outputStore outputValue
                                                                returned hctx hreturned hconcrete
                                                              apply Fact.holds_join
                                                              exact Or.inr
                                                                (holds_of_applyShapeFacts_member
                                                                  hmember hstep hheap
                                                                  hreturnedHolds)
                                                      · have hexact :
                                                            ((captured.toList ++
                                                              arguments).length ==
                                                                declArity declaration) = false := by
                                                          simpa using hexactEq
                                                        simp only [hexact,
                                                          Bool.false_eq_true, if_false]
                                                          at hconcrete
                                                        have hoverAbstract :
                                                              declArity declaration <
                                                                supplied + arguments.length := by
                                                            have hnunder : ¬
                                                                supplied + arguments.length <
                                                                  declArity declaration := by
                                                              simpa [htotalLength] using hunder
                                                            have hneConcrete :
                                                                (captured.toList ++
                                                                  arguments).length ≠
                                                                    declArity declaration := by
                                                              intro heq
                                                              apply hexactEq
                                                              simpa [heq]
                                                            omega
                                                        have hnunderAbstract : ¬
                                                            supplied + arguments.length <
                                                              declArity declaration := by
                                                          omega
                                                        have hneAbstract :
                                                            supplied + arguments.length ≠
                                                              declArity declaration := by
                                                          omega
                                                        cases hreturned :
                                                              callableResult declarations
                                                                summaries address with
                                                          | error error =>
                                                              have hstepError :
                                                                  applyShapeFact declarations
                                                                    summaries
                                                                    (applyFact declarations
                                                                      summaries abstractFuel)
                                                                    arguments.length
                                                                    (.pap address supplied) =
                                                                      .error error := by
                                                                simp [applyShapeFact, hdecl,
                                                                  hproper, hnunderAbstract,
                                                                  hneAbstract,
                                                                  hreturned]
                                                                simp only [bind, Except.bind]
                                                              exact False.elim
                                                                (applyShapeFacts_ne_ok_of_member_error
                                                                  hmember hstepError hheap)
                                                          | ok returned =>
                                                              cases happlied :
                                                                  applyFact declarations summaries
                                                                    abstractFuel returned
                                                                    (supplied + arguments.length -
                                                                      declArity declaration) with
                                                              | error error =>
                                                                  have hstepError :
                                                                      applyShapeFact declarations
                                                                        summaries
                                                                        (applyFact declarations
                                                                          summaries abstractFuel)
                                                                        arguments.length
                                                                        (.pap address supplied) =
                                                                          .error error := by
                                                                    simp [applyShapeFact, hdecl,
                                                                      hproper, hnunderAbstract,
                                                                      hneAbstract,
                                                                      hreturned, happlied]
                                                                    simpa only [bind, Except.bind]
                                                                      using happlied
                                                                  exact False.elim
                                                                    (applyShapeFacts_ne_ok_of_member_error
                                                                      hmember hstepError hheap)
                                                              | ok applied =>
                                                                  have hstep :
                                                                      applyShapeFact declarations
                                                                        summaries
                                                                        (applyFact declarations
                                                                          summaries abstractFuel)
                                                                        arguments.length
                                                                        (.pap address supplied) =
                                                                          .ok applied := by
                                                                    simp [applyShapeFact, hdecl,
                                                                      hproper, hnunderAbstract,
                                                                      hneAbstract,
                                                                      hreturned, happlied]
                                                                    simpa only [bind, Except.bind]
                                                                      using happlied
                                                                  cases hinvoke : invoke ctx fuel
                                                                      address
                                                                      ((captured.toList ++ arguments).take
                                                                        (declArity declaration))
                                                                      ready with
                                                                  | error error =>
                                                                      rw [hinvoke] at hconcrete
                                                                      simp only [bind, Except.bind]
                                                                        at hconcrete
                                                                      contradiction
                                                                  | ok called =>
                                                                      rcases called with
                                                                        ⟨calledStore, calledValue⟩
                                                                      rw [hinvoke] at hconcrete
                                                                      simp only [bind, Except.bind]
                                                                        at hconcrete
                                                                      have hreturnedHolds := ihInvoke
                                                                        ctx address
                                                                        ((captured.toList ++
                                                                          arguments).take
                                                                            (declArity declaration))
                                                                        ready calledStore calledValue
                                                                        returned hctx hreturned hinvoke
                                                                      have hdropLength :
                                                                          ((captured.toList ++
                                                                            arguments).drop
                                                                              (declArity declaration)).length =
                                                                            supplied + arguments.length -
                                                                              declArity declaration := by
                                                                        simp [List.length_drop,
                                                                          htotalLength]
                                                                      have happliedHolds := ihApply ctx
                                                                        calledStore calledValue
                                                                        ((captured.toList ++ arguments).drop
                                                                          (declArity declaration))
                                                                        outputStore outputValue returned
                                                                        applied abstractFuel hctx
                                                                        hreturnedHolds
                                                                        (by simpa [hdropLength] using
                                                                          happlied)
                                                                        hconcrete
                                                                      apply Fact.holds_join
                                                                      exact Or.inr
                                                                        (holds_of_applyShapeFacts_member
                                                                          hmember hstep hheap
                                                                          happliedHolds)

/-! ## Public semantic interface -/

/-- Successful concrete execution of analyzed code is covered when the owner
is exact or self-analysis is forced to fail closed. -/
theorem analyzeCode_sound_ownerCompatible
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef} {store outputStore : Store}
    {facts : List Fact} {values : List RVal} {code : Code}
    {outputValue : RVal} {inferred : Fact} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (howner : AnalysisOwnerCompatible declarations summaries owner current)
    (henvironment : EnvironmentHolds declarations store facts values)
    (habstract : analyzeCode declarations summaries owner current facts code =
      .ok inferred)
    (hconcrete : runCode ctx fuel current store values code =
      .ok (outputStore, outputValue)) :
    inferred.Holds declarations outputStore outputValue :=
  (soundAt hpost fuel).1 ctx owner current store facts values code outputStore
    outputValue inferred hctx howner henvironment habstract hconcrete

/-- Exact stored-owner specialization of
`analyzeCode_sound_ownerCompatible`. -/
theorem analyzeCode_sound {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef} {store outputStore : Store}
    {facts : List Fact} {values : List RVal} {code : Code}
    {outputValue : RVal} {inferred : Fact} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (henvironment : EnvironmentHolds declarations store facts values)
    (habstract : analyzeCode declarations summaries owner current facts code =
      .ok inferred)
    (hconcrete : runCode ctx fuel current store values code =
      .ok (outputStore, outputValue)) :
    inferred.Holds declarations outputStore outputValue :=
  analyzeCode_sound_ownerCompatible hpost hctx (.inl hcurrent) henvironment
    habstract hconcrete

/-- Operation-level form of `analyzeCode_sound_ownerCompatible`. -/
theorem analyzeOp_sound_ownerCompatible
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef} {store outputStore : Store}
    {facts : List Fact} {values : List RVal} {operation : Op}
    {outputValue : RVal} {inferred : Fact} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (howner : AnalysisOwnerCompatible declarations summaries owner current)
    (henvironment : EnvironmentHolds declarations store facts values)
    (habstract : analyzeOp declarations summaries owner current facts operation =
      .ok inferred)
    (hconcrete : runOp ctx fuel current store values operation =
      .ok (outputStore, outputValue)) :
    inferred.Holds declarations outputStore outputValue :=
  (soundAt hpost fuel).2.1 ctx owner current store facts values operation
    outputStore outputValue inferred hctx howner henvironment habstract
    hconcrete

/-- Exact stored-owner specialization used by ordinary HPT consumers. -/
theorem analyzeOp_sound {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef} {store outputStore : Store}
    {facts : List Fact} {values : List RVal} {operation : Op}
    {outputValue : RVal} {inferred : Fact} {fuel : Nat}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current))
    (henvironment : EnvironmentHolds declarations store facts values)
    (habstract : analyzeOp declarations summaries owner current facts operation =
      .ok inferred)
    (hconcrete : runOp ctx fuel current store values operation =
      .ok (outputStore, outputValue)) :
    inferred.Holds declarations outputStore outputValue :=
  analyzeOp_sound_ownerCompatible hpost hctx (.inl hcurrent) henvironment
    habstract hconcrete

/-- Known invocation respects `callableResult` under a local post-fixpoint. -/
theorem invoke_sound {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {address : Address} {arguments : List RVal}
    {store outputStore : Store} {outputValue : RVal} {fact : Fact}
    {fuel : Nat} (hctx : ctx.decls = declarations)
    (habstract : callableResult declarations summaries address = .ok fact)
    (hconcrete : invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    fact.Holds declarations outputStore outputValue :=
  (soundAt hpost fuel).2.2.1 ctx address arguments store outputStore
    outputValue fact hctx habstract hconcrete

private theorem lookup_build_some_mem {α : Type}
    {entries : List (Address × α)} {address : Address} {value : α}
    (hlookup : AddressEnv.lookup (AddressEnv.build entries) address =
      some value) : (address, value) ∈ entries := by
  rw [AddressEnv.lookup_build_apply] at hlookup
  obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryValue⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Address × α => entry.1 == address) hfind
  have haddress : entryAddress = address := Address.eq_of_beq hbeq
  have hentryValue : entryValue = value := by simpa using hvalue
  subst entryAddress
  subst entryValue
  exact List.mem_of_find?_eq_some hfind

private theorem checked_of_checkLocalRows
    {declarations : DeclEnv} {summaries : SummaryEnv}
    {entries : List (Address × Decl)} {address : Address}
    {declaration : Decl} {claimed : Fact}
    (hrows : checkLocalRows declarations summaries entries = true)
    (hmember : (address, declaration) ∈ entries)
    (hsummary : summaries address = some claimed) :
    checkMember declarations summaries (address, declaration)
      (address, claimed) = true := by
  induction entries with
  | nil => contradiction
  | cons entry entries ih =>
      rcases entry with ⟨entryAddress, entryDeclaration⟩
      simp only [checkLocalRows, Bool.and_eq_true] at hrows
      rcases List.mem_cons.mp hmember with hsame | hmember
      · injection hsame with haddress hdeclaration
        subst entryAddress
        subst entryDeclaration
        simpa [hsummary] using hrows.1
      · exact ih hrows.2 hmember

/-- The executable whole-program condition implies the propositional local
post-fixpoint used by the evaluator proof. -/
theorem localPostFixpoint_of_postFixpoint
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    (hcertificate : certificate.postFixpoint program = true) :
    LocalPostFixpoint (programDeclEnv program) certificate.summaryEnv := by
  intro address function claimed hdeclaration hsummary
  have hrows : checkLocalRows (programDeclEnv program) certificate.summaryEnv
      (declarationEntries program) = true := by
    unfold Certificate.postFixpoint at hcertificate
    simp only [Bool.and_eq_true] at hcertificate
    exact hcertificate.1.2
  have hmember : (address, Decl.fn function) ∈ declarationEntries program := by
    apply lookup_build_some_mem
    simpa [programDeclEnv] using hdeclaration
  have hchecked := checked_of_checkLocalRows hrows hmember hsummary
  cases hinferred : inferFunction (programDeclEnv program)
      certificate.summaryEnv address function with
  | error error =>
      simp [checkMember, hinferred] at hchecked
  | ok inferred =>
      refine ⟨inferred, rfl, ?_⟩
      have hparts : claimed.canonical = true ∧ inferred.le claimed = true := by
        simpa [checkMember, hinferred] using hchecked
      exact hparts.2

/-- A function row in any accepted certificate covers every successful
runtime invocation, for arbitrary arguments and fuel. -/
theorem functionSummary_sound_of_postFixpoint
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {ctx : Ctx} {address : Address} {function : FnDef} {claimed : Fact}
    {arguments : List RVal} {store outputStore : Store}
    {outputValue : RVal} {fuel : Nat}
    (hcertificate : certificate.postFixpoint program = true)
    (hctx : ctx.decls = programDeclEnv program)
    (hdeclaration : programDeclEnv program address = some (.fn function))
    (hsummary : certificate.summaryEnv address = some claimed)
    (hinvoke : invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds (programDeclEnv program) outputStore outputValue := by
  apply invoke_sound (localPostFixpoint_of_postFixpoint hcertificate) hctx
    (hconcrete := hinvoke)
  simp [callableResult, hdeclaration, hsummary]

/-- Configurable checker success supplies the semantic certificate premise. -/
theorem functionSummary_sound_of_runWith_eq_ok
    {limits : Limits} {program : List ReaddressAll.Artifact}
    {certificate : Certificate} {result : Result}
    {ctx : Ctx} {address : Address} {function : FnDef} {claimed : Fact}
    {arguments : List RVal} {store outputStore : Store}
    {outputValue : RVal} {fuel : Nat}
    (hcheck : runWith limits program certificate = .ok result)
    (hctx : ctx.decls = programDeclEnv program)
    (hdeclaration : programDeclEnv program address = some (.fn function))
    (hsummary : certificate.summaryEnv address = some claimed)
    (hinvoke : invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds (programDeclEnv program) outputStore outputValue := by
  exact functionSummary_sound_of_postFixpoint
    (postFixpoint_of_runWith_eq_ok hcheck) hctx hdeclaration hsummary hinvoke

/-- Default-limit specialization of
`functionSummary_sound_of_runWith_eq_ok`. -/
theorem functionSummary_sound_of_run_eq_ok
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {result : Result} {ctx : Ctx} {address : Address} {function : FnDef}
    {claimed : Fact} {arguments : List RVal} {store outputStore : Store}
    {outputValue : RVal} {fuel : Nat}
    (hcheck : run program certificate = .ok result)
    (hctx : ctx.decls = programDeclEnv program)
    (hdeclaration : programDeclEnv program address = some (.fn function))
    (hsummary : certificate.summaryEnv address = some claimed)
    (hinvoke : invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds (programDeclEnv program) outputStore outputValue := by
  exact functionSummary_sound_of_runWith_eq_ok
    (limits := defaultLimits) (by simpa [run] using hcheck) hctx hdeclaration
    hsummary hinvoke

end Ix.Compiler.IxIR1.HPT
