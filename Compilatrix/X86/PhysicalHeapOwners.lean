import Compilatrix.X86.PhysicalHeapTransferCode

namespace Compilatrix.X86.PhysicalHeap

def Scope.owners (scope : Scope) : Nat :=
  scope.values.countP (· == some .node) + scope.credits.countP Option.isSome

def kindOwners (kinds : List Kind) : Nat := (kinds.map Kind.owners).sum

def Primitive.frees : Primitive → Nat | .release .. | .discard .. => 1 | _ => 0

def Primitive.counterDelta (operation : Primitive) (field : Nat) : Nat :=
  match operation with
  | .alloc .. => if field = 2 then 1 else 0
  | .release world _ => if field = 3 ∨ (world = .shared ∧ field = 5) then 1 else 0
  | .discard .. => if field = 3 then 1 else 0
  | .reserve world .. => if world = .shared ∧ (field = 6 ∨ field = 7) then 1 else 0
  | .reuse _ ctor .. => if field = 4 then 1 else if field = 8 then ctor.schema.fields.size else 0
  | _ => 0

@[simp] theorem Primitive.counterDelta_allocations (operation : Primitive) : operation.counterDelta 2 = operation.allocations := by
  cases operation <;> simp [counterDelta, allocations]

@[simp] theorem Primitive.counterDelta_frees (operation : Primitive) : operation.counterDelta 3 = operation.frees := by
  cases operation <;> simp [counterDelta, frees]

theorem Scope.clearValue_owners {scope : Scope} {index : Nat}
    (found : scope.values[index]? = some (some .node)) :
    { scope with values := scope.values.setIfInBounds index none }.owners + 1 = scope.owners := by
  obtain ⟨bound, atIndex⟩ := Array.getElem?_eq_some_iff.mp found
  have positive := Array.boole_getElem_le_countP (p := (· == some Kind.node)) bound
  simp only [atIndex, beq_self_eq_true, ↓reduceIte] at positive
  simp only [Scope.owners, Array.setIfInBounds_def, bound, ↓reduceDIte, Array.countP_set, atIndex,
    beq_self_eq_true, ↓reduceIte, show (none == some Kind.node) = false from rfl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  omega

theorem Scope.clearCredit_owners {scope : Scope} {index : Nat} {id : IxIR2.LayoutId}
    (found : scope.credits[index]? = some (some id)) :
    { scope with credits := scope.credits.setIfInBounds index none }.owners + 1 = scope.owners := by
  obtain ⟨bound, atIndex⟩ := Array.getElem?_eq_some_iff.mp found
  have positive := Array.boole_getElem_le_countP (p := Option.isSome) bound
  simp only [atIndex, Option.isSome_some, ↓reduceIte] at positive
  simp only [Scope.owners, Array.setIfInBounds_def, bound, ↓reduceDIte, Array.countP_set, atIndex,
    Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  omega

theorem Scope.peek_node {scope : Scope} {source : IxIR2.Atom} {operand : Scalar.Atom}
    (peeked : scope.peek source = .ok (.node, operand)) :
    ∃ index, source = .reg index ∧ scope.values[index]? = some (some .node) ∧ operand = .var index := by
  cases source with
  | reg index =>
      simp only [Scope.peek] at peeked
      split at peeked
      · rename_i kind found
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at peeked
        rcases peeked with ⟨rfl, rfl⟩
        exact ⟨index, rfl, found, rfl⟩
      · contradiction
  | erased => simp [Scope.peek] at peeked
  | lit literal =>
      cases literal with
      | nat number =>
          simp only [Scope.peek] at peeked
          split at peeked <;> simp_all [pure, Except.pure]
      | _ => contradiction

theorem Scope.take_owners {scope next : Scope} {source : IxIR2.Atom} {kind : Kind} {operand : Scalar.Atom}
    (taken : scope.take source = .ok (kind, operand, next)) : next.owners + kind.owners = scope.owners := by
  unfold Scope.take at taken
  cases peeked : scope.peek source with
  | error error => simp [peeked, bind, Except.bind] at taken
  | ok output =>
      rcases output with ⟨actual, value⟩
      cases actual with
      | scalar =>
          simp only [peeked, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at taken
          rcases taken with ⟨rfl, rfl, rfl⟩
          rfl
      | erased =>
          simp only [peeked, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at taken
          rcases taken with ⟨rfl, rfl, rfl⟩
          rfl
      | node =>
          obtain ⟨index, rfl, found, rfl⟩ := Scope.peek_node peeked
          simp only [peeked, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at taken
          rcases taken with ⟨rfl, rfl, rfl⟩
          exact Scope.clearValue_owners found

theorem Scope.takeCredit_owners {scope next : Scope} {index : Nat} {id : IxIR2.LayoutId}
    (taken : scope.takeCredit index = .ok (id, next)) : next.owners + 1 = scope.owners := by
  unfold Scope.takeCredit at taken
  split at taken
  · rename_i actual found
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at taken
    rcases taken with ⟨rfl, rfl⟩
    exact Scope.clearCredit_owners found
  · contradiction

theorem Scope.pushValue_owners {scope next : Scope} {kind : Kind}
    (pushed : scope.pushValue kind = .ok next) : next.owners = scope.owners + kind.owners := by
  unfold Scope.pushValue at pushed
  split at pushed
  · cases pushed
    cases kind <;> simp [Scope.owners, Kind.owners, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · contradiction

theorem Scope.pushFields_owners {scope next : Scope} {count : Nat}
    (pushed : scope.pushFields count = .ok next) : next.owners = scope.owners := by
  unfold Scope.pushFields at pushed
  split at pushed
  · cases pushed
    simp [Scope.owners]
  · contradiction

theorem Scope.pushCredit_owners {scope next : Scope} {id : IxIR2.LayoutId}
    (pushed : scope.pushCredit id = .ok next) : next.owners = scope.owners + 1 := by
  unfold Scope.pushCredit at pushed
  split at pushed
  · cases pushed
    simp [Scope.owners, Nat.add_assoc]
  · contradiction

theorem Scope.finished_owners {scope : Scope} (finished : scope.finished = true) : scope.owners = 0 := by
  simp only [Scope.finished, Bool.and_eq_true] at finished
  have noValues : scope.values.countP (· == some .node) = 0 := by
    apply Array.countP_eq_zero.mpr
    intro value member
    have absent := Array.all_eq_true_iff_forall_mem.mp finished.1 value member
    simpa only [bne_iff_ne, beq_iff_eq] using absent
  have noCredits : scope.credits.countP Option.isSome = 0 := by
    apply Array.countP_eq_zero.mpr
    intro credit member
    have absent := Array.all_eq_true_iff_forall_mem.mp finished.2 credit member
    cases credit <;> simp_all
  simp only [Scope.owners, noValues, noCredits, Nat.add_zero]

theorem PrimitiveCode.owners {schemas constructors scope instruction operation next}
    (code : PrimitiveCode schemas constructors scope instruction operation next) :
    next.owners + operation.frees = scope.owners + operation.allocations := by
  cases code with
  | move taken pushed => have := Scope.take_owners taken; have := Scope.pushValue_owners pushed; simp only [Primitive.frees, Primitive.allocations]; omega
  | @retain source kind operand _ peeked scalar pushed =>
      have := Scope.pushValue_owners pushed
      have zero : kind.owners = 0 := by cases kind <;> simp_all [Kind.owners]
      simp only [Primitive.frees, Primitive.allocations]; omega
  | release taken | drop taken =>
      have own := Scope.take_owners taken
      cases ‹Kind› <;> simpa [Primitive.frees, Primitive.allocations, Kind.owners] using own
  | alloc selected arity fields pushed => simpa [Primitive.frees, Primitive.allocations, Kind.owners] using Scope.pushValue_owners pushed
  | reuse selected arity fields taken pushed =>
      have := Scope.takeCredit_owners taken; have := Scope.pushValue_owners pushed
      simp only [Kind.owners] at *; simp only [Primitive.frees, Primitive.allocations]; omega
  | takeUnique selected taken fields credit | resetShared selected taken fields credit =>
      have := Scope.take_owners taken; have := Scope.pushFields_owners fields; have := Scope.pushCredit_owners credit
      simp only [Kind.owners] at *; simp only [Primitive.frees, Primitive.allocations]; omega
  | discard taken => simpa [Primitive.frees, Primitive.allocations] using Scope.takeCredit_owners taken
  | free selected taken => simpa [Primitive.frees, Primitive.allocations, Kind.owners] using Scope.take_owners taken
  | fetch peeked small pushed => simpa [Primitive.frees, Primitive.allocations, Kind.owners] using Scope.pushValue_owners pushed

theorem TakeValues.owners {scope sources kinds operands next}
    (taken : TakeValues scope sources kinds operands next) : next.owners + kindOwners kinds = scope.owners := by
  induction taken with
  | nil => rfl
  | cons head tail ih =>
      have := Scope.take_owners head
      simp only [kindOwners, List.map_cons, List.sum_cons] at *
      omega

theorem TakeCredits.owners {scope sources layouts next}
    (taken : TakeCredits scope sources layouts next) : next.owners + layouts.length = scope.owners := by
  induction taken with
  | nil => rfl
  | cons head tail ih =>
      have := Scope.takeCredit_owners head
      simp only [List.length_cons]
      omega

theorem scopeOfLists_owners (kinds : List Kind) (ids : List IxIR2.LayoutId) :
    (Scope.mk (kinds.map some).toArray (ids.map some).toArray).owners = kindOwners kinds + ids.length := by
  have values : (kinds.map some).countP (· == some .node) = kindOwners kinds := by
    induction kinds with
    | nil => rfl
    | cons kind kinds ih => cases kind <;> simp [kindOwners, Kind.owners] at ih ⊢ <;> omega
  simp [Scope.owners, values, List.countP_map, Function.comp_def]

theorem Scope.initial_owners (kinds : Array Kind) : (Scope.initial kinds).owners = kindOwners kinds.toList := by
  simpa [Scope.initial, ← List.map_toArray] using scopeOfLists_owners kinds.toList []

theorem TransferCode.owners {definition scope edge implicitValue transfer}
    (selected : TransferCode definition scope edge implicitValue transfer) : transfer.scope.owners = scope.owners := by
  cases selected with
  | mk targetAt values credits finished bounded =>
      have valuesCount := values.owners
      have creditCount := credits.owners
      have zero := Scope.finished_owners finished
      simp only [edgeTransfer, scopeOfLists_owners]
      cases implicitValue <;> simp only [implicitKinds, List.nil_append, List.cons_append, kindOwners, List.map_cons,
        Kind.owners, List.sum_cons, Nat.zero_add] at * <;> omega

def Balance (store : IxIR2.Eval.Store) (owners outside : Nat) : Prop := store.heap.allocs = store.heap.frees + owners + outside

end Compilatrix.X86.PhysicalHeap
