import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Rt.Proof.Lang

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own.Rc

theorem numeric_refs (location : Nat) (numbers : List Nat) :
    refsIn location (Own.litArgs numbers) = 0 := by
  induction numbers with
  | nil => rfl
  | cons number numbers ih => simpa [Own.litArgs, refsIn] using ih

theorem numeric_selectOwned_refs (location : Nat) :
    ∀ (bs : List Bool) (numbers : List Nat),
      refsIn location (Own.Plain.selectOwnedVals bs (Own.litArgs numbers)) = 0
  | [], numbers => by rw [Own.Plain.selectOwnedVals_nil_left]; exact numeric_refs location numbers
  | _ :: _, [] => rfl
  | false :: bs, _ :: numbers => by
    simpa [Own.Plain.selectOwnedVals, Own.litArgs, refsIn] using
      numeric_selectOwned_refs location bs numbers
  | true :: bs, _ :: numbers => by
    simpa [Own.Plain.selectOwnedVals, Own.litArgs] using
      numeric_selectOwned_refs location bs numbers

theorem numeric_selectOwned_balance {H : Own.Heap} {external : Nat → Nat} (bs : List Bool)
    (numbers : List Nat) (h : Balance H external (Own.litArgs numbers)) :
    Balance H external (Own.Plain.selectOwnedVals bs (Own.litArgs numbers)) := by
  intro location
  have hl := h location
  simpa only [Balance, total, numeric_refs, numeric_selectOwned_refs] using hl

theorem numeric_selectBorrowed_reachable (H : Own.Heap) (external : Nat → Nat) :
    ∀ (bs : List Bool) (numbers : List Nat) (v : Own.RVal),
      v ∈ Own.Plain.selectBorrowedVals bs (Own.litArgs numbers) →
      Own.Plain.ReachableFrom H external v
  | [], [], _, hv => by simp [Own.Plain.selectBorrowedVals, Own.litArgs] at hv
  | [], _ :: _, _, hv => by simp [Own.Plain.selectBorrowedVals, Own.litArgs] at hv
  | _ :: _, [], _, hv => by simp [Own.Plain.selectBorrowedVals, Own.litArgs] at hv
  | false :: bs, _ :: numbers, v, hv =>
    numeric_selectBorrowed_reachable H external bs numbers v
      (by simpa [Own.Plain.selectBorrowedVals, Own.litArgs] using hv)
  | true :: bs, _ :: numbers, v, hv => by
    simp only [Own.Plain.selectBorrowedVals, Own.litArgs, List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact .imm (fun _ h => by cases h)
    · exact numeric_selectBorrowed_reachable H external bs numbers v hv

private theorem mem_selectUniqueVals {bs us : List Bool} {vs : List Own.RVal} {v : Own.RVal}
    (hv : v ∈ Own.Plain.selectUniqueVals bs us vs) : v ∈ vs := by
  induction vs generalizing bs us with
  | nil => simp [Own.Plain.selectUniqueVals] at hv
  | cons x xs ih =>
    cases bs with
    | nil =>
      cases us with
      | nil => simp [Own.Plain.selectUniqueVals] at hv
      | cons u us =>
        cases u
        · exact List.mem_cons_of_mem _ (ih (by simpa [Own.Plain.selectUniqueVals] using hv))
        · simp only [Own.Plain.selectUniqueVals, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hv)
    | cons b bs =>
      cases b
      · cases us with
        | nil => exact List.mem_cons_of_mem _ (ih (by simpa [Own.Plain.selectUniqueVals] using hv))
        | cons u us =>
          cases u
          · exact List.mem_cons_of_mem _ (ih (by simpa [Own.Plain.selectUniqueVals] using hv))
          · simp only [Own.Plain.selectUniqueVals, List.mem_cons] at hv
            rcases hv with rfl | hv
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih hv)
      · cases us with
        | nil => exact List.mem_cons_of_mem _ (ih (by simpa [Own.Plain.selectUniqueVals] using hv))
        | cons _ us => exact List.mem_cons_of_mem _ (ih (by simpa [Own.Plain.selectUniqueVals] using hv))

theorem numeric_selectUnique_uniq (ctors : List Lam.CtorInfo) (H : Own.Heap) (external : Nat → Nat)
    (owned : List Own.RVal) (bs us : List Bool) (numbers : List Nat) (v : Own.RVal)
    (hv : v ∈ Own.Plain.selectUniqueVals bs us (Own.litArgs numbers)) :
    Own.Plain.UniqVal ctors H external owned v := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp (mem_selectUniqueVals hv)
  trivial

theorem HeapState.numeric_selectOwned {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {H : Own.Heap} {addresses : AddressMap} {memory : X86.Memory} {external : Nat → Nat}
    {context base bump limit : Lir.Word} {regionBytes : Nat} {slots : List Slot}
    {lists : Nat → List Lir.Word} (bs : List Bool) (numbers : List Nat)
    (before : HeapState P pairs H addresses memory external (Own.litArgs numbers)
      context base bump limit regionBytes slots lists) :
    HeapState P pairs H addresses memory external
      (Own.Plain.selectOwnedVals bs (Own.litArgs numbers))
      context base bump limit regionBytes slots lists := by
  have roots : holdRoots external (Own.Plain.selectOwnedVals bs (Own.litArgs numbers)) =
      holdRoots external (Own.litArgs numbers) := by
    funext location
    simp [holdRoots, numeric_refs, numeric_selectOwned_refs]
  refine ⟨?_, before.ordered, before.compatible, before.extent⟩
  rw [roots]
  exact before.ready

theorem numeric_balance (numbers : List Nat) : Balance {} (fun _ => 0) (Own.litArgs numbers) := by
  intro location
  simp [dynCount, Own.Heap.cell?, edgeCount, total, numeric_refs]

theorem numeric_words {addresses : AddressMap} :
    ∀ {numbers : List Nat} {words : List Lir.Word}, Rt.natWords numbers = some words →
      Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) (Own.litArgs numbers) words
  | [], words, encoded => by
    simp only [Rt.natWords, List.mapM_nil, pure, Option.some.injEq] at encoded
    subst words
    exact .nil
  | number :: numbers, words, encoded => by
    simp only [Rt.natWords, List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at encoded
    obtain ⟨word, encodedHead, rest, encodedTail, rfl⟩ := encoded
    exact .cons encodedHead (numeric_words encodedTail)

theorem numeric_compatible (tables : Rt.Lower.Tables) (numbers : List Nat) :
    ∀ value ∈ Own.litArgs numbers, ValueCtorOk tables value := by
  intro value member
  obtain ⟨number, _, rfl⟩ := List.mem_map.mp member
  trivial

/-- Immediate driver arguments change no ownership count. The initializer's
actual physical state therefore already satisfies the argument-rooted heap
invariant; no cell, capacity or representation premise is manufactured. -/
theorem HeapState.numeric_roots {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {addresses : AddressMap} {memory : X86.Memory} {context base bump limit : Lir.Word}
    {regionBytes : Nat} {slots : List Slot} {lists : Nat → List Lir.Word}
    (before : HeapState P pairs {} addresses memory (fun _ => 0) []
      context base bump limit regionBytes slots lists) (numbers : List Nat) :
    HeapState P pairs {} addresses memory (fun _ => 0) (Own.litArgs numbers)
      context base bump limit regionBytes slots lists := by
  have roots : holdRoots (fun _ => 0) (Own.litArgs numbers) = holdRoots (fun _ => 0) [] := by
    funext location
    simp [holdRoots, numeric_refs, refsIn]
  refine ⟨?_, before.ordered, before.compatible, before.extent⟩
  rw [roots]
  exact before.ready

theorem numeric_inputs {P : Program} (pairs : List (Nat × Cfg.Fun))
    {numbers : List Nat} {words : List Lir.Word} (encoded : Rt.natWords numbers = some words) :
    Sem.Forall2 (Own.Proof.Den {}) (Own.litArgs numbers) (Fir.litArgs numbers) ∧
      Balance {} (fun _ => 0) (Own.litArgs numbers) ∧
      Rt.Proof.ListRel (fun value word => valueWord (fun _ => none) value = some word)
        (Own.litArgs numbers) words ∧
      (∀ value ∈ Own.litArgs numbers, ValueCtorOk (tablesOf P pairs) value) :=
  ⟨Own.dens_lits {} numbers, numeric_balance numbers, numeric_words encoded,
    numeric_compatible _ numbers⟩







end IxCC.Cfg.Rc.Native.Spec
