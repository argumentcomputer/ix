import Compilatrix.Cfg.Rc.Proof.Native.Activation
import Compilatrix.Rt.Proof.Lang

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs Compilatrix.Own.Rc

theorem numeric_refs (location : Nat) (numbers : List Nat) :
    refsIn location (Own.litArgs numbers) = 0 := by
  induction numbers with
  | nil => rfl
  | cons number numbers ih => simpa [Own.litArgs, refsIn] using ih

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







end Compilatrix.Cfg.Rc.Native.Spec
