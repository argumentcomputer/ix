import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorInvariant
import IxCC.Rt.Proof.Switches

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Lir (Word)

/-- Actual accepted switch tests agree with source keys using only constructor
compatibility. There is no immortal heap or blanket unique-key premise. -/
theorem compatible_dispatches {T : Tables} {H : Own.Heap}
    {v : Own.RVal} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge}
    {key : Key.CtorKey} {fs : List Own.RVal} {e : Cfg.Edge}
    (hpins : pinsApart T.known = true) (hok : switchOk T alts d = true) (hv : ValueCtorOk T v)
    (hheap : HeapCtorOk T H) (hac : v.asCtor T.known H = some (key, fs))
    (hsel : Cfg.selectEdge key alts d = some e) : Dispatches T H v alts := by
  simp only [switchOk, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true, List.all_eq_true,
    Bool.not_eq_true'] at hok
  obtain ⟨⟨rfl, hmix⟩, hdist⟩ := hok
  obtain ⟨q, hq, hqk⟩ := selectEdge_key hsel
  have hpins' : ∀ k, T.known.natZero = some k → T.known.natSucc ≠ some k := by
    intro k h0 h1
    simp [pinsApart, h0, h1] at hpins
  -- the key's kind and the scrutinee's shape
  have hcases : (∃ n, v = .lit (.nat n) ∧ natAlt T key = true ∧
        (∀ k', keyKind T k' = some .zero → v = .lit (.nat 0) → k' = key) ∧
        (∀ k', keyKind T k' = some .succ → (∃ n', v = .lit (.nat (n' + 1))) → k' = key) ∧
        Accepts T H key v) ∨
      (natAlt T key = false ∧ altTest T key = valTest H v ∧ Accepts T H key v ∧ (∀ n, v ≠ .lit (.nat n))) := by
    cases v with
    | lit l =>
      cases l with
      | str _ => simp [Own.RVal.asCtor] at hac
      | nat n =>
        cases n with
        | zero =>
          simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
          obtain ⟨k, hk, rfl, -⟩ := hac
          refine .inl ⟨0, rfl, natAlt_of_zero hk, fun k' h' _ => ?_, fun k' _ ⟨n', hn'⟩ => ?_, ?_⟩
          · rw [keyKind_zero] at h'; rw [hk] at h'; cases h'; rfl
          · cases hn'
          · simp [Accepts, keyKind_of_zero hk]
        | succ n =>
          simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
          obtain ⟨k, hk, rfl, -⟩ := hac
          have h0 : T.known.natZero ≠ some k := fun h0 => hpins' k h0 hk
          refine .inl ⟨n + 1, rfl, natAlt_of_succ h0 hk, fun k' _ h => ?_, fun k' h' _ => ?_, ?_⟩
          · cases h
          · rw [(keyKind_succ h').2] at hk; cases hk; rfl
          · simp [Accepts, keyKind_succ_of h0 hk]
    | ctor0 c =>
      simp only [Own.RVal.asCtor, Option.some.injEq, Prod.mk.injEq] at hac
      obtain ⟨rfl, -⟩ := hac
      obtain ⟨hc, hf⟩ := hv
      have hk := keyKind_ctor0 hc hf
      refine .inr ⟨natAlt_ctorOk hc, altTest_imm hk, ?_, fun n h => nomatch h⟩
      simp [Accepts, hk, valWord]
    | erased => simp [Own.RVal.asCtor] at hac
    | loc ℓ =>
      simp only [Own.RVal.asCtor, Own.Heap.cell?] at hac
      split at hac
      · rename_i rc mode b hcell
        simp only [Option.some.injEq, Prod.mk.injEq] at hac
        obtain ⟨rfl, -⟩ := hac
        obtain ⟨hc, hf, _⟩ := hheap ℓ rc mode b hcell
        have hk := keyKind_cellOk hc hf
        refine .inr ⟨natAlt_ctorOk hc, ?_, ?_, fun n h => nomatch h⟩
        · rw [altTest_cell hk]; simp [valTest, hcell]
        · simp only [Accepts, hk]
          exact ⟨ℓ, rc, mode, b, rfl, hcell, rfl⟩
      · cases hac
  refine ⟨fun p hp hnat => ?_, fun p hp c fs' hac' => ?_⟩
  · -- a `Nat` key: the scrutinee is a literal
    have hpn : natAlt T p.1 = true := natAlt_iff.2 hnat
    rcases hcases with ⟨n, rfl, -⟩ | ⟨hkn, -⟩
    · exact ⟨n, rfl⟩
    · rcases hmix with hall | hall
      · rw [← hqk, hall q hq] at hkn; cases hkn
      · rw [hall p hp] at hpn; cases hpn
  · rw [hac] at hac'
    simp only [Option.some.injEq, Prod.mk.injEq] at hac'
    obtain ⟨rfl, -⟩ := hac'
    constructor
    · intro hacc
      rcases hcases with ⟨n, rfl, hkn, hz, hs, -⟩ | ⟨hkn, hkt, -, hnl⟩
      · -- a literal: only `Nat` tests accept it, and they name its key
        unfold Accepts at hacc
        split at hacc
        · rename_i hk; exact hz _ hk hacc
        · rename_i hk; exact hs _ hk hacc
        · rename_i w' hk
          exfalso
          rcases hmix with hall | hall
          · have := hall p hp
            simp [natAlt, hk] at this
          · have := hall q hq
            rw [hqk, hkn] at this
            cases this
        · rename_i t hk
          obtain ⟨_, _, _, _, h, -⟩ := hacc
          cases h
        · exact hacc.elim
      · -- a constructor: its test is the key's, and tests are distinct
        unfold Accepts at hacc
        split at hacc
        · rename_i hk; exact absurd hacc (hnl 0)
        · rename_i hk; obtain ⟨n', h⟩ := hacc; exact absurd h (hnl _)
        · rename_i w' hk
          have ht : altTest T p.1 = altTest T q.1 := by
            rw [altTest_imm hk, hqk, hkt]
            cases v with
            | ctor0 c =>
              simp only [valWord, Option.some.injEq] at hacc
              rw [← hacc]; rfl
            | lit l =>
              cases l with
              | nat n => exact absurd rfl (hnl n)
              | str _ => simp [valWord] at hacc
            | erased => simp [Own.RVal.asCtor] at hac
            | loc ℓ => simp [valWord] at hacc
          exact (testsDistinct_eq hdist hp hq ht).trans hqk
        · rename_i t hk
          obtain ⟨ℓ, rc, mode, b, rfl, hcell, htag⟩ := hacc
          have ht : altTest T p.1 = altTest T q.1 := by
            rw [altTest_cell hk, hqk, hkt]
            simp [valTest, hcell, htag]
          exact (testsDistinct_eq hdist hp hq ht).trans hqk
        · exact hacc.elim
    · intro hpk
      rw [hpk]
      rcases hcases with ⟨-, -, -, -, -, h⟩ | ⟨-, -, h, -⟩ <;> exact h



end IxCC.Cfg.Rc.Proof.Physical.Bridge
