import IxCC.Rt.Proof.Diagram
import IxCC.Rt.Switches

/-!
# The pipeline's switch check gives `SwitchSel` everywhere

`Rt.lower_correct` needs, at each switch Cfg steps on, that the lowering's
word and tag tests dispatch the scrutinee as Cfg's key selection does
(`Dispatches`). Cfg carries no types, so this is not a consequence of the
simulation. The pipeline discharges it with a check rather than a typing invariant
(`Rt.switchesOk`): no default arm, `Nat` keys not mixed with
others, distinct keys with distinct tests, `Nat.zero` and `Nat.succ` apart.

`dispatches_of_ok`: under the check, a scrutinee related to a word under the
heap invariant (so a constructor as the table has it, outside `Nat`'s keys)
whose key selects an alternative is dispatched: its key is among the
alternatives, which its own test accepts, and every other alternative's
test, being distinct, rejects it. `switchSel_of_ok` lifts it to every Cfg
state, reachable or not.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower

/-! ## Key kinds of the values the relation allows -/

theorem keyKind_of_zero {T : Tables} {k : Key.CtorKey} (h : T.known.natZero = some k) :
    keyKind T k = some .zero := keyKind_zero.2 h

/-- A constructor as the table has it, outside `Nat`'s keys: its kind is
its word (field-less) or its tag (a cell). -/
theorem keyKind_ctorOk {T : Tables} {c : Fir.CtorInfo} (hc : CtorOk T c) :
    keyKind T c.key = some (if c.fieldless then .imm (ctor0Word c.tag) else .cell c.tag) := by
  have hn := hc.notNat
  simp only [isNatKey, Bool.or_eq_false_iff] at hn
  unfold keyKind
  simp only [hn.1, hn.2, Bool.false_eq_true, ↓reduceIte, hc.table, Option.map_some]

theorem keyKind_ctor0 {T : Tables} {c : Fir.CtorInfo} (hc : CtorOk T c) (hf : c.fieldless = true) :
    keyKind T c.key = some (.imm (ctor0Word c.tag)) := by
  rw [keyKind_ctorOk hc, hf]; rfl

theorem keyKind_cellOk {T : Tables} {c : Fir.CtorInfo} (hc : CtorOk T c) (hf : c.fieldless = false) :
    keyKind T c.key = some (.cell c.tag) := by
  rw [keyKind_ctorOk hc, hf]; rfl

theorem ctorOk_notNat {T : Tables} {c : Fir.CtorInfo} (hc : CtorOk T c) :
    T.known.natZero ≠ some c.key ∧ T.known.natSucc ≠ some c.key := by
  have hn := hc.notNat
  simp only [isNatKey, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hn
  exact hn

/-! ## The check's parts -/

theorem natAlt_iff {T : Tables} {k : Key.CtorKey} :
    natAlt T k = true ↔ (keyKind T k).map KeyKind.isNat = some true := by
  unfold natAlt
  split <;> rename_i h <;> simp [h, KeyKind.isNat]
  rename_i hz hs
  cases hk : keyKind T k with
  | none => simp
  | some kind => cases kind <;> simp_all [KeyKind.isNat]

theorem natAlt_of_zero {T : Tables} {k : Key.CtorKey} (h : T.known.natZero = some k) : natAlt T k = true := by
  simp [natAlt, keyKind_of_zero h]

theorem natAlt_of_succ {T : Tables} {k : Key.CtorKey} (h0 : T.known.natZero ≠ some k)
    (h1 : T.known.natSucc = some k) : natAlt T k = true := by
  simp [natAlt, keyKind_succ_of h0 h1]

theorem natAlt_ctorOk {T : Tables} {c : Fir.CtorInfo} (hc : CtorOk T c) : natAlt T c.key = false := by
  unfold natAlt
  rw [keyKind_ctorOk hc]
  cases c.fieldless <;> rfl

/-- The test a constructor value answers to: a field-less constructor's
word, a live cell's tag. -/
def valTest (H : Own.Heap) : Own.RVal → Option (Nat × Word)
  | .ctor0 c => some (2, ctor0Word c.tag)
  | .loc ℓ =>
    match H.cells[ℓ]? with
    | some (.live _ _ b) => some (3, UInt64.ofNat b.ctor.tag)
    | _ => none
  | _ => none

theorem testsDistinct_eq {T : Tables} :
    ∀ {alts : List (Key.CtorKey × Cfg.Edge)}, testsDistinct T alts = true →
      ∀ {p q : Key.CtorKey × Cfg.Edge}, p ∈ alts → q ∈ alts → altTest T p.1 = altTest T q.1 → p.1 = q.1
  | [], _, _, _, hp, _, _ => nomatch hp
  | a :: rest, h, p, q, hp, hq, he => by
    simp only [testsDistinct, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
      bne_iff_ne, ne_eq] at h
    obtain ⟨ha, hr⟩ := h
    rcases List.mem_cons.1 hp with rfl | hp' <;> rcases List.mem_cons.1 hq with rfl | hq'
    · rfl
    · rcases ha q hq' with h | h
      · exact h
      · exact absurd he h
    · rcases ha p hp' with h | h
      · exact h.symm
      · exact absurd he.symm h
    · exact testsDistinct_eq hr hp' hq' he

theorem selectEdge_key {key : Key.CtorKey} {alts : List (Key.CtorKey × Cfg.Edge)} {e : Cfg.Edge}
    (h : Cfg.selectEdge key alts none = some e) : ∃ p ∈ alts, p.1 = key := by
  refine Classical.byContradiction fun hn => ?_
  rw [selectEdge_none (fun p hp hk => hn ⟨p, hp, hk⟩)] at h
  cases h

theorem altTest_imm {T : Tables} {k : Key.CtorKey} {w : Word} (h : keyKind T k = some (.imm w)) :
    altTest T k = some (2, w) := by simp [altTest, h]

theorem altTest_cell {T : Tables} {k : Key.CtorKey} {t : Nat} (h : keyKind T k = some (.cell t)) :
    altTest T k = some (3, UInt64.ofNat t) := by simp [altTest, h]

/-! ## Dispatch -/

/-- **The check dispatches every scrutinee Cfg can select on**: a value
related to a word under the heap invariant, whose key selects an
alternative of a switch the check accepts (no default), is dispatched. -/
theorem dispatches_of_ok {T : Tables} {H : Own.Heap} {Pw : List Word} {ctx : Word} {m : X86.Memory}
    {v : Own.RVal} {w : Word} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge}
    {key : Key.CtorKey} {fs : List Own.RVal} {e : Cfg.Edge}
    (hpins : pinsApart T.known = true) (hok : switchOk T alts d = true) (hv : ValRel T Pw v w)
    (hheap : HeapInv T Pw H ctx m) (hac : v.asCtor T.known H = some (key, fs))
    (hsel : Cfg.selectEdge key alts d = some e) : Dispatches T H v alts := by
  simp only [switchOk, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true, List.all_eq_true,
    Bool.not_eq_true'] at hok
  obtain ⟨⟨rfl, hmix⟩, hdist⟩ := hok
  obtain ⟨q, hq, hqk⟩ := selectEdge_key hsel
  have hpins' : ∀ k, T.known.natZero = some k → T.known.natSucc ≠ some k := by
    intro k h0 h1
    simp [pinsApart, h0, h1] at hpins
  -- the key's kind and the scrutinee's shape
  obtain ⟨bH, lm, hlm⟩ := hheap
  have hcases : (∃ n, v = .lit (.nat n) ∧ natAlt T key = true ∧
        (∀ k', keyKind T k' = some .zero → v = .lit (.nat 0) → k' = key) ∧
        (∀ k', keyKind T k' = some .succ → (∃ n', v = .lit (.nat (n' + 1))) → k' = key) ∧
        Accepts T H key v) ∨
      (natAlt T key = false ∧ altTest T key = valTest H v ∧ Accepts T H key v ∧ (∀ n, v ≠ .lit (.nat n))) := by
    cases v with
    | lit l =>
      cases l with
      | str _ => exact absurd hv id
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
      obtain ⟨rfl, hc, hf⟩ := hv
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
        obtain ⟨-, hca, -, -⟩ := hlm.cell hv hcell
        have hk := keyKind_cellOk hca.ctor hca.fieldless
        refine .inr ⟨natAlt_ctorOk hca.ctor, ?_, ?_, fun n h => nomatch h⟩
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

/-- **The pipeline's check gives `SwitchSel` at every state.** -/
theorem switchSel_of_ok {P : Cfg.Program} (h : switchesOk P = true) : ∀ s, SwitchSel P s
  | .run fr _ H => by
    intro fd b x alts d v key fs e Pw w ctx m hfd hb _ _ hterm _ hv hheap hac hsel
    simp only [switchesOk, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hpins, hall⟩ := h
    have hblk := hall _ (Src.NatMap.mem_toList hfd) b (List.mem_of_getElem? hb)
    simp only [blockSwitchOk, hterm] at hblk
    exact dispatches_of_ok hpins hblk hv hheap hac hsel
  | .call .. => trivial
  | .ret .. => trivial

end IxCC.Rt.Proof
