import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorDispatch
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords
import IxCC.Rt.Proof.SwitchSim

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

theorem scalar_valRel {T : Tables} {addresses : AddressMap}
    {value : Own.RVal} {word : Word} (compatible : ValueCtorOk T value)
    (represented : valueWord addresses value = some word)
    (noncell : ∀ l, value ≠ .loc l) : ValRel T [] value word := by
  cases value with
  | loc l => exact False.elim (noncell l rfl)
  | lit literal =>
    cases literal with
    | nat n => exact represented
    | str s => cases represented
  | erased =>
    cases represented
    rfl
  | ctor0 ctor =>
    simp only [valueWord] at represented
    split at represented
    · exact ⟨(Option.some.inj represented).symm, compatible⟩
    · cases represented

/-- Ordinary immediate switches need no heap liveness assumption. Their
registers may still omit unrelated fused comparison results. -/
theorem scalar_switch {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {src x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge} {st st' stF : St}
    (hrun : (switch f T src x alts d).run st = .ok ((), st')) (hl : Labels st) (ho : Open st)
    (hg : Grows st' stF) (hC : Ext C stF)
    {addresses : AddressMap} {H : Own.Heap} {ctx : Word} {mem : X86.Memory} {rest : List Lir.Frame}
    {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : FusedWords addresses D sup ρ ρl) (hsup : sup ≤ st.fresh) (hxD : ¬ D x)
    {v : Own.RVal} (hv : ρ.get? x = some v) {c : Key.CtorKey} {fs : List Own.RVal}
    (hac : v.asCtor T.known H = some (c, fs)) {e : Cfg.Edge} (hsel : Cfg.selectEdge c alts d = some e)
    (hdis : Dispatches T H v alts)
    (compatible : ValueCtorOk T v) (noncell : ∀ l, v ≠ .loc l) :
    ∃ pe le ρl', EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) ∧ resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl' ∧ FusedWords addresses D sup ρ ρl' := by
  obtain ⟨wx, represented, hwx⟩ := hρ.word hv hxD
  have hrel := scalar_valRel compatible represented noncell
  unfold switch at hrun
  obtain ⟨es, st₁, h₁, h₂⟩ := run_bind hrun
  obtain ⟨dd, st₂, h₃, h₄⟩ := run_bind h₂
  obtain ⟨hg₁, hl₁, hc₁, ha₁, -, hf₁, ho₁, hrel₁⟩ := alts_run (mapM_run h₁) hl
  obtain ⟨hg₂, hl₂, hc₂, ha₂, -, hf₂, ho₂, hdd⟩ := dflt_run h₃ hl₁
  have ho₂' := ho₂ (ho₁ ho)
  have hcur : st₂.cur = st.cur := hc₂.trans hc₁
  have hacc : st₂.acc = st.acc := ha₂.trans ha₁
  have hfresh : st₂.fresh = st.fresh := hf₂.trans hf₁
  rw [← hcur, ← hacc]
  have hR : ∀ p q, AltIn C f T src alts es p q → EdgeOk C f p.2 q.2 ∧ p.2.back = decide (p.2.target ≤ src) :=
    fun p q h => ⟨h.1.2.1, h.1.2.2⟩
  dsimp only at h₄
  split at h₄
  · -- `Nat` keys
    rename_i hnats
    obtain ⟨hall, h₆⟩ : ((es.filter (·.1.isNat)).length == es.length) = true ∧
        (natSwitch x es dd).run st₂ = .ok ((), st') := by
      split at h₄
      · exact ⟨by assumption, h₄⟩
      · exfalso
        obtain ⟨_, s, h₅, -⟩ := run_bind h₄
        exact throw_not_ok _ _ (by rw [h₅]; rfl)
    obtain ⟨t, rfl⟩ := natSwitch_grows h₆
    have hgF : Grows st₁ stF := (hg₂.trans (grows_close ho₂' t)).trans hg
    have hrelM : ListRel (AltIn C f T src alts es) alts es := ListRel.with_mem (hrel₁ hgF hC)
    have hddF := hdd ((grows_close ho₂' t).trans hg) hC
    have hallNat : ∀ q ∈ es, q.1.isNat = true := by
      have h' : ∀ (a : KeyKind) (b : PEdge), (a, b) ∈ es → a.isNat = true := by simpa using hall
      intro q hq
      exact h' q.1 q.2 hq
    -- the scrutinee is a `Nat` literal
    obtain ⟨q₀, hq₀⟩ : ∃ q, q ∈ es := by
      cases es with
      | nil => simp at hnats
      | cons q _ => exact ⟨q, by simp⟩
    obtain ⟨p₀, hp₀, hpq₀⟩ := (hrel₁ hgF hC).exists_left hq₀
    obtain ⟨n, rfl⟩ := hdis.1 p₀ hp₀ (by rw [hpq₀.1]; simp [hallNat q₀ hq₀])
    have hwx' := natWord_toNat hrel
    cases n with
    | zero =>
      have hw1 : wx = 1 := UInt64.toNat_inj.mp (by rw [hwx']; rfl)
      have hc : T.known.natZero = some c := by
        simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
        obtain ⟨k, hk, rfl, -⟩ := hac
        exact hk
      have hlink := link_find (P := isZero) (c := c) (R := AltIn C f T src alts es) (fun p q hpq => by
        rw [← keyKind_zero.trans (by rw [hc]; exact ⟨fun h => Option.some.inj h.symm ▸ rfl, fun h => h ▸ rfl⟩ :
          T.known.natZero = some p.1 ↔ p.1 = c)]
        obtain ⟨k, e⟩ := q
        rw [hpq.1.1]
        cases k <;> simp [isZero]) hrelM
      obtain ⟨pe, hpick, hok, hb⟩ := pick_nat hR hlink hddF hsel (other := succEdge es)
      obtain ⟨le, hle, hr⟩ := natSwitch_reaches (mem := mem) (ctx := ctx) (rest := rest) hF hH h₆ hg hC hwx
        (pe := pe) (by simp only [natPick, hw1, ↓reduceIte]; exact hpick)
      exact ⟨pe, le, ρl, hok, hb, hle, hr, hρ⟩
    | succ m =>
      have hw1 : wx ≠ 1 := by intro h; subst h; simp at hwx'
      have hc : T.known.natSucc = some c := by
        simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
        obtain ⟨k, hk, rfl, -⟩ := hac
        exact hk
      have hlink := link_find (P := isSucc) (c := c) (R := AltIn C f T src alts es) (fun p q hpq => by
        obtain ⟨⟨hk, -, -⟩, hp, -⟩ := hpq
        constructor
        · intro hs
          obtain ⟨k, e⟩ := q
          cases k <;> simp [isSucc] at hs
          have := (keyKind_succ hk).2
          rw [hc] at this
          exact (Option.some.inj this).symm
        · intro hpc
          have hA := (hdis.2 p hp c fs hac).2 hpc
          by_cases hz : T.known.natZero = some p.1
          · have hk0 := keyKind_zero.2 hz
            simp only [Accepts, hk0] at hA
            cases hA
          · rw [keyKind_succ_of hz (hpc ▸ hc)] at hk
            obtain ⟨k, e⟩ := q
            cases hk
            rfl) hrelM
      obtain ⟨pe, hpick, hok, hb⟩ := pick_nat hR hlink hddF hsel (other := zeroEdge es)
      obtain ⟨le, hle, hr⟩ := natSwitch_reaches (mem := mem) (ctx := ctx) (rest := rest) hF hH h₆ hg hC hwx
        (pe := pe) (by simp only [natPick, hw1, ↓reduceIte]; exact hpick)
      exact ⟨pe, le, ρl, hok, hb, hle, hr, hρ⟩
  · -- other keys
    rename_i hnats
    have hnone : ∀ q ∈ es, q.1.isNat = false := by
      intro q hq
      cases hqn : q.1.isNat
      · rfl
      · exfalso
        apply hnats
        simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff]
        exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hq, hqn⟩)
    have hg₂F : Grows st₂ stF := (tagSwitch_grows h₄ hl₂ ho₂').trans hg
    have hgF : Grows st₁ stF := hg₂.trans hg₂F
    have hrelM : ListRel (AltIn C f T src alts es) alts es := ListRel.with_mem (hrel₁ hgF hC)
    have hddF := hdd hg₂F hC
    cases v with
    | loc ℓ => exact False.elim (noncell ℓ rfl)
    | erased => simp [Own.RVal.asCtor] at hac
    | _ =>
      all_goals
        obtain ⟨hvw, hodd⟩ := valWord_rel hrel (fun ℓ h => by cases h)
        have hodd' : wx &&& 1 ≠ 0 := odd_and hodd
        have hiff : ∀ p ∈ alts, ∀ q, AltRel C f T src p q → q ∈ es →
            ((∃ a pe, immTest q = some (a, pe) ∧ immOf a = some wx) ↔ p.1 = c) := by
          intro p hp q hpq hq
          rw [← hdis.2 p hp c fs hac]
          obtain ⟨k, e'⟩ := q
          have hk := hpq.1
          simp only at hk
          cases k with
          | imm w =>
            simp only [Accepts, hk, hvw, Option.some.injEq]
            constructor
            · rintro ⟨a, pe, hga, ha⟩
              obtain ⟨w', hw', rfl, -⟩ := immTest_some.1 hga
              cases hw'
              exact (by simpa [immOf] using ha : _ = wx).symm
            · intro h; subst h; exact ⟨_, _, rfl, rfl⟩
          | cell t =>
            simp only [Accepts, hk]
            constructor
            · rintro ⟨a, pe, hga, -⟩; simp [immTest] at hga
            · rintro ⟨ℓ, -, -, -, h, -⟩; cases h
          | zero => exact absurd (hnone _ hq) (by simp [KeyKind.isNat])
          | succ => exact absurd (hnone _ hq) (by simp [KeyKind.isNat])
        obtain ⟨pe, hpick, hok, hb⟩ := pick_tests hR (link_tests (g := immTest)
          (fun _ _ _ h => immTest_snd h) (fun p q hpq => hiff p hpq.2.1 q hpq.1 hpq.2.2) hrelM)
          hddF hsel
        have hshape : cellTests es = [] ∨ immTests es ≠ [] ∨ dd ≠ none := by
          by_cases hce : cellTests es = []
          · exact .inl hce
          · by_cases hie : immTests es = []
            · right; right
              intro hddn
              subst hddn
              rcases hddF with ⟨rfl, -⟩ | ⟨_, _, _, h, -⟩
              · -- every key is a cell's, and the value is not a cell: Cfg selects nothing
                have hsel' := hsel
                rw [selectEdge_dflt] at hsel'
                rw [selectEdge_none (fun p hp hpc => ?_)] at hsel'
                · cases hsel'
                · obtain ⟨q, hq, hpq⟩ : ∃ q ∈ es, AltRel C f T src p q := by
                    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
                    obtain ⟨q, hq, hpq⟩ := (hrel₁ hgF hC).get hi
                    exact ⟨q, List.mem_of_getElem? hq, hpq⟩
                  have := (hiff p hp q hpq hq).2 hpc
                  obtain ⟨a, pe', hga, -⟩ := this
                  have hnoImm : ∀ q ∈ es, immTest q = none := List.filterMap_eq_nil_iff.1 hie
                  rw [hnoImm q hq] at hga
                  cases hga
              · cases h
            · exact .inr (.inl hie)
        obtain ⟨le, hle, hr⟩ := tagSwitch_odd (mem := mem) (ctx := ctx) (rest := rest) hF hH h₄ hl₂ ho₂' hg hC hwx
          hodd' hshape hpick
        exact ⟨pe, le, ρl, hok, hb, hle, hr, hρ⟩




theorem scalar_switch_checked {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {src x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge} {st st' stF : St}
    (hrun : (switch f T src x alts d).run st = .ok ((), st')) (hl : Labels st) (ho : Open st)
    (hg : Grows st' stF) (hC : Ext C stF)
    {addresses : AddressMap} {H : Own.Heap} {ctx : Word} {mem : X86.Memory} {rest : List Lir.Frame}
    {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : FusedWords addresses D sup ρ ρl) (hsup : sup ≤ st.fresh) (hxD : ¬ D x)
    {v : Own.RVal} (hv : ρ.get? x = some v) {c : Key.CtorKey} {fs : List Own.RVal}
    (hac : v.asCtor T.known H = some (c, fs)) {e : Cfg.Edge} (hsel : Cfg.selectEdge c alts d = some e)
    (compatibleHeap : HeapCtorOk T H)
    (pins : pinsApart T.known = true) (accepted : switchOk T alts d = true)
    (compatible : ValueCtorOk T v) (noncell : ∀ l, v ≠ .loc l) :
    ∃ pe le ρl', EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) ∧ resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl' ∧ FusedWords addresses D sup ρ ρl' := by
  exact scalar_switch hF hH hrun hl ho hg hC hρ hsup hxD hv hac hsel
    (compatible_dispatches pins accepted compatible compatibleHeap hac hsel) compatible noncell



end IxCC.Cfg.Rc.Proof.Physical.Bridge
