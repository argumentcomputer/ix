import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.DynamicTag
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.CtorDispatch
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedWords
import Compilatrix.Rt.Proof.SwitchSim

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

/-- A live dynamic location follows the source-selected edge through the
actual lowered switch. The machine header load is derived from LiveCell. -/
theorem dynamic_switch {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {src x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge} {st st' stF : St}
    (hrun : (switch f T src x alts d).run st = .ok ((), st')) (hl : Labels st) (ho : Open st)
    (hg : Grows st' stF) (hC : Ext C stF)
    {addresses : AddressMap} {H : Own.Heap} {ctx : Word} {mem : X86.Memory} {rest : List Lir.Frame}
    {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hheap : HeapLive H addresses mem) (hρ : FusedWords addresses D sup ρ ρl) (hsup : sup ≤ st.fresh) (hxD : ¬ D x)
    {ℓ : Nat} (hv : ρ.get? x = some (.loc ℓ)) {c : Key.CtorKey} {fs : List Own.RVal}
    (hac : (Own.RVal.loc ℓ).asCtor T.known H = some (c, fs)) {e : Cfg.Edge} (hsel : Cfg.selectEdge c alts d = some e)
    (hdis : Dispatches T H (.loc ℓ) alts) :
    ∃ pe le ρl', EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) ∧ resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl' ∧ FusedWords addresses D sup ρ ρl' := by
  obtain ⟨wx, hrel, hwx⟩ := hρ.word hv hxD
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
    obtain ⟨n, impossible⟩ := hdis.1 p₀ hp₀ (by rw [hpq₀.1]; simp [hallNat q₀ hq₀])
    cases impossible
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
    -- a cell: its even address, its tag
    simp only [Own.RVal.asCtor, Own.Heap.cell?] at hac
    split at hac
    · rename_i rc mode b hcell
      simp only [Option.some.injEq, Prod.mk.injEq] at hac
      obtain ⟨rfl, -⟩ := hac
      obtain ⟨_, address, placed, hcellAt⟩ := hheap.cell ℓ rc mode b hcell
      have equal : address = wx := Option.some.inj (placed.symm.trans hrel)
      subst address
      have heven := live_pointer_even hcellAt
      have htag := live_tag_read hcellAt
      obtain ⟨pe, hpick, hok, hb⟩ : ∃ pe, (if cellTests es = [] then chainOrPick wx (immTests es) dd
          else chainOrPick (UInt64.ofNat b.ctor.tag) (cellTests es) dd) = some pe ∧ EdgeOk C f e pe ∧
          e.back = decide (e.target ≤ src) := by
        by_cases hce : cellTests es = []
        · simp only [hce, ↓reduceIte]
          have hnoCell : ∀ q ∈ es, cellTest q = none := List.filterMap_eq_nil_iff.1 hce
          refine pick_tests hR (link_tests (g := immTest) (fun _ _ _ h => immTest_snd h)
            (fun p q hpq => ?_) hrelM) hddF hsel
          obtain ⟨⟨hk, -, -⟩, hp, hq⟩ := hpq
          constructor
          · rintro ⟨a, pe, hga, ha⟩
            obtain ⟨w, hw, rfl, -⟩ := immTest_some.1 hga
            simp only [immOf, Option.some.injEq] at ha
            subst ha
            rw [hw] at hk
            obtain ⟨t, rfl⟩ := keyKind_imm hk
            have := ctor0Word_odd t
            have h0 := and_one_toNat (ctor0Word t)
            rw [heven] at h0
            simp at h0
            omega
          · intro hpc
            have hAcc := (hdis.2 p hp b.ctor.key b.fields (by simp [Own.RVal.asCtor, Own.Heap.cell?, hcell])).2 hpc
            obtain ⟨k, e'⟩ := q
            cases k with
            | imm w => simp only at hk; simp only [Accepts, hk, valWord] at hAcc; cases hAcc
            | cell t => exact absurd (hnoCell _ hq) (by simp [cellTest])
            | zero => exact absurd (hnone _ hq) (by simp [KeyKind.isNat])
            | succ => exact absurd (hnone _ hq) (by simp [KeyKind.isNat])
        · simp only [hce, ↓reduceIte]
          refine pick_tests hR (link_tests (g := cellTest) (fun _ _ _ h => cellTest_snd h)
            (fun p q hpq => ?_) hrelM) hddF hsel
          obtain ⟨⟨hk, -, -⟩, hp, hq⟩ := hpq
          have hiff := hdis.2 p hp b.ctor.key b.fields (by simp [Own.RVal.asCtor, Own.Heap.cell?, hcell])
          rw [← hiff]
          obtain ⟨k, e'⟩ := q
          simp only at hk
          cases k with
          | cell t =>
            simp only [Accepts, hk]
            constructor
            · rintro ⟨a, pe, hga, ha⟩
              obtain ⟨t', ht', rfl, -⟩ := cellTest_some.1 hga
              cases ht'
              simp only [immOf, Option.some.injEq] at ha
              exact ⟨ℓ, rc, mode, b, rfl, hcell, ha.symm⟩
            · rintro ⟨ℓ', rc', mode', b', hℓ, hcell', htag'⟩
              cases hℓ
              rw [hcell] at hcell'
              cases hcell'
              exact ⟨_, _, rfl, by simp [immOf, htag']⟩
          | imm w =>
            simp only [Accepts, hk, valWord]
            constructor
            · rintro ⟨a, pe, hga, -⟩; simp [cellTest] at hga
            · intro h; cases h
          | zero => exact absurd (hnone _ hq) (by simp [KeyKind.isNat])
          | succ => exact absurd (hnone _ hq) (by simp [KeyKind.isNat])
      obtain ⟨le, ρl', hle, hρl', hr⟩ := tagSwitch_even (mem := mem) (ctx := ctx) (rest := rest) hF hH h₄ hl₂
        ho₂' hg hC hwx heven htag hpick
      refine ⟨pe, le, ρl', hok, hb, hle, hr, ?_⟩
      rcases hρl' with rfl | rfl
      · exact hρ
      · exact hρ.marker (hfresh ▸ hsup) _
    · cases hac


theorem dynamic_switch_checked {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {src x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge} {st st' stF : St}
    (hrun : (switch f T src x alts d).run st = .ok ((), st')) (hl : Labels st) (ho : Open st)
    (hg : Grows st' stF) (hC : Ext C stF)
    {addresses : AddressMap} {H : Own.Heap} {ctx : Word} {mem : X86.Memory} {rest : List Lir.Frame}
    {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hheap : HeapLive H addresses mem) (hρ : FusedWords addresses D sup ρ ρl) (hsup : sup ≤ st.fresh) (hxD : ¬ D x)
    {ℓ : Nat} (hv : ρ.get? x = some (.loc ℓ)) {c : Key.CtorKey} {fs : List Own.RVal}
    (hac : (Own.RVal.loc ℓ).asCtor T.known H = some (c, fs)) {e : Cfg.Edge} (hsel : Cfg.selectEdge c alts d = some e)
    (compatible : HeapCtorOk T H)
    (pins : pinsApart T.known = true) (accepted : switchOk T alts d = true) :
    ∃ pe le ρl', EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) ∧ resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl' ∧ FusedWords addresses D sup ρ ρl' := by
  exact dynamic_switch hF hH hrun hl ho hg hC hheap hρ hsup hxD hv hac hsel
    (compatible_dispatches pins accepted (by trivial) compatible hac hsel)



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
