import IxCC.Rt.Proof.SwitchLink

/-!
# Switches: the simulation

`switch_sim`: from the position where a switch's code starts, Lir reaches
the block that takes the lowered edge of the alternative Cfg's `switch`
selects (`Dispatches` assumed of the scrutinee), with its registers related
to Cfg's variables (a loaded tag is a fresh temporary).
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

theorem ListRel.with_mem {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → ListRel (fun a b => R a b ∧ a ∈ as ∧ b ∈ bs) as bs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hr =>
    .cons ⟨h, by simp, by simp⟩
      ((ListRel.with_mem hr).mono fun _ _ ⟨hxy, hx, hy⟩ => ⟨hxy, by simp [hx], by simp [hy]⟩)

/-- A lowered alternative of the switch's lists. -/
def AltIn (C : List PBlock) (f : Fir.FunId) (T : Tables) (src : Nat) (alts : List (Key.CtorKey × Cfg.Edge))
    (es : List (KeyKind × PEdge)) (p : Key.CtorKey × Cfg.Edge) (q : KeyKind × PEdge) : Prop :=
  AltRel C f T src p q ∧ p ∈ alts ∧ q ∈ es

/-- The edge a chain with a default takes, from where the tests match. -/
theorem pick_tests {C : List PBlock} {f : Fir.FunId} {src : Nat}
    {R : Key.CtorKey × Cfg.Edge → KeyKind × PEdge → Prop}
    (hR : ∀ p q, R p q → EdgeOk C f p.2 q.2 ∧ p.2.back = decide (p.2.target ≤ src))
    {alts : List (Key.CtorKey × Cfg.Edge)} {c : Key.CtorKey} {wx : Word} {tests : List (Lir.Arg × PEdge)}
    (hlink : (∀ e, Cfg.selectEdge c alts none = some e → ∃ p q, R p q ∧ p.2 = e ∧ firstMatch wx tests = some q.2) ∧
      (Cfg.selectEdge c alts none = none → firstMatch wx tests = none))
    {d : Option Cfg.Edge} {dd : Option PEdge}
    (hdd : (d = none ∧ dd = none) ∨
      ∃ e pe, d = some e ∧ dd = some pe ∧ EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src))
    {e : Cfg.Edge} (hsel : Cfg.selectEdge c alts d = some e) :
    ∃ pe, chainOrPick wx tests dd = some pe ∧ EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) := by
  rw [selectEdge_dflt] at hsel
  cases hs : Cfg.selectEdge c alts none with
  | some e' =>
    rw [hs] at hsel
    cases hsel
    obtain ⟨p, q, hpq, rfl, hfm⟩ := hlink.1 _ hs
    exact ⟨q.2, chainOrPick_of_match hfm dd, hR p q hpq⟩
  | none =>
    rw [hs] at hsel
    rcases hdd with ⟨rfl, -⟩ | ⟨e', pe, rfl, rfl, hok, hb⟩
    · cases hsel
    · cases hsel
      exact ⟨pe, chainOrPick_dflt (hlink.2 hs) pe, hok, hb⟩

/-- The edge a `Nat` switch takes, from where the kinds match. -/
theorem pick_nat {C : List PBlock} {f : Fir.FunId} {src : Nat}
    {R : Key.CtorKey × Cfg.Edge → KeyKind × PEdge → Prop}
    (hR : ∀ p q, R p q → EdgeOk C f p.2 q.2 ∧ p.2.back = decide (p.2.target ≤ src))
    {alts : List (Key.CtorKey × Cfg.Edge)} {c : Key.CtorKey} {first other : Option PEdge}
    (hlink : (∀ e, Cfg.selectEdge c alts none = some e → ∃ p q, R p q ∧ p.2 = e ∧ first = some q.2) ∧
      (Cfg.selectEdge c alts none = none → first = none))
    {d : Option Cfg.Edge} {dd : Option PEdge}
    (hdd : (d = none ∧ dd = none) ∨
      ∃ e pe, d = some e ∧ dd = some pe ∧ EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src))
    {e : Cfg.Edge} (hsel : Cfg.selectEdge c alts d = some e) :
    ∃ pe, pick3 first dd other = some pe ∧ EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) := by
  rw [selectEdge_dflt] at hsel
  cases hs : Cfg.selectEdge c alts none with
  | some e' =>
    rw [hs] at hsel
    cases hsel
    obtain ⟨p, q, hpq, rfl, hfm⟩ := hlink.1 _ hs
    exact ⟨q.2, by rw [hfm]; rfl, hR p q hpq⟩
  | none =>
    rw [hs] at hsel
    rcases hdd with ⟨rfl, -⟩ | ⟨e', pe, rfl, rfl, hok, hb⟩
    · cases hsel
    · cases hsel
      exact ⟨pe, by rw [hlink.2 hs]; rfl, hok, hb⟩

/-- Cfg selects nothing where no key matches and there is no default. -/
theorem selectEdge_none {c : Key.CtorKey} :
    ∀ {alts : List (Key.CtorKey × Cfg.Edge)}, (∀ p ∈ alts, p.1 ≠ c) → Cfg.selectEdge c alts none = none
  | [], _ => rfl
  | (k, e) :: rest, h => by
    simp only [Cfg.selectEdge]
    rw [if_neg (h (k, e) (by simp))]
    exact selectEdge_none (fun p hp => h p (by simp [hp]))

theorem unless_run {c : Bool} {a : M Unit} {st st' : St} (h : (unless c do a).run st = .ok ((), st'))
    (ha : ∀ s, ¬ (a.run s).isOk) : c = true ∧ st' = st := by
  cases c with
  | true =>
    have e : (unless true do a : M Unit) = pure () := rfl
    rw [e] at h
    simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨rfl, h.2.symm⟩
  | false =>
    have e : (unless false do a : M Unit) = a := rfl
    rw [e] at h
    exact absurd (by rw [h]; rfl) (ha st)

theorem throw_not_ok {α : Type} (e : Error) (s : St) : ¬ ((throw e : M α).run s).isOk := by
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run, Except.isOk,
    Except.toBool]

theorem ListRel.exists_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, ListRel R as bs → ∀ {b : β}, b ∈ bs → ∃ a ∈ as, R a b
  | [], [], .nil, _, h => nomatch h
  | a :: _, _ :: _, .cons hab hr, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨a', ha', h'⟩ := ListRel.exists_left hr hb
      exact ⟨a', by simp [ha'], h'⟩

theorem immTest_some {q : KeyKind × PEdge} {a : Lir.Arg} {pe : PEdge} :
    immTest q = some (a, pe) ↔ ∃ w, q.1 = .imm w ∧ a = .imm w ∧ pe = q.2 := by
  obtain ⟨k, e⟩ := q
  cases k <;> simp [immTest, eq_comm]

theorem cellTest_some {q : KeyKind × PEdge} {a : Lir.Arg} {pe : PEdge} :
    cellTest q = some (a, pe) ↔ ∃ t, q.1 = .cell t ∧ a = .imm (UInt64.ofNat t) ∧ pe = q.2 := by
  obtain ⟨k, e⟩ := q
  cases k <;> simp [cellTest, eq_comm]

theorem immTest_snd {q : KeyKind × PEdge} {a : Lir.Arg} {pe : PEdge} (h : immTest q = some (a, pe)) :
    pe = q.2 := by
  obtain ⟨_, _, _, h'⟩ := immTest_some.1 h
  exact h'

theorem cellTest_snd {q : KeyKind × PEdge} {a : Lir.Arg} {pe : PEdge} (h : cellTest q = some (a, pe)) :
    pe = q.2 := by
  obtain ⟨_, _, _, h'⟩ := cellTest_some.1 h
  exact h'

/-- **A switch simulates Cfg's**: Lir reaches the block that takes the
lowered edge of the alternative Cfg selects. -/
theorem switch_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {src x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge} {st st' stF : St}
    (hrun : (switch f T src x alts d).run st = .ok ((), st')) (hl : Labels st) (ho : Open st)
    (hg : Grows st' stF) (hC : Ext C stF)
    {P : List Word} {H : Own.Heap} {ctx : Word} {mem : X86.Memory} {rest : List Lir.Frame}
    {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hheap : HeapInv T P H ctx mem) (hρ : EnvRel T P D sup ρ ρl) (hsup : sup ≤ st.fresh) (hxD : ¬ D x)
    {v : Own.RVal} (hv : ρ.get? x = some v) {c : Key.CtorKey} {fs : List Own.RVal}
    (hac : v.asCtor T.known H = some (c, fs)) {e : Cfg.Edge} (hsel : Cfg.selectEdge c alts d = some e)
    (hdis : Dispatches T H v alts) :
    ∃ pe le ρl', EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) ∧ resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl' ∧ EnvRel T P D sup ρ ρl' := by
  obtain ⟨wx, hwx, hrel⟩ := hρ.val hv hxD
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
    | loc ℓ =>
      -- a cell: its even address, its tag
      simp only [Own.RVal.asCtor, Own.Heap.cell?] at hac
      split at hac
      · rename_i rc mode b hcell
        simp only [Option.some.injEq, Prod.mk.injEq] at hac
        obtain ⟨rfl, -⟩ := hac
        obtain ⟨bump, limit, hA⟩ := hheap
        obtain ⟨-, hcellAt, -, hhi⟩ := hA.cell hrel hcell
        have hlim := hA.limitLt
        have hbl := hA.bumpLe
        have heven : wx &&& 1 = 0 := even_and (by have := hcellAt.aligned; omega)
        have htag := tag_mem hcellAt (by simp only [cellSize] at hhi; omega)
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
        · exact hρ.temp (hfresh ▸ hsup) _
      · cases hac
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

end IxCC.Rt.Proof
