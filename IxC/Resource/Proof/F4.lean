import IxC.Resource.Proof.F4Eval
import IxC.Resource.Proof.F4Inputs

/-!
# Soundness of `ModeOk` (`F4`: `ModeOk P → Safe P`)

Assembles the top-level outer budget induction (`FullIH P ext B`) and proves
`f4 : ∀ P, ModeOk P → Safe P`:

1. **Helpers**: `FunOkAt_once_true`, `initBody_props`, `NonValSafe_of_clsSafe_ne_val`.
2. **Checked body soundness**: `enterS_checked_sound` (`openRegion` + `bindParamsM_checked_sound`
   + `evalS_checked_sound` + `retCheck_bridge` + `closeRegion`) and `staticS_checked_sound`
   (cache hit via `StOk` + cache miss via `evalS_checked_sound` + `conform_spec_full` +
   `StOk_pushStatic`).
3. **Default body adapters**: `enterS_default_to_FullIH` and `staticS_default_to_FullIH`
   connecting `F4Default.enterS_default_sound` / `staticS_default_sound` to `FullIH`.
4. **Outer budget induction & main theorem**: `fullIH_zero`, `fullIH_step`, `fullIH_all`,
   and `theorem f4 : ∀ P, ModeOk P → Safe P`.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. Helpers -/

theorem FunOkAt_once_true {P : Prog} {ext : ExternOracle} {B : Nat}
    {st : St} {sk : Skel} {Foot : Nat → Prop} {f : Val}
    (hf : FunOkAt P ext B st sk false Foot f) :
    FunOkAt P ext B st sk true Foot f := by
  induction B using Nat.strongRecOn generalizing st sk Foot f with
  | ind B ih =>
    cases B with
    | zero => rw [FunOkAt]; trivial
    | succ b =>
      rw [FunOkAt] at hf ⊢
      rcases hap : arrowParts sk with ⟨m_in, dom, res, cod⟩
      rw [hap] at hf; dsimp only at hf ⊢
      intro B_call fuel st' f' a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt
        hsame hshape hrf hbf hopenF hcfF hba hopenA hcfA hFf hFa hFFa hfa haf haNum harg
      obtain ⟨hnoV, hok⟩ := hf B_call fuel st' f' a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt
        hsame hshape hrf hbf hopenF hcfF hba hopenA hcfA hFf hFa hFFa hfa haf haNum harg
      refine ⟨hnoV, fun rv st'' B' hrun => ?_⟩
      obtain ⟨hB', hst'', hsz, hcap, hrg, hnr, hstatExt, hstrExt, hpresF, honce, hssf,
        hbv, hcls, hopen, hcf, hreach, ⟨hResF, hResT⟩, huniq⟩ := hok rv st'' B' hrun
      refine ⟨hB', hst'', hsz, hcap, hrg, hnr, hstatExt, hstrExt, hpresF, honce, hssf,
        hbv, hcls, hopen, hcf, hreach, ⟨?_, ?_⟩, huniq⟩
      · intro hF1
        have hF0 : (isArrowSkel cod && (false || m_in.isUnique || (m_in.usage == .once))) = false := by
          cases hia : isArrowSkel cod <;> simp [hia] at hF1 ⊢
        exact hResF hF0
      · intro hT1
        cases h0 : (isArrowSkel cod && (false || m_in.isUnique || (m_in.usage == .once))) with
        | true => exact hResT h0
        | false =>
          obtain ⟨_, hfun0⟩ := hResF h0
          exact ⟨fun _ => False, (fun _ h => False.elim h), ih B' (by omega) hfun0⟩

theorem initBody_props (params : Array Param) :
    (initBody params).2.regions = [2, 1] ∧
    (initBody params).2.nextRegion = 3 ∧
    (∀ i, i < (initBody params).2.st.size → (initBody params).2.st[i]? ≠ some .dead) ∧
    (∀ i, i < (initBody params).2.spent.size → (initBody params).2.spent[i]? = some false) := by
  unfold initBody
  rw [← Array.foldl_toList]
  have hgo : ∀ (ps : List Param) (acc : List ABnd × AState),
      acc.2.regions = [2, 1] →
      acc.2.nextRegion = 3 →
      (∀ i, i < acc.2.st.size → acc.2.st[i]? ≠ some .dead) →
      (∀ i, i < acc.2.spent.size → acc.2.spent[i]? = some false) →
      let res := ps.foldl (init := acc) fun (env, σ) p =>
        let v := paramVal p 2
        let (id, σ') := σ.pushBnd v (p.mode.usage == .once)
        ({ id, mode := p.mode, val := v } :: env, σ')
      res.2.regions = [2, 1] ∧
      res.2.nextRegion = 3 ∧
      (∀ i, i < res.2.st.size → res.2.st[i]? ≠ some .dead) ∧
      (∀ i, i < res.2.spent.size → res.2.spent[i]? = some false) := by
    intro ps
    induction ps with
    | nil => intro acc h1 h2 h3 h4; exact ⟨h1, h2, h3, h4⟩
    | cons p rest ih =>
      intro ⟨env, σ⟩ h1 h2 h3 h4
      dsimp only [List.foldl]
      apply ih
      · simpa [AState.pushBnd] using h1
      · simpa [AState.pushBnd] using h2
      · intro i hi
        simp only [AState.pushBnd, Array.size_push] at hi
        by_cases hlt : i < σ.st.size
        · simp only [AState.pushBnd, Array.getElem?_push, Nat.ne_of_lt hlt, ↓reduceIte]
          exact h3 i hlt
        · have heq : i = σ.st.size := by omega
          subst heq; simp only [AState.pushBnd, Array.getElem?_push, ↓reduceIte]
          cases (paramVal p 2).own == .uniq <;> decide
      · intro i hi
        simp only [AState.pushBnd, Array.size_push] at hi
        by_cases hlt : i < σ.spent.size
        · simp only [AState.pushBnd, Array.getElem?_push, Nat.ne_of_lt hlt, ↓reduceIte]
          exact h4 i hlt
        · have heq : i = σ.spent.size := by omega
          subst heq; simp [AState.pushBnd]
  exact hgo params.toList ([], { regions := [2, 1], nextRegion := 3 })
    rfl rfl (fun _ h => by simp at h) (fun _ h => by simp at h)

theorem NonValSafe_of_clsSafe_ne_val {st : St} {c : Cls} {v : Val}
    (hbv : ValBaseOk st v) (hcls : ClsSafe st.heap c v) (hne : c ≠ .val) :
    NonValSafe st.heap v := by
  cases c with
  | val => exact absurd rfl hne
  | irr =>
    rcases hcls with h | h
    · exact Or.inl ⟨.irr, h⟩
    · exact Or.inl ⟨.irr, h⟩
  | imm =>
    rcases hcls with h | ⟨imm, h⟩
    · exact Or.inl ⟨.irr, h⟩
    · exact Or.inl ⟨imm, h⟩
  | leaf =>
    rcases hcls with h | ⟨loc, cap, o, n, rfl, ho, hnum, hcap⟩
    · exact Or.inl ⟨.irr, h⟩
    · obtain ⟨o', ho', hcap'⟩ := hbv.1.self.1
      rw [ho] at ho'; cases ho'
      exact Or.inr ⟨loc, cap, o, n, rfl, ho, hcap', hnum⟩

/-! ## 2. Checked Body Soundness (`enterS_checked_sound` and `staticS_checked_sound`) -/

theorem enterS_checked_sound {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {params : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term}
    {vs : List Val} {st : St} {Frame : Nat → Prop} {argRegs : List Nat}
    {argOnce : Nat → Bool} {argFoot : Nat → Nat → Prop}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    (hb : b ≤ B + 1)
    (hlc : LamsClosed body) (hcfd : CaseFieldsDistinct body)
    (hbody : BodyOk P params res rc rs body)
    (hlen : vs.length = params.size)
    (hst : StOk P ext b st)
    (hstat : ∀ l, StaticStrLoc st l → Frame l)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hargs : ∀ (i : Nat) (p : Param) (v : Val), params[i]? = some p → vs[i]? = some v →
      (p.mode ≠ .erased →
        ValBaseOk st v ∧
        DeepOpenUnder st.heap st.regions argRegs v ∧
        CtorFieldsOk P ext b st v ∧
        (p.mode.usage = .once →
          FunOkAt P ext b st p.skel (argOnce i) (argFoot i) v ∧
          (∀ l, argFoot i l → Reach st.heap v l ∧ ¬ Frame l ∧ ¬ NumLoc st.heap l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st.heap v ∧ argOnce i = false ∧ (∀ l, ¬ argFoot i l) ∧
          FunOkAt P ext b st p.skel false (fun _ => False) v) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st.heap v ∧
          (∀ l, OwnReach P st.heap v l → ¬ Frame l) ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v))))
    (hdisj : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      params[i]? = some pi → vs[i]? = some vi →
      params[j]? = some pj → vs[j]? = some vj →
      pj.mode ≠ .erased →
      (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) ∧
      (pi.mode.usage = .once → ∀ l, argFoot i l → ¬ Reach st.heap vj l) ∧
      (pi.mode.usage = .once → pj.mode.usage = .once → ∀ l, argFoot i l → ¬ argFoot j l)) :
    (∀ k, (enterS P ext fuel params res rc body vs).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (enterS P ext fuel params res rc body vs).run (st, b) = .ok (rv, (st', B')) →
        B' ≤ b ∧
        StOk P ext B' st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧
        st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧
        ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesOnceShell st.heap st'.heap ∧
        StaticStrFresh st st' ∧
        ValBaseOk st' rv ∧
        ClsSafe st'.heap rc rv ∧
        NoOnceCell st'.heap rv ∧
        CtorFieldsOk P ext B' st' rv ∧
        FunOkAt P ext B' st' rs false (fun _ => False) rv ∧
        DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc [] argRegs) rv ∧
        (∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨
          (∃ (i : Nat) (p : Param) (v : Val),
            params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧
            (res.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧
            Reach st.heap v l) ∨
          StaticStrLoc st l ∨
          NumLoc st'.heap l) ∧
        (res.isUnique = true ∧ rc = .val →
          OwnTreeFull P st'.heap rv ∧
          ∀ l, OwnReach P st'.heap rv l → ¬ Frame l ∧ ¬ StaticStrLoc st' l) := by
  cases fuel with
  | zero =>
    cases b with
    | zero =>
      have h0 : (enterS P ext 0 params res rc body vs).run (st, 0) = .error .outOfFuel := by
        unfold enterS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b0 =>
      have h0 : (enterS P ext 0 params res rc body vs).run (st, b0 + 1) = .error .outOfFuel := by
        unfold enterS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    cases b with
    | zero =>
      have h0 : (enterS P ext (n + 1) params res rc body vs).run (st, 0) = .error .outOfFuel := by
        unfold enterS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b0 =>
      obtain ⟨_, r_a, σ₁, σ₂, hder, hretChk⟩ := hbody
      have hb0B : b0 ≤ B := Nat.le_of_succ_le_succ hb
      have hst0 : StOk P ext b0 st := StOk_mono (Nat.le_succ b0) hst
      let s := st.nextRegion
      let cur := st.regions.headD 0
      let st₁ : St := { st with nextRegion := s + 1, regions := s :: st.regions }
      have hbpArgs : ∀ (i : Nat) (p : Param) (v : Val), params[i]? = some p → vs[i]? = some v → p.mode ≠ .erased →
          ValBaseOk st v ∧
          DeepOpenUnder st.heap st.regions argRegs v ∧
          CtorFieldsOk P ext b0 st v ∧
          (p.mode.usage = .once →
            FunOkAt P ext b0 st p.skel true (argFoot i) v ∧
            (true = false → ∀ l, ¬ argFoot i l) ∧
            (∀ l, argFoot i l → Reach st.heap v l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l)) ∧
          (p.mode.usage ≠ .once →
            NoOnceCell st.heap v ∧ FunOkAt P ext b0 st p.skel false (fun _ => False) v) ∧
          (p.mode.isUnique = true →
            OwnTreeFull P st.heap v ∧
            (∀ l, OwnReach P st.heap v l → ¬ Frame l ∧ ¬ StaticStrLoc st l) ∧
            (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v)) := by
        intro i p v hp hv hne
        obtain ⟨hbv, hopen, hcf, honce, hnotOnce, huniq⟩ := hargs i p v hp hv hne
        refine ⟨hbv, hopen, CtorFieldsOk_mono (Nat.le_succ b0) hcf, ?_, ?_, ?_⟩
        · intro hu
          obtain ⟨hfun, hft⟩ := honce hu
          have hfunT : FunOkAt P ext b0 st p.skel true (argFoot i) v := by
            cases hao : argOnce i with
            | true => rw [hao] at hfun; exact FunOkAt_mono (Nat.le_succ b0) hfun
            | false => rw [hao] at hfun; exact FunOkAt_once_true (FunOkAt_mono (Nat.le_succ b0) hfun)
          exact ⟨hfunT, (fun h => by cases h), fun l hl =>
            let ⟨hr, hnf, hnn⟩ := hft l hl
            ⟨hr, hnf, fun hss => hnf (hstat l hss), hnn⟩⟩
        · intro hnu
          obtain ⟨hno, _, _, hfun⟩ := hnotOnce hnu
          exact ⟨hno, FunOkAt_mono (Nat.le_succ b0) hfun⟩
        · intro hu
          obtain ⟨hot, hor, hdo⟩ := huniq hu
          exact ⟨hot, fun l h => ⟨hor l h, fun hss => hor l h (hstat l hss)⟩, hdo⟩
      have hbpPair : ∀ (i j : Nat) (p₁ p₂ : Param) (v₁ v₂ : Val), i ≠ j →
          params[i]? = some p₁ → vs[i]? = some v₁ →
          params[j]? = some p₂ → vs[j]? = some v₂ →
          p₁.mode ≠ .erased → p₂.mode ≠ .erased →
          (p₁.mode.isUnique = true → ∀ l, OwnReach P st.heap v₁ l → ¬ Reach st.heap v₂ l) ∧
          (p₁.mode.usage = .once → ∀ l, argFoot i l → ¬ Reach st.heap v₂ l) := by
        intro i j p₁ p₂ v₁ v₂ hij hp₁ hv₁ hp₂ hv₂ _ hne₂
        have hd := hdisj i j p₁ p₂ v₁ v₂ hij hp₁ hv₁ hp₂ hv₂ hne₂
        exact ⟨hd.1, hd.2.1⟩
      have hbp := bindParamsM_checked_sound (fuel := n) (argOnce := fun _ => true) (argFoot := argFoot)
        hst0 hlen hFlt hbpArgs hbpPair
      dsimp only at hbp
      have hunfold : (enterS P ext (n + 1) params res rc body vs).run (st, b0 + 1) =
          match (bindParamsM P n s (params.toList.zip vs) []).run st₁ with
          | .error e => .error e
          | .ok (env, st₂) =>
            match (evalS P ext n env body).run (st₂, b0) with
            | .error e => .error e
            | .ok (rv_b, (st₃, B₃)) =>
              match (ret P n s cur res rc rv_b).run st₃ with
              | .error e => .error e
              | .ok (rv', st_ret) => .ok (rv', ({ st_ret with regions := st_ret.regions.filter (· != s) }, B₃)) := by
        unfold enterS; rw [MS_bind_run, MS_spend_succ]; dsimp only
        rw [MS_bind_run, MS_liftM_run, openRegion_run st]; dsimp only [s, cur, st₁]
        rw [MS_bind_run, MS_liftM_run]
        cases (bindParamsM P n s (params.toList.zip vs) []).run st₁ with
        | error _ => rfl
        | ok p1 =>
          rcases p1 with ⟨env, st₂⟩; dsimp only
          rw [MS_bind_run]
          cases (evalS P ext n env body).run (st₂, b0) with
          | error _ => rfl
          | ok p2 =>
            rcases p2 with ⟨rv_b, ⟨st₃, B₃⟩⟩; dsimp only
            rw [MS_bind_run, MS_liftM_run]
            cases (ret P n s cur res rc rv_b).run st₃ with
            | error _ => rfl
            | ok p3 =>
              rcases p3 with ⟨rv', st_ret⟩; dsimp only
              rw [MS_bind_run, MS_liftM_run, closeRegion_run s st_ret]; rfl
      rw [hunfold]
      rcases hbp with hSt | hOOF |
        ⟨env, st₂, hbpRun, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
         hpFrame₂, hpSS₂, honce₂, hssf₂, hst₂, ⟨envFoot, hsim₀⟩, hregU₀, henvNRF₀, hreachEnv₂⟩
      · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hbpRun]; dsimp only
        let I₀ : Interp := ⟨fun r => if r == 2 then [s] else argRegs.filter (· < s)⟩
        let I : Interp := ⟨fun r => if r == 2 then [s] else if r < 3 then argRegs.filter (· < s) else []⟩
        obtain ⟨hinitRegs, hinitNR, hinitSt, hinitSp⟩ := initBody_props params
        have hIagree : ∀ r, r < (initBody params).2.nextRegion → I₀.reg r = I.reg r := by
          intro r hr; rw [hinitNR] at hr; dsimp only [I₀, I]; simp [hr]
        have hIok₂ : InterpOk (initBody params).2 st₂ I :=
          ⟨fun r hr c hc => hsim₀.2.2.1.1 r hr c (hIagree r hr ▸ hc),
           fun c hc => by
            have h0 := hsim₀.2.2.1.2 c hc
            rw [hinitRegs] at h0 ⊢; exact h0⟩
        have hsim₂ : Sim P ext b0 st₂ Frame (fun _ => False) (fun _ => False) (fun _ => True)
            env (initBody params).1 (initBody params).2 I envFoot :=
          Sim_interp_congr hIok₂ hIagree hsim₀
        have hregU₂ : RegUnique I (initBody params).2 2 s := by
          refine ⟨by dsimp [I], fun r hr hne hmem => ?_⟩
          by_cases hlt : r < 3
          · exact hregU₀.2 r hr hne (hIagree r (hinitNR ▸ hlt) ▸ hmem)
          · dsimp only [I] at hmem
            have hne2 : (r == 2) = false := beq_false_of_ne hne
            simp [hne2, hlt] at hmem
        have hIZero₂ : ∀ reg, (initBody params).2.nextRegion ≤ reg → I.reg reg = [] := by
          intro reg hge; rw [hinitNR] at hge
          dsimp only [I]
          have hne2 : (reg == 2) = false := beq_false_of_ne (by omega)
          have hnotLt : ¬ (reg < 3) := by omega
          simp [hne2, hnotLt]
        have hHeadReg₂ : st₂.regions.headD 0 = 0 ∨ st₂.regions.headD 0 ∈ I.reg ((initBody params).2.regions.headD 1) := by
          right; rw [hrg₂, hinitRegs]; exact List.mem_singleton.mpr rfl
        have hstat₂F : ∀ l, StaticStrLoc st₂ l → Frame l := fun l hss => by
          have hss0 : StaticStrLoc st l := by
            rcases hss with ⟨r0, v0, hm, hr⟩ | ⟨s0, v0, hm, hr⟩
            · rw [hstat₂] at hm
              have hpv : PreservesLocs (Reach st.heap v0) st.heap st₂.heap :=
                hpSS₂.mono fun l' hl' => Or.inl ⟨r0, v0, hm, hl'⟩
              exact Or.inl ⟨r0, v0, hm, (Reach_congr hpv l).mp hr⟩
            · rw [hstr₂] at hm
              have hpv : PreservesLocs (Reach st.heap v0) st.heap st₂.heap :=
                hpSS₂.mono fun l' hl' => Or.inr ⟨s0, v0, hm, hl'⟩
              exact Or.inr ⟨s0, v0, hm, (Reach_congr hpv l).mp hr⟩
          exact hstat l hss0
        have hFlt₂ : ∀ l, Frame l → l < st₂.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₂
        have henvTaint₂ : EnvTaintOk (fun _ => True) env (initBody params).1 st₂ I := by
          intro i b_c ab _ hbi habi hne
          have hvB := ((hsim₂.2.2.2.2.2.1 i b_c ab trivial hbi habi).2 hne).2
          have hvd : ValidDeps (initBody params).2 (effVal ab).deps := fun d hd =>
            have hlt := hvB.2.1 d hd
            ⟨hlt, hinitSt d hlt⟩
          have hact : ActiveVal (initBody params).2 (effVal ab) :=
            ⟨hvd, fun _ d hd _ => by rw [hinitSp d (hsim₂.2.1.2.1 ▸ hvB.2.1 d hd)]⟩
          obtain ⟨hbv, hdou, _⟩ := hvB.2.2.2.2 hact
          exact ⟨hbv.2.2.2 b_c.val (Or.inl rfl), hdou b_c.val (Or.inl rfl)⟩
        let ForbidNB : Nat → Prop := fun l =>
          l < st.heap.objs.size ∧ ¬ StaticStrLoc st l ∧
          ∀ (i : Nat) p v, params[i]? = some p → vs[i]? = some v →
            p.mode ≠ .erased → p.mode.isBorrowed = false → ¬ Reach st.heap v l
        let ForbidAll : Nat → Prop := fun l =>
          l < st.heap.objs.size ∧ ¬ StaticStrLoc st l ∧
          ∀ (i : Nat) p v, params[i]? = some p → vs[i]? = some v →
            p.mode ≠ .erased → ¬ Reach st.heap v l
        let Forbid : Nat → Prop := if res.isBorrowed then ForbidAll else ForbidNB
        let BadReg : Nat → Prop := if res.isBorrowed then (fun _ => False) else (· = 2)
        have hForbLt₂ : ∀ l, Forbid l → l < st₂.heap.objs.size := fun l hF => by
          dsimp only [Forbid] at hF
          cases hrb : res.isBorrowed <;> rw [hrb] at hF
          · exact Nat.lt_of_lt_of_le hF.1 hsz₂
          · exact Nat.lt_of_lt_of_le hF.1 hsz₂
        have henvNRF₂ : EnvNoReachForbid st₂ (fun _ => True) env (initBody params).1 (initBody params).2
            Forbid BadReg (fun _ => False) := by
          dsimp only [Forbid, BadReg]
          cases hrb : res.isBorrowed with
          | false => exact henvNRF₀
          | true =>
            intro i b_c ab _ hbi _ _ _ _ _ l hr _ _ hF
            rcases hreachEnv₂ b_c (List.mem_of_getElem? hbi) l hr with hge | ⟨k, pk, vk, hpk, hvk, hnek, hrk⟩
            · exact Nat.not_lt_of_ge hge hF.1
            · exact hF.2.2 k pk vk hpk hvk hnek hrk
        obtain ⟨hok₁, hle₁, hreg₁⟩ := ATerm_state_le hsim₂.2.1 hder
        obtain ⟨hnoVE, hokE⟩ := evalS_checked_sound hidx hext hih hder hlc hcfd (B₀ := b0) (fuel := n)
          (by omega) (fun _ _ => trivial) hst₂ hsim₂ hstat₂F hFlt₂
          (fun _ h => False.elim h) (fun _ h => False.elim h)
          hIZero₂ hHeadReg₂ henvTaint₂ henvNRF₂ hForbLt₂ (fun _ h => False.elim h)
        cases hev : (evalS P ext n env body).run (st₂, b0) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoVE k hev), (fun _ _ _ h => by cases h)⟩
        | ok pe =>
          rcases pe with ⟨rv_b, ⟨st₃, B₃⟩⟩; dsimp only
          obtain ⟨rFoot, hB₃, hst₃, hsz₃, hcap₃, hr₃, hnr₃, hstat₃, hstr₃,
            hpFrame₃, hpEnv₃, hpNum₃, honce₃, hssf₃, hsim₃, henvTaint₃, henvNRF₃,
            hvR, hdisjR, hnrfR, hnvR, _, _, _⟩ := hokE rv_b st₃ B₃ hev
          let Frame₃ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₃ l
          have hFlt₃ : ∀ l, Frame₃ l → l < st₃.heap.objs.size := fun l h =>
            h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt₂ l hF) hsz₃) (fun hss => StOk_staticStrLoc_lt hst₃ hss)
          have hcurLt₃ : cur < st₃.nextRegion := by
            have hcurLt0 : cur < st.nextRegion := by
              dsimp only [cur]
              cases hregs : st.regions with
              | nil => exact hst.2.1.1
              | cons c _ => exact (hst.2.1.2.2 c (hregs ▸ List.mem_cons_self)).2
            have : st.nextRegion < st₃.nextRegion := by
              have : st₂.nextRegion = st.nextRegion + 1 := hnr₂
              omega
            omega
          have hregU₃ : RegUnique I σ₁ 2 s := by
            refine ⟨hregU₂.1, fun r hr hne hmem => ?_⟩
            by_cases hlt : r < 3
            · exact hregU₂.2 r (hinitNR ▸ hlt) hne hmem
            · rw [hIZero₂ r (by rw [hinitNR]; omega)] at hmem; cases hmem
          have hsIn₃ : s ∈ st₃.regions := by
            rw [hr₃, hrg₂]; exact List.mem_cons_self
          rcases retCheck_bridge (fuel := n) (cur := cur) hst₃ (Sim_add_staticStr hsim₃) henvNRF₃ hFlt₃
              (fun _ h => False.elim h) hcurLt₃ hregU₃ hsIn₃ (VSim_add_staticStr hvR) hdisjR hretChk with
            hSt | hOOF |
            ⟨rv', st_ret, hretRun, hrg_ret, hnr_ret, hstat_ret, hstr_ret, hsz_ret, hcap_ret,
             hpFrame_ret, hpSS_ret, honce_ret, hssf_ret, hst_ret, _, _,
             hbv', hcls', hno', hcf', hfunExp', _, hnv', _, huniqRet, hopenSU, hopenU, hopenB,
             hreachRet, _, _, _⟩
          · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hretRun]; dsimp only
            refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
            cases hokEq
            let st' : St := { st_ret with regions := st_ret.regions.filter (· != s) }
            have hsNotIn : s ∉ st.regions := fun hm => Nat.lt_irrefl s (hst.2.1.2.2 s hm).2
            have hst'Regs : st'.regions = st.regions := by
              dsimp only [st']; rw [hrg_ret, hr₃, hrg₂]
              rw [List.filter_cons, bne_self_eq_false]
              exact List.filter_eq_self.mpr fun x hx => bne_iff_ne.mpr fun hEq => hsNotIn (hEq ▸ hx)
            have hrfClose : RegsFuture st_ret st' := RegsFuture.closeRegion st_ret s
            have hst'Ok : StOk P ext B₃ st' := StOk_closeRegion s hst_ret
            have hssf03 : StaticStrFresh st st₃ :=
              StaticStrFresh.trans hsz₂ (hpFrame₃.mono hstat₂F) hssf₂ hssf₃
            have hssf0ret : StaticStrFresh st st_ret :=
              StaticStrFresh.trans (Nat.le_trans hsz₂ hsz₃) hpSS_ret hssf03 hssf_ret
            have hssfFinal : StaticStrFresh st st' := hssf0ret
            have hopenFinal : DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc [] argRegs) rv' := by
              have hregsEq : st'.regions = st₃.regions.filter (· != s) := by
                dsimp only [st']; rw [hrg_ret]
              rw [hregsEq]
              by_cases hrcV : rc = .val
              · subst hrcV
                have hIsub : ∀ x ∈ I.regsOf (r_a.regs.filter (· != 2)), x ∈ argRegs := by
                  intro x hx
                  obtain ⟨rg, hrgIn, hxIn⟩ := Interp.mem_regsOf.mp hx
                  have hne2 : rg ≠ 2 := by
                    have := (List.mem_filter.mp hrgIn).2
                    exact bne_iff_ne.mp this
                  dsimp only [I] at hxIn
                  rw [beq_false_of_ne hne2] at hxIn
                  simp only [Bool.false_eq_true, ↓reduceIte] at hxIn
                  split at hxIn
                  · exact (List.mem_filter.mp hxIn).1
                  · cases hxIn
                cases hres : res with
                | unique =>
                  simpa [applyResultRegs] using hopenU hres
                | shared =>
                  simp only [applyResultRegs, List.append_nil]
                  exact hopenSU argRegs (Or.inl hres) hIsub
                | borrowed =>
                  cases hsr : st.regions with
                  | nil =>
                    have hcur0 : cur = 0 := by dsimp [cur]; rw [hsr]; rfl
                    simp only [applyResultRegs, hsr, List.append_nil]
                    exact hopenB argRegs (by rw [hres]; rfl) hIsub (Or.inr (Or.inl hcur0))
                  | cons c rest =>
                    have hcurC : cur = c := by dsimp [cur]; rw [hsr]; rfl
                    simp only [applyResultRegs, hsr, List.append_nil]
                    exact hopenB (c :: argRegs) (by rw [hres]; rfl)
                      (fun x hx => List.mem_cons_of_mem c (hIsub x hx)) (Or.inr (Or.inr (hcurC ▸ List.mem_cons_self)))
                | uniqueBorrowed =>
                  cases hsr : st.regions with
                  | nil =>
                    have hcur0 : cur = 0 := by dsimp [cur]; rw [hsr]; rfl
                    simp only [applyResultRegs, hsr, List.append_nil]
                    exact hopenB argRegs (by rw [hres]; rfl) hIsub (Or.inr (Or.inl hcur0))
                  | cons c rest =>
                    have hcurC : cur = c := by dsimp [cur]; rw [hsr]; rfl
                    simp only [applyResultRegs, hsr, List.append_nil]
                    exact hopenB (c :: argRegs) (by rw [hres]; rfl)
                      (fun x hx => List.mem_cons_of_mem c (hIsub x hx)) (Or.inr (Or.inr (hcurC ▸ List.mem_cons_self)))
              · exact (hnv' hrcV).deepOpenUnder_nil
            have hreachFinal : ∀ l, Reach st'.heap rv' l →
                st.heap.objs.size ≤ l ∨
                (∃ (i : Nat) (p : Param) (v : Val),
                  params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧
                  (res.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧
                  Reach st.heap v l) ∨
                StaticStrLoc st l ∨
                NumLoc st'.heap l := by
              intro l hl
              by_cases hge0 : st.heap.objs.size ≤ l
              · exact Or.inl hge0
              · have hlt0 : l < st.heap.objs.size := Nat.lt_of_not_ge hge0
                by_cases hrcV : rc = .val
                · subst hrcV
                  rcases hreachRet l hl with hge3 | hrB
                  · exact Or.inl (Nat.le_trans (Nat.le_trans hsz₂ hsz₃) hge3)
                  · by_cases hss3 : StaticStrLoc st₃ l
                    · rcases hssf03 l hss3 with hge | hss0 | ⟨o3, n3, ho3, hc3⟩
                      · exact Or.inl hge
                      · exact Or.inr (Or.inr (Or.inl hss0))
                      · have hpRet3 := hpSS_ret l hss3
                        exact Or.inr (Or.inr (Or.inr ⟨o3, n3, hpRet3.trans ho3, hc3⟩))
                    · by_cases hnum3 : NumLoc st₃.heap l
                      · obtain ⟨o3, n3, ho3, hc3⟩ := hnum3
                        obtain ⟨_, _, _, _, _, _, _, hvdR, _, hooR, hnotOnceR, hvalInfo, _⟩ := Runs_retCheck hok₁ hretChk
                        have haR : ActiveVal σ₁ r_a := ⟨hvdR, fun his => absurd his hnotOnceR⟩
                        obtain ⟨hbvB, hdouB, _, _, _, _, _, htrB⟩ := hvR.2.2.2.2 haR
                        have htreeR : res.isUnique = true → OwnTreeFull P st₃.heap rv_b := fun hu => by
                          by_cases hrCls : r_a.cls = .val
                          · exact (htrB ⟨hrCls, (hvalInfo rfl).2.2 hu |>.1, hooR, hnotOnceR,
                              fun d hd => ⟨(hvalInfo rfl).2.2 hu |>.2 d hd, fun h => False.elim h⟩⟩).1
                          · obtain ⟨_, hnvB⟩ := hnvR hvdR hrCls
                            rcases hnvB with ⟨imm, rfl⟩ | ⟨loc, cap, o, num, rfl, ho, _, hc⟩
                            · exact OwnTreeFull_imm P st₃.heap imm
                            · exact OwnTreeFull_num ho hc
                        have hnoS : (res = .shared ∨ res = .unique) → OpenUnder [s] [] rv_b := fun hsu => by
                          have hnot2 : 2 ∉ r_a.regs := (hvalInfo rfl).1 hsu
                          have hnotS : s ∉ I.regsOf r_a.regs := fun hm => by
                            obtain ⟨rg, hrgIn, hsIn⟩ := Interp.mem_regsOf.mp hm
                            exact hregU₃.2 rg (hvR.1 rg hrgIn) (fun h => hnot2 (h ▸ hrgIn)) hsIn
                          intro c hc hcs
                          have h1 := hdouB rv_b (Or.inl rfl) c hc
                          simp only [List.mem_singleton] at hcs
                          subst hcs; exact False.elim (hnotS (h1 hsIn₃))
                        have hnoOpen : res = .unique → OpenUnder st₃.regions [] rv_b := fun hu => by
                          have hregsNil : r_a.regs = [] := (hvalInfo rfl).2.1 hu
                          have h1 := hdouB rv_b (Or.inl rfl)
                          simpa [hregsNil, Interp.regsOf] using h1
                        have hretSp := ret_spec (P := P) (fuel := n) (s := s) (cur := cur) (r := res) (c := .val)
                          hst₃.1 hbvB.1 hbvB.2.1 htreeR hnoS hnoOpen
                        rcases hretSp with hSt' | hOOF' | ⟨_, _, hrun', _, _, _, _, _, _, _, _, hpresNum, _⟩
                        · rw [hretRun] at hSt'; cases hSt'
                        · rw [hretRun] at hOOF'; cases hOOF'
                        · rw [hretRun] at hrun'; cases hrun'
                          have hlt3 : l < st₃.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho3).1
                          have hnotOwn : ¬ OwnReach P st₃.heap rv_b l := fun hor =>
                            OwnReach_not_numLoc hor ⟨o3, n3, ho3, hc3⟩
                          have hpL := hpresNum l ⟨hlt3, fun _ => hnotOwn⟩
                          exact Or.inr (Or.inr (Or.inr ⟨o3, n3, hpL.trans ho3, hc3⟩))
                      · obtain ⟨_, _, _, _, _, _, _, hvdR, _, _, hnotOnceR, hvalInfo, _⟩ := Runs_retCheck hok₁ hretChk
                        have haR : ActiveVal σ₁ r_a := ⟨hvdR, fun his => absurd his hnotOnceR⟩
                        have hnotForb : ¬ Forbid l := by
                          apply hnrfR haR _ (fun _ _ h => False.elim h) l hrB hss3 hnum3
                          dsimp only [BadReg]
                          cases hrb : res.isBorrowed with
                          | true => intro _ _ h; exact h
                          | false =>
                            intro rg hrgIn hEq2; subst hEq2
                            have hsu : res = .shared ∨ res = .unique := by
                              cases res <;> simp [ResultMode.isBorrowed] at hrb ⊢
                            exact (hvalInfo rfl).1 hsu hrgIn
                        by_cases hss0 : StaticStrLoc st l
                        · exact Or.inr (Or.inr (Or.inl hss0))
                        · right; left
                          dsimp only [Forbid] at hnotForb
                          cases hrb : res.isBorrowed with
                          | true =>
                            rw [hrb] at hnotForb; dsimp only [ForbidAll] at hnotForb
                            have hEx : ∃ (i : Nat) (p : Param) (v : Val), params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧ Reach st.heap v l :=
                              Classical.byContradiction fun hno => hnotForb ⟨hlt0, hss0, fun i p v hp hv hne hr => hno ⟨i, p, v, hp, hv, hne, hr⟩⟩
                            obtain ⟨i, p, v, hp, hv, hne, hr⟩ := hEx
                            exact ⟨i, p, v, hp, hv, hne, Or.inl rfl, hr⟩
                          | false =>
                            rw [hrb] at hnotForb; dsimp only [ForbidNB] at hnotForb
                            have hEx : ∃ (i : Nat) (p : Param) (v : Val), params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧ p.mode.isBorrowed = false ∧ Reach st.heap v l :=
                              Classical.byContradiction fun hno => hnotForb ⟨hlt0, hss0, fun i p v hp hv hne hnb hr => hno ⟨i, p, v, hp, hv, hne, hnb, hr⟩⟩
                            obtain ⟨i, p, v, hp, hv, hne, hnb, hr⟩ := hEx
                            exact ⟨i, p, v, hp, hv, hne, Or.inr hnb, hr⟩
                · rcases hnv' hrcV with ⟨_, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hc⟩
                  · cases hl
                  · rcases hl with _ | ⟨ho', hmem, _⟩
                    · exact Or.inr (Or.inr (Or.inr ⟨o, n, ho, hc⟩))
                    · rw [ho] at ho'; cases ho'; rw [hc] at hmem; cases hmem
            have hstat02 : ArrayExtends st.statics st₂.statics := by rw [hstat₂]; exact ArrayExtends.refl _
            have hstr02 : ArrayExtends st.strs st₂.strs := by rw [hstr₂]; exact ArrayExtends.refl _
            have hstat3r : ArrayExtends st₃.statics st'.statics := by dsimp only [st']; rw [hstat_ret]; exact ArrayExtends.refl _
            have hstr3r : ArrayExtends st₃.strs st'.strs := by dsimp only [st']; rw [hstr_ret]; exact ArrayExtends.refl _
            refine ⟨by omega, hst'Ok,
              Nat.le_trans hsz₂ (Nat.le_trans hsz₃ hsz_ret),
              Nat.le_trans hcap₂ (Nat.le_trans hcap₃ hcap_ret),
              hst'Regs,
              Nat.le_trans (by omega) (Nat.le_trans hnr₃ (hnr_ret ▸ Nat.le_refl _)),
              (hstat02.trans hstat₃).trans hstat3r,
              (hstr02.trans hstr₃).trans hstr3r,
              hpFrame₂.trans (hpFrame₃.trans (hpFrame_ret.mono fun _ h => Or.inl h)),
              honce₂.trans (honce₃.trans honce_ret),
              hssfFinal,
              ValBaseOk_congr (PreservesLocs.refl _ _) (Nat.le_refl _) hbv',
              hcls', hno',
              CtorFieldsOk_congr hbv'.1 (PreservesLocs.refl _ _) hrfClose hcf',
              FunOkAt_preserve_locs (st₀ := st_ret) (PreservesLocs.refl _ _) hrfClose hfunExp',
              hopenFinal, hreachFinal, ?_⟩
            intro hu
            obtain ⟨hot, hor⟩ := huniqRet hu
            exact ⟨hot, fun l h => ⟨fun hF => (hor l h).1 (Or.inl hF), (hor l h).2⟩⟩

theorem staticS_checked_sound {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {r : Ref} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term} {st : St}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    (hb : b ≤ B + 1)
    (hfind : P.find? r = some (.body #[] res rc rs body))
    (hlc : LamsClosed body) (hcfd : CaseFieldsDistinct body)
    (hbody : BodyOk P #[] res rc rs body)
    (hst : StOk P ext b st) :
    (∀ k, (staticS P ext fuel r body rc).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (staticS P ext fuel r body rc).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        ValBaseOk st' rv ∧
        ClsSafe st'.heap rc rv ∧
        DeepOpenUnder st'.heap st'.regions [] rv ∧
        NoOnceCell st'.heap rv ∧
        CtorFieldsOk P ext B' st' rv ∧
        FunOkAt P ext B' st' rs false (fun _ => False) rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
  obtain ⟨hresOr, r_a, σ₁, σ₂, hder, hretChk⟩ := hbody
  have hresEq : res = .shared := hresOr.resolve_left (by simp)
  subst hresEq
  cases fuel with
  | zero =>
    cases b with
    | zero =>
      have h0 : (staticS P ext 0 r body rc).run (st, 0) = .error .outOfFuel := by
        unfold staticS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b0 =>
      have h0 : (staticS P ext 0 r body rc).run (st, b0 + 1) = .error .outOfFuel := by
        unfold staticS; rw [MS_bind_run, MS_spend_succ]; rfl
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | succ n =>
    cases b with
    | zero =>
      have h0 : (staticS P ext (n + 1) r body rc).run (st, 0) = .error .outOfFuel := by
        unfold staticS; rw [MS_bind_run, MS_spend_zero]
      rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ b0 =>
      have hb0B : b0 ≤ B := Nat.le_of_succ_le_succ hb
      have hunfold : (staticS P ext (n + 1) r body rc).run (st, b0 + 1) =
          (match st.statics.find? (·.1 == r) with
           | some (_, v) =>
             match (live v).run st with
             | .error e => .error e
             | .ok ((), st₁) => .ok (v, (st₁, b0))
           | none =>
             match (evalS P ext n [] body).run (st, b0) with
             | .error e => .error e
             | .ok (v0, (st₁, B₁)) =>
               match (conform rc v0).run st₁ with
               | .error e => .error e
               | .ok (v, st₂) => .ok (v, ({ st₂ with statics := st₂.statics.push (r, v) }, B₁))) := by
        unfold staticS; rw [MS_bind_run, MS_spend_succ]; dsimp only
        rw [MS_bind_run, MS_liftM_run]
        have hget : (get : M St).run st = .ok (st, st) := rfl
        rw [hget]; dsimp only
        cases st.statics.find? (·.1 == r) with
        | some p =>
          rcases p with ⟨r', v⟩; dsimp only
          rw [MS_liftM_run, M_bind_run]
          cases (live v).run st with
          | error _ => rfl
          | ok pl => rcases pl with ⟨⟨⟩, st₁⟩; rfl
        | none =>
          dsimp only; rw [MS_bind_run]
          cases (evalS P ext n [] body).run (st, b0) with
          | error _ => rfl
          | ok p1 =>
            rcases p1 with ⟨v0, ⟨st₁, B₁⟩⟩; dsimp only
            rw [MS_bind_run, MS_liftM_run]
            cases (conform rc v0).run st₁ with
            | error _ => rfl
            | ok p2 =>
              rcases p2 with ⟨v, st₂⟩; dsimp only
              rw [MS_bind_run, MS_liftM_run]
              have hmod : (modify fun s : St => { s with statics := s.statics.push (r, v) } : M Unit).run st₂ =
                  .ok ((), { st₂ with statics := st₂.statics.push (r, v) }) := rfl
              rw [hmod]; rfl
      rw [hunfold]
      cases hcache : st.statics.find? (·.1 == r) with
      | some p =>
        rcases p with ⟨r', v⟩
        have hmem : (r', v) ∈ st.statics.toList :=
          Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hcache)
        have hreq : r' = r := beq_iff_eq.mp (Array.find?_some (p := fun x : Ref × Val => x.1 == r) hcache)
        subst hreq
        obtain ⟨rc', rs', body', hfind', hbaseV, hclsV, hopenV, hnoV, hfunV, hcfV⟩ :=
          hst.2.2.1 r' v hmem
        rw [hfind] at hfind'; cases hfind'
        dsimp only
        rw [live_ok hbaseV.1.self.1]
        refine ⟨(fun _ h => by cases h), fun rv st' B' hok => ?_⟩
        cases hok
        exact ⟨(DefStep.refl (StOk_mono (Nat.le_succ b0) hst)).dec_in (Nat.le_succ b0),
          hbaseV, hclsV, hopenV, hnoV,
          CtorFieldsOk_mono (Nat.le_succ b0) hcfV,
          FunOkAt_mono (Nat.le_succ b0) hfunV,
          fun l hl => Or.inr (Or.inl (Or.inl ⟨r', v, hmem, hl⟩))⟩
      | none =>
        have hst0 : StOk P ext b0 st := StOk_mono (Nat.le_succ b0) hst
        let σ₀ : AState := { regions := [2, 1], nextRegion := 3 }
        let I : Interp := ⟨fun rg => if rg == 2 then st.regions else []⟩
        have hok₀ : AStateOk σ₀ :=
          ⟨rfl, rfl, by decide, by decide, by decide, fun rg hrg => by simp [σ₀] at hrg; rcases hrg with rfl | rfl <;> decide⟩
        have hIok₀ : InterpOk σ₀ st I := by
          refine ⟨fun rg _ c hc => ?_, fun c hc => ?_⟩
          · dsimp only [I] at hc
            by_cases h2 : (rg == 2) = true
            · rw [h2] at hc; exact (hst.2.1.2.2 c hc).2
            · simp [h2] at hc
          · dsimp only [σ₀, I]
            cases hr : st.regions with
            | nil => rw [hr] at hc; cases hc
            | cons c0 rest => rw [hr] at hc; cases hc; exact List.mem_cons_self
        have hsim₀ : Sim P ext b0 st (fun l => l < st.heap.objs.size) (fun _ => False) (fun _ => False) (fun _ => True)
            [] [] σ₀ I (fun _ _ => False) :=
          ⟨rfl, hok₀, hIok₀, (fun _ _ h => by simp at h), (fun _ _ _ _ h => by simp at h),
           (fun _ _ _ _ h => by simp at h), (fun _ _ _ _ _ _ _ _ _ h => by simp at h)⟩
        have hIZero₀ : ∀ rg, σ₀.nextRegion ≤ rg → I.reg rg = [] := fun rg hge => by
          dsimp only [σ₀] at hge; dsimp only [I]
          have hne2 : (rg == 2) = false := beq_false_of_ne (by omega)
          simp [hne2]
        have hHeadReg₀ : st.regions.headD 0 = 0 ∨ st.regions.headD 0 ∈ I.reg (σ₀.regions.headD 1) := by
          cases hr : st.regions with
          | nil => exact Or.inl rfl
          | cons c rest => right; dsimp only [σ₀, I]; simp [hr]
        let Forbid : Nat → Prop := fun l => l < st.heap.objs.size ∧ ¬ StaticStrLoc st l
        have hder' : ATerm P [] body σ₀ r_a σ₁ := hder
        obtain ⟨hok₁, _, _⟩ := ATerm_state_le hok₀ hder'
        obtain ⟨hnoVE, hokE⟩ := evalS_checked_sound hidx hext hih hder' hlc hcfd (B₀ := b0) (fuel := n)
          (Forbid := Forbid) (BadReg := (· = 2)) (BadDep := (fun _ => False))
          (by omega) (fun _ _ => trivial) hst0 hsim₀
          (fun _ hss => StOk_staticStrLoc_lt hst hss) (fun _ h => h)
          (fun _ h => False.elim h) (fun _ h => False.elim h)
          hIZero₀ hHeadReg₀
          (fun _ _ _ _ h => by simp at h)
          (fun _ _ _ _ h => by simp at h)
          (fun _ hF => hF.1) (fun _ h => False.elim h)
        cases hev : (evalS P ext n [] body).run (st, b0) with
        | error e =>
          refine ⟨(fun k hk => by cases hk; exact hnoVE k hev), (fun _ _ _ h => by cases h)⟩
        | ok pe =>
          rcases pe with ⟨v0, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨_, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
            hpOld₁, _, hpNum₁, honce₁, hssf₁, _, _, _,
            hv0, _, hnrf0, _, _, _, _⟩ := hokE v0 st₁ B₁ hev
          obtain ⟨_, _, _, _, _, _, _, hvdR, hadmR, hooR, hnotOnceR, hvalInfo, _⟩ :=
            Runs_retCheck hok₁ hretChk
          have haR : ActiveVal σ₁ r_a := ⟨hvdR, fun his => absurd his hnotOnceR⟩
          obtain ⟨hbv0, hdou0, hcf0, _, hplain0, _, _, _⟩ := hv0.2.2.2.2 haR
          obtain ⟨hno0, _, hfun0⟩ := hplain0 ⟨hnotOnceR, hooR⟩
          rcases conform_spec_full (P := P) hst₁.1 hbv0.1 hbv0.2.1 with hSt |
            ⟨v, st₂, hconfRun, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, hcaps₂,
             hdl₂, hclsOk₂, hacyc₂, htaintSub₂, hreach₂, _, _, hdou₂⟩
          · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hconfRun]; dsimp only
            have hrf₁₂ : RegsFuture st₁ st₂ := RegsFuture.same_regions (hnr₂ ▸ Nat.le_refl _) hrg₂
            have hst₂Ok : StOk P ext B₁ st₂ :=
              StOk_of_preserves_old hst₁ hcaps₂ hrg₂ (hnr₂ ▸ Nat.le_refl _) hstat₂ hstr₂ hpres₂
            have honce₂ : PreservesOnceShell st₁.heap st₂.heap :=
              PreservesOnceShell.of_preservesLocs (hpres₂.mono fun _ ⟨_, _, _, ho, _⟩ => (Array.getElem?_eq_some_iff.mp ho).1)
            have hssf₁₂ : StaticStrFresh st₁ st₂ :=
              StaticStrFresh_of_preserves_outside (S := fun _ => False) hst₁ hstat₂ hstr₂ (hpres₂.mono fun _ h => h.1) (fun _ _ h => h)
            have hbv₂ : ValBaseOk st₂ v := by
              by_cases hrcV : rc = .val
              · subst hrcV
                have hvEq : v = v0 ∧ st₂ = st₁ := by
                  have : (conform .val v0).run st₁ = .ok (v0, st₁) := rfl
                  rw [this] at hconfRun; cases hconfRun; exact ⟨rfl, rfl⟩
                rw [hvEq.1, hvEq.2]; exact hbv0
              · cases rc with
                | val => exact absurd rfl hrcV
                | irr => rw [hclsOk₂]; exact ValBaseOk_imm st₂ .irr
                | imm => obtain ⟨imm, rfl⟩ := hclsOk₂; exact ValBaseOk_imm st₂ imm
                | leaf =>
                  obtain ⟨loc, cap, o, num, rfl, ho, hnum, _⟩ := hclsOk₂
                  exact ValBaseOk_of_deepLive hdl₂ hacyc₂ (DeepTaintsBounded_num ho hnum)
            have hcls₂ : ClsSafe st₂.heap rc v := ClsSafe.of_clsOk hclsOk₂
            have hopen₂ : DeepOpenUnder st₂.heap st₂.regions [] v := by
              by_cases hrcV : rc = .val
              · subst hrcV
                have hnot2 : 2 ∉ r_a.regs := (hvalInfo rfl).1 (Or.inl rfl)
                have hIempty : I.regsOf r_a.regs = [] := by
                  have hgo : ∀ xs : List Nat, 2 ∉ xs → I.regsOf xs = [] := by
                    intro xs hxs
                    induction xs with
                    | nil => rfl
                    | cons x rest ih =>
                      have hxNe : x ≠ 2 := fun h => hxs (h ▸ List.mem_cons_self)
                      have hrest : 2 ∉ rest := fun h => hxs (List.mem_cons_of_mem _ h)
                      dsimp only [Interp.regsOf]
                      rw [List.flatMap_cons, show I.reg x = [] by dsimp only [I]; simp [beq_false_of_ne hxNe], List.nil_append]
                      exact ih hrest
                  exact hgo r_a.regs hnot2
                rw [hIempty] at hdou0
                rw [hrg₂]; exact hdou₂ st₁.regions [] hdou0
              · exact (NonValSafe_of_clsSafe_ne_val hbv₂ hcls₂ hrcV).deepOpenUnder_nil
            have hno₂ : NoOnceCell st₂.heap v := by
              by_cases hrcV : rc = .val
              · subst hrcV
                have hvEq : v = v0 ∧ st₂ = st₁ := by
                  have : (conform .val v0).run st₁ = .ok (v0, st₁) := rfl
                  rw [this] at hconfRun; cases hconfRun; exact ⟨rfl, rfl⟩
                rw [hvEq.1, hvEq.2]; exact hno0
              · exact (NonValSafe_of_clsSafe_ne_val hbv₂ hcls₂ hrcV).noOnceCell
            have hcf₂ : CtorFieldsOk P ext B₁ st₂ v := by
              by_cases hrcV : rc = .val
              · subst hrcV
                have hvEq : v = v0 ∧ st₂ = st₁ := by
                  have : (conform .val v0).run st₁ = .ok (v0, st₁) := rfl
                  rw [this] at hconfRun; cases hconfRun; exact ⟨rfl, rfl⟩
                rw [hvEq.1, hvEq.2]; exact hcf0
              · exact (NonValSafe_of_clsSafe_ne_val hbv₂ hcls₂ hrcV).ctorFieldsOk P ext B₁ st₂
            have hfun₂ : FunOkAt P ext B₁ st₂ rs false (fun _ => False) v := by
              have hadmSym : r_a.skel.admits rs = true := by rw [Skel.admits_symm]; exact hadmR
              by_cases hrcV : rc = .val
              · subst hrcV
                have hvEq : v = v0 ∧ st₂ = st₁ := by
                  have : (conform .val v0).run st₁ = .ok (v0, st₁) := rfl
                  rw [this] at hconfRun; cases hconfRun; exact ⟨rfl, rfl⟩
                rw [hvEq.1, hvEq.2]; exact FunOkAt_of_admits hadmSym hfun0
              · exact (NonValSafe_of_clsSafe_ne_val hbv₂ hcls₂ hrcV).funOkAt P ext B₁ st₂ rs
            have hreachV : ∀ l, Reach st₂.heap v l →
                st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st₂.heap l := by
              intro l hl
              by_cases hrcV : rc = .val
              · subst hrcV
                have hvEq : v = v0 ∧ st₂ = st₁ := by
                  have : (conform .val v0).run st₁ = .ok (v0, st₁) := rfl
                  rw [this] at hconfRun; cases hconfRun; exact ⟨rfl, rfl⟩
                rw [hvEq.1] at hl; rw [hvEq.2] at hl ⊢
                by_cases hge0 : st.heap.objs.size ≤ l
                · exact Or.inl hge0
                · by_cases hss1 : StaticStrLoc st₁ l
                  · exact hssf₁ l hss1
                  · by_cases hnum1 : NumLoc st₁.heap l
                    · exact Or.inr (Or.inr hnum1)
                    · by_cases hss0 : StaticStrLoc st l
                      · exact Or.inr (Or.inl hss0)
                      · exfalso
                        have hnot2 : 2 ∉ r_a.regs := (hvalInfo rfl).1 (Or.inl rfl)
                        exact hnrf0 haR (fun rg hrg hEq => hnot2 (hEq ▸ hrg)) (fun _ _ h => False.elim h)
                          l hl hss1 hnum1 ⟨Nat.lt_of_not_ge hge0, hss0⟩
              · rcases NonValSafe_of_clsSafe_ne_val hbv₂ hcls₂ hrcV with ⟨_, rfl⟩ | ⟨loc, cap, o, num, rfl, ho, _, hc⟩
                · cases hl
                · rcases hl with _ | ⟨ho', hm, _⟩
                  · exact Or.inr (Or.inr ⟨o, num, ho, hc⟩)
                  · rw [ho] at ho'; cases ho'; rw [hc] at hm; cases hm
            let st' : St := { st₂ with statics := st₂.statics.push (r, v) }
            have hst'Ok : StOk P ext B₁ st' :=
              StOk_pushStatic hst₂Ok hfind hbv₂ hcls₂ hopen₂ hno₂ hfun₂ hcf₂
            have hssf02 : StaticStrFresh st st₂ :=
              StaticStrFresh.trans hsz₁ (hpres₂.mono fun _ hss => StOk_staticStrLoc_lt hst₁ hss) hssf₁ hssf₁₂
            have hssf' : StaticStrFresh st st' := by
              intro l hl
              rcases hl with ⟨r0, v0', hm, hr⟩ | ⟨s0, v0', hm, hr⟩
              · rw [show st'.statics.toList = st₂.statics.toList ++ [(r, v)] by
                    simp [st', Array.toList_push]] at hm
                rcases List.mem_append.mp hm with hmOld | hmNew
                · exact hssf02 l (Or.inl ⟨r0, v0', hmOld, hr⟩)
                · simp only [List.mem_singleton, Prod.mk.injEq] at hmNew
                  obtain ⟨_, rfl⟩ := hmNew
                  exact hreachV l hr
              · exact hssf02 l (Or.inr ⟨s0, v0', hm, hr⟩)
            have hrfSt : RegsFuture st₂ st' := RegsFuture.same_regions (Nat.le_refl _) rfl
            have hstep' : DefStep P ext (b0 + 1) B₁ st st' :=
              ⟨Nat.le_trans hB₁ (Nat.le_succ b0), hst'Ok,
               Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
               hrg₂.trans hr₁, Nat.le_trans hnr₁ (hnr₂ ▸ Nat.le_refl _),
               (hstat₁.trans (hstat₂ ▸ ArrayExtends.refl _)).trans (ArrayExtends.push st₂.statics (r, v)),
               hstr₁.trans (hstr₂ ▸ ArrayExtends.refl _),
               hpOld₁.trans (hpres₂.mono fun l hl => Nat.lt_of_lt_of_le hl hsz₁),
               honce₁.trans honce₂, hssf'⟩
            refine ⟨(fun _ h => by cases h), fun rv st'' B' hok => ?_⟩
            cases hok
            exact ⟨hstep', hbv₂, hcls₂, hopen₂, hno₂,
              CtorFieldsOk_congr hbv₂.1 (PreservesLocs.refl _ _) hrfSt hcf₂,
              FunOkAt_preserve_locs (st₀ := st₂) (PreservesLocs.refl _ _) hrfSt hfun₂,
              hreachV⟩

/-! ## 3. Default Body Adapters into `FullIH` -/

theorem enterS_default_to_FullIH {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {params : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term}
    {vs : List Val} {st : St} {Frame : Nat → Prop} {argRegs : List Nat}
    {argOnce : Nat → Bool} {argFoot : Nat → Nat → Prop}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    (hb : b ≤ B + 1)
    (hlc : LamsClosed body)
    (hdef : DefaultBodyOk P params res rs body)
    (hlen : vs.length = params.size)
    (hst : StOk P ext b st)
    (hFlt : ∀ l, Frame l → l < st.heap.objs.size)
    (hargs : ∀ (i : Nat) (p : Param) (v : Val), params[i]? = some p → vs[i]? = some v →
      (p.mode ≠ .erased →
        ValBaseOk st v ∧
        DeepOpenUnder st.heap st.regions argRegs v ∧
        CtorFieldsOk P ext b st v ∧
        (p.mode.usage = .once →
          FunOkAt P ext b st p.skel (argOnce i) (argFoot i) v ∧
          (∀ l, argFoot i l → Reach st.heap v l ∧ ¬ Frame l ∧ ¬ NumLoc st.heap l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st.heap v ∧ argOnce i = false ∧ (∀ l, ¬ argFoot i l) ∧
          FunOkAt P ext b st p.skel false (fun _ => False) v) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st.heap v ∧
          (∀ l, OwnReach P st.heap v l → ¬ Frame l) ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v)))) :
    (∀ k, (enterS P ext fuel params res rc body vs).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (enterS P ext fuel params res rc body vs).run (st, b) = .ok (rv, (st', B')) →
        B' ≤ b ∧
        StOk P ext B' st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧
        st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧
        ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesOnceShell st.heap st'.heap ∧
        StaticStrFresh st st' ∧
        ValBaseOk st' rv ∧
        ClsSafe st'.heap rc rv ∧
        NoOnceCell st'.heap rv ∧
        CtorFieldsOk P ext B' st' rv ∧
        FunOkAt P ext B' st' rs false (fun _ => False) rv ∧
        DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc [] argRegs) rv ∧
        (∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨
          (∃ (i : Nat) (p : Param) (v : Val),
            params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧
            (res.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧
            Reach st.heap v l) ∨
          StaticStrLoc st l ∨
          NumLoc st'.heap l) ∧
        (res.isUnique = true ∧ rc = .val →
          OwnTreeFull P st'.heap rv ∧
          ∀ l, OwnReach P st'.heap rv l → ¬ Frame l ∧ ¬ StaticStrLoc st' l) := by
  have ⟨hpmSk, hresEq, hrsDef, _⟩ := hdef
  have hvsDef : ∀ v ∈ vs, DefValOk P ext b st argRegs v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hiP : i < params.size := hlen ▸ hi
    have hp : params[i]? = some params[i] := Array.getElem?_eq_getElem hiP
    have hvi : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
    obtain ⟨hpm, hpsk⟩ := hpmSk params[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hiP))
    have hne : params[i].mode ≠ .erased := by rw [hpm]; decide
    have hnu : params[i].mode.usage ≠ .once := by rw [hpm]; decide
    obtain ⟨hbv, hopen, hcf, _, hnoF, _⟩ := hargs i params[i] vs[i] hp hvi hne
    obtain ⟨hno, _, _, hfun⟩ := hnoF hnu
    exact ⟨hbv, hopen, hno, hcf, (FunOkAt_default_equiv hpsk rfl).mp hfun⟩
  obtain ⟨hnoV, hok⟩ := enterS_default_sound hidx hext hih.to_DefaultCallIH hb hdef hlc hst hvsDef
  refine ⟨hnoV, fun rv st' B' hrun => ?_⟩
  obtain ⟨hstep, hcls, hdv, hreach⟩ := hok rv st' B' hrun
  have hopenR : DeepOpenUnder st'.heap st'.regions (applyResultRegs st res rc [] argRegs) rv := by
    by_cases hrcV : rc = .val
    · subst hrcV; rw [hresEq]
      simp only [applyResultRegs, List.append_nil]
      exact hdv.2.1
    · exact (NonValSafe_of_clsSafe_ne_val hdv.1 hcls hrcV).deepOpenUnder_nil
  have hreachR : ∀ l, Reach st'.heap rv l →
      st.heap.objs.size ≤ l ∨
      (∃ (i : Nat) (p : Param) (v : Val),
        params[i]? = some p ∧ vs[i]? = some v ∧ p.mode ≠ .erased ∧
        (res.isBorrowed = true ∨ p.mode.isBorrowed = false) ∧
        Reach st.heap v l) ∨
      StaticStrLoc st l ∨
      NumLoc st'.heap l := by
    intro l hl
    rcases hreach l hl with hge | ⟨v, hv, hrv⟩ | hss | hnum
    · exact Or.inl hge
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      have hiP : i < params.size := hlen ▸ hi
      have hpm := (hpmSk params[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hiP))).1
      exact Or.inr (Or.inl ⟨i, params[i], vs[i], Array.getElem?_eq_getElem hiP, List.getElem?_eq_getElem hi,
        by rw [hpm]; decide, Or.inr (by rw [hpm]; rfl), hrv⟩)
    · exact Or.inr (Or.inr (Or.inl hss))
    · exact Or.inr (Or.inr (Or.inr hnum))
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2.1,
    hstep.2.2.2.2.2.2.1, hstep.2.2.2.2.2.2.2.1, hstep.preserves_old.mono hFlt,
    hstep.2.2.2.2.2.2.2.2.2.1, hstep.staticStrFresh,
    hdv.1, hcls, hdv.2.2.1, hdv.2.2.2.1,
    (FunOkAt_default_equiv rfl hrsDef).mp hdv.2.2.2.2,
    hopenR, hreachR, fun ⟨hu, _⟩ => by rw [hresEq] at hu; cases hu⟩

theorem staticS_default_to_FullIH {P : Prog} {ext : ExternOracle} {B b fuel : Nat}
    {r : Ref} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term} {st : St}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    (hb : b ≤ B + 1)
    (hfind : P.find? r = some (.body #[] res rc rs body))
    (hlc : LamsClosed body)
    (hdef : DefaultBodyOk P #[] res rs body)
    (hst : StOk P ext b st) :
    (∀ k, (staticS P ext fuel r body rc).run (st, b) ≠ .error (.violation k)) ∧
    ∀ rv st' B',
      (staticS P ext fuel r body rc).run (st, b) = .ok (rv, (st', B')) →
        DefStep P ext b B' st st' ∧
        ValBaseOk st' rv ∧
        ClsSafe st'.heap rc rv ∧
        DeepOpenUnder st'.heap st'.regions [] rv ∧
        NoOnceCell st'.heap rv ∧
        CtorFieldsOk P ext B' st' rv ∧
        FunOkAt P ext B' st' rs false (fun _ => False) rv ∧
        ∀ l, Reach st'.heap rv l →
          st.heap.objs.size ≤ l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l := by
  obtain ⟨hnoV, hok⟩ := staticS_default_sound hidx hext hih.to_DefaultCallIH hb hfind hdef hlc hst
  refine ⟨hnoV, fun rv st' B' hrun => ?_⟩
  obtain ⟨hstep, hcls, hdv, hreach⟩ := hok rv st' B' hrun
  exact ⟨hstep, hdv.1, hcls, hdv.2.1, hdv.2.2.1, hdv.2.2.2.1,
    (FunOkAt_default_equiv rfl hdef.2.2.1).mp hdv.2.2.2.2, hreach⟩

/-! ## 4. Outer Budget Induction and Main Theorem `f4` -/

theorem fullIH_zero (P : Prog) (ext : ExternOracle) : FullIH P ext 0 := by
  refine ⟨fun b hb => ?_, fun b fuel r params res rc rs body vs st Frame argRegs argOnce argFoot hb => ?_,
    fun b fuel r res rc rs body st hb => ?_⟩
  · have hb0 : b = 0 := Nat.eq_zero_of_le_zero hb; subst hb0
    intro _ _ _ _ _ _ _ _ _ _ _; rw [FunOkAt]; trivial
  · have hb0 : b = 0 := Nat.eq_zero_of_le_zero hb; subst hb0
    intro _ _ _ _ _ _ _
    have h0 : (enterS P ext fuel params res rc body vs).run (st, 0) = .error .outOfFuel := by
      cases fuel <;> (unfold enterS; rw [MS_bind_run, MS_spend_zero])
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  · have hb0 : b = 0 := Nat.eq_zero_of_le_zero hb; subst hb0
    intro _ _
    have h0 : (staticS P ext fuel r body rc).run (st, 0) = .error .outOfFuel := by
      cases fuel <;> (unfold staticS; rw [MS_bind_run, MS_spend_zero])
    rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩

theorem fullIH_step {P : Prog} {ext : ExternOracle} {B : Nat}
    (hmode : ModeOk P) (hext : ExternOk P ext) (hih : FullIH P ext B) :
    FullIH P ext (B + 1) := by
  refine ⟨fun b hb => ?_, ?_, ?_⟩
  · by_cases hle : b ≤ B
    · exact hih.1 b hle
    · have hEq : b = B + 1 := by omega
      subst hEq; exact FullIH_to_PapsFunOk hext hih
  · intro b fuel r params res rc rs body vs st Frame argRegs argOnce argFoot hb hfind
      hlen hst hstat hFlt hargs hdisj
    obtain ⟨hlc, hcfd, hbd⟩ := hmode.2 r params res rc rs body hfind
    rcases hbd with hchk | hdef
    · exact enterS_checked_sound hmode.1 hext hih hb hlc hcfd hchk hlen hst hstat hFlt hargs hdisj
    · exact enterS_default_to_FullIH hmode.1 hext hih hb hlc hdef hlen hst hFlt hargs
  · intro b fuel r res rc rs body st hb hfind hst
    obtain ⟨hlc, hcfd, hbd⟩ := hmode.2 r #[] res rc rs body hfind
    rcases hbd with hchk | hdef
    · exact staticS_checked_sound hmode.1 hext hih hb hfind hlc hcfd hchk hst
    · exact staticS_default_to_FullIH hmode.1 hext hih hb hfind hlc hdef hst

theorem fullIH_all {P : Prog} {ext : ExternOracle}
    (hmode : ModeOk P) (hext : ExternOk P ext) : ∀ B, FullIH P ext B
  | 0 => fullIH_zero P ext
  | B + 1 => fullIH_step hmode hext (fullIH_all hmode hext B)

/-- **F4 (`ModeOk P → Safe P`)**: any run program with a step-free `ModeOk` certificate
never hits a mode violation from admissible inputs under any compliant extern oracle. -/
theorem f4 : ∀ P, ModeOk P → Safe P := by
  intro P hmode r params res rc rs body hfind ext hext h args hinp fuel k hviol
  unfold runR at hviol
  rw [hfind] at hviol
  have hlenF : (args.length != params.size) = false := by
    simp [hinp.1]
  simp only [hlenF, Bool.false_eq_true, ↓reduceIte] at hviol
  have hentViol : (enter P ext fuel params res rc body args).run { heap := h } = .error (.violation k) := by
    cases hrun : (enter P ext fuel params res rc body args).run { heap := h } with
    | ok _ => rw [hrun] at hviol; cases hviol
    | error e =>
      rw [hrun] at hviol
      cases e with
      | stuck => cases hviol
      | outOfFuel => cases hviol
      | violation k' => cases hviol; rfl
  obtain ⟨B, hB⟩ := enter_violation_to_enterS hentViol
  have hih := fullIH_all hmode hext B
  obtain ⟨hstOk, hlen, hargInfo⟩ := InputsOk_to_StOk_and_Args hinp (hih.1 B (Nat.le_refl B))
  let st : St := { heap := h }
  have hstatEmpty : ∀ l, StaticStrLoc st l → False := by
    intro l hss
    rcases hss with ⟨_, _, hm, _⟩ | ⟨_, _, hm, _⟩ <;> simp [st] at hm
  have hargsBody : ∀ (i : Nat) (p : Param) (v : Val), params[i]? = some p → args[i]? = some v →
      (p.mode ≠ .erased →
        ValBaseOk st v ∧
        DeepOpenUnder st.heap st.regions [] v ∧
        CtorFieldsOk P ext B st v ∧
        (p.mode.usage = .once →
          FunOkAt P ext B st p.skel false (fun _ => False) v ∧
          (∀ l, False → Reach st.heap v l ∧ ¬ False ∧ ¬ NumLoc st.heap l)) ∧
        (p.mode.usage ≠ .once →
          NoOnceCell st.heap v ∧ false = false ∧ (∀ l : Nat, ¬ False) ∧
          FunOkAt P ext B st p.skel false (fun _ => False) v) ∧
        (p.mode.isUnique = true →
          OwnTreeFull P st.heap v ∧
          (∀ l, OwnReach P st.heap v l → ¬ False) ∧
          (p.mode.isBorrowed = false → DeepOpenUnder st.heap st.regions [] v))) := by
    intro i p v hp hv hne
    obtain ⟨hbv, hopen, hno, _, hner, huniq⟩ := hargInfo i p v hp hv
    obtain ⟨_, hcf, hfun⟩ := hner hne
    exact ⟨hbv, hopen, hcf,
      (fun _ => ⟨hfun, fun _ h => False.elim h⟩),
      (fun _ => ⟨hno, rfl, fun _ h => h, hfun⟩),
      (fun hu => ⟨(huniq hu).1, fun _ _ h => h, fun _ => hopen⟩)⟩
  have hdisjBody : ∀ (i j : Nat) (pi pj : Param) (vi vj : Val), i ≠ j →
      params[i]? = some pi → args[i]? = some vi →
      params[j]? = some pj → args[j]? = some vj →
      pj.mode ≠ .erased →
      (pi.mode.isUnique = true → ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) ∧
      (pi.mode.usage = .once → ∀ l, False → ¬ Reach st.heap vj l) ∧
      (pi.mode.usage = .once → pj.mode.usage = .once → ∀ l : Nat, False → ¬ False) := by
    intro i j pi pj vi vj hij hpi hvi hpj hvj _
    obtain ⟨_, _, _, _, _, huniq⟩ := hargInfo i pi vi hpi hvi
    exact ⟨fun hu l hor => (huniq hu).2 j vj l hij.symm hvj hor,
      (fun _ _ h => False.elim h), (fun _ _ _ h => False.elim h)⟩
  exact (hih.2.1 B fuel r params res rc rs body args st (fun _ => False) [] (fun _ => false)
    (fun _ _ => False) (Nat.le_refl B) hfind hlen hstOk hstatEmpty (fun _ h => False.elim h)
    hargsBody hdisjBody).1 k hB

end IxC.Resource.Proof
