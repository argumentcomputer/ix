import IxC.Resource.Proof.F4CallBridge
import IxC.Resource.Proof.F4OpsBridge

/-!
# Checked-Body Evaluation Soundness (`F4Eval`)

Proves the main mutual structural soundness theorem for checked `ATerm` / `AAlts` / `AEvals` /
`ACallArgs` / `ACall` / `AMajor` / `AAlt` derivations against `EvalS` (`evalS`, `evalListS`,
`evalCallArgsS`, `callWithS`, `applyAltS`) at any budget `B_call ≤ B + 1` given `FullIH P ext B`.

Key design points:
1. **Invariant `Interp` (`I`)**: carrying `hIZero : ∀ r, σ.nextRegion ≤ r → I.reg r = []` keeps
   the **exact same `I`** across every term step, making `ArgListOk_push` compose with zero
   adapters and giving `RegUnique (I.extend s_a s_c) σ_body s_a s_c` in 4 lines.
2. **Taint safety for spent `@once` bindings (`EnvTaintOk`)**: tracks
   `(∀ c ∈ b.val.taint, c < st.nextRegion) ∧ OpenUnder st.regions (I.regsOf (effVal ab).regs) b.val`
   for every non-erased binding in scope (even after `@once` spending), guaranteeing
   `confinedTo s_c rv = false` at `ATerm.letVal` exit without changing `VSim`/`Sim`.
3. **Pure static monotonicity (`ATerm_state_le`)**: proves `AStateOk σ' ∧ AStateLe σ σ' ∧
   σ'.regions = σ.regions` ahead of time so `NoKillOk`/`NoSpendOk`/`BadDep` pull back cleanly
   across multi-step constructors.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. `EnvTaintOk`, `Interp` Congruence, and Restriction Helpers -/

/-- Taint-bounding and open-region confinement for every non-erased binding in scope
(holds even after `@once` bindings become spent). -/
def EnvTaintOk (Scope : Nat → Prop) (env : List Bnd) (aenv : List ABnd)
    (st : St) (I : Interp) : Prop :=
  ∀ (i : Nat) (b : Bnd) (ab : ABnd), Scope i → env[i]? = some b → aenv[i]? = some ab →
    ab.mode ≠ .erased →
    (∀ c ∈ b.val.taint, c < st.nextRegion) ∧
    OpenUnder st.regions (I.regsOf (effVal ab).regs) b.val

theorem EnvTaintOk.step {Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {st st' : St} {I : Interp}
    (hr : st'.regions = st.regions) (hnr : st.nextRegion ≤ st'.nextRegion)
    (h : EnvTaintOk Scope env aenv st I) : EnvTaintOk Scope env aenv st' I := by
  intro i b ab hsc hbi habi hne
  obtain ⟨hlt, hopen⟩ := h i b ab hsc hbi habi hne
  exact ⟨fun c hc => Nat.lt_of_lt_of_le (hlt c hc) hnr, hr ▸ hopen⟩

theorem EnvTaintOk.mono_scope {Scope₁ Scope₂ : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {st : St} {I : Interp}
    (hsub : ∀ i, Scope₁ i → Scope₂ i) (h : EnvTaintOk Scope₂ env aenv st I) :
    EnvTaintOk Scope₁ env aenv st I :=
  fun i b ab hsc => h i b ab (hsub i hsc)

theorem Interp.regsOf_congr {I₁ I₂ : Interp} {rs : List Nat}
    (heq : ∀ r ∈ rs, I₁.reg r = I₂.reg r) : I₁.regsOf rs = I₂.regsOf rs := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    simp only [Interp.regsOf, List.flatMap_cons]
    rw [heq r List.mem_cons_self]
    exact congrArg (I₂.reg r ++ ·) (ih fun r' hr' => heq r' (List.mem_cons_of_mem _ hr'))

theorem EnvTaintOk.interp_congr {Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {st : St} {I₁ I₂ : Interp}
    (heq : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ r ∈ (effVal ab).regs, I₁.reg r = I₂.reg r)
    (h : EnvTaintOk Scope env aenv st I₁) : EnvTaintOk Scope env aenv st I₂ := by
  intro i b ab hsc hbi habi hne
  obtain ⟨hlt, hopen⟩ := h i b ab hsc hbi habi hne
  rw [Interp.regsOf_congr (heq i ab hsc habi hne)] at hopen
  exact ⟨hlt, hopen⟩

theorem EnvTaintOk.openRegion {Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {st : St} {I : Interp}
    (hregsLt : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ r ∈ (effVal ab).regs, r < σ.nextRegion)
    (h : EnvTaintOk Scope env aenv st I) :
    EnvTaintOk Scope env aenv
      { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions }
      (I.extend σ.nextRegion st.nextRegion) := by
  intro i b ab hsc hbi habi hne
  obtain ⟨hlt, hopen⟩ := h i b ab hsc hbi habi hne
  have hIeq : (I.extend σ.nextRegion st.nextRegion).regsOf (effVal ab).regs = I.regsOf (effVal ab).regs := by
    refine Interp.regsOf_congr fun r hr => ?_
    have hltR := hregsLt i ab hsc habi hne r hr
    simp [Interp.extend, Nat.ne_of_lt hltR]
  refine ⟨fun c hc => Nat.lt_succ_of_lt (hlt c hc), fun c hc hmem => ?_⟩
  rw [hIeq]
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact False.elim (Nat.lt_irrefl _ (hlt _ hc))
  · exact hopen c hc hmem'

theorem EnvTaintOk.cons_erased {Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {st : St} {I : Interp} {b : Bnd} {ab : ABnd}
    (her : ab.mode = .erased)
    (h : EnvTaintOk Scope env aenv st I) :
    EnvTaintOk (shiftScope Scope) (b :: env) (ab :: aenv) st I := by
  intro i b' ab' hsc hbi habi hne
  cases i with
  | zero => simp at habi; subst habi; exact absurd her hne
  | succ k => exact h k b' ab' hsc (by simpa using hbi) (by simpa using habi) hne

theorem EnvTaintOk.cons_active {P : Prog} {ext : ExternOracle} {B : Nat}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {st : St} {I : Interp}
    {bFoot : Nat → Prop} {b : Bnd} {ab : ABnd}
    (hv : VSim P ext B st Frame NoKill NoSpend σ I bFoot (effVal ab) b.val)
    (ha : ActiveVal σ (effVal ab))
    (h : EnvTaintOk Scope env aenv st I) :
    EnvTaintOk (shiftScope Scope) (b :: env) (ab :: aenv) st I := by
  intro i b' ab' hsc hbi habi hne
  cases i with
  | zero =>
    simp at hbi habi; subst hbi; subst habi
    obtain ⟨hbv, hdou, _⟩ := hv.2.2.2.2 ha
    exact ⟨fun c hc => hbv.2.2.2 b.val (HeldBy.refl _ _) c hc, hdou b.val (HeldBy.refl _ _)⟩
  | succ k => exact h k b' ab' hsc (by simpa using hbi) (by simpa using habi) hne

/-- `VSim` depends on `I` only at regions appearing in `av.regs`. -/
theorem VSim_interp_congr {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I₁ I₂ : Interp}
    {Foot : Nat → Prop} {av : AVal} {v : Val}
    (heq : ∀ r ∈ av.regs, I₁.reg r = I₂.reg r)
    (hv : VSim P ext B st Frame NoKill NoSpend σ I₁ Foot av v) :
    VSim P ext B st Frame NoKill NoSpend σ I₂ Foot av v := by
  refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, fun ha => ?_⟩
  have hact := hv.2.2.2.2 ha
  rw [Interp.regsOf_congr heq] at hact
  exact hact

/-- `Sim` depends on `I` only via `InterpOk` and on `< σ.nextRegion`. -/
theorem Sim_interp_congr {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {I₁ I₂ : Interp} {envFoot : Nat → Nat → Prop}
    (hIok₂ : InterpOk σ st I₂)
    (heq : ∀ r, r < σ.nextRegion → I₁.reg r = I₂.reg r)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I₁ envFoot) :
    Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I₂ envFoot := by
  refine ⟨hsim.1, hsim.2.1, hIok₂, hsim.2.2.2.1, hsim.2.2.2.2.1, ?_, hsim.2.2.2.2.2.2⟩
  intro i b ab hsc hbi habi
  obtain ⟨hmode, hne⟩ := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
  refine ⟨hmode, fun hne' => ?_⟩
  obtain ⟨honce, hv⟩ := hne hne'
  exact ⟨honce, VSim_interp_congr (fun r hr => heq r (hv.1 r hr)) hv⟩

/-- `Sim` transfers from `I` to `I'` when `I` and `I'` agree on every `r ≠ s_a`
and `s_a ∉ (effVal ab).regs` (used when closing `letVal` and `AAlt` regions). -/
theorem Sim_interp_congr_ne {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {I₁ I₂ : Interp} {envFoot : Nat → Nat → Prop} {s_a : Nat}
    (hIok₂ : InterpOk σ st I₂)
    (heq : ∀ r, r ≠ s_a → I₁.reg r = I₂.reg r)
    (hnotIn : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      s_a ∉ (effVal ab).regs)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I₁ envFoot) :
    Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I₂ envFoot := by
  refine ⟨hsim.1, hsim.2.1, hIok₂, hsim.2.2.2.1, hsim.2.2.2.2.1, ?_, hsim.2.2.2.2.2.2⟩
  intro i b ab hsc hbi habi
  obtain ⟨hmode, hne⟩ := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
  refine ⟨hmode, fun hne' => ?_⟩
  obtain ⟨honce, hv⟩ := hne hne'
  exact ⟨honce, VSim_interp_congr (fun r hr => heq r (fun hEq => hnotIn i ab hsc habi hne' (hEq ▸ hr))) hv⟩

/-- When `∀ r ≥ σ.nextRegion, I.reg r = []`, advancing `σ.nextRegion` to `n ≥ σ.nextRegion`
preserves `InterpOk`, `Sim`, `VSim`, and `ArgListOk` with the **same** `I`. -/
theorem AStateOk_advance_nextRegion {σ : AState} {n : Nat}
    (hok : AStateOk σ) (hle : σ.nextRegion ≤ n) :
    AStateOk { σ with nextRegion := n } ∧ AStateLe σ { σ with nextRegion := n } := by
  refine ⟨⟨hok.1, hok.2.1, Nat.le_trans hok.2.2.1 hle, hok.2.2.2.1, hok.2.2.2.2.1,
    fun r hr => let ⟨h1, h2⟩ := hok.2.2.2.2.2 r hr; ⟨h1, Nat.lt_of_lt_of_le h2 hle⟩⟩,
    ⟨Nat.le_refl _, hle, fun i hi => by rw [Array.getElem?_eq_getElem hi]; exact BSt.le_refl _,
     fun _ _ => rfl, fun _ _ h => h⟩⟩

theorem InterpOk_advance_nextRegion {σ : AState} {st : St} {I : Interp} {n : Nat}
    (hIok : InterpOk σ st I)
    (hIZero : ∀ r, σ.nextRegion ≤ r → I.reg r = []) :
    InterpOk { σ with nextRegion := n } st I := by
  refine ⟨fun r _ c hc => ?_, hIok.2⟩
  by_cases hlt : r < σ.nextRegion
  · exact hIok.1 r hlt c hc
  · rw [hIZero r (Nat.le_of_not_lt hlt)] at hc; cases hc

/-- `RegUnique (I.extend s_a s_c) σ' s_a s_c` holds at any future `σ'` as soon as
`I` is zero at `≥ s_a` and bounded by `< s_c` on `< s_a`. -/
theorem RegUnique_extend_of_zero {I : Interp} {σ' : AState} {s_a s_c : Nat}
    (hIZero : ∀ r, s_a ≤ r → I.reg r = [])
    (hILt : ∀ r, r < s_a → ∀ c ∈ I.reg r, c < s_c) :
    RegUnique (I.extend s_a s_c) σ' s_a s_c := by
  refine ⟨by simp [Interp.extend], fun r _ hne hmem => ?_⟩
  simp only [Interp.extend, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hmem
  by_cases hlt : r < s_a
  · exact Nat.lt_irrefl s_c (hILt r hlt s_c hmem)
  · rw [hIZero r (Nat.le_of_not_lt hlt)] at hmem; cases hmem

/-- Restricting `(NoKill, NoSpend)` to `< σ.st.size` preserves `VSim`, `ValEnvDisj`, `Sim`,
and `ArgListOk` (since all existing deps/src are `< σ.st.size`). -/
theorem VSim_restrict_noKill {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp}
    {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot av v) :
    VSim P ext B st Frame
      (fun d => d < σ.st.size ∧ NoKill d)
      (fun d => d < σ.st.size ∧ NoSpend d) σ I Foot av v := by
  refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, fun ha => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv.2.2.2.2 ha
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro hoo
    obtain ⟨ha1, ha2, ha3, ha4⟩ := h6 hoo
    exact ⟨ha1, fun hnk => ha2 fun x hx h => hnk x hx ⟨(hv.2.2.1 x hx).1, h⟩, ha3, ha4⟩
  · intro his
    obtain ⟨hb1, hb2, hb3⟩ := h7 his
    exact ⟨hb1, fun hnsp => hb2 fun d hd ho h => hnsp d hd ho ⟨hv.2.1 d hd, h⟩, hb3⟩
  · intro htr
    refine h8 ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.1, fun d hd => ?_⟩
    exact ⟨(htr.2.2.2.2 d hd).1, fun hnk => (htr.2.2.2.2 d hd).2 ⟨hv.2.1 d hd, hnk⟩⟩

theorem ValEnvDisj_restrict_noKill {P : Prog} {st : St}
    {NoKill Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {envFoot : Nat → Nat → Prop} {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hdeps : ∀ d ∈ av.deps, d < σ.st.size)
    (hdepsE : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ∀ d ∈ (effVal ab).deps, d < σ.st.size)
    (hd : ValEnvDisj P st NoKill Scope env aenv σ envFoot Foot av v) :
    ValEnvDisj P st (fun d => d < σ.st.size ∧ NoKill d) Scope env aenv σ envFoot Foot av v := by
  intro i b ab hsc hbi habi hne
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hd i b ab hsc hbi habi hne
  refine ⟨fun ha htr => c1 ha ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.1,
      fun d hd' => ⟨(htr.2.2.2.2 d hd').1, fun h => (htr.2.2.2.2 d hd').2 ⟨hdeps d hd', h⟩⟩⟩,
    fun ha htr => c2 ha ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.1,
      fun d hd' => ⟨(htr.2.2.2.2 d hd').1, fun h => (htr.2.2.2.2 d hd').2 ⟨hdepsE i ab habi d hd', h⟩⟩⟩,
    c3, c4, c5, c6, c7⟩

theorem Sim_restrict_noKill {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    Sim P ext B st Frame
      (fun d => d < σ.st.size ∧ NoKill d)
      (fun d => d < σ.st.size ∧ NoSpend d) Scope env aenv σ I envFoot := by
  refine ⟨hsim.1, hsim.2.1, hsim.2.2.1, hsim.2.2.2.1, hsim.2.2.2.2.1, ?_, ?_⟩
  · intro i b ab hsc hbi habi
    obtain ⟨hm, hne⟩ := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
    exact ⟨hm, fun hne' => let ⟨ho, hv⟩ := hne hne'; ⟨ho, VSim_restrict_noKill hv⟩⟩
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ ha₁ hb₂ ha₂ hne₁ hne₂
    obtain ⟨c1, c2⟩ := hsim.2.2.2.2.2.2 i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ ha₁ hb₂ ha₂ hne₁ hne₂
    have hdeps₁ := ((hsim.2.2.2.2.2.1 i b₁ ab₁ hsi hb₁ ha₁).2 hne₁).2.2.1
    refine ⟨fun ha₁' htr₁ => c1 ha₁' ⟨htr₁.1, htr₁.2.1, htr₁.2.2.1, htr₁.2.2.2.1,
      fun d hd => ⟨(htr₁.2.2.2.2 d hd).1, fun h => (htr₁.2.2.2.2 d hd).2 ⟨hdeps₁ d hd, h⟩⟩⟩, c2⟩

theorem ArgListOk_restrict_noKill {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {args : List (Option (Val × AVal × (Nat → Prop)))}
    (hdepsE : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ∀ d ∈ (effVal ab).deps, d < σ.st.size)
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep args) :
    ArgListOk P ext B st Frame
      (fun d => d < σ.st.size ∧ NoKill d)
      (fun d => d < σ.st.size ∧ NoSpend d)
      Scope env aenv σ I envFoot Forbid BadReg BadDep args := by
  refine ⟨fun i v av ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
  · obtain ⟨hv, hd, hnrf, hnv⟩ := hargs.1 i v av ft hg
    exact ⟨VSim_restrict_noKill hv, ValEnvDisj_restrict_noKill hv.2.1 hdepsE hd, hnrf, hnv⟩
  · obtain ⟨c1, c2⟩ := hargs.2 i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂
    have hdeps₁ := (hargs.1 i v₁ av₁ ft₁ hg₁).1.2.1
    exact ⟨fun ha₁ htr₁ => c1 ha₁ ⟨htr₁.1, htr₁.2.1, htr₁.2.2.1, htr₁.2.2.2.1,
      fun d hd => ⟨(htr₁.2.2.2.2 d hd).1, fun h => (htr₁.2.2.2.2 d hd).2 ⟨hdeps₁ d hd, h⟩⟩⟩, c2⟩

/-- Restricting `BadReg` to `< σ.nextRegion` preserves `EnvNoReachForbid` and `ArgListOk`,
and guarantees `¬ BadReg' σ.nextRegion` for fresh regions. -/
theorem EnvNoReachForbid_restrict_badReg {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henv : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep) :
    EnvNoReachForbid st Scope env aenv σ Forbid (fun r => r < σ.nextRegion ∧ BadReg r) BadDep := by
  intro i b ab hsc hbi habi hne ha hregs hdeps
  have hlt := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2.1
  exact henv i b ab hsc hbi habi hne ha (fun r hr hbr => hregs r hr ⟨hlt r hr, hbr⟩) hdeps

theorem ArgListOk_restrict_badReg {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {args : List (Option (Val × AVal × (Nat → Prop)))}
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep args) :
    ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid (fun r => r < σ.nextRegion ∧ BadReg r) BadDep args := by
  refine ⟨fun i v av ft hg => ?_, hargs.2⟩
  obtain ⟨hv, hd, hnrf, hnv⟩ := hargs.1 i v av ft hg
  exact ⟨hv, hd, fun ha hregs hdeps => hnrf ha (fun r hr hbr => hregs r hr ⟨hv.1 r hr, hbr⟩) hdeps, hnv⟩

theorem NoReachForbid_weaken_badReg {st : St} {Forbid BadReg₁ BadReg₂ BadDep : Nat → Prop}
    {av : AVal} {v : Val}
    (hsub : ∀ r, BadReg₁ r → BadReg₂ r)
    (hnrf : NoReachForbid st Forbid BadReg₁ BadDep av v) :
    NoReachForbid st Forbid BadReg₂ BadDep av v :=
  fun hregs hdeps => hnrf (fun r hr h1 => hregs r hr (hsub r h1)) hdeps

/-- Pull back `NoKillOk`, `NoSpendOk`, and `hBadDepLive` across `AStateLe`. -/
theorem NoKillOk_of_AStateLe {NoKill : Nat → Prop} {σ₁ σ₂ : AState}
    (hle : AStateLe σ₁ σ₂) (hnk : NoKillOk NoKill σ₂) : NoKillOk NoKill σ₁ := by
  intro d hd hdead
  have hlt : d < σ₁.st.size := (Array.getElem?_eq_some_iff.mp hdead).1
  have h2 := hle.2.2.1 d hlt
  rw [hdead] at h2
  cases h : σ₂.st[d]? with
  | none => rw [h] at h2; cases h2
  | some b₂ =>
    rw [h] at h2; cases b₂ with
    | live | shared => cases h2
    | dead => exact hnk d hd h

theorem NoSpendOk_of_AStateLe {NoSpend : Nat → Prop} {σ₁ σ₂ : AState}
    (hle : AStateLe σ₁ σ₂) (hnsp : NoSpendOk NoSpend σ₂) : NoSpendOk NoSpend σ₁ := by
  intro d hd hsp
  have hlt : d < σ₁.spent.size := (Array.getElem?_eq_some_iff.mp hsp).1
  exact hnsp d hd (hle.2.2.2.2 d hlt hsp)

theorem BadDepLive_of_AStateLe {BadDep : Nat → Prop} {σ₁ σ₂ : AState}
    (hle : AStateLe σ₁ σ₂) (hBad : ∀ d, BadDep d → σ₂.st[d]? = some .live)
    (hLt : ∀ d, BadDep d → d < σ₁.st.size) :
    ∀ d, BadDep d → σ₁.st[d]? = some .live := by
  intro d hd
  have hlt := hLt d hd
  have h1 := hle.2.2.1 d hlt
  rw [hBad d hd] at h1
  cases h : σ₁.st[d]? with
  | none => rw [h] at h1; cases h1
  | some b₁ =>
    rw [h] at h1; cases b₁ with
    | live => rfl
    | shared | dead => cases h1

theorem Sim_deps_lt_of_sim {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < σ.st.size := by
  intro i ab hsc habi hne d hd
  have hiA := (List.getElem?_eq_some_iff.mp habi).1
  have hiE : i < env.length := by rw [hsim.1]; exact hiA
  exact ((hsim.2.2.2.2.2.1 i env[i] ab hsc (List.getElem?_eq_getElem hiE) habi).2 hne).2.2.1 d hd

theorem Sim_regs_lt_of_sim {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ r ∈ (effVal ab).regs, r < σ.nextRegion := by
  intro i ab hsc habi hne r hr
  have hiA := (List.getElem?_eq_some_iff.mp habi).1
  have hiE : i < env.length := by rw [hsim.1]; exact hiA
  exact ((hsim.2.2.2.2.2.1 i env[i] ab hsc (List.getElem?_eq_getElem hiE) habi).2 hne).2.1 r hr

theorem AApps_state_le :
    ∀ {f : AVal} {xs : List AVal} {c : Cls} {σ σ' : AState} {r : AVal},
      AStateOk σ → AApps f xs c σ r σ' →
      AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions ∧ σ'.st.size = σ.st.size
  | _, _, _, _, _, _, hok, .nil => ⟨hok, AStateLe.refl _, rfl, rfl⟩
  | _, _, _, _, _, _, hok, .consLast hr =>
    let hu := Runs_applyValue hok hr
    ⟨hu.1, hu.2.1, hu.2.2.2.2.2.1, hu.2.2.1⟩
  | _, _, _, _, _, _, hok, .consMore hr hrest =>
    let hu := Runs_applyValue hok hr
    let ⟨hok2, hle2, hreg2, hsz2⟩ := AApps_state_le hu.1 hrest
    ⟨hok2, hu.2.1.trans hle2, hreg2.trans hu.2.2.2.2.2.1, hsz2.trans hu.2.2.1⟩

private theorem AStateOk_restoreOwned_eval (owned : List Nat) (σ : AState) (hok : AStateOk σ) :
    AStateOk (restoreOwned owned σ) ∧ (restoreOwned owned σ).nextRegion = σ.nextRegion := by
  have hsz : ∀ (xs : List Nat) (arr : Array BSt),
      (xs.foldl (fun a x => a.set! x BSt.live) arr).size = arr.size := by
    intro xs; induction xs with
    | nil => intro _; rfl
    | cons x rest ih => intro arr; simp only [List.foldl_cons, ih, Array.size_set!]
  refine ⟨⟨?_, ?_, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2⟩, rfl⟩
  · dsimp only [restoreOwned]; rw [hsz]; exact hok.1
  · dsimp only [restoreOwned]; rw [hsz]; exact hok.2.1

theorem ACaps_state_le {aenv : List ABnd} :
    ∀ {fvs : List Nat} {σ σ' : AState} {deps₀ regs₀ owned₀ deps regs owned : List Nat},
      AStateOk σ → ACaps aenv fvs σ deps₀ regs₀ owned₀ deps regs owned σ' →
      AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion
  | _, _, _, _, _, _, _, _, _, hok, .nil => ⟨hok, AStateLe.refl _, rfl, rfl⟩
  | _, _, _, _, _, _, _, _, _, hok, .consUniq _ hread _ hflow hrest => by
    obtain ⟨_, _, _, _, _, rfl⟩ := Runs_readVar hread
    obtain ⟨hok2, hle2, _, _, _, hreg2, hnr2, _⟩ := Runs_flowTo hok hflow
    obtain ⟨hok', hle', hreg', hnr'⟩ := ACaps_state_le hok2 hrest
    exact ⟨hok', hle2.trans hle', hreg'.trans hreg2, hnr'.trans hnr2⟩
  | _, _, _, _, _, _, _, _, _, hok, .consShare _ hread _ hflow hrest => by
    obtain ⟨_, _, _, _, _, rfl⟩ := Runs_readVar hread
    obtain ⟨hok2, hle2, _, _, _, hreg2, hnr2, _⟩ := Runs_flowTo hok hflow
    obtain ⟨hok', hle', hreg', hnr'⟩ := ACaps_state_le hok2 hrest
    exact ⟨hok', hle2.trans hle', hreg'.trans hreg2, hnr'.trans hnr2⟩

/- Pure static monotonicity of all `ModeOk` derivations: every derivation preserves `AStateOk`,
advances `AStateLe`, and restores `σ.regions`. -/
mutual

theorem ATerm_state_le {P : Prog} {aenv : List ABnd} {t : Term} {σ : AState} {av : AVal} {σ' : AState}
    (hok : AStateOk σ) (h : ATerm P aenv t σ av σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions := by
  match h with
  | .irr | .natLit | .strLit => exact ⟨hok, AStateLe.refl _, rfl⟩
  | .var hr =>
    obtain ⟨_, _, _, _, _, rfl⟩ := Runs_readVar hr
    exact ⟨hok, AStateLe.refl _, rfl⟩
  | .constCall hc | .appConst _ hc => exact ACall_state_le hok hc
  | .appVal _ _ hh hev happs =>
    obtain ⟨hok1, hle1, hreg1⟩ := ATerm_state_le hok hh
    obtain ⟨hok2, hle2, hreg2⟩ := AEvals_state_le hok1 hev
    obtain ⟨hok3, hle3, hreg3, _⟩ := AApps_state_le hok2 happs
    exact ⟨hok3, (hle1.trans hle2).trans hle3, hreg3.trans (hreg2.trans hreg1)⟩
  | .lam (owned := owned) (σ₁ := σ₁) (σ_ret := σ_ret) hcaps hbody hret _ hEq =>
    obtain ⟨hok1, hle1, hreg1, _⟩ := ACaps_state_le hok hcaps
    obtain ⟨hokCall, hnrCall⟩ := AStateOk_restoreOwned_eval owned σ₁ hok1
    have hokO := hokCall.openReg.1
    obtain ⟨hokB, hleB, _⟩ := ATerm_state_le (hokO.pushBnd _ _).1 hbody
    obtain ⟨_, _, _, _, _, _, hnrR, _⟩ := Runs_retCheck hokB hret
    have hnrLe : σ₁.nextRegion ≤ σ_ret.nextRegion := by
      have h1 : (restoreOwned owned σ₁).openReg.2.nextRegion = σ₁.nextRegion + 1 := by
        simp [AState.openReg, hnrCall]
      have h2 := hleB.2.1; simp [AState.pushBnd] at h2; omega
    subst hEq
    refine ⟨⟨hok1.1, hok1.2.1, Nat.le_trans hok1.2.2.1 hnrLe, hok1.2.2.2.1, hok1.2.2.2.2.1,
      fun r hr => let ⟨h1, h2⟩ := hok1.2.2.2.2.2 r hr; ⟨h1, Nat.lt_of_lt_of_le h2 hnrLe⟩⟩,
      ⟨hle1.1, Nat.le_trans hle1.2.1 hnrLe, hle1.2.2.1, hle1.2.2.2.1, hle1.2.2.2.2⟩, hreg1⟩
  | .letErased hb =>
    obtain ⟨hokP, hleP⟩ := hok.pushBnd { cls := .irr } false
    obtain ⟨hok', hle', hreg'⟩ := ATerm_state_le hokP hb
    exact ⟨hok', hleP.trans hle', hreg'⟩
  | .letVal (σ₁ := σ₁) (σ₄ := σ₄) _ hv hbind hb hval _ =>
    obtain ⟨hok1, hle1, hreg1⟩ := ATerm_state_le hok hv
    obtain ⟨hokO, _, hsaNotIn⟩ := hok1.openReg
    have hle1O := AStateLe_openReg σ₁
    obtain ⟨hok2, hle2, _, _, _, hreg2, _⟩ := Runs_bindInner hokO hbind
    obtain ⟨hokP, hleP⟩ := hok2.pushBnd _ _
    obtain ⟨hok3, hle3, hreg3⟩ := ATerm_state_le hokP hb
    obtain ⟨_, rfl⟩ := Runs_valid hval
    have hsaNe1 : σ₁.openReg.1 ≠ 1 := by have := hok1.2.2.1; simp [AState.openReg]; omega
    have hregClose : (σ₄.closeReg σ₁.openReg.1).regions = σ₁.regions := by
      dsimp only [AState.closeReg]; rw [hreg3]; dsimp only [AState.pushBnd]; rw [hreg2]; dsimp only [AState.openReg]
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun r hr => bne_iff_ne.mpr fun hEq => hsaNotIn (by subst hEq; exact hr)
    exact ⟨hok3.closeReg hsaNe1, (((hle1.trans hle1O).trans hle2).trans hleP).trans hle3, hregClose.trans hreg1⟩
  | .proj he hval hproj =>
    obtain ⟨hok1, hle1, hreg1⟩ := ATerm_state_le hok he
    obtain ⟨_, rfl⟩ := Runs_valid hval
    obtain ⟨rfl, _⟩ := Runs_anProj hproj
    exact ⟨hok1, hle1, hreg1⟩
  | @ATerm.caseTerm _ _ k _ alts _ _ _ _ _ pre _ σ_join _ _ _ _ haltsSz hmj halts hzero _ _ _ _ _ hex happs =>
    obtain ⟨hokPre, hlePre, hregPre⟩ := AMajor_state_le hok hmj
    have hjoinOkLe : AStateOk σ_join ∧ AStateLe pre σ_join ∧ σ_join.regions = pre.regions := by
      cases hsz : k.alts.size with
      | zero =>
        obtain ⟨hstJ, honceJ, hspJ, hregJ, hnrJ⟩ := hzero hsz
        refine ⟨⟨by rw [hstJ, honceJ]; exact hokPre.1, by rw [hstJ, hspJ]; exact hokPre.2.1,
          Nat.le_trans hokPre.2.2.1 hnrJ, hregJ ▸ hokPre.2.2.2.1, hregJ ▸ hokPre.2.2.2.2.1,
          fun r hr => let ⟨h1, h2⟩ := hokPre.2.2.2.2.2 r (hregJ ▸ hr); ⟨h1, Nat.lt_of_lt_of_le h2 hnrJ⟩⟩,
          ⟨by rw [hstJ]; exact Nat.le_refl _, hnrJ,
           fun i hi => by rw [hstJ, Array.getElem?_eq_getElem hi]; exact BSt.le_refl _,
           fun i hi => by rw [honceJ],
           fun i hi hsp => by rw [hspJ]; exact hsp⟩, hregJ⟩
      | succ m =>
        have hltK : 0 < k.alts.toList.length := by simp [hsz]
        have hltA : 0 < alts.toList.length := by simp [haltsSz, hsz]
        exact AAlts_state_le hokPre halts (List.getElem?_eq_getElem hltK) (List.getElem?_eq_getElem hltA)
    obtain ⟨hokJ, hleJ, hregJ⟩ := hjoinOkLe
    obtain ⟨hokEx, hleEx, hregEx⟩ := AEvals_state_le hokJ hex
    obtain ⟨hokEnd, hleEnd, hregEnd, _⟩ := AApps_state_le hokEx happs
    exact ⟨hokEnd, ((hlePre.trans hleJ).trans hleEx).trans hleEnd,
      hregEnd.trans (hregEx.trans (hregJ.trans hregPre))⟩

theorem AAlts_state_le {P : Prog} {aenv : List ABnd} {k : CaseInfo} {mv : AVal} {consuming : Bool}
    {pre : AState} {j : Nat} {cas : List CaseAlt} {altTs : List Term} {r_join : AVal} {σ_join : AState}
    {ca : CaseAlt} {altT : Term}
    (hok : AStateOk pre)
    (h : AAlts P aenv k mv consuming pre j cas altTs r_join σ_join)
    (hca : cas[0]? = some ca) (haltT : altTs[0]? = some altT) :
    AStateOk σ_join ∧ AStateLe pre σ_join ∧ σ_join.regions = pre.regions := by
  match h with
  | .nil => cases hca
  | .cons hnr halt hno _ hval huniq hsj _ _ =>
    obtain ⟨hokPre', hlePre'⟩ := AStateOk_advance_nextRegion hok hnr
    obtain ⟨hokPost, hlePost, _⟩ := AAlt_state_le hokPre' halt
    obtain ⟨_, rfl⟩ := Runs_notOnceSrc hno
    obtain ⟨_, rfl⟩ := Runs_valid hval
    obtain ⟨rfl, _⟩ := Runs_isUniq huniq
    obtain ⟨hstSz, honceEq, hspSz, hregEq, hnrLe, hstGe, hspGe⟩ := hsj
    have hle1 : AStateLe pre _ := hlePre'.trans hlePost
    refine ⟨⟨by rw [hstSz, honceEq]; exact hok.1, by rw [hstSz, hspSz]; exact hok.2.1,
      Nat.le_trans hokPost.2.2.1 hnrLe, hregEq ▸ hok.2.2.2.1, hregEq ▸ hok.2.2.2.2.1,
      fun r hr => let ⟨h1, h2⟩ := hok.2.2.2.2.2 r (hregEq ▸ hr)
                  ⟨h1, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h2 hle1.2.1) hnrLe⟩⟩,
      ⟨by omega, Nat.le_trans hle1.2.1 hnrLe, fun i hi => ?_, fun i _ => by rw [honceEq], fun i hi hsp => ?_⟩,
      hregEq⟩
    · have h1 := hle1.2.2.1 i hi
      have h2 := hstGe i hi
      split at h1
      · rename_i b0 b1 hb0 hb1
        rw [hb0]
        rw [hb1] at h2
        split at h2
        · rename_i b1' b2 hb1' hb2
          cases hb1'; rw [hb2]; exact BSt.le_trans h1 h2
        · cases h2
      · cases h1
    · exact hspGe i hi (hle1.2.2.2.2 i hi hsp)

theorem AEvals_state_le {P : Prog} {aenv : List ABnd} {ts : List Term} {σ : AState}
    {avs : List AVal} {σ' : AState}
    (hok : AStateOk σ) (h : AEvals P aenv ts σ avs σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions := by
  match h with
  | .nil => exact ⟨hok, AStateLe.refl _, rfl⟩
  | .cons ht hrest =>
    obtain ⟨hok1, hle1, hreg1⟩ := ATerm_state_le hok ht
    obtain ⟨hok2, hle2, hreg2⟩ := AEvals_state_le hok1 hrest
    exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩

theorem ACallArgs_state_le {P : Prog} {d? : Option RunDef} {aenv : List ABnd} {idx : Nat}
    {ts : List Term} {σ : AState} {avs : List (Option AVal)} {σ' : AState}
    (hok : AStateOk σ) (h : ACallArgs P d? aenv idx ts σ avs σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions := by
  match h with
  | .nil => exact ⟨hok, AStateLe.refl _, rfl⟩
  | .consSkip _ hrest => exact ACallArgs_state_le hok hrest
  | .consEval _ ht hrest =>
    obtain ⟨hok1, hle1, hreg1⟩ := ATerm_state_le hok ht
    obtain ⟨hok2, hle2, hreg2⟩ := ACallArgs_state_le hok1 hrest
    exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩

theorem ACall_state_le {P : Prog} {aenv : List ABnd} {r : Ref} {args : List Term} {c : Cls}
    {σ : AState} {res : AVal} {σ' : AState}
    (hok : AStateOk σ) (h : ACall P aenv r args c σ res σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions := by
  match h with
  | .ind _ hargs => exact ACallArgs_state_le hok hargs
  | .ctor _ hargs hctor =>
    obtain ⟨hok1, hle1, hreg1⟩ := ACallArgs_state_le hok hargs
    obtain ⟨hok2, hle2, _, _, _, hreg2, _⟩ := Runs_anCtor hok1 hctor
    exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩
  | .prim _ hargs hprim =>
    obtain ⟨hok1, hle1, hreg1⟩ := ACallArgs_state_le hok hargs
    obtain ⟨hok2, hle2, _, _, _, hreg2, _⟩ := APrimArgs_info hok1 hprim
    exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩
  | .ifacePap _ _ hargs _ hpap =>
    obtain ⟨hok1, hle1, hreg1⟩ := ACallArgs_state_le hok hargs
    obtain ⟨hok2, hle2, _, _, _, hreg2, _⟩ := Runs_papVal hok1 hpap
    exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩
  | .ifaceFullZero _ _ hargs _ happs =>
    obtain ⟨hok1, hle1, hreg1⟩ := ACallArgs_state_le hok hargs
    obtain ⟨hok2, hle2, hreg2, _⟩ := AApps_state_le hok1 happs
    exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩
  | .ifaceFullPos _ _ hargs _ _ hcall happs =>
    obtain ⟨hok1, hle1, hreg1⟩ := ACallArgs_state_le hok hargs
    obtain ⟨hok2, hle2, _, _, _, hreg2, _⟩ := Runs_callResult hok1 hcall
    obtain ⟨hok3, hle3, hreg3, _⟩ := AApps_state_le hok2 happs
    exact ⟨hok3, (hle1.trans hle2).trans hle3, hreg3.trans (hreg2.trans hreg1)⟩

theorem AMajor_state_le {P : Prog} {aenv : List ABnd} {t : Term} {σ : AState}
    {av : AVal} {cons : Bool} {σ' : AState}
    (hok : AStateOk σ) (h : AMajor P aenv t σ av cons σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions := by
  match h with
  | .varConsuming _ hread _ _ hflow =>
    obtain ⟨_, _, _, _, _, rfl⟩ := Runs_readVar hread
    obtain ⟨hok2, hle2, _, _, _, hreg2, _⟩ := Runs_flowTo hok hflow
    exact ⟨hok2, hle2, hreg2⟩
  | .varPlain _ hread _ =>
    obtain ⟨_, _, _, _, _, rfl⟩ := Runs_readVar hread
    exact ⟨hok, AStateLe.refl _, rfl⟩
  | .nonVar _ ht => exact ATerm_state_le hok ht

theorem AAlt_state_le {P : Prog} {aenv : List ABnd} {t : Term}
    {aargs : List (AVal × Bool × Bool)} {σ : AState} {r : AVal} {σ' : AState}
    (hok : AStateOk σ) (h : AAlt P aenv t aargs σ r σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧ σ'.regions = σ.regions := by
  match h with
  | .nil ht => exact ATerm_state_le hok ht
  | .lamErased (σ₂ := σ₂) halt hret =>
    obtain ⟨hokO, _, hsaNotIn⟩ := hok.openReg
    have hleO : AStateLe σ σ.openReg.2 := AStateLe_openReg σ
    obtain ⟨hokP, hleP⟩ := hokO.pushBnd { cls := .irr } false
    obtain ⟨hok1, hle1, hreg1⟩ := AAlt_state_le hokP halt
    obtain ⟨hok2, hle2, _, _, _, hreg2, _⟩ := Runs_retCheck hok1 hret
    have hsaNe1 : σ.openReg.1 ≠ 1 := by have := hok.2.2.1; simp [AState.openReg]; omega
    have hregClose : (σ₂.closeReg σ.openReg.1).regions = σ.regions := by
      dsimp only [AState.closeReg]; rw [hreg2, hreg1]; dsimp only [AState.openReg, AState.pushBnd]
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun rg hrg => bne_iff_ne.mpr fun hEq => hsaNotIn (by subst hEq; exact hrg)
    exact ⟨hok2.closeReg hsaNe1, ((hleO.trans hleP).trans hle1).trans hle2, hregClose⟩
  | .lamKept (σ₃ := σ₃) _ hbind halt hret =>
    obtain ⟨hokO, _, hsaNotIn⟩ := hok.openReg
    have hleO : AStateLe σ σ.openReg.2 := AStateLe_openReg σ
    obtain ⟨hok1, hle1, _, _, _, hreg1, _⟩ := Runs_bindInner hokO hbind
    obtain ⟨hokP, hleP⟩ := hok1.pushBnd _ _
    obtain ⟨hok2, hle2, hreg2⟩ := AAlt_state_le hokP halt
    obtain ⟨hok3, hle3, _, _, _, hreg3, _⟩ := Runs_retCheck hok2 hret
    have hsaNe1 : σ.openReg.1 ≠ 1 := by have := hok.2.2.1; simp [AState.openReg]; omega
    have hregClose : (σ₃.closeReg σ.openReg.1).regions = σ.regions := by
      dsimp only [AState.closeReg]; rw [hreg3, hreg2]; dsimp only [AState.pushBnd]; rw [hreg1]; dsimp only [AState.openReg]
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun rg hrg => bne_iff_ne.mpr fun hEq => hsaNotIn (by subst hEq; exact hrg)
    exact ⟨hok3.closeReg hsaNe1, (((hleO.trans hle1).trans hleP).trans hle2).trans hle3, hregClose⟩
  | .nonLam _ _ ht happs =>
    obtain ⟨hok1, hle1, hreg1⟩ := ATerm_state_le hok ht
    obtain ⟨hok2, hle2, hreg2, _⟩ := AApps_state_le hok1 happs
    exact ⟨hok2, hle1.trans hle2, hreg2.trans hreg1⟩

end

/-! ## 2. Structural & Evaluator Helpers (`collect`, `case_join_weaken`) -/

theorem collect_caseFieldsDistinct :
    ∀ (t : Term) (acc : List Term),
      CaseFieldsDistinct t → (∀ a ∈ acc, CaseFieldsDistinct a) →
      CaseFieldsDistinct (collect t acc).1 ∧ ∀ a ∈ (collect t acc).2, CaseFieldsDistinct a
  | .app f a c, acc, hcfd, hacc => by
    cases hcfd with
    | app hcf hca =>
      simp only [collect]
      exact collect_caseFieldsDistinct f (a :: acc) hcf (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hca
        · exact hacc x hx')
  | .irr, _, hcfd, hacc | .var .., _, hcfd, hacc | .const .., _, hcfd, hacc
  | .natLit _, _, hcfd, hacc | .strLit _, _, hcfd, hacc | .lam .., _, hcfd, hacc
  | .letE .., _, hcfd, hacc | .proj .., _, hcfd, hacc | .case .., _, hcfd, hacc =>
    ⟨hcfd, hacc⟩

theorem ACallArgs_erased_iff {P : Prog} {d? : Option RunDef} {aenv : List ABnd} :
    ∀ {idx : Nat} {ts : List Term} {σ σ' : AState} {avs : List (Option AVal)},
      ACallArgs P d? aenv idx ts σ avs σ' →
      avs.length = ts.length ∧
      ∀ (i : Nat), i < avs.length →
        (avs[i]? = some none ↔ (match d? with | some d => erasedAt d (idx + i) | none => false) = true)
  | _, _, _, _, _, .nil => ⟨rfl, fun _ h => by cases h⟩
  | idx, _ :: _, _, _, _, .consSkip hskip hrest => by
    obtain ⟨hlen, hiff⟩ := ACallArgs_erased_iff hrest
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.add_zero]
      exact ⟨(fun _ => hskip), (fun _ => trivial)⟩
    | succ k =>
      have h1 := hiff k (by simpa using hi)
      have hidx : idx + 1 + k = idx + (k + 1) := by omega
      simpa [hidx] using h1
  | idx, _ :: _, _, _, _, .consEval hkeep _ hrest => by
    obtain ⟨hlen, hiff⟩ := ACallArgs_erased_iff hrest
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.add_zero]
      exact ⟨(fun h => by cases h), (fun h => by cases d? <;> simp at hkeep h <;> rw [hkeep] at h <;> cases h)⟩
    | succ k =>
      have h1 := hiff k (by simpa using hi)
      have hidx : idx + 1 + k = idx + (k + 1) := by omega
      simpa [hidx] using h1

theorem AApps_change_cls {f : AVal} {xs : List AVal} {c c' : Cls} {σ σ' : AState} {r : AVal}
    (h : AApps f xs c σ r σ') : AApps { f with cls := c' } xs c σ r σ' := by
  cases h with
  | nil => exact AApps.nil
  | consLast hr => exact AApps.consLast hr
  | consMore hr hrest => exact AApps.consMore hr hrest

/-- Weakening a case alternative's result `(r_j, post_j)` to the joined `(r_join_v, σ_join)`
(with `r_join_v := { r_join with cls := r_j.cls }`, since `AApps` is independent of `f.cls` and
`applyAllS` performs the final `conform c`) via `notOnceSrc`, `valid`, `isUniq`, `StateJoinGe`,
and `ValJoinGe`. -/
theorem case_join_weaken {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd}
    {pre post_j σ_join : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {rFoot : Nat → Prop}
    {r_j r_join : AVal} {rv : Val} {uniq_j : Bool}
    (hokPre : AStateOk pre)
    (hlePrePost : AStateLe pre post_j)
    (hIZero : ∀ r, pre.nextRegion ≤ r → I.reg r = [])
    (hregPre : pre.regions = post_j.regions)
    (hsimPost : Sim P ext B st Frame
      (fun d => d < pre.st.size ∧ NoKill d)
      (fun d => d < pre.st.size ∧ NoSpend d) Scope env aenv post_j I envFoot)
    (henvNRFPost : EnvNoReachForbid st Scope env aenv post_j Forbid BadReg BadDep)
    (hdepsEnvPre : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < pre.st.size)
    (hidsPre : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < pre.st.size)
    (hvPost : VSim P ext B st Frame
      (fun d => d < pre.st.size ∧ NoKill d)
      (fun d => d < pre.st.size ∧ NoSpend d) post_j I rFoot r_j rv)
    (hdisjPost : ValEnvDisj P st (fun d => d < pre.st.size ∧ NoKill d) Scope env aenv post_j envFoot rFoot r_j rv)
    (hnrfPost : ActiveVal post_j r_j → NoReachForbid st Forbid BadReg BadDep r_j rv)
    (hnoOnce : Runs (notOnceSrc r_j "a case alternative's result") post_j () post_j)
    (hooRj : r_j.onceOnly = false)
    (hvalRj : Runs (valid r_j "a case alternative's result") post_j () post_j)
    (huniqRj : Runs (isUniq r_j) post_j uniq_j post_j)
    (hsj : StateJoinGe pre post_j σ_join)
    (hvj : ValJoinGe pre.st.size
      { r_j with own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared } r_join)
    (hrjSrc : r_join.src = none)
    (hrjOO : r_join.onceOnly = false)
    (hrjDeps : ∀ d ∈ r_join.deps, d < pre.st.size)
    (hrjRegs : ∀ rg ∈ r_join.regs, rg < σ_join.nextRegion)
    (hBadDepJoin : ∀ d, BadDep d → σ_join.st[d]? = some .live) :
    let r_join_v : AVal := { r_join with cls := r_j.cls }
    AStateOk σ_join ∧ AStateLe pre σ_join ∧
    Sim P ext B st Frame NoKill NoSpend Scope env aenv σ_join I envFoot ∧
    EnvNoReachForbid st Scope env aenv σ_join Forbid BadReg BadDep ∧
    VSim P ext B st Frame NoKill NoSpend σ_join I (fun _ => False) r_join_v rv ∧
    ValEnvDisj P st NoKill Scope env aenv σ_join envFoot (fun _ => False) r_join_v rv ∧
    (ActiveVal σ_join r_join_v → NoReachForbid st Forbid BadReg BadDep r_join_v rv) ∧
    (ValidDeps σ_join r_join_v.deps → r_join_v.cls ≠ .val → ValBaseOk st rv ∧ NonValSafe st.heap rv) ∧
    ValBaseOk st rv ∧
    (∀ c ∈ rv.taint, c < st.nextRegion) ∧
    OpenUnder st.regions (I.regsOf r_join_v.regs) rv := by
  intro r_join_v
  obtain ⟨hstSz, honceEq, hspSz, hregEq, hnrLe, hstGe, hspGe⟩ := hsj
  obtain ⟨hnotOnceRj, _⟩ := Runs_notOnceSrc hnoOnce
  obtain ⟨hvdRj, _⟩ := Runs_valid hvalRj
  obtain ⟨_, huniqIff⟩ := Runs_isUniq huniqRj
  have haRj : ActiveVal post_j r_j := ⟨hvdRj, fun his => absurd his hnotOnceRj⟩
  have hvAct := hvPost.2.2.2.2 haRj
  have hplain := hvAct.2.2.2.2.1 ⟨hnotOnceRj, hooRj⟩
  have hokPost := hsimPost.2.1
  have hokJoin : AStateOk σ_join :=
    ⟨by rw [hstSz, honceEq]; exact hokPre.1,
     by rw [hstSz, hspSz]; exact hokPre.2.1,
     Nat.le_trans hokPost.2.2.1 hnrLe,
     hregEq ▸ hokPre.2.2.2.1,
     hregEq ▸ hokPre.2.2.2.2.1,
     fun r hr => let ⟨h1, h2⟩ := hokPre.2.2.2.2.2 r (hregEq ▸ hr)
                 ⟨h1, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h2 hlePrePost.2.1) hnrLe⟩⟩
  have hlePreJoin : AStateLe pre σ_join := by
    refine ⟨by omega, Nat.le_trans hlePrePost.2.1 hnrLe, fun i hi => ?_, fun _ _ => by rw [honceEq], fun i hi hsp => ?_⟩
    · have h1 := hlePrePost.2.2.1 i hi
      have h2 := hstGe i hi
      cases hp0 : pre.st[i]? with
      | none => rw [hp0] at h1; cases h1
      | some b0 =>
        rw [hp0] at h1
        cases hp1 : post_j.st[i]? with
        | none => rw [hp1] at h1; cases h1
        | some b1 =>
          rw [hp1] at h1 h2
          cases hp2 : σ_join.st[i]? with
          | none => rw [hp2] at h2; cases h2
          | some b2 => rw [hp2] at h2; exact BSt.le_trans h1 h2
    · exact hspGe i hi (hlePrePost.2.2.2.2 i hi hsp)
  -- Pull back `once`, `st`, `spent`, `ActiveVal`, `Transferable`, `FootActive` from `σ_join` to `post_j` on `< pre.st.size`
  have honceBack : ∀ d, d < pre.st.size → post_j.once[d]? = σ_join.once[d]? := by
    intro d hd
    have hdO : d < pre.once.size := by rw [← hokPre.1]; exact hd
    rw [honceEq]; exact hlePrePost.2.2.2.1 d hdO
  have hstNotDeadBack : ∀ d, d < pre.st.size → σ_join.st[d]? ≠ some .dead → post_j.st[d]? ≠ some .dead := by
    intro d hd hnd hdead
    have h2 := hstGe d hd
    rw [hdead] at h2
    cases h : σ_join.st[d]? with
    | none => rw [h] at h2; cases h2
    | some b2 =>
      rw [h] at h2; cases b2 with
      | live | shared => cases h2
      | dead => exact hnd h
  have hstLiveBack : ∀ d, d < pre.st.size → σ_join.st[d]? = some .live → post_j.st[d]? = some .live := by
    intro d hd hlv
    have h2 := hstGe d hd
    rw [hlv] at h2
    cases h : post_j.st[d]? with
    | none => rw [h] at h2; cases h2
    | some b1 =>
      rw [h] at h2; cases b1 with
      | live => rfl
      | shared | dead => cases h2
  have hspFalseBack : ∀ d, d < pre.st.size → σ_join.spent[d]? = some false → post_j.spent[d]? = some false := by
    intro d hd hsf
    have hltSp : d < post_j.spent.size := by have := hlePrePost.1; have := hokPost.2.1; omega
    have hltPreSp : d < pre.spent.size := by rw [← hokPre.2.1]; exact hd
    cases h : post_j.spent[d]? with
    | none => exact absurd (Array.getElem?_eq_none_iff.mp h) (Nat.not_le_of_lt hltSp)
    | some b =>
      cases b with
      | false => rfl
      | true => rw [hspGe d hltPreSp h] at hsf; cases hsf
  have hvdBack : ∀ {ds : List Nat}, (∀ d ∈ ds, d < pre.st.size) →
      ValidDeps σ_join ds → ValidDeps post_j ds := by
    intro ds hlt hvd d hd
    exact ⟨Nat.lt_of_lt_of_le (hlt d hd) hlePrePost.1, hstNotDeadBack d (hlt d hd) (hvd d hd).2⟩
  have hisOnceBack : ∀ {av : AVal}, (∀ x, av.src = some x → x < pre.st.size) →
      (IsOnceSrc σ_join av ↔ IsOnceSrc post_j av) := by
    intro av hlt
    constructor
    · rintro ⟨x, hs, ho⟩; exact ⟨x, hs, (honceBack x (hlt x hs)).trans ho⟩
    · rintro ⟨x, hs, ho⟩; exact ⟨x, hs, (honceBack x (hlt x hs)).symm.trans ho⟩
  have hactBack : ∀ {av : AVal}, (∀ d ∈ av.deps, d < pre.st.size) →
      (∀ x, av.src = some x → x < pre.st.size) →
      ActiveVal σ_join av → ActiveVal post_j av := by
    intro av hltD hltS ⟨hvd, hunsp⟩
    refine ⟨hvdBack hltD hvd, fun his d hd ho => ?_⟩
    have hoJ : σ_join.once[d]? = some true := (honceBack d (hltD d hd)).symm.trans ho
    exact hspFalseBack d (hltD d hd) (hunsp ((hisOnceBack hltS).mpr his) d hd hoJ)
  have htrBack : ∀ {av : AVal}, (∀ d ∈ av.deps, d < pre.st.size) →
      (∀ x, av.src = some x → x < pre.st.size) →
      Transferable σ_join NoKill av → Transferable post_j (fun d => d < pre.st.size ∧ NoKill d) av := by
    intro av hltD hltS ⟨hc, ho, hoo, hno, hlv⟩
    exact ⟨hc, ho, hoo, fun his => hno ((hisOnceBack hltS).mpr his), fun d hd =>
      ⟨hstLiveBack d (hltD d hd) (hlv d hd).1, fun hnk => (hlv d hd).2 hnk.2⟩⟩
  have hftBack : ∀ {av : AVal}, (∀ d ∈ av.deps, d < pre.st.size) →
      (∀ x, av.src = some x → x < pre.st.size) →
      FootActive σ_join av → FootActive post_j av := by
    intro av hltD hltS hft
    rcases hft with hoo | ⟨his, hunsp⟩
    · exact Or.inl hoo
    · refine Or.inr ⟨(hisOnceBack hltS).mp his, fun d hd ho => ?_⟩
      exact hspFalseBack d (hltD d hd) (hunsp d hd ((honceBack d (hltD d hd)).symm.trans ho))
  have hIokJoin : InterpOk σ_join st I := by
    refine ⟨fun r _ c hc => ?_, ?_⟩
    · by_cases hlt : r < pre.nextRegion
      · exact hsimPost.2.2.1.1 r (Nat.lt_of_lt_of_le hlt hlePrePost.2.1) c hc
      · rw [hIZero r (Nat.le_of_not_lt hlt)] at hc; cases hc
    · rw [hregEq, hregPre]; exact hsimPost.2.2.1.2
  -- Build `Sim` at `σ_join`
  have hsimJoin : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ_join I envFoot := by
    refine ⟨hsimPost.1, hokJoin, hIokJoin, fun i ab hab => by rw [hstSz]; exact hidsPre i ab hab,
      hsimPost.2.2.2.2.1, ?_, ?_⟩
    · intro i b ab hsc hbi habi
      obtain ⟨hmode, hne⟩ := hsimPost.2.2.2.2.2.1 i b ab hsc hbi habi
      refine ⟨hmode, fun hne' => ?_⟩
      obtain ⟨honceP, hvP⟩ := hne hne'
      have hdepsLt := hdepsEnvPre i ab hsc habi hne'
      have hsrcLt : ∀ x, (effVal ab).src = some x → x < pre.st.size := by
        intro x hs; dsimp [effVal] at hs; cases hs; exact hidsPre i ab habi
      refine ⟨(honceBack ab.id (hidsPre i ab habi)).symm.trans honceP,
        ⟨fun r hr => Nat.lt_of_lt_of_le (hvP.1 r hr) hnrLe,
         fun d hd => by rw [hstSz]; exact hdepsLt d hd,
         fun x hs => ⟨by rw [hstSz]; exact hsrcLt x hs, (hvP.2.2.1 x hs).2⟩,
         fun hvd his => hvP.2.2.2.1 (hvdBack hdepsLt hvd) ((hisOnceBack hsrcLt).mp his),
         fun haJ => ?_⟩⟩
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hvP.2.2.2.2 (hactBack hdepsLt hsrcLt haJ)
      refine ⟨b1, b2, b3,
        fun hno => b4 (fun h => hno ((hisOnceBack hsrcLt).mpr h)),
        fun ⟨hno, hoo⟩ => b5 ⟨fun h => hno ((hisOnceBack hsrcLt).mpr h), hoo⟩,
        fun hoo => let ⟨q1, q2, q3, q4⟩ := b6 hoo
          ⟨q1, fun hnk => q2 (fun x hs h => hnk x hs h.2), q3, q4⟩,
        fun his => let ⟨q1, q2, q3⟩ := b7 ((hisOnceBack hsrcLt).mp his)
          ⟨q1, fun hnsp => q2 (fun d hd ho h => hnsp d hd ((honceBack d (hdepsLt d hd)).symm.trans ho) h.2), q3⟩,
        fun htr => b8 (htrBack hdepsLt hsrcLt htr)⟩
    · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ ha₁ hb₂ ha₂ hne₁ hne₂
      obtain ⟨d1, d2⟩ := hsimPost.2.2.2.2.2.2 i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ ha₁ hb₂ ha₂ hne₁ hne₂
      have hdeps₁ := hdepsEnvPre i ab₁ hsi ha₁ hne₁
      have hdeps₂ := hdepsEnvPre j ab₂ hsj ha₂ hne₂
      have hsrc₁ : ∀ x, (effVal ab₁).src = some x → x < pre.st.size := by
        intro x hs; dsimp [effVal] at hs; cases hs; exact hidsPre i ab₁ ha₁
      have hsrc₂ : ∀ x, (effVal ab₂).src = some x → x < pre.st.size := by
        intro x hs; dsimp [effVal] at hs; cases hs; exact hidsPre j ab₂ ha₂
      exact ⟨fun ha₁' htr₁ ha₂' => d1 (hactBack hdeps₁ hsrc₁ ha₁') (htrBack hdeps₁ hsrc₁ htr₁) (hactBack hdeps₂ hsrc₂ ha₂'),
        fun ha₁' hft₁ ha₂' => d2 (hactBack hdeps₁ hsrc₁ ha₁') (hftBack hdeps₁ hsrc₁ hft₁) (hactBack hdeps₂ hsrc₂ ha₂')⟩
  -- Build `EnvNoReachForbid` at `σ_join`
  have henvNRFJoin : EnvNoReachForbid st Scope env aenv σ_join Forbid BadReg BadDep := by
    intro i b ab hsc hbi habi hne haJ
    have hdepsLt := hdepsEnvPre i ab hsc habi hne
    have hsrcLt : ∀ x, (effVal ab).src = some x → x < pre.st.size := by
      intro x hs; dsimp [effVal] at hs; cases hs; exact hidsPre i ab habi
    exact henvNRFPost i b ab hsc hbi habi hne (hactBack hdepsLt hsrcLt haJ)
  -- Helper: `Transferable σ_join NoKill r_join_v → Transferable post_j NoKill_alt r_j`
  have hrjTrBack : Transferable σ_join NoKill r_join_v →
      Transferable post_j (fun d => d < pre.st.size ∧ NoKill d) r_j := by
    intro htrJ
    have hcvRj : r_j.cls = .val := htrJ.1
    have hown' := hvj.2.1 htrJ.2.1
    have hcond : (r_j.own == Own.uniq && uniq_j) = true := by
      cases hc : (r_j.own == Own.uniq && uniq_j) with
      | true => rfl
      | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at hown'; cases hown'
    obtain ⟨hownB, huniqT⟩ := Bool.and_eq_true_iff.mp hcond
    have hlvRj : ∀ d ∈ r_j.deps, post_j.st[d]? = some .live := by
      have h1 := huniqIff.mp huniqT
      rcases h1 with hne | ⟨_, hlv⟩
      · exact absurd hcvRj hne
      · exact hlv
    have hownEq : r_j.own = Own.uniq := by
      cases ho : r_j.own with
      | shared => rw [ho] at hownB; cases hownB
      | uniq => rfl
    refine ⟨hcvRj, hownEq, hooRj, hnotOnceRj, fun d hd => ⟨hlvRj d hd, fun ⟨hlt, hnk⟩ => ?_⟩⟩
    exact (htrJ.2.2.2.2 d (hvj.2.2.1 d hd hlt)).2 hnk
  have hdouJoin : DeepOpenUnder st.heap st.regions (I.regsOf r_join_v.regs) rv :=
    hvAct.2.1.mono fun c hc => by
      obtain ⟨rg, hrgM, hcRg⟩ := Interp.mem_regsOf.mp hc
      exact Interp.mem_regsOf.mpr ⟨rg, hvj.2.2.2.1 rg hrgM, hcRg⟩
  have hVSimJoin : VSim P ext B st Frame NoKill NoSpend σ_join I (fun _ => False) r_join_v rv := by
    refine ⟨hrjRegs, (fun d hd => by rw [hstSz]; exact hrjDeps d hd),
      (fun _ hs => by dsimp only [r_join_v] at hs; rw [hrjSrc] at hs; cases hs),
      (fun _ ⟨_, hs, _⟩ => by dsimp only [r_join_v] at hs; rw [hrjSrc] at hs; cases hs), fun _ => ?_⟩
    exact ⟨hvAct.1, hdouJoin, hvAct.2.2.1,
      fun _ hneJ => hvAct.2.2.2.1 hnotOnceRj hneJ,
      fun _ => ⟨hplain.1, fun _ h => h, FunOkAt_of_admits hvj.1 hplain.2.2⟩,
      (fun hoo => by dsimp only [r_join_v] at hoo; rw [hrjOO] at hoo; cases hoo),
      (fun ⟨_, hs, _⟩ => by dsimp only [r_join_v] at hs; rw [hrjSrc] at hs; cases hs),
      fun htrJ => hvAct.2.2.2.2.2.2.2 (hrjTrBack htrJ)⟩
  have hDisjJoin : ValEnvDisj P st NoKill Scope env aenv σ_join envFoot (fun _ => False) r_join_v rv := by
    intro i b ab hsc hbi habi hne
    obtain ⟨c1, c2, _, c4, _, c6, _⟩ := hdisjPost i b ab hsc hbi habi hne
    have hdepsLt := hdepsEnvPre i ab hsc habi hne
    have hsrcLt : ∀ x, (effVal ab).src = some x → x < pre.st.size := by
      intro x hs; dsimp [effVal] at hs; cases hs; exact hidsPre i ab habi
    refine ⟨?_, ?_, (fun _ _ _ _ _ h => False.elim h), ?_,
      (fun _ _ _ _ h => False.elim h),
      (fun hs => by simp only [r_join_v, hrjSrc] at hs; cases hs),
      (fun _ hs => by simp only [r_join_v, hrjSrc] at hs; cases hs)⟩
    · intro _ htrJ haB hdd
      refine c1 haRj (hrjTrBack htrJ) (hactBack hdepsLt hsrcLt haB) fun d hdR hdB => ?_
      exact hdd d (hvj.2.2.1 d hdR (hdepsLt d hdB)) hdB
    · intro haB htrB _ hdd
      refine c2 (hactBack hdepsLt hsrcLt haB) (htrBack hdepsLt hsrcLt htrB) haRj fun d hdB hdR => ?_
      exact hdd d hdB (hvj.2.2.1 d hdR (hdepsLt d hdB))
    · intro haB hftB _ _
      refine c4 (hactBack hdepsLt hsrcLt haB) (hftBack hdepsLt hsrcLt hftB) haRj fun hs => ?_
      rcases hftB with hoo | ⟨⟨id, hsrc, ho⟩, _⟩
      · rw [c6 hs hoo] at hooRj; cases hooRj
      · dsimp [effVal] at hsrc; cases hsrc
        exact hnotOnceRj ⟨ab.id, hs, (honceBack ab.id (hidsPre i ab habi)).trans ho⟩
  have hNrfJoin : ActiveVal σ_join r_join_v → NoReachForbid st Forbid BadReg BadDep r_join_v rv := by
    intro _ hregs hdeps
    refine hnrfPost haRj (fun r hr => hregs r (hvj.2.2.2.1 r hr)) fun d hd hbd => ?_
    have hlt : d < pre.st.size := by
      have h1 := (Array.getElem?_eq_some_iff.mp (hBadDepJoin d hbd)).1; omega
    exact hdeps d (hvj.2.2.1 d hd hlt) hbd
  exact ⟨hokJoin, hlePreJoin, hsimJoin, henvNRFJoin, hVSimJoin, hDisjJoin, hNrfJoin,
    fun _ hne => ⟨hvAct.1, hvAct.2.2.2.1 hnotOnceRj hne⟩,
    hvAct.1, fun c hc => hvAct.1.2.2.2 rv (HeldBy.refl _ _) c hc, hdouJoin rv (HeldBy.refl _ _)⟩

/-! ## 3. Accumulator, Prefix, and Single-Binder Push Helpers -/

theorem evalListS_acc {P : Prog} {ext : ExternOracle} {n : Nat} {env : List Bnd} :
    ∀ (ts : List Term) (acc₁ acc₂ : List Val) (s : St × Nat),
      (evalListS P ext n env ts (acc₁ ++ acc₂)).run s =
        match (evalListS P ext n env ts acc₂).run s with
        | .error e => .error e
        | .ok (vs, s') => .ok (acc₁ ++ vs, s')
  | [], _, _, _ => by unfold evalListS; rfl
  | t :: rest, acc₁, acc₂, s => by
    unfold evalListS
    rw [MS_bind_run, MS_bind_run]
    cases (evalS P ext n env t).run s with
    | error _ => rfl
    | ok p =>
      dsimp only
      have h1 : (acc₁ ++ acc₂) ++ [p.1] = acc₁ ++ (acc₂ ++ [p.1]) := by simp [List.append_assoc]
      rw [h1]
      exact evalListS_acc rest acc₁ (acc₂ ++ [p.1]) p.2

theorem evalCallArgsS_acc {P : Prog} {ext : ExternOracle} {n : Nat} {env : List Bnd}
    {d : Option RunDef} :
    ∀ (ts : List (Term × Nat)) (acc₁ acc₂ : List Val) (s : St × Nat),
      (evalCallArgsS P ext n env d ts (acc₁ ++ acc₂)).run s =
        match (evalCallArgsS P ext n env d ts acc₂).run s with
        | .error e => .error e
        | .ok (vs, s') => .ok (acc₁ ++ vs, s')
  | [], _, _, _ => by unfold evalCallArgsS; rfl
  | (t, i) :: rest, acc₁, acc₂, (st, b) => by
    unfold evalCallArgsS
    cases d with
    | none =>
      dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte, MS_bind_run]
      cases (evalS P ext n env t).run (st, b) with
      | error _ => rfl
      | ok p =>
        dsimp only
        have h1 : (acc₁ ++ acc₂) ++ [p.1] = acc₁ ++ (acc₂ ++ [p.1]) := by simp [List.append_assoc]
        rw [h1]
        exact evalCallArgsS_acc rest acc₁ (acc₂ ++ [p.1]) p.2
    | some d' =>
      cases hsk : erasedAt d' i with
      | true =>
        dsimp only
        simp only [hsk, ↓reduceIte, MS_bind_run, MS_pure_run]
        have h1 : (acc₁ ++ acc₂) ++ [Val.imm .irr] = acc₁ ++ (acc₂ ++ [Val.imm .irr]) := by simp [List.append_assoc]
        rw [h1]
        exact evalCallArgsS_acc rest acc₁ (acc₂ ++ [Val.imm .irr]) (st, b)
      | false =>
        dsimp only
        simp only [hsk, Bool.false_eq_true, ↓reduceIte, MS_bind_run]
        cases (evalS P ext n env t).run (st, b) with
        | error _ => rfl
        | ok p =>
          dsimp only
          have h1 : (acc₁ ++ acc₂) ++ [p.1] = acc₁ ++ (acc₂ ++ [p.1]) := by simp [List.append_assoc]
          rw [h1]
          exact evalCallArgsS_acc rest acc₁ (acc₂ ++ [p.1]) p.2

theorem Sim_congr_scope_foot {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope₁ Scope₂ : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot₁ envFoot₂ : Nat → Nat → Prop}
    (hSc : ∀ i, Scope₁ i ↔ Scope₂ i)
    (hFt : ∀ i l, envFoot₁ i l ↔ envFoot₂ i l)
    (h : Sim P ext B st Frame NoKill NoSpend Scope₁ env aenv σ I envFoot₁) :
    Sim P ext B st Frame NoKill NoSpend Scope₂ env aenv σ I envFoot₂ := by
  have h1 : Scope₁ = Scope₂ := funext fun i => propext (hSc i)
  have h2 : envFoot₁ = envFoot₂ := funext fun i => funext fun l => propext (hFt i l)
  exact h1 ▸ h2 ▸ h

theorem PrefixSrcOk_of_SrcOk {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ₀ σ₁ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    {v : Val} {av : AVal} {ft : Nat → Prop}
    (hids₀ : ∀ (k : Nat) (ab : ABnd), aenv[k]? = some ab → ab.id < σ₀.st.size)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ₁ I envFoot)
    (hsrc : SrcOk Scope aenv σ₀ σ₁ av) :
    PrefixSrcOk Scope aenv [some (v, av, ft)] := by
  intro i v' av' ft' hg x hs k ab hsc habk hne hid
  cases i with
  | zero =>
    simp at hg; obtain ⟨rfl, rfl, rfl⟩ := hg
    rcases hsrc x hs with ⟨i', ab', _, habi', _, hid', hoo, hdeps⟩ | ⟨hge, _⟩
    · have hEq : i' = k := hsim.2.2.2.2.1 i' k ab' ab habi' habk (hid'.trans hid.symm)
      subst hEq; rw [habi'] at habk; cases habk
      exact ⟨hoo, hdeps⟩
    · have hlt := hids₀ k ab habk; omega
  | succ _ => simp at hg

theorem ArgsMatch_cons_none {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)}
    (hm : ArgsMatch args vs avs) :
    ArgsMatch (none :: args) (.imm .irr :: vs) (none :: avs) := by
  refine ⟨by simp [hm.1], by simp [hm.2.1], fun i => ?_⟩
  cases i with
  | zero => simp
  | succ k => simpa using hm.2.2 k

theorem ArgsMatch_cons_some {args : List (Option (Val × AVal × (Nat → Prop)))}
    {vs : List Val} {avs : List (Option AVal)} {v : Val} {av : AVal} {ft : Nat → Prop}
    (hm : ArgsMatch args vs avs) :
    ArgsMatch (some (v, av, ft) :: args) (v :: vs) (some av :: avs) := by
  refine ⟨by simp [hm.1], by simp [hm.2.1], fun i => ?_⟩
  cases i with
  | zero => simp
  | succ k => simpa using hm.2.2 k

theorem ArgListOk_drop_prefix {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    {pref tail : List (Option (Val × AVal × (Nat → Prop)))}
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep (pref ++ tail)) :
    ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot
      Forbid BadReg BadDep tail := by
  refine ⟨fun i v av ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
  · have h1 : (pref ++ tail)[pref.length + i]? = some (some (v, av, ft)) := by
      rw [List.getElem?_append_right (Nat.le_add_right ..)]; simpa using hg
    exact hargs.1 (pref.length + i) v av ft h1
  · have h1 : (pref ++ tail)[pref.length + i]? = some (some (v₁, av₁, ft₁)) := by
      rw [List.getElem?_append_right (Nat.le_add_right ..)]; simpa using hg₁
    have h2 : (pref ++ tail)[pref.length + j]? = some (some (v₂, av₂, ft₂)) := by
      rw [List.getElem?_append_right (Nat.le_add_right ..)]; simpa using hg₂
    exact hargs.2 (pref.length + i) (pref.length + j) v₁ v₂ av₁ av₂ ft₁ ft₂ (by omega) h1 h2

theorem ArgsSrcOk_drop_prefix {pref tail : List (Option (Val × AVal × (Nat → Prop)))}
    (h : ArgsSrcOk (pref ++ tail)) : ArgsSrcOk tail := by
  intro i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ hs₁ hs₂
  have h1 : (pref ++ tail)[pref.length + i]? = some (some (v₁, av₁, ft₁)) := by
    rw [List.getElem?_append_right (Nat.le_add_right ..)]; simpa using hg₁
  have h2 : (pref ++ tail)[pref.length + j]? = some (some (v₂, av₂, ft₂)) := by
    rw [List.getElem?_append_right (Nat.le_add_right ..)]; simpa using hg₂
  exact h (pref.length + i) (pref.length + j) v₁ v₂ av₁ av₂ ft₁ ft₂ x h1 h2 hs₁ hs₂

/-- Upgrading `onceOnly` from `aOnce` to `true` keeps `OwnFoot` identical and only weakens
the `resOnce` conclusion of `FunOkAt`. -/
theorem FunOkAt_upgrade_onceOnly {P : Prog} {ext : ExternOracle} :
    ∀ {B : Nat} {st : St} {sk : Skel} {aOnce : Bool} {Foot : Nat → Prop} {f : Val},
      FunOkAt P ext B st sk aOnce Foot f →
      FunOkAt P ext B st sk true Foot f
  | 0, _, _, _, _, _, _ => by rw [FunOkAt]; trivial
  | _ + 1, _, _, true, _, _, hf => hf
  | B + 1, st₀, sk, false, Foot, f₀, hf => by
    rw [FunOkAt] at hf ⊢
    rcases hap : arrowParts sk with ⟨m_in, dom, res, cod⟩
    simp only [hap] at hf ⊢
    intro B_call fuel st f a c Frame fRegs aRegs aOnce' aFoot hB hst hstat hFlt hloc hsh hrf
      hfBase hfOpen hfCf haBase haOpen haCf hFf hFa hfa1 hfa2 hfa3 haNum harg
    obtain ⟨hnoViol, hok⟩ := hf B_call fuel st f a c Frame fRegs aRegs aOnce' aFoot hB hst hstat hFlt
      hloc hsh hrf hfBase hfOpen hfCf haBase haOpen haCf hFf hFa hfa1 hfa2 hfa3 haNum harg
    refine ⟨hnoViol, fun rv st' B' hrun => ?_⟩
    obtain ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf, hbase, hcls, hopen, hcf,
      hrb, ⟨hroF, hroT⟩, huniq⟩ := hok rv st' B' hrun
    refine ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf, hbase, hcls, hopen, hcf,
      hrb, ⟨?_, ?_⟩, huniq⟩
    · intro hfalse
      have hcodF : isArrowSkel cod = false := by simpa using hfalse
      exact hroF (by simp [hcodF])
    · intro htrue
      by_cases hprev : (isArrowSkel cod && (false || m_in.isUnique || m_in.usage == .once)) = true
      · exact hroT hprev
      · obtain ⟨_, hfun⟩ := hroF (Bool.eq_false_iff.mpr hprev)
        exact ⟨fun _ => False, fun _ h => False.elim h, FunOkAt_weaken_onceOnly hfun⟩

/-- Push a single closure parameter `a` bound via `bindAt P fuel s_c p.mode p.cls a` into
`Sim` + `EnvTaintOk` + `EnvNoReachForbid` on `(env_call, aenv, σ_open, I_open)` for `ATerm.lam`. -/
theorem clo_bindParam_push {P : Prog} {ext : ExternOracle} {B fuel s_a s_c : Nat}
    {st_call : St} {Frame_call NoKill_call Scope : Nat → Prop}
    {env_call : List Bnd} {aenv : List ABnd} {σ_open : AState} {I_open : Interp}
    {p : Param} {res : ResultMode} {c_app : Cls} {f_call a : Val}
    {aRegs : List Nat} {aOnce : Bool} {aFoot : Nat → Prop}
    (hst_call : StOk P ext B st_call)
    (hstat_call : ∀ l, StaticStrLoc st_call l → Frame_call l)
    (hFlt_call : ∀ l, Frame_call l → l < st_call.heap.objs.size)
    (hs_a_lt : s_a < σ_open.nextRegion)
    (hI_sa : I_open.reg s_a = [s_c])
    (hI_1 : ∀ c, c ∈ aRegs → c < s_c → c ∈ I_open.reg 1)
    (hsim_open : Sim P ext B { st_call with nextRegion := s_c + 1, regions := s_c :: st_call.regions }
      Frame_call NoKill_call (fun _ => False) Scope env_call aenv σ_open I_open (fun _ _ => False))
    (hs_c_eq : s_c = st_call.nextRegion)
    (henvReachF : ∀ (i : Nat) (b_c : Bnd), Scope i → env_call[i]? = some b_c →
      ∀ l, Reach st_call.heap b_c.val l → Reach st_call.heap f_call l)
    (henvTaint_open : EnvTaintOk Scope env_call aenv
      { st_call with nextRegion := s_c + 1, regions := s_c :: st_call.regions } I_open)
    (haBase : ValBaseOk st_call a)
    (haOpen : DeepOpenUnder st_call.heap st_call.regions aRegs a)
    (haCf : CtorFieldsOk P ext B st_call a)
    (hFa : ∀ l, Frame_call l → ¬ aFoot l)
    (hfa2 : ∀ l, Reach st_call.heap f_call l → ¬ aFoot l)
    (haNum : (∀ l, aFoot l → Reach st_call.heap a l ∧ ¬ NumLoc st_call.heap l) ∧
      (p.mode = .erased → NoOnceCell st_call.heap a))
    (harg : p.mode ≠ .erased →
      (p.mode.usage = .once → FunOkAt P ext B st_call p.skel aOnce aFoot a) ∧
      (p.mode.usage ≠ .once →
        NoOnceCell st_call.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
        FunOkAt P ext B st_call p.skel false (fun _ => False) a) ∧
      (p.mode.isUnique = true →
        OwnTreeFull P st_call.heap a ∧
        (∀ l, OwnReach P st_call.heap a l → ¬ Frame_call l ∧ ¬ Reach st_call.heap f_call l) ∧
        (p.mode.isBorrowed = false → DeepOpenUnder st_call.heap st_call.regions [] a)) ∧
      ((res = .unique ∧ c_app = .val ∧ (p.mode = .many ∨ p.mode = .once)) →
        DeepOpenUnder st_call.heap st_call.regions [] a))
    (henvOwnDisjA : ∀ (i : Nat) (b_c : Bnd) (ab : ABnd), Scope i → env_call[i]? = some b_c →
      aenv[i]? = some ab → ab.mode ≠ .erased →
      ActiveVal σ_open (effVal ab) → Transferable σ_open NoKill_call (effVal ab) →
      ∀ l, OwnReach P st_call.heap b_c.val l → ¬ Reach st_call.heap a l) :
    let st_open : St := { st_call with nextRegion := s_c + 1, regions := s_c :: st_call.regions }
    let pv := paramVal p s_a
    let σ_push := (σ_open.pushBnd pv (p.mode.usage == .once)).2
    let ab_new : ABnd := { id := σ_open.st.size, mode := p.mode, val := pv }
    let Forbid_call : Nat → Prop := fun l =>
      l < st_call.heap.objs.size ∧ ¬ Reach st_call.heap f_call l ∧ ¬ StaticStrLoc st_call l ∧
      ((res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased)) ∨ ¬ Reach st_call.heap a l)
    let BadReg_call : Nat → Prop :=
      if res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased)
      then (· = s_a) else fun _ => False
    (bindAt P fuel s_c p.mode p.cls a).run st_open = .error .stuck ∨
    (bindAt P fuel s_c p.mode p.cls a).run st_open = .error .outOfFuel ∨
    ∃ bnd st₂ bFoot, (bindAt P fuel s_c p.mode p.cls a).run st_open = .ok (bnd, st₂) ∧
      st₂.regions = st_open.regions ∧ st₂.nextRegion = st_open.nextRegion ∧
      st₂.statics = st_call.statics ∧ st₂.strs = st_call.strs ∧
      st_call.heap.objs.size ≤ st₂.heap.objs.size ∧ st_call.heap.nextCap ≤ st₂.heap.nextCap ∧
      PreservesLocs Frame_call st_call.heap st₂.heap ∧
      PreservesLocs (StaticStrLoc st_call) st_call.heap st₂.heap ∧
      PreservesOnceShell st_call.heap st₂.heap ∧
      StaticStrFresh st_call st₂ ∧
      StOk P ext B st₂ ∧
      Sim P ext B st₂ Frame_call NoKill_call (fun _ => False) (shiftScope Scope)
        (bnd :: env_call) (ab_new :: aenv) σ_push I_open
        (fun i => match i with | 0 => bFoot | _k + 1 => fun _ => False) ∧
      EnvTaintOk (shiftScope Scope) (bnd :: env_call) (ab_new :: aenv) st₂ I_open ∧
      EnvNoReachForbid st₂ (shiftScope Scope) (bnd :: env_call) (ab_new :: aenv) σ_push
        Forbid_call BadReg_call (fun _ => False) := by
  classical
  intro st_open pv σ_push ab_new Forbid_call BadReg_call
  have hokOpen := hsim_open.2.1
  have hstOpen : StOk P ext B st_open := by
    subst hs_c_eq; exact StOk_openRegion hst_call
  have hrfOpen : RegsFuture st_call st_open := by
    subst hs_c_eq; exact RegsFuture.openRegion st_call
  have haBaseO : ValBaseOk st_open a :=
    ValBaseOk_congr (st := st_call) (st' := st_open) (PreservesLocs.refl _ _) hrfOpen.1 haBase
  have haCfO : CtorFieldsOk P ext B st_open a :=
    CtorFieldsOk_congr haBase.1 (PreservesLocs.refl _ _) hrfOpen haCf
  have haOpenO : DeepOpenUnder st_open.heap st_open.regions (I_open.reg 1) a := by
    intro u hu r hr hopen
    rcases List.mem_cons.mp hopen with rfl | hmem
    · exact False.elim (Nat.lt_irrefl _ (hs_c_eq ▸ haBase.2.2.2 u hu _ hr))
    · exact hI_1 r (haOpen u hu r hr hmem) (hs_c_eq ▸ haBase.2.2.2 u hu r hr)
  -- Case 1: `p.mode = .erased`
  by_cases hpEr : p.mode = .erased
  · have hrun : (bindAt P fuel s_c p.mode p.cls a).run st_open = .ok (⟨.imm .irr, .erased⟩, st_open) := by
      rw [hpEr]; unfold bindAt; rfl
    have hpvEq : pv = { cls := .irr } := by simp [pv, paramVal, hpEr]
    have hU : (Usage.erased == Usage.once) = false := rfl
    have hsimP : Sim P ext B st_open Frame_call NoKill_call (fun _ => False) (shiftScope Scope)
        (⟨.imm .irr, .erased⟩ :: env_call) (ab_new :: aenv) σ_push I_open
        (fun i => match i with | 0 => fun _ => False | k + 1 => fun _ => False) := by
      have h1 := Sim_congr_scope_foot (Scope₂ := shiftScope Scope)
        (envFoot₂ := fun i => match i with | 0 => fun _ => False | k + 1 => fun _ => False)
        (fun i => by cases i <;> exact Iff.rfl)
        (fun i _ => by cases i <;> exact Iff.rfl)
        (Sim_push_erased hsim_open)
      simpa [σ_push, ab_new, pv, hpvEq, hpEr, hU, AState.pushBnd, BinderMode.usage] using h1
    have henvNRF : EnvNoReachForbid st_open (shiftScope Scope) (⟨.imm .irr, .erased⟩ :: env_call)
        (ab_new :: aenv) σ_push Forbid_call BadReg_call (fun _ => False) := by
      intro i b' ab' hsc hbi habi hne ha _ _ l hr _ _ hForb
      cases i with
      | zero => simp at habi; subst habi; exact absurd hpEr hne
      | succ k =>
        exact hForb.2.1 (henvReachF k b' hsc (by simpa using hbi) l hr)
    right; right
    refine ⟨⟨.imm .irr, .erased⟩, st_open, fun _ => False, hrun, rfl, rfl, rfl, rfl,
      Nat.le_refl _, Nat.le_refl _, PreservesLocs.refl _ _, PreservesLocs.refl _ _,
      PreservesOnceShell.refl _, StaticStrFresh.refl _, hstOpen, hsimP,
      henvTaint_open.cons_erased hpEr, henvNRF⟩
  -- Case 2: `p.mode ≠ .erased`
  obtain ⟨hOnceArg, hNonOnceArg, hUniqArg, _⟩ := harg hpEr
  have h1lt : 1 < σ_open.nextRegion := by have := hokOpen.2.2.1; omega
  have hpvRegsLt : ∀ r ∈ pv.regs, r < σ_open.nextRegion := by
    intro r hr
    unfold pv paramVal at hr
    cases hm : p.mode with
    | erased => exact absurd hm hpEr
    | many =>
      simp only [hm] at hr
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact h1lt
      · cases hr
    | borrowed =>
      simp only [hm] at hr
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> first | exact hs_a_lt | exact h1lt
      · cases hr
    | unique => simp only [hm] at hr; cases hr
    | uniqueBorrowed =>
      simp only [hm] at hr
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> first | exact hs_a_lt | exact h1lt
      · cases hr
    | once =>
      simp only [hm] at hr
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact h1lt
      · cases hr
    | onceBorrowed =>
      simp only [hm] at hr
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> first | exact hs_a_lt | exact h1lt
      · cases hr
  have hpvSrcNone : pv.src = none := by unfold pv paramVal; cases p.mode <;> rfl
  have hpvDepsNil : pv.deps = [] := by unfold pv paramVal; cases p.mode <;> rfl
  have hpvOONil : pv.onceOnly = false := by unfold pv paramVal; cases p.mode <;> rfl
  have hpvSkel : pv.skel = p.skel := by
    unfold pv paramVal; cases hm : p.mode <;> simp [hm] at hpEr ⊢
  have hpvCls : pv.cls = p.cls := by
    unfold pv paramVal; cases hm : p.mode <;> simp [hm] at hpEr ⊢
  have hconfO : p.mode.isUnique = true → p.mode.isBorrowed = false → OpenUnder st_open.regions [] a := by
    intro hu hnb r hr hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact False.elim (Nat.lt_irrefl _ (hs_c_eq ▸ haBase.2.2.2 a (HeldBy.refl _ _) _ hr))
    · exact (hUniqArg hu).2.2 hnb a (HeldBy.refl _ _) r hr hmem'
  -- Effective `aOnce'` / `aFoot'` satisfying `aOnce' = false → ∀ l, ¬ aFoot' l`
  let aOnce' : Bool := p.mode.usage == .once
  let aFoot' : Nat → Prop := if p.mode.usage == .once then aFoot else fun _ => False
  have hFunA' : FunOkAt P ext B st_open p.skel aOnce' aFoot' a := by
    by_cases ho : p.mode.usage = .once
    · have hob : (p.mode.usage == .once) = true := by rw [ho]; rfl
      have h1 : aOnce' = true := hob
      have h2 : aFoot' = aFoot := by funext l; simp [aFoot', hob]
      rw [h1, h2]
      exact FunOkAt_upgrade_onceOnly
        (FunOkAt_preserve_locs (st₀ := st_call) (st₁ := st_open) (PreservesLocs.refl _ _) hrfOpen (hOnceArg ho))
    · have hob : (p.mode.usage == .once) = false := beq_false_of_ne ho
      have h1 : aOnce' = false := hob
      have h2 : aFoot' = fun _ => False := by funext l; simp [aFoot', hob]
      rw [h1, h2]
      exact FunOkAt_preserve_locs (st₀ := st_call) (st₁ := st_open) (PreservesLocs.refl _ _) hrfOpen (hNonOnceArg ho).2.2.2
  have hFootF' : aOnce' = false → ∀ l, ¬ aFoot' l := fun h l hl => by
    dsimp only [aOnce'] at h; dsimp only [aFoot'] at hl; rw [h] at hl; exact hl
  have hFootOk' : p.mode.usage = .once → ∀ l, aFoot' l → Reach st_open.heap a l ∧ ¬ StaticStrLoc st_open l := by
    intro ho l hl
    have hob : (p.mode.usage == .once) = true := by rw [ho]; rfl
    dsimp only [aFoot'] at hl; simp only [hob, ↓reduceIte] at hl
    exact ⟨(haNum.1 l hl).1, fun hss => hFa l (hstat_call l hss) hl⟩
  rcases bindAt_sound (P := P) (ext := ext) (B := B) (st := st_open) (fuel := fuel) (s := s_c)
      (m := p.mode) (c := p.cls) (sk := p.skel) (onceOnly := aOnce') (Foot := aFoot') (v := a)
      hstOpen (Nat.lt_succ_self s_c)
      (fun _ => haBaseO) (fun _ => haCfO) (fun _ hnu => (hNonOnceArg hnu).1) (fun _ => hFunA')
      (fun hnu => beq_false_of_ne hnu) hFootF' hFootOk'
      (fun hu => (hUniqArg hu).1) (fun hu l hor hss => ((hUniqArg hu).2.1 l hor).1 (hstat_call l hss))
      hconfO with hSt | hOOF |
    ⟨bnd, st₂, hrun, hmode, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, _, hpres₂, honce₂, hssf₂,
     hst₂, hbase₂, hcf₂, _, hplain₂, _, htree₂, _, hdou₂, hreach₂, hown₂⟩
  · exact Or.inl hSt
  · exact Or.inr (Or.inl hOOF)
  · right; right
    have hrf₂ : RegsFuture st_open st₂ := RegsFuture.same_regions (hnr₂ ▸ Nat.le_refl _) hrg₂
    have hIok₂ : InterpOk σ_open st₂ I_open :=
      ⟨fun r hr c hc => Nat.lt_of_lt_of_le (hsim_open.2.2.1.1 r hr c hc) hrf₂.1,
       fun c hc => hsim_open.2.2.1.2 c (hrg₂ ▸ hc)⟩
    have hpFrame₂ : PreservesLocs Frame_call st_call.heap st₂.heap :=
      hpres₂.mono fun l hF => ⟨hFlt_call l hF, fun hu hor => ((hUniqArg hu).2.1 l hor).1 hF⟩
    have hpSS₂ : PreservesLocs (StaticStrLoc st_call) st_call.heap st₂.heap :=
      hpFrame₂.mono fun _ h => hstat_call _ h
    have hpEnv₂ : PreservesActiveEnv Scope env_call aenv σ_open st_open.heap st₂.heap :=
      fun i b_c ab hsc hbi habi hne haB =>
        hpres₂.mono fun l hl =>
          ⟨(((hsim_open.2.2.2.2.2.1 i b_c ab hsc hbi habi).2 hne).2.2.2.2.2 haB).1.1.reach_lt_size hl,
           fun hu hor => ((hUniqArg hu).2.1 l hor).2 (henvReachF i b_c hsc hbi l hl)⟩
    have hsim₂ := Sim_step (Nat.le_refl B) (AStateLe.refl _) hokOpen hIok₂ hrf₂ honce₂ hssf₂
      (fun _ _ _ h => h) hpEnv₂ hsim_open
    have henvTaint₂ : EnvTaintOk Scope env_call aenv st₂ I_open :=
      henvTaint_open.step hrg₂ (hnr₂ ▸ Nat.le_refl _)
    -- `DeepOpenUnder st₂.heap st₂.regions (I_open.regsOf pv.regs) bnd.val`
    have hdouPv : DeepOpenUnder st₂.heap st₂.regions (I_open.regsOf pv.regs) bnd.val := by
      by_cases hcV : p.cls = .val
      · by_cases huB : p.mode = .unique
        · have hregsNil : pv.regs = [] := by simp [pv, paramVal, huB]
          rw [hregsNil, Interp.regsOf_nil]
          have haNil : DeepOpenUnder st_open.heap st_open.regions [] a := by
            intro u hu' r hr' hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact False.elim (Nat.lt_irrefl _ (hs_c_eq ▸ haBase.2.2.2 u hu' _ hr'))
            · exact (hUniqArg (by rw [huB]; rfl)).2.2 (by rw [huB]; rfl) u hu' r hr' hmem'
          have h1 := hdou₂ st_open.regions [] (fun _ => haNil)
          simpa [hrg₂, huB, BinderMode.isBorrowed] using h1
        · have hregsEq : I_open.regsOf pv.regs =
              if p.mode.isBorrowed then s_c :: I_open.reg 1 else I_open.reg 1 := by
            have hvv : (Cls.val == Cls.val) = true := rfl
            cases hm : p.mode <;>
              simp [hm, pv, paramVal, hcV, hvv, Interp.regsOf, List.flatMap, hI_sa, BinderMode.isBorrowed] at hpEr huB ⊢
          rw [hregsEq, hrg₂]
          exact hdou₂ st_open.regions (I_open.reg 1) (fun _ => haOpenO)
      · have hregsNil : pv.regs = [] := by
          unfold pv paramVal
          have hcf : (p.cls == .val) = false := by
            cases hc : p.cls with
            | val => exact absurd hc hcV
            | _ => rfl
          cases p.mode <;> simp [hcf]
        rw [hregsNil, Interp.regsOf_nil]
        by_cases hu : p.mode.usage = .once
        · have hOnceSpec : ∃ base loc cap, bnd.val = .ref loc cap base.taint ∧
              st₂.heap.objs[loc]? = some ⟨.once base false, cap⟩ ∧
              DeepLive st₂.heap base ∧ ClsOk st₂.heap p.cls base := by
            rcases bindAt_spec (P := P) (fuel := fuel) (s := s_c) (m := p.mode) (c := p.cls) (v := a)
                hstOpen.1 (fun _ => haBaseO.1) (fun _ => haBaseO.2.1)
                (fun h => (hUniqArg h).1) hconfO with hS | hO |
              ⟨b0, s0, hr0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ho0, _, _, _, _, _⟩
            · rw [hS] at hrun; cases hrun
            · rw [hO] at hrun; cases hrun
            · have hEq := Except.ok.inj (hr0.symm.trans hrun)
              cases congrArg Prod.fst hEq; cases congrArg Prod.snd hEq
              obtain ⟨base, loc, cap, hbvEq, _, _, ho, hdlB, hclsB, _, _⟩ := ho0 hu
              exact ⟨base, loc, cap, hbvEq, ho, hdlB, hclsB⟩
          obtain ⟨base, loc, cap, hbvEq, ho, hdlB, hclsB⟩ := hOnceSpec
          have hnvB : NonValSafe st₂.heap base :=
            ClsSafe.to_nonValSafe hcV (ClsSafe.of_clsOk hclsB) hdlB.self.1
          have hbtNil : base.taint = [] := by
            rcases hnvB with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl, _, _, _⟩ <;> rfl
          intro w hw r hrW _
          rw [hbvEq] at hw
          rcases hw with rfl | ⟨l0, o0, hr0, ho0, hm0⟩
          · rw [hbtNil] at hrW; cases hrW
          · cases hr0 with
            | here =>
              rw [ho] at ho0; cases ho0
              simp only [Cell.vals, List.mem_singleton] at hm0; subst hm0
              rw [hbtNil] at hrW; cases hrW
            | step ho2 hm2 hr2 =>
              rw [ho] at ho2; cases ho2
              simp only [Cell.vals, List.mem_singleton] at hm2; subst hm2
              rcases hnvB with ⟨_, rfl⟩ | ⟨_, _, o', _, rfl, ho', _, hn'⟩
              · cases hr2
              · cases hr2 with
                | here => rw [ho'] at ho0; cases ho0; rw [hn'] at hm0; cases hm0
                | step ho3 hm3 _ => rw [ho'] at ho3; cases ho3; rw [hn'] at hm3; cases hm3
        · exact (ClsSafe.to_nonValSafe hcV (hplain₂ hpEr hu).1 hbase₂.1.self.1).deepOpenUnder_nil
    -- Pairwise env disjointness for `(bnd, pv)` against existing `env_call`
    have hEnvDisjNew : ∀ (i : Nat) (b₂ : Bnd) (ab₂ : ABnd), Scope i → env_call[i]? = some b₂ →
        aenv[i]? = some ab₂ → ab₂.mode ≠ .erased →
        (ActiveVal σ_open (effVal ab₂) → Transferable σ_open NoKill_call (effVal ab₂) →
          ∀ l, OwnReach P st₂.heap b₂.val l → ¬ Reach st₂.heap bnd.val l) ∧
        (ActiveVal σ_open (effVal ab₂) → FootActive σ_open (effVal ab₂) →
          ∀ l, False → ¬ Reach st₂.heap bnd.val l) := by
      intro i b₂ ab₂ hsc hbi₂ habi₂ hne₂
      have hv₂ := ((hsim_open.2.2.2.2.2.1 i b₂ ab₂ hsc hbi₂ habi₂).2 hne₂).2
      refine ⟨fun haB htrB l horB hrV => ?_, fun _ _ _ h => False.elim h⟩
      have hpB := hpEnv₂ i b₂ ab₂ hsc hbi₂ habi₂ hne₂ haB
      have horB0 : OwnReach P st_call.heap b₂.val l := (OwnReach_congr hpB l).mp horB
      rcases hreach₂ l hrV with hge | ⟨_, hrA⟩
      · exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 haB).1.1.reach_lt_size (OwnReach_toReach horB0))
      · exact henvOwnDisjA i b₂ ab₂ hsc hbi₂ habi₂ hne₂ haB htrB l horB0 hrA
    -- `EnvNoReachForbid` on `(bnd :: env_call)`
    have hNewNRF : NoReachForbid st₂ Forbid_call BadReg_call (fun _ => False) (effVal ab_new) bnd.val := by
      intro hregs _ l hrB hnotSS₂ hnotNum₂ hForb
      rcases hreach₂ l hrB with hge | ⟨_, hrA⟩
      · exact Nat.not_lt_of_ge hge hForb.1
      · rcases hForb.2.2.2 with ⟨hru, hrc, hbrOrEr⟩ | hnotA
        · rcases hbrOrEr with hbr | her
          · by_cases hcV : p.cls = .val
            · have hsaIn : s_a ∈ (effVal ab_new).regs := by
                change s_a ∈ pv.regs; unfold pv paramVal
                have hcv' : (p.cls == .val) = true := by rw [hcV]; rfl
                simp only [hcv', ↓reduceIte]
                cases hm : p.mode <;> rw [hm] at hbr <;>
                  first | contradiction | (dsimp only; exact List.mem_cons_self)
              have hbadSa : BadReg_call s_a := by
                dsimp only [BadReg_call]
                split
                · rfl
                · rename_i hn; exact False.elim (hn ⟨hru, hrc, Or.inl hbr⟩)
              exact hregs s_a hsaIn hbadSa
            · by_cases hu : p.mode.usage = .once
              · obtain ⟨_, hneValR, _⟩ := bindAt_once_foot hstOpen hu haBaseO hFunA' hFootF'
                  (fun l' hl' => ⟨(hFootOk' hu l' hl').1, (hFootOk' hu l' hl').2, by
                    have hob : (p.mode.usage == .once) = true := by rw [hu]; rfl
                    dsimp only [aFoot'] at hl'; rw [hob] at hl'; exact (haNum.1 l' hl').2⟩) hrun
                rcases hneValR hcV l hrB with hge' | hnum'
                · exact Nat.not_lt_of_ge hge' hForb.1
                · exact hnotNum₂ hnum'
              · have hnv := ClsSafe.to_nonValSafe hcV (hplain₂ hpEr hu).1 hbase₂.1.self.1
                exact hnotNum₂ (hnv.reach_numLoc hrB)
          · exact absurd her hpEr
        · exact hnotA hrA
    have henvNRF_all : EnvNoReachForbid st₂ (shiftScope Scope) (bnd :: env_call) (ab_new :: aenv)
        σ_push Forbid_call BadReg_call (fun _ => False) := by
      intro i b' ab' hsc' hbi' habi' hne' ha'
      cases i with
      | zero =>
        simp at hbi' habi'; subst hbi'; subst habi'; exact hNewNRF
      | succ k =>
        intro _ _ l hrK _ _ hForb
        have hbiK : env_call[k]? = some b' := by simpa using hbi'
        have habiK : aenv[k]? = some ab' := by simpa using habi'
        have hvK := ((hsim_open.2.2.2.2.2.1 k b' ab' hsc' hbiK habiK).2 hne').2
        have hleP : AStateLe σ_open σ_push := (hokOpen.pushBnd pv (p.mode.usage == .once)).2
        have haO := ActiveVal.of_AStateLe hokOpen hleP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha'
        have hpK := hpEnv₂ k b' ab' hsc' hbiK habiK hne' haO
        exact hForb.2.1 (henvReachF k b' hsc' hbiK l ((Reach_congr hpK l).mp hrK))
    have hNewActive : ActiveVal σ_push (effVal ab_new) := by
      have hszEq : σ_push.st.size = σ_open.st.size + 1 := by simp [σ_push, AState.pushBnd]
      refine ⟨fun d hd => ?_, fun _ d hd _ => ?_⟩
      · simp only [effVal, ab_new, hpvDepsNil, List.mem_cons, List.mem_filter, List.not_mem_nil, false_and, or_false] at hd
        subst hd
        refine ⟨by omega, ?_⟩
        dsimp only [σ_push, AState.pushBnd]; rw [Array.getElem?_push_size]
        split <;> intro h <;> cases h
      · simp only [effVal, ab_new, hpvDepsNil, List.mem_cons, List.mem_filter, List.not_mem_nil, false_and, or_false] at hd
        subst hd
        dsimp only [σ_push, AState.pushBnd]; rw [hokOpen.2.1, Array.getElem?_push_size]
    -- Split `.once` vs non-`.once` to push `(bnd, ab_new)` into `Sim`
    by_cases hpOnce : p.mode.usage = .once
    · have hpOnceB : (p.mode.usage == .once) = true := by rw [hpOnce]; rfl
      obtain ⟨hsp₂, _, loc, bFoot, hlocGe, hbFootSub, hbFootOk, hfun₂⟩ :=
        bindAt_once_foot hstOpen hpOnce haBaseO hFunA' hFootF'
          (fun l' hl' => ⟨(hFootOk' hpOnce l' hl').1, (hFootOk' hpOnce l' hl').2, by
            dsimp only [aFoot'] at hl'; rw [hpOnceB] at hl'; exact (haNum.1 l' hl').2⟩) hrun
      have hbFootNotF : ∀ l, bFoot l → ¬ Frame_call l := fun l hl hF => by
        rcases hbFootSub l hl with rfl | hfa
        · exact Nat.not_lt_of_ge hlocGe (hFlt_call _ hF)
        · dsimp only [aFoot'] at hfa; rw [hpOnceB] at hfa; exact hFa l hF hfa
      have hbFootNotEnv : ∀ (i : Nat) (b₂ : Bnd) (ab₂ : ABnd), Scope i → env_call[i]? = some b₂ →
          aenv[i]? = some ab₂ → ab₂.mode ≠ .erased → ActiveVal σ_open (effVal ab₂) →
          ∀ l, bFoot l → ¬ Reach st₂.heap b₂.val l := by
        intro i b₂ ab₂ hsc hbi₂ habi₂ hne₂ haB l hl hrB₂
        have hpB := hpEnv₂ i b₂ ab₂ hsc hbi₂ habi₂ hne₂ haB
        have hrB0 := (Reach_congr hpB l).mp hrB₂
        rcases hbFootSub l hl with rfl | hfa
        · have hv₂ := ((hsim_open.2.2.2.2.2.1 i b₂ ab₂ hsc hbi₂ habi₂).2 hne₂).2
          exact Nat.not_lt_of_ge hlocGe ((hv₂.2.2.2.2 haB).1.1.reach_lt_size hrB0)
        · dsimp only [aFoot'] at hfa; rw [hpOnceB] at hfa
          exact hfa2 l (henvReachF i b₂ hsc hbi₂ l hrB0) hfa
      have hsimP0 := Sim_push_once_bnd (b := bnd) (bv := pv) (bFoot := bFoot)
        (hmode.symm ▸ hpOnce) hpvRegsLt (fun _ h => by rw [hpvDepsNil] at h; cases h)
        hsp₂ hbase₂ hdouPv hcf₂
        (fun l hl => ⟨(hbFootOk l hl).1, hbFootNotF l hl, (hbFootOk l hl).2.1, (hbFootOk l hl).2.2⟩)
        (hpvSkel.symm ▸ hfun₂) hbFootNotEnv
        (fun i b₁ ab₁ hsc hbi₁ habi₁ hne₁ =>
          ⟨fun ha₁ htr₁ _ _ => (hEnvDisjNew i b₁ ab₁ hsc hbi₁ habi₁ hne₁).1 ha₁ htr₁,
           fun ha₁ hft₁ _ => (hEnvDisjNew i b₁ ab₁ hsc hbi₁ habi₁ hne₁).2 ha₁ hft₁⟩)
        hsim₂
      have hsimP : Sim P ext B st₂ Frame_call NoKill_call (fun _ => False) (shiftScope Scope)
          (bnd :: env_call) (ab_new :: aenv) σ_push I_open
          (fun i => match i with | 0 => bFoot | k + 1 => fun _ => False) := by
        have h1' := Sim_congr_scope_foot (Scope₂ := shiftScope Scope)
          (envFoot₂ := fun i => match i with | 0 => bFoot | k + 1 => fun _ => False)
          (fun i => by cases i <;> exact Iff.rfl)
          (fun i _ => by cases i <;> exact Iff.rfl) hsimP0
        simpa [σ_push, ab_new, hpOnceB, hmode, AState.pushBnd] using h1'
      have hvNew : VSim P ext B st₂ Frame_call NoKill_call (fun _ => False) σ_push I_open bFoot (effVal ab_new) bnd.val :=
        ((hsimP.2.2.2.2.2.1 0 bnd ab_new trivial rfl rfl).2 hpEr).2
      exact ⟨bnd, st₂, bFoot, hrun, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
        hpFrame₂, hpSS₂, honce₂, hssf₂, hst₂, hsimP,
        henvTaint₂.cons_active hvNew hNewActive, henvNRF_all⟩
    · have hpOnceF : (p.mode.usage == .once) = false := beq_false_of_ne hpOnce
      obtain ⟨hcls₂, hno₂, hfun₂⟩ := hplain₂ hpEr hpOnce
      have hVSimPv : VSim P ext B st₂ Frame_call NoKill_call (fun _ => False) σ_open I_open (fun _ => False) pv bnd.val := by
        refine ⟨hpvRegsLt, (fun _ h => by rw [hpvDepsNil] at h; cases h),
          (fun _ hs => by rw [hpvSrcNone] at hs; cases hs),
          (fun _ ⟨_, hs, _⟩ => by rw [hpvSrcNone] at hs; cases hs), fun _ => ?_⟩
        refine ⟨hbase₂, hdouPv, hcf₂,
          (fun _ hneC => ClsSafe.to_nonValSafe (hpvCls ▸ hneC) hcls₂ hbase₂.1.self.1),
          (fun _ => ⟨hno₂, fun _ h => h, hpvSkel.symm ▸ hfun₂⟩),
          (fun hoo => by rw [hpvOONil] at hoo; cases hoo),
          (fun ⟨_, hs, _⟩ => by rw [hpvSrcNone] at hs; cases hs), fun htr => ?_⟩
        have hu : p.mode.isUnique = true := by
          have hown := htr.2.1
          dsimp only [pv, paramVal] at hown
          cases hm : p.mode <;> simp [hm, BinderMode.isUnique] at hown hpEr ⊢
        refine ⟨htree₂ hu, fun l hor => ?_⟩
        rcases hown₂ l hor with hge | ⟨_, hor0⟩
        · exact ⟨fun hF => Nat.not_lt_of_ge hge (hFlt_call l hF), fun hss =>
            Nat.not_lt_of_ge hge (StOk_staticStrLoc_lt hstOpen (StaticStrLoc_of_preserves_outside hstat₂ hstr₂ hpSS₂ l hss))⟩
        · exact ⟨((hUniqArg hu).2.1 l hor0).1, fun hss =>
            ((hUniqArg hu).2.1 l hor0).1 (hstat_call l (StaticStrLoc_of_preserves_outside hstat₂ hstr₂ hpSS₂ l hss))⟩
      have hDisjPv : ValEnvDisj P st₂ NoKill_call Scope env_call aenv σ_open (fun _ _ => False) (fun _ => False) pv bnd.val := by
        intro i b₂ ab₂ hsc hbi₂ habi₂ hne₂
        refine ⟨?_, (fun haB htrB _ _ => (hEnvDisjNew i b₂ ab₂ hsc hbi₂ habi₂ hne₂).1 haB htrB),
          (fun _ _ _ _ _ h => False.elim h), (fun _ _ _ _ _ h => False.elim h),
          (fun _ _ _ _ h => False.elim h),
          (fun hs => by rw [hpvSrcNone] at hs; cases hs),
          (fun _ hs => by rw [hpvSrcNone] at hs; cases hs)⟩
        intro _ htr haB _ l hor hrB₂
        have hu : p.mode.isUnique = true := by
          have hown := htr.2.1
          dsimp only [pv, paramVal] at hown
          cases hm : p.mode <;> simp [hm, BinderMode.isUnique] at hown hpEr ⊢
        have hpB := hpEnv₂ i b₂ ab₂ hsc hbi₂ habi₂ hne₂ haB
        have hrB0 := (Reach_congr hpB l).mp hrB₂
        rcases hown₂ l hor with hge | ⟨_, hor0⟩
        · have hv₂ := ((hsim_open.2.2.2.2.2.1 i b₂ ab₂ hsc hbi₂ habi₂).2 hne₂).2
          exact Nat.not_lt_of_ge hge ((hv₂.2.2.2.2 haB).1.1.reach_lt_size hrB0)
        · exact ((hUniqArg hu).2.1 l hor0).2 (henvReachF i b₂ hsc hbi₂ l hrB0)
      have hsimP0 := Sim_push_bnd (b := bnd) (bv := pv) (bFoot := fun _ => False)
        hpvSrcNone (fun _ _ _ h => h) (fun h => absurd (hmode ▸ h) hpOnce)
        (fun h => absurd (hmode ▸ h) hpOnce) (fun h => absurd (hmode ▸ h) hpOnce)
        hVSimPv hDisjPv hsim₂
      have hsimP : Sim P ext B st₂ Frame_call NoKill_call (fun _ => False) (shiftScope Scope)
          (bnd :: env_call) (ab_new :: aenv) σ_push I_open
          (fun i => match i with | 0 => fun _ => False | k + 1 => fun _ => False) := by
        have h1' := Sim_congr_scope_foot (Scope₂ := shiftScope Scope)
          (envFoot₂ := fun i => match i with | 0 => fun _ => False | k + 1 => fun _ => False)
          (fun i => by cases i <;> exact Iff.rfl)
          (fun i _ => by cases i <;> exact Iff.rfl) hsimP0
        simpa [σ_push, ab_new, hpOnceF, hmode, AState.pushBnd] using h1'
      have hvNew : VSim P ext B st₂ Frame_call NoKill_call (fun _ => False) σ_push I_open (fun _ => False) (effVal ab_new) bnd.val :=
        ((hsimP.2.2.2.2.2.1 0 bnd ab_new trivial rfl rfl).2 hpEr).2
      exact ⟨bnd, st₂, fun _ => False, hrun, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
        hpFrame₂, hpSS₂, honce₂, hssf₂, hst₂, hsimP,
        henvTaint₂.cons_active hvNew hNewActive, henvNRF_all⟩

/-! ## 4. Mutual Soundness Predicates and Heavy Constructor Case Lemmas -/

/-- Runtime evaluation of the major premise of a `Term.case`, matching `evalS` verbatim. -/
def evalMajorS (P : Prog) (ext : ExternOracle) (fuel : Nat) (env : List Bnd) : Term → MS Val
  | .var j mc => liftM do
      let some b := env[j]? | stuckM
      if b.mode == .erased then violate .erasedRead
      live b.val
      let v ← conform mc b.val
      if b.mode.isUnique then transfer P fuel b.mode.isBorrowed v else pure v
  | t => evalS P ext fuel env t

/-- Unified postcondition for term/call/major/alt soundness steps. -/
def TermPost (P : Prog) (ext : ExternOracle) (B₀ : Nat) (st : St)
    (Frame NoKill NoSpend Scope : Nat → Prop) (env : List Bnd) (aenv : List ABnd)
    (σ σ' : AState) (I : Interp) (envFoot : Nat → Nat → Prop)
    (Forbid BadReg BadDep : Nat → Prop) (r : AVal) (m : MS Val) : Prop :=
  (∀ k, m.run (st, B₀) ≠ .error (.violation k)) ∧
  ∀ rv st' B', m.run (st, B₀) = .ok (rv, (st', B')) →
    ∃ rvFoot : Nat → Prop,
      B' ≤ B₀ ∧
      StOk P ext B' st' ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧
      st.heap.nextCap ≤ st'.heap.nextCap ∧
      st'.regions = st.regions ∧
      st.nextRegion ≤ st'.nextRegion ∧
      ArrayExtends st.statics st'.statics ∧
      ArrayExtends st.strs st'.strs ∧
      PreservesLocs Frame st.heap st'.heap ∧
      PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
      (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
      EnvTaintOk Scope env aenv st' I ∧
      EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
      VSim P ext B' st' Frame NoKill NoSpend σ' I rvFoot r rv ∧
      ValEnvDisj P st' NoKill Scope env aenv σ' envFoot rvFoot r rv ∧
      (ActiveVal σ' r → NoReachForbid st' Forbid BadReg BadDep r rv) ∧
      (ValidDeps σ' r.deps → r.cls ≠ .val → ValBaseOk st' rv ∧ NonValSafe st'.heap rv) ∧
      (ValidDeps σ' r.deps → (∀ c ∈ rv.taint, c < st'.nextRegion) ∧ OpenUnder st'.regions (I.regsOf r.regs) rv) ∧
      ((ValBaseOk st' rv ∧ CtorFieldsOk P ext B' st' rv) ∨ (IsOnceSrc σ' r ∧ SpentOnceSafe st'.heap rv)) ∧
      SrcOk Scope aenv σ σ' r

theorem TermPost.of_outOfFuel {P : Prog} {ext : ExternOracle} {B₀ : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ σ' : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop} {r : AVal} {m : MS Val}
    (h : m.run (st, B₀) = .error .outOfFuel) :
    TermPost P ext B₀ st Frame NoKill NoSpend Scope env aenv σ σ' I envFoot Forbid BadReg BadDep r m :=
  ⟨(fun _ hk => by rw [h] at hk; cases hk), (fun _ _ _ hk => by rw [h] at hk; cases hk)⟩

theorem TermPost.of_stuck {P : Prog} {ext : ExternOracle} {B₀ : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ σ' : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop} {r : AVal} {m : MS Val}
    (h : m.run (st, B₀) = .error .stuck) :
    TermPost P ext B₀ st Frame NoKill NoSpend Scope env aenv σ σ' I envFoot Forbid BadReg BadDep r m :=
  ⟨(fun _ hk => by rw [h] at hk; cases hk), (fun _ _ _ hk => by rw [h] at hk; cases hk)⟩

theorem taint_of_vsim_src_none {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp} {Foot : Nat → Prop}
    {r : AVal} {rv : Val}
    (hsrc : r.src = none)
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot r rv)
    (hvd : ValidDeps σ r.deps) :
    (∀ c ∈ rv.taint, c < st.nextRegion) ∧ OpenUnder st.regions (I.regsOf r.regs) rv := by
  have hact : ActiveVal σ r := ⟨hvd, fun ⟨_, hs, _⟩ => by rw [hsrc] at hs; cases hs⟩
  obtain ⟨hbv, hdou, _⟩ := hv.2.2.2.2 hact
  exact ⟨fun c hc => hbv.2.2.2 rv (HeldBy.refl _ _) c hc, hdou rv (HeldBy.refl _ _)⟩

theorem live_of_vsim_validDeps {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp} {Foot : Nat → Prop}
    {r : AVal} {rv : Val}
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot r rv)
    (hvd : ValidDeps σ r.deps) :
    (ValBaseOk st rv ∧ CtorFieldsOk P ext B st rv) ∨ (IsOnceSrc σ r ∧ SpentOnceSafe st.heap rv) := by
  by_cases hact : ActiveVal σ r
  · obtain ⟨hbv, _, hcf, _⟩ := hv.2.2.2.2 hact
    exact Or.inl ⟨hbv, hcf⟩
  · have his : IsOnceSrc σ r := Classical.byContradiction fun hno =>
      hact ⟨hvd, fun his' => absurd his' hno⟩
    exact Or.inr ⟨his, hv.2.2.2.1 hvd his⟩

theorem VSim_of_not_validDeps {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp}
    {av : AVal} {v : Val}
    (hregs : ∀ r ∈ av.regs, r < σ.nextRegion)
    (hdeps : ∀ d ∈ av.deps, d < σ.st.size)
    (hsrc : av.src = none)
    (hnvd : ¬ ValidDeps σ av.deps) :
    VSim P ext B st Frame NoKill NoSpend σ I (fun _ => False) av v :=
  ⟨hregs, hdeps, (fun _ hs => by rw [hsrc] at hs; cases hs),
   (fun hvd _ => absurd hvd hnvd), (fun hact => absurd hact.1 hnvd)⟩

theorem ValEnvDisj_of_not_validDeps {P : Prog} {st : St} {NoKill Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {envFoot : Nat → Nat → Prop}
    {av : AVal} {v : Val}
    (hsrc : av.src = none) (hnvd : ¬ ValidDeps σ av.deps) :
    ValEnvDisj P st NoKill Scope env aenv σ envFoot (fun _ => False) av v :=
  fun _ _ _ _ _ _ _ =>
    ⟨fun ha => absurd ha.1 hnvd,
     fun _ _ ha => absurd ha.1 hnvd,
     fun ha => absurd ha.1 hnvd,
     fun _ _ ha => absurd ha.1 hnvd,
     fun ha => absurd ha.1 hnvd,
     (fun hs => by rw [hsrc] at hs; cases hs),
     (fun _ hs => by rw [hsrc] at hs; cases hs)⟩

theorem NonValSafe.taint_nil {h : Heap} {v : Val} (hnv : NonValSafe h v) : v.taint = [] := by
  rcases hnv with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl, _, _, _⟩ <;> rfl

/-! ### The Seven Mutual Induction Predicates -/

def ATermProp (P : Prog) (ext : ExternOracle) (B : Nat)
    (aenv : List ABnd) (t : Term) (σ : AState) (r : AVal) (σ' : AState) : Prop :=
  LamsClosed t → CaseFieldsDistinct t →
  ∀ {B₀ fuel : Nat} {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop},
    B₀ ≤ B + 1 →
    (∀ x, FreeVarIn 0 t x → Scope x) →
    StOk P ext B₀ st →
    Sim P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot →
    (∀ l, StaticStrLoc st l → Frame l) →
    (∀ l, Frame l → l < st.heap.objs.size) →
    NoKillOk NoKill σ' →
    NoSpendOk NoSpend σ' →
    (∀ reg, σ.nextRegion ≤ reg → I.reg reg = []) →
    (st.regions.headD 0 = 0 ∨ st.regions.headD 0 ∈ I.reg (σ.regions.headD 1)) →
    EnvTaintOk Scope env aenv st I →
    EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep →
    (∀ l, Forbid l → l < st.heap.objs.size) →
    (∀ d, BadDep d → σ'.st[d]? = some .live) →
    TermPost P ext B₀ st Frame NoKill NoSpend Scope env aenv σ σ' I envFoot Forbid BadReg BadDep r
      (evalS P ext fuel env t)

def AEvalsProp (P : Prog) (ext : ExternOracle) (B : Nat)
    (aenv : List ABnd) (ts : List Term) (σ : AState) (avs : List AVal) (σ' : AState) : Prop :=
  (∀ t ∈ ts, LamsClosed t) → (∀ t ∈ ts, CaseFieldsDistinct t) →
  ∀ {B₀ fuel : Nat} {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop}
    {pref : List (Option (Val × AVal × (Nat → Prop)))},
    B₀ ≤ B + 1 →
    (∀ t ∈ ts, ∀ x, FreeVarIn 0 t x → Scope x) →
    StOk P ext B₀ st →
    Sim P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot →
    (∀ l, StaticStrLoc st l → Frame l) →
    (∀ l, Frame l → l < st.heap.objs.size) →
    NoKillOk NoKill σ' →
    NoSpendOk NoSpend σ' →
    (∀ reg, σ.nextRegion ≤ reg → I.reg reg = []) →
    (st.regions.headD 0 = 0 ∨ st.regions.headD 0 ∈ I.reg (σ.regions.headD 1)) →
    EnvTaintOk Scope env aenv st I →
    EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep →
    (∀ l, Forbid l → l < st.heap.objs.size) →
    (∀ d, BadDep d → σ'.st[d]? = some .live) →
    ArgListOk P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep pref →
    PrefixSrcOk Scope aenv pref →
    ArgsSrcOk pref →
    (∀ k, (evalListS P ext fuel env ts []).run (st, B₀) ≠ .error (.violation k)) ∧
    ∀ vs st' B', (evalListS P ext fuel env ts []).run (st, B₀) = .ok (vs, (st', B')) →
      ∃ args : List (Val × AVal × (Nat → Prop)),
        args.map (·.1) = vs ∧ args.map (·.2.1) = avs ∧
        B' ≤ B₀ ∧ StOk P ext B' st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧ st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧ ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
        (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
        PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
        Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
        EnvTaintOk Scope env aenv st' I ∧
        EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
        ArgListOk P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot Forbid BadReg BadDep (pref ++ args.map some) ∧
        PrefixSrcOk Scope aenv (pref ++ args.map some) ∧
        ArgsSrcOk (pref ++ args.map some)

def ACallArgsProp (P : Prog) (ext : ExternOracle) (B : Nat)
    (d? : Option RunDef) (aenv : List ABnd) (idx : Nat) (ts : List Term)
    (σ : AState) (avs : List (Option AVal)) (σ' : AState) : Prop :=
  (∀ t ∈ ts, LamsClosed t) → (∀ t ∈ ts, CaseFieldsDistinct t) →
  ∀ {B₀ fuel : Nat} {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop}
    {pref : List (Option (Val × AVal × (Nat → Prop)))},
    B₀ ≤ B + 1 →
    (∀ t ∈ ts, ∀ x, FreeVarIn 0 t x → Scope x) →
    StOk P ext B₀ st →
    Sim P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot →
    (∀ l, StaticStrLoc st l → Frame l) →
    (∀ l, Frame l → l < st.heap.objs.size) →
    NoKillOk NoKill σ' →
    NoSpendOk NoSpend σ' →
    (∀ reg, σ.nextRegion ≤ reg → I.reg reg = []) →
    (st.regions.headD 0 = 0 ∨ st.regions.headD 0 ∈ I.reg (σ.regions.headD 1)) →
    EnvTaintOk Scope env aenv st I →
    EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep →
    (∀ l, Forbid l → l < st.heap.objs.size) →
    (∀ d, BadDep d → σ'.st[d]? = some .live) →
    ArgListOk P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep pref →
    PrefixSrcOk Scope aenv pref →
    ArgsSrcOk pref →
    (∀ k, (evalCallArgsS P ext fuel env d? (ts.zipIdx idx) []).run (st, B₀) ≠ .error (.violation k)) ∧
    ∀ vs st' B', (evalCallArgsS P ext fuel env d? (ts.zipIdx idx) []).run (st, B₀) = .ok (vs, (st', B')) →
      ∃ args : List (Option (Val × AVal × (Nat → Prop))),
        ArgsMatch args vs avs ∧
        B' ≤ B₀ ∧ StOk P ext B' st' ∧
        st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
        st'.regions = st.regions ∧ st.nextRegion ≤ st'.nextRegion ∧
        ArrayExtends st.statics st'.statics ∧ ArrayExtends st.strs st'.strs ∧
        PreservesLocs Frame st.heap st'.heap ∧
        PreservesActiveEnv Scope env aenv σ' st.heap st'.heap ∧
        (∀ (l : Nat) (o : Obj) (n : Nat), st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o) ∧
        PreservesOnceShell st.heap st'.heap ∧ StaticStrFresh st st' ∧
        Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot ∧
        EnvTaintOk Scope env aenv st' I ∧
        EnvNoReachForbid st' Scope env aenv σ' Forbid BadReg BadDep ∧
        ArgListOk P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot Forbid BadReg BadDep (pref ++ args) ∧
        PrefixSrcOk Scope aenv (pref ++ args) ∧
        ArgsSrcOk (pref ++ args)

def ACallProp (P : Prog) (ext : ExternOracle) (B : Nat)
    (aenv : List ABnd) (r : Ref) (args : List Term) (c : Cls)
    (σ : AState) (res : AVal) (σ' : AState) : Prop :=
  (∀ t ∈ args, LamsClosed t) → (∀ t ∈ args, CaseFieldsDistinct t) →
  ∀ {B₀ fuel : Nat} {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop},
    B₀ ≤ B + 1 →
    (∀ t ∈ args, ∀ x, FreeVarIn 0 t x → Scope x) →
    StOk P ext B₀ st →
    Sim P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot →
    (∀ l, StaticStrLoc st l → Frame l) →
    (∀ l, Frame l → l < st.heap.objs.size) →
    NoKillOk NoKill σ' →
    NoSpendOk NoSpend σ' →
    (∀ reg, σ.nextRegion ≤ reg → I.reg reg = []) →
    (st.regions.headD 0 = 0 ∨ st.regions.headD 0 ∈ I.reg (σ.regions.headD 1)) →
    EnvTaintOk Scope env aenv st I →
    EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep →
    (∀ l, Forbid l → l < st.heap.objs.size) →
    (∀ d, BadDep d → σ'.st[d]? = some .live) →
    TermPost P ext B₀ st Frame NoKill NoSpend Scope env aenv σ σ' I envFoot Forbid BadReg BadDep res
      (do let vs ← evalCallArgsS P ext fuel env (P.find? r) args.zipIdx []; callWithS P ext fuel r vs c)

def AMajorProp (P : Prog) (ext : ExternOracle) (B : Nat)
    (aenv : List ABnd) (mj : Term) (σ : AState) (mv : AVal) (consuming : Bool) (pre : AState) : Prop :=
  LamsClosed mj → CaseFieldsDistinct mj →
  ∀ {B₀ fuel : Nat} {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop},
    B₀ ≤ B + 1 →
    (∀ x, FreeVarIn 0 mj x → Scope x) →
    StOk P ext B₀ st →
    Sim P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot →
    (∀ l, StaticStrLoc st l → Frame l) →
    (∀ l, Frame l → l < st.heap.objs.size) →
    NoKillOk NoKill pre →
    NoSpendOk NoSpend pre →
    (∀ reg, σ.nextRegion ≤ reg → I.reg reg = []) →
    (st.regions.headD 0 = 0 ∨ st.regions.headD 0 ∈ I.reg (σ.regions.headD 1)) →
    EnvTaintOk Scope env aenv st I →
    EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep →
    (∀ l, Forbid l → l < st.heap.objs.size) →
    (∀ d, BadDep d → pre.st[d]? = some .live) →
    TermPost P ext B₀ st Frame NoKill NoSpend Scope env aenv σ pre I envFoot Forbid BadReg BadDep mv
      (evalMajorS P ext fuel env mj) ∧
    (consuming = true → ActiveVal pre mv ∧ Transferable pre NoKill mv ∧ mv.deps = [] ∧ mv.src = none)

def AAltProp (P : Prog) (ext : ExternOracle) (B : Nat)
    (aenv : List ABnd) (altT : Term) (aargs : List (AVal × Bool × Bool))
    (σ : AState) (r : AVal) (σ' : AState) : Prop :=
  LamsClosed altT → CaseFieldsDistinct altT →
  ∀ {B₀ fuel : Nat} {st : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {I : Interp} {envFoot : Nat → Nat → Prop}
    {Forbid BadReg BadDep : Nat → Prop} {cargs : List (Val × Bool)},
    B₀ ≤ B + 1 →
    (∀ x, FreeVarIn 0 altT x → Scope x) →
    StOk P ext B₀ st →
    Sim P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot →
    (∀ l, StaticStrLoc st l → Frame l) →
    (∀ l, Frame l → l < st.heap.objs.size) →
    NoKillOk NoKill σ' →
    NoSpendOk NoSpend σ' →
    (∀ reg, σ.nextRegion ≤ reg → I.reg reg = []) →
    (st.regions.headD 0 = 0 ∨ st.regions.headD 0 ∈ I.reg (σ.regions.headD 1)) →
    EnvTaintOk Scope env aenv st I →
    EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep →
    (∀ l, Forbid l → l < st.heap.objs.size) →
    (∀ d, BadDep d → σ'.st[d]? = some .live) →
    cargs.length = aargs.length →
    (∀ a_d er_d fc_d, (a_d, er_d, fc_d) ∈ aargs → er_d = false → fc_d = true → a_d.deps ≠ [] →
      ∀ a0 er0 fc0, (a0, er0, fc0) ∈ aargs → er0 = false → a0.cls = .val → a0.own = .shared) →
    (∀ (idx : Nat) v er_c a0 er_a fc,
      cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
      er_c = er_a ∧ a0.src = none ∧
      (er_a = false → fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown ∧
        ValBaseOk st v ∧ CtorFieldsOk P ext B₀ st v ∧ NoOnceCell st.heap v ∧
        FunOkAt P ext B₀ st .unknown false (fun _ => False) v)) →
    ArgListOk P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep
      ((cargs.zip aargs).map fun ((v, _), (a0, er, _)) => if er then none else some (v, a0, fun _ => False)) →
    TermPost P ext B₀ st Frame NoKill NoSpend Scope env aenv σ σ' I envFoot Forbid BadReg BadDep r
      (applyAltS P ext fuel env altT cargs)

def AAltsProp (P : Prog) (ext : ExternOracle) (B : Nat)
    (aenv : List ABnd) (k : CaseInfo) (mv : AVal) (consuming : Bool) (pre : AState)
    (j : Nat) (cas : List CaseAlt) (altTs : List Term) (r_join : AVal) (σ_join : AState) : Prop :=
  ∀ (offset : Nat) (ca : CaseAlt) (altT : Term),
    cas[offset]? = some ca → altTs[offset]? = some altT →
    ∃ nextReg_j r_j post_j σ_chk_j σ_val_j uniq_j σ_u_j,
      pre.nextRegion ≤ nextReg_j ∧
      AAlt P aenv altT (caseAltArgs P k mv consuming (j + offset) ca) { pre with nextRegion := nextReg_j } r_j post_j ∧
      AAltProp P ext B aenv altT (caseAltArgs P k mv consuming (j + offset) ca) { pre with nextRegion := nextReg_j } r_j post_j ∧
      Runs (notOnceSrc r_j "a case alternative's result") post_j () σ_chk_j ∧
      r_j.onceOnly = false ∧
      Runs (valid r_j "a case alternative's result") σ_chk_j () σ_val_j ∧
      Runs (isUniq r_j) σ_val_j uniq_j σ_u_j ∧
      StateJoinGe pre σ_u_j σ_join ∧
      ValJoinGe pre.st.size { r_j with own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared } r_join

/-! ### Companion `select` Bridge for Dead Major Deps (`¬ ValidDeps σ av_mv.deps`) -/

theorem wrapperField?_spec {P : Prog} {k : CaseInfo} {wi : Nat}
    (hwi : P.wrapperField? k.ind = some wi) :
    ∃ f, (selectFieldsOf P k 0)[wi]? = some f ∧ f.kept = true := by
  unfold Prog.wrapperField? at hwi
  cases hsz : ((P.ctorsOf k.ind).size == 1) with
  | false =>
    simp only [guard, hsz, Bool.false_eq_true, ↓reduceIte, failure, Option.bind_eq_bind, Option.bind_none] at hwi
    cases hwi
  | true =>
    simp only [guard, hsz, ↓reduceIte, pure, Option.bind_eq_bind, Option.bind_some] at hwi
    cases hcs : (P.ctorsOf k.ind)[0]? with
    | none => rw [hcs] at hwi; cases hwi
    | some ctor =>
      rw [hcs] at hwi; dsimp only [Option.bind] at hwi
      cases hct : P.ctorOf? ctor with
      | none => rw [hct] at hwi; cases hwi
      | some p =>
        rcases p with ⟨ind, ci, nP, fs⟩
        rw [hct] at hwi; dsimp only [Option.bind] at hwi
        have hsel : selectFieldsOf P k 0 = fs := by unfold selectFieldsOf; simp [hcs, hct]
        rw [hsel]
        let kept := (fs.zipIdx.filter fun (f, _) => f.kept).map (·.2)
        cases hks : (kept.size == 1) with
        | false =>
          change (if (kept.size == 1) = true then pure () else none) >>= (fun _ => kept[0]?) = some wi at hwi
          rw [hks] at hwi; cases hwi
        | true =>
          change (if (kept.size == 1) = true then pure () else none) >>= (fun _ => kept[0]?) = some wi at hwi
          rw [hks] at hwi; simp only [↓reduceIte, pure, Option.bind_eq_bind, Option.bind_some] at hwi
          have hmem : wi ∈ kept.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hwi)
          dsimp only [kept] at hmem
          rw [Array.mem_toList_iff, Array.mem_map] at hmem
          obtain ⟨⟨f, idx⟩, hmf, rfl⟩ := hmem
          rw [Array.mem_filter] at hmf
          obtain ⟨j, hj, heq⟩ := Array.getElem_of_mem hmf.1
          have hjLt : j < fs.size := by simpa using hj
          simp only [Array.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨fs[j], Array.getElem?_eq_getElem hjLt, hmf.2⟩

/-- Companion to `select_caseAltArgs_bridge` when `¬ ValidDeps σ av_mv.deps` (e.g. a non-variable
major whose `callResult` / `applyValue` included a consumed argument's dead dep) while runtime
`mv` still satisfies `ValBaseOk st mv ∧ CtorFieldsOk P ext B st mv` and `consuming = false`. -/
theorem select_caseAltArgs_of_dead {P : Prog} {ext : ExternOracle} {B : Nat}
    {k : CaseInfo} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {av_mv : AVal} {mv : Val}
    (hst : StOk P ext B st)
    (hidx : CtorsIndexed P)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (henvNRF : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep)
    (hregsLt : ∀ r ∈ av_mv.regs, r < σ.nextRegion)
    (hdepsLt : ∀ d ∈ av_mv.deps, d < σ.st.size)
    (hnvd : ¬ ValidDeps σ av_mv.deps)
    (hbv : ValBaseOk st mv)
    (hcf : CtorFieldsOk P ext B st mv) :
    (select P k mv).run st = .error .stuck ∨
    ∃ cidx out st', (select P k mv).run st = .ok ((cidx, out), st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot ∧
      EnvNoReachForbid st' Scope env aenv σ Forbid BadReg BadDep ∧
      ∀ (ca : CaseAlt),
        let cargs : List (Val × Bool) := ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)
        let aargs := caseAltArgs P k av_mv false cidx ca
        let argList : List (Option (Val × AVal × (Nat → Prop))) :=
          (cargs.zip aargs).map fun ((v, _), (a0, er, _)) =>
            if er then none else some (v, a0, fun _ => False)
        cargs.length = aargs.length ∧
        (∀ (idx : Nat) v er_c a0 er_a fc,
          cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
          er_c = er_a ∧ a0.src = none ∧
          (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown ∧
            ValBaseOk st' v ∧ CtorFieldsOk P ext B st' v ∧ NoOnceCell st'.heap v ∧
            FunOkAt P ext B st' .unknown false (fun _ => False) v)) ∧
        ArgListOk P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep argList := by
  have hcaseFieldMeta : ∀ (cidx q : Nat),
      let (a0, er_a, fc) := caseField P k (selectFieldsOf P k cidx) av_mv false q
      a0.src = none ∧
      (∀ r ∈ a0.regs, r < σ.nextRegion) ∧
      (∀ d ∈ a0.deps, d < σ.st.size) ∧
      (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown ∧ ¬ ValidDeps σ a0.deps) := by
    intro cidx q
    dsimp only; unfold caseField
    by_cases hnat : (some k.ind == P.nat) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnat)]
      exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnat)]
      cases hf : (selectFieldsOf P k cidx)[q]? with
      | none => exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩
      | some f =>
        dsimp only
        by_cases h1 : (f.mode == .erased) = true
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]; exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
          by_cases h2 : (f.cls == .irr) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]; exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
            by_cases h3 : (av_mv.cls != .val && P.wrapperField? k.ind == some q) = true
            · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]; exact ⟨rfl, hregsLt, hdepsLt, (fun h => by cases h)⟩
            · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]
              by_cases h4 : (f.cls != .val) = true
              · rw [ite_eq_left_of_eq_true _ _ (eq_true h4)]; exact ⟨rfl, (fun _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩
              · rw [ite_eq_right_of_eq_false _ _ (eq_false h4)]
                by_cases h5 : (f.fmode == .shared) = true
                · rw [ite_eq_left_of_eq_true _ _ (eq_true h5)]; exact ⟨rfl, hregsLt, hdepsLt, fun _ => ⟨rfl, rfl, rfl, hnvd⟩⟩
                · rw [ite_eq_right_of_eq_false _ _ (eq_false h5)]; exact ⟨rfl, hregsLt, hdepsLt, fun _ => ⟨rfl, rfl, rfl, hnvd⟩⟩
  have hBuild : ∀ (cidx : Nat) (out : Array (Val × Bool)) (st' : St),
      st'.regions = st.regions → st'.nextRegion = st.nextRegion →
      st'.statics = st.statics → st'.strs = st.strs →
      st.heap.objs.size ≤ st'.heap.objs.size → st.heap.nextCap ≤ st'.heap.nextCap →
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap →
      StOk P ext B st' →
      Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot →
      (∀ (q : Nat),
        let (v, er_c) := out[q]?.getD (.imm .irr, false)
        let (a0, er_a, fc) := caseField P k (selectFieldsOf P k cidx) av_mv false q
        er_c = er_a ∧
        (er_a = false →
          (ValBaseOk st' v ∧ NonValSafe st'.heap v) ∨
          (¬ ValidDeps σ a0.deps ∧
            (fc = true → ValBaseOk st' v ∧ CtorFieldsOk P ext B st' v ∧ NoOnceCell st'.heap v ∧
              FunOkAt P ext B st' .unknown false (fun _ => False) v)))) →
      ∀ (ca : CaseAlt),
        let cargs : List (Val × Bool) := ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)
        let aargs := caseAltArgs P k av_mv false cidx ca
        let argList : List (Option (Val × AVal × (Nat → Prop))) :=
          (cargs.zip aargs).map fun ((v, _), (a0, er, _)) =>
            if er then none else some (v, a0, fun _ => False)
        cargs.length = aargs.length ∧
        (∀ (idx : Nat) v er_c a0 er_a fc,
          cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
          er_c = er_a ∧ a0.src = none ∧
          (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown ∧
            ValBaseOk st' v ∧ CtorFieldsOk P ext B st' v ∧ NoOnceCell st'.heap v ∧
            FunOkAt P ext B st' .unknown false (fun _ => False) v)) ∧
        ArgListOk P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep argList := by
    intro cidx out st' hrg' hnr' _ _ _ _ _ hst' hsim' hOut ca
    intro cargs aargs argList
    have hfieldsEq : (match (P.ctorsOf k.ind)[cidx]? with
        | some ctor => match P.ctorOf? ctor with | some (_, _, _, fs) => fs | none => #[]
        | none => #[]) = selectFieldsOf P k cidx := rfl
    have hlen : cargs.length = aargs.length := by simp [cargs, aargs, caseAltArgs]
    have hItem : ∀ (idx : Nat) v er_c a0 er_a fc,
        cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
        er_c = er_a ∧ a0.src = none ∧
        (∀ r ∈ a0.regs, r < σ.nextRegion) ∧ (∀ d ∈ a0.deps, d < σ.st.size) ∧
        (fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown ∧
          ValBaseOk st' v ∧ CtorFieldsOk P ext B st' v ∧ NoOnceCell st'.heap v ∧
          FunOkAt P ext B st' .unknown false (fun _ => False) v) ∧
        (er_a = false → (ValBaseOk st' v ∧ NonValSafe st'.heap v) ∨ ¬ ValidDeps σ a0.deps) := by
      intro idx v er_c a0 er_a fc hc ha
      simp only [cargs, List.getElem?_map] at hc
      simp only [aargs, caseAltArgs, List.getElem?_map] at ha
      cases hfa : ca.args.toList[idx]? with
      | none => rw [hfa] at hc; cases hc
      | some fa =>
        rw [hfa] at hc ha
        cases fa with
        | irr =>
          simp at hc ha; rcases hc with ⟨rfl, rfl⟩; rcases ha with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h),
            (fun h => by cases h), fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
        | unit =>
          simp at hc ha; rcases hc with ⟨rfl, rfl⟩; rcases ha with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h),
            (fun h => by cases h), fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
        | field q =>
          simp only [Option.map_some, Option.some.injEq] at hc ha
          change caseField P k (selectFieldsOf P k cidx) av_mv false q = (a0, er_a, fc) at ha
          have hcfM := hcaseFieldMeta cidx q
          have hoQ := hOut q
          dsimp only at hoQ hcfM
          rw [hc, ha] at hoQ
          rw [ha] at hcfM
          refine ⟨hoQ.1, hcfM.1, hcfM.2.1, hcfM.2.2.1, fun hfc => ?_, fun hne => ?_⟩
          · obtain ⟨hoo, hcls, hsk, hnvdA⟩ := hcfM.2.2.2 hfc
            have hne : er_a = false := by
              unfold caseField at ha
              split at ha
              · cases ha; cases hfc
              · cases hfQ : (selectFieldsOf P k cidx)[q]? with
                | none => rw [hfQ] at ha; cases ha; cases hfc
                | some f =>
                  rw [hfQ] at ha; dsimp only at ha
                  split at ha
                  · cases ha; cases hfc
                  · split at ha
                    · cases ha; cases hfc
                    · split at ha
                      · cases ha; cases hfc
                      · split at ha
                        · cases ha; cases hfc
                        · split at ha <;> (cases ha; rfl)
            rcases hoQ.2 hne with ⟨hbvQ, hnvQ⟩ | ⟨_, hfcQ⟩
            · exact ⟨hoo, hcls, hsk, hbvQ, hnvQ.ctorFieldsOk P ext B st', hnvQ.noOnceCell,
                hnvQ.funOkAt P ext B st' .unknown⟩
            · obtain ⟨hbvQ, hcfQ, hnoQ, hfunQ⟩ := hfcQ hfc
              exact ⟨hoo, hcls, hsk, hbvQ, hcfQ, hnoQ, hfunQ⟩
          · rcases hoQ.2 hne with h1 | ⟨h2, _⟩
            · exact Or.inl h1
            · exact Or.inr h2
    have hArgGet : ∀ (idx : Nat) v a0 ft,
        argList[idx]? = some (some (v, a0, ft)) →
        ∃ er_c fc, cargs[idx]? = some (v, er_c) ∧ aargs[idx]? = some (a0, false, fc) ∧ ft = fun _ => False := by
      intro idx v a0 ft hg
      simp only [argList, List.getElem?_map] at hg
      by_cases hlt : idx < (cargs.zip aargs).length
      · have hltC : idx < cargs.length := by rw [List.length_zip, hlen, Nat.min_self] at hlt; omega
        have hltA : idx < aargs.length := hlen ▸ hltC
        rw [List.getElem?_eq_getElem hlt, Option.map_some, List.getElem_zip] at hg
        rcases hc : cargs[idx] with ⟨v', er_c⟩
        rcases ha : aargs[idx] with ⟨a0', er_a, fc⟩
        rw [hc, ha] at hg
        cases er_a with
        | true => simp at hg
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hg
          rcases hg with ⟨rfl, rfl, rfl⟩
          exact ⟨er_c, fc, by rw [List.getElem?_eq_getElem hltC, hc], by rw [List.getElem?_eq_getElem hltA, ha], rfl⟩
      · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hg; cases hg
    refine ⟨hlen, fun idx v er_c a0 er_a fc hc ha => ?_, ⟨fun idx v a0 ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ _ hg₁ hg₂ => ?_⟩⟩
    · obtain ⟨h1, h2, _, _, h5, _⟩ := hItem idx v er_c a0 er_a fc hc ha
      exact ⟨h1, h2, h5⟩
    · obtain ⟨er_c, fc, hc, ha, rfl⟩ := hArgGet idx v a0 ft hg
      obtain ⟨_, hsrc, hrl, hdl, _, hor⟩ := hItem idx v er_c a0 false fc hc ha
      rcases hor rfl with ⟨hbvQ, hnvQ⟩ | hnvdA
      · exact ⟨VSim_nonValSafe hrl hdl hsrc hbvQ hnvQ,
          ValEnvDisj_nonValSafe hsrc hnvQ hsim',
          fun _ => NoReachForbid_nonValSafe hnvQ,
          fun _ _ => ⟨hbvQ, hnvQ⟩⟩
      · exact ⟨VSim_of_not_validDeps hrl hdl hsrc hnvdA,
          ValEnvDisj_of_not_validDeps hsrc hnvdA,
          fun ha' => absurd ha'.1 hnvdA,
          fun hvd _ => absurd hvd hnvdA⟩
    · obtain ⟨er₁, fc₁, hc₁, ha₁, rfl⟩ := hArgGet i v₁ av₁ ft₁ hg₁
      obtain ⟨er₂, fc₂, hc₂, ha₂, rfl⟩ := hArgGet j v₂ av₂ ft₂ hg₂
      obtain ⟨_, _, _, _, _, hor₁⟩ := hItem i v₁ er₁ av₁ false fc₁ hc₁ ha₁
      obtain ⟨_, _, _, _, _, hor₂⟩ := hItem j v₂ er₂ av₂ false fc₂ hc₂ ha₂
      refine ⟨fun ha1 htr1 ha2 _ l hor hr2 => ?_, fun _ _ _ _ _ h => False.elim h⟩
      rcases hor₁ rfl with ⟨_, hnv1⟩ | hnvd1
      · exact False.elim (hnv1.ownTreeFull.2 l hor)
      · exact absurd ha1.1 hnvd1
  rcases select_spec hidx hst.1 hbv.1 hbv.2.1 with hSt |
    ⟨cidx, out, st', hrun, hrg', hnr', hstat', hstr', hsz', hcap', hpres', hc', hoss', hnewNum, hcases⟩
  · exact Or.inl hSt
  · right
    have honce' : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_preservesLocs (hpres'.mono fun _ ⟨_, _, _, ho, _⟩ => (Array.getElem?_eq_some_iff.mp ho).1)
    have hssf' : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat' hstr'
        (hpres'.mono fun _ h => h.1) (fun _ _ h => h)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_old hst hc' hrg' (hnr' ▸ Nat.le_refl _) hstat' hstr' hpres'
    have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hrg'
    have hIok' : InterpOk σ st' I :=
      ⟨fun r hr c hc => hnr' ▸ hsim.2.2.1.1 r hr c hc,
       fun c hc => by rw [hrg'] at hc; exact hsim.2.2.1.2 c hc⟩
    have hpEnv' : PreservesActiveEnv Scope env aenv σ st.heap st'.heap :=
      Sim_preserves_of_old (AStateLe.refl _) hpres' hsim
    have hsim' : Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ I envFoot :=
      Sim_step (Nat.le_refl _) (AStateLe.refl _) hsim.2.1 hIok' hrf' honce' hssf' (fun _ _ _ h => h) hpEnv' hsim
    have henvNRF' : EnvNoReachForbid st' Scope env aenv σ Forbid BadReg BadDep :=
      EnvNoReachForbid_step hsim.2.1 (AStateLe.refl _) (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
        (hpres'.mono fun _ hl => StaticStrLoc_lt_size hst hl) hpEnv' henvNRF
    refine ⟨cidx, out, st', hrun, hrg', hnr', hstat', hstr', hsz', hcap', hpres', honce', hssf',
      hst', hsim', henvNRF', ?_⟩
    apply hBuild cidx out st' hrg' hnr' hstat' hstr' hsz' hcap' hpres' hst' hsim'
    intro q
    rcases hcases with ⟨hNat, hNatBr⟩ | ⟨hNotNat, hIrr | hWrap | hCtor⟩
    · have hcfNat : caseField P k (selectFieldsOf P k cidx) av_mv false q = ({ cls := natClass }, false, false) := by
        unfold caseField; simp [hNat]
      rw [hcfNat]
      rcases hNatBr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, m, v, rfl, _, hdlV, hclsV, htV, hacycV, _, _⟩
      · exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
      · cases q with
        | zero =>
          have hbvV : ValBaseOk st' v := ValBaseOk_of_deepLive hdlV hacycV (by
            intro w hw r hr
            rcases hw with rfl | ⟨l, o, hrl, ho, hm⟩
            · rw [htV] at hr; cases hr
            · have hnv := ClsSafe.to_nonValSafe (by decide) (Or.inr hclsV) hdlV.self.1
              obtain ⟨o2, n2, ho2, hc2⟩ := hnv.reach_numLoc hrl
              rw [ho2] at ho; cases ho; rw [hc2] at hm; cases hm)
          exact ⟨rfl, fun _ => Or.inl ⟨hbvV, ClsSafe.to_nonValSafe (by decide) (Or.inr hclsV) hdlV.self.1⟩⟩
        | succ _ => exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
    · rcases hIrr with ⟨rfl, rfl⟩
      unfold caseField
      have hneN : (some k.ind == P.nat) = false := beq_false_of_ne (Ne.symm hNotNat)
      simp only [hneN, Bool.false_eq_true, ↓reduceIte]
      cases hf : (selectFieldsOf P k cidx)[q]? with
      | none =>
        have hout : ((selectFieldsOf P k cidx).map fun f => (Val.imm .irr, f.mode == .erased))[q]? = none := by
          rw [Array.getElem?_map, hf]; rfl
        simp [hout]; exact Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩
      | some f =>
        have hout : ((selectFieldsOf P k cidx).map fun f => (Val.imm .irr, f.mode == .erased))[q]? =
            some (.imm .irr, f.mode == .erased) := by
          rw [Array.getElem?_map, hf]; rfl
        simp only [hout, Option.getD_some]
        split
        · rename_i hfe; simp [hfe]
        · rename_i hfe
          have hfeF : (f.mode == .erased) = false := Bool.eq_false_iff.mpr hfe
          simp only [hfeF]
          split
          · exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
          · split
            · exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
            · split
              · exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
              · split <;> exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
    · rcases hWrap with ⟨hStEq, rfl, wi, hwi, rfl, hmvNV⟩
      subst st'
      have hnvMv : NonValSafe st.heap mv := by
        rcases hmvNV with ⟨imm, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, hcell⟩
        · exact Or.inl ⟨imm, rfl⟩
        · exact Or.inr ⟨loc, cap, o, n, rfl, ho, by
            obtain ⟨o', ho', hcap⟩ := hbv.1.self.1; rw [ho] at ho'; cases ho'; exact hcap, hcell⟩
      unfold caseField
      have hneN : (some k.ind == P.nat) = false := beq_false_of_ne (Ne.symm hNotNat)
      simp only [hneN, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨fwi, hfwi, hfwiKept⟩ := wrapperField?_spec hwi
      have hwiLtMap : wi < ((selectFieldsOf P k 0).map fun f => (Val.imm .irr, f.mode == .erased)).size := by
        simpa using (Array.getElem?_eq_some_iff.mp hfwi).1
      by_cases hqw : q = wi
      · subst hqw
        have hout : (((selectFieldsOf P k 0).map fun f => (Val.imm .irr, f.mode == .erased)).set! q (mv, false))[q]? =
            some (mv, false) := by
          simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self, hwiLtMap, ↓reduceIte]
        rw [hfwi]; simp only [hout, Option.getD_some]
        have hfeF : (fwi.mode == .erased) = false := by
          unfold Field.kept at hfwiKept
          cases hm : fwi.mode <;> rw [hm] at hfwiKept <;> first | cases hfwiKept | rfl
        simp only [hfeF, Bool.false_eq_true, ↓reduceIte]
        split
        · exact ⟨rfl, fun _ => Or.inl ⟨hbv, hnvMv⟩⟩
        · split
          · exact ⟨rfl, fun _ => Or.inl ⟨hbv, hnvMv⟩⟩
          · split
            · exact ⟨rfl, fun _ => Or.inl ⟨hbv, hnvMv⟩⟩
            · split <;> exact ⟨rfl, fun _ => Or.inl ⟨hbv, hnvMv⟩⟩
      · have hout : (((selectFieldsOf P k 0).map fun f => (Val.imm .irr, f.mode == .erased)).set! wi (mv, false))[q]? =
            ((selectFieldsOf P k 0).map fun f => (Val.imm .irr, f.mode == .erased))[q]? := by
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hqw)]
        rw [hout]
        cases hf : (selectFieldsOf P k 0)[q]? with
        | none =>
          have h1 : ((selectFieldsOf P k 0).map fun f => (Val.imm .irr, f.mode == .erased))[q]? = none := by
            rw [Array.getElem?_map, hf]; rfl
          simp [h1]; exact Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩
        | some f =>
          have h1 : ((selectFieldsOf P k 0).map fun f => (Val.imm .irr, f.mode == .erased))[q]? =
              some (.imm .irr, f.mode == .erased) := by
            rw [Array.getElem?_map, hf]; rfl
          simp only [h1, Option.getD_some]
          split
          · rename_i hfe; simp [hfe]
          · rename_i hfe
            have hfeF : (f.mode == .erased) = false := Bool.eq_false_iff.mpr hfe
            simp only [hfeF]
            split
            · exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
            · split
              · exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
              · split
                · exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
                · split <;> exact ⟨rfl, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
    · rcases hCtor with ⟨loc, cap, t, o, r, fs, nP, fdefs, rfl, ho, hcap, hcell, hctor, hsel, houtSz, hperF, _⟩
      unfold caseField
      have hneN : (some k.ind == P.nat) = false := beq_false_of_ne (Ne.symm hNotNat)
      simp only [hneN, Bool.false_eq_true, ↓reduceIte, hsel]
      cases hf : fdefs[q]? with
      | none =>
        have hge : fdefs.size ≤ q := by
          cases Nat.lt_or_ge q fdefs.size with
          | inl hlt => rw [Array.getElem?_eq_getElem hlt] at hf; cases hf
          | inr hge => exact hge
        have hout : out[q]? = none := Array.getElem?_eq_none (by omega)
        simp [hout]; exact Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩
      | some f =>
        obtain ⟨v, houtQ, hnotKept, hkept⟩ := hperF q f hf
        simp only [houtQ, Option.getD_some]
        by_cases hfe : f.mode = .erased
        · have hfeT : (f.mode == .erased) = true := by rw [hfe]; rfl
          simp [hfeT]
        · have hfeF : (f.mode == .erased) = false := beq_false_of_ne hfe
          simp only [hfeF, Bool.false_eq_true, ↓reduceIte]
          by_cases hfirr : f.cls = .irr
          · have hfiT : (f.cls == .irr) = true := by rw [hfirr]; rfl
            have hnk : f.kept = false := by unfold Field.kept; rw [hfirr]; cases f.mode <;> rfl
            rw [hnotKept hnk]
            simp only [hfiT, ↓reduceIte]
            exact ⟨trivial, fun _ => Or.inl ⟨ValBaseOk_imm _ _, Or.inl ⟨.irr, rfl⟩⟩⟩
          · have hfiF : (f.cls == .irr) = false := Cls_beq_false_of_ne hfirr
            simp only [hfiF, Bool.false_eq_true, ↓reduceIte]
            have hfk : f.kept = true := by
              unfold Field.kept
              cases hm' : f.mode <;> rw [hm'] at hfe <;> cases hc' : f.cls <;> rw [hc'] at hfirr <;>
                first | exact absurd rfl hfe | exact absurd rfl hfirr | rfl
            obtain ⟨hrawMem, hrawVal, hclsV, hdlV, hacycV, htV, hnvT, hreachV, hhbV, _, _, _⟩ := hkept hfk
            have hrawBase : ValBaseOk st (fs[q]?.getD (.imm .irr)) := by
              rcases hrawMem with hIrr | hIn
              · rw [hIrr]; exact ValBaseOk_imm _ _
              · exact ValBaseOk.sub hbv (Or.inr ⟨loc, o, Reach.here, ho, by simpa [Cell.vals, hcell] using hIn⟩)
            have hbvV : ValBaseOk st' v := ValBaseOk_of_deepLive hdlV hacycV (by
              intro w hw r' hr'
              rcases hhbV w hw with rfl | hhbR
              · rcases htV r' hr' with h1 | ⟨_, h2⟩
                · exact hnr' ▸ hrawBase.2.2.2 _ (HeldBy.refl _ _) r' h1
                · exact hnr' ▸ hbv.2.2.2 (.ref loc cap t) (HeldBy.refl _ _) r' h2
              · exact hnr' ▸ hrawBase.2.2.2 w hhbR r' hr')
            have hrawCfNoFun : ValBaseOk st' v ∧ CtorFieldsOk P ext B st' v ∧ NoOnceCell st'.heap v ∧
                FunOkAt P ext B st' .unknown false (fun _ => False) v := by
              by_cases hfV : f.cls = .val
              · rcases hrawMem with hIrr | hIn
                · have hvImm : ∃ imm, v = .imm imm := by
                    rcases hrawVal hfV with ⟨imm, _, hvEq⟩ | ⟨_, _, _, _, hEq, _⟩
                    · exact ⟨imm, hvEq⟩
                    · rw [hIrr] at hEq; cases hEq
                  rcases hvImm with ⟨imm, rfl⟩
                  have hnvI : NonValSafe st'.heap (.imm imm) := Or.inl ⟨imm, rfl⟩
                  exact ⟨ValBaseOk_imm _ _, hnvI.ctorFieldsOk P ext B st', hnvI.noOnceCell, hnvI.funOkAt P ext B st' .unknown⟩
                · have hcfRaw := hcf loc o r fs (fs[q]?.getD (.imm .irr)) Reach.here ho hcell hIn
                  have hcfSub : CtorFieldsOk P ext B st (fs[q]?.getD (.imm .irr)) :=
                    CtorFieldsOk.sub hcf (Or.inr ⟨loc, o, Reach.here, ho, by simpa [Cell.vals, hcell] using hIn⟩)
                  have hlocRV : SameLoc (fs[q]?.getD (.imm .irr)) v := by
                    rcases hrawVal hfV with ⟨imm, h1, h2⟩ | ⟨l', c', t₁, t₂, h1, h2⟩
                    · rw [h1, h2]; rfl
                    · rw [h1, h2]; rfl
                  have hshRV : SameShapeOn (Reach st.heap (fs[q]?.getD (.imm .irr))) st.heap st'.heap :=
                    hoss'.to_sameShapeOn _
                  have hnoV : NoOnceCell st'.heap v :=
                    NoOnceCell_of_sameShape hrawBase.1 hshRV hlocRV hcfRaw.1
                  have hcfV : CtorFieldsOk P ext B st' v :=
                    CtorFieldsOk_of_sameShape hrawBase.1 hshRV hlocRV hrf' hcfSub
                  have hfunV : FunOkAt P ext B st' .unknown false (fun _ => False) v :=
                    FunOkAt_preserve_sameShape hlocRV hshRV hrf' hcfRaw.2
                  exact ⟨hbvV, hcfV, hnoV, hfunV⟩
              · have hnvV : NonValSafe st'.heap v := ClsSafe.to_nonValSafe hfV (Or.inr hclsV) hdlV.self.1
                exact ⟨hbvV, hnvV.ctorFieldsOk P ext B st', hnvV.noOnceCell, hnvV.funOkAt P ext B st' .unknown⟩
            split
            · exact ⟨rfl, fun _ => Or.inr ⟨hnvd, fun h => by cases h⟩⟩
            · split
              · rename_i hneV
                have hfneV : f.cls ≠ .val := by intro h; rw [h] at hneV; cases hneV
                exact ⟨rfl, fun _ => Or.inl ⟨hbvV, ClsSafe.to_nonValSafe hfneV (Or.inr hclsV) hdlV.self.1⟩⟩
              · split <;> exact ⟨rfl, fun _ => Or.inr ⟨hnvd, fun _ => hrawCfNoFun⟩⟩

/-! ### Standalone Heavy Case Lemmas -/

theorem restoreOwned_getElem?_not_mem (xs : List Nat) (σ : AState) (y : Nat) (hny : y ∉ xs) :
    (restoreOwned xs σ).st[y]? = σ.st[y]? := by
  have hgo : ∀ (zs : List Nat) (arr : Array BSt), y ∉ zs →
      (zs.foldl (fun a x => a.set! x BSt.live) arr)[y]? = arr[y]? := by
    intro zs; induction zs with
    | nil => intro arr _; rfl
    | cons z rest ih =>
      intro arr hny'
      simp only [List.foldl_cons]
      rw [ih _ (fun hz => hny' (List.mem_cons_of_mem _ hz))]
      have hne : z ≠ y := fun h => hny' (h ▸ List.mem_cons_self)
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hne]
  exact hgo xs σ.st hny

theorem ACaps_props {aenv : List ABnd} :
    ∀ {ys : List Nat} {σ₀ σ₁ : AState} {d0 r0 o0 d1 r1 o1 : List Nat},
      AStateOk σ₀ →
      ACaps aenv ys σ₀ d0 r0 o0 d1 r1 o1 σ₁ →
      σ₁.st.size = σ₀.st.size ∧
      (∀ x ∈ o0, x ∈ o1) ∧
      (∀ x ∈ o1, x ∈ o0 ∨ ∃ i ∈ ys, ∃ ab, aenv[i]? = some ab ∧ ab.id = x ∧ captureTransfers ab.mode = true) ∧
      (∀ i ∈ ys, ∃ ab, aenv[i]? = some ab ∧ ab.mode ≠ .erased ∧
        ValidDeps σ₀ (effVal ab).deps ∧ (effVal ab).onceOnly = false ∧ ¬ IsOnceSrc σ₀ (effVal ab) ∧
        (captureTransfers ab.mode = true → ab.id ∈ o1 ∧
          ((effVal ab).cls = .val →
            (effVal ab).own = .uniq ∧
            (∀ d ∈ (effVal ab).deps, σ₀.st[d]? = some .live) ∧
            (ab.mode.isBorrowed = false → (effVal ab).regs = []) ∧
            (∀ d ∈ (effVal ab).deps, σ₁.st[d]? = some .dead))) ∧
        (captureTransfers ab.mode = false → (effVal ab).cls = .val → σ₁.st[ab.id]? ≠ some .live)) ∧
      (∀ (p q : Nat) ia ib aba abb, p ≠ q →
        ys[p]? = some ia → ys[q]? = some ib →
        aenv[ia]? = some aba → aenv[ib]? = some abb →
        captureTransfers aba.mode = true → (effVal aba).cls = .val → (effVal abb).cls = .val →
        ∀ d ∈ (effVal aba).deps, d ∉ (effVal abb).deps) := by
  intro ys σ₀ σ₁ d0 r0 o0 d1 r1 o1 hok₀ hc
  induction hc with
  | nil =>
    exact ⟨rfl, fun _ h => h, fun _ h => Or.inl h, (fun _ h => by cases h), (fun _ _ _ _ _ _ _ h1 => by cases h1)⟩
  | @consUniq i rest b v sA sB sC dA rA oA dB rB oB sD hbi hrd hct hfl hrest ih =>
    obtain ⟨ab', habi', hne', hvEq, hvdB, hσEq⟩ := Runs_readVar hrd
    rw [hbi] at habi'; cases habi'
    subst sB
    obtain ⟨hokC, hleC, hszC, honceC, _, _, _, _, _, hneOnceC, _, _, _, _, huniqC⟩ := Runs_flowTo hok₀ hfl
    obtain ⟨hszR, hoSubR, hoMemR, hmemR, hpairR⟩ := ih hokC
    have hpullLive : ∀ d, sC.st[d]? = some BSt.live → sA.st[d]? = some BSt.live := fun d hlvC => by
      have hltA : d < sA.st.size := by have := (Array.getElem?_eq_some_iff.mp hlvC).1; omega
      have h1 := hleC.2.2.1 d hltA; rw [hlvC] at h1
      cases h3 : sA.st[d]? with
      | none => exact False.elim (Nat.not_le_of_lt hltA (Array.getElem?_eq_none_iff.mp h3))
      | some b3 => rw [h3] at h1; cases b3 with | live => rfl | shared | dead => exact False.elim h1
    refine ⟨hszR.trans hszC, fun x hx => hoSubR x (List.mem_cons_of_mem _ hx), fun x hx => ?_, fun j hj => ?_, fun p q ia ib aba abb hpq hp hq haba habb hctA hcvA hcvB d hd hdb => ?_⟩
    · rcases hoMemR x hx with hm | ⟨k, hk, ab, habk, hid, hctk⟩
      · rcases List.mem_cons.mp hm with rfl | hm'
        · exact Or.inr ⟨i, List.mem_cons_self, b, hbi, rfl, hct⟩
        · exact Or.inl hm'
      · exact Or.inr ⟨k, List.mem_cons_of_mem _ hk, ab, habk, hid, hctk⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · refine ⟨b, hbi, hne', hvdB, hvEq ▸ (hneOnceC (by intro h; cases h)).2.1, ?_, fun _ => ⟨hoSubR b.id List.mem_cons_self, fun hcv => ?_⟩,
          fun hf => by rw [hct] at hf; cases hf⟩
        · exact hvEq ▸ (hneOnceC (by intro h; cases h)).2.2
        · have h1 := (huniqC b.mode.isBorrowed rfl).1 (hvEq ▸ hcv)
          rw [hvEq] at h1
          refine ⟨h1.1, h1.2.1, h1.2.2, fun d hd => ?_⟩
          have hd' : d ∈ v.deps := hvEq ▸ hd
          have hltD : d < sA.st.size := (hvdB d hd).1
          have hdeadC : sC.st[d]? = some .dead := by
            have h2 := (huniqC b.mode.isBorrowed rfl).2 d hltD
            have hcv' : v.cls = .val := hvEq ▸ hcv
            simp only [hcv', hd', and_self, ↓reduceIte] at h2
            exact h2
          obtain ⟨_, hleR, _, _⟩ := ACaps_state_le hokC hrest
          have h3 := hleR.2.2.1 d (Array.getElem?_eq_some_iff.mp hdeadC).1
          rw [hdeadC] at h3
          cases h4 : sD.st[d]? with
          | none => rw [h4] at h3; exact False.elim h3
          | some b4 => rw [h4] at h3; cases b4 with | dead => rfl | live | shared => exact False.elim h3
      · obtain ⟨ab, habj, hnej, hvdC, hooC, hnoC, hctT, hctF⟩ := hmemR j hj'
        have hvdA : ValidDeps sA (effVal ab).deps := fun d hd => by
          obtain ⟨hltC, hneC⟩ := hvdC d hd
          have hltA : d < sA.st.size := by omega
          refine ⟨hltA, fun hdeadA => ?_⟩
          have h1 := hleC.2.2.1 d hltA; rw [hdeadA] at h1
          cases h2 : sC.st[d]? with
          | none => rw [h2] at h1; exact h1
          | some b2 => rw [h2] at h1; cases b2 with | dead => exact hneC h2 | live | shared => exact h1
        have hnoA : ¬ IsOnceSrc sA (effVal ab) := fun ⟨x, hs, ho⟩ =>
          hnoC ⟨x, hs, honceC.symm ▸ ho⟩
        refine ⟨ab, habj, hnej, hvdA, hooC, hnoA, fun hctJ => ?_, hctF⟩
        obtain ⟨hoJ, hvalJ⟩ := hctT hctJ
        exact ⟨hoJ, fun hcvJ =>
          let ⟨hownJ, hlvC, hrgJ, hdeadJ⟩ := hvalJ hcvJ
          ⟨hownJ, fun d hd => hpullLive d (hlvC d hd), hrgJ, hdeadJ⟩⟩
    · cases p with
      | zero =>
        simp at hp; subst hp; rw [haba] at hbi; cases hbi
        cases q with
        | zero => exact absurd rfl hpq
        | succ q' =>
          simp at hq
          obtain ⟨abb2, habb2, _, hvdC, _, _, _, _⟩ := hmemR ib (List.mem_of_getElem? hq)
          rw [habb] at habb2; cases habb2
          have hd' : d ∈ v.deps := hvEq ▸ hd
          have hltD : d < sA.st.size := (hvdB d hd).1
          have hdeadC := (huniqC b.mode.isBorrowed rfl).2 d hltD
          have hcv' : v.cls = .val := hvEq ▸ hcvA
          simp only [hcv', hd', and_self, ↓reduceIte] at hdeadC
          exact (hvdC d hdb).2 hdeadC
      | succ p' =>
        cases q with
        | zero =>
          simp at hp hq; subst hq; rw [habb] at hbi; cases hbi
          obtain ⟨aba2, haba2, _, hvdC, _, _, _, _⟩ := hmemR ia (List.mem_of_getElem? hp)
          rw [haba] at haba2; cases haba2
          have hdb' : d ∈ v.deps := hvEq ▸ hdb
          have hltD : d < sA.st.size := (hvdB d hdb).1
          have hdeadC := (huniqC b.mode.isBorrowed rfl).2 d hltD
          have hcv' : v.cls = .val := hvEq ▸ hcvB
          simp only [hcv', hdb', and_self, ↓reduceIte] at hdeadC
          exact (hvdC d hd).2 hdeadC
        | succ q' =>
          simp at hp hq
          exact hpairR p' q' ia ib aba abb (by omega) hp hq haba habb hctA hcvA hcvB d hd hdb
  | @consShare i rest b v sA sB sC dA rA oA dB rB oB sD hbi hrd hct hfl hrest ih =>
    obtain ⟨ab', habi', hne', hvEq, hvdB, hσEq⟩ := Runs_readVar hrd
    rw [hbi] at habi'; cases habi'
    subst sB
    obtain ⟨hokC, hleC, hszC, honceC, _, _, _, _, _, hneOnceC, _, _, hshareC, _, _⟩ := Runs_flowTo hok₀ hfl
    obtain ⟨hszR, hoSubR, hoMemR, hmemR, hpairR⟩ := ih hokC
    have hpullLive : ∀ d, sC.st[d]? = some BSt.live → sA.st[d]? = some BSt.live := fun d hlvC => by
      have hltA : d < sA.st.size := by have := (Array.getElem?_eq_some_iff.mp hlvC).1; omega
      have h1 := hleC.2.2.1 d hltA; rw [hlvC] at h1
      cases h3 : sA.st[d]? with
      | none => exact False.elim (Nat.not_le_of_lt hltA (Array.getElem?_eq_none_iff.mp h3))
      | some b3 => rw [h3] at h1; cases b3 with | live => rfl | shared | dead => exact False.elim h1
    refine ⟨hszR.trans hszC, hoSubR, fun x hx => ?_, fun j hj => ?_, fun p q ia ib aba abb hpq hp hq haba habb hctA hcvA hcvB d hd hdb => ?_⟩
    · rcases hoMemR x hx with hm | ⟨k, hk, ab, habk, hid, hctk⟩
      · exact Or.inl hm
      · exact Or.inr ⟨k, List.mem_cons_of_mem _ hk, ab, habk, hid, hctk⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · refine ⟨b, hbi, hne', hvdB, hvEq ▸ (hneOnceC (by intro h; cases h)).2.1, ?_, (fun ht => by rw [hct] at ht; cases ht), fun _ hcv => ?_⟩
        · exact hvEq ▸ (hneOnceC (by intro h; cases h)).2.2
        · have hidIn : b.id ∈ v.deps := hvEq ▸ List.mem_cons_self
          have hltId : b.id < sA.st.size := (hvdB b.id List.mem_cons_self).1
          have hneDead : sA.st[b.id]? ≠ some .dead := (hvdB b.id List.mem_cons_self).2
          have hshC : sC.st[b.id]? = some .shared := by
            have h1 := hshareC rfl b.id hltId
            have hcv' : v.cls = .val := hvEq ▸ hcv
            cases hstA : sA.st[b.id]? with
            | none => exact False.elim (Nat.not_le_of_lt hltId (Array.getElem?_eq_none_iff.mp hstA))
            | some bA =>
              cases bA with
              | live => simp only [hcv', hidIn, hstA, and_self, ↓reduceIte] at h1; exact h1
              | shared => rw [hstA] at h1; simp at h1; exact h1
              | dead => exact absurd hstA hneDead
          obtain ⟨_, hleR, _, _⟩ := ACaps_state_le hokC hrest
          have h2 := hleR.2.2.1 b.id (Array.getElem?_eq_some_iff.mp hshC).1
          rw [hshC] at h2
          intro hlv; rw [hlv] at h2; exact h2
      · obtain ⟨ab, habj, hnej, hvdC, hooC, hnoC, hctT, hctF⟩ := hmemR j hj'
        have hvdA : ValidDeps sA (effVal ab).deps := fun d hd => by
          obtain ⟨hltC, hneC⟩ := hvdC d hd
          have hltA : d < sA.st.size := by omega
          refine ⟨hltA, fun hdeadA => ?_⟩
          have h1 := hleC.2.2.1 d hltA; rw [hdeadA] at h1
          cases h2 : sC.st[d]? with
          | none => rw [h2] at h1; exact h1
          | some b2 => rw [h2] at h1; cases b2 with | dead => exact hneC h2 | live | shared => exact h1
        have hnoA : ¬ IsOnceSrc sA (effVal ab) := fun ⟨x, hs, ho⟩ =>
          hnoC ⟨x, hs, honceC.symm ▸ ho⟩
        refine ⟨ab, habj, hnej, hvdA, hooC, hnoA, fun hctJ => ?_, hctF⟩
        obtain ⟨hoJ, hvalJ⟩ := hctT hctJ
        exact ⟨hoJ, fun hcvJ =>
          let ⟨hownJ, hlvC, hrgJ, hdeadJ⟩ := hvalJ hcvJ
          ⟨hownJ, fun d hd => hpullLive d (hlvC d hd), hrgJ, hdeadJ⟩⟩
    · cases p with
      | zero => simp at hp; subst hp; rw [haba] at hbi; cases hbi; rw [hctA] at hct; cases hct
      | succ p' =>
        cases q with
        | zero =>
          simp at hp hq; subst hq; rw [habb] at hbi; cases hbi
          obtain ⟨aba2, haba2, _, _, _, _, hctTA, _⟩ := hmemR ia (List.mem_of_getElem? hp)
          rw [haba] at haba2; cases haba2
          have hlvC : sC.st[d]? = some .live := ((hctTA hctA).2 hcvA).2.1 d hd
          have hlvA : sA.st[d]? = some .live := hpullLive d hlvC
          have hltD : d < sA.st.size := (Array.getElem?_eq_some_iff.mp hlvA).1
          have hsh := hshareC rfl d hltD
          have hdb' : d ∈ v.deps := hvEq ▸ hdb
          have hcv' : v.cls = .val := hvEq ▸ hcvB
          simp only [hcv', hdb', hlvA, and_self, ↓reduceIte] at hsh
          rw [hsh] at hlvC; cases hlvC
        | succ q' =>
          simp at hp hq
          exact hpairR p' q' ia ib aba abb (by omega) hp hq haba habb hctA hcvA hcvB d hd hdb

/-- Soundness for `ATerm.lam` (closure creation + `FunOkAt` via `clo_call_sim_of_captures`,
`clo_bindParam_push`, body IH, `retCheck_bridge`, and `conform_post_apply`). -/
theorem evalS_lam_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {p : Param} {res : ResultMode} {rc : Cls}
    {fvs : Array Nat} {body : Term}
    {σ σ₁ σ_body σ_ret σ_end : AState} {deps regs owned : List Nat}
    {r_body : AVal} {consumed : Bool}
    (hcaps : ACaps aenv fvs.toList σ [] [] [] deps regs owned σ₁)
    (hbodyD : ATerm P
      ({ id := (restoreOwned owned σ₁).openReg.2.st.size,
         mode := p.mode,
         val := paramVal p (restoreOwned owned σ₁).openReg.1 } :: aenv)
      body
      ((restoreOwned owned σ₁).openReg.2.pushBnd
        (paramVal p (restoreOwned owned σ₁).openReg.1) (p.mode.usage == .once)).2
      r_body σ_body)
    (hbodyIH : ATermProp P ext B
      ({ id := (restoreOwned owned σ₁).openReg.2.st.size,
         mode := p.mode,
         val := paramVal p (restoreOwned owned σ₁).openReg.1 } :: aenv)
      body
      ((restoreOwned owned σ₁).openReg.2.pushBnd
        (paramVal p (restoreOwned owned σ₁).openReg.1) (p.mode.usage == .once)).2
      r_body σ_body)
    (hretChk : Runs (retCheck r_body.skel res (restoreOwned owned σ₁).openReg.1
      { r_body with cls := rc } "a closure's result") σ_body () σ_ret)
    (hcons : ∀ x ∈ owned, σ_ret.st[x]?.getD .dead = .dead → consumed = true)
    (hσEnd : σ_end = { σ₁ with nextRegion := σ_ret.nextRegion }) :
    ATermProp P ext B aenv (.lam p res rc fvs body) σ
      { cls := .val, deps, regs, onceOnly := consumed, skel := .arrow p.mode p.skel res r_body.skel }
      σ_end := by
  classical
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero _ henvTaint henvNRF hForbidLt hBadDepEnd
  cases hlc with
  | lam hlcB hfvsIff =>
  cases hcfd with
  | lam hcfdB =>
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b =>
      have hbB : b ≤ B := by omega
      have hstep : (evalS P ext (n + 1) env (.lam p res rc fvs body)).run (st, b + 1) =
          match (formClosure P n env p res rc fvs body).run st with
          | .error e => .error e
          | .ok (rv, st') => .ok (rv, (st', b)) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only
        rw [MS_liftM_run]; cases (formClosure P n env p res rc fvs body).run st <;> rfl
      unfold TermPost; rw [hstep]
      have hok := hsim.2.1
      obtain ⟨hok₁, hle₁, _, hnr₁⟩ := ACaps_state_le hok hcaps
      obtain ⟨hszC₁, _, hoMem₁, hcapMem₁, hcapPair₁⟩ := ACaps_props hok hcaps
      have hokCall : AStateOk (restoreOwned owned σ₁) := (AStateOk_restoreOwned_eval owned σ₁ hok₁).1
      have hokOpen : AStateOk (restoreOwned owned σ₁).openReg.2 := (AStateOk.openReg hokCall).1
      have hokPush : AStateOk ((restoreOwned owned σ₁).openReg.2.pushBnd
          (paramVal p (restoreOwned owned σ₁).openReg.1) (p.mode.usage == .once)).2 :=
        (hokOpen.pushBnd _ _).1
      obtain ⟨hokBody, hleBody, hregBody⟩ := ATerm_state_le hokPush hbodyD
      have hretU := Runs_retCheck hokBody hretChk
      have hleRet : AStateLe σ_body σ_ret := hretU.2.1
      have hnrRetLe : σ₁.nextRegion ≤ σ_ret.nextRegion := by
        have h1 : (restoreOwned owned σ₁).nextRegion = σ₁.nextRegion := rfl
        have h2 : (restoreOwned owned σ₁).openReg.2.nextRegion = σ₁.nextRegion + 1 := by
          simp [AState.openReg, h1]
        have h3 : ((restoreOwned owned σ₁).openReg.2.pushBnd
            (paramVal p (restoreOwned owned σ₁).openReg.1) (p.mode.usage == .once)).2.nextRegion =
            σ₁.nextRegion + 1 := by simp [AState.pushBnd, h2]
        have := hleBody.2.1
        have := hleRet.2.1
        omega
      have hfvsScope : ∀ i ∈ fvs.toList, Scope i := fun i hi =>
        hfv i (.lam ((hfvsIff i).mp hi))
      have hnk₁ : NoKillOk NoKill σ₁ := fun d hd hdead => by
        apply hnkEnd d hd; rw [hσEnd]; exact hdead
      have hBadDep₁ : ∀ d, BadDep d → σ₁.st[d]? = some .live := fun d hd => by
        have := hBadDepEnd d hd; rw [hσEnd] at this; exact this
      have hsimB : Sim P ext b st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (by omega) (AStateLe.refl _) hok hsim.2.2.1 (RegsFuture.refl _)
          (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
          (PreservesActiveEnv.refl _ _ _ _ _) hsim
      have hstB : StOk P ext b st := StOk_mono (by omega) hst
      obtain ⟨_, _, hokEnd, hleEnd, _, hfc⟩ := acaps_formClosure_bridge (B := b) (fuel := n)
        (p := p) (res := res) (rc := rc) (fvs := fvs) (body := body)
        (nextReg_end := σ_ret.nextRegion) (consumed := consumed) (r_body_skel := r_body.skel)
        hstB hsimB henvNRF hFlt hForbidLt hnk₁ hBadDep₁ hfvsScope hcaps hnrRetLe
      have hIendEq : (⟨fun r => if r < σ₁.nextRegion then I.reg r else []⟩ : Interp) = I := by
        cases I with
        | mk reg =>
          congr 1; funext r
          by_cases hlt : r < σ₁.nextRegion
          · simp [hlt]
          · simp only [hlt, ↓reduceIte]
            exact (hIZero r (by omega)).symm
      rcases hfc with hSt | hOOF | ⟨rv, env', taint, st', hrun, hr', hnr', hstat', hstr',
        hsz', hcap', hoss', hpresF', honce', hssf', hst', hsim', henvNRF', hrvObj, henvLen',
        hcapProps, hbv', hno', hcf', hdou', hreach', hfootOk', hVSimFn, hDisj', hNrf'⟩
      · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · rw [hrun]
        refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
        cases hokEq
        obtain ⟨cap, hrvEq, hoNew⟩ := hrvObj
        -- Extract `PreservesLocs` outside unique captures from `formClosure_spec`
        have hpresOut : PreservesLocs
            (fun l => l < st.heap.objs.size ∧
              ∀ i ∈ fvs.toList, ∀ b0, env[i]? = some b0 → b0.mode.isUnique = true →
                ¬ OwnReach P st.heap b0.val l)
            st.heap st'.heap := by
          have hfvsSpec : ∀ i ∈ fvs.toList, ∀ b0, env[i]? = some b0 →
              b0.mode ≠ .erased ∧ DeepLive st.heap b0.val ∧ AcyclicFrom st.heap b0.val ∧
              (b0.mode.isUnique = true →
                OwnTreeFull P st.heap b0.val ∧ (b0.mode.isBorrowed = false → OpenUnder st.regions [] b0.val)) := by
            intro i hi b0 hbi0
            obtain ⟨ab, habi, hneAb, hvd0, hoo0, hno0, hctT, _⟩ := hcapMem₁ i hi
            obtain ⟨hmode, hneB⟩ := hsimB.2.2.2.2.2.1 i b0 ab (hfvsScope i hi) hbi0 habi
            have hact0 : ActiveVal σ (effVal ab) := ⟨hvd0, fun his => absurd his hno0⟩
            have hv0 := ((hneB hneAb).2.2.2.2.2 hact0)
            refine ⟨hmode ▸ hneAb, hv0.1.1, hv0.1.2.1, fun hu => ?_⟩
            by_cases hcv : (effVal ab).cls = .val
            · have hct : captureTransfers ab.mode = true := (captureTransfers_eq_isUnique _).trans (hmode ▸ hu)
              obtain ⟨hown, hlv, hrg, hdead1⟩ := (hctT hct).2 hcv
              have htr0 : Transferable σ NoKill (effVal ab) :=
                ⟨hcv, hown, hoo0, hno0, fun d hd => ⟨hlv d hd, fun hnkD => hnk₁ d hnkD (hdead1 d hd)⟩⟩
              refine ⟨(hv0.2.2.2.2.2.2.2 htr0).1, fun hnb => ?_⟩
              have hrgNil := hrg (hmode ▸ hnb)
              have hdou := hv0.2.1
              rw [hrgNil, Interp.regsOf_nil] at hdou
              exact hdou b0.val (HeldBy.refl _ _)
            · have hnv := hv0.2.2.2.1 hno0 hcv
              exact ⟨hnv.ownTreeFull.1, fun _ => hnv.deepOpenUnder_nil b0.val (HeldBy.refl _ _)⟩
          have hdisjSpec : ∀ (a b : Nat) (ia ib : Nat) (ba bb : Bnd), a ≠ b →
              fvs.toList[a]? = some ia → fvs.toList[b]? = some ib →
              env[ia]? = some ba → env[ib]? = some bb →
              ba.mode.isUnique = true →
              ∀ l, OwnReach P st.heap ba.val l → ¬ Reach st.heap bb.val l := by
            intro aidx bidx ia ib ba bb hab hia hib hba hbb hua l hor hrb
            have hiaM : ia ∈ fvs.toList := List.mem_of_getElem? hia
            have hibM : ib ∈ fvs.toList := List.mem_of_getElem? hib
            obtain ⟨aba, haba, hnea, hvda, hooa, hnoa, hctTa, _⟩ := hcapMem₁ ia hiaM
            obtain ⟨abb, habb, hneb, hvdb, _, hnob, _, _⟩ := hcapMem₁ ib hibM
            have hma := (hsimB.2.2.2.2.2.1 ia ba aba (hfvsScope ia hiaM) hba haba).1
            have hactA : ActiveVal σ (effVal aba) := ⟨hvda, fun his => absurd his hnoa⟩
            have hactB : ActiveVal σ (effVal abb) := ⟨hvdb, fun his => absurd his hnob⟩
            by_cases hcvA : (effVal aba).cls = .val
            · by_cases hcvB : (effVal abb).cls = .val
              · have hctA : captureTransfers aba.mode = true := (captureTransfers_eq_isUnique _).trans (hma ▸ hua)
                obtain ⟨hoA, hlvA, _, hdeadA⟩ := (hctTa hctA).2 hcvA
                have hdd := hcapPair₁ aidx bidx ia ib aba abb hab hia hib haba habb hctA hcvA hcvB
                have hiaNeIb : ia ≠ ib := by
                  intro hEq; subst hEq; rw [haba] at habb; cases habb
                  exact hdd aba.id List.mem_cons_self List.mem_cons_self
                have htrA : Transferable σ NoKill (effVal aba) :=
                  ⟨hcvA, hoA, hooa, hnoa, fun d hd => ⟨hlvA d hd, fun hnkD => hnk₁ d hnkD (hdeadA d hd)⟩⟩
                exact (hsimB.2.2.2.2.2.2 ia ib ba bb aba abb hiaNeIb (hfvsScope ia hiaM) (hfvsScope ib hibM)
                  hba haba hbb habb hnea hneb).1 hactA htrA hactB hdd l hor hrb
              · have hvB := (((hsimB.2.2.2.2.2.1 ib bb abb (hfvsScope ib hibM) hbb habb).2 hneb).2.2.2.2.2 hactB)
                exact OwnReach_not_numLoc hor ((hvB.2.2.2.1 hnob hcvB).reach_numLoc hrb)
            · have hvA := (((hsimB.2.2.2.2.2.1 ia ba aba (hfvsScope ia hiaM) hba haba).2 hnea).2.2.2.2.2 hactA)
              exact (hvA.2.2.2.1 hnoa hcvA).ownTreeFull.2 l hor
          rcases formClosure_spec hst.1 hfvsSpec hdisjSpec with hSt2 | hOOF2 |
            ⟨rv2, env2, taint2, st2, hrun2, _, _, _, _, _, _, _, _, hpres2, _⟩
          · rw [hrun] at hSt2; cases hSt2
          · rw [hrun] at hOOF2; cases hOOF2
          · rw [hrun] at hrun2; cases hrun2; exact hpres2
        have hpresNum' : ∀ (l : Nat) (o : Obj) (n : Nat),
            st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o := fun l o n ho hc =>
          (hpresOut l ⟨(Array.getElem?_eq_some_iff.mp ho).1,
            fun _ _ _ _ _ hor => OwnReach_not_numLoc hor ⟨o, n, ho, hc⟩⟩).trans ho
        have hpresEnv' : PreservesActiveEnv Scope env aenv σ_end st.heap st'.heap := by
          intro k bk abk hsc hbk habk hne haEnd
          have hvK := ((hsimB.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
          have ha0 := ActiveVal.of_AStateLe hok (hσEnd ▸ hleEnd) hvK.2.1 (fun x hx => (hvK.2.2.1 x hx).1) haEnd
          refine hpresOut.mono fun l hrK => ⟨(hvK.2.2.2.2 ha0).1.1.reach_lt_size hrK, fun i hi b0 hbi0 hu0 hor => ?_⟩
          obtain ⟨ab0, hab0, hne0, hvd0, hoo0, hno0, hctT0, _⟩ := hcapMem₁ i hi
          have hmode0 := (hsimB.2.2.2.2.2.1 i b0 ab0 (hfvsScope i hi) hbi0 hab0).1
          have hct0 : captureTransfers ab0.mode = true := (captureTransfers_eq_isUnique _).trans (hmode0 ▸ hu0)
          have hact0 : ActiveVal σ (effVal ab0) := ⟨hvd0, fun his => absurd his hno0⟩
          by_cases hcv0 : (effVal ab0).cls = .val
          · obtain ⟨ho0, hlv0, _, hdead0⟩ := (hctT0 hct0).2 hcv0
            have hdd : ∀ d ∈ (effVal ab0).deps, d ∉ (effVal abk).deps := fun d hd hdk => by
              have hdeadE : σ_end.st[d]? = some .dead := by rw [hσEnd]; exact hdead0 d hd
              exact (haEnd.1 d hdk).2 hdeadE
            have hik : i ≠ k := fun hEq => by
              subst hEq; rw [hab0] at habk; cases habk
              exact hdd abk.id List.mem_cons_self List.mem_cons_self
            have htr0 : Transferable σ NoKill (effVal ab0) :=
              ⟨hcv0, ho0, hoo0, hno0, fun d hd => ⟨hlv0 d hd, fun hnkD => hnk₁ d hnkD (hdead0 d hd)⟩⟩
            exact (hsimB.2.2.2.2.2.2 i k b0 bk ab0 abk hik (hfvsScope i hi) hsc hbi0 hab0 hbk habk hne0 hne).1
              hact0 htr0 ha0 hdd l hor hrK
          · have hv0 := (((hsimB.2.2.2.2.2.1 i b0 ab0 (hfvsScope i hi) hbi0 hab0).2 hne0).2.2.2.2.2 hact0)
            exact (hv0.2.2.2.1 hno0 hcv0).ownTreeFull.2 l hor
        -- Prove `FunOkAt P ext b st' (.arrow p.mode p.skel res r_body.skel) consumed cloFoot rv`
        let cloFoot : Nat → Prop := fun l =>
          consumed = true ∧ ∃ i ∈ fvs.toList, ∃ b0, env[i]? = some b0 ∧
            b0.mode.isUnique = true ∧ OwnReach P st.heap b0.val l
        have hFunClo : FunOkAt P ext b st' (.arrow p.mode p.skel res r_body.skel) consumed cloFoot rv := by
          cases b with
          | zero => rw [FunOkAt]; trivial
          | succ b' =>
            rw [FunOkAt]
            intro B_call fuel_c st_call f_call a c_app Frame_call fRegs aRegs aOnce aFoot
              hBc hst_call hstat_call hFlt_call hloc hsh hrf hfBase hfOpen hfCf
              haBase haOpen haCf hFclo hFa hFootDisj hfa2 haf2 haNum harg
            dsimp only [arrowParts] at haNum harg ⊢
            let σ_call := restoreOwned owned σ₁
            let s_a := σ_call.openReg.1
            let σ_open := σ_call.openReg.2
            let s_c := st_call.nextRegion
            let st_open : St := { st_call with nextRegion := s_c + 1, regions := s_c :: st_call.regions }
            let NoKill_call : Nat → Prop := if consumed then fun _ => False else (· ∈ owned)
            let I_base : Interp := ⟨fun r =>
              if r == 1 then (aRegs ++ fRegs).filter (· < s_c) else fRegs.filter (· < s_c)⟩
            let I_open : Interp := I_base.extend s_a s_c
            obtain ⟨cap_c, taint_c, o_c, env_call, hfEq, ho_c, hcap_c, hcell_c,
              _, _, hstOpen, hregU0, hnkOpen, _, hsim_open0, hNrfOpen0,
              hIopenRegs, hIopen1, henvReachF⟩ :=
              clo_call_sim_of_captures (B := b' + 1) (B_call := B_call)
                hsimB hnk₁ hfvsScope hcaps hrvEq hoNew hr' hoss' henvLen' hcapProps
                (by omega) hst_call hstat_call hloc hsh hrf hfBase hfOpen hfCf hFclo
            -- Restrict `I_open` to `< σ_open.nextRegion` so `hIZero` holds for `body`!
            let I_zero : Interp := ⟨fun r => if r < σ_open.nextRegion then I_open.reg r else []⟩
            have hIzeroEq : ∀ r, r < σ_open.nextRegion → I_zero.reg r = I_open.reg r := fun r hr => by
              dsimp only [I_zero]; simp [hr]
            have hIzeroGe : ∀ r, σ_open.nextRegion ≤ r → I_zero.reg r = [] := fun r hr => by
              dsimp only [I_zero]; simp [Nat.not_lt_of_ge hr]
            have hsaLt : s_a < σ_open.nextRegion := by simp [s_a, σ_open, AState.openReg]
            have hIzero_sa : I_zero.reg s_a = [s_c] := by
              rw [hIzeroEq s_a hsaLt]; simp [I_open, Interp.extend]
            have h1ltOpen : 1 < σ_open.nextRegion := by
              have := hokOpen.2.2.1; change 1 < (restoreOwned owned σ₁).openReg.2.nextRegion; omega
            have hIzero_1 : ∀ c, c ∈ aRegs → c < s_c → c ∈ I_zero.reg 1 := fun c hc hlt => by
              rw [hIzeroEq 1 h1ltOpen]; exact hIopen1 c hc hlt
            have hIok_zero : InterpOk σ_open st_open I_zero :=
              ⟨fun r hr c hc => by rw [hIzeroEq r hr] at hc; exact hsim_open0.2.2.1.1 r hr c hc,
               fun c hc => by
                 have hhdLt : σ_open.regions.headD 1 < σ_open.nextRegion := by
                   simp only [σ_open, AState.openReg, List.headD]; exact hsaLt
                 rw [hIzeroEq _ hhdLt]; exact hsim_open0.2.2.1.2 c hc⟩
            have hsim_open : Sim P ext B_call st_open Frame_call NoKill_call (fun _ => False) (· ∈ fvs.toList)
                env_call aenv σ_open I_zero (fun _ _ => False) :=
              Sim_interp_congr hIok_zero (fun r hr => (hIzeroEq r hr).symm) hsim_open0
            have hregU_body : RegUnique I_zero σ_body s_a s_c := by
              refine ⟨hIzero_sa, fun r _ hne hmem => ?_⟩
              by_cases hlt : r < σ_open.nextRegion
              · rw [hIzeroEq r hlt] at hmem
                exact hregU0.2 r hlt hne hmem
              · rw [hIzeroGe r (Nat.le_of_not_lt hlt)] at hmem; cases hmem
            -- Prove `EnvTaintOk (· ∈ fvs.toList) env_call aenv st_open I_zero`
            have henvTaint_open : EnvTaintOk (· ∈ fvs.toList) env_call aenv st_open I_zero := by
              intro i b_c ab hi hbc habi hneAb
              have hhb : HeldBy st_call.heap f_call b_c.val := by
                rw [hfEq]
                exact Or.inr ⟨st.heap.objs.size, o_c, .here, ho_c, by
                  rw [hcell_c]; simp only [Cell.vals, List.mem_filterMap]
                  exact ⟨i, hi, by simp [hbc]⟩⟩
              have hbaseC : ValBaseOk st_call b_c.val := ValBaseOk.sub hfBase hhb
              refine ⟨fun c hc => Nat.lt_succ_of_lt (hbaseC.2.2.2 b_c.val (HeldBy.refl _ _) c hc), fun c hc hopen => ?_⟩
              have hcLt : c < s_c := hbaseC.2.2.2 b_c.val (HeldBy.refl _ _) c hc
              have hcOpenC : c ∈ st_call.regions := by
                rcases List.mem_cons.mp hopen with rfl | hm
                · exact absurd hcLt (Nat.lt_irrefl _)
                · exact hm
              have hcF : c ∈ fRegs := hfOpen b_c.val hhb c hc hcOpenC
              cases hregs : (effVal ab).regs with
              | nil =>
                obtain ⟨b0, v', hbi0, hbi', hvsh1, _, _, _, _⟩ := hcapProps i hi
                have hclSh : CellSameShape (.clo env' p res rc fvs body) (.clo env_call p res rc fvs body) := by
                  have hrHere : Reach st'.heap rv st.heap.objs.size := by rw [hrvEq]; exact .here
                  obtain ⟨o2, ho2, hcs⟩ := hsh st.heap.objs.size ⟨.clo env' p res rc fvs body, cap⟩ hrHere hoNew
                  rw [ho_c] at ho2; cases ho2; rw [← hcell_c]; exact hcs
                have hvsh2 : ValSameShape v' b_c.val := by
                  have h1 := hclSh.2.2.2.2.2.2 i
                  rw [hbi', hbc] at h1; exact h1.2
                have htEq : b_c.val.taint = b0.val.taint := by
                  rw [← hvsh2.taint_eq, ← hvsh1.taint_eq]
                have hopen0 : OpenUnder st.regions [] b0.val := by
                  have ht0 := (henvTaint i b0 ab (hfvsScope i hi) hbi0 habi hneAb).2
                  rw [hregs, Interp.regsOf_nil] at ht0; exact ht0
                have htb0 : ∀ r ∈ b0.val.taint, r < st'.nextRegion := fun r hr => by
                  rw [hnr']; exact (henvTaint i b0 ab (hfvsScope i hi) hbi0 habi hneAb).1 r hr
                have hcIn0 : c ∈ st'.regions := by
                  have hc0 : c ∈ b0.val.taint := htEq ▸ hc
                  exact (hrf.2 c hcOpenC).resolve_right (Nat.not_le_of_lt (htb0 c hc0))
                rw [hr'] at hcIn0
                cases hopen0 c (htEq ▸ hc) hcIn0
              | cons rg0 rgs =>
                have hrg0Lt : rg0 < s_a := by
                  obtain ⟨b0, _, hbi0, _⟩ := hcapProps i hi
                  have hv0 := ((hsimB.2.2.2.2.2.1 i b0 ab (hfvsScope i hi) hbi0 habi).2 hneAb).2
                  have h1 := hv0.1 rg0 (hregs ▸ List.mem_cons_self)
                  change rg0 < (restoreOwned owned σ₁).nextRegion
                  change rg0 < σ₁.nextRegion; omega
                refine Interp.mem_regsOf.mpr ⟨rg0, List.mem_cons_self, ?_⟩
                rw [hIzeroEq rg0 (Nat.lt_trans hrg0Lt hsaLt)]
                dsimp only [I_open, Interp.extend]
                rw [beq_false_of_ne (Nat.ne_of_lt hrg0Lt)]
                simp only [Bool.false_eq_true, ↓reduceIte, I_base]
                by_cases h1 : (rg0 == 1) = true
                · simp only [h1, ↓reduceIte, List.mem_filter, List.mem_append, decide_eq_true_eq]
                  exact ⟨Or.inr hcF, hcLt⟩
                · simp only [h1, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
                  exact ⟨hcF, hcLt⟩
            cases fuel_c with
            | zero =>
              have h0 : (applyOneConformS P ext 0 f_call a c_app).run (st_call, B_call) = .error .outOfFuel := by
                cases B_call with
                | zero => unfold applyOneConformS applyOneS; rw [MS_bind_run, MS_bind_run, MS_spend_zero]
                | succ bc => unfold applyOneConformS applyOneS; rw [MS_bind_run, MS_bind_run, MS_spend_succ]; rfl
              rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            | succ nf =>
              cases B_call with
              | zero =>
                have h0 : (applyOneConformS P ext (nf + 1) f_call a c_app).run (st_call, 0) = .error .outOfFuel := by
                  unfold applyOneConformS applyOneS; rw [MS_bind_run, MS_bind_run, MS_spend_zero]
                rw [h0]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              | succ bc =>
                have hstepA : (applyOneConformS P ext (nf + 1) f_call a c_app).run (st_call, bc + 1) =
                    (do
                      let bnd ← liftM (bindAt P nf s_c p.mode p.cls a)
                      let r ← evalS P ext nf (bnd :: env_call) body
                      let r ← liftM (ret P nf s_c (st_call.regions.headD 0) res rc r)
                      liftM (closeRegion s_c)
                      let r ← liftM (conform c_app r)
                      liftM (conform c_app r)).run (st_open, bc) := by
                  unfold applyOneConformS applyOneS
                  rw [MS_bind_run, MS_bind_run, MS_spend_succ]; dsimp only
                  rw [hfEq]; dsimp only
                  rw [MS_bind_run, MS_liftM_run]
                  have hobj : (obj st.heap.objs.size).run st_call = .ok (o_c, st_call) := by
                    unfold obj; rw [M_bind_run, M_get_run]; simp [ho_c]; rfl
                  rw [hobj]; dsimp only
                  have hcapB : (o_c.cap == cap_c) = true := beq_iff_eq.mpr hcap_c
                  simp only [hcapB, ↓reduceIte, hcell_c]
                  rw [MS_bind_run, MS_liftM_run]
                  have hopenR : openRegion.run st_call = .ok ((s_c, st_call.regions.headD 0), st_open) := rfl
                  rw [hopenR]; dsimp only
                  simp only [MS_bind_run, MS_liftM_run]
                  cases (bindAt P nf s_c p.mode p.cls a).run st_open with
                  | error _ => rfl
                  | ok pb =>
                    rcases pb with ⟨bv, stb⟩
                    simp only [MS_bind_run]
                    cases (evalS P ext nf (bv :: env_call) body).run (stb, bc) with
                    | error _ => rfl
                    | ok pr =>
                      rcases pr with ⟨rv_0, ⟨st_0, b_0⟩⟩
                      simp only [MS_bind_run, MS_liftM_run]
                      cases (ret P nf s_c (st_call.regions.headD 0) res rc rv_0).run st_0 with
                      | error _ => rfl
                      | ok pret =>
                        rcases pret with ⟨rv_1, st_1⟩
                        simp only [MS_bind_run, MS_liftM_run]
                        cases (closeRegion s_c).run st_1 with
                        | error _ => rfl
                        | ok pcls =>
                          rcases pcls with ⟨⟨⟩, st_2⟩
                          simp only [MS_bind_run, MS_liftM_run]
                have hsim_open_bc : Sim P ext bc st_open Frame_call NoKill_call (fun _ => False) (· ∈ fvs.toList)
                    env_call aenv σ_open I_zero (fun _ _ => False) :=
                  Sim_step (by omega) (AStateLe.refl _) hokOpen hsim_open.2.2.1 (RegsFuture.refl _)
                    (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
                    (PreservesActiveEnv.refl _ _ _ _ _) hsim_open
                have harg_bc : p.mode ≠ .erased →
                    (p.mode.usage = .once → FunOkAt P ext bc st_call p.skel aOnce aFoot a) ∧
                    (p.mode.usage ≠ .once → NoOnceCell st_call.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
                      FunOkAt P ext bc st_call p.skel false (fun _ => False) a) ∧
                    (p.mode.isUnique = true → OwnTreeFull P st_call.heap a ∧
                      (∀ l, OwnReach P st_call.heap a l → ¬ Frame_call l ∧ ¬ Reach st_call.heap f_call l) ∧
                      (p.mode.isBorrowed = false → DeepOpenUnder st_call.heap st_call.regions [] a)) ∧
                    (res = .unique ∧ c_app = .val ∧ (p.mode = .many ∨ p.mode = .once) →
                      DeepOpenUnder st_call.heap st_call.regions [] a) := fun hne =>
                  let ⟨h1, h2, h3, h4⟩ := harg hne
                  ⟨fun ho => FunOkAt_mono (by omega) (h1 ho),
                   fun hnu => let ⟨a1, a2, a3, a4⟩ := h2 hnu; ⟨a1, a2, a3, FunOkAt_mono (by omega) a4⟩,
                   h3, h4⟩
                have hOwnDisjA : ∀ (i : Nat) (b_c : Bnd) (ab : ABnd), i ∈ fvs.toList →
                    env_call[i]? = some b_c → aenv[i]? = some ab → ab.mode ≠ .erased →
                    ActiveVal σ_open (effVal ab) → Transferable σ_open NoKill_call (effVal ab) →
                    ∀ l, OwnReach P st_call.heap b_c.val l → ¬ Reach st_call.heap a l := by
                  intro i b_c ab hi hbc habi hneAb _ htrAb l hor hra
                  obtain ⟨ab1, hab1, _, hvd0, _, hno0, hctT1, hctF1⟩ := hcapMem₁ i hi
                  rw [habi] at hab1; cases hab1
                  have hstLv : σ_open.st[ab.id]? = some .live := (htrAb.2.2.2.2 ab.id List.mem_cons_self).1
                  have huM : ab.mode.isUnique = true := by
                    by_cases hu : ab.mode.isUnique = true
                    · exact hu
                    · exfalso
                      have hctF : captureTransfers ab.mode = false := by
                        rw [captureTransfers_eq_isUnique]; exact Bool.eq_false_iff.mpr hu
                      have hnotOwn : ab.id ∉ owned := fun hmem => by
                        rcases hoMem₁ ab.id hmem with hm0 | ⟨j, _, abj, habj, hidj, hctj⟩
                        · cases hm0
                        · have hji : j = i := hsimB.2.2.2.2.1 j i abj ab habj habi hidj
                          subst hji; rw [habi] at habj; cases habj; rw [hctF] at hctj; cases hctj
                      have hst1Lv : σ₁.st[ab.id]? = some .live := by
                        have := restoreOwned_getElem?_not_mem owned σ₁ ab.id hnotOwn
                        exact this.symm.trans hstLv
                      exact hctF1 hctF htrAb.1 hst1Lv
                  have hctT : captureTransfers ab.mode = true := (captureTransfers_eq_isUnique _).trans huM
                  have hInOwn : ab.id ∈ owned := (hctT1 hctT).1
                  have hconsT : consumed = true := by
                    by_cases hc : consumed = true
                    · exact hc
                    · exfalso
                      have hcfF : consumed = false := Bool.eq_false_iff.mpr hc
                      have hnotNK := (htrAb.2.2.2.2 ab.id List.mem_cons_self).2
                      simp only [NoKill_call, hcfF, Bool.false_eq_true, ↓reduceIte] at hnotNK
                      exact hnotNK hInOwn
                  have hclSh : CellSameShape (.clo env' p res rc fvs body) (.clo env_call p res rc fvs body) := by
                    have hrHere : Reach st'.heap rv st.heap.objs.size := by rw [hrvEq]; exact .here
                    obtain ⟨o2, ho2, hcs⟩ := hsh st.heap.objs.size ⟨.clo env' p res rc fvs body, cap⟩ hrHere hoNew
                    rw [ho_c] at ho2; cases ho2; rw [← hcell_c]; exact hcs
                  obtain ⟨b0, v', hbi0, hbi', hvsh1, hbv', _, _, _⟩ := hcapProps i hi
                  have hvsh2 : ValSameShape v' b_c.val := by
                    have h1 := hclSh.2.2.2.2.2.2 i
                    rw [hbi', hbc] at h1; exact h1.2
                  have hmode0 : b0.mode = ab.mode := (hsimB.2.2.2.2.2.1 i b0 ab (hfvsScope i hi) hbi0 habi).1
                  have hshV' : SameShapeOn (Reach st'.heap v') st'.heap st_call.heap := by
                    intro l' o' hrl' ho'
                    have hrRv' : Reach st'.heap rv l' := by
                      rw [hrvEq]
                      exact .step hoNew (by simp only [Cell.vals, List.mem_filterMap]; exact ⟨i, hi, by simp [hbi']⟩) hrl'
                    exact hsh l' o' hrRv' ho'
                  have horV' : OwnReach P st'.heap v' l :=
                    OwnReach_of_sameShapeOn_rev hbv'.1 hshV' (SameLoc.of_valSameShape hvsh2) hor
                  have hdlB0 : DeepLive st.heap b0.val :=
                    (((hsimB.2.2.2.2.2.1 i b0 ab (hfvsScope i hi) hbi0 habi).2 hneAb).2.2.2.2.2 ⟨hvd0, fun his => absurd his hno0⟩).1.1
                  exact haf2 l hra ⟨hconsT, i, hi, b0, hbi0, hmode0 ▸ huM,
                    OwnReach_of_sameShapeOn_rev hdlB0 (hoss'.to_sameShapeOn _) (SameLoc.of_valSameShape hvsh1) horV'⟩
                rcases clo_bindParam_push (P := P) (ext := ext) (B := bc) (fuel := nf)
                    (s_a := s_a) (s_c := s_c) (res := res) (c_app := c_app)
                    (st_call := st_call) (Frame_call := Frame_call) (NoKill_call := NoKill_call)
                    (Scope := (· ∈ fvs.toList)) (env_call := env_call) (aenv := aenv)
                    (σ_open := σ_open) (I_open := I_zero)
                    (f_call := f_call) (a := a) (aRegs := aRegs) (aOnce := aOnce) (aFoot := aFoot) (p := p)
                    (StOk_mono (by omega) hst_call) hstat_call hFlt_call hsaLt hIzero_sa hIzero_1
                    hsim_open_bc rfl (fun i b_c hi => henvReachF i hi b_c) henvTaint_open haBase haOpen (CtorFieldsOk_mono (by omega) haCf)
                    hFa hfa2 haNum harg_bc hOwnDisjA with hStB | hOOFB |
                  ⟨bnd, st₂, bFoot, hrunBind, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
                   hpFrame₂, hpSS₂, honce₂, hssf₂, hst₂, hsimP, henvTaintP, henvNRFP⟩
                · rw [hstepA, MS_bind_run, MS_liftM_run, hStB]
                  exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                · rw [hstepA, MS_bind_run, MS_liftM_run, hOOFB]
                  exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                · rw [hstepA, MS_bind_run, MS_liftM_run, hrunBind]; dsimp only
                  have hNoKill_ret : NoKillOk NoKill_call σ_ret := by
                    intro d hd hdead
                    by_cases hc : consumed = true
                    · simp only [NoKill_call, hc, ↓reduceIte] at hd
                    · have hcfF : consumed = false := Bool.eq_false_iff.mpr hc
                      simp only [NoKill_call, hcfF, Bool.false_eq_true, ↓reduceIte] at hd
                      have h1 := hcons d hd (by rw [hdead]; rfl)
                      rw [hcfF] at h1; cases h1
                  have hNoKill_body : NoKillOk NoKill_call σ_body :=
                    NoKillOk_of_AStateLe hleRet hNoKill_ret
                  have hIZero_push : ∀ r, ((σ_open.pushBnd (paramVal p s_a) (p.mode.usage == .once)).2).nextRegion ≤ r → I_zero.reg r = [] :=
                    fun r hr => hIzeroGe r (by simpa [AState.pushBnd] using hr)
                  have hHeadReg_push : st₂.regions.headD 0 = 0 ∨
                      st₂.regions.headD 0 ∈ I_zero.reg (((σ_open.pushBnd (paramVal p s_a) (p.mode.usage == .once)).2).regions.headD 1) := by
                    right; rw [hrg₂]; dsimp only [st_open, σ_open, AState.pushBnd, AState.openReg, List.headD]
                    change s_c ∈ I_zero.reg s_a; rw [hIzero_sa]; exact List.mem_cons_self
                  have hForbLt₂ : ∀ l, (l < st_call.heap.objs.size ∧ ¬ Reach st_call.heap f_call l ∧
                      ¬ StaticStrLoc st_call l ∧
                      (res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased) ∨ ¬ Reach st_call.heap a l)) →
                      l < st₂.heap.objs.size := fun l hf => Nat.lt_of_lt_of_le hf.1 hsz₂
                  have hstat₂F : ∀ l, StaticStrLoc st₂ l → Frame_call l := fun l hss =>
                    hstat_call l (StaticStrLoc_of_preserves_outside hstat₂ hstr₂ hpSS₂ l hss)
                  have hFlt₂ : ∀ l, Frame_call l → l < st₂.heap.objs.size := fun l hF =>
                    Nat.lt_of_lt_of_le (hFlt_call l hF) hsz₂
                  obtain ⟨hnoVB, hokB⟩ := hbodyIH hlcB hcfdB (B₀ := bc) (fuel := nf)
                    (by omega) (shiftScope_of_freeVarIn fun x hx => (hfvsIff x).mpr hx)
                    hst₂ hsimP hstat₂F hFlt₂ hNoKill_body (fun _ h => False.elim h)
                    hIZero_push hHeadReg_push henvTaintP henvNRFP hForbLt₂ (fun _ h => False.elim h)
                  rw [MS_bind_run]
                  cases hevalB : (evalS P ext nf (bnd :: env_call) body).run (st₂, bc) with
                  | error e =>
                    refine ⟨fun k hk => by cases hk; exact hnoVB k hevalB, fun _ _ _ h => by cases h⟩
                  | ok pb =>
                    rcases pb with ⟨rv_b, ⟨st₃, B₃⟩⟩; dsimp only
                    obtain ⟨rvFoot, hB₃, hst₃, hsz₃, hcap₃, hr₃, hnr₃, hstat₃, hstr₃,
                      hpFrame₃, _, _, honce₃, hssf₃, hsim₃, _, henvNRF₃, hvR₃, hdisjR₃, hnrfR₃, _, _, _, _⟩ :=
                      hokB rv_b st₃ B₃ hevalB
                    have hcurLt : st_call.regions.headD 0 < st₃.nextRegion := by
                      have h1 : st_open.nextRegion = s_c + 1 := rfl
                      have h2 : st₂.nextRegion = s_c + 1 := hnr₂.trans h1
                      cases hcr : st_call.regions with
                      | nil =>
                        simp only [List.headD]; omega
                      | cons c0 cs =>
                        simp only [List.headD]
                        have hc0 := (hst_call.2.1.2.2 c0 (hcr ▸ List.mem_cons_self)).2
                        omega
                    have hFlt₃ : ∀ l, Frame_call l → l < st₃.heap.objs.size := fun l hF =>
                      Nat.lt_of_lt_of_le (hFlt₂ l hF) hsz₃
                    have hsIn₃ : s_c ∈ st₃.regions := by
                      rw [hr₃, hrg₂]; exact List.mem_cons_self
                    rcases retCheck_bridge (fuel := nf) (s_a := s_a) (s_c := s_c) (cur := st_call.regions.headD 0)
                        hst₃ hsim₃ henvNRF₃ hFlt₃ hNoKill_ret hcurLt hregU_body hsIn₃ hvR₃ hdisjR₃ hretChk with
                      hStR | hOOFR | ⟨rv_r, st₄, hrunR, hr₄, hnr₄, hstat₄, hstr₄, hsz₄, hcap₄,
                        hpFrame₄, hpSS₄, honce₄, hssf₄, hst₄, _, _, hbv₄, hcls₄, hno₄, hcf₄,
                        hfunExp₄, _, hnvNe₄, _, huniq₄, hdouSU₄, hdouU₄, hdouB₄, hreach₄, hown₄, _, _⟩
                    · rw [MS_bind_run, MS_liftM_run, hStR]
                      exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                    · rw [MS_bind_run, MS_liftM_run, hOOFR]
                      exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                    · rw [MS_bind_run, MS_liftM_run, hrunR]; dsimp only
                      let st₅ : St := { st₄ with regions := st₄.regions.filter (· != s_c) }
                      have hcloseRun : (closeRegion s_c).run st₄ = .ok ((), st₅) := rfl
                      rw [MS_bind_run, MS_liftM_run, hcloseRun]; dsimp only
                      have hrg₅ : st₅.regions = st_call.regions := by
                        dsimp only [st₅]
                        rw [hr₄, hr₃, hrg₂]; dsimp only [st_open]
                        have hneS : ∀ r ∈ st_call.regions, (r != s_c) = true := fun r hr =>
                          bne_iff_ne.mpr (Nat.ne_of_lt (hst_call.2.1.2.2 r hr).2)
                        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                        exact List.filter_eq_self.mpr hneS
                      have hst₅ : StOk P ext B₃ st₅ := StOk_closeRegion s_c hst₄
                      have hrf₄₅ : RegsFuture st₄ st₅ := RegsFuture.closeRegion st₄ s_c
                      have hbv₅ : ValBaseOk st₅ rv_r :=
                        ValBaseOk_congr (st := st₄) (st' := st₅) (PreservesLocs.refl _ _) hrf₄₅.1 hbv₄
                      have hcf₅ : CtorFieldsOk P ext B₃ st₅ rv_r :=
                        CtorFieldsOk_congr hbv₄.1 (PreservesLocs.refl _ _) hrf₄₅ hcf₄
                      have hfun₅ : FunOkAt P ext B₃ st₅ r_body.skel false (fun _ => False) rv_r :=
                        FunOkAt_preserve_locs (st₀ := st₄) (st₁ := st₅) (PreservesLocs.refl _ _) hrf₄₅ hfunExp₄
                      have hIfiltSub : ∀ x ∈ I_zero.regsOf (r_body.regs.filter (· != s_a)), x ∈ aRegs ++ fRegs := by
                        intro x hx
                        obtain ⟨rg, hrgF, hxRg⟩ := Interp.mem_regsOf.mp hx
                        rw [List.mem_filter] at hrgF
                        have hneSa : rg ≠ s_a := bne_iff_ne.mp hrgF.2
                        by_cases hltO : rg < σ_open.nextRegion
                        · rw [hIzeroEq rg hltO] at hxRg
                          exact (hIopenRegs rg hltO hneSa x hxRg).1
                        · rw [hIzeroGe rg (Nat.le_of_not_lt hltO)] at hxRg; cases hxRg
                      have hopen₅ : c_app = .val →
                          DeepOpenUnder st₅.heap st₅.regions (applyResultRegs st₅ res .val fRegs aRegs) rv_r := by
                        intro _
                        have hregFilt : st₃.regions.filter (· != s_c) = st₅.regions := by
                          dsimp only [st₅]; rw [hr₄]
                        rw [← hregFilt]
                        have hvalF : (Cls.val != Cls.val) = false := rfl
                        cases hrm : res with
                        | unique =>
                          unfold applyResultRegs; simp only [hvalF, Bool.false_eq_true, ↓reduceIte]
                          exact DeepOpenUnder.mono (hdouU₄ hrm) (fun _ h => by cases h)
                        | shared =>
                          unfold applyResultRegs; simp only [hvalF, Bool.false_eq_true, ↓reduceIte]
                          exact hdouSU₄ (aRegs ++ fRegs) (Or.inl hrm) hIfiltSub
                        | borrowed =>
                          have hcurIn : st_call.regions.headD 0 = 0 ∨
                              st_call.regions.headD 0 ∈ applyResultRegs st₅ .borrowed .val fRegs aRegs := by
                            unfold applyResultRegs; simp only [hvalF, Bool.false_eq_true, ↓reduceIte]; rw [hrg₅]
                            cases hcr : st_call.regions with
                            | nil => left; rfl
                            | cons c0 cs => right; exact List.mem_cons_self
                          have hsub : ∀ x ∈ I_zero.regsOf (r_body.regs.filter (· != s_a)),
                              x ∈ applyResultRegs st₅ .borrowed .val fRegs aRegs := fun x hx => by
                            have hx1 := hIfiltSub x hx
                            unfold applyResultRegs; simp only [hvalF, Bool.false_eq_true, ↓reduceIte]; rw [hrg₅]
                            cases hcr : st_call.regions with
                            | nil => exact hx1
                            | cons c0 cs => exact List.mem_cons_of_mem _ hx1
                          exact hdouB₄ _ (by rw [hrm]; rfl) hsub (Or.inr hcurIn)
                        | uniqueBorrowed =>
                          have hcurIn : st_call.regions.headD 0 = 0 ∨
                              st_call.regions.headD 0 ∈ applyResultRegs st₅ .uniqueBorrowed .val fRegs aRegs := by
                            unfold applyResultRegs; simp only [hvalF, Bool.false_eq_true, ↓reduceIte]; rw [hrg₅]
                            cases hcr : st_call.regions with
                            | nil => left; rfl
                            | cons c0 cs => right; exact List.mem_cons_self
                          have hsub : ∀ x ∈ I_zero.regsOf (r_body.regs.filter (· != s_a)),
                              x ∈ applyResultRegs st₅ .uniqueBorrowed .val fRegs aRegs := fun x hx => by
                            have hx1 := hIfiltSub x hx
                            unfold applyResultRegs; simp only [hvalF, Bool.false_eq_true, ↓reduceIte]; rw [hrg₅]
                            cases hcr : st_call.regions with
                            | nil => exact hx1
                            | cons c0 cs => exact List.mem_cons_of_mem _ hx1
                          exact hdouB₄ _ (by rw [hrm]; rfl) hsub (Or.inr hcurIn)
                      rcases conform_post_apply (res := res) (fRegs := fRegs) (aRegs := aRegs) (c := c_app)
                          hst₅ hbv₅ hcf₅ (fun _ => hno₄) hfun₅ hopen₅ with hStC1 |
                        ⟨rv₁, st₆, hrunC1, hrg₆, hnr₆, hstat₆, hstr₆, hsz₆, hcap₆, hp₆, honce₆, hssf₆,
                         hst₆, hbv₆, hcls₆, hopen₆, hcf₆, hreach₆, hno₆, hfun₆, hcval₆⟩
                      · rw [MS_bind_run, MS_liftM_run, hStC1]
                        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                      · rw [MS_bind_run, MS_liftM_run, hrunC1]; dsimp only
                        have hopen₆' : c_app = .val →
                            DeepOpenUnder st₆.heap st₆.regions (applyResultRegs st₆ res .val fRegs aRegs) rv₁ := fun hcv => by
                          subst hcv
                          obtain ⟨rfl, rfl⟩ := hcval₆ rfl
                          exact hopen₅ rfl
                        rcases conform_post_apply (res := res) (fRegs := fRegs) (aRegs := aRegs) (c := c_app)
                            hst₆ hbv₆ hcf₆ hno₆ hfun₆ hopen₆' with hStC2 |
                          ⟨rv₂, st₇, hrunC2, hrg₇, hnr₇, hstat₇, hstr₇, hsz₇, hcap₇, hp₇, honce₇, hssf₇,
                           hst₇, hbv₇, hcls₇, hopen₇, hcf₇, hreach₇, hno₇, hfun₇, hcval₇⟩
                        · rw [MS_liftM_run, hStC2]
                          exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
                        · rw [MS_liftM_run, hrunC2]
                          refine ⟨(fun _ h => by cases h), fun rvF stF BF hokF => ?_⟩
                          cases hokF
                          have hstOpenSz : st_open.heap.objs.size = st_call.heap.objs.size := rfl
                          have hstOpenCap : st_open.heap.nextCap = st_call.heap.nextCap := rfl
                          have hstOpenNr : st_open.nextRegion = st_call.nextRegion + 1 := rfl
                          have hst5Sz : st₅.heap.objs.size = st₄.heap.objs.size := rfl
                          have hst5Cap : st₅.heap.nextCap = st₄.heap.nextCap := rfl
                          have hst5Nr : st₅.nextRegion = st₄.nextRegion := rfl
                          have hst2Nr : st₂.nextRegion = st_call.nextRegion + 1 := hnr₂
                          have hrgAll : st₇.regions = st_call.regions := hrg₇.trans (hrg₆.trans hrg₅)
                          have hnrAll : st_call.nextRegion ≤ st₇.nextRegion := by omega
                          have hszAll : st_call.heap.objs.size ≤ st₇.heap.objs.size := by omega
                          have hcapAll : st_call.heap.nextCap ≤ st₇.heap.nextCap := by omega
                          have hstatAll : ArrayExtends st_call.statics st₇.statics := by
                            rw [hstat₇, hstat₆, hstat₄, ← hstat₂]; exact hstat₃
                          have hstrAll : ArrayExtends st_call.strs st₇.strs := by
                            rw [hstr₇, hstr₆, hstr₄, ← hstr₂]; exact hstr₃
                          have hpFrame₆ : PreservesLocs Frame_call st₄.heap st₆.heap :=
                            hp₆.mono fun l hF => Nat.lt_of_lt_of_le (hFlt₃ l hF) hsz₄
                          have hpFrame₇ : PreservesLocs Frame_call st₆.heap st₇.heap :=
                            hp₇.mono fun l hF => Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hFlt₃ l hF) hsz₄) hsz₆
                          have hpFrameAll : PreservesLocs Frame_call st_call.heap st₇.heap :=
                            hpFrame₂.trans (hpFrame₃.trans (hpFrame₄.trans (hpFrame₆.trans hpFrame₇)))
                          have honceAll : PreservesOnceShell st_call.heap st₇.heap :=
                            honce₂.trans (honce₃.trans (honce₄.trans (honce₆.trans honce₇)))
                          have hpSS₃ : PreservesLocs (StaticStrLoc st₂) st₂.heap st₃.heap :=
                            hpFrame₃.mono fun l hss => hstat₂F l hss
                          have hpSS₆ : PreservesLocs (StaticStrLoc st₄) st₄.heap st₆.heap :=
                            hp₆.mono fun l hss => StaticStrLoc_lt_size hst₄ hss
                          have hpSS₇ : PreservesLocs (StaticStrLoc st₆) st₆.heap st₇.heap :=
                            hp₇.mono fun l hss => StaticStrLoc_lt_size hst₆ hss
                          have hssf13 : StaticStrFresh st_call st₃ :=
                            StaticStrFresh.trans (hstOpenSz ▸ hsz₂) hpSS₃ hssf₂ hssf₃
                          have hssf14 : StaticStrFresh st_call st₄ :=
                            StaticStrFresh.trans (by omega) hpSS₄ hssf13 hssf₄
                          have hssf16 : StaticStrFresh st_call st₆ :=
                            StaticStrFresh.trans (by omega) hpSS₆ hssf14 hssf₆
                          have hssfAll : StaticStrFresh st_call st₇ :=
                            StaticStrFresh.trans (by omega) hpSS₇ hssf16 hssf₇
                          have hopenAll : DeepOpenUnder st₇.heap st₇.regions
                              (applyResultRegs st_call res c_app fRegs aRegs) rv₂ := by
                            have h1 : applyResultRegs st₆ res c_app fRegs aRegs =
                                applyResultRegs st_call res c_app fRegs aRegs := by
                              unfold applyResultRegs; rw [hrg₆, hrg₅]
                            rwa [h1] at hopen₇
                          -- Reachability bound (both general line 742 and unique+borrowed/erased line 754!)
                          have hReachCore : ∀ l, Reach st₇.heap rv₂ l →
                              st_call.heap.objs.size ≤ l ∨ Reach st_call.heap f_call l ∨
                              (¬ (res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased)) ∧
                                Reach st_call.heap a l) ∨
                              StaticStrLoc st_call l ∨ NumLoc st₇.heap l := by
                            intro l hrl7
                            by_cases hge : st_call.heap.objs.size ≤ l
                            · exact Or.inl hge
                            · by_cases hrfL : Reach st_call.heap f_call l
                              · exact Or.inr (Or.inl hrfL)
                              · by_cases hss0 : StaticStrLoc st_call l
                                · exact Or.inr (Or.inr (Or.inr (Or.inl hss0)))
                                · by_cases hnum7 : NumLoc st₇.heap l
                                  · exact Or.inr (Or.inr (Or.inr (Or.inr hnum7)))
                                  · by_cases hnotU : ¬ (res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased)) ∧ Reach st_call.heap a l
                                    · exact Or.inr (Or.inr (Or.inl hnotU))
                                    · exfalso
                                      have hlt0 : l < st_call.heap.objs.size := Nat.lt_of_not_le hge
                                      have hForbL : l < st_call.heap.objs.size ∧ ¬ Reach st_call.heap f_call l ∧
                                          ¬ StaticStrLoc st_call l ∧
                                          (res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased) ∨ ¬ Reach st_call.heap a l) := by
                                        refine ⟨hlt0, hrfL, hss0, ?_⟩
                                        by_cases hu : res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased)
                                        · exact Or.inl hu
                                        · right; intro hra; exact hnotU ⟨hu, hra⟩
                                      have hrl6 : Reach st₆.heap rv₁ l := (hreach₇ l hrl7).resolve_left (by omega)
                                      have hrl5 : Reach st₅.heap rv_r l := (hreach₆ l hrl6).resolve_left (by omega)
                                      have hrl3 : Reach st₃.heap rv_b l := (hreach₄ l hrl5).resolve_left (by omega)
                                      have hnotNum3 : ¬ NumLoc st₃.heap l := fun ⟨o3, n3, ho3, hc3⟩ => by
                                        by_cases hrcV : rc = .val
                                        · have hnum4 : NumLoc st₄.heap l := by
                                            have hvdR := hretU.2.2.2.2.2.2.2.1
                                            have hooR : r_body.onceOnly = false := hretU.2.2.2.2.2.2.2.2.2.1
                                            have hnotOnceR := hretU.2.2.2.2.2.2.2.2.2.2.1
                                            have hvAct := hvR₃.2.2.2.2 ⟨hvdR, fun his => absurd his hnotOnceR⟩
                                            have hinfo := hretU.2.2.2.2.2.2.2.2.2.2.2.1 hrcV
                                            have hretS := ret_spec (P := P) (fuel := nf) (s := s_c) (cur := st_call.regions.headD 0)
                                              (r := res) (c := rc) (v := rv_b) hst₃.1 hvAct.1.1 hvAct.1.2.1
                                              (fun hu => by
                                                by_cases hrv : r_body.cls = .val
                                                · exact (hvAct.2.2.2.2.2.2.2 ⟨hrv, (hinfo.2.2 hu).1, hooR, hnotOnceR,
                                                    fun d hd => ⟨(hinfo.2.2 hu).2 d hd, fun hnkD => hNoKill_ret d hnkD (by
                                                      have h2 := hretU.2.2.2.2.2.2.2.2.2.2.2.2 d (hvR₃.2.1 d hd)
                                                      simp only [hrcV, hu, hd, and_self, ↓reduceIte] at h2; exact h2)⟩⟩).1
                                                · exact (hvAct.2.2.2.1 hnotOnceR hrv).ownTreeFull.1)
                                              (fun hnb x hx hm => by
                                                simp only [List.mem_singleton] at hm; subst x
                                                have hnoS := hinfo.1 hnb
                                                have hmem := hvAct.2.1 rv_b (HeldBy.refl _ _) s_c hx hsIn₃
                                                obtain ⟨rg, hrg, hscRg⟩ := Interp.mem_regsOf.mp hmem
                                                have hne : rg ≠ s_a := fun hEq => hnoS (show s_a ∈ r_body.regs from hEq ▸ hrg)
                                                exact False.elim (hregU_body.2 rg (hvR₃.1 rg hrg) hne hscRg))
                                              (fun hu => by
                                                have hdou := hvAct.2.1
                                                rw [hinfo.2.1 hu, Interp.regsOf_nil] at hdou
                                                exact hdou rv_b (HeldBy.refl _ _))
                                            rcases hretS with hS | hO | ⟨rv0, st0, hrun0, _, _, _, _, _, _, _, _, hpres0, _⟩
                                            · rw [hrunR] at hS; cases hS
                                            · rw [hrunR] at hO; cases hO
                                            · rw [hrunR] at hrun0; cases hrun0
                                              exact ⟨o3, n3, (hpres0 l ⟨(Array.getElem?_eq_some_iff.mp ho3).1,
                                                fun _ hor => OwnReach_not_numLoc hor ⟨o3, n3, ho3, hc3⟩⟩).trans ho3, hc3⟩
                                          obtain ⟨o4, n4, ho4, hc4⟩ := hnum4
                                          have ho6 : st₆.heap.objs[l]? = some o4 := (hp₆ l (Array.getElem?_eq_some_iff.mp ho4).1).trans ho4
                                          have ho7 : st₇.heap.objs[l]? = some o4 := (hp₇ l (Array.getElem?_eq_some_iff.mp ho6).1).trans ho6
                                          exact hnum7 ⟨o4, n4, ho7, hc4⟩
                                        · obtain ⟨o5, n5, ho5, hc5⟩ := (hnvNe₄ hrcV).reach_numLoc hrl5
                                          have ho6 : st₆.heap.objs[l]? = some o5 := (hp₆ l (Array.getElem?_eq_some_iff.mp ho5).1).trans ho5
                                          have ho7 : st₇.heap.objs[l]? = some o5 := (hp₇ l (Array.getElem?_eq_some_iff.mp ho6).1).trans ho6
                                          exact hnum7 ⟨o5, n5, ho7, hc5⟩
                                      have hnotSS3 : ¬ StaticStrLoc st₃ l := fun hss3 => by
                                        rcases hssf₃ l hss3 with hge2 | hss2 | hnum3
                                        · exact Nat.not_lt_of_ge hge2 (Nat.lt_of_lt_of_le hlt0 hsz₂)
                                        · exact hss0 (StaticStrLoc_of_preserves_outside hstat₂ hstr₂ hpSS₂ l hss2)
                                        · exact hnotNum3 hnum3
                                      have hvdR := hretU.2.2.2.2.2.2.2.1
                                      have hnotOnceR := hretU.2.2.2.2.2.2.2.2.2.2.1
                                      have hregsBad : ∀ rg ∈ r_body.regs, ¬ (if res = .unique ∧ c_app = .val ∧ (p.mode.isBorrowed = true ∨ p.mode = .erased) then (· = s_a) else fun _ => False) rg := by
                                        intro rg hrg
                                        split
                                        · rename_i hcond
                                          by_cases hrcV : rc = .val
                                          · have hrgNil := (hretU.2.2.2.2.2.2.2.2.2.2.2.1 hrcV).2.1 hcond.1
                                            rw [hrgNil] at hrg; cases hrg
                                          · exfalso
                                            have hnv4 := hnvNe₄ hrcV
                                            have hnum5 : NumLoc st₅.heap l := hnv4.reach_numLoc hrl5
                                            obtain ⟨o5, n5, ho5, hc5⟩ := hnum5
                                            have ho6 : st₆.heap.objs[l]? = some o5 := (hp₆ l (Array.getElem?_eq_some_iff.mp ho5).1).trans ho5
                                            have ho7 : st₇.heap.objs[l]? = some o5 := (hp₇ l (Array.getElem?_eq_some_iff.mp ho6).1).trans ho6
                                            exact hnum7 ⟨o5, n5, ho7, hc5⟩
                                        · exact id
                                      exact hnrfR₃ ⟨hvdR, fun his => absurd his hnotOnceR⟩ hregsBad (fun _ _ h => h)
                                        l hrl3 hnotSS3 hnotNum3 hForbL
                          refine ⟨by omega, hst₇, hszAll, hcapAll, hrgAll, hnrAll, hstatAll, hstrAll,
                            hpFrameAll, honceAll, hssfAll, hbv₇, hcls₇, hopenAll, hcf₇, ?_, ?_, ?_⟩
                          · intro l hrl7
                            rcases hReachCore l hrl7 with h1 | h2 | ⟨_, h3⟩ | h4 | h5
                            · exact Or.inl h1
                            · exact Or.inr (Or.inl h2)
                            · exact Or.inr (Or.inr (Or.inl h3))
                            · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
                            · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
                          · refine ⟨fun _ => ⟨hno₇ rfl, hfun₇⟩,
                              fun _ => ⟨fun _ => False, fun _ h => False.elim h, FunOkAt_upgrade_onceOnly hfun₇⟩⟩
                          · rintro ⟨hu, hcv⟩
                            subst hcv
                            obtain ⟨rfl, rfl⟩ := hcval₇ rfl
                            obtain ⟨rfl, rfl⟩ := hcval₆ rfl
                            refine ⟨?_, ?_, fun hru hbe l hrl5 => ?_⟩
                            · by_cases hrcV : rc = .val
                              · exact (huniq₄ ⟨hu, hrcV⟩).1
                              · exact (hnvNe₄ hrcV).ownTreeFull.1
                            · intro l hor5
                              by_cases hrcV : rc = .val
                              · exact (huniq₄ ⟨hu, hrcV⟩).2 l hor5
                              · exact False.elim ((hnvNe₄ hrcV).ownTreeFull.2 l hor5)
                            · rcases hReachCore l hrl5 with h1 | h2 | ⟨hno, _⟩ | h4 | h5
                              · exact Or.inl h1
                              · exact Or.inr (Or.inl h2)
                              · exact absurd ⟨hru, rfl, hbe⟩ hno
                              · exact Or.inr (Or.inr (Or.inl h4))
                              · exact Or.inr (Or.inr (Or.inr h5))
        -- Package `TermPost` for `ATerm.lam`
        have hVSim' := hVSimFn hFunClo
        rw [hIendEq] at hsim' hVSim' hdou'
        rw [← hσEnd] at hsim' hVSim' henvNRF' hDisj' hNrf'
        exact ⟨cloFoot, by omega, hst', by omega, hcap', hr', hnr' ▸ Nat.le_refl _,
          hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
          hpresF', hpresEnv', hpresNum', honce', hssf',
          hsim', henvTaint.step hr' (hnr' ▸ Nat.le_refl _), henvNRF',
          hVSim', hDisj', hNrf',
          (fun _ hne => absurd rfl hne),
          (fun _ => ⟨fun c hc => hbv'.2.2.2 rv (HeldBy.refl _ _) c hc, hdou' rv (HeldBy.refl _ _)⟩),
          Or.inl ⟨hbv', hcf'⟩, SrcOk_none rfl⟩

theorem Runs_bindInner_deps_mem {m : BinderMode} {d : Cls} {x bv : AVal} {s : Nat} {w : String}
    {σ σ' : AState} (hok : AStateOk σ) (h : Runs (bindInner m d x s w) σ bv σ') :
    ∀ dep ∈ bv.deps, dep ∈ x.deps := by
  cases m <;> (
    have hbv := (Runs_bindInner hok h).2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [hbv]; cases (d == .leaf) <;> simp)

theorem Runs_bindInner_regs_of_mem {m : BinderMode} {d : Cls} {x bv : AVal} {s : Nat} {w : String}
    {σ σ' : AState} (hok : AStateOk σ) (h : Runs (bindInner m d x s w) σ bv σ')
    (hmNe : m ≠ .erased) (hmu : m ≠ .unique) (hd : d ≠ .leaf) :
    ∀ rg ∈ x.regs, rg ∈ bv.regs := by
  have hdF : (d == .leaf) = false := Cls_beq_false_of_ne hd
  cases m <;> first
    | exact absurd rfl hmNe
    | exact absurd rfl hmu
    | (have hbv := (Runs_bindInner hok h).2.2.2.2.2.2.2.2.2.2.2.2.2
       intro rg hrg; rw [hbv]; simp only [hdF, Bool.false_eq_true, ↓reduceIte]; simp [mem_natUnion, hrg])

theorem Runs_bindInner_regs_of_borrowed {m : BinderMode} {d : Cls} {x bv : AVal} {s : Nat} {w : String}
    {σ σ' : AState} (hok : AStateOk σ) (h : Runs (bindInner m d x s w) σ bv σ')
    (hbor : m.isBorrowed = true) (hd : d ≠ .leaf) :
    s ∈ bv.regs := by
  have hdF : (d == .leaf) = false := Cls_beq_false_of_ne hd
  cases m <;> first
    | (simp [BinderMode.isBorrowed] at hbor; done)
    | (have hbv := (Runs_bindInner hok h).2.2.2.2.2.2.2.2.2.2.2.2.2
       rw [hbv]; simp only [hdF, Bool.false_eq_true, ↓reduceIte]; simp [mem_natUnion])

theorem Runs_bindInner_cls {m : BinderMode} {d : Cls} {x bv : AVal} {s : Nat} {w : String}
    {σ σ' : AState} (hok : AStateOk σ) (h : Runs (bindInner m d x s w) σ bv σ')
    (hmNe : m ≠ .erased) :
    bv.cls = d := by
  cases m <;> first
    | exact absurd rfl hmNe
    | (have hbv := (Runs_bindInner hok h).2.2.2.2.2.2.2.2.2.2.2.2.2
       rw [hbv]; cases (d == .leaf) <;> rfl)

theorem Runs_bindInner_deps_uniq {m : BinderMode} {d : Cls} {x bv : AVal} {s : Nat} {w : String}
    {σ σ' : AState} (hok : AStateOk σ) (h : Runs (bindInner m d x s w) σ bv σ')
    (hu : m.isUnique = true) :
    bv.deps = [] := by
  cases m <;> first
    | (simp [BinderMode.isUnique] at hu; done)
    | (have hbv := (Runs_bindInner hok h).2.2.2.2.2.2.2.2.2.2.2.2.2
       rw [hbv]; cases (d == .leaf) <;> rfl)

theorem Runs_bindInner_nonUniq {m : BinderMode} {d : Cls} {x bv : AVal} {s : Nat} {w : String}
    {σ σ' : AState} (hok : AStateOk σ) (h : Runs (bindInner m d x s w) σ bv σ')
    (hmNe : m ≠ .erased) (hnu : m.isUnique = false) :
    bv.own = x.own ∧ bv.deps = x.deps ∧ bv.onceOnly = x.onceOnly := by
  cases m <;> first
    | exact absurd rfl hmNe
    | (simp [BinderMode.isUnique] at hnu; done)
    | (have hbv := (Runs_bindInner hok h).2.2.2.2.2.2.2.2.2.2.2.2.2
       rw [hbv]; cases (d == .leaf) <;> exact ⟨rfl, rfl, rfl⟩)

/-- Soundness for `ATerm.letVal` (`evalS` on `v`, `openRegion`, `bindInner_bridge`, `evalS` on `b`,
`confinedTo = false` via `EnvTaintOk`/taint postcondition, and `closeRegion`). -/
theorem evalS_letVal_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {m : LetMode} {d : Cls} {v b : Term}
    {σ σ₁ σ₂ σ₃ σ₄ : AState} {x bv r : AVal}
    (hneEr : m ≠ .value .erased)
    (hvD : ATerm P aenv v σ x σ₁)
    (hvIH : ATermProp P ext B aenv v σ x σ₁)
    (hbind : Runs (bindInner m.binderMode d x σ₁.openReg.1 "a let") σ₁.openReg.2 bv σ₂)
    (hbD : ATerm P ({ id := σ₂.st.size, mode := m.binderMode, val := bv } :: aenv)
      b (σ₂.pushBnd bv (m.binderMode.usage == .once)).2 r σ₃)
    (hbIH : ATermProp P ext B ({ id := σ₂.st.size, mode := m.binderMode, val := bv } :: aenv)
      b (σ₂.pushBnd bv (m.binderMode.usage == .once)).2 r σ₃)
    (hvalR : Runs (valid r "a let's value") σ₃ () σ₄)
    (hnotIn : ¬ (σ₁.openReg.1 ∈ r.regs)) :
    ATermProp P ext B aenv (.letE m d v b) σ r (σ₄.closeReg σ₁.openReg.1) := by
  classical
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  cases hlc with
  | letE hlcV hlcB =>
  cases hcfd with
  | letE hcfdV hcfdB =>
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hok := hsim.2.1
      obtain ⟨hok₁, hle₁, hreg₁⟩ := ATerm_state_le hok hvD
      let s_a := σ₁.openReg.1
      let σ_open := σ₁.openReg.2
      have hokOpen : AStateOk σ_open := (AStateOk.openReg hok₁).1
      have hleOpen : AStateLe σ₁ σ_open := AStateLe_openReg σ₁
      obtain ⟨hok₂, hle₂, hszSt₂, hσonce₂, hszSp₂, hσreg₂, hσnr₂, hnotOnce₂, hvdX₂, huniq₂, hunsp₂, hspUpd₂, hstUpd₂, hbvEq₂⟩ :=
        Runs_bindInner hokOpen hbind
      change σ₂.st.size = σ₁.st.size at hszSt₂
      change σ₂.once = σ₁.once at hσonce₂
      change σ₂.regions = s_a :: σ₁.regions at hσreg₂
      let ab : ABnd := { id := σ₂.st.size, mode := m.binderMode, val := bv }
      let σ_push := (σ₂.pushBnd bv (m.binderMode.usage == .once)).2
      have hokPush : AStateOk σ_push := (hok₂.pushBnd bv _).1
      have hlePush : AStateLe σ₂ σ_push := (hok₂.pushBnd bv _).2
      obtain ⟨hok₃, hle₃, hreg₃⟩ := ATerm_state_le hokPush hbD
      obtain ⟨hvdR₃, hσ₄Eq⟩ := Runs_valid hvalR
      subst σ₄
      have hleClose : AStateLe σ₃ (σ₃.closeReg s_a) := AStateLe_closeReg s_a σ₃
      have hle₁₃ : AStateLe σ₁ σ₃ := hleOpen.trans (hle₂.trans (hlePush.trans hle₃))
      have hnk₃ : NoKillOk NoKill σ₃ := NoKillOk_of_AStateLe hleClose hnkEnd
      have hnsp₃ : NoSpendOk NoSpend σ₃ := NoSpendOk_of_AStateLe hleClose hnspEnd
      let BadDep₁ : Nat → Prop := fun dep => dep < σ₁.st.size ∧ BadDep dep
      let BadDepP : Nat → Prop := fun dep => dep < σ_push.st.size ∧ BadDep dep
      have hBadDep₃ : ∀ dep, BadDep dep → σ₃.st[dep]? = some .live := fun dep hbd => hBadDepEnd dep hbd
      have hBadDepP : ∀ dep, BadDepP dep → σ₃.st[dep]? = some .live := fun dep hbd => hBadDep₃ dep hbd.2
      have hBadDep₂ : ∀ dep, BadDep₁ dep → σ₂.st[dep]? = some .live :=
        BadDepLive_of_AStateLe (hlePush.trans hle₃) (fun dep hbd => hBadDep₃ dep hbd.2) (fun dep hbd => hszSt₂ ▸ hbd.1)
      have hBadDep₁ : ∀ dep, BadDep₁ dep → σ₁.st[dep]? = some .live :=
        BadDepLive_of_AStateLe hle₁₃ (fun dep hbd => hBadDep₃ dep hbd.2) (fun dep hbd => hbd.1)
      have hnk₂ : NoKillOk NoKill σ₂ := NoKillOk_of_AStateLe (hlePush.trans hle₃) hnk₃
      have hnsp₂ : NoSpendOk NoSpend σ₂ := NoSpendOk_of_AStateLe (hlePush.trans hle₃) hnsp₃
      have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₁₃ hnk₃
      have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₁₃ hnsp₃
      have hstep : (evalS P ext (n + 1) env (.letE m d v b)).run (st, b0 + 1) =
          (do
            let x ← evalS P ext n env v
            let (s, _) ← liftM openRegion
            let bnd ← liftM (bindAt P n s m.binderMode d x)
            let r ← evalS P ext n (bnd :: env) b
            if confinedTo s r then liftM (violate .borrowEscape)
            liftM (closeRegion s)
            pure r).run (st, b0) := by
        conv => lhs; unfold evalS
        rw [MS_bind_run, MS_spend_succ]; dsimp only
        cases m with
        | value bm =>
          cases bm with
          | erased => exact absurd rfl hneEr
          | _ => rfl
        | borrow => rfl
      unfold TermPost; rw [hstep, MS_bind_run]
      have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (by omega) (AStateLe.refl _) hok hsim.2.2.1 (RegsFuture.refl _)
          (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
          (PreservesActiveEnv.refl _ _ _ _ _) hsim
      have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := by
        intro i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps
        have hvI := ((hsimB.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
        exact henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
          (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
      obtain ⟨hnoVV, hokV⟩ := hvIH hlcV hcfdV (B₀ := b0) (fuel := n) (by omega)
        (fun z hz => hfv z (.letV hz)) (StOk_mono (by omega) hst) hsimB hstat hFlt
        hnk₁ hnsp₁ hIZero hHeadReg henvTaint henvNRF_bd₁ hForbidLt hBadDep₁
      cases hevV : (evalS P ext n env v).run (st, b0) with
      | error e =>
        refine ⟨fun k hk => by cases hk; exact hnoVV k hevV, fun _ _ _ h => by cases h⟩
      | ok pv =>
        rcases pv with ⟨xv, ⟨st₁, B₁⟩⟩; dsimp only
        obtain ⟨xFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
          hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
          hvX₁, hdisjX₁, hnrfX₁, hnvX₁, htaintX₁, _, _⟩ := hokV xv st₁ B₁ hevV
        let s_c := st₁.nextRegion
        let st_open : St := { st₁ with nextRegion := s_c + 1, regions := s_c :: st₁.regions }
        have hopenRun : openRegion.run st₁ = .ok ((s_c, st₁.regions.headD 0), st_open) := rfl
        rw [MS_bind_run, MS_liftM_run, hopenRun]; dsimp only
        let I_open : Interp := I.extend s_a s_c
        let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
        have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
        have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
          h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
        have hIopenLt : ∀ rg, rg < s_a → I_open.reg rg = I.reg rg := fun rg hlt => by
          simp [I_open, Interp.extend, Nat.ne_of_lt hlt]
        have hIopenSa : I_open.reg s_a = [s_c] := by simp [I_open, Interp.extend]
        have hIopenZero : ∀ rg, σ_open.nextRegion ≤ rg → I_open.reg rg = [] := fun rg hge => by
          have hne : rg ≠ s_a := by simp only [σ_open, s_a, AState.openReg] at hge ⊢; omega
          have hge0 : σ.nextRegion ≤ rg := by
            have := hle₁.2.1; simp only [σ_open, AState.openReg] at hge ⊢; omega
          simp [I_open, Interp.extend, hne, hIZero rg hge0]
        have hstOpen : StOk P ext B₁ st_open := StOk_openRegion hst₁
        have hrfOpen : RegsFuture st₁ st_open := RegsFuture.openRegion st₁
        have hIokOpen : InterpOk σ_open st_open I_open :=
          (InterpOk.openRegion hsim₁.2.2.1).1
        have hIokOpen1 : InterpOk σ₁ st₁ I_open :=
          ⟨fun rg hlt c hc => by rw [hIopenLt rg hlt] at hc; exact hsim₁.2.2.1.1 rg hlt c hc,
           fun c hc => by
             have hhdLt : σ₁.regions.headD 1 < s_a := by
               cases hrg : σ₁.regions with
               | nil => simp only [List.headD]; have := hok₁.2.2.1; change 1 < σ₁.nextRegion; omega
               | cons hd tl =>
                 simp only [List.headD]
                 exact (hok₁.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2
             rw [hIopenLt _ hhdLt]; exact hsim₁.2.2.1.2 c hc⟩
        have hsimOpen : Sim P ext B₁ st_open Frame₁ NoKill NoSpend Scope env aenv σ_open I_open envFoot :=
          Sim_step (Nat.le_refl B₁) hleOpen hokOpen hIokOpen hrfOpen
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _)
            (Sim_interp_congr hIokOpen1 (fun rg hlt => (hIopenLt rg hlt).symm) (Sim_add_staticStr hsim₁))
        have hvXOpen : VSim P ext B₁ st_open Frame₁ NoKill NoSpend σ_open I_open xFoot x xv :=
          VSim_step (Nat.le_refl B₁) hok₁ hleOpen hrfOpen (PreservesOnceShell.refl _) (StaticStrFresh.refl _)
            (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _)
            (VSim_interp_congr (fun rg hrg => (hIopenLt rg (hvX₁.1 rg hrg)).symm) (VSim_add_staticStr hvX₁))
        have henvNRFOpen : EnvNoReachForbid st_open Scope env aenv σ_open Forbid BadReg BadDep₁ :=
          EnvNoReachForbid_step hok₁ hleOpen (Sim_deps_lt hsim₁) hsim₁.2.2.2.1
            (ArrayExtends.refl _) (ArrayExtends.refl _) (PreservesLocs.refl _ _)
            (PreservesActiveEnv.refl _ _ _ _ _) henvNRF₁
        have henvTaintOpen : EnvTaintOk Scope env aenv st_open I_open :=
          henvTaint₁.openRegion (fun i ab0 hsc0 hab0 hne0 r hr =>
            let hiE : i < env.length := by rw [hsim₁.1]; exact (List.getElem?_eq_some_iff.mp hab0).1
            ((hsim₁.2.2.2.2.2.1 i env[i] ab0 hsc0 (List.getElem?_eq_getElem hiE) hab0).2 hne0).2.1 r hr)
        have hForbLt₁ : ∀ l, Forbid l → l < st_open.heap.objs.size := fun l hF =>
          Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
        rcases bindInner_bridge (fuel := n) (s_a := s_a) (s_c := s_c)
            hstOpen (by simp [s_a, σ_open, AState.openReg]) (Nat.lt_succ_self s_c)
            (by rw [hIopenSa]; exact List.mem_cons_self) hFlt₁ hForbLt₁ hnk₂ hnsp₂ hBadDep₂
            hsimOpen henvNRFOpen hvXOpen hdisjX₁ hnrfX₁ hbind with hStB | hOOFB |
          ⟨bnd, st₂, bFoot, hrunBind, hmodeB, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
           hpFrame₂, hpSS₂, honce₂, hssf₂, hst₂, hsimP0, henvNRFP0⟩
        · rw [MS_bind_run, MS_liftM_run, hStB]
          exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [MS_bind_run, MS_liftM_run, hOOFB]
          exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [MS_bind_run, MS_liftM_run, hrunBind]; dsimp only
          -- Extract `PreservesLocs` outside unique `xv` and taint bounds from `bindAt_spec`
          have hbindSpecOut :
              PreservesLocs (fun l => l < st₁.heap.objs.size ∧ (m.binderMode.isUnique = true → ¬ OwnReach P st₁.heap xv l))
                st₁.heap st₂.heap ∧
              (∀ c ∈ bnd.val.taint, c ∈ xv.taint ∨ (m.binderMode.isBorrowed = true ∧ c = s_c)) ∧
              (d = .leaf → bnd.val.taint = []) := by
            by_cases hmEr : m.binderMode = .erased
            · have hEq : (bindAt P n s_c .erased d xv).run st_open = .ok (⟨.imm .irr, .erased⟩, st_open) := by
                unfold bindAt; rfl
              rw [hmEr] at hrunBind; rw [hEq] at hrunBind; cases hrunBind
              exact ⟨PreservesLocs.refl _ _, (fun _ h => by cases h), fun _ => rfl⟩
            · have hvdX : ValidDeps σ_open x.deps := hvdX₂ hmEr
              have hactX : ActiveVal σ_open x := by
                refine ⟨hvdX, fun his => ?_⟩
                by_cases ho : m.binderMode.usage = .once
                · exact hunsp₂ ho
                · exact absurd his (hnotOnce₂ ho)
              have hvActX := hvXOpen.2.2.2.2 hactX
              rcases bindAt_spec (P := P) (fuel := n) (s := s_c) (m := m.binderMode) (c := d) (v := xv)
                  hstOpen.1 (fun _ => hvActX.1.1) (fun _ => hvActX.1.2.1)
                  (fun hu => by
                    have hneO : m.binderMode.usage ≠ .once := by
                      cases hm' : m.binderMode <;> rw [hm'] at hu <;> simp [BinderMode.isUnique, BinderMode.usage] at hu ⊢
                    have hnoX : ¬ IsOnceSrc σ_open x := hnotOnce₂ hneO
                    by_cases hcv : x.cls = .val
                    · have huO := huniq₂ hu
                      have huI := huO.2 hcv
                      have htrX : Transferable σ_open NoKill x :=
                        ⟨hcv, huI.1, huO.1, hnoX, fun dep hdep => ⟨huI.2.1 dep hdep, fun hnkD => hnk₂ dep hnkD (by
                          have h1 := hstUpd₂ dep (hvXOpen.2.1 dep hdep)
                          simp only [hu, hcv, hdep, and_self, ↓reduceIte] at h1; exact h1)⟩⟩
                      exact (hvActX.2.2.2.2.2.2.2 htrX).1
                    · exact (hvActX.2.2.2.1 hnoX hcv).ownTreeFull.1)
                  (fun hu hnb => by
                    have hneO : m.binderMode.usage ≠ .once := by
                      cases hm' : m.binderMode <;> rw [hm'] at hu <;> simp [BinderMode.isUnique, BinderMode.usage] at hu ⊢
                    have hnoX : ¬ IsOnceSrc σ_open x := hnotOnce₂ hneO
                    by_cases hcv : x.cls = .val
                    · have hrgNil := ((huniq₂ hu).2 hcv).2.2 hnb
                      have hdou := hvActX.2.1
                      rw [hrgNil, Interp.regsOf_nil] at hdou
                      exact hdou xv (HeldBy.refl _ _)
                    · exact (hvActX.2.2.2.1 hnoX hcv).deepOpenUnder_nil xv (HeldBy.refl _ _)) with
                hS | hO | ⟨_, _, hrun0, _, _, _, _, _, _, _, _, _, hpres0, _, _, _, _, _, _, hbt0, hbl0, _⟩
              · rw [hrunBind] at hS; cases hS
              · rw [hrunBind] at hO; cases hO
              · rw [hrunBind] at hrun0; cases hrun0
                exact ⟨hpres0, hbt0, hbl0⟩
          have hpresBindOut := hbindSpecOut.1
          have hpresNum₂ : ∀ (l : Nat) (o : Obj) (n : Nat),
              st₁.heap.objs[l]? = some o → o.cell = .num n → st₂.heap.objs[l]? = some o := fun l o n ho hc =>
            (hpresBindOut l ⟨(Array.getElem?_eq_some_iff.mp ho).1,
              fun _ hor => OwnReach_not_numLoc hor ⟨o, n, ho, hc⟩⟩).trans ho
          have hpresEnv₂ : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap := by
            intro k bk abk hsc hbk habk hne ha₂
            have hvK := ((hsim₁.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
            have ha₁ := ActiveVal.of_AStateLe hok₁ (hleOpen.trans hle₂) hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha₂
            refine hpresBindOut.mono fun l hrK => ⟨(hvK.2.2.2.2 ha₁).1.1.reach_lt_size hrK, fun hu hor => ?_⟩
            have hmNe : m.binderMode ≠ .erased := by
              cases hm' : m.binderMode <;> rw [hm'] at hu <;> simp [BinderMode.isUnique] at hu ⊢
            have hvdX : ValidDeps σ_open x.deps := hvdX₂ hmNe
            have hneO : m.binderMode.usage ≠ .once := by
              cases hm' : m.binderMode <;> rw [hm'] at hu <;> simp [BinderMode.isUnique, BinderMode.usage] at hu ⊢
            have hnotOS : ¬ IsOnceSrc σ_open x := hnotOnce₂ hneO
            by_cases hcv : x.cls = .val
            · have huO := huniq₂ hu
              have huI := huO.2 hcv
              have htrX : Transferable σ₁ NoKill x :=
                ⟨hcv, huI.1, huO.1, hnotOS, fun dep hdep => ⟨huI.2.1 dep hdep, fun hnkD => hnk₂ dep hnkD (by
                  have h1 := hstUpd₂ dep (hvX₁.2.1 dep hdep)
                  simp only [hu, hcv, hdep, and_self, ↓reduceIte] at h1; exact h1)⟩⟩
              have hdd : ∀ dep ∈ x.deps, dep ∉ (effVal abk).deps := fun dep hdep hdk => by
                have h1 := hstUpd₂ dep (hvX₁.2.1 dep hdep)
                simp only [hu, hcv, hdep, and_self, ↓reduceIte] at h1
                exact (ha₂.1 dep hdk).2 h1
              exact (hdisjX₁ k bk abk hsc hbk habk hne).1 ⟨hvdX, fun his => absurd his hnotOS⟩ htrX ha₁ hdd l hor hrK
            · exact ((hvX₁.2.2.2.2 ⟨hvdX, fun his => absurd his hnotOS⟩).2.2.2.1 hnotOS hcv).ownTreeFull.2 l hor
          have hsimP : Sim P ext B₁ st₂ Frame₁ NoKill NoSpend (shiftScope Scope) (bnd :: env) (ab :: aenv) σ_push I_open
              (fun i => match i with | 0 => bFoot | k + 1 => envFoot k) :=
            Sim_congr_scope_foot (fun i => by cases i <;> exact Iff.rfl)
              (fun i _ => by cases i <;> exact Iff.rfl) hsimP0
          have henvNRFP : EnvNoReachForbid st₂ (shiftScope Scope) (bnd :: env) (ab :: aenv) σ_push Forbid BadReg BadDepP := by
            intro i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps
            have hvP := ((hsimP.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
            exact henvNRFP0 i b' ab' (by cases i <;> exact hsc') hbi' habi' hne' ha' hregs
              (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvP.2.1 dep hdep) (Nat.le_refl _), hbd.2⟩)
          have henvTaintP : EnvTaintOk (shiftScope Scope) (bnd :: env) (ab :: aenv) st₂ I_open := by
            have ht₂ := henvTaintOpen.step hrg₂ (hnr₂ ▸ Nat.le_refl _)
            intro i b' ab' hsc' hbi' habi' hne'
            cases i with
            | succ k => exact ht₂ k b' ab' hsc' hbi' habi' hne'
            | zero =>
              simp at hbi' habi'; subst hbi' habi'
              have hmNe : m.binderMode ≠ .erased := hne'
              have hvdX : ValidDeps σ₁ x.deps := hvdX₂ hmNe
              obtain ⟨hxtLt, hxtOpen⟩ := htaintX₁ hvdX
              have hIopenX : I_open.regsOf x.regs = I.regsOf x.regs :=
                Interp.regsOf_congr fun rg hrg => hIopenLt rg (hvX₁.1 rg hrg)
              refine ⟨fun c hc => ?_, fun c hc hopen => ?_⟩
              · rcases hbindSpecOut.2.1 c hc with hcx | ⟨_, rfl⟩
                · rw [hnr₂]; exact Nat.lt_succ_of_lt (hxtLt c hcx)
                · rw [hnr₂]; exact Nat.lt_succ_self s_c
              · by_cases hdLeaf : d = .leaf
                · rw [hbindSpecOut.2.2 hdLeaf] at hc; cases hc
                · rcases hbindSpecOut.2.1 c hc with hcx | ⟨hbor, rfl⟩
                  · have hcLt : c < s_c := hxtLt c hcx
                    have hcIn1 : c ∈ st₁.regions := by
                      rw [hrg₂] at hopen
                      rcases List.mem_cons.mp hopen with rfl | hm'
                      · exact absurd hcLt (Nat.lt_irrefl _)
                      · exact hm'
                    have hcInIx : c ∈ I_open.regsOf x.regs := by rw [hIopenX]; exact hxtOpen c hcx hcIn1
                    obtain ⟨rg, hrgX, hcRg⟩ := Interp.mem_regsOf.mp hcInIx
                    refine Interp.mem_regsOf.mpr ⟨rg, ?_, hcRg⟩
                    by_cases hmu : m.binderMode = .unique
                    · exfalso
                      by_cases hcv : x.cls = .val
                      · have hrgNil := ((huniq₂ (by rw [hmu]; rfl)).2 hcv).2.2 (by rw [hmu]; rfl)
                        rw [hrgNil] at hrgX; cases hrgX
                      · have hnv := (hnvX₁ hvdX hcv).2
                        rw [hnv.taint_nil] at hcx; cases hcx
                    · exact Runs_bindInner_regs_of_mem hokOpen hbind hmNe hmu hdLeaf rg hrgX
                  · refine Interp.mem_regsOf.mpr ⟨s_a, ?_, by rw [hIopenSa]; exact List.mem_cons_self⟩
                    change s_a ∈ bv.regs
                    exact Runs_bindInner_regs_of_borrowed hokOpen hbind hbor hdLeaf
          have hstat₂F : ∀ l, StaticStrLoc st₂ l → Frame₁ l := fun l hss =>
            Or.inr (StaticStrLoc_of_preserves_outside hstat₂ hstr₂ hpSS₂ l hss)
          have hFlt₂ : ∀ l, Frame₁ l → l < st₂.heap.objs.size := fun l hF =>
            Nat.lt_of_lt_of_le (hFlt₁ l hF) hsz₂
          have hForbLt₂ : ∀ l, Forbid l → l < st₂.heap.objs.size := fun l hF =>
            Nat.lt_of_lt_of_le (hForbLt₁ l hF) hsz₂
          have hIZeroP : ∀ rg, σ_push.nextRegion ≤ rg → I_open.reg rg = [] := fun rg hge =>
            hIopenZero rg (by simpa [σ_push, AState.pushBnd, hσnr₂] using hge)
          have hHeadRegP : st₂.regions.headD 0 = 0 ∨ st₂.regions.headD 0 ∈ I_open.reg (σ_push.regions.headD 1) := by
            right; rw [hrg₂]; simp only [st_open, σ_push, AState.pushBnd, hσreg₂, List.headD]
            rw [hIopenSa]; exact List.mem_cons_self
          obtain ⟨hnoVB, hokB⟩ := hbIH hlcB hcfdB (B₀ := B₁) (fuel := n) (by omega)
            (shiftScope_of_freeVarIn fun z hz => hfv z (.letB hz))
            hst₂ hsimP hstat₂F hFlt₂ hnk₃ hnsp₃ hIZeroP hHeadRegP henvTaintP henvNRFP hForbLt₂ hBadDepP
          rw [MS_bind_run]
          cases hevB : (evalS P ext n (bnd :: env) b).run (st₂, B₁) with
          | error e =>
            refine ⟨fun k hk => by cases hk; exact hnoVB k hevB, fun _ _ _ h => by cases h⟩
          | ok pb =>
            rcases pb with ⟨rv, ⟨st₃, B₃⟩⟩; dsimp only
            obtain ⟨rvFoot, hB₃, hst₃, hsz₃, hcap₃, hr₃, hnr₃, hstat₃, hstr₃,
              hpFrame₃, hpEnv₃, hpNum₃, honce₃, hssf₃, hsim₃, henvTaint₃, henvNRF₃,
              hvR₃, hdisjR₃, hnrfR₃, hnvR₃, htaintR₃, hliveR₃, hsrcR₃⟩ := hokB rv st₃ B₃ hevB
            -- Prove `confinedTo s_c rv = false` using `htaintR₃ hvdR₃` + `hnotIn` + `RegUnique_extend_of_zero`!
            have hregU₃ : RegUnique I_open σ₃ s_a s_c :=
              RegUnique_extend_of_zero (fun rg hge => hIZero rg (Nat.le_trans hle₁.2.1 hge)) hsim₁.2.2.1.1
            have hconfF : confinedTo s_c rv = false := by
              unfold confinedTo
              by_cases hmem : s_c ∈ rv.taint
              · exfalso
                have hscIn3 : s_c ∈ st₃.regions := by rw [hr₃, hrg₂]; exact List.mem_cons_self
                have hscInI := (htaintR₃ hvdR₃).2 s_c hmem hscIn3
                obtain ⟨rg, hrgR, hscRg⟩ := Interp.mem_regsOf.mp hscInI
                have hne : rg ≠ s_a := fun hEq => by subst hEq; exact hnotIn hrgR
                exact hregU₃.2 rg (hvR₃.1 rg hrgR) hne hscRg
              · simp [hmem]
            simp only [hconfF, Bool.false_eq_true, ↓reduceIte]
            let st₄ : St := { st₃ with regions := st₃.regions.filter (· != s_c) }
            have hcloseRun : (closeRegion s_c).run st₃ = .ok ((), st₄) := rfl
            rw [MS_bind_run, MS_liftM_run, hcloseRun]; dsimp only
            rw [MS_pure_run]
            refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
            cases hokEq
            -- Close `(s_a, s_c)`, pop index `0`, switch `I_open` back to `I`, shrink `Frame₁` back to `Frame`!
            have hrg₄ : st₄.regions = st.regions := by
              dsimp only [st₄]; rw [hr₃, hrg₂]; dsimp only [st_open]
              have hneS : ∀ rg ∈ st₁.regions, (rg != s_c) = true := fun rg hrg =>
                bne_iff_ne.mpr (Nat.ne_of_lt (hst₁.2.1.2.2 rg hrg).2)
              simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
              rw [List.filter_eq_self.mpr hneS, hr₁]
            have hst₄ : StOk P ext B₃ st₄ := StOk_closeRegion s_c hst₃
            have hsaNe1 : s_a ≠ 1 := by have := hok₁.2.2.1; change σ₁.nextRegion ≠ 1; omega
            have hregClose : (σ₃.closeReg s_a).regions = σ.regions := by
              change σ₃.regions.filter (· != s_a) = σ.regions
              rw [hreg₃]; change σ₂.regions.filter (· != s_a) = σ.regions
              rw [hσreg₂]
              have hne : ∀ rg ∈ σ₁.regions, (rg != s_a) = true := fun rg hrg =>
                bne_iff_ne.mpr (Nat.ne_of_lt (hok₁.2.2.2.2.2 rg hrg).2)
              simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
              rw [List.filter_eq_self.mpr hne, hreg₁]
            have hIokCloseI : InterpOk (σ₃.closeReg s_a) st₄ I := by
              refine ⟨fun rg hlt c hc => ?_, fun c hc => ?_⟩
              · by_cases hltSa : rg < s_a
                · rw [← hIopenLt rg hltSa] at hc; exact hsim₃.2.2.1.1 rg hlt c hc
                · rw [hIZero rg (Nat.le_trans hle₁.2.1 (Nat.le_of_not_lt hltSa))] at hc; cases hc
              · rw [hregClose]; rw [hrg₄] at hc; exact hsim.2.2.1.2 c hc
            have hIokClose : InterpOk (σ₃.closeReg s_a) st₄ I_open := by
              refine ⟨fun rg hlt c hc => hsim₃.2.2.1.1 rg hlt c hc, fun c hc => ?_⟩
              have hhdLt : σ.regions.headD 1 < s_a := by
                cases hrg : σ.regions with
                | nil => simp only [List.headD]; have := hok₁.2.2.1; change 1 < σ₁.nextRegion; omega
                | cons hd tl =>
                  simp only [List.headD]
                  exact Nat.lt_of_lt_of_le (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2 hle₁.2.1
              rw [hregClose, hIopenLt _ hhdLt]
              rw [hrg₄] at hc; exact hsim.2.2.1.2 c hc
            have hsimCloseOpen := Sim_closeRegion s_a s_c hsaNe1 hIokClose hsim₃
            -- Pop index `0` from `hsimCloseOpen` and switch `I_open` → `I`!
            have hsimPopOpen : Sim P ext B₃ st₄ Frame₁ NoKill NoSpend Scope env aenv (σ₃.closeReg s_a) I_open envFoot := by
              obtain ⟨hlen, hokC, hIokC, hidsC, huniqC, hbndsC, hdisjC⟩ := hsimCloseOpen
              refine ⟨by simpa using hlen, hokC, hIokC,
                fun i ab' hab' => hidsC (i + 1) ab' hab',
                fun i j ab₁ ab₂ h1 h2 hid => Nat.succ.inj (huniqC (i + 1) (j + 1) ab₁ ab₂ h1 h2 hid),
                fun i b' ab' hsc' hbi' habi' => hbndsC (i + 1) b' ab' hsc' hbi' habi',
                fun i j b₁ b₂ ab₁ ab₂ hij hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂ =>
                  hdisjC (i + 1) (j + 1) b₁ b₂ ab₁ ab₂ (by omega) hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂⟩
            have hsimFinal : Sim P ext B₃ st₄ Frame NoKill NoSpend Scope env aenv (σ₃.closeReg s_a) I envFoot :=
              Sim_shrink_frame (fun _ h => Or.inl h)
                (Sim_interp_congr_ne (s_a := s_a)
                  hIokCloseI
                  (fun rg hne => by simp [I_open, Interp.extend, hne])
                  (fun i ab' hsc' hab' hne' hmem => by
                    have hiE : i < env.length := by rw [hsim₁.1]; exact (List.getElem?_eq_some_iff.mp hab').1
                    have hlt := ((hsim₁.2.2.2.2.2.1 i env[i] ab' hsc' (List.getElem?_eq_getElem hiE) hab').2 hne').2.1 s_a hmem
                    exact Nat.lt_irrefl _ hlt)
                  hsimPopOpen)
            have hrf₃₄ : RegsFuture st₃ st₄ := RegsFuture.closeRegion st₃ s_c
            have hvRCloseOpen : VSim P ext B₃ st₄ Frame₁ NoKill NoSpend (σ₃.closeReg s_a) I_open rvFoot r rv :=
              VSim_step (Nat.le_refl B₃) hok₃ hleClose hrf₃₄ (PreservesOnceShell.refl _) (StaticStrFresh.refl _)
                (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _) hvR₃
            have hvRFinal : VSim P ext B₃ st₄ Frame NoKill NoSpend (σ₃.closeReg s_a) I rvFoot r rv :=
              VSim_shrink_frame (fun _ h => Or.inl h)
                (VSim_interp_congr (fun rg hrg => by
                  have hne : rg ≠ s_a := fun hEq => by subst hEq; exact hnotIn hrg
                  simp [I_open, Interp.extend, hne]) hvRCloseOpen)
            have hdisjRFinal : ValEnvDisj P st₄ NoKill Scope env aenv (σ₃.closeReg s_a) envFoot rvFoot r rv :=
              fun i b' ab' hsc' hbi' habi' hne' => hdisjR₃ (i + 1) b' ab' hsc' hbi' habi' hne'
            have henvTaintFinal : EnvTaintOk Scope env aenv st₄ I :=
              henvTaint.step hrg₄ (by have : st_open.nextRegion = s_c + 1 := rfl; have : st₄.nextRegion = st₃.nextRegion := rfl; omega)
            have henvNRFFinal : EnvNoReachForbid st₄ Scope env aenv (σ₃.closeReg s_a) Forbid BadReg BadDep :=
              fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
                henvNRF₃ (i + 1) b' ab' hsc' hbi' habi' hne' ha' hregs (fun dep hdep hbd => hdeps dep hdep hbd.2)
            have hpresSS₂ : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap := hpSS₂
            have hpresSS₃ : PreservesLocs (StaticStrLoc st₂) st₂.heap st₃.heap :=
              hpFrame₃.mono fun l hss => hstat₂F l hss
            have hpresEnvAll : PreservesActiveEnv Scope env aenv (σ₃.closeReg s_a) st.heap st₄.heap := by
              intro i b' ab' hsc' hbi' habi' hne' haEnd
              have hvI := ((hsimB.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
              have ha₃ : ActiveVal σ₃ (effVal ab') := haEnd
              have ha₂ : ActiveVal σ₂ (effVal ab') :=
                ActiveVal.of_AStateLe hok₂ (hlePush.trans hle₃) (by have := hle₁.1; exact fun d hd => by have := hvI.2.1 d hd; change d < σ₂.st.size; rw [hszSt₂]; exact Nat.lt_of_lt_of_le this hle₁.1)
                  (fun z hz => by change z < σ₂.st.size; rw [hszSt₂]; exact Nat.lt_of_lt_of_le (hvI.2.2.1 z hz).1 hle₁.1) ha₃
              have ha₁ : ActiveVal σ₁ (effVal ab') :=
                ActiveVal.of_AStateLe hok₁ (hleOpen.trans hle₂) (fun d hd => Nat.lt_of_lt_of_le (hvI.2.1 d hd) hle₁.1)
                  (fun z hz => Nat.lt_of_lt_of_le (hvI.2.2.1 z hz).1 hle₁.1) ha₂
              have hp1 := hpEnv₁ i b' ab' hsc' hbi' habi' hne' ha₁
              have hp2 := hpresEnv₂ i b' ab' hsc' hbi' habi' hne' ha₂
              have hp3 := hpEnv₃ (i + 1) b' ab' hsc' hbi' habi' hne' ha₃
              have hp12 : PreservesLocs (Reach st.heap b'.val) st.heap st₂.heap :=
                hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
              exact hp12.trans (hp3.mono fun l hr => (Reach_congr hp12 l).mpr hr)
            have htaintFinal : ValidDeps (σ₃.closeReg s_a) r.deps →
                (∀ c ∈ rv.taint, c < st₄.nextRegion) ∧ OpenUnder st₄.regions (I.regsOf r.regs) rv := by
              intro hvd
              obtain ⟨ht1, ht2⟩ := htaintR₃ hvd
              have hIeq : I.regsOf r.regs = I_open.regsOf r.regs :=
                Interp.regsOf_congr fun rg hrg => by
                  have hne : rg ≠ s_a := fun hEq => by subst hEq; exact hnotIn hrg
                  simp [I_open, Interp.extend, hne]
              refine ⟨ht1, fun c hc hopen => ?_⟩
              rw [hIeq]
              exact ht2 c hc (List.mem_filter.mp hopen).1
            have hliveFinal : (ValBaseOk st₄ rv ∧ CtorFieldsOk P ext B₃ st₄ rv) ∨
                (IsOnceSrc (σ₃.closeReg s_a) r ∧ SpentOnceSafe st₄.heap rv) :=
              hliveR₃.elim
                (fun ⟨hb, hcf⟩ => Or.inl ⟨ValBaseOk_congr (st := st₃) (st' := st₄) (PreservesLocs.refl _ _) hrf₃₄.1 hb,
                  CtorFieldsOk_congr hb.1 (PreservesLocs.refl _ _) hrf₃₄ hcf⟩)
                (fun ⟨his, hsp⟩ => Or.inr ⟨his, hsp⟩)
            have hsrcFinal : SrcOk Scope aenv σ (σ₃.closeReg s_a) r := by
              intro id hrs
              rcases hsrcR₃ id hrs with ⟨i, ab', hsc', hab', hne', hid', hoo', hdeps'⟩ | ⟨hgeP, hspP⟩
              · cases i with
                | succ k => exact Or.inl ⟨k, ab', hsc', hab', hne', hid', hoo', hdeps'⟩
                | zero =>
                  simp at hab'; subst hab'
                  dsimp only at hid'
                  right
                  have hge0 : σ.st.size ≤ id := by
                    have h1 := hle₁.1; omega
                  refine ⟨hge0, fun hoId dep hdep hlt0 hoDep => ?_⟩
                  have hdepEff := (hdeps' dep).mp hdep
                  have hneDepId : dep ≠ id := by omega
                  have hdepBv : dep ∈ bv.deps := by
                    simp only [effVal, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hdepEff
                    rcases hdepEff with rfl | ⟨h1, _⟩
                    · exact absurd hid'.symm hneDepId.symm
                    · exact h1
                  have hdepX : dep ∈ x.deps := Runs_bindInner_deps_mem hokOpen hbind dep hdepBv
                  have hmOnce : m.binderMode.usage = .once := by
                    have hltP : id < σ_push.once.size := by
                      simp only [σ_push, AState.pushBnd, Array.size_push]; have := hok₂.1; omega
                    have hoP : σ_push.once[id]? = some true := by
                      change σ₃.once[id]? = some true at hoId
                      have h1 := hle₃.2.2.2.1 id hltP; rw [h1] at hoId; exact hoId
                    have hszO : σ₂.once.size = σ₂.st.size := hok₂.1.symm
                    simp only [σ_push, AState.pushBnd, ← hid', ← hszO, Array.getElem?_push_size] at hoP
                    exact beq_iff_eq.mp (Option.some.inj hoP)
                  have hltSp1 : dep < σ_open.spent.size := by
                    have := hle₁.1; have := hok₁.2.1; change dep < σ₁.spent.size; omega
                  have hoOpen : σ_open.once[dep]? = some true := by
                    have hltO2 : dep < σ₂.once.size := by have := hok₂.1; have := hle₁.1; omega
                    have hltOP : dep < σ_push.once.size := by simp [σ_push, AState.pushBnd]; omega
                    change σ₃.once[dep]? = some true at hoDep
                    have h1 := hle₃.2.2.2.1 dep hltOP
                    have h2 := hlePush.2.2.2.1 dep hltO2
                    change σ₁.once[dep]? = some true
                    rw [← hσonce₂, ← h2, ← h1]; exact hoDep
                  have hsp2 : σ₂.spent[dep]? = some true := by
                    have h1 := hspUpd₂ dep hltSp1
                    simp only [hmOnce, or_true, hdepX, hoOpen, and_self, ↓reduceIte] at h1
                    exact h1
                  have hltSp2 : dep < σ₂.spent.size := (Array.getElem?_eq_some_iff.mp hsp2).1
                  have hspP' : σ_push.spent[dep]? = some true := hlePush.2.2.2.2 dep hltSp2 hsp2
                  exact hle₃.2.2.2.2 dep (Array.getElem?_eq_some_iff.mp hspP').1 hspP'
              · right
                have hle0P : σ.st.size ≤ σ_push.st.size :=
                  Nat.le_trans hle₁.1 (Nat.le_trans hleOpen.1 (Nat.le_trans hle₂.1 hlePush.1))
                exact ⟨Nat.le_trans hle0P hgeP, fun hoId dep hdep hlt0 hoDep =>
                  hspP hoId dep hdep (Nat.lt_of_lt_of_le hlt0 hle0P) hoDep⟩
            exact ⟨rvFoot, by omega, hst₄,
              Nat.le_trans hsz₁ (Nat.le_trans hsz₂ hsz₃), Nat.le_trans hcap₁ (Nat.le_trans hcap₂ hcap₃),
              hrg₄, by have : st_open.nextRegion = s_c + 1 := rfl; have : st₄.nextRegion = st₃.nextRegion := rfl; omega,
              hstat₁.trans (hstat₂ ▸ hstat₃), hstr₁.trans (hstr₂ ▸ hstr₃),
              hpFrame₁.trans ((hpFrame₂.mono fun _ h => Or.inl h).trans (hpFrame₃.mono fun _ h => Or.inl h)),
              hpresEnvAll,
              fun l o num ho hc => hpNum₃ l o num (hpresNum₂ l o num (hpNum₁ l o num ho hc) hc) hc,
              honce₁.trans (honce₂.trans honce₃),
              StaticStrFresh.trans (Nat.le_trans hsz₁ hsz₂) hpresSS₃
                (StaticStrFresh.trans hsz₁ hpresSS₂ hssf₁ hssf₂) hssf₃,
              hsimFinal, henvTaintFinal, henvNRFFinal, hvRFinal, hdisjRFinal,
              (fun ha hregs hdeps => hnrfR₃ ha hregs (fun dep hdep hbd => hdeps dep hdep hbd.2)),
              (fun hvd hne =>
                let ⟨hb, hnv⟩ := hnvR₃ hvd hne
                ⟨ValBaseOk_congr (st := st₃) (st' := st₄) (PreservesLocs.refl _ _) hrf₃₄.1 hb, hnv⟩),
              htaintFinal, hliveFinal, hsrcFinal⟩

/-! ### Section 4B: `AMajor.varConsuming`, `AAlt.lamErased`, `AAlt.lamKept`, `ATerm.caseTerm` -/

/-- `select` on a live `.once` reference is always `.error .stuck` (never a violation). -/
theorem select_spentOnce_ref_stuck {P : Prog} {k : CaseInfo} {st : St}
    {loc cap : Nat} {t : List Nat} {o : Obj} {tgt : Val} {sp : Bool}
    (ho : st.heap.objs[loc]? = some o) (hcap : o.cap = cap) (hcell : o.cell = .once tgt sp) :
    (select P k (.ref loc cap t)).run st = .error .stuck := by
  unfold select
  by_cases hnat : (P.nat == some k.ind) = true
  · simp only [hnat, ↓reduceIte, M_bind_run]
    have hnum : (numOf? (.ref loc cap t)).run st = .ok (none, st) := by
      unfold numOf?; rw [M_bind_run]
      have hobj : (obj loc).run st = .ok (o, st) := by unfold obj; rw [M_bind_run, M_get_run]; simp [ho]; rfl
      rw [hobj]; dsimp only
      have hcB : (o.cap == cap) = true := beq_iff_eq.mpr hcap
      simp only [hcB, ↓reduceIte, hcell, M_pure_run]
    rw [hnum]; rfl
  · simp only [hnat, Bool.false_eq_true, ↓reduceIte, M_bind_run]
    have hobj : (obj loc).run st = .ok (o, st) := by unfold obj; rw [M_bind_run, M_get_run]; simp [ho]; rfl
    rw [hobj]; dsimp only
    have hcB : (o.cap == cap) = true := beq_iff_eq.mpr hcap
    simp only [hcB, ↓reduceIte, hcell]; rfl

/-- Extract `PreservesActiveEnv` and `.num`-cell preservation across `Eval.ret` from `ret_spec`
and `conform_spec_full` (for both `rc = .val` and `rc ≠ .val`). -/
theorem ret_preserves_env_num {P : Prog} {ext : ExternOracle} {B fuel s_a s_c cur : Nat}
    {res : ResultMode} {rc : Cls} {w : String}
    {st_b st_ret : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ_b σ_ret : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {rFoot : Nat → Prop}
    {r : AVal} {rv_b rv' : Val}
    (hst : StOk P ext B st_b)
    (hsim : Sim P ext B st_b Frame NoKill NoSpend Scope env aenv σ_b I envFoot)
    (hNoKill : NoKillOk NoKill σ_ret)
    (hregU : RegUnique I σ_b s_a s_c)
    (hs_in : s_c ∈ st_b.regions)
    (hvR : VSim P ext B st_b Frame NoKill NoSpend σ_b I rFoot r rv_b)
    (hdisjR : ValEnvDisj P st_b NoKill Scope env aenv σ_b envFoot rFoot r rv_b)
    (hretChk : Runs (retCheck r.skel res s_a { r with cls := rc } w) σ_b () σ_ret)
    (hrunR : (ret P fuel s_c cur res rc rv_b).run st_b = .ok (rv', st_ret)) :
    PreservesActiveEnv Scope env aenv (σ_ret.closeReg s_a) st_b.heap st_ret.heap ∧
    (∀ (l : Nat) (o : Obj) (n : Nat), st_b.heap.objs[l]? = some o → o.cell = .num n →
      st_ret.heap.objs[l]? = some o) := by
  obtain ⟨_, hle, _, _, _, _, _, hvdR, _, hooR, hnotOnceR, hvalInfo, hstUpd⟩ :=
    Runs_retCheck hsim.2.1 hretChk
  have haR : ActiveVal σ_b r := ⟨hvdR, fun his => absurd his hnotOnceR⟩
  have hvAct := hvR.2.2.2.2 haR
  by_cases hrcV : rc = .val
  · subst hrcV
    have hinfo := hvalInfo rfl
    have hretS := ret_spec (P := P) (fuel := fuel) (s := s_c) (cur := cur) (r := res) (c := .val) (v := rv_b)
      hst.1 hvAct.1.1 hvAct.1.2.1
      (fun hu => by
        by_cases hrv : r.cls = .val
        · exact (hvAct.2.2.2.2.2.2.2 ⟨hrv, (hinfo.2.2 hu).1, hooR, hnotOnceR,
            fun d hd => ⟨(hinfo.2.2 hu).2 d hd, fun hnkD => hNoKill d hnkD (by
              have h1 := hstUpd d (hvR.2.1 d hd)
              simp only [hu, hd, and_self, ↓reduceIte] at h1; exact h1)⟩⟩).1
        · exact (hvAct.2.2.2.1 hnotOnceR hrv).ownTreeFull.1)
      (fun hnb x hx hm => by
        simp only [List.mem_singleton] at hm; subst x
        have hnoS := hinfo.1 hnb
        obtain ⟨rg, hrg, hscRg⟩ := Interp.mem_regsOf.mp (hvAct.2.1 rv_b (HeldBy.refl _ _) s_c hx hs_in)
        have hne : rg ≠ s_a := fun hEq => hnoS (show s_a ∈ r.regs from hEq ▸ hrg)
        exact False.elim (hregU.2 rg (hvR.1 rg hrg) hne hscRg))
      (fun hu => by
        have hdou := hvAct.2.1; rw [hinfo.2.1 hu, Interp.regsOf_nil] at hdou
        exact hdou rv_b (HeldBy.refl _ _))
    rcases hretS with hS | hO | ⟨_, _, hrun0, _, _, _, _, _, _, _, _, hpres0, _⟩
    · rw [hrunR] at hS; cases hS
    · rw [hrunR] at hO; cases hO
    · rw [hrunR] at hrun0; cases hrun0
      refine ⟨fun i b ab hsc hbi habi hne haEnd => ?_, fun l o n ho hc =>
        (hpres0 l ⟨(Array.getElem?_eq_some_iff.mp ho).1,
          fun _ hor => OwnReach_not_numLoc hor ⟨o, n, ho, hc⟩⟩).trans ho⟩
      have hvI := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
      have ha0 := ActiveVal.of_AStateLe hsim.2.1 hle hvI.2.1 (fun z hz => (hvI.2.2.1 z hz).1) haEnd
      refine hpres0.mono fun l hrB => ⟨(hvI.2.2.2.2 ha0).1.1.reach_lt_size hrB, fun hu hor => ?_⟩
      by_cases hrv : r.cls = .val
      · have htrR : Transferable σ_b NoKill r :=
          ⟨hrv, (hinfo.2.2 hu).1, hooR, hnotOnceR, fun d hd => ⟨(hinfo.2.2 hu).2 d hd, fun hnkD => hNoKill d hnkD (by
            have h1 := hstUpd d (hvR.2.1 d hd); simp only [hu, hd, and_self, ↓reduceIte] at h1; exact h1)⟩⟩
        have hdd : ∀ d ∈ r.deps, d ∉ (effVal ab).deps := fun d hd hdk => by
          have h1 := hstUpd d (hvR.2.1 d hd); simp only [hu, hd, and_self, ↓reduceIte] at h1
          exact (haEnd.1 d hdk).2 h1
        exact (hdisjR i b ab hsc hbi habi hne).1 haR htrR ha0 hdd l hor hrB
      · exact (hvAct.2.2.2.1 hnotOnceR hrv).ownTreeFull.2 l hor
  · -- `rc ≠ .val`: `conform rc rv_b` produces `NonValSafe`, so `ret` preserves ALL old heap locations!
    have hpresAll : PreservesLocs (fun l => l < st_b.heap.objs.size) st_b.heap st_ret.heap := by
      unfold ret at hrunR; rw [M_bind_run] at hrunR
      rcases conform_spec_full (P := P) hst.1 hvAct.1.1 hvAct.1.2.1 with hStC |
        ⟨v₁, st₁, hrunC, _, _, _, _, hsz₁, _, hpres₁, hc₁, hdl₁, hcls₁, hacyc₁, _⟩
      · rw [hStC] at hrunR; cases hrunR
      · rw [hrunC] at hrunR; dsimp only at hrunR
        have hnv₁ : NonValSafe st₁.heap v₁ := ClsSafe.to_nonValSafe hrcV (ClsSafe.of_clsOk hcls₁) hdl₁.self.1
        have hconfF : confinedTo s_c v₁ = false := by
          unfold confinedTo; rw [hnv₁.taint_nil]; rfl
        cases res with
        | shared =>
          simp only [hconfF, Bool.false_eq_true, ↓reduceIte, M_pure_run] at hrunR; cases hrunR; exact hpres₁
        | borrowed =>
          rw [M_pure_run] at hrunR; cases hrunR; exact hpres₁
        | unique =>
          simp only [hconfF, Bool.false_eq_true, ↓reduceIte] at hrunR
          rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := false)
              hc₁ hdl₁ hacyc₁ hnv₁.ownTreeFull.1 (fun _ => hnv₁.deepOpenUnder_nil v₁ (HeldBy.refl _ _)) with hOOF |
            ⟨_, _, hrunT, _, _, _, _, _, _, _, _, _, _, hpresT⟩
          · rw [hrunR] at hOOF; cases hOOF
          · rw [hrunR] at hrunT; cases hrunT
            exact hpres₁.trans (hpresT.mono fun l _ hor => hnv₁.ownTreeFull.2 l hor)
        | uniqueBorrowed =>
          rw [M_bind_run] at hrunR
          rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := true)
              hc₁ hdl₁ hacyc₁ hnv₁.ownTreeFull.1 (fun h => by cases h) with hOOF |
            ⟨_, _, hrunT, _, _, _, _, _, _, _, _, _, _, hpresT⟩
          · rw [hOOF] at hrunR; cases hrunR
          · rw [hrunT] at hrunR; dsimp only at hrunR; rw [M_pure_run] at hrunR; cases hrunR
            exact hpres₁.trans (hpresT.mono fun l _ hor => hnv₁.ownTreeFull.2 l hor)
    exact ⟨Sim_preserves_of_old (hle.trans (AStateLe_closeReg s_a σ_ret)) hpresAll hsim,
      fun l o n ho _ => (hpresAll l (Array.getElem?_eq_some_iff.mp ho).1).trans ho⟩

/-- Soundness for `AMajor.varConsuming` (`var_bridge` + `Runs_flowTo` + `transfer_sound`). -/
theorem evalS_major_varConsuming {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {j : Nat} {mc : Cls} {b : ABnd} {σ σ₁ σ₂ : AState} {v : AVal}
    (hb : aenv[j]? = some b)
    (hread : Runs (readVar aenv j) σ v σ₁)
    (hu : b.mode.isUnique = true)
    (hmc : mc = .val)
    (hfl : Runs (flowTo (.uniq b.mode.isBorrowed) v.skel v "a consuming match") σ₁ () σ₂) :
    AMajorProp P ext B aenv (.var j mc) σ
      { v with own := .uniq, deps := [], cls := mc, src := none } true σ₂ := by
  classical
  subst hmc
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    _ hfv hst hsim hstat hFlt hnk₂ hnsp₂ _ _ henvTaint henvNRF hForbidLt hBadDep₂
  have hok := hsim.2.1
  have hscJ : Scope j := hfv j (by simpa using FreeVarIn.var (d := 0) (i := j) (c := .val) (Nat.zero_le j))
  obtain ⟨hσ₁Eq, ⟨bc, ab', hbcJ, habJ, hmodeEq, hneAb, hvEq⟩, hvar⟩ :=
    var_bridge hst hsim henvNRF hFlt hForbidLt hscJ hread (c := .val)
  subst σ₁
  rw [hb] at habJ; cases habJ
  obtain ⟨hok₂, hle₂, hsz₂, honce₂, hspSz₂, hreg₂, hnr₂, hvd, _, hneOnce, _, _, _, _, huniq⟩ :=
    Runs_flowTo hok hfl
  obtain ⟨_, hooF, hnotOnce⟩ := hneOnce (by intro h; cases h)
  have hactV : ActiveVal σ v := ⟨hvd, fun his => absurd his hnotOnce⟩
  have hbcU : bc.mode.isUnique = true := hmodeEq ▸ hu
  have hbcNe : bc.mode ≠ .erased := hmodeEq ▸ hneAb
  have hbcNeB : (bc.mode == .erased) = false := BinderMode_beq_false_of_ne hbcNe
  let mVar : M Val := do
    let some b := env[j]? | stuckM
    if b.mode == BinderMode.erased then violate .erasedRead
    live b.val
    conform .val b.val
  have hstep : (evalMajorS P ext fuel env (.var j .val)).run (st, B₀) =
      match (match mVar.run st with
        | .ok (rv0, st0) => (transfer P fuel bc.mode.isBorrowed rv0).run st0
        | .error e => .error e) with
      | .ok (rv, st') => .ok (rv, (st', B₀))
      | .error e => .error e := by
    have hinner : (do
        let some b := env[j]? | stuckM
        if b.mode == BinderMode.erased then violate .erasedRead
        live b.val
        let v ← conform .val b.val
        if b.mode.isUnique then transfer P fuel b.mode.isBorrowed v else pure v).run st =
        match mVar.run st with
        | .ok (rv0, st0) => (transfer P fuel bc.mode.isBorrowed rv0).run st0
        | .error e => .error e := by
      dsimp only [mVar]
      simp only [hbcJ, hbcNeB, Bool.false_eq_true, ↓reduceIte, hbcU, M_bind_run]
      cases (live bc.val).run st with
      | error _ => rfl
      | ok pl =>
        dsimp only
        have hconf : (conform .val bc.val).run pl.2 = .ok (bc.val, pl.2) := rfl
        rw [hconf]
    unfold evalMajorS; rw [MS_liftM_run, hinner]
    cases (match mVar.run st with
      | .ok (rv0, st0) => (transfer P fuel bc.mode.isBorrowed rv0).run st0
      | .error e => .error e) <;> rfl
  let mv' : AVal := { v with own := .uniq, deps := [], cls := .val, src := none }
  have hconsPost : True → ActiveVal σ₂ mv' ∧ Transferable σ₂ NoKill mv' ∧ mv'.deps = [] ∧ mv'.src = none := fun _ =>
    ⟨⟨(fun _ h => by cases h), (fun ⟨_, hs, _⟩ => by cases hs)⟩,
     ⟨rfl, rfl, hooF, (fun ⟨_, hs, _⟩ => by cases hs), (fun _ h => by cases h)⟩, rfl, rfl⟩
  refine ⟨?_, fun _ => hconsPost trivial⟩
  unfold TermPost; rw [hstep]
  rcases hvar with hStV | ⟨rv0, st0, hrunV, hrg0, hnr0, hstat0, hstr0, hsz0, hcap0, hpresAll0, hpresF0,
    honce0, hssf0, hst0, hsim0, henvNRF0, hv0, hdisj0, hnrf0, hnv0, hreach0⟩
  · change mVar.run st = .error .stuck at hStV
    rw [hStV]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  · change mVar.run st = .ok (rv0, st0) at hrunV
    rw [hrunV]; dsimp only
    have hv0Act := hv0.2.2.2.2 hactV
    have hplain0 := hv0Act.2.2.2.2.1 ⟨hnotOnce, hooF⟩
    have htr_and_open : OwnTreeFull P st0.heap rv0 ∧
        (bc.mode.isBorrowed = false → OpenUnder st0.regions [] rv0) ∧
        (∀ l, OwnReach P st0.heap rv0 l → ¬ Frame l ∧ ¬ StaticStrLoc st0 l) := by
      by_cases hcv : v.cls = .val
      · obtain ⟨hown, hlv, hrgNil⟩ := (huniq b.mode.isBorrowed rfl).1 hcv
        have hdead2 : ∀ d ∈ v.deps, σ₂.st[d]? = some .dead := fun d hd => by
          have h1 := (huniq b.mode.isBorrowed rfl).2 d (hvd d hd).1
          simp only [hcv, hd, and_self, ↓reduceIte] at h1; exact h1
        have htr : Transferable σ NoKill { v with cls := .val } :=
          ⟨rfl, hown, hooF, hnotOnce, fun d hd => ⟨hlv d hd, fun hnkD => hnk₂ d hnkD (hdead2 d hd)⟩⟩
        obtain ⟨hotf, hdisjF⟩ := hv0Act.2.2.2.2.2.2.2 htr
        refine ⟨hotf, fun hnb => ?_, hdisjF⟩
        have hdou := hv0Act.2.1
        rw [show ({ v with cls := .val } : AVal).regs = [] from hrgNil (hmodeEq ▸ hnb), Interp.regsOf_nil] at hdou
        exact hdou rv0 (HeldBy.refl _ _)
      · have hnv := ((hsim0.2.2.2.2.2.1 j bc b hscJ hbcJ hb).2 hneAb).2.2.2.2.2 (hvEq ▸ hactV) |>.2.2.2.1
            (hvEq ▸ hnotOnce) (hvEq ▸ hcv)
        have hrv0Eq : rv0 = bc.val ∧ st0 = st := by
          have hvBc := ((hsim.2.2.2.2.2.1 j bc b hscJ hbcJ hb).2 hneAb).2.2.2.2.2 (hvEq ▸ hactV)
          dsimp only [mVar] at hrunV
          simp only [hbcJ, hbcNeB, Bool.false_eq_true, ↓reduceIte, M_bind_run] at hrunV
          rw [live_ok hvBc.1.1.self.1] at hrunV; dsimp only at hrunV
          have hconf : (conform .val bc.val).run st = .ok (bc.val, st) := rfl
          rw [hconf] at hrunV; cases hrunV; exact ⟨rfl, rfl⟩
        obtain ⟨hrv0Eq, hst0Eq⟩ := hrv0Eq; subst rv0; subst st0
        exact ⟨hnv.ownTreeFull.1, fun _ => hnv.deepOpenUnder_nil bc.val (HeldBy.refl _ _),
          fun l hor => False.elim (hnv.ownTreeFull.2 l hor)⟩
    rcases transfer_sound (fuel := fuel) (toBorrowed := bc.mode.isBorrowed)
        hst0 hv0Act.1 hplain0.1 hv0Act.2.2.1 hplain0.2.2
        htr_and_open.1 htr_and_open.2.1 (fun l hor => (htr_and_open.2.2 l hor).2) with hOOF |
      ⟨rv', st', hrunT, hr', hnr', hstat', hstr', hsz', hcap', _, _, hvsh', hpresT,
       honceT, hssfT, hst', hbv', hno', hcf', hfun', hotf', hdouT, hreachT, hownT⟩
    · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · rw [hrunT]
      refine ⟨(fun _ h => by cases h), fun rv1 st1 B1 hokEq => ?_⟩
      cases hokEq
      have hrv0Eq : rv0 = bc.val ∧ st0 = st := by
        have hvBc := ((hsim.2.2.2.2.2.1 j bc b hscJ hbcJ hb).2 hneAb).2.2.2.2.2 (hvEq ▸ hactV)
        dsimp only [mVar] at hrunV
        simp only [hbcJ, hbcNeB, Bool.false_eq_true, ↓reduceIte, M_bind_run] at hrunV
        rw [live_ok hvBc.1.1.self.1] at hrunV; dsimp only at hrunV
        have hconf : (conform .val bc.val).run st = .ok (bc.val, st) := rfl
        rw [hconf] at hrunV; cases hrunV; exact ⟨rfl, rfl⟩
      obtain ⟨hrv0Eq, hst0Eq⟩ := hrv0Eq; subst rv0; subst st0
      have hrf' : RegsFuture st st' := RegsFuture.same_regions (hnr' ▸ Nat.le_refl _) hr'
      have hIok₂ : InterpOk σ₂ st' I :=
        ⟨fun rg hlt c hc => hnr' ▸ hsim.2.2.1.1 rg (hnr₂ ▸ hlt) c hc,
         fun c hc => by rw [hreg₂]; rw [hr'] at hc; exact hsim.2.2.1.2 c hc⟩
      have hdead_of_val : v.cls = .val → ∀ d ∈ v.deps, σ₂.st[d]? = some .dead := fun hcv d hd => by
        have h1 := (huniq b.mode.isBorrowed rfl).2 d (hvd d hd).1
        simp only [hcv, hd, and_self, ↓reduceIte] at h1; exact h1
      have htrV_of_val : v.cls = .val → Transferable σ NoKill { v with cls := .val } := fun hcv =>
        let ⟨hown, hlv, _⟩ := (huniq b.mode.isBorrowed rfl).1 hcv
        ⟨rfl, hown, hooF, hnotOnce, fun d hd => ⟨hlv d hd, fun hnkD => hnk₂ d hnkD (hdead_of_val hcv d hd)⟩⟩
      have hnv_of_ne : v.cls ≠ .val → NonValSafe st.heap bc.val := fun hne =>
        (((hsim.2.2.2.2.2.1 j bc b hscJ hbcJ hb).2 hneAb).2.2.2.2.2 (hvEq ▸ hactV)).2.2.2.1
          (hvEq ▸ hnotOnce) (hvEq ▸ hne)
      have hpresF' : PreservesLocs Frame st.heap st'.heap :=
        hpresT.mono fun l hF hor => (htr_and_open.2.2 l hor).1 hF
      have hpresSS' : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
        hpresT.mono fun l hss hor => (htr_and_open.2.2 l hor).2 hss
      have hpresNum' : ∀ (l : Nat) (o : Obj) (n : Nat),
          st.heap.objs[l]? = some o → o.cell = .num n → st'.heap.objs[l]? = some o := fun l o n ho hc =>
        (hpresT l fun hor => OwnReach_not_numLoc hor ⟨o, n, ho, hc⟩).trans ho
      have hpresEnv' : PreservesActiveEnv Scope env aenv σ₂ st.heap st'.heap := by
        intro k bk abk hsc hbk habk hne ha₂
        have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
        have ha0 := ActiveVal.of_AStateLe hok hle₂ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha₂
        refine hpresT.mono fun l hrK hor => ?_
        by_cases hcv : v.cls = .val
        · have hdd : ∀ d ∈ ({ v with cls := .val } : AVal).deps, d ∉ (effVal abk).deps := fun d hd hdk =>
            (ha₂.1 d hdk).2 (hdead_of_val hcv d hd)
          exact (hdisj0 k bk abk hsc hbk habk hne).1 hactV (htrV_of_val hcv) ha0 hdd l hor hrK
        · exact (hnv_of_ne hcv).ownTreeFull.2 l hor
      have hsim₂ : Sim P ext B₀ st' Frame NoKill NoSpend Scope env aenv σ₂ I envFoot :=
        Sim_step (Nat.le_refl B₀) hle₂ hok₂ hIok₂ hrf' honceT hssfT (fun _ _ _ h => h) hpresEnv' hsim
      have henvNRF₂ : EnvNoReachForbid st' Scope env aenv σ₂ Forbid BadReg BadDep :=
        EnvNoReachForbid_step hok hle₂ (Sim_deps_lt hsim) hsim.2.2.2.1
          (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpresSS' hpresEnv' henvNRF
      have hdouMv' : DeepOpenUnder st'.heap st'.regions (I.regsOf mv'.regs) rv' := by
        rw [hr']; exact hdouT st.regions (I.regsOf mv'.regs) hv0Act.2.1
      have hVSimMv' : VSim P ext B₀ st' Frame NoKill NoSpend σ₂ I (fun _ => False) mv' rv' :=
        ⟨fun rg hrg => hnr₂ ▸ hv0.1 rg hrg, (fun _ h => by cases h), (fun _ hs => by cases hs),
         (fun _ ⟨_, hs, _⟩ => by cases hs), fun _ =>
          ⟨hbv', hdouMv', hcf', (fun _ hne => absurd rfl hne),
           fun _ => ⟨hno', fun _ h => h, hfun'⟩,
           (fun h => by change v.onceOnly = true at h; rw [hooF] at h; cases h),
           (fun ⟨_, hs, _⟩ => by cases hs),
           fun _ => ⟨hotf', fun l hor =>
             let hor0 := (hownT l).mp hor
             ⟨(htr_and_open.2.2 l hor0).1, fun hss' => by
               rcases hssfT l hss' with hge | hss0 | hnum'
               · exact Nat.not_lt_of_ge hge (hsz' ▸ hv0Act.1.1.reach_lt_size (OwnReach_toReach hor0))
               · exact (htr_and_open.2.2 l hor0).2 hss0
               · exact OwnReach_not_numLoc hor hnum'⟩⟩⟩⟩
      have hDisjMv' : ValEnvDisj P st' NoKill Scope env aenv σ₂ envFoot (fun _ => False) mv' rv' := by
        intro k bk abk hsc hbk habk hne
        have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
        refine ⟨?_, ?_, (fun _ hf => by
            rcases hf with hoo | ⟨⟨_, hs, _⟩, _⟩
            · change v.onceOnly = true at hoo; rw [hooF] at hoo; cases hoo
            · cases hs),
          ?_,
          (fun _ hf => by
            rcases hf with hoo | ⟨⟨_, hs, _⟩, _⟩
            · change v.onceOnly = true at hoo; rw [hooF] at hoo; cases hoo
            · cases hs),
          (fun hs => by cases hs), (fun _ hs => by cases hs)⟩
        · intro _ _ haK₂ _ l hor' hrK'
          have haK0 := ActiveVal.of_AStateLe hok hle₂ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haK₂
          have hor0 := (hownT l).mp hor'
          have hrK0 := (Reach_congr (hpresEnv' k bk abk hsc hbk habk hne haK₂) l).mp hrK'
          by_cases hcv : v.cls = .val
          · have hdd : ∀ d ∈ ({ v with cls := .val } : AVal).deps, d ∉ (effVal abk).deps := fun d hd hdk =>
              (haK₂.1 d hdk).2 (hdead_of_val hcv d hd)
            exact (hdisj0 k bk abk hsc hbk habk hne).1 hactV (htrV_of_val hcv) haK0 hdd l hor0 hrK0
          · exact (hnv_of_ne hcv).ownTreeFull.2 l hor0
        · intro haK₂ htrK₂ _ _ l horK' hr'
          have haK0 := ActiveVal.of_AStateLe hok hle₂ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haK₂
          have htrK0 := Transferable.of_AStateLe hok hle₂ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) (fun _ h => h) htrK₂
          have horK0 := (OwnReach_congr (hpresEnv' k bk abk hsc hbk habk hne haK₂) l).mp horK'
          have hr0 := (hreachT l).mp hr'
          by_cases hcv : v.cls = .val
          · have hdd : ∀ d ∈ (effVal abk).deps, d ∉ ({ v with cls := .val } : AVal).deps := fun d hdk hd => by
              have hlv := (htrK₂.2.2.2.2 d hdk).1
              rw [hdead_of_val hcv d hd] at hlv; cases hlv
            exact (hdisj0 k bk abk hsc hbk habk hne).2.1 haK0 htrK0 hactV hdd l horK0 hr0
          · exact OwnReach_not_numLoc horK0 ((hnv_of_ne hcv).reach_numLoc hr0)
        · intro haK₂ hftK₂ _ _ l hft hr'
          have haK0 := ActiveVal.of_AStateLe hok hle₂ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haK₂
          have hftK0 := FootActive.of_AStateLe hok hle₂ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) hftK₂
          have hr0 := (hreachT l).mp hr'
          have hneSrc : ({ v with cls := .val } : AVal).src ≠ some abk.id := by
            intro hEq
            have hidEq : b.id = abk.id := Option.some.inj (by simpa [hvEq, effVal] using hEq)
            have hjk : j = k := hsim.2.2.2.2.1 j k b abk hb habk hidEq
            subst hjk; rw [hb] at habk; cases habk
            rcases hftK0 with hooB | ⟨hisB, _⟩
            · rw [← hvEq] at hooB; rw [hooF] at hooB; cases hooB
            · exact hnotOnce (hvEq ▸ hisB)
          exact (hdisj0 k bk abk hsc hbk habk hne).2.2.2.1 haK0 hftK0 hactV hneSrc l hft hr0
      have hNrfMv' : ActiveVal σ₂ mv' → NoReachForbid st' Forbid BadReg BadDep mv' rv' := by
        intro _ hbadR _ l hr' hnotSS' hnotNum' hF
        have hr0 := (hreachT l).mp hr'
        have hnotSS0 : ¬ StaticStrLoc st l := fun hss0 =>
          hnotSS' (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _) hpresSS' hss0)
        have hnotNum0 : ¬ NumLoc st.heap l := fun ⟨o, n, ho, hc⟩ =>
          hnotNum' ⟨o, n, hpresNum' l o n ho hc, hc⟩
        by_cases hcv : v.cls = .val
        · have hbadD0 : ∀ d ∈ ({ v with cls := .val } : AVal).deps, ¬ BadDep d := fun d hd hbd => by
            have hlv := hBadDep₂ d hbd
            rw [hdead_of_val hcv d hd] at hlv; cases hlv
          exact hnrf0 hactV hbadR hbadD0 l hr0 hnotSS0 hnotNum0 hF
        · exact hnotNum0 ((hnv_of_ne hcv).reach_numLoc hr0)
      exact ⟨fun _ => False, Nat.le_refl B₀, hst', hsz' ▸ Nat.le_refl _, hcap', hr', hnr' ▸ Nat.le_refl _,
        hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
        hpresF', hpresEnv', hpresNum', honceT, hssfT,
        hsim₂, henvTaint.step hr' (hnr' ▸ Nat.le_refl _), henvNRF₂,
        hVSimMv', hDisjMv', hNrfMv', (fun _ hne => absurd rfl hne),
        taint_of_vsim_src_none rfl hVSimMv', Or.inl ⟨hbv', hcf'⟩, SrcOk_none rfl⟩

/-- Soundness for `AAlt.lamErased` (open region, push erased binder, recurse on `rest`,
`retCheck_altRetVal_bridge`, and switch `I_open` back to `I`). -/
theorem evalS_alt_lamErased {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {body : Term}
    {a0 : AVal} {fromCell : Bool} {rest : List (AVal × Bool × Bool)}
    {σ σ₁ σ₂ : AState} {r : AVal}
    (haltD : AAlt P ({ id := σ.openReg.2.st.size, mode := .erased, val := { cls := .irr } } :: aenv)
      body rest (σ.openReg.2.pushBnd { cls := .irr } false).2 r σ₁)
    (haltIH : AAltProp P ext B ({ id := σ.openReg.2.st.size, mode := .erased, val := { cls := .irr } } :: aenv)
      body rest (σ.openReg.2.pushBnd { cls := .irr } false).2 r σ₁)
    (hretChk : Runs (retCheck r.skel res σ.openReg.1 { r with cls := rc } "a case alternative") σ₁ () σ₂) :
    AAltProp P ext B aenv (.lam p res rc fvs body) ((a0, true, fromCell) :: rest) σ
      (altRetVal res rc σ.openReg.1 ((σ₂.closeReg σ.openReg.1).regions.headD 1) r)
      (σ₂.closeReg σ.openReg.1) := by
  classical
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep cargs
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    hlen hNonCons hArgsMeta hArgList
  cases hlc with | lam hlcB _ =>
  cases hcfd with | lam hcfdB =>
  cases cargs with
  | nil => simp at hlen
  | cons hdC restC =>
    rcases hdC with ⟨a, er_c⟩
    have hErTrue : er_c = true := (hArgsMeta 0 a er_c a0 true fromCell rfl rfl).1
    subst hErTrue
    cases fuel with
    | zero =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ b0 => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_succ]; rfl)
    | succ n =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ b0 =>
        have hok := hsim.2.1
        let s_a := σ.openReg.1
        let σ_open := σ.openReg.2
        have hokOpen : AStateOk σ_open := (AStateOk.openReg hok).1
        have hleOpen : AStateLe σ σ_open := AStateLe_openReg σ
        let ab : ABnd := { id := σ_open.st.size, mode := .erased, val := { cls := .irr } }
        let σ_push := (σ_open.pushBnd { cls := .irr } false).2
        have hokPush : AStateOk σ_push := (hokOpen.pushBnd _ _).1
        have hlePush : AStateLe σ_open σ_push := (hokOpen.pushBnd _ _).2
        obtain ⟨hok₁, hle₁, hreg₁⟩ := AAlt_state_le hokPush haltD
        obtain ⟨hok₂, hle₂, hstSz₂, honce₂, hsp₂, hreg₂, hnr₂, hvdR₁, _, hooR₁, hnotOnceR₁, _, _⟩ :=
          Runs_retCheck hok₁ hretChk
        have hleClose : AStateLe σ₂ (σ₂.closeReg s_a) := AStateLe_closeReg s_a σ₂
        have hnk₂ : NoKillOk NoKill σ₂ := NoKillOk_of_AStateLe hleClose hnkEnd
        have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnk₂
        have hnsp₂ : NoSpendOk NoSpend σ₂ := NoSpendOk_of_AStateLe hleClose hnspEnd
        have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnsp₂
        let BadReg' : Nat → Prop := fun rg => rg < σ.nextRegion ∧ BadReg rg
        let BadDep' : Nat → Prop := fun dep => dep < σ_push.st.size ∧ BadDep dep
        have hBadDep₂ : ∀ dep, BadDep' dep → σ₂.st[dep]? = some .live := fun dep hbd => hBadDepEnd dep hbd.2
        have hBadDep₁ : ∀ dep, BadDep' dep → σ₁.st[dep]? = some .live :=
          BadDepLive_of_AStateLe hle₂ hBadDep₂ (fun dep hbd => Nat.lt_of_lt_of_le hbd.1 hle₁.1)
        have hNotBadS : ¬ BadReg' s_a := fun h => Nat.lt_irrefl _ h.1
        have hstep : (applyAltS P ext (n + 1) env (.lam p res rc fvs body) ((a, true) :: restC)).run (st, b0 + 1) =
            (do
              let (s, cur) ← liftM openRegion
              let r ← applyAltS P ext n (⟨.imm .irr, .erased⟩ :: env) body restC
              let r ← liftM (ret P n s cur res rc r)
              liftM (closeRegion s)
              pure r).run (st, b0) := by
          conv => lhs; unfold applyAltS
          rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [↓reduceIte, MS_bind_run, MS_liftM_run]
          cases openRegion.run st with
          | error _ => rfl
          | ok p0 => rcases p0 with ⟨⟨s, cur⟩, st0⟩; rfl
        unfold TermPost; rw [hstep]
        let s_c := st.nextRegion
        let cur := st.regions.headD 0
        let st_open : St := { st with nextRegion := s_c + 1, regions := s_c :: st.regions }
        have hopenRun : openRegion.run st = .ok ((s_c, cur), st_open) := rfl
        rw [MS_bind_run, MS_liftM_run, hopenRun]; dsimp only
        let I_open : Interp := I.extend s_a s_c
        have hIopenLt : ∀ rg, rg < s_a → I_open.reg rg = I.reg rg := fun rg hlt => by
          simp [I_open, Interp.extend, Nat.ne_of_lt hlt]
        have hIopenSa : I_open.reg s_a = [s_c] := by simp [I_open, Interp.extend]
        have hIopenZero : ∀ rg, σ_push.nextRegion ≤ rg → I_open.reg rg = [] := fun rg hge => by
          have hne : rg ≠ s_a := by simp only [σ_push, AState.pushBnd, σ_open, s_a, AState.openReg] at hge ⊢; omega
          have hge0 : σ.nextRegion ≤ rg := by simp only [σ_push, AState.pushBnd, σ_open, AState.openReg] at hge ⊢; omega
          simp [I_open, Interp.extend, hne, hIZero rg hge0]
        have hstOpen : StOk P ext b0 st_open := StOk_openRegion (StOk_mono (by omega) hst)
        have hrfOpen : RegsFuture st st_open := RegsFuture.openRegion st
        have hIokOpen : InterpOk σ_open st_open I_open := (InterpOk.openRegion hsim.2.2.1).1
        have hIokOpen0 : InterpOk σ st I_open :=
          ⟨fun rg hlt c hc => by rw [hIopenLt rg hlt] at hc; exact hsim.2.2.1.1 rg hlt c hc,
           fun c hc => by
             have hhdLt : σ.regions.headD 1 < s_a := by
               cases hrg : σ.regions with
               | nil => simp only [List.headD]; have := hok.2.2.1; change 1 < σ.nextRegion; omega
               | cons hd tl => simp only [List.headD]; exact (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2
             rw [hIopenLt _ hhdLt]; exact hsim.2.2.1.2 c hc⟩
        have hsimOpen : Sim P ext b0 st_open Frame NoKill NoSpend Scope env aenv σ_open I_open envFoot :=
          Sim_step (by omega) hleOpen hokOpen hIokOpen hrfOpen
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _)
            (Sim_interp_congr hIokOpen0 (fun rg hlt => (hIopenLt rg hlt).symm) hsim)
        have hsimPush : Sim P ext b0 st_open Frame NoKill NoSpend (shiftScope Scope)
            (⟨.imm .irr, .erased⟩ :: env) (ab :: aenv) σ_push I_open
            (fun i => match i with | 0 => fun _ => False | k + 1 => envFoot k) :=
          Sim_congr_scope_foot (fun i => by cases i <;> exact Iff.rfl) (fun i _ => by cases i <;> exact Iff.rfl)
            (Sim_push_erased hsimOpen)
        have henvTaintPush : EnvTaintOk (shiftScope Scope) (⟨.imm .irr, .erased⟩ :: env) (ab :: aenv) st_open I_open := by
          have ht0 := henvTaint.openRegion (fun i ab0 hsc0 hab0 hne0 r hr =>
            let hiE : i < env.length := by rw [hsim.1]; exact (List.getElem?_eq_some_iff.mp hab0).1
            ((hsim.2.2.2.2.2.1 i env[i] ab0 hsc0 (List.getElem?_eq_getElem hiE) hab0).2 hne0).2.1 r hr)
          intro i b' ab' hsc' hbi' habi' hne'
          cases i with
          | zero => simp at habi'; subst habi'; exact absurd rfl hne'
          | succ k => exact ht0 k b' ab' hsc' hbi' habi' hne'
        have henvNRFPush : EnvNoReachForbid st_open (shiftScope Scope)
            (⟨.imm .irr, .erased⟩ :: env) (ab :: aenv) σ_push Forbid BadReg' BadDep' := by
          intro i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps
          cases i with
          | zero => simp at habi'; subst habi'; exact absurd rfl hne'
          | succ k =>
            have hvK := ((hsim.2.2.2.2.2.1 k b' ab' hsc' hbi' habi').2 hne').2
            have ha0 := ActiveVal.of_AStateLe hok (hleOpen.trans hlePush) hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha'
            exact henvNRF k b' ab' hsc' hbi' habi' hne' ha0
              (fun rg hrg hbr => hregs rg hrg ⟨hvK.1 rg hrg, hbr⟩)
              (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvK.2.1 dep hdep) (hleOpen.trans hlePush).1, hbd⟩)
        have hRestArgList : ArgListOk P ext b0 st_open Frame NoKill NoSpend (shiftScope Scope)
            (⟨.imm .irr, .erased⟩ :: env) (ab :: aenv) σ_push I_open
            (fun i => match i with | 0 => fun _ => False | k + 1 => envFoot k)
            Forbid BadReg' BadDep'
            ((restC.zip rest).map fun ((v, _), (a1, er, _)) => if er then none else some (v, a1, fun _ => False)) := by
          have htail : ∀ (k : Nat) (opt : Option (Val × AVal × (Nat → Prop))),
              ((restC.zip rest).map fun ((v, _), (a1, er, _)) => if er then none else some (v, a1, fun (_ : Nat) => False))[k]? = some opt →
              (((a, true) :: restC).zip ((a0, true, fromCell) :: rest) |>.map
                fun ((v, _), (a1, er, _)) => if er then none else some (v, a1, fun (_ : Nat) => False))[k + 1]? = some opt :=
            fun _ _ h => h
          refine ⟨fun k v av ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
          · obtain ⟨hvK, hdisjK, hnrfK, hnvK⟩ := hArgList.1 (k + 1) v av ft (htail k _ hg)
            have hvK' : VSim P ext b0 st_open Frame NoKill NoSpend σ_push I_open ft av v :=
              VSim_step (by omega) hok (hleOpen.trans hlePush) hrfOpen
                (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _)
                (VSim_interp_congr (fun rg hrg => (hIopenLt rg (hvK.1 rg hrg)).symm) hvK)
            have hdisjK' : ValEnvDisj P st_open NoKill (shiftScope Scope) (⟨.imm .irr, .erased⟩ :: env) (ab :: aenv) σ_push
                (fun i => match i with | 0 => fun _ => False | k + 1 => envFoot k) ft av v := by
              intro idx b' ab' hsc' hbi' habi' hne'
              cases idx with
              | zero => simp at habi'; subst habi'; exact absurd rfl hne'
              | succ m =>
                have hleOP := hleOpen.trans hlePush
                have hvM := ((hsim.2.2.2.2.2.1 m b' ab' hsc' hbi' habi').2 hne').2
                have h0 := hdisjK m b' ab' hsc' hbi' habi' hne'
                refine ⟨fun haV htrV haB => h0.1 (ActiveVal.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haV)
                    (Transferable.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) (fun _ h => h) htrV)
                    (ActiveVal.of_AStateLe hok hleOP hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) haB),
                  fun haB htrB haV => h0.2.1 (ActiveVal.of_AStateLe hok hleOP hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) haB)
                    (Transferable.of_AStateLe hok hleOP hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) (fun _ h => h) htrB)
                    (ActiveVal.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haV),
                  fun haV hfV haB => h0.2.2.1 (ActiveVal.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haV)
                    (FootActive.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) hfV)
                    (ActiveVal.of_AStateLe hok hleOP hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) haB),
                  fun haB hfB haV => h0.2.2.2.1 (ActiveVal.of_AStateLe hok hleOP hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) haB)
                    (FootActive.of_AStateLe hok hleOP hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) hfB)
                    (ActiveVal.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haV),
                  fun haV hfV hs => h0.2.2.2.2.1 (ActiveVal.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haV)
                    (FootActive.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) hfV) hs,
                  h0.2.2.2.2.2.1,
                  fun haV hs => h0.2.2.2.2.2.2 (ActiveVal.of_AStateLe hok hleOP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haV) hs⟩
            have hnrfK' : ActiveVal σ_push av → NoReachForbid st_open Forbid BadReg' BadDep' av v := fun ha' hregs hdeps =>
              hnrfK (ActiveVal.of_AStateLe hok (hleOpen.trans hlePush) hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha')
                (fun rg hrg hbr => hregs rg hrg ⟨hvK.1 rg hrg, hbr⟩)
                (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvK.2.1 dep hdep) (hleOpen.trans hlePush).1, hbd⟩)
            have hnvK' : ValidDeps σ_push av.deps → av.cls ≠ .val → ValBaseOk st_open v ∧ NonValSafe st_open.heap v :=
              fun hvd' hne =>
                let ⟨hbv, hnv⟩ := hnvK (ValidDeps.of_AStateLe (hleOpen.trans hlePush) hvK.2.1 hvd') hne
                ⟨ValBaseOk_congr (st := st) (st' := st_open) (PreservesLocs.refl _ _) hrfOpen.1 hbv, hnv⟩
            exact ⟨hvK', hdisjK', hnrfK', hnvK'⟩
          · have hleOP := hleOpen.trans hlePush
            have hv₁ := (hArgList.1 (i + 1) v₁ av₁ ft₁ (htail i _ hg₁)).1
            have hv₂ := (hArgList.1 (j + 1) v₂ av₂ ft₂ (htail j _ hg₂)).1
            have h0 := hArgList.2 (i + 1) (j + 1) v₁ v₂ av₁ av₂ ft₁ ft₂ (by omega) (htail i _ hg₁) (htail j _ hg₂)
            exact ⟨fun ha₁ htr₁ ha₂ => h0.1 (ActiveVal.of_AStateLe hok hleOP hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) ha₁)
                (Transferable.of_AStateLe hok hleOP hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) (fun _ h => h) htr₁)
                (ActiveVal.of_AStateLe hok hleOP hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂),
              fun ha₁ hf₁ ha₂ => h0.2 (ActiveVal.of_AStateLe hok hleOP hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) ha₁)
                (FootActive.of_AStateLe hok hleOP hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) hf₁)
                (ActiveVal.of_AStateLe hok hleOP hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂)⟩
        have hHeadRegPush : st_open.regions.headD 0 = 0 ∨ st_open.regions.headD 0 ∈ I_open.reg (σ_push.regions.headD 1) := by
          right; dsimp only [st_open, σ_push, AState.pushBnd, σ_open, AState.openReg, List.headD]
          change s_c ∈ I_open.reg s_a; rw [hIopenSa]; exact List.mem_cons_self
        have hRestMeta : ∀ (idx : Nat) v er_c a1 er_a fc,
            restC[idx]? = some (v, er_c) → rest[idx]? = some (a1, er_a, fc) →
            er_c = er_a ∧ a1.src = none ∧
            (er_a = false → fc = true → a1.onceOnly = false ∧ a1.cls = .val ∧ a1.skel = .unknown ∧
              ValBaseOk st_open v ∧ CtorFieldsOk P ext b0 st_open v ∧ NoOnceCell st_open.heap v ∧
              FunOkAt P ext b0 st_open .unknown false (fun _ => False) v) := by
          intro idx v er_c a1 er_a fc hc ha
          obtain ⟨h1, h2, h3⟩ := hArgsMeta (idx + 1) v er_c a1 er_a fc hc ha
          refine ⟨h1, h2, fun herF hfc => ?_⟩
          obtain ⟨a_1, a_2, a_3, hbv, hcf, hno, hfun⟩ := h3 herF hfc
          exact ⟨a_1, a_2, a_3, ValBaseOk_congr (st := st) (st' := st_open) (PreservesLocs.refl _ _) hrfOpen.1 hbv,
            CtorFieldsOk_congr hbv.1 (PreservesLocs.refl _ _) hrfOpen (CtorFieldsOk_mono (by omega) hcf), hno,
            FunOkAt_preserve_locs (st₀ := st) (st₁ := st_open) (PreservesLocs.refl _ _) hrfOpen (FunOkAt_mono (by omega) hfun)⟩
        obtain ⟨hnoVA, hokA⟩ := haltIH hlcB hcfdB (B₀ := b0) (fuel := n) (by omega)
          (shiftScope_of_freeVarIn fun z hz => hfv z (.lam hz))
          hstOpen hsimPush hstat hFlt hnk₁ hnsp₁ hIopenZero hHeadRegPush henvTaintPush henvNRFPush
          hForbidLt hBadDep₁ (by simpa using hlen)
          (fun a_d er_d fc_d hm1 he1 hfc1 hnd1 a1 er1 fc1 hm2 he2 hcv2 =>
            hNonCons a_d er_d fc_d (List.mem_cons_of_mem _ hm1) he1 hfc1 hnd1 a1 er1 fc1 (List.mem_cons_of_mem _ hm2) he2 hcv2)
          hRestMeta hRestArgList
        rw [MS_bind_run]
        cases hevA : (applyAltS P ext n (⟨.imm .irr, .erased⟩ :: env) body restC).run (st_open, b0) with
        | error e =>
          refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
        | ok pa =>
          rcases pa with ⟨rv_b, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨rvFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
            hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, _, henvNRF₁,
            hvR₁, hdisjR₁, hnrfR₁, _, _, _, hsrcR₁⟩ := hokA rv_b st₁ B₁ hevA
          have hsaNe1 : s_a ≠ 1 := by have := hok.2.2.1; change σ.nextRegion ≠ 1; omega
          have hcurLt : cur < st₁.nextRegion := by
            have h1 : st_open.nextRegion = s_c + 1 := rfl
            cases hcr : st.regions with
            | nil => simp only [cur, hcr, List.headD]; omega
            | cons c0 cs =>
              simp only [cur, hcr, List.headD]
              have hc0 := (hst.2.1.2.2 c0 (hcr ▸ List.mem_cons_self)).2
              omega
          have hregClose : (σ₂.closeReg s_a).regions = σ.regions := by
            change σ₂.regions.filter (· != s_a) = σ.regions
            rw [hreg₂, hreg₁]; change (s_a :: σ.regions).filter (· != s_a) = σ.regions
            have hne : ∀ rg ∈ σ.regions, (rg != s_a) = true := fun rg hrg =>
              bne_iff_ne.mpr (Nat.ne_of_lt (hok.2.2.2.2.2 rg hrg).2)
            simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            exact List.filter_eq_self.mpr hne
          have hcurIn : cur = 0 ∨ cur ∈ I_open.reg ((σ₂.closeReg s_a).regions.headD 1) := by
            rw [hregClose]
            rcases hHeadReg with h0 | hIn
            · exact Or.inl h0
            · right
              have hhdLt : σ.regions.headD 1 < s_a := by
                cases hrg : σ.regions with
                | nil => simp only [List.headD]; have := hok.2.2.1; change 1 < σ.nextRegion; omega
                | cons hd tl => simp only [List.headD]; exact (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2
              rw [hIopenLt _ hhdLt]; exact hIn
          have hrgFilt1 : st₁.regions.filter (· != s_c) = st.regions := by
            rw [hr₁]; dsimp only [st_open]
            have hne : ∀ rg ∈ st.regions, (rg != s_c) = true := fun rg hrg =>
              bne_iff_ne.mpr (Nat.ne_of_lt (hst.2.1.2.2 rg hrg).2)
            simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            exact List.filter_eq_self.mpr hne
          have hIokClose0 : InterpOk (σ₂.closeReg s_a) { st₁ with regions := st₁.regions.filter (· != s_c) } I_open := by
            refine ⟨fun rg hlt c hc => hsim₁.2.2.1.1 rg (hnr₂ ▸ hlt) c hc, fun c hc => ?_⟩
            have hhdLt : σ.regions.headD 1 < s_a := by
              cases hrg : σ.regions with
              | nil => simp only [List.headD]; have := hok.2.2.1; change 1 < σ.nextRegion; omega
              | cons hd tl => simp only [List.headD]; exact (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2
            rw [hregClose, hIopenLt _ hhdLt]
            dsimp only at hc; rw [hrgFilt1] at hc; exact hsim.2.2.1.2 c hc
          have hregU₁ : RegUnique I_open σ₁ s_a s_c :=
            RegUnique_extend_of_zero hIZero hsim.2.2.1.1
          have hsIn₁ : s_c ∈ st₁.regions := by rw [hr₁]; exact List.mem_cons_self
          have hFlt₁ : ∀ l, Frame l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁
          have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
          rcases retCheck_altRetVal_bridge (fuel := n) (s_a := s_a) (s_c := s_c) (cur := cur)
              hst₁ hsim₁ henvNRF₁ hFlt₁ hForbLt₁ hnk₂ hBadDep₂ hNotBadS hsaNe1 hcurLt hcurIn
              hIokClose0 hregU₁ hsIn₁ hvR₁ hdisjR₁ hnrfR₁ hretChk with hStR | hOOFR |
            ⟨rv', st_ret, hrunR, hrgR, hnrR, hstatR, hstrR, hszR, hcapR,
             hpFrameR, hpSSR, honceR, hssfR, hstClose, hsimClose, henvNRFClose,
             hvClose, hdisjClose, hnrfClose⟩
          · rw [MS_bind_run, MS_liftM_run, hStR]
            exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [MS_bind_run, MS_liftM_run, hOOFR]
            exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [MS_bind_run, MS_liftM_run, hrunR]; dsimp only
            let st_close : St := { st_ret with regions := st_ret.regions.filter (· != s_c) }
            have hcloseRun : (closeRegion s_c).run st_ret = .ok ((), st_close) := rfl
            rw [MS_bind_run, MS_liftM_run, hcloseRun]; dsimp only
            rw [MS_pure_run]
            refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
            cases hokEq
            have hrgCloseC : st_close.regions = st.regions := by
              dsimp only [st_close]; rw [hrgR, hrgFilt1]
            obtain ⟨hpEnvR, hpNumR⟩ := ret_preserves_env_num hst₁ hsim₁ hnk₂ hregU₁ hsIn₁ hvR₁ hdisjR₁ hretChk hrunR
            have hIokCloseI : InterpOk (σ₂.closeReg s_a) st_close I := by
              refine ⟨fun rg hlt c hc => ?_, fun c hc => ?_⟩
              · by_cases hltSa : rg < s_a
                · rw [← hIopenLt rg hltSa] at hc; exact hsimClose.2.2.1.1 rg hlt c hc
                · rw [hIZero rg (Nat.le_of_not_lt hltSa)] at hc; cases hc
              · rw [hregClose]; rw [hrgCloseC] at hc; exact hsim.2.2.1.2 c hc
            have hsimPopOpen : Sim P ext B₁ st_close Frame NoKill NoSpend Scope env aenv (σ₂.closeReg s_a) I_open envFoot := by
              obtain ⟨hlenC, hokC, hIokC, hidsC, huniqC, hbndsC, hdisjC⟩ := hsimClose
              refine ⟨by simpa using hlenC, hokC, hIokC,
                fun i ab' hab' => hidsC (i + 1) ab' hab',
                fun i j ab₁ ab₂ h1 h2 hid => Nat.succ.inj (huniqC (i + 1) (j + 1) ab₁ ab₂ h1 h2 hid),
                fun i b' ab' hsc' hbi' habi' => hbndsC (i + 1) b' ab' hsc' hbi' habi',
                fun i j b₁ b₂ ab₁ ab₂ hij hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂ =>
                  hdisjC (i + 1) (j + 1) b₁ b₂ ab₁ ab₂ (by omega) hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂⟩
            have hsimFinal : Sim P ext B₁ st_close Frame NoKill NoSpend Scope env aenv (σ₂.closeReg s_a) I envFoot :=
              Sim_interp_congr_ne (s_a := s_a) hIokCloseI (fun rg hne => by simp [I_open, Interp.extend, hne])
                (fun i ab' hsc' hab' hne' hmem => by
                  have hiE : i < env.length := by rw [hsim.1]; exact (List.getElem?_eq_some_iff.mp hab').1
                  exact Nat.lt_irrefl _ (((hsim.2.2.2.2.2.1 i env[i] ab' hsc' (List.getElem?_eq_getElem hiE) hab').2 hne').2.1 s_a hmem))
                hsimPopOpen
            let arv := altRetVal res rc s_a ((σ₂.closeReg s_a).regions.headD 1) r
            have harvNotSa : s_a ∉ arv.regs := by
              intro hmem; dsimp only [arv, altRetVal] at hmem
              by_cases hnv : (rc == .irr || rc == .imm || rc == .leaf) = true
              · simp only [hnv, ↓reduceIte] at hmem; cases hmem
              · simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases hb : (res.isBorrowed && r.regs.contains s_a) = true
                · simp only [hb, ↓reduceIte, mem_natUnion, List.mem_filter, List.mem_singleton] at hmem
                  rcases hmem with ⟨_, hne⟩ | hEq
                  · simp at hne
                  · rw [hregClose] at hEq
                    cases hrg : σ.regions with
                    | nil => rw [hrg] at hEq; simp only [List.headD] at hEq; have := hok.2.2.1; change σ.nextRegion = 1 at hEq; omega
                    | cons hd tl =>
                      rw [hrg] at hEq; simp only [List.headD] at hEq
                      exact Nat.lt_irrefl _ (hEq ▸ (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2)
                · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hmem; simp at hmem
            have hvFinal : VSim P ext B₁ st_close Frame NoKill NoSpend (σ₂.closeReg s_a) I (fun _ => False) arv rv' :=
              VSim_interp_congr (fun rg hrg => by
                have hne : rg ≠ s_a := fun hEq => harvNotSa (hEq ▸ hrg)
                simp [I_open, Interp.extend, hne]) hvClose
            have hdisjFinal : ValEnvDisj P st_close NoKill Scope env aenv (σ₂.closeReg s_a) envFoot (fun _ => False) arv rv' :=
              fun i b' ab' hsc' hbi' habi' hne' => hdisjClose (i + 1) b' ab' hsc' hbi' habi' hne'
            have henvNRFFinal : EnvNoReachForbid st_close Scope env aenv (σ₂.closeReg s_a) Forbid BadReg BadDep :=
              fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
                henvNRFClose (i + 1) b' ab' hsc' hbi' habi' hne' ha'
                  (fun rg hrg hbr => hregs rg hrg hbr.2) (fun dep hdep hbd => hdeps dep hdep hbd.2)
            have hnrfFinal : ActiveVal (σ₂.closeReg s_a) arv → NoReachForbid st_close Forbid BadReg BadDep arv rv' :=
              fun ha' hregs hdeps => hnrfClose ha'
                (fun rg hrg hbr => hregs rg hrg hbr.2) (fun dep hdep hbd => hdeps dep hdep hbd.2)
            have hpresEnvAll : PreservesActiveEnv Scope env aenv (σ₂.closeReg s_a) st.heap st_close.heap := by
              intro i b' ab' hsc' hbi' habi' hne' haEnd
              have hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
              have hleOP := hleOpen.trans hlePush
              have ha₁ := ActiveVal.of_AStateLe hok₁ (hle₂.trans hleClose)
                (fun d hd => Nat.lt_of_lt_of_le (hvI.2.1 d hd) (hleOP.trans hle₁).1)
                (fun z hz => Nat.lt_of_lt_of_le (hvI.2.2.1 z hz).1 (hleOP.trans hle₁).1) haEnd
              have hp1 := hpEnv₁ (i + 1) b' ab' hsc' hbi' habi' hne' ha₁
              have hp2 := hpEnvR (i + 1) b' ab' hsc' hbi' habi' hne' haEnd
              exact hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
            have harvNotOnce : ¬ IsOnceSrc (σ₂.closeReg s_a) arv := by
              rintro ⟨id, hsrc, ho⟩
              dsimp only [arv, altRetVal] at hsrc
              by_cases hu : (res.isUnique && rc == .val) = true
              · simp only [hu, ↓reduceIte] at hsrc; cases hsrc
              · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hsrc
                exact hnotOnceR₁ ⟨id, hsrc, honce₂ ▸ ho⟩
            have harvAct : ActiveVal (σ₂.closeReg s_a) arv := by
              refine ⟨?_, fun his => absurd his harvNotOnce⟩
              dsimp only [arv, altRetVal]
              by_cases hu : (res.isUnique && rc == .val) = true
              · simp only [hu, ↓reduceIte]; exact fun _ h => by cases h
              · simp only [hu, Bool.false_eq_true, ↓reduceIte]
                intro d hd
                refine ⟨hstSz₂ ▸ (hvdR₁ d hd).1, fun hdead => ?_⟩
                have hstUpd := (Runs_retCheck hok₁ hretChk).2.2.2.2.2.2.2.2.2.2.2.2 d (hvdR₁ d hd).1
                have hcondF : ¬ (rc = .val ∧ res.isUnique = true ∧ d ∈ r.deps) := by
                  rintro ⟨rfl, hru, _⟩
                  exact hu (by simp [hru, show (Cls.val == Cls.val) = true from rfl])
                simp only [hcondF, ↓reduceIte] at hstUpd
                exact (hvdR₁ d hd).2 (hstUpd ▸ hdead)
            have hsrcFinal : SrcOk Scope aenv σ (σ₂.closeReg s_a) arv := by
              intro id hrs
              dsimp only [arv, altRetVal] at hrs
              by_cases hu : (res.isUnique && rc == .val) = true
              · simp only [hu, ↓reduceIte] at hrs; cases hrs
              · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hrs
                have harvDeps : arv.deps = r.deps := by dsimp only [arv, altRetVal]; simp [hu]
                rcases hsrcR₁ id hrs with ⟨i, ab', hsc', hab', hne', hid', hoo', hdeps'⟩ | ⟨hgeP, hspP⟩
                · cases i with
                  | zero => simp at hab'; subst hab'; exact absurd rfl hne'
                  | succ k => exact Or.inl ⟨k, ab', hsc', hab', hne', hid', hoo', fun d => by rw [harvDeps]; exact hdeps' d⟩
                · right
                  have hle0P : σ.st.size ≤ σ_push.st.size := (hleOpen.trans hlePush).1
                  refine ⟨Nat.le_trans hle0P hgeP, fun hoId dep hdep hlt0 hoDep => ?_⟩
                  change σ₂.spent[dep]? = some true
                  rw [hsp₂]
                  exact hspP (honce₂ ▸ hoId) dep (harvDeps ▸ hdep) (Nat.lt_of_lt_of_le hlt0 hle0P) (honce₂ ▸ hoDep)
            have hnvFinal : ValidDeps (σ₂.closeReg s_a) arv.deps → arv.cls ≠ .val →
                ValBaseOk st_close rv' ∧ NonValSafe st_close.heap rv' := fun _ hne =>
              ⟨(hvFinal.2.2.2.2 harvAct).1, (hvFinal.2.2.2.2 harvAct).2.2.2.1 harvNotOnce hne⟩
            have htaintFinal : ValidDeps (σ₂.closeReg s_a) arv.deps →
                (∀ c ∈ rv'.taint, c < st_close.nextRegion) ∧ OpenUnder st_close.regions (I.regsOf arv.regs) rv' := fun _ =>
              let hvA := hvFinal.2.2.2.2 harvAct
              ⟨fun c hc => hvA.1.2.2.2 rv' (HeldBy.refl _ _) c hc, hvA.2.1 rv' (HeldBy.refl _ _)⟩
            exact ⟨fun _ => False, by omega, hstClose,
              Nat.le_trans hsz₁ hszR, Nat.le_trans hcap₁ hcapR,
              hrgCloseC, by have : st_open.nextRegion = s_c + 1 := rfl; have : st_close.nextRegion = st_ret.nextRegion := rfl; omega,
              hstatR ▸ hstat₁, hstrR ▸ hstr₁,
              hpFrame₁.trans hpFrameR, hpresEnvAll,
              fun l o num ho hc => hpNumR l o num (hpNum₁ l o num ho hc) hc,
              honce₁.trans honceR,
              StaticStrFresh.trans hsz₁ hpSSR hssf₁ hssfR,
              hsimFinal, henvTaint.step hrgCloseC (by have : st_open.nextRegion = s_c + 1 := rfl; have : st_close.nextRegion = st_ret.nextRegion := rfl; omega),
              henvNRFFinal, hvFinal, hdisjFinal, hnrfFinal, hnvFinal, htaintFinal,
              Or.inl ⟨(hvFinal.2.2.2.2 harvAct).1, (hvFinal.2.2.2.2 harvAct).2.2.1⟩, hsrcFinal⟩

/-- Soundness for `AAlt.lamKept` (open region, optional `caseField_fromCell_clear`,
`Sim_extend_frame_of_args` + `bindInner_bridge`, lift remaining case-field args,
recurse on `rest`, and close via `retCheck_altRetVal_bridge`). -/
theorem evalS_alt_lamKept {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {body : Term}
    {a0 bv r : AVal} {fromCell : Bool} {rest : List (AVal × Bool × Bool)}
    {σ σ₁ σ₂ σ₃ : AState}
    (hadm : p.skel.admits (if fromCell && p.cls != .val then { a0 with deps := [], regs := [] } else a0).skel = true)
    (hbind : Runs (bindInner p.mode p.cls
      (if fromCell && p.cls != .val then { a0 with deps := [], regs := [] } else a0)
      σ.openReg.1 "a case field's binder") σ.openReg.2 bv σ₁)
    (haltD : AAlt P ({ id := σ₁.st.size, mode := p.mode, val := bv } :: aenv)
      body rest (σ₁.pushBnd bv (p.mode.usage == .once)).2 r σ₂)
    (haltIH : AAltProp P ext B ({ id := σ₁.st.size, mode := p.mode, val := bv } :: aenv)
      body rest (σ₁.pushBnd bv (p.mode.usage == .once)).2 r σ₂)
    (hretChk : Runs (retCheck r.skel res σ.openReg.1 { r with cls := rc } "a case alternative") σ₂ () σ₃) :
    AAltProp P ext B aenv (.lam p res rc fvs body) ((a0, false, fromCell) :: rest) σ
      (altRetVal res rc σ.openReg.1 ((σ₃.closeReg σ.openReg.1).regions.headD 1) r)
      (σ₃.closeReg σ.openReg.1) := by
  classical
  have _ := hadm
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep cargs
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    hlen hNonCons hArgsMeta hArgList
  cases hlc with | lam hlcB _ =>
  cases hcfd with | lam hcfdB =>
  cases cargs with
  | nil => simp at hlen
  | cons hdC restC =>
    rcases hdC with ⟨a, er_c⟩
    obtain ⟨hErFalse, ha0Src, ha0FcMeta⟩ := hArgsMeta 0 a er_c a0 false fromCell rfl rfl
    subst hErFalse
    cases fuel with
    | zero =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ b0 => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_succ]; rfl)
    | succ n =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ b0 =>
        have hok := hsim.2.1
        let s_a := σ.openReg.1
        let σ_open := σ.openReg.2
        have hokOpen : AStateOk σ_open := (AStateOk.openReg hok).1
        have hleOpen : AStateLe σ σ_open := AStateLe_openReg σ
        let a0' : AVal := if fromCell && p.cls != .val then { a0 with deps := [], regs := [] } else a0
        have hbind' : Runs (bindInner p.mode p.cls a0' s_a "a case field's binder") σ_open bv σ₁ := hbind
        obtain ⟨hok₁, hle₁, hszSt₁, hσonce₁, hszSp₁, hσreg₁, hσnr₁, hnotOnce₁, hvdA₁, huniq₁, hunsp₁, hspUpd₁, hstUpd₁, hbvEq₁⟩ :=
          Runs_bindInner hokOpen hbind'
        change σ₁.st.size = σ.st.size at hszSt₁
        change σ₁.once = σ.once at hσonce₁
        change σ₁.regions = s_a :: σ.regions at hσreg₁
        let ab : ABnd := { id := σ₁.st.size, mode := p.mode, val := bv }
        let σ_push := (σ₁.pushBnd bv (p.mode.usage == .once)).2
        have hokPush : AStateOk σ_push := (hok₁.pushBnd bv _).1
        have hlePush : AStateLe σ₁ σ_push := (hok₁.pushBnd bv _).2
        obtain ⟨hok₂, hle₂, hreg₂⟩ := AAlt_state_le hokPush haltD
        obtain ⟨hok₃, hle₃, hstSz₃, hσonce₃, hσsp₃, hσreg₃, hσnr₃, hvdR₂, _, hooR₂, hnotOnceR₂, _, _⟩ :=
          Runs_retCheck hok₂ hretChk
        have hleClose : AStateLe σ₃ (σ₃.closeReg s_a) := AStateLe_closeReg s_a σ₃
        have hnk₃ : NoKillOk NoKill σ₃ := NoKillOk_of_AStateLe hleClose hnkEnd
        have hnk₂ : NoKillOk NoKill σ₂ := NoKillOk_of_AStateLe hle₃ hnk₃
        have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe (hlePush.trans hle₂) hnk₂
        have hnsp₃ : NoSpendOk NoSpend σ₃ := NoSpendOk_of_AStateLe hleClose hnspEnd
        have hnsp₂ : NoSpendOk NoSpend σ₂ := NoSpendOk_of_AStateLe hle₃ hnsp₃
        have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe (hlePush.trans hle₂) hnsp₂
        let BadReg' : Nat → Prop := fun rg => rg < σ.nextRegion ∧ BadReg rg
        let BadDep₁ : Nat → Prop := fun dep => dep < σ.st.size ∧ BadDep dep
        let BadDepP : Nat → Prop := fun dep => dep < σ_push.st.size ∧ BadDep dep
        have hBadDep₃ : ∀ dep, BadDep dep → σ₃.st[dep]? = some .live := fun dep hbd => hBadDepEnd dep hbd
        have hBadDepP₃ : ∀ dep, BadDepP dep → σ₃.st[dep]? = some .live := fun dep hbd => hBadDep₃ dep hbd.2
        have hBadDepP₂ : ∀ dep, BadDepP dep → σ₂.st[dep]? = some .live :=
          BadDepLive_of_AStateLe hle₃ hBadDepP₃ (fun dep hbd => Nat.lt_of_lt_of_le hbd.1 hle₂.1)
        have hBadDep₁ : ∀ dep, BadDep₁ dep → σ₁.st[dep]? = some .live :=
          BadDepLive_of_AStateLe (hlePush.trans (hle₂.trans hle₃))
            (fun dep hbd => hBadDep₃ dep hbd.2) (fun dep hbd => hszSt₁ ▸ hbd.1)
        have hNotBadS : ¬ BadReg' s_a := fun h => Nat.lt_irrefl _ h.1
        have hstep : (applyAltS P ext (n + 1) env (.lam p res rc fvs body) ((a, false) :: restC)).run (st, b0 + 1) =
            (do
              let (s, cur) ← liftM openRegion
              let bnd ← liftM (bindAt P n s p.mode p.cls a)
              let r ← applyAltS P ext n (bnd :: env) body restC
              let r ← liftM (ret P n s cur res rc r)
              liftM (closeRegion s)
              pure r).run (st, b0) := by
          conv => lhs; unfold applyAltS
          rw [MS_bind_run, MS_spend_succ]; dsimp only
          simp only [Bool.false_eq_true, ↓reduceIte]
        unfold TermPost; rw [hstep]
        let s_c := st.nextRegion
        let cur := st.regions.headD 0
        let st_open : St := { st with nextRegion := s_c + 1, regions := s_c :: st.regions }
        have hopenRun : openRegion.run st = .ok ((s_c, cur), st_open) := rfl
        rw [MS_bind_run, MS_liftM_run, hopenRun]; dsimp only
        let I_open : Interp := I.extend s_a s_c
        have hIopenLt : ∀ rg, rg < s_a → I_open.reg rg = I.reg rg := fun rg hlt => by
          simp [I_open, Interp.extend, Nat.ne_of_lt hlt]
        have hIopenSa : I_open.reg s_a = [s_c] := by simp [I_open, Interp.extend]
        have hIopenZero : ∀ rg, σ_push.nextRegion ≤ rg → I_open.reg rg = [] := fun rg hge => by
          have hne : rg ≠ s_a := by simp only [σ_push, AState.pushBnd, hσnr₁, σ_open, s_a, AState.openReg] at hge ⊢; omega
          have hge0 : σ.nextRegion ≤ rg := by simp only [σ_push, AState.pushBnd, hσnr₁, σ_open, AState.openReg] at hge ⊢; omega
          simp [I_open, Interp.extend, hne, hIZero rg hge0]
        have hstOpen : StOk P ext b0 st_open := StOk_openRegion (StOk_mono (by omega) hst)
        have hrfOpen : RegsFuture st st_open := RegsFuture.openRegion st
        have hIokOpen : InterpOk σ_open st_open I_open := (InterpOk.openRegion hsim.2.2.1).1
        have hIokOpen0 : InterpOk σ st I_open :=
          ⟨fun rg hlt c hc => by rw [hIopenLt rg hlt] at hc; exact hsim.2.2.1.1 rg hlt c hc,
           fun c hc => by
             have hhdLt : σ.regions.headD 1 < s_a := by
               cases hrg : σ.regions with
               | nil => simp only [List.headD]; have := hok.2.2.1; change 1 < σ.nextRegion; omega
               | cons hd tl => simp only [List.headD]; exact (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2
             rw [hIopenLt _ hhdLt]; exact hsim.2.2.1.2 c hc⟩
        have hsimOpen0 : Sim P ext b0 st_open Frame NoKill NoSpend Scope env aenv σ_open I_open envFoot :=
          Sim_step (by omega) hleOpen hokOpen hIokOpen hrfOpen
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _)
            (Sim_interp_congr hIokOpen0 (fun rg hlt => (hIopenLt rg hlt).symm) hsim)
        have henvNRFOpen0 : EnvNoReachForbid st_open Scope env aenv σ_open Forbid BadReg' BadDep₁ := by
          intro i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps
          have hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
          have ha0 := ActiveVal.of_AStateLe hok hleOpen hvI.2.1 (fun z hz => (hvI.2.2.1 z hz).1) ha'
          exact henvNRF i b' ab' hsc' hbi' habi' hne' ha0
            (fun rg hrg hbr => hregs rg hrg ⟨hvI.1 rg hrg, hbr⟩)
            (fun dep hdep hbd => hdeps dep hdep ⟨hvI.2.1 dep hdep, hbd⟩)
        have henvTaintOpen : EnvTaintOk Scope env aenv st_open I_open :=
          henvTaint.openRegion (fun i ab0 hsc0 hab0 hne0 r hr =>
            let hiE : i < env.length := by rw [hsim.1]; exact (List.getElem?_eq_some_iff.mp hab0).1
            ((hsim.2.2.2.2.2.1 i env[i] ab0 hsc0 (List.getElem?_eq_getElem hiE) hab0).2 hne0).2.1 r hr)
        -- Lift full `argList` to `(st_open, σ_open, I_open, BadReg', BadDep₁)`
        let fullArgList : List (Option (Val × AVal × (Nat → Prop))) :=
          (((a, false) :: restC).zip ((a0, false, fromCell) :: rest)).map
            fun ((v, _), (a1, er, _)) => if er then none else some (v, a1, fun (_ : Nat) => False)
        let restArgList : List (Option (Val × AVal × (Nat → Prop))) :=
          (restC.zip rest).map
            fun ((v, _), (a1, er, _)) => if er then none else some (v, a1, fun (_ : Nat) => False)
        have hFullEq : fullArgList = some (a, a0, fun (_ : Nat) => False) :: restArgList := rfl
        have hArgListOpen : ArgListOk P ext b0 st_open Frame NoKill NoSpend Scope env aenv σ_open I_open envFoot
            Forbid BadReg' BadDep₁ fullArgList := by
          refine ⟨fun k v av ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
          · obtain ⟨hvK, hdisjK, hnrfK, hnvK⟩ := hArgList.1 k v av ft hg
            refine ⟨VSim_step (by omega) hok hleOpen hrfOpen (PreservesOnceShell.refl _) (StaticStrFresh.refl _)
                (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _)
                (VSim_interp_congr (fun rg hrg => (hIopenLt rg (hvK.1 rg hrg)).symm) hvK),
              hdisjK,
              fun ha' hregs hdeps => hnrfK ha'
                (fun rg hrg hbr => hregs rg hrg ⟨hvK.1 rg hrg, hbr⟩)
                (fun dep hdep hbd => hdeps dep hdep ⟨hvK.2.1 dep hdep, hbd⟩),
              fun hvd' hne =>
                let ⟨hbv, hnv⟩ := hnvK hvd' hne
                ⟨ValBaseOk_congr (st := st) (st' := st_open) (PreservesLocs.refl _ _) hrfOpen.1 hbv, hnv⟩⟩
          · exact hArgList.2 i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂
        -- Frame active tail arguments (`k > 0`) across `bindAt`
        obtain ⟨hstatF', hFlt', hnk₁', hnsp₁', hsimOpen'⟩ :=
          Sim_extend_frame_of_args (Pick := fun k => 0 < k) hle₁ hsimOpen0 hstOpen hFlt hnk₁ hnsp₁ hArgListOpen
        let Frame' : Nat → Prop := fun l =>
          Frame l ∨ StaticStrLoc st_open l ∨
          ∃ k v av ft, 0 < k ∧ fullArgList[k]? = some (some (v, av, ft)) ∧ ActiveVal σ₁ av ∧ Reach st_open.heap v l
        let NoKill' : Nat → Prop := fun d =>
          d < σ_open.st.size ∧ (NoKill d ∨
            ∃ k v av ft, 0 < k ∧ fullArgList[k]? = some (some (v, av, ft)) ∧ ActiveVal σ₁ av ∧ d ∈ av.deps)
        let NoSpend' : Nat → Prop := fun d =>
          d < σ_open.st.size ∧ (NoSpend d ∨
            ∃ k v av ft, 0 < k ∧ fullArgList[k]? = some (some (v, av, ft)) ∧ ActiveVal σ₁ av ∧
              IsOnceSrc σ₁ av ∧ av.src = some d ∧ σ_open.once[d]? = some true)
        -- Helper: upgrade `(a, a0)`'s `VSim` and `ValEnvDisj` to `Frame', NoKill', NoSpend'`
        obtain ⟨hvA0, hdisjA0, hnrfA0, hnvA0⟩ := hArgListOpen.1 0 a a0 (fun (_ : Nat) => False) (by rw [hFullEq]; rfl)
        have hvA_F' : VSim P ext b0 st_open Frame' NoKill' NoSpend' σ_open I_open (fun (_ : Nat) => False) a0 a := by
          refine ⟨hvA0.1, hvA0.2.1, hvA0.2.2.1, hvA0.2.2.2.1, fun ha => ?_⟩
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hvA0.2.2.2.2 ha
          refine ⟨b1, b2, b3, b4, b5,
            (fun hoo => let ⟨q1, _, q3, q4⟩ := b6 hoo; ⟨q1, (fun _ _ h => False.elim h), q3, q4⟩),
            (fun his => let ⟨q1, _, q3⟩ := b7 his; ⟨q1, (fun _ _ h => False.elim h), q3⟩),
            fun htr' => ?_⟩
          have htr0 : Transferable σ_open NoKill a0 :=
            ⟨htr'.1, htr'.2.1, htr'.2.2.1, htr'.2.2.2.1, fun d hd =>
              ⟨(htr'.2.2.2.2 d hd).1, fun hnk => (htr'.2.2.2.2 d hd).2 ⟨hvA0.2.1 d hd, Or.inl hnk⟩⟩⟩
          obtain ⟨hotf, hdisj0⟩ := b8 htr0
          refine ⟨hotf, fun l hor => ⟨fun hFr => ?_, (hdisj0 l hor).2⟩⟩
          rcases hFr with hF | hss | ⟨k, vk, avk, ftk, hpos, hgk, haK₁, hrk⟩
          · exact (hdisj0 l hor).1 hF
          · exact (hdisj0 l hor).2 hss
          · have hvK := (hArgListOpen.1 k vk avk ftk hgk).1
            have haK0 := ActiveVal.of_AStateLe hokOpen hle₁ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haK₁
            have hdd : ∀ d ∈ a0.deps, ¬ (d ∈ avk.deps) := fun d hd hdk =>
              (htr'.2.2.2.2 d hd).2 ⟨hvA0.2.1 d hd, Or.inr ⟨k, vk, avk, ftk, hpos, hgk, haK₁, hdk⟩⟩
            exact (hArgListOpen.2 0 k a vk a0 avk (fun (_ : Nat) => False) ftk (by omega)
              (by rw [hFullEq]; rfl) hgk).1 ha htr0 haK0 hdd l hor hrk
        have hdisjA_F' : ValEnvDisj P st_open NoKill' Scope env aenv σ_open envFoot (fun (_ : Nat) => False) a0 a := by
          intro i b' ab' hsc' hbi' habi' hne'
          have h0 := hdisjA0 i b' ab' hsc' hbi' habi' hne'
          have hvI := ((hsimOpen0.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
          refine ⟨fun haV htrV => h0.1 haV ⟨htrV.1, htrV.2.1, htrV.2.2.1, htrV.2.2.2.1, fun d hd =>
              ⟨(htrV.2.2.2.2 d hd).1, fun hnk => (htrV.2.2.2.2 d hd).2 ⟨hvA0.2.1 d hd, Or.inl hnk⟩⟩⟩,
            fun haB htrB => h0.2.1 haB ⟨htrB.1, htrB.2.1, htrB.2.2.1, htrB.2.2.2.1, fun d hd =>
              ⟨(htrB.2.2.2.2 d hd).1, fun hnk => (htrB.2.2.2.2 d hd).2 ⟨hvI.2.1 d hd, Or.inl hnk⟩⟩⟩,
            h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2.1, h0.2.2.2.2.2.2⟩
        -- Prepare unified pre-`bindAt` state `(a_in, st_in)` (either direct or via `caseField_fromCell_clear`)
        have hPrep :
            (bindAt P n s_c p.mode p.cls a).run st_open = .error .stuck ∨
            ∃ a_in st_in,
              (bindAt P n s_c p.mode p.cls a).run st_open = (bindAt P n s_c p.mode p.cls a_in).run st_in ∧
              st_in.regions = st_open.regions ∧ st_in.nextRegion = st_open.nextRegion ∧
              st_in.statics = st_open.statics ∧ st_in.strs = st_open.strs ∧
              st_open.heap.objs.size ≤ st_in.heap.objs.size ∧ st_open.heap.nextCap ≤ st_in.heap.nextCap ∧
              PreservesLocs (fun l => l < st_open.heap.objs.size) st_open.heap st_in.heap ∧
              PreservesOnceShell st_open.heap st_in.heap ∧ StaticStrFresh st_open st_in ∧
              StOk P ext b0 st_in ∧
              Sim P ext b0 st_in Frame' NoKill' NoSpend' Scope env aenv σ_open I_open envFoot ∧
              EnvNoReachForbid st_in Scope env aenv σ_open Forbid BadReg' BadDep₁ ∧
              VSim P ext b0 st_in Frame' NoKill' NoSpend' σ_open I_open (fun (_ : Nat) => False) a0' a_in ∧
              ValEnvDisj P st_in NoKill' Scope env aenv σ_open envFoot (fun (_ : Nat) => False) a0' a_in ∧
              (ActiveVal σ_open a0' → NoReachForbid st_in Forbid BadReg' BadDep₁ a0' a_in) ∧
              ((fromCell && p.cls != .val) = true → p.mode ≠ .erased → p.cls ≠ .val) ∧
              ((fromCell && p.cls != .val) = false → a_in = a ∧ st_in = st_open) := by
          by_cases hclr : (fromCell && p.cls != .val) = true
          · obtain ⟨hfcT, hpNeB⟩ := Bool.and_eq_true_iff.mp hclr
            have hpNe : p.cls ≠ .val := fun hEq => by rw [hEq] at hpNeB; cases hpNeB
            by_cases hpEr : p.mode = .erased
            · right
              have ha0'Def : a0' = { a0 with deps := [], regs := [] } := by simp [a0', hclr]
              have hbindEr : (bindAt P n s_c p.mode p.cls a).run st_open =
                  (bindAt P n s_c p.mode p.cls (.imm .irr)).run st_open := by
                rw [hpEr]; unfold bindAt; rfl
              refine ⟨.imm .irr, st_open, hbindEr, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
                PreservesLocs.refl _ _, PreservesOnceShell.refl _, StaticStrFresh.refl _,
                hstOpen, hsimOpen', henvNRFOpen0,
                VSim_imm_irr (by rw [ha0'Def]; intro _ h; cases h) (by rw [ha0'Def]; intro _ h; cases h)
                  (fun _ hs => by rw [ha0'Def] at hs; change a0.src = some _ at hs; rw [ha0Src] at hs; cases hs),
                ValEnvDisj_imm_irr (by rw [ha0'Def]; exact ha0Src),
                fun _ => NoReachForbid_imm_irr st_open Forbid BadReg' BadDep₁ a0',
                fun _ hne => absurd hpEr hne, fun hf => by rw [hclr] at hf; cases hf⟩
            · obtain ⟨_, _, hsk0, hbv0, hcf0, hno0, hfun0⟩ := ha0FcMeta rfl hfcT
              have hbvO : ValBaseOk st_open a := ValBaseOk_congr (st := st) (st' := st_open) (PreservesLocs.refl _ _) hrfOpen.1 hbv0
              have hcfO : CtorFieldsOk P ext b0 st_open a :=
                CtorFieldsOk_congr hbv0.1 (PreservesLocs.refl _ _) hrfOpen (CtorFieldsOk_mono (by omega) hcf0)
              have hfunO : FunOkAt P ext b0 st_open a0.skel false (fun (_ : Nat) => False) a :=
                hsk0 ▸ FunOkAt_preserve_locs (st₀ := st) (st₁ := st_open) (PreservesLocs.refl _ _) hrfOpen (FunOkAt_mono (by omega) hfun0)
              rcases caseField_fromCell_clear (fuel := n) (s_c := s_c) hpEr hpNe ha0Src hstOpen hsimOpen' henvNRFOpen0
                  hbvO hcfO hno0 hfunO with hStC |
                ⟨a1, st_c, hbindEq, hrgC, hnrC, hstatC, hstrC, hszC, hcapC, hpresC, honceC, hssfC,
                 hstC, hsimC, henvNRFC, hvC, hdisjC, hnrfC⟩
              · exact Or.inl hStC
              · right
                have ha0'Def : a0' = { a0 with deps := [], regs := [] } := by simp [a0', hclr]
                rw [ha0'Def]
                exact ⟨a1, st_c, hbindEq, hrgC, hnrC, hstatC, hstrC, hszC, hcapC, hpresC, honceC, hssfC,
                  hstC, hsimC, henvNRFC, hvC, hdisjC, fun _ => hnrfC,
                  fun _ _ => hpNe, fun hf => by rw [hclr] at hf; cases hf⟩
          · have hclrF : (fromCell && p.cls != .val) = false := Bool.eq_false_iff.mpr hclr
            have ha0'Def : a0' = a0 := by simp [a0', hclrF]
            right; rw [ha0'Def]
            exact ⟨a, st_open, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
              PreservesLocs.refl _ _, PreservesOnceShell.refl _, StaticStrFresh.refl _,
              hstOpen, hsimOpen', henvNRFOpen0, hvA_F', hdisjA_F', hnrfA0,
              (fun ht _ => by rw [hclrF] at ht; cases ht), fun _ => ⟨rfl, rfl⟩⟩
        rcases hPrep with hStP | ⟨a_in, st_in, hbindEqIn, hrgIn, hnrIn, hstatIn, hstrIn, hszIn, hcapIn,
            hpresIn, honceIn, hssfIn, hstIn, hsimIn, henvNRFIn, hvIn, hdisjIn, hnrfIn, hclrClsNe, hnoClrEq⟩
        · rw [MS_bind_run, MS_liftM_run, hStP]
          exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [MS_bind_run, MS_liftM_run, hbindEqIn]
          have hFltIn : ∀ l, Frame' l → l < st_in.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hFlt' l hF) hszIn
          have hForbLtIn : ∀ l, Forbid l → l < st_in.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hszIn
          rcases bindInner_bridge (fuel := n) (s_a := s_a) (s_c := s_c)
              hstIn (by simp [s_a, σ_open, AState.openReg]) (by rw [hnrIn]; exact Nat.lt_succ_self s_c)
              (by rw [hIopenSa]; exact List.mem_cons_self) hFltIn hForbLtIn hnk₁' hnsp₁' hBadDep₁
              hsimIn henvNRFIn hvIn hdisjIn hnrfIn hbind' with hStB | hOOFB |
            ⟨bnd, st₂, bFoot, hrunBind, hmodeB, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
             hpFrame₂, hpSS₂, honce₂, hssf₂, hst₂, hsimP0, henvNRFP0⟩
          · rw [hStB]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hOOFB]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · rw [hrunBind]; dsimp only
            -- Extract `PreservesLocs`, taint bounds, `Reach`/`OwnReach` bounds, and `ClsOk`/`.once` from `bindAt_spec`
            have hbindSpecOut :
                PreservesLocs (fun l => l < st_in.heap.objs.size ∧ (p.mode.isUnique = true → ¬ OwnReach P st_in.heap a_in l))
                  st_in.heap st₂.heap ∧
                (∀ c ∈ bnd.val.taint, c ∈ a_in.taint ∨ (p.mode.isBorrowed = true ∧ c = s_c)) ∧
                (p.cls = .leaf → bnd.val.taint = []) ∧
                (∀ l, Reach st₂.heap bnd.val l → st_in.heap.objs.size ≤ l ∨ (p.mode ≠ .erased ∧ Reach st_in.heap a_in l)) ∧
                (∀ l, OwnReach P st₂.heap bnd.val l → st_in.heap.objs.size ≤ l ∨ (p.mode ≠ .erased ∧ OwnReach P st_in.heap a_in l)) ∧
                (p.mode ≠ .erased → p.cls ≠ .val → ∀ l, Reach st₂.heap bnd.val l → st_in.heap.objs.size ≤ l ∨ NumLoc st₂.heap l) := by
              by_cases hpEr : p.mode = .erased
              · have hEq : (bindAt P n s_c .erased p.cls a_in).run st_in = .ok (⟨.imm .irr, .erased⟩, st_in) := by
                  unfold bindAt; rfl
                rw [hpEr] at hrunBind; rw [hEq] at hrunBind; cases hrunBind
                exact ⟨PreservesLocs.refl _ _, (fun _ h => by cases h), (fun _ => rfl),
                  (fun _ h => by cases h), (fun _ h => by cases h), (fun h => absurd hpEr h)⟩
              · have hvdA : ValidDeps σ_open a0'.deps := hvdA₁ hpEr
                have ha0'Src : a0'.src = none := by dsimp only [a0']; split <;> exact ha0Src
                have hnotOnceA : ¬ IsOnceSrc σ_open a0' := fun ⟨_, hs, _⟩ => by rw [ha0'Src] at hs; cases hs
                have hactA : ActiveVal σ_open a0' := ⟨hvdA, fun his => absurd his hnotOnceA⟩
                have hvActA := hvIn.2.2.2.2 hactA
                rcases bindAt_spec (P := P) (fuel := n) (s := s_c) (m := p.mode) (c := p.cls) (v := a_in)
                    hstIn.1 (fun _ => hvActA.1.1) (fun _ => hvActA.1.2.1)
                    (fun hu => by
                      by_cases hcv : a0'.cls = .val
                      · have huO := huniq₁ hu; have huI := huO.2 hcv
                        have htrA : Transferable σ_open NoKill' a0' :=
                          ⟨hcv, huI.1, huO.1, hnotOnceA, fun dep hdep => ⟨huI.2.1 dep hdep, fun hnkD => hnk₁' dep hnkD (by
                            have h1 := hstUpd₁ dep (hvIn.2.1 dep hdep); simp only [hu, hcv, hdep, and_self, ↓reduceIte] at h1; exact h1)⟩⟩
                        exact (hvActA.2.2.2.2.2.2.2 htrA).1
                      · exact (hvActA.2.2.2.1 hnotOnceA hcv).ownTreeFull.1)
                    (fun hu hnb => by
                      by_cases hcv : a0'.cls = .val
                      · have hrgNil := ((huniq₁ hu).2 hcv).2.2 hnb
                        have hdou := hvActA.2.1; rw [hrgNil, Interp.regsOf_nil] at hdou
                        exact hdou a_in (HeldBy.refl _ _)
                      · exact (hvActA.2.2.2.1 hnotOnceA hcv).deepOpenUnder_nil a_in (HeldBy.refl _ _)) with
                  hS | hO | ⟨_, _, hrun0, _, _, _, _, _, _, _, _, _, hpres0, hdl0, _, _, _, hcls0, honce0, hbt0, hbl0, _, hr0, hor0⟩
                · rw [hrunBind] at hS; cases hS
                · rw [hrunBind] at hO; cases hO
                · rw [hrunBind] at hrun0; cases hrun0
                  refine ⟨hpres0, hbt0, hbl0, hr0, hor0, fun _ hpClsNe l hrl => ?_⟩
                  by_cases huO : p.mode.usage = .once
                  · obtain ⟨base, loc, cap, hbvEq, _, hgeLoc, hoLoc, hdlB, hclsB, _, _⟩ := honce0 huO
                    rw [hbvEq] at hrl
                    cases hrl with
                    | here => exact Or.inl hgeLoc
                    | step ho1 hm1 hrB =>
                      rw [hoLoc] at ho1; cases ho1; simp only [Cell.vals, List.mem_singleton] at hm1; subst hm1
                      exact Or.inr ((ClsSafe.to_nonValSafe hpClsNe (ClsSafe.of_clsOk hclsB) hdlB.self.1).reach_numLoc hrB)
                  · exact Or.inr ((ClsSafe.to_nonValSafe hpClsNe (ClsSafe.of_clsOk (hcls0 hpEr huO)) hdl0.self.1).reach_numLoc hrl)
            obtain ⟨hpresBindOut, hbtBind, hblBind, hreachBind, hownBind, hnvClsBind⟩ := hbindSpecOut
            have hpresNum₂ : ∀ (l : Nat) (o : Obj) (n : Nat),
                st.heap.objs[l]? = some o → o.cell = .num n → st₂.heap.objs[l]? = some o := fun l o n ho hc => by
              have hoIn : st_in.heap.objs[l]? = some o := (hpresIn l (Array.getElem?_eq_some_iff.mp ho).1).trans ho
              exact (hpresBindOut l ⟨(Array.getElem?_eq_some_iff.mp hoIn).1,
                fun _ hor => OwnReach_not_numLoc hor ⟨o, n, hoIn, hc⟩⟩).trans hoIn
            have hpresEnv₂ : PreservesActiveEnv Scope env aenv σ₁ st.heap st₂.heap := by
              intro k bk abk hsc hbk habk hne ha₁
              have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
              have ha0 := ActiveVal.of_AStateLe hok (hleOpen.trans hle₁) hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha₁
              have hpresInK : PreservesLocs (Reach st.heap bk.val) st.heap st_in.heap :=
                hpresIn.mono fun l hrK => (hvK.2.2.2.2 ha0).1.1.reach_lt_size hrK
              refine hpresInK.trans (hpresBindOut.mono fun l hrK =>
                ⟨Nat.lt_of_lt_of_le ((hvK.2.2.2.2 ha0).1.1.reach_lt_size hrK) hszIn, fun hu hor => ?_⟩)
              have hrKIn : Reach st_in.heap bk.val l := (Reach_congr hpresInK l).mpr hrK
              have hpNe : p.mode ≠ .erased := by
                cases hm' : p.mode <;> rw [hm'] at hu <;> simp [BinderMode.isUnique] at hu ⊢
              have hvdA : ValidDeps σ_open a0'.deps := hvdA₁ hpNe
              have ha0'Src : a0'.src = none := by dsimp only [a0']; split <;> exact ha0Src
              have hnotOnceA : ¬ IsOnceSrc σ_open a0' := fun ⟨_, hs, _⟩ => by rw [ha0'Src] at hs; cases hs
              have hactA : ActiveVal σ_open a0' := ⟨hvdA, fun his => absurd his hnotOnceA⟩
              by_cases hcv : a0'.cls = .val
              · have huO := huniq₁ hu; have huI := huO.2 hcv
                have htrA : Transferable σ_open NoKill' a0' :=
                  ⟨hcv, huI.1, huO.1, hnotOnceA, fun dep hdep => ⟨huI.2.1 dep hdep, fun hnkD => hnk₁' dep hnkD (by
                    have h1 := hstUpd₁ dep (hvIn.2.1 dep hdep); simp only [hu, hcv, hdep, and_self, ↓reduceIte] at h1; exact h1)⟩⟩
                have hdd : ∀ dep ∈ a0'.deps, dep ∉ (effVal abk).deps := fun dep hdep hdk => by
                  have h1 := hstUpd₁ dep (hvIn.2.1 dep hdep); simp only [hu, hcv, hdep, and_self, ↓reduceIte] at h1
                  exact (ha₁.1 dep hdk).2 h1
                exact (hdisjIn k bk abk hsc hbk habk hne).1 hactA htrA ha0 hdd l hor hrKIn
              · exact ((hvIn.2.2.2.2 hactA).2.2.2.1 hnotOnceA hcv).ownTreeFull.2 l hor
            -- Build `Sim` at `(Frame, NoKill, NoSpend)` with the SAME `bFoot` from `hsimP0`!
            have hsimP0' : Sim P ext b0 st₂ Frame' NoKill' NoSpend' (shiftScope Scope) (bnd :: env) (ab :: aenv) σ_push I_open
                (fun i => match i with | 0 => bFoot | k + 1 => envFoot k) :=
              Sim_congr_scope_foot (fun i => by cases i <;> exact Iff.rfl) (fun i _ => by cases i <;> exact Iff.rfl) hsimP0
            have hrfOpen2 : RegsFuture st_open st₂ :=
              RegsFuture.same_regions (by rw [hnr₂, hnrIn]; exact Nat.le_refl _) (hrg₂.trans hrgIn)
            have honceOpen2 : PreservesOnceShell st_open.heap st₂.heap := honceIn.trans honce₂
            have hssfOpen2 : StaticStrFresh st_open st₂ := StaticStrFresh.trans hszIn hpSS₂ hssfIn hssf₂
            have hpresEnvOpen2 : PreservesActiveEnv Scope env aenv σ_push st_open.heap st₂.heap := by
              intro k bk abk hsc hbk habk hne haP
              have hvK := ((hsimOpen0.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
              have ha₁ := ActiveVal.of_AStateLe hok₁ hlePush
                (fun d hd => hszSt₁ ▸ hvK.2.1 d hd) (fun z hz => hszSt₁ ▸ (hvK.2.2.1 z hz).1) haP
              exact hpresEnv₂ k bk abk hsc hbk habk hne ha₁
            have hsimTail2 : Sim P ext b0 st₂ Frame NoKill NoSpend Scope env aenv σ_push I_open envFoot :=
              Sim_step (Nat.le_refl b0) (hle₁.trans hlePush) hokPush hsimP0'.2.2.1 hrfOpen2
                honceOpen2 hssfOpen2 (fun _ _ _ h => h) hpresEnvOpen2 hsimOpen0
            have hpresF2 : PreservesLocs Frame st_open.heap st₂.heap :=
              (hpresIn.mono fun l hF => hFlt l hF).trans (hpFrame₂.mono fun l hF => Or.inl hF)
            have hpresSSAll2 : PreservesLocs (StaticStrLoc st_open) st_open.heap st₂.heap :=
              (hpresIn.mono fun l hss => StaticStrLoc_lt_size hstOpen hss).trans
                (hpFrame₂.mono fun l hss => Or.inr (Or.inl hss))
            -- Key helper: `bFoot` is disjoint from ALL of `Frame'` whenever `FootActive σ_push (effVal ab)`!
            have hbFootDisjF' : p.mode ≠ .erased → ActiveVal σ_push (effVal ab) → FootActive σ_push (effVal ab) →
                ∀ l, bFoot l → ¬ Frame' l := by
              intro hpNe haB hfB l hfl hFr
              have hvB := (((hsimP0'.2.2.2.2.2.1 0 bnd ab trivial rfl rfl).2 hpNe).2.2.2.2.2 haB)
              rcases hfB with hooB | ⟨hisB, _⟩
              · exact (hvB.2.2.2.2.2.1 hooB).2.1 (fun x hx hnk' => by
                  dsimp [effVal] at hx; cases hx
                  have hlt : ab.id < σ_open.st.size := hnk'.1
                  change σ₁.st.size < σ.st.size at hlt; omega) l hfl hFr
              · exact (hvB.2.2.2.2.2.2.1 hisB).2.1 (fun d hd hoD hnsp' => by
                  simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hd
                  rcases hd with rfl | ⟨hdBv, _⟩
                  · have hlt : σ₁.st.size < σ_open.st.size := hnsp'.1
                    change σ₁.st.size < σ.st.size at hlt; omega
                  · have hdA0' : d ∈ a0'.deps := Runs_bindInner_deps_mem hokOpen hbind' d hdBv
                    have hmOnce : p.mode.usage = .once := by
                      obtain ⟨id, hs, hoId⟩ := hisB; dsimp [effVal, ab] at hs; cases hs
                      have hszO : σ₁.once.size = σ₁.st.size := hok₁.1.symm
                      simp only [σ_push, AState.pushBnd, ← hszO, Array.getElem?_push_size] at hoId
                      exact beq_iff_eq.mp (Option.some.inj hoId)
                    have hltSp : d < σ_open.spent.size := by have := hokOpen.2.1; exact hokOpen.2.1 ▸ hnsp'.1
                    have hoOpen : σ_open.once[d]? = some true := by
                      have hltO1 : d < σ₁.once.size := by rw [← hok₁.1, hszSt₁]; exact hnsp'.1
                      have h1 := hlePush.2.2.2.1 d hltO1; rw [h1] at hoD
                      change σ.once[d]? = some true; rw [← hσonce₁]; exact hoD
                    have hsp1 : σ₁.spent[d]? = some true := by
                      have h1 := hspUpd₁ d hltSp
                      simp only [hmOnce, or_true, hdA0', hoOpen, and_self, ↓reduceIte] at h1; exact h1
                    exact hnsp₁' d hnsp' hsp1) l hfl hFr
            -- Helper: `bv.deps` when `p.mode.isUnique = false ∧ p.mode ≠ .erased`
            have hbvNonUniq : p.mode ≠ .erased → p.mode.isUnique = false →
                bv.own = a0'.own ∧ bv.deps = a0'.deps ∧ bv.onceOnly = a0'.onceOnly :=
              fun hpNe hnu => Runs_bindInner_nonUniq hokOpen hbind' hpNe hnu
            have hsimP : Sim P ext b0 st₂ Frame NoKill NoSpend (shiftScope Scope) (bnd :: env) (ab :: aenv) σ_push I_open
                (fun i => match i with | 0 => bFoot | k + 1 => envFoot k) := by
              refine ⟨hsimP0'.1, hokPush, hsimP0'.2.2.1, hsimP0'.2.2.2.1, hsimP0'.2.2.2.2.1, ?_, ?_⟩
              · intro i b' ab' hsc' hbi' habi'
                cases i with
                | succ k => exact hsimTail2.2.2.2.2.2.1 k b' ab' hsc' hbi' habi'
                | zero =>
                  simp at hbi' habi'; subst hbi' habi'
                  obtain ⟨hmode0, hne0⟩ := hsimP0'.2.2.2.2.2.1 0 bnd ab trivial rfl rfl
                  refine ⟨hmode0, fun hpNe => ?_⟩
                  obtain ⟨honce0, hv0⟩ := hne0 hpNe
                  refine ⟨honce0, hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1, fun haB => ?_⟩
                  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hv0.2.2.2.2 haB
                  refine ⟨b1, b2, b3, b4, b5,
                    (fun hooB => let ⟨q1, _, q3, q4⟩ := b6 hooB
                      ⟨q1, fun _ l hfl hF => hbFootDisjF' hpNe haB (Or.inl hooB) l hfl (Or.inl hF), q3, q4⟩),
                    (fun hisB => let ⟨q1, _, q3⟩ := b7 hisB
                      ⟨q1, fun _ l hfl hF => hbFootDisjF' hpNe haB (Or.inr ⟨hisB, haB.2 hisB⟩) l hfl (Or.inl hF), q3⟩),
                    fun htrB => ?_⟩
                  by_cases hu : p.mode.isUnique = true
                  · have hbvDepsNil : bv.deps = [] := Runs_bindInner_deps_uniq hokOpen hbind' hu
                    have htrB' : Transferable σ_push NoKill' (effVal ab) :=
                      ⟨htrB.1, htrB.2.1, htrB.2.2.1, htrB.2.2.2.1, fun d hd => by
                        simp only [effVal, ab, hbvDepsNil, List.filter_nil, List.mem_singleton] at hd; subst hd
                        exact ⟨(htrB.2.2.2.2 _ List.mem_cons_self).1, fun hnk' => by
                          have hlt : σ₁.st.size < σ_open.st.size := hnk'.1; change σ₁.st.size < σ.st.size at hlt; omega⟩⟩
                    obtain ⟨hotf, hdisj⟩ := b8 htrB'
                    exact ⟨hotf, fun l hor => ⟨fun hF => (hdisj l hor).1 (Or.inl hF), (hdisj l hor).2⟩⟩
                  · have hnu : p.mode.isUnique = false := Bool.eq_false_iff.mpr hu
                    by_cases hclr : (fromCell && p.cls != .val) = true
                    · have hpClsNe : p.cls ≠ .val := hclrClsNe hclr hpNe
                      have hbvCls : bv.cls = p.cls := Runs_bindInner_cls hokOpen hbind' hpNe
                      exact absurd (hbvCls.symm.trans htrB.1) hpClsNe
                    · have hclrF : (fromCell && p.cls != .val) = false := Bool.eq_false_iff.mpr hclr
                      obtain ⟨haInEq, hstInEq⟩ := hnoClrEq hclrF; subst a_in; subst st_in
                      have ha0'Eq : a0' = a0 := by simp [a0', hclrF]
                      obtain ⟨hownEq, hdepsEq, hooEq⟩ := hbvNonUniq hpNe hnu
                      have hpClsV : p.cls = .val := (Runs_bindInner_cls hokOpen hbind' hpNe).symm.trans htrB.1
                      have hvdA0 : ValidDeps σ_open a0.deps := ha0'Eq ▸ hvdA₁ hpNe
                      have hnotOnceA0 : ¬ IsOnceSrc σ_open a0 := fun ⟨_, hs, _⟩ => by rw [ha0Src] at hs; cases hs
                      have hactA0 : ActiveVal σ_open a0 := ⟨hvdA0, fun his => absurd his hnotOnceA0⟩
                      have hpNotOnce : p.mode.usage ≠ .once := fun ho => by
                        apply htrB.2.2.2.1; refine ⟨ab.id, rfl, ?_⟩
                        have hszO : σ₁.once.size = σ₁.st.size := hok₁.1.symm
                        simp only [σ_push, AState.pushBnd, ab, ← hszO, Array.getElem?_push_size, ho]; rfl
                      have hlocEq : SameLoc a bnd.val ∧ st₂.heap = st_open.heap := by
                        obtain ⟨lf, hlf⟩ : ∃ lf, (isLeaf a).run st_open = .ok (lf, st_open) :=
                          ⟨_, isLeaf_ok (hvA0.2.2.2.2 hactA0).1.1.self.1⟩
                        unfold bindAt at hrunBind
                        have hpErF : (p.mode == .erased) = false := BinderMode_beq_false_of_ne hpNe
                        simp only [hpErF, Bool.false_eq_true, ↓reduceIte, hpClsV, M_bind_run] at hrunBind
                        have hconf : (conform .val a).run st_open = .ok (a, st_open) := rfl
                        rw [hconf] at hrunBind; dsimp only at hrunBind
                        cases hm' : p.mode with
                        | erased => exact absurd hm' hpNe
                        | unique | uniqueBorrowed => rw [hm'] at hnu; cases hnu
                        | once | onceBorrowed => rw [hm'] at hpNotOnce; exact absurd rfl hpNotOnce
                        | many =>
                          rw [hm'] at hrunBind
                          simp only [BinderMode.isUnique, BinderMode.isBorrowed, BinderMode.usage,
                            Bool.false_eq_true, ↓reduceIte, M_bind_run, M_pure_run] at hrunBind
                          rw [hlf] at hrunBind
                          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrunBind
                          cases hrunBind; exact ⟨SameLoc.refl _, rfl⟩
                        | borrowed =>
                          rw [hm'] at hrunBind
                          simp only [BinderMode.isUnique, BinderMode.isBorrowed, BinderMode.usage,
                            Bool.false_eq_true, ↓reduceIte, M_bind_run, M_pure_run] at hrunBind
                          rw [hlf] at hrunBind
                          cases lf with
                          | true =>
                            simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrunBind
                            cases hrunBind; exact ⟨SameLoc.refl _, rfl⟩
                          | false =>
                            simp only [Bool.not_false, Bool.and_true, ↓reduceIte] at hrunBind
                            cases hrunBind; exact ⟨by cases a <;> simp [SameLoc, addTaint], rfl⟩
                      by_cases ha0V : a0.cls = .val
                      · have htrA0 : Transferable σ_open NoKill a0 := by
                          refine ⟨ha0V, by rw [← ha0'Eq, ← hownEq]; exact htrB.2.1,
                            by rw [← ha0'Eq, ← hooEq]; exact htrB.2.2.1, hnotOnceA0, fun d hd => ?_⟩
                          have hdBv : d ∈ bv.deps := hdepsEq.symm ▸ (ha0'Eq.symm ▸ hd)
                          have hdLt : d < σ₁.st.size := hszSt₁ ▸ hvA0.2.1 d hd
                          have hdInEff : d ∈ (effVal ab).deps := by
                            simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]
                            exact Or.inr ⟨hdBv, Nat.ne_of_lt hdLt⟩
                          obtain ⟨hlvP, hnotNK⟩ := htrB.2.2.2.2 d hdInEff
                          have h1 := (hle₁.trans hlePush).2.2.1 d (hvA0.2.1 d hd); rw [hlvP] at h1
                          refine ⟨?_, hnotNK⟩
                          cases h0 : σ_open.st[d]? with
                          | none => rw [h0] at h1; cases h1
                          | some b0' => rw [h0] at h1; cases b0' with | live => rfl | shared | dead => cases h1
                        have hotfA0 := (hvA0.2.2.2.2 hactA0).2.2.2.2.2.2.2 htrA0
                        refine ⟨OwnTreeFull_of_sameLoc hlocEq.1 (hlocEq.2 ▸ hotfA0.1), fun l hor => ?_⟩
                        have hor0 : OwnReach P st_open.heap a l := (hownBind l hor).resolve_left
                          (Nat.not_le_of_lt (hlocEq.2 ▸ b1.1.reach_lt_size (OwnReach_toReach hor))) |>.2
                        exact ⟨(hotfA0.2 l hor0).1, fun hss2 => by
                          rcases hssf₂ l hss2 with hge | hss0 | hnum2
                          · exact Nat.not_lt_of_ge hge (hvA0.2.2.2.2 hactA0 |>.1.1.reach_lt_size (OwnReach_toReach hor0))
                          · exact (hotfA0.2 l hor0).2 hss0
                          · exact OwnReach_not_numLoc hor hnum2⟩
                      · have hnvA0 := (hvA0.2.2.2.2 hactA0).2.2.2.1 hnotOnceA0 ha0V
                        refine ⟨OwnTreeFull_of_sameLoc hlocEq.1 (hlocEq.2 ▸ hnvA0.ownTreeFull.1), fun l hor =>
                          False.elim (hnvA0.ownTreeFull.2 l ((hownBind l hor).resolve_left
                            (Nat.not_le_of_lt (hlocEq.2 ▸ b1.1.reach_lt_size (OwnReach_toReach hor))) |>.2))⟩
              · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
                cases i with
                | succ k₁ =>
                  cases j with
                  | succ k₂ => exact hsimTail2.2.2.2.2.2.2 k₁ k₂ b₁ b₂ ab₁ ab₂ (by omega) hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
                  | zero =>
                    simp at hb₂ hab₂; subst hb₂ hab₂
                    refine ⟨fun ha₁ htr₁ ha₂ hdd l hor₁ hr₂ => ?_,
                      (hsimP0'.2.2.2.2.2.2 (k₁ + 1) 0 b₁ bnd ab₁ ab hij hsi hsj hb₁ hab₁ rfl rfl hne₁ hne₂).2⟩
                    have hvK := ((hsimOpen0.2.2.2.2.2.1 k₁ b₁ ab₁ hsi hb₁ hab₁).2 hne₁).2
                    have haK0 := ActiveVal.of_AStateLe hokOpen (hle₁.trans hlePush) hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha₁
                    have htrK0 := Transferable.of_AStateLe hokOpen (hle₁.trans hlePush) hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) (fun _ h => h) htr₁
                    have horK0 : OwnReach P st_open.heap b₁.val l :=
                      (OwnReach_congr (hpresEnvOpen2 k₁ b₁ ab₁ hsi hb₁ hab₁ hne₁ ha₁) l).mp hor₁
                    have hltO : l < st_open.heap.objs.size := (hvK.2.2.2.2 haK0).1.1.reach_lt_size (OwnReach_toReach horK0)
                    by_cases hclr : (fromCell && p.cls != .val) = true
                    · rcases hnvClsBind hne₂ (hclrClsNe hclr hne₂) l hr₂ with hge | hnum2
                      · exact Nat.not_lt_of_ge hge (Nat.lt_of_lt_of_le hltO hszIn)
                      · exact OwnReach_not_numLoc hor₁ hnum2
                    · have hclrF : (fromCell && p.cls != .val) = false := Bool.eq_false_iff.mpr hclr
                      obtain ⟨haInEq, hstInEq⟩ := hnoClrEq hclrF; subst a_in; subst st_in
                      have ha0'Eq : a0' = a0 := by simp [a0', hclrF]
                      have hrA : Reach st_open.heap a l := (hreachBind l hr₂).resolve_left (Nat.not_le_of_lt hltO) |>.2
                      have hvdA0 : ValidDeps σ_open a0.deps := ha0'Eq ▸ hvdA₁ hne₂
                      have hnotOnceA0 : ¬ IsOnceSrc σ_open a0 := fun ⟨_, hs, _⟩ => by rw [ha0Src] at hs; cases hs
                      have hactA0 : ActiveVal σ_open a0 := ⟨hvdA0, fun his => absurd his hnotOnceA0⟩
                      by_cases hu : p.mode.isUnique = true
                      · by_cases ha0V : a0.cls = .val
                        · have hdd0 : ∀ d ∈ (effVal ab₁).deps, d ∉ a0.deps := fun d hdk hd => by
                            have h1 := hstUpd₁ d (hvA0.2.1 d hd); rw [ha0'Eq] at h1
                            simp only [hu, ha0V, hd, and_self, ↓reduceIte] at h1
                            have hlv := (htr₁.2.2.2.2 d hdk).1
                            have h2 := hlePush.2.2.1 d (hszSt₁ ▸ hvK.2.1 d hdk); rw [h1, hlv] at h2; cases h2
                          exact (hdisjA0 k₁ b₁ ab₁ hsi hb₁ hab₁ hne₁).2.1 haK0 htrK0 hactA0 hdd0 l horK0 hrA
                        · exact OwnReach_not_numLoc horK0 (((hvA0.2.2.2.2 hactA0).2.2.2.1 hnotOnceA0 ha0V).reach_numLoc hrA)
                      · have hnu : p.mode.isUnique = false := Bool.eq_false_iff.mpr hu
                        obtain ⟨_, hdepsEq, _⟩ := hbvNonUniq hne₂ hnu
                        have hdd0 : ∀ d ∈ (effVal ab₁).deps, d ∉ a0.deps := fun d hdk hd => by
                          have hdBv : d ∈ bv.deps := hdepsEq.symm ▸ (ha0'Eq.symm ▸ hd)
                          have hdLt : d < σ₁.st.size := hszSt₁ ▸ hvA0.2.1 d hd
                          exact hdd d hdk (by simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]; exact Or.inr ⟨hdBv, Nat.ne_of_lt hdLt⟩)
                        exact (hdisjA0 k₁ b₁ ab₁ hsi hb₁ hab₁ hne₁).2.1 haK0 htrK0 hactA0 hdd0 l horK0 hrA
                | zero =>
                  cases j with
                  | zero => exact absurd rfl hij
                  | succ k₂ =>
                    simp at hb₁ hab₁; subst hb₁ hab₁
                    refine ⟨fun ha₁ htr₁ ha₂ hdd l hor₁ hr₂ => ?_,
                      (hsimP0'.2.2.2.2.2.2 0 (k₂ + 1) bnd b₂ ab ab₂ hij hsi hsj rfl rfl hb₂ hab₂ hne₁ hne₂).2⟩
                    by_cases hu : p.mode.isUnique = true
                    · have hbvDepsNil : bv.deps = [] := Runs_bindInner_deps_uniq hokOpen hbind' hu
                      have htr₁' : Transferable σ_push NoKill' (effVal ab) :=
                        ⟨htr₁.1, htr₁.2.1, htr₁.2.2.1, htr₁.2.2.2.1, fun d hd => by
                          simp only [effVal, ab, hbvDepsNil, List.filter_nil, List.mem_singleton] at hd; subst hd
                          exact ⟨(htr₁.2.2.2.2 _ List.mem_cons_self).1, fun hnk' => by
                            have hlt : σ₁.st.size < σ_open.st.size := hnk'.1; change σ₁.st.size < σ.st.size at hlt; omega⟩⟩
                      exact (hsimP0'.2.2.2.2.2.2 0 (k₂ + 1) bnd b₂ ab ab₂ hij hsi hsj rfl rfl hb₂ hab₂ hne₁ hne₂).1
                        ha₁ htr₁' ha₂ hdd l hor₁ hr₂
                    · have hnu : p.mode.isUnique = false := Bool.eq_false_iff.mpr hu
                      by_cases hclr : (fromCell && p.cls != .val) = true
                      · have hpClsNe : p.cls ≠ .val := hclrClsNe hclr hne₁
                        have hbvCls : bv.cls = p.cls := Runs_bindInner_cls hokOpen hbind' hne₁
                        exact absurd (hbvCls.symm.trans htr₁.1) hpClsNe
                      · have hclrF : (fromCell && p.cls != .val) = false := Bool.eq_false_iff.mpr hclr
                        obtain ⟨haInEq, hstInEq⟩ := hnoClrEq hclrF; subst a_in; subst st_in
                        have ha0'Eq : a0' = a0 := by simp [a0', hclrF]
                        obtain ⟨hownEq, hdepsEq, hooEq⟩ := hbvNonUniq hne₁ hnu
                        have hvK := ((hsimOpen0.2.2.2.2.2.1 k₂ b₂ ab₂ hsj hb₂ hab₂).2 hne₂).2
                        have haK0 := ActiveVal.of_AStateLe hokOpen (hle₁.trans hlePush) hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha₂
                        have hrK0 : Reach st_open.heap b₂.val l :=
                          (Reach_congr (hpresEnvOpen2 k₂ b₂ ab₂ hsj hb₂ hab₂ hne₂ ha₂) l).mp hr₂
                        have hltO : l < st_open.heap.objs.size := (hvK.2.2.2.2 haK0).1.1.reach_lt_size hrK0
                        have horA : OwnReach P st_open.heap a l := (hownBind l hor₁).resolve_left (Nat.not_le_of_lt hltO) |>.2
                        have hvdA0 : ValidDeps σ_open a0.deps := ha0'Eq ▸ hvdA₁ hne₁
                        have hnotOnceA0 : ¬ IsOnceSrc σ_open a0 := fun ⟨_, hs, _⟩ => by rw [ha0Src] at hs; cases hs
                        have hactA0 : ActiveVal σ_open a0 := ⟨hvdA0, fun his => absurd his hnotOnceA0⟩
                        by_cases ha0V : a0.cls = .val
                        · have htrA0 : Transferable σ_open NoKill a0 := by
                            refine ⟨ha0V, by rw [← ha0'Eq, ← hownEq]; exact htr₁.2.1,
                              by rw [← ha0'Eq, ← hooEq]; exact htr₁.2.2.1, hnotOnceA0, fun d hd => ?_⟩
                            have hdBv : d ∈ bv.deps := hdepsEq.symm ▸ (ha0'Eq.symm ▸ hd)
                            have hdLt : d < σ₁.st.size := hszSt₁ ▸ hvA0.2.1 d hd
                            have hdInEff : d ∈ (effVal ab).deps := by
                              simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]
                              exact Or.inr ⟨hdBv, Nat.ne_of_lt hdLt⟩
                            obtain ⟨hlvP, hnotNK⟩ := htr₁.2.2.2.2 d hdInEff
                            have h1 := (hle₁.trans hlePush).2.2.1 d (hvA0.2.1 d hd); rw [hlvP] at h1
                            refine ⟨?_, hnotNK⟩
                            cases h0 : σ_open.st[d]? with
                            | none => rw [h0] at h1; cases h1
                            | some b0' => rw [h0] at h1; cases b0' with | live => rfl | shared | dead => cases h1
                          have hdd0 : ∀ d ∈ a0.deps, d ∉ (effVal ab₂).deps := fun d hd hdk => by
                            have hdBv : d ∈ bv.deps := hdepsEq.symm ▸ (ha0'Eq.symm ▸ hd)
                            have hdLt : d < σ₁.st.size := hszSt₁ ▸ hvA0.2.1 d hd
                            exact hdd d (by simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]; exact Or.inr ⟨hdBv, Nat.ne_of_lt hdLt⟩) hdk
                          exact (hdisjA0 k₂ b₂ ab₂ hsj hb₂ hab₂ hne₂).1 hactA0 htrA0 haK0 hdd0 l horA hrK0
                        · exact ((hvA0.2.2.2.2 hactA0).2.2.2.1 hnotOnceA0 ha0V).ownTreeFull.2 l horA
            have henvNRFP : EnvNoReachForbid st₂ (shiftScope Scope) (bnd :: env) (ab :: aenv) σ_push Forbid BadReg' BadDepP := by
              intro i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps
              have hvP := ((hsimP.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
              exact henvNRFP0 i b' ab' (by cases i <;> exact hsc') hbi' habi' hne' ha' hregs
                (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvP.2.1 dep hdep) (Nat.le_refl _), hbd.2⟩)
            have henvTaintP : EnvTaintOk (shiftScope Scope) (bnd :: env) (ab :: aenv) st₂ I_open := by
              have ht₂ := henvTaintOpen.step (hrg₂.trans hrgIn) (by rw [hnr₂, hnrIn]; exact Nat.le_refl _)
              intro i b' ab' hsc' hbi' habi' hne'
              cases i with
              | succ k => exact ht₂ k b' ab' hsc' hbi' habi' hne'
              | zero =>
                simp at hbi' habi'; subst hbi' habi'
                have hpNe : p.mode ≠ .erased := hne'
                have hvdA : ValidDeps σ_open a0'.deps := hvdA₁ hpNe
                have ha0'Src : a0'.src = none := by dsimp only [a0']; split <;> exact ha0Src
                have hnotOnceA : ¬ IsOnceSrc σ_open a0' := fun ⟨_, hs, _⟩ => by rw [ha0'Src] at hs; cases hs
                have hvActA := hvIn.2.2.2.2 ⟨hvdA, fun his => absurd his hnotOnceA⟩
                refine ⟨fun c hc => ?_, fun c hc hopen => ?_⟩
                · rcases hbtBind c hc with hcA | ⟨_, rfl⟩
                  · rw [hnr₂]; exact hvActA.1.2.2.2 a_in (HeldBy.refl _ _) c hcA
                  · rw [hnr₂, hnrIn]; exact Nat.lt_succ_self s_c
                · by_cases hdLeaf : p.cls = .leaf
                  · rw [hblBind hdLeaf] at hc; cases hc
                  · rcases hbtBind c hc with hcA | ⟨hbor, rfl⟩
                    · have hcInI : c ∈ I_open.regsOf a0'.regs := hvActA.2.1 a_in (HeldBy.refl _ _) c hcA (hrg₂ ▸ hopen)
                      obtain ⟨rg, hrgA, hcRg⟩ := Interp.mem_regsOf.mp hcInI
                      refine Interp.mem_regsOf.mpr ⟨rg, ?_, hcRg⟩
                      by_cases hmu : p.mode = .unique
                      · exfalso
                        by_cases hcv : a0'.cls = .val
                        · have hrgNil := ((huniq₁ (by rw [hmu]; rfl)).2 hcv).2.2 (by rw [hmu]; rfl)
                          rw [hrgNil] at hrgA; cases hrgA
                        · have hnv := hvActA.2.2.2.1 hnotOnceA hcv
                          rw [hnv.taint_nil] at hcA; cases hcA
                      · change rg ∈ bv.regs
                        exact Runs_bindInner_regs_of_mem hokOpen hbind hpNe hmu hdLeaf rg hrgA
                    · refine Interp.mem_regsOf.mpr ⟨s_a, ?_, by rw [hIopenSa]; exact List.mem_cons_self⟩
                      change s_a ∈ bv.regs
                      exact Runs_bindInner_regs_of_borrowed hokOpen hbind hbor hdLeaf
            -- Lift `restArgList` and `hRestMeta` across `(st_open → st_in → st₂)` and `(env → bnd :: env, σ_open → σ_push)`!
            have hpresRestActive : ∀ (k : Nat) v av ft,
                restArgList[k]? = some (some (v, av, ft)) → ActiveVal σ₁ av →
                PreservesLocs (Reach st_open.heap v) st_open.heap st₂.heap := by
              intro k v av ft hgk haK₁
              have hgFull : fullArgList[k + 1]? = some (some (v, av, ft)) := by rw [hFullEq]; exact hgk
              have hvK := (hArgListOpen.1 (k + 1) v av ft hgFull).1
              have haK0 := ActiveVal.of_AStateLe hokOpen hle₁ hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) haK₁
              exact (hpresIn.mono fun l hr => (hvK.2.2.2.2 haK0).1.1.reach_lt_size hr).trans
                (hpFrame₂.mono fun l hr => Or.inr (Or.inr ⟨k + 1, v, av, ft, Nat.succ_pos k, hgFull, haK₁, hr⟩))
            have hRestArgList : ArgListOk P ext b0 st₂ Frame NoKill NoSpend (shiftScope Scope)
                (bnd :: env) (ab :: aenv) σ_push I_open
                (fun i => match i with | 0 => bFoot | k + 1 => envFoot k)
                Forbid BadReg' BadDepP restArgList := by
              have hle1P : AStateLe σ_open σ_push := hle₁.trans hlePush
              refine ⟨fun k v av ft hgk => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
              · have hgFull : fullArgList[k + 1]? = some (some (v, av, ft)) := by rw [hFullEq]; exact hgk
                obtain ⟨hvK0, hdisjK0, hnrfK0, hnvK0⟩ := hArgListOpen.1 (k + 1) v av ft hgFull
                have hftK : ft = fun (_ : Nat) => False := by
                  simp only [restArgList, List.getElem?_map] at hgk
                  cases hz : (restC.zip rest)[k]? with
                  | none => rw [hz] at hgk; cases hgk
                  | some pr =>
                    rw [hz] at hgk; rcases pr with ⟨⟨v', _⟩, ⟨a1', er', _⟩⟩
                    cases er' with
                    | true => simp at hgk
                    | false => simp at hgk; exact hgk.2.2.symm
                subst hftK
                have hpresK : ActiveVal σ_push av → PreservesLocs (Reach st_open.heap v) st_open.heap st₂.heap := fun haP =>
                  hpresRestActive k v av (fun (_ : Nat) => False) hgk
                    (ActiveVal.of_AStateLe hok₁ hlePush (fun d hd => hszSt₁ ▸ hvK0.2.1 d hd) (fun z hz => hszSt₁ ▸ (hvK0.2.2.1 z hz).1) haP)
                have hvK2 : VSim P ext b0 st₂ Frame NoKill NoSpend σ_push I_open (fun (_ : Nat) => False) av v :=
                  VSim_step (Nat.le_refl b0) hokOpen hle1P hrfOpen2 honceOpen2 hssfOpen2 (fun _ _ _ h => h) hpresK hvK0
                have hdisjK2 : ValEnvDisj P st₂ NoKill (shiftScope Scope) (bnd :: env) (ab :: aenv) σ_push
                    (fun i => match i with | 0 => bFoot | k + 1 => envFoot k) (fun (_ : Nat) => False) av v := by
                  intro idx b' ab' hsc' hbi' habi' hne'
                  cases idx with
                  | succ m =>
                    have h0 := hdisjK0 m b' ab' hsc' hbi' habi' hne'
                    have hvM := ((hsimOpen0.2.2.2.2.2.1 m b' ab' hsc' hbi' habi').2 hne').2
                    refine ⟨fun haV htrV haB hdd l horV hrB =>
                        h0.1 (ActiveVal.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) haV)
                          (Transferable.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) (fun _ h => h) htrV)
                          (ActiveVal.of_AStateLe hokOpen hle1P hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) haB) hdd l
                          ((OwnReach_congr (hpresK haV) l).mp horV)
                          ((Reach_congr (hpresEnvOpen2 m b' ab' hsc' hbi' habi' hne' haB) l).mp hrB),
                      fun haB htrB haV hdd l horB hrV =>
                        h0.2.1 (ActiveVal.of_AStateLe hokOpen hle1P hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) haB)
                          (Transferable.of_AStateLe hokOpen hle1P hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) (fun _ h => h) htrB)
                          (ActiveVal.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) haV) hdd l
                          ((OwnReach_congr (hpresEnvOpen2 m b' ab' hsc' hbi' habi' hne' haB) l).mp horB)
                          ((Reach_congr (hpresK haV) l).mp hrV),
                      (fun _ _ _ _ _ h => False.elim h),
                      fun haB hfB haV hneS l hft hrV =>
                        h0.2.2.2.1 (ActiveVal.of_AStateLe hokOpen hle1P hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) haB)
                          (FootActive.of_AStateLe hokOpen hle1P hvM.2.1 (fun z hz => (hvM.2.2.1 z hz).1) hfB)
                          (ActiveVal.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) haV) hneS l hft
                          ((Reach_congr (hpresK haV) l).mp hrV),
                      (fun _ _ _ _ h => False.elim h),
                      h0.2.2.2.2.2.1,
                      fun haV hs => by
                        rcases h0.2.2.2.2.2.2 (ActiveVal.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) haV) hs with hl | hn
                        · exact Or.inl hl
                        · exact Or.inr fun l hr => (NumLoc_congr (hpresK haV) ((Reach_congr (hpresK haV) l).mp hr)).mp (hn l ((Reach_congr (hpresK haV) l).mp hr))⟩
                  | zero =>
                    simp at hbi' habi'; subst hbi' habi'
                    have havSrc : av.src = none := by
                      have hltZ : k < (restC.zip rest).length := by
                        simp only [restArgList, List.getElem?_map] at hgk
                        cases hz : (restC.zip rest)[k]? with
                        | none => rw [hz] at hgk; cases hgk
                        | some _ => exact (List.getElem?_eq_some_iff.mp hz).1
                      have hltC : k < restC.length := by rw [List.length_zip] at hltZ; omega
                      have hltR : k < rest.length := by rw [List.length_zip] at hltZ; omega
                      simp only [restArgList, List.getElem?_map, List.getElem?_eq_getElem hltZ, List.getElem_zip] at hgk
                      rcases hc' : restC[k] with ⟨v', er_c'⟩
                      rcases ha' : rest[k] with ⟨a1', er_a', fc'⟩
                      rw [hc', ha'] at hgk
                      cases er_a' with
                      | true => simp at hgk
                      | false =>
                        simp at hgk; rcases hgk with ⟨_, rfl⟩
                        exact (hArgsMeta (k + 1) v' er_c' a1' false fc' (by simp only [List.getElem?_cons_succ]; rw [List.getElem?_eq_getElem hltC, hc'])
                          (by simp only [List.getElem?_cons_succ]; rw [List.getElem?_eq_getElem hltR, ha'])).2.1
                    refine ⟨?_, ?_, (fun _ _ _ _ _ h => False.elim h), ?_, (fun _ _ _ _ h => False.elim h),
                      (fun hs => by rw [havSrc] at hs; cases hs), (fun _ hs => by rw [havSrc] at hs; cases hs)⟩
                    · -- `OwnReach v` vs `Reach bnd.val`
                      intro haV htrV haB hdd l horV hrB
                      have haV0 := ActiveVal.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) haV
                      have htrV0 := Transferable.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) (fun _ h => h) htrV
                      have horV0 : OwnReach P st_open.heap v l := (OwnReach_congr (hpresK haV) l).mp horV
                      have hltO : l < st_open.heap.objs.size := (hvK0.2.2.2.2 haV0).1.1.reach_lt_size (OwnReach_toReach horV0)
                      by_cases hclr : (fromCell && p.cls != .val) = true
                      · rcases hnvClsBind hne' (hclrClsNe hclr hne') l hrB with hge | hnum2
                        · exact Nat.not_lt_of_ge hge (Nat.lt_of_lt_of_le hltO hszIn)
                        · exact OwnReach_not_numLoc horV hnum2
                      · have hclrF : (fromCell && p.cls != .val) = false := Bool.eq_false_iff.mpr hclr
                        obtain ⟨haInEq, hstInEq⟩ := hnoClrEq hclrF; subst a_in; subst st_in
                        have ha0'Eq : a0' = a0 := by simp [a0', hclrF]
                        have hrA : Reach st_open.heap a l := (hreachBind l hrB).resolve_left (Nat.not_le_of_lt hltO) |>.2
                        have hvdA0 : ValidDeps σ_open a0.deps := ha0'Eq ▸ hvdA₁ hne'
                        have hnotOnceA0 : ¬ IsOnceSrc σ_open a0 := fun ⟨_, hs, _⟩ => by rw [ha0Src] at hs; cases hs
                        have hactA0 : ActiveVal σ_open a0 := ⟨hvdA0, fun his => absurd his hnotOnceA0⟩
                        by_cases hu : p.mode.isUnique = true
                        · by_cases ha0V : a0.cls = .val
                          · have hdd0 : ∀ d ∈ av.deps, d ∉ a0.deps := fun d hdk hd => by
                              have h1 := hstUpd₁ d (hvA0.2.1 d hd); rw [ha0'Eq] at h1
                              simp only [hu, ha0V, hd, and_self, ↓reduceIte] at h1
                              have hlv := (htrV.2.2.2.2 d hdk).1
                              have h2 := hlePush.2.2.1 d (hszSt₁ ▸ hvK0.2.1 d hdk); rw [h1, hlv] at h2; cases h2
                            exact (hArgListOpen.2 (k + 1) 0 v a av a0 (fun (_ : Nat) => False) (fun (_ : Nat) => False)
                              (by omega) hgFull (by rw [hFullEq]; rfl)).1 haV0 htrV0 hactA0 hdd0 l horV0 hrA
                          · exact OwnReach_not_numLoc horV0 (((hvA0.2.2.2.2 hactA0).2.2.2.1 hnotOnceA0 ha0V).reach_numLoc hrA)
                        · have hnu : p.mode.isUnique = false := Bool.eq_false_iff.mpr hu
                          obtain ⟨_, hdepsEq, _⟩ := hbvNonUniq hne' hnu
                          have hdd0 : ∀ d ∈ av.deps, d ∉ a0.deps := fun d hdk hd => by
                            have hdBv : d ∈ bv.deps := hdepsEq.symm ▸ (ha0'Eq.symm ▸ hd)
                            have hdLt : d < σ₁.st.size := hszSt₁ ▸ hvA0.2.1 d hd
                            exact hdd d hdk (by simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]; exact Or.inr ⟨hdBv, Nat.ne_of_lt hdLt⟩)
                          exact (hArgListOpen.2 (k + 1) 0 v a av a0 (fun (_ : Nat) => False) (fun (_ : Nat) => False)
                            (by omega) hgFull (by rw [hFullEq]; rfl)).1 haV0 htrV0 hactA0 hdd0 l horV0 hrA
                    · -- `OwnReach bnd.val` vs `Reach v`
                      intro haB htrB haV hdd l horB hrV
                      have haV1 : ActiveVal σ₁ av := ActiveVal.of_AStateLe hok₁ hlePush
                        (fun d hd => hszSt₁ ▸ hvK0.2.1 d hd) (fun z hz => hszSt₁ ▸ (hvK0.2.2.1 z hz).1) haV
                      have haV0 := ActiveVal.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) haV
                      have hrV0 : Reach st_open.heap v l := (Reach_congr (hpresK haV) l).mp hrV
                      have hltO : l < st_open.heap.objs.size := (hvK0.2.2.2.2 haV0).1.1.reach_lt_size hrV0
                      by_cases hu : p.mode.isUnique = true
                      · have hbvDepsNil : bv.deps = [] := Runs_bindInner_deps_uniq hokOpen hbind' hu
                        have htrB' : Transferable σ_push NoKill' (effVal ab) :=
                          ⟨htrB.1, htrB.2.1, htrB.2.2.1, htrB.2.2.2.1, fun d hd => by
                            simp only [effVal, ab, hbvDepsNil, List.filter_nil, List.mem_singleton] at hd; subst hd
                            exact ⟨(htrB.2.2.2.2 _ List.mem_cons_self).1, fun hnk' => by
                              have hlt : σ₁.st.size < σ_open.st.size := hnk'.1; change σ₁.st.size < σ.st.size at hlt; omega⟩⟩
                        have hdisjF' := ((((hsimP0'.2.2.2.2.2.1 0 bnd ab trivial rfl rfl).2 hne').2.2.2.2.2 haB).2.2.2.2.2.2.2 htrB').2 l horB
                        exact hdisjF'.1 (Or.inr (Or.inr ⟨k + 1, v, av, fun (_ : Nat) => False, Nat.succ_pos k, hgFull, haV1, hrV0⟩))
                      · have hnu : p.mode.isUnique = false := Bool.eq_false_iff.mpr hu
                        by_cases hclr : (fromCell && p.cls != .val) = true
                        · have hpClsNe : p.cls ≠ .val := hclrClsNe hclr hne'
                          have hbvCls : bv.cls = p.cls := Runs_bindInner_cls hokOpen hbind' hne'
                          exact absurd (hbvCls.symm.trans htrB.1) hpClsNe
                        · have hclrF : (fromCell && p.cls != .val) = false := Bool.eq_false_iff.mpr hclr
                          obtain ⟨haInEq, hstInEq⟩ := hnoClrEq hclrF; subst a_in; subst st_in
                          have ha0'Eq : a0' = a0 := by simp [a0', hclrF]
                          obtain ⟨hownEq, hdepsEq, hooEq⟩ := hbvNonUniq hne' hnu
                          have horA : OwnReach P st_open.heap a l := (hownBind l horB).resolve_left (Nat.not_le_of_lt hltO) |>.2
                          have hvdA0 : ValidDeps σ_open a0.deps := ha0'Eq ▸ hvdA₁ hne'
                          have hnotOnceA0 : ¬ IsOnceSrc σ_open a0 := fun ⟨_, hs, _⟩ => by rw [ha0Src] at hs; cases hs
                          have hactA0 : ActiveVal σ_open a0 := ⟨hvdA0, fun his => absurd his hnotOnceA0⟩
                          by_cases ha0V : a0.cls = .val
                          · have htrA0 : Transferable σ_open NoKill a0 := by
                              refine ⟨ha0V, by rw [← ha0'Eq, ← hownEq]; exact htrB.2.1,
                                by rw [← ha0'Eq, ← hooEq]; exact htrB.2.2.1, hnotOnceA0, fun d hd => ?_⟩
                              have hdBv : d ∈ bv.deps := hdepsEq.symm ▸ (ha0'Eq.symm ▸ hd)
                              have hdLt : d < σ₁.st.size := hszSt₁ ▸ hvA0.2.1 d hd
                              have hdInEff : d ∈ (effVal ab).deps := by
                                simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]
                                exact Or.inr ⟨hdBv, Nat.ne_of_lt hdLt⟩
                              obtain ⟨hlvP, hnotNK⟩ := htrB.2.2.2.2 d hdInEff
                              have h1 := hle1P.2.2.1 d (hvA0.2.1 d hd); rw [hlvP] at h1
                              refine ⟨?_, hnotNK⟩
                              cases h0 : σ_open.st[d]? with
                              | none => rw [h0] at h1; cases h1
                              | some b0' => rw [h0] at h1; cases b0' with | live => rfl | shared | dead => cases h1
                            have hdd0 : ∀ d ∈ a0.deps, d ∉ av.deps := fun d hd hdk => by
                              have hdBv : d ∈ bv.deps := hdepsEq.symm ▸ (ha0'Eq.symm ▸ hd)
                              have hdLt : d < σ₁.st.size := hszSt₁ ▸ hvA0.2.1 d hd
                              exact hdd d (by simp only [effVal, ab, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]; exact Or.inr ⟨hdBv, Nat.ne_of_lt hdLt⟩) hdk
                            exact (hArgListOpen.2 0 (k + 1) a v a0 av (fun (_ : Nat) => False) (fun (_ : Nat) => False)
                              (by omega) (by rw [hFullEq]; rfl) hgFull).1 hactA0 htrA0 haV0 hdd0 l horA hrV0
                          · exact ((hvA0.2.2.2.2 hactA0).2.2.2.1 hnotOnceA0 ha0V).ownTreeFull.2 l horA
                    · -- `bFoot l → ¬ Reach st₂.heap v l`
                      intro haB hfB haV _ l hfl hrV
                      have haV1 : ActiveVal σ₁ av := ActiveVal.of_AStateLe hok₁ hlePush
                        (fun d hd => hszSt₁ ▸ hvK0.2.1 d hd) (fun z hz => hszSt₁ ▸ (hvK0.2.2.1 z hz).1) haV
                      have hrV0 : Reach st_open.heap v l := (Reach_congr (hpresK haV) l).mp hrV
                      exact hbFootDisjF' hne' haB hfB l hfl
                        (Or.inr (Or.inr ⟨k + 1, v, av, fun (_ : Nat) => False, Nat.succ_pos k, hgFull, haV1, hrV0⟩))
                have hnrfK2 : ActiveVal σ_push av → NoReachForbid st₂ Forbid BadReg' BadDepP av v := by
                  intro haP hregs hdeps l hr2 hnotSS2 hnotNum2 hF
                  have hpK := hpresK haP
                  have hr0 := (Reach_congr hpK l).mp hr2
                  have hnotSS0 : ¬ StaticStrLoc st_open l := fun hss0 =>
                    hnotSS2 (StaticStrLoc_mono (hstat₂ ▸ hstatIn ▸ ArrayExtends.refl _)
                      (hstr₂ ▸ hstrIn ▸ ArrayExtends.refl _) hpresSSAll2 hss0)
                  have hnotNum0 : ¬ NumLoc st_open.heap l := fun hnum0 => hnotNum2 ((NumLoc_congr hpK hr0).mp hnum0)
                  exact hnrfK0 (ActiveVal.of_AStateLe hokOpen hle1P hvK0.2.1 (fun z hz => (hvK0.2.2.1 z hz).1) haP)
                    hregs (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le hbd.1 hle1P.1, hbd.2⟩)
                    l hr0 hnotSS0 hnotNum0 hF
                have hnvK2 : ValidDeps σ_push av.deps → av.cls ≠ .val → ValBaseOk st₂ v ∧ NonValSafe st₂.heap v := by
                  intro hvdP hneV
                  have hvd0 := ValidDeps.of_AStateLe hle1P hvK0.2.1 hvdP
                  obtain ⟨hbv0, hnv0⟩ := hnvK0 hvd0 hneV
                  have hpK : PreservesLocs (Reach st_open.heap v) st_open.heap st₂.heap :=
                    hpresIn.mono (fun _ hr => hbv0.1.reach_lt_size hr) |>.trans
                      (hpresBindOut.mono fun l hr =>
                        ⟨Nat.lt_of_lt_of_le (hbv0.1.reach_lt_size hr) hszIn, fun _ hor =>
                          OwnReach_not_numLoc hor (by
                            have hnum0 := hnv0.reach_numLoc hr
                            exact (NumLoc_congr (hpresIn.mono fun _ hr' => hbv0.1.reach_lt_size hr') hr).mp hnum0)⟩)
                  exact ⟨ValBaseOk_congr hpK hrfOpen2.1 hbv0, NonValSafe.congr hpK hnv0⟩
                exact ⟨hvK2, hdisjK2, hnrfK2, hnvK2⟩
              · have hgi : fullArgList[i + 1]? = some (some (v₁, av₁, ft₁)) := by rw [hFullEq]; exact hg₁
                have hgj : fullArgList[j + 1]? = some (some (v₂, av₂, ft₂)) := by rw [hFullEq]; exact hg₂
                have hv₁ := (hArgListOpen.1 (i + 1) v₁ av₁ ft₁ hgi).1
                have hv₂ := (hArgListOpen.1 (j + 1) v₂ av₂ ft₂ hgj).1
                have h0 := hArgListOpen.2 (i + 1) (j + 1) v₁ v₂ av₁ av₂ ft₁ ft₂ (by omega) hgi hgj
                exact ⟨fun ha₁ htr₁ ha₂ hdd l hor₁ hr₂ =>
                    have hp₁ := hpresRestActive i v₁ av₁ ft₁ hg₁ (ActiveVal.of_AStateLe hok₁ hlePush (fun d hd => hszSt₁ ▸ hv₁.2.1 d hd) (fun z hz => hszSt₁ ▸ (hv₁.2.2.1 z hz).1) ha₁)
                    have hp₂ := hpresRestActive j v₂ av₂ ft₂ hg₂ (ActiveVal.of_AStateLe hok₁ hlePush (fun d hd => hszSt₁ ▸ hv₂.2.1 d hd) (fun z hz => hszSt₁ ▸ (hv₂.2.2.1 z hz).1) ha₂)
                    h0.1 (ActiveVal.of_AStateLe hokOpen hle1P hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) ha₁)
                      (Transferable.of_AStateLe hokOpen hle1P hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) (fun _ h => h) htr₁)
                      (ActiveVal.of_AStateLe hokOpen hle1P hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂) hdd l
                      ((OwnReach_congr hp₁ l).mp hor₁) ((Reach_congr hp₂ l).mp hr₂),
                  fun ha₁ hf₁ ha₂ hne l hft hr₂ =>
                    have hp₂ := hpresRestActive j v₂ av₂ ft₂ hg₂ (ActiveVal.of_AStateLe hok₁ hlePush (fun d hd => hszSt₁ ▸ hv₂.2.1 d hd) (fun z hz => hszSt₁ ▸ (hv₂.2.2.1 z hz).1) ha₂)
                    h0.2 (ActiveVal.of_AStateLe hokOpen hle1P hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) ha₁)
                      (FootActive.of_AStateLe hokOpen hle1P hv₁.2.1 (fun z hz => (hv₁.2.2.1 z hz).1) hf₁)
                      (ActiveVal.of_AStateLe hokOpen hle1P hv₂.2.1 (fun z hz => (hv₂.2.2.1 z hz).1) ha₂) hne l hft
                      ((Reach_congr hp₂ l).mp hr₂)⟩
            -- Lift `hRestMeta` across `st_open → st₂` using `hNonCons` for `fc = true`!
            have hRestMeta : ∀ (idx : Nat) v er_c a1 er_a fc,
                restC[idx]? = some (v, er_c) → rest[idx]? = some (a1, er_a, fc) →
                er_c = er_a ∧ a1.src = none ∧
                (er_a = false → fc = true → a1.onceOnly = false ∧ a1.cls = .val ∧ a1.skel = .unknown ∧
                  ValBaseOk st₂ v ∧ CtorFieldsOk P ext b0 st₂ v ∧ NoOnceCell st₂.heap v ∧
                  FunOkAt P ext b0 st₂ .unknown false (fun (_ : Nat) => False) v) := by
              intro idx v er_c a1 er_a fc hc ha
              obtain ⟨h1, h2, h3⟩ := hArgsMeta (idx + 1) v er_c a1 er_a fc hc ha
              refine ⟨h1, h2, fun herF hfc => ?_⟩
              obtain ⟨a_1, a_2, a_3, hbv, hcf, hno, hfun⟩ := h3 herF hfc
              have hbvO : ValBaseOk st_open v := ValBaseOk_congr (st := st) (st' := st_open) (PreservesLocs.refl _ _) hrfOpen.1 hbv
              have hgkIdx : restArgList[idx]? = some (some (v, a1, fun (_ : Nat) => False)) := by
                have hltC : idx < restC.length := (List.getElem?_eq_some_iff.mp hc).1
                have hltR : idx < rest.length := (List.getElem?_eq_some_iff.mp ha).1
                have hltZ : idx < (restC.zip rest).length := by rw [List.length_zip, Nat.lt_min]; exact ⟨hltC, hltR⟩
                simp only [restArgList, List.getElem?_map, List.getElem?_eq_getElem hltZ, List.getElem_zip]
                have h1' : restC[idx]'hltC = (v, er_c) := by have := List.getElem?_eq_getElem hltC; rw [this] at hc; exact Option.some.inj hc
                have h2' : rest[idx]'hltR = (a1, false, true) := by
                  have := List.getElem?_eq_getElem hltR; rw [this] at ha
                  have hEq := Option.some.inj ha; rw [hEq, herF, hfc]
                rw [h1', h2']; rfl
              have hpresV : PreservesLocs (Reach st_open.heap v) st_open.heap st₂.heap := by
                  by_cases hu : p.mode.isUnique = true
                  · have hpNe : p.mode ≠ .erased := by cases hm' : p.mode <;> rw [hm'] at hu <;> simp [BinderMode.isUnique] at hu ⊢
                    by_cases hclr : (fromCell && p.cls != .val) = true
                    · have hfc0 : fromCell = true := (Bool.and_eq_true_iff.mp hclr).1
                      have ha0Cls : a0.cls = .val := (ha0FcMeta rfl hfc0).2.1
                      have ha0Own : a0.own = .uniq := by
                        have h' := ((huniq₁ hu).2 (by simp [a0', hclr, ha0Cls])).1
                        simpa [a0', hclr] using h'
                      have ha1DepsNil : a1.deps = [] := Classical.byContradiction fun hne => by
                        have hsh := hNonCons a1 false true (List.mem_cons_of_mem _ (herF ▸ hfc ▸ List.mem_of_getElem? ha))
                          rfl rfl hne a0 false fromCell List.mem_cons_self rfl ha0Cls
                        rw [ha0Own] at hsh; cases hsh
                      have ha1Act : ActiveVal σ₁ a1 := ⟨(by rw [ha1DepsNil]; intro _ h; cases h), fun ⟨_, hs, _⟩ => by rw [h2] at hs; cases hs⟩
                      exact hpresRestActive idx v a1 (fun (_ : Nat) => False) hgkIdx ha1Act
                    · have hclrF : (fromCell && p.cls != .val) = false := Bool.eq_false_iff.mpr hclr
                      obtain ⟨haInEq, hstInEq⟩ := hnoClrEq hclrF; subst a_in; subst st_in
                      have ha0'Eq : a0' = a0 := by simp [a0', hclrF]
                      by_cases ha0V : a0.cls = .val
                      · have ha0Own : a0.own = .uniq := by
                          have h' := ((huniq₁ hu).2 (ha0'Eq.symm ▸ ha0V)).1
                          rwa [ha0'Eq] at h'
                        have ha1DepsNil : a1.deps = [] := Classical.byContradiction fun hne => by
                          have hsh := hNonCons a1 false true (List.mem_cons_of_mem _ (herF ▸ hfc ▸ List.mem_of_getElem? ha))
                            rfl rfl hne a0 false fromCell List.mem_cons_self rfl ha0V
                          rw [ha0Own] at hsh; cases hsh
                        have ha1Act : ActiveVal σ₁ a1 := ⟨(by rw [ha1DepsNil]; intro _ h; cases h), fun ⟨_, hs, _⟩ => by rw [h2] at hs; cases hs⟩
                        exact hpresRestActive idx v a1 (fun (_ : Nat) => False) hgkIdx ha1Act
                      · have hvdA0 : ValidDeps σ_open a0.deps := ha0'Eq ▸ hvdA₁ hpNe
                        have hnotOnceA0 : ¬ IsOnceSrc σ_open a0 := fun ⟨_, hs, _⟩ => by rw [ha0Src] at hs; cases hs
                        have hnvA0 := (hvA0.2.2.2.2 ⟨hvdA0, fun his => absurd his hnotOnceA0⟩).2.2.2.1 hnotOnceA0 ha0V
                        exact hpresBindOut.mono fun l hr => ⟨hbvO.1.reach_lt_size hr, fun _ hor => hnvA0.ownTreeFull.2 l hor⟩
                  · have hnu : p.mode.isUnique = false := Bool.eq_false_iff.mpr hu
                    exact (hpresIn.mono fun _ hr => hbvO.1.reach_lt_size hr).trans
                      (hpresBindOut.mono fun l hr => ⟨Nat.lt_of_lt_of_le (hbvO.1.reach_lt_size hr) hszIn,
                        fun hu' => by rw [hnu] at hu'; cases hu'⟩)
              exact ⟨a_1, a_2, a_3, ValBaseOk_congr hpresV hrfOpen2.1 hbvO,
                CtorFieldsOk_congr hbvO.1 hpresV hrfOpen2 (CtorFieldsOk_congr hbv.1 (PreservesLocs.refl _ _) hrfOpen (CtorFieldsOk_mono (by omega) hcf)),
                NoOnceCell_congr hbvO.1 hpresV hno,
                FunOkAt_preserve_locs (st₀ := st_open) (st₁ := st₂) hpresV hrfOpen2
                  (FunOkAt_preserve_locs (st₀ := st) (st₁ := st_open) (PreservesLocs.refl _ _) hrfOpen (FunOkAt_mono (by omega) hfun))⟩
            have hstat₂F : ∀ l, StaticStrLoc st₂ l → Frame l := fun l hss =>
              hstat l (StaticStrLoc_of_preserves_outside (hstat₂.trans hstatIn)
                (hstr₂.trans hstrIn) hpresSSAll2 l hss)
            have hFlt₂ : ∀ l, Frame l → l < st₂.heap.objs.size := fun l hF =>
              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hFlt l hF) hszIn) hsz₂
            have hForbLt₂ : ∀ l, Forbid l → l < st₂.heap.objs.size := fun l hF =>
              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hForbidLt l hF) hszIn) hsz₂
            have hHeadRegPush : st₂.regions.headD 0 = 0 ∨ st₂.regions.headD 0 ∈ I_open.reg (σ_push.regions.headD 1) := by
              right; rw [hrg₂, hrgIn]; simp only [st_open, σ_push, AState.pushBnd, hσreg₁, List.headD]
              rw [hIopenSa]; exact List.mem_cons_self
            obtain ⟨hnoVA, hokA⟩ := haltIH hlcB hcfdB (B₀ := b0) (fuel := n) (by omega)
              (shiftScope_of_freeVarIn fun z hz => hfv z (.lam hz))
              hst₂ hsimP hstat₂F hFlt₂ hnk₂ hnsp₂ hIopenZero hHeadRegPush henvTaintP henvNRFP
              hForbLt₂ hBadDepP₂ (by simpa using hlen)
              (fun a_d er_d fc_d hm1 he1 hfc1 hnd1 a1 er1 fc1 hm2 he2 hcv2 =>
                hNonCons a_d er_d fc_d (List.mem_cons_of_mem _ hm1) he1 hfc1 hnd1 a1 er1 fc1 (List.mem_cons_of_mem _ hm2) he2 hcv2)
              hRestMeta hRestArgList
            rw [MS_bind_run]
            cases hevA : (applyAltS P ext n (bnd :: env) body restC).run (st₂, b0) with
            | error e =>
              refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
            | ok pa =>
              rcases pa with ⟨rv_b, ⟨st₃, B₃⟩⟩; dsimp only
              obtain ⟨rvFoot, hB₃, hst₃, hsz₃, hcap₃, hr₃, hnr₃, hstat₃, hstr₃,
                hpFrame₃, hpEnv₃, hpNum₃, honce₃, hssf₃, hsim₃, _, henvNRF₃,
                hvR₃, hdisjR₃, hnrfR₃, _, _, _, hsrcR₃⟩ := hokA rv_b st₃ B₃ hevA
              have hsaNe1 : s_a ≠ 1 := by have := hok.2.2.1; change σ.nextRegion ≠ 1; omega
              have hcurLt : cur < st₃.nextRegion := by
                have h1 : st_open.nextRegion = s_c + 1 := rfl
                have h2 : st₂.nextRegion = s_c + 1 := hnr₂.trans (hnrIn.trans h1)
                cases hcr : st.regions with
                | nil => simp only [cur, hcr, List.headD]; omega
                | cons c0 cs =>
                  simp only [cur, hcr, List.headD]
                  have hc0 := (hst.2.1.2.2 c0 (hcr ▸ List.mem_cons_self)).2; omega
              have hregClose : (σ₃.closeReg s_a).regions = σ.regions := by
                change σ₃.regions.filter (· != s_a) = σ.regions
                rw [hσreg₃, hreg₂]; change σ₁.regions.filter (· != s_a) = σ.regions
                rw [hσreg₁]
                have hne : ∀ rg ∈ σ.regions, (rg != s_a) = true := fun rg hrg =>
                  bne_iff_ne.mpr (Nat.ne_of_lt (hok.2.2.2.2.2 rg hrg).2)
                simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                exact List.filter_eq_self.mpr hne
              have hcurIn : cur = 0 ∨ cur ∈ I_open.reg ((σ₃.closeReg s_a).regions.headD 1) := by
                rw [hregClose]
                rcases hHeadReg with h0 | hIn
                · exact Or.inl h0
                · right
                  have hhdLt : σ.regions.headD 1 < s_a := by
                    cases hrg : σ.regions with
                    | nil => simp only [List.headD]; have := hok.2.2.1; change 1 < σ.nextRegion; omega
                    | cons hd tl => simp only [List.headD]; exact (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2
                  rw [hIopenLt _ hhdLt]; exact hIn
              have hrgFilt3 : st₃.regions.filter (· != s_c) = st.regions := by
                rw [hr₃, hrg₂, hrgIn]; dsimp only [st_open]
                have hne : ∀ rg ∈ st.regions, (rg != s_c) = true := fun rg hrg =>
                  bne_iff_ne.mpr (Nat.ne_of_lt (hst.2.1.2.2 rg hrg).2)
                simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                exact List.filter_eq_self.mpr hne
              have hIokClose0 : InterpOk (σ₃.closeReg s_a) { st₃ with regions := st₃.regions.filter (· != s_c) } I_open := by
                refine ⟨fun rg hlt c hc => hsim₃.2.2.1.1 rg (hσnr₃ ▸ hlt) c hc, fun c hc => ?_⟩
                have hhdLt : σ.regions.headD 1 < s_a := by
                  cases hrg : σ.regions with
                  | nil => simp only [List.headD]; have := hok.2.2.1; change 1 < σ.nextRegion; omega
                  | cons hd tl => simp only [List.headD]; exact (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2
                rw [hregClose, hIopenLt _ hhdLt]
                dsimp only at hc; rw [hrgFilt3] at hc; exact hsim.2.2.1.2 c hc
              have hregU₂ : RegUnique I_open σ₂ s_a s_c := RegUnique_extend_of_zero hIZero hsim.2.2.1.1
              have hsIn₃ : s_c ∈ st₃.regions := by rw [hr₃, hrg₂, hrgIn]; exact List.mem_cons_self
              have hFlt₃ : ∀ l, Frame l → l < st₃.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hFlt₂ l hF) hsz₃
              have hForbLt₃ : ∀ l, Forbid l → l < st₃.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbLt₂ l hF) hsz₃
              rcases retCheck_altRetVal_bridge (fuel := n) (s_a := s_a) (s_c := s_c) (cur := cur)
                  hst₃ hsim₃ henvNRF₃ hFlt₃ hForbLt₃ hnk₃ hBadDepP₃ hNotBadS hsaNe1 hcurLt hcurIn
                  hIokClose0 hregU₂ hsIn₃ hvR₃ hdisjR₃ hnrfR₃ hretChk with hStR | hOOFR |
                ⟨rv', st_ret, hrunR, hrgR, hnrR, hstatR, hstrR, hszR, hcapR,
                 hpFrameR, hpSSR, honceR, hssfR, hstClose, hsimClose, henvNRFClose,
                 hvClose, hdisjClose, hnrfClose⟩
              · rw [MS_bind_run, MS_liftM_run, hStR]
                exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              · rw [MS_bind_run, MS_liftM_run, hOOFR]
                exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
              · rw [MS_bind_run, MS_liftM_run, hrunR]; dsimp only
                let st_close : St := { st_ret with regions := st_ret.regions.filter (· != s_c) }
                have hcloseRun : (closeRegion s_c).run st_ret = .ok ((), st_close) := rfl
                rw [MS_bind_run, MS_liftM_run, hcloseRun]; dsimp only
                rw [MS_pure_run]
                refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
                cases hokEq
                have hrgCloseC : st_close.regions = st.regions := by
                  dsimp only [st_close]; rw [hrgR, hrgFilt3]
                obtain ⟨hpEnvR, hpNumR⟩ := ret_preserves_env_num hst₃ hsim₃ hnk₃ hregU₂ hsIn₃ hvR₃ hdisjR₃ hretChk hrunR
                have hIokCloseI : InterpOk (σ₃.closeReg s_a) st_close I := by
                  refine ⟨fun rg hlt c hc => ?_, fun c hc => ?_⟩
                  · by_cases hltSa : rg < s_a
                    · rw [← hIopenLt rg hltSa] at hc; exact hsimClose.2.2.1.1 rg hlt c hc
                    · rw [hIZero rg (Nat.le_of_not_lt hltSa)] at hc; cases hc
                  · rw [hregClose]; rw [hrgCloseC] at hc; exact hsim.2.2.1.2 c hc
                have hsimPopOpen : Sim P ext B₃ st_close Frame NoKill NoSpend Scope env aenv (σ₃.closeReg s_a) I_open envFoot := by
                  obtain ⟨hlenC, hokC, hIokC, hidsC, huniqC, hbndsC, hdisjC⟩ := hsimClose
                  refine ⟨by simpa using hlenC, hokC, hIokC,
                    fun i ab' hab' => hidsC (i + 1) ab' hab',
                    fun i j ab₁ ab₂ h1 h2 hid => Nat.succ.inj (huniqC (i + 1) (j + 1) ab₁ ab₂ h1 h2 hid),
                    fun i b' ab' hsc' hbi' habi' => hbndsC (i + 1) b' ab' hsc' hbi' habi',
                    fun i j b₁ b₂ ab₁ ab₂ hij hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂ =>
                      hdisjC (i + 1) (j + 1) b₁ b₂ ab₁ ab₂ (by omega) hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂⟩
                have hsimFinal : Sim P ext B₃ st_close Frame NoKill NoSpend Scope env aenv (σ₃.closeReg s_a) I envFoot :=
                  Sim_interp_congr_ne (s_a := s_a) hIokCloseI (fun rg hne => by simp [I_open, Interp.extend, hne])
                    (fun i ab' hsc' hab' hne' hmem => by
                      have hiE : i < env.length := by rw [hsim.1]; exact (List.getElem?_eq_some_iff.mp hab').1
                      exact Nat.lt_irrefl _ (((hsim.2.2.2.2.2.1 i env[i] ab' hsc' (List.getElem?_eq_getElem hiE) hab').2 hne').2.1 s_a hmem))
                    hsimPopOpen
                let arv := altRetVal res rc s_a ((σ₃.closeReg s_a).regions.headD 1) r
                have harvNotSa : s_a ∉ arv.regs := by
                  intro hmem; dsimp only [arv, altRetVal] at hmem
                  by_cases hnv : (rc == .irr || rc == .imm || rc == .leaf) = true
                  · simp only [hnv, ↓reduceIte] at hmem; cases hmem
                  · simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hmem
                    by_cases hb : (res.isBorrowed && r.regs.contains s_a) = true
                    · simp only [hb, ↓reduceIte, mem_natUnion, List.mem_filter, List.mem_singleton] at hmem
                      rcases hmem with ⟨_, hne⟩ | hEq
                      · simp at hne
                      · rw [hregClose] at hEq
                        cases hrg : σ.regions with
                        | nil => rw [hrg] at hEq; simp only [List.headD] at hEq; have := hok.2.2.1; change σ.nextRegion = 1 at hEq; omega
                        | cons hd tl =>
                          rw [hrg] at hEq; simp only [List.headD] at hEq
                          exact Nat.lt_irrefl _ (hEq ▸ (hok.2.2.2.2.2 hd (hrg ▸ List.mem_cons_self)).2)
                    · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hmem; simp at hmem
                have hvFinal : VSim P ext B₃ st_close Frame NoKill NoSpend (σ₃.closeReg s_a) I (fun (_ : Nat) => False) arv rv' :=
                  VSim_interp_congr (fun rg hrg => by
                    have hne : rg ≠ s_a := fun hEq => harvNotSa (hEq ▸ hrg)
                    simp [I_open, Interp.extend, hne]) hvClose
                have hdisjFinal : ValEnvDisj P st_close NoKill Scope env aenv (σ₃.closeReg s_a) envFoot (fun (_ : Nat) => False) arv rv' :=
                  fun i b' ab' hsc' hbi' habi' hne' => hdisjClose (i + 1) b' ab' hsc' hbi' habi' hne'
                have henvNRFFinal : EnvNoReachForbid st_close Scope env aenv (σ₃.closeReg s_a) Forbid BadReg BadDep :=
                  fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
                    henvNRFClose (i + 1) b' ab' hsc' hbi' habi' hne' ha'
                      (fun rg hrg hbr => hregs rg hrg hbr.2) (fun dep hdep hbd => hdeps dep hdep hbd.2)
                have hnrfFinal : ActiveVal (σ₃.closeReg s_a) arv → NoReachForbid st_close Forbid BadReg BadDep arv rv' :=
                  fun ha' hregs hdeps => hnrfClose ha'
                    (fun rg hrg hbr => hregs rg hrg hbr.2) (fun dep hdep hbd => hdeps dep hdep hbd.2)
                have hpresEnvAll : PreservesActiveEnv Scope env aenv (σ₃.closeReg s_a) st.heap st_close.heap := by
                  intro i b' ab' hsc' hbi' habi' hne' haEnd
                  have hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
                  have ha₂ := ActiveVal.of_AStateLe hok₂ (hle₃.trans hleClose)
                    (fun d hd => Nat.lt_of_lt_of_le (hvI.2.1 d hd) (hleOpen.trans (hle₁.trans (hlePush.trans hle₂))).1)
                    (fun z hz => Nat.lt_of_lt_of_le (hvI.2.2.1 z hz).1 (hleOpen.trans (hle₁.trans (hlePush.trans hle₂))).1) haEnd
                  have ha₁ := ActiveVal.of_AStateLe hok₁ (hlePush.trans hle₂)
                    (fun d hd => hszSt₁ ▸ hvI.2.1 d hd) (fun z hz => hszSt₁ ▸ (hvI.2.2.1 z hz).1) ha₂
                  have hp1 := hpresEnv₂ i b' ab' hsc' hbi' habi' hne' ha₁
                  have hp2 := hpEnv₃ (i + 1) b' ab' hsc' hbi' habi' hne' ha₂
                  have hp3 := hpEnvR (i + 1) b' ab' hsc' hbi' habi' hne' haEnd
                  have hp12 : PreservesLocs (Reach st.heap b'.val) st.heap st₃.heap :=
                    hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
                  exact hp12.trans (hp3.mono fun l hr => (Reach_congr hp12 l).mpr hr)
                have harvNotOnce : ¬ IsOnceSrc (σ₃.closeReg s_a) arv := by
                  rintro ⟨id, hsrc, ho⟩
                  dsimp only [arv, altRetVal] at hsrc
                  by_cases hu : (res.isUnique && rc == .val) = true
                  · simp only [hu, ↓reduceIte] at hsrc; cases hsrc
                  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hsrc
                    exact hnotOnceR₂ ⟨id, hsrc, hσonce₃ ▸ ho⟩
                have harvAct : ActiveVal (σ₃.closeReg s_a) arv := by
                  refine ⟨?_, fun his => absurd his harvNotOnce⟩
                  dsimp only [arv, altRetVal]
                  by_cases hu : (res.isUnique && rc == .val) = true
                  · simp only [hu, ↓reduceIte]; exact fun _ h => by cases h
                  · simp only [hu, Bool.false_eq_true, ↓reduceIte]
                    intro d hd
                    refine ⟨hstSz₃ ▸ (hvdR₂ d hd).1, fun hdead => ?_⟩
                    have hstUpd := (Runs_retCheck hok₂ hretChk).2.2.2.2.2.2.2.2.2.2.2.2 d (hvdR₂ d hd).1
                    have hcondF : ¬ (rc = .val ∧ res.isUnique = true ∧ d ∈ r.deps) := by
                      rintro ⟨rfl, hru, _⟩
                      exact hu (by simp [hru, show (Cls.val == Cls.val) = true from rfl])
                    simp only [hcondF, ↓reduceIte] at hstUpd
                    exact (hvdR₂ d hd).2 (hstUpd ▸ hdead)
                have hsrcFinal : SrcOk Scope aenv σ (σ₃.closeReg s_a) arv := by
                  intro id hrs
                  dsimp only [arv, altRetVal] at hrs
                  by_cases hu : (res.isUnique && rc == .val) = true
                  · simp only [hu, ↓reduceIte] at hrs; cases hrs
                  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hrs
                    have harvDeps : arv.deps = r.deps := by dsimp only [arv, altRetVal]; simp [hu]
                    rcases hsrcR₃ id hrs with ⟨i, ab', hsc', hab', hne', hid', hoo', hdeps'⟩ | ⟨hgeP, hspP⟩
                    · cases i with
                      | succ k => exact Or.inl ⟨k, ab', hsc', hab', hne', hid', hoo', fun d => by rw [harvDeps]; exact hdeps' d⟩
                      | zero =>
                        simp at hab'; subst hab'; dsimp only at hid'
                        right
                        refine ⟨by omega, fun hoId dep hdep hlt0 hoDep => ?_⟩
                        have hdepEff := (hdeps' dep).mp (harvDeps ▸ hdep)
                        have hneDepId : dep ≠ id := by omega
                        have hdepBv : dep ∈ bv.deps := by
                          simp only [effVal, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hdepEff
                          rcases hdepEff with rfl | ⟨h1, _⟩
                          · exact absurd hid'.symm hneDepId.symm
                          · exact h1
                        have hdepA0' : dep ∈ a0'.deps := Runs_bindInner_deps_mem hokOpen hbind' dep hdepBv
                        have hmOnce : p.mode.usage = .once := by
                          have hltP : id < σ_push.once.size := by
                            simp only [σ_push, AState.pushBnd, Array.size_push]; have := hok₁.1; omega
                          have hoP : σ_push.once[id]? = some true := by
                            change σ₃.once[id]? = some true at hoId; rw [hσonce₃] at hoId
                            have h1 := hle₂.2.2.2.1 id hltP; rw [h1] at hoId; exact hoId
                          have hszO : σ₁.once.size = σ₁.st.size := hok₁.1.symm
                          simp only [σ_push, AState.pushBnd, ← hid', ← hszO, Array.getElem?_push_size] at hoP
                          exact beq_iff_eq.mp (Option.some.inj hoP)
                        have hltSp0 : dep < σ_open.spent.size := by have := hok.2.1; change dep < σ.spent.size; omega
                        have hoOpen : σ_open.once[dep]? = some true := by
                          have hltO1 : dep < σ₁.once.size := by have := hok₁.1; omega
                          have hltOP : dep < σ_push.once.size := by simp [σ_push, AState.pushBnd]; omega
                          change σ₃.once[dep]? = some true at hoDep; rw [hσonce₃] at hoDep
                          have h1 := hle₂.2.2.2.1 dep hltOP
                          have h2 := hlePush.2.2.2.1 dep hltO1
                          change σ.once[dep]? = some true
                          rw [← hσonce₁, ← h2, ← h1]; exact hoDep
                        have hsp1 : σ₁.spent[dep]? = some true := by
                          have h1 := hspUpd₁ dep hltSp0
                          simp only [hmOnce, or_true, hdepA0', hoOpen, and_self, ↓reduceIte] at h1; exact h1
                        have hspP' : σ_push.spent[dep]? = some true :=
                          hlePush.2.2.2.2 dep (Array.getElem?_eq_some_iff.mp hsp1).1 hsp1
                        change σ₃.spent[dep]? = some true; rw [hσsp₃]
                        exact hle₂.2.2.2.2 dep (Array.getElem?_eq_some_iff.mp hspP').1 hspP'
                    · right
                      have hle0P : σ.st.size ≤ σ_push.st.size := (hleOpen.trans (hle₁.trans hlePush)).1
                      refine ⟨Nat.le_trans hle0P hgeP, fun hoId dep hdep hlt0 hoDep => ?_⟩
                      change σ₃.spent[dep]? = some true; rw [hσsp₃]
                      exact hspP (hσonce₃ ▸ hoId) dep (harvDeps ▸ hdep) (Nat.lt_of_lt_of_le hlt0 hle0P) (hσonce₃ ▸ hoDep)
                have hnvFinal : ValidDeps (σ₃.closeReg s_a) arv.deps → arv.cls ≠ .val →
                    ValBaseOk st_close rv' ∧ NonValSafe st_close.heap rv' := fun _ hne =>
                  ⟨(hvFinal.2.2.2.2 harvAct).1, (hvFinal.2.2.2.2 harvAct).2.2.2.1 harvNotOnce hne⟩
                have htaintFinal : ValidDeps (σ₃.closeReg s_a) arv.deps →
                    (∀ c ∈ rv'.taint, c < st_close.nextRegion) ∧ OpenUnder st_close.regions (I.regsOf arv.regs) rv' := fun _ =>
                  let hvA := hvFinal.2.2.2.2 harvAct
                  ⟨fun c hc => hvA.1.2.2.2 rv' (HeldBy.refl _ _) c hc, hvA.2.1 rv' (HeldBy.refl _ _)⟩
                have hpresSS3 : PreservesLocs (StaticStrLoc st₂) st₂.heap st₃.heap :=
                  hpFrame₃.mono fun l hss => hstat₂F l hss
                have hssf03 : StaticStrFresh st_open st₃ :=
                  StaticStrFresh.trans (Nat.le_trans hszIn hsz₂) hpresSS3 hssfOpen2 hssf₃
                have hstatFinal : ArrayExtends st.statics st_close.statics := by
                  change ArrayExtends st_open.statics st_ret.statics
                  rw [hstatR, ← hstatIn, ← hstat₂]; exact hstat₃
                have hstrFinal : ArrayExtends st.strs st_close.strs := by
                  change ArrayExtends st_open.strs st_ret.strs
                  rw [hstrR, ← hstrIn, ← hstr₂]; exact hstr₃
                exact ⟨fun (_ : Nat) => False, by omega, hstClose,
                  Nat.le_trans hszIn (Nat.le_trans hsz₂ (Nat.le_trans hsz₃ hszR)),
                  Nat.le_trans hcapIn (Nat.le_trans hcap₂ (Nat.le_trans hcap₃ hcapR)),
                  hrgCloseC,
                  by have : st_open.nextRegion = s_c + 1 := rfl; have : st₂.nextRegion = s_c + 1 := hnr₂.trans (hnrIn.trans this)
                     have : st_close.nextRegion = st_ret.nextRegion := rfl; omega,
                  hstatFinal, hstrFinal,
                  hpresF2.trans (hpFrame₃.trans hpFrameR), hpresEnvAll,
                  fun l o num ho hc => hpNumR l o num (hpNum₃ l o num (hpresNum₂ l o num ho hc) hc) hc,
                  honceOpen2.trans (honce₃.trans honceR),
                  StaticStrFresh.trans (Nat.le_trans (Nat.le_trans hszIn hsz₂) hsz₃) hpSSR hssf03 hssfR,
                  hsimFinal,
                  henvTaint.step hrgCloseC (by
                    have : st_open.nextRegion = s_c + 1 := rfl; have : st₂.nextRegion = s_c + 1 := hnr₂.trans (hnrIn.trans this)
                    have : st_close.nextRegion = st_ret.nextRegion := rfl; omega),
                  henvNRFFinal, hvFinal, hdisjFinal, hnrfFinal, hnvFinal, htaintFinal,
                  Or.inl ⟨(hvFinal.2.2.2.2 harvAct).1, (hvFinal.2.2.2.2 harvAct).2.2.1⟩, hsrcFinal⟩

private theorem caseField_deps_sub {P : Prog} {k : CaseInfo} {fields : Array Field}
    {mv : AVal} {consuming : Bool} {q : Nat} {a0 : AVal} {er_a fc : Bool}
    (hEq : caseField P k fields mv consuming q = (a0, er_a, fc)) :
    ∀ d ∈ a0.deps, d ∈ mv.deps := by
  unfold caseField at hEq
  by_cases hnat : (some k.ind == P.nat) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hnat)] at hEq; cases hEq; exact fun _ h => by cases h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hnat)] at hEq
    cases hf : fields[q]? with
    | none => rw [hf] at hEq; cases hEq; exact fun _ h => by cases h
    | some f =>
      rw [hf] at hEq; dsimp only at hEq
      by_cases h1 : (f.mode == .erased) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hEq; cases hEq; exact fun _ h => by cases h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hEq
        by_cases h2 : (f.cls == .irr) = true
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at hEq; cases hEq; exact fun _ h => by cases h
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at hEq
          by_cases h3 : (mv.cls != .val && P.wrapperField? k.ind == some q) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)] at hEq; cases hEq; exact fun _ h => h
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)] at hEq
            by_cases h4 : (f.cls != .val) = true
            · rw [ite_eq_left_of_eq_true _ _ (eq_true h4)] at hEq; cases hEq; exact fun _ h => by cases h
            · rw [ite_eq_right_of_eq_false _ _ (eq_false h4)] at hEq
              by_cases h5 : (f.fmode == .shared) = true
              · rw [ite_eq_left_of_eq_true _ _ (eq_true h5)] at hEq; cases hEq; exact fun _ h => h
              · rw [ite_eq_right_of_eq_false _ _ (eq_false h5)] at hEq
                cases consuming with
                | true => simp at hEq; rcases hEq with ⟨rfl, _, _⟩; exact fun _ h => by cases h
                | false => simp at hEq; rcases hEq with ⟨rfl, _, _⟩; exact fun _ h => h

private theorem caseField_nonCons_own_shared {P : Prog} {k : CaseInfo} {fields : Array Field}
    {mv : AVal} {q : Nat} {a0 : AVal} {er0 fc0 : Bool}
    (hEq : caseField P k fields mv false q = (a0, er0, fc0)) (ha0V : a0.cls = .val) :
    a0.own = .shared := by
  unfold caseField at hEq
  by_cases hnat : (some k.ind == P.nat) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hnat)] at hEq; cases hEq; cases ha0V
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hnat)] at hEq
    cases hf : fields[q]? with
    | none => rw [hf] at hEq; cases hEq; cases ha0V
    | some f =>
      rw [hf] at hEq; dsimp only at hEq
      by_cases h1 : (f.mode == .erased) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hEq; cases hEq; cases ha0V
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hEq
        by_cases h2 : (f.cls == .irr) = true
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at hEq; cases hEq; cases ha0V
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at hEq
          by_cases h3 : (mv.cls != .val && P.wrapperField? k.ind == some q) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)] at hEq
            have hmvNe : mv.cls ≠ .val := by
              have h1' := (Bool.and_eq_true_iff.mp h3).1
              intro hV; rw [hV] at h1'; cases h1'
            cases hEq; exact absurd ha0V hmvNe
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)] at hEq
            by_cases h4 : (f.cls != .val) = true
            · rw [ite_eq_left_of_eq_true _ _ (eq_true h4)] at hEq
              have hfNe : f.cls ≠ .val := by intro hV; rw [hV] at h4; cases h4
              cases hEq; exact absurd ha0V hfNe
            · rw [ite_eq_right_of_eq_false _ _ (eq_false h4)] at hEq
              by_cases h5 : (f.fmode == .shared) = true
              · rw [ite_eq_left_of_eq_true _ _ (eq_true h5)] at hEq; cases hEq; rfl
              · rw [ite_eq_right_of_eq_false _ _ (eq_false h5)] at hEq; simp at hEq; rcases hEq with ⟨rfl, _, _⟩; rfl

theorem caseAltArgs_deps_sub {P : Prog} {k : CaseInfo} {mv : AVal} {consuming : Bool}
    {cidx : Nat} {ca : CaseAlt} {a0 : AVal} {er_a fc : Bool}
    (hmem : (a0, er_a, fc) ∈ caseAltArgs P k mv consuming cidx ca) :
    ∀ d ∈ a0.deps, d ∈ mv.deps := by
  unfold caseAltArgs at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨fa, _, hEq⟩
  cases fa with
  | irr => simp at hEq; rcases hEq with ⟨rfl, _, _⟩; exact fun _ h => by cases h
  | unit => simp at hEq; rcases hEq with ⟨rfl, _, _⟩; exact fun _ h => by cases h
  | field q => exact caseField_deps_sub hEq

theorem caseAltArgs_nonCons {P : Prog} {k : CaseInfo} {mv : AVal} {consuming : Bool}
    {cidx : Nat} {ca : CaseAlt}
    (hconsDeps : consuming = true → mv.deps = []) :
    ∀ a_d er_d fc_d, (a_d, er_d, fc_d) ∈ caseAltArgs P k mv consuming cidx ca →
      er_d = false → fc_d = true → a_d.deps ≠ [] →
      ∀ a0 er0 fc0, (a0, er0, fc0) ∈ caseAltArgs P k mv consuming cidx ca →
        er0 = false → a0.cls = .val → a0.own = .shared := by
  intro a_d er_d fc_d hmemD _ _ hneD a0 er0 fc0 hmem0 _ ha0V
  have hconsF : consuming = false := by
    cases hc : consuming with
    | false => rfl
    | true =>
      exfalso; apply hneD
      have hsub := caseAltArgs_deps_sub hmemD
      rw [hconsDeps hc] at hsub
      cases hd : a_d.deps with
      | nil => rfl
      | cons x xs => exact False.elim (by cases hsub x (hd ▸ List.mem_cons_self))
  subst hconsF
  unfold caseAltArgs at hmem0
  simp only [List.mem_map] at hmem0
  rcases hmem0 with ⟨fa, _, hEq⟩
  cases fa with
  | irr => simp at hEq; rcases hEq with ⟨rfl, _, _⟩; cases ha0V
  | unit => simp at hEq; rcases hEq with ⟨rfl, _, _⟩; cases ha0V
  | field q => exact caseField_nonCons_own_shared hEq ha0V

theorem AApps_src_none {f : AVal} {xs : List AVal} {c : Cls} {σ σ' : AState} {r : AVal}
    (hok : AStateOk σ) (hf : f.src = none) (h : AApps f xs c σ r σ') : r.src = none := by
  induction h with
  | nil => exact hf
  | consLast hr =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsrc, _⟩ := Runs_applyValue hok hr
    exact hsrc
  | consMore hr _ ih =>
    obtain ⟨hok₁, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsrc, _⟩ := Runs_applyValue hok hr
    exact ih hok₁ hsrc

private theorem AEvals_length_eval {P : Prog} {aenv : List ABnd} :
    ∀ {ts : List Term} {σ σ' : AState} {avs : List AVal},
      AEvals P aenv ts σ avs σ' → avs.length = ts.length
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ hrest => by simp [AEvals_length_eval hrest]

theorem VSim_restrict_nk_nsp {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop} {σ : AState} {I : Interp} {Foot : Nat → Prop}
    {av : AVal} {v : Val}
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot av v) :
    VSim P ext B st Frame (fun d => d < σ.st.size ∧ NoKill d)
      (fun d => d < σ.st.size ∧ NoSpend d) σ I Foot av v := by
  refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, fun ha => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hv.2.2.2.2 ha
  refine ⟨b1, b2, b3, b4, b5,
    (fun hoo => let ⟨q1, q2, q3, q4⟩ := b6 hoo
      ⟨q1, fun hnk => q2 fun x hx hnk0 => hnk x hx ⟨(hv.2.2.1 x hx).1, hnk0⟩, q3, q4⟩),
    (fun his => let ⟨q1, q2, q3⟩ := b7 his
      ⟨q1, fun hnsp => q2 fun d hd ho hnsp0 => hnsp d hd ho ⟨hv.2.1 d hd, hnsp0⟩, q3⟩),
    fun htr => b8 ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.1, fun d hd =>
      ⟨(htr.2.2.2.2 d hd).1, fun hnk0 => (htr.2.2.2.2 d hd).2 ⟨hv.2.1 d hd, hnk0⟩⟩⟩⟩

theorem ValEnvDisj_restrict_nk {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop} {Foot : Nat → Prop}
    {av : AVal} {v : Val}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hv : VSim P ext B st Frame NoKill NoSpend σ I Foot av v)
    (hdisj : ValEnvDisj P st NoKill Scope env aenv σ envFoot Foot av v) :
    ValEnvDisj P st (fun d => d < σ.st.size ∧ NoKill d) Scope env aenv σ envFoot Foot av v := by
  intro i b ab hsc hbi habi hne
  have h0 := hdisj i b ab hsc hbi habi hne
  have hvI := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
  refine ⟨fun haV htrV => h0.1 haV ⟨htrV.1, htrV.2.1, htrV.2.2.1, htrV.2.2.2.1, fun d hd =>
      ⟨(htrV.2.2.2.2 d hd).1, fun hnk0 => (htrV.2.2.2.2 d hd).2 ⟨hv.2.1 d hd, hnk0⟩⟩⟩,
    fun haB htrB => h0.2.1 haB ⟨htrB.1, htrB.2.1, htrB.2.2.1, htrB.2.2.2.1, fun d hd =>
      ⟨(htrB.2.2.2.2 d hd).1, fun hnk0 => (htrB.2.2.2.2 d hd).2 ⟨hvI.2.1 d hd, hnk0⟩⟩⟩,
    h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2.1, h0.2.2.2.2.2.2⟩

theorem Sim_restrict_nk_nsp {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ : AState} {I : Interp} {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    Sim P ext B st Frame (fun d => d < σ.st.size ∧ NoKill d)
      (fun d => d < σ.st.size ∧ NoSpend d) Scope env aenv σ I envFoot := by
  refine ⟨hsim.1, hsim.2.1, hsim.2.2.1, hsim.2.2.2.1, hsim.2.2.2.2.1, ?_, ?_⟩
  · intro i b ab hsc hbi habi
    obtain ⟨hm, hneB⟩ := hsim.2.2.2.2.2.1 i b ab hsc hbi habi
    exact ⟨hm, fun hne => let ⟨ho, hv⟩ := hneB hne; ⟨ho, VSim_restrict_nk_nsp hv⟩⟩
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    have h0 := hsim.2.2.2.2.2.2 i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    have hv₁ := ((hsim.2.2.2.2.2.1 i b₁ ab₁ hsi hb₁ hab₁).2 hne₁).2
    exact ⟨fun ha₁ htr₁ => h0.1 ha₁ ⟨htr₁.1, htr₁.2.1, htr₁.2.2.1, htr₁.2.2.2.1, fun d hd =>
        ⟨(htr₁.2.2.2.2 d hd).1, fun hnk0 => (htr₁.2.2.2.2 d hd).2 ⟨hv₁.2.1 d hd, hnk0⟩⟩⟩,
      h0.2⟩

theorem ArgListOk_restrict_nk_nsp {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {args : List (Option (Val × AVal × (Nat → Prop)))}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot)
    (hargs : ArgListOk P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep args) :
    ArgListOk P ext B st Frame (fun d => d < σ.st.size ∧ NoKill d)
      (fun d => d < σ.st.size ∧ NoSpend d) Scope env aenv σ I envFoot Forbid BadReg BadDep args := by
  refine ⟨fun k v av ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
  · obtain ⟨hv, hd, hnrf, hnv⟩ := hargs.1 k v av ft hg
    exact ⟨VSim_restrict_nk_nsp hv, ValEnvDisj_restrict_nk hsim hv hd, hnrf, hnv⟩
  · have hv₁ := (hargs.1 i v₁ av₁ ft₁ hg₁).1
    have h0 := hargs.2 i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂
    exact ⟨fun ha₁ htr₁ => h0.1 ha₁ ⟨htr₁.1, htr₁.2.1, htr₁.2.2.1, htr₁.2.2.2.1, fun d hd =>
        ⟨(htr₁.2.2.2.2 d hd).1, fun hnk0 => (htr₁.2.2.2.2 d hd).2 ⟨hv₁.2.1 d hd, hnk0⟩⟩⟩,
      h0.2⟩

private theorem evalS_caseTerm_select {P : Prog} {ext : ExternOracle} {B₁ : Nat}
    {k : CaseInfo} {consuming : Bool} {st₁ : St}
    {Frame NoKill NoSpend Scope Forbid BadReg BadDep : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {pre : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {mvFoot : Nat → Prop} {mv : AVal} {mv_c : Val}
    (hst₁ : StOk P ext B₁ st₁) (hidx : CtorsIndexed P)
    (hsim₁ : Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv pre I envFoot)
    (henvNRF₁ : EnvNoReachForbid st₁ Scope env aenv pre Forbid BadReg BadDep)
    (hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size)
    (hvMv : VSim P ext B₁ st₁ Frame NoKill NoSpend pre I mvFoot mv mv_c)
    (hdisjMv : ValEnvDisj P st₁ NoKill Scope env aenv pre envFoot mvFoot mv mv_c)
    (hnrfMv : ActiveVal pre mv → NoReachForbid st₁ Forbid BadReg BadDep mv mv_c)
    (hliveMv : (ValBaseOk st₁ mv_c ∧ CtorFieldsOk P ext B₁ st₁ mv_c) ∨
      (IsOnceSrc pre mv ∧ SpentOnceSafe st₁.heap mv_c))
    (hconsPost : consuming = true → ActiveVal pre mv ∧ Transferable pre NoKill mv ∧ mv.deps = [] ∧ mv.src = none) :
    (select P k mv_c).run st₁ = .error .stuck ∨
    ∃ cidx out st₂, (select P k mv_c).run st₁ = .ok ((cidx, out), st₂) ∧
      st₂.regions = st₁.regions ∧ st₂.nextRegion = st₁.nextRegion ∧
      st₂.statics = st₁.statics ∧ st₂.strs = st₁.strs ∧
      st₁.heap.objs.size ≤ st₂.heap.objs.size ∧ st₁.heap.nextCap ≤ st₂.heap.nextCap ∧
      PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap ∧
      PreservesOnceShell st₁.heap st₂.heap ∧ StaticStrFresh st₁ st₂ ∧
      StOk P ext B₁ st₂ ∧
      Sim P ext B₁ st₂ Frame NoKill NoSpend Scope env aenv pre I envFoot ∧
      EnvNoReachForbid st₂ Scope env aenv pre Forbid BadReg BadDep ∧
      ∀ (ca : CaseAlt),
        (∀ (i₁ i₂ q : Nat), ca.args[i₁]? = some (.field q) → ca.args[i₂]? = some (.field q) → i₁ = i₂) →
        let cargs : List (Val × Bool) := ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)
        let aargs := caseAltArgs P k mv consuming cidx ca
        let argList : List (Option (Val × AVal × (Nat → Prop))) :=
          (cargs.zip aargs).map fun ((v, _), (a0, er, _)) => if er then none else some (v, a0, fun (_ : Nat) => False)
        cargs.length = aargs.length ∧
        (∀ (idx : Nat) v er_c a0 er_a fc,
          cargs[idx]? = some (v, er_c) → aargs[idx]? = some (a0, er_a, fc) →
          er_c = er_a ∧ a0.src = none ∧
          (er_a = false → fc = true → a0.onceOnly = false ∧ a0.cls = .val ∧ a0.skel = .unknown ∧
            ValBaseOk st₂ v ∧ CtorFieldsOk P ext B₁ st₂ v ∧ NoOnceCell st₂.heap v ∧
            FunOkAt P ext B₁ st₂ .unknown false (fun (_ : Nat) => False) v)) ∧
        ArgListOk P ext B₁ st₂ Frame NoKill NoSpend Scope env aenv pre I envFoot Forbid BadReg BadDep argList := by
  by_cases hvdMv : ValidDeps pre mv.deps
  · rcases select_caseAltArgs_bridge hst₁ hidx hsim₁ henvNRF₁ hForbLt₁ hvdMv hvMv hdisjMv hnrfMv
        hconsPost with hSt |
      ⟨cidx, out, st₂, hrunS, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, honce₂, hssf₂,
       hst₂, hsim₂, henvNRF₂, hcaOk⟩
    · exact Or.inl hSt
    · refine Or.inr ⟨cidx, out, st₂, hrunS, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂,
        honce₂, hssf₂, hst₂, hsim₂, henvNRF₂, fun ca hdist => ?_⟩
      obtain ⟨hlen, hmeta0, hargOk⟩ := hcaOk ca hdist
      refine ⟨hlen, fun idx v er_c a0 er_a fc hc ha => ?_, hargOk⟩
      obtain ⟨h1, h2, h3⟩ := hmeta0 idx v er_c a0 er_a fc hc ha
      refine ⟨h1, h2, fun herF hfc => ?_⟩
      obtain ⟨hoo0, hcls0, hsk0⟩ := h3 hfc
      have hltC : idx < (ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)).length := (List.getElem?_eq_some_iff.mp hc).1
      have hltA : idx < (caseAltArgs P k mv consuming cidx ca).length := (List.getElem?_eq_some_iff.mp ha).1
      have hltZ : idx < ((ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)).zip (caseAltArgs P k mv consuming cidx ca)).length := by
        rw [List.length_zip, Nat.lt_min]; exact ⟨hltC, hltA⟩
      have hgk : (((ca.args.toList.map fun fa => match fa with
          | .field i => out[i]?.getD (.imm .irr, false)
          | .irr => (.imm .irr, false)
          | .unit => (.imm .irr, false)).zip (caseAltArgs P k mv consuming cidx ca)).map
          fun ((v, _), (a0, er, _)) => if er then none else some (v, a0, fun (_ : Nat) => False))[idx]? =
          some (some (v, a0, fun (_ : Nat) => False)) := by
        simp only [List.getElem?_map, List.getElem?_eq_getElem hltZ, List.getElem_zip]
        have hc' : (ca.args.toList.map fun fa => match fa with
            | .field i => out[i]?.getD (.imm .irr, false)
            | .irr => (.imm .irr, false)
            | .unit => (.imm .irr, false))[idx]'hltC = (v, er_c) := by
          have := List.getElem?_eq_getElem hltC; rw [this] at hc; exact Option.some.inj hc
        have ha' : (caseAltArgs P k mv consuming cidx ca)[idx]'hltA = (a0, false, true) := by
          have := List.getElem?_eq_getElem hltA; rw [this] at ha
          have hEq := Option.some.inj ha; rw [hEq, herF, hfc]
        rw [hc', ha']; rfl
      have hv0 := (hargOk.1 idx v a0 (fun (_ : Nat) => False) hgk).1
      have hvdA0 : ValidDeps pre a0.deps := fun d hd =>
        hvdMv d (caseAltArgs_deps_sub (List.mem_of_getElem? ha) d hd)
      have hnotOnce0 : ¬ IsOnceSrc pre a0 := fun ⟨_, hs, _⟩ => by rw [h2] at hs; cases hs
      have hvA0 := hv0.2.2.2.2 ⟨hvdA0, fun his => absurd his hnotOnce0⟩
      have hpl0 := hvA0.2.2.2.2.1 ⟨hnotOnce0, hoo0⟩
      exact ⟨hoo0, hcls0, hsk0, hvA0.1, hvA0.2.2.1, hpl0.1, hsk0 ▸ hpl0.2.2⟩
  · have hconsF : consuming = false := by
      cases hc : consuming with
      | false => rfl
      | true => exact absurd (hconsPost hc).1.1 hvdMv
    subst hconsF
    have hlivePair : (ValBaseOk st₁ mv_c ∧ CtorFieldsOk P ext B₁ st₁ mv_c) ∨
        (select P k mv_c).run st₁ = .error .stuck := by
      rcases hliveMv with h1 | ⟨_, hspMv⟩
      · exact Or.inl h1
      · rcases hspMv with rfl | ⟨loc, cap, t, o, tgt, sp, rfl, ho, hcap, hcell⟩
        · exact Or.inl ⟨ValBaseOk_imm st₁ .irr, CtorFieldsOk_imm P ext B₁ st₁ .irr⟩
        · exact Or.inr (select_spentOnce_ref_stuck ho hcap hcell)
    rcases hlivePair with ⟨hbvMv, hcfMv⟩ | hStOnce
    · rcases select_caseAltArgs_of_dead hst₁ hidx hsim₁ henvNRF₁ hvMv.1 hvMv.2.1 hvdMv hbvMv hcfMv with hSt |
        ⟨cidx, out, st₂, hrunS, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, honce₂, hssf₂,
         hst₂, hsim₂, henvNRF₂, hcaOk⟩
      · exact Or.inl hSt
      · refine Or.inr ⟨cidx, out, st₂, hrunS, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂,
          honce₂, hssf₂, hst₂, hsim₂, henvNRF₂, fun ca _ => ?_⟩
        obtain ⟨hlen, hmeta0, hargOk⟩ := hcaOk ca
        exact ⟨hlen, fun idx v er_c a0 er_a fc hc ha =>
          let ⟨h1, h2, h3⟩ := hmeta0 idx v er_c a0 er_a fc hc ha
          ⟨h1, h2, fun _ hfc => h3 hfc⟩, hargOk⟩
    · exact Or.inl hStOnce

/-- Soundness for `ATerm.caseTerm` (`evalMajorS`, `select` via `select_caseAltArgs_bridge` /
`select_caseAltArgs_of_dead` / `select_spentOnce_ref_stuck`, `applyAltS` via `AAltsProp`/`AAltProp`,
`case_join_weaken`, `evalListS` on extra args, and `applyAllS_bridge`). -/
theorem evalS_caseTerm_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {k : CaseInfo} {mj : Term} {alts ex : Array Term} {c : Cls}
    {σ pre σ_join σ_ex σ_end : AState} {mv r_join res : AVal} {consuming : Bool} {avs : List AVal}
    (hidx : CtorsIndexed P)
    (halSz : alts.size = k.alts.size)
    (hmjD : AMajor P aenv mj σ mv consuming pre)
    (hmjIH : AMajorProp P ext B aenv mj σ mv consuming pre)
    (haltsD : AAlts P aenv k mv consuming pre 0 k.alts.toList alts.toList r_join σ_join)
    (haltsIH : AAltsProp P ext B aenv k mv consuming pre 0 k.alts.toList alts.toList r_join σ_join)
    (h0Alts : k.alts.size = 0 →
      σ_join.st = pre.st ∧ σ_join.once = pre.once ∧
      σ_join.spent = pre.spent ∧ σ_join.regions = pre.regions ∧
      pre.nextRegion ≤ σ_join.nextRegion)
    (hrjCls : r_join.cls = c) (hrjSrc : r_join.src = none) (hrjOO : r_join.onceOnly = false)
    (hrjDeps : ∀ d ∈ r_join.deps, d < pre.st.size)
    (hrjRegs : ∀ reg ∈ r_join.regs, reg < σ_join.nextRegion)
    (hexD : AEvals P aenv ex.toList σ_join avs σ_ex)
    (hexIH : AEvalsProp P ext B aenv ex.toList σ_join avs σ_ex)
    (happs : AApps r_join avs c σ_ex res σ_end) :
    ATermProp P ext B aenv (.case k mj alts ex c) σ res σ_end := by
  classical
  have _ := hrjCls
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  cases hlc with | case hlcMj hlcAlts hlcEx =>
  cases hcfd with | case hcfdDistinct hcfdMj hcfdAlts hcfdEx =>
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hok := hsim.2.1
      obtain ⟨hokPre, hlePre, hregPre⟩ := AMajor_state_le hok hmjD
      have hjoinOkLe : AStateOk σ_join ∧ AStateLe pre σ_join ∧ σ_join.regions = pre.regions := by
        cases hsz : k.alts.size with
        | zero =>
          obtain ⟨hstJ, honceJ, hspJ, hregJ, hnrJ⟩ := h0Alts hsz
          refine ⟨⟨by rw [hstJ, honceJ]; exact hokPre.1, by rw [hstJ, hspJ]; exact hokPre.2.1,
            Nat.le_trans hokPre.2.2.1 hnrJ, hregJ ▸ hokPre.2.2.2.1, hregJ ▸ hokPre.2.2.2.2.1,
            fun r hr => let ⟨h1, h2⟩ := hokPre.2.2.2.2.2 r (hregJ ▸ hr); ⟨h1, Nat.lt_of_lt_of_le h2 hnrJ⟩⟩,
            ⟨by rw [hstJ]; exact Nat.le_refl _, hnrJ,
             fun i hi => by rw [hstJ, Array.getElem?_eq_getElem hi]; exact BSt.le_refl _,
             fun _ _ => by rw [honceJ], fun _ _ hsp => by rw [hspJ]; exact hsp⟩, hregJ⟩
        | succ _ =>
          have hltK : 0 < k.alts.toList.length := by simp [hsz]
          have hltA : 0 < alts.toList.length := by simp [halSz, hsz]
          exact AAlts_state_le hokPre haltsD (List.getElem?_eq_getElem hltK) (List.getElem?_eq_getElem hltA)
      obtain ⟨hokJoin, hleJoin, hregJoin⟩ := hjoinOkLe
      obtain ⟨hokEx, hleEx, hregEx⟩ := AEvals_state_le hokJoin hexD
      obtain ⟨hokEnd, hleEnd, hregEnd, _⟩ := AApps_state_le hokEx happs
      have hleJoinEnd : AStateLe σ_join σ_end := hleEx.trans hleEnd
      have hlePreEnd : AStateLe pre σ_end := hleJoin.trans hleJoinEnd
      have hnkEx : NoKillOk NoKill σ_ex := NoKillOk_of_AStateLe hleEnd hnkEnd
      have hnkJoin : NoKillOk NoKill σ_join := NoKillOk_of_AStateLe hleEx hnkEx
      have hnkPre : NoKillOk NoKill pre := NoKillOk_of_AStateLe hleJoin hnkJoin
      have hnspEx : NoSpendOk NoSpend σ_ex := NoSpendOk_of_AStateLe hleEnd hnspEnd
      have hnspJoin : NoSpendOk NoSpend σ_join := NoSpendOk_of_AStateLe hleEx hnspEx
      have hnspPre : NoSpendOk NoSpend pre := NoSpendOk_of_AStateLe hleJoin hnspJoin
      let BadDepPre : Nat → Prop := fun d => d < pre.st.size ∧ BadDep d
      have hBadDepJoin : ∀ d, BadDepPre d → σ_join.st[d]? = some .live :=
        BadDepLive_of_AStateLe hleJoinEnd (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => Nat.lt_of_lt_of_le hbd.1 hleJoin.1)
      have hBadDepPre : ∀ d, BadDepPre d → pre.st[d]? = some .live :=
        BadDepLive_of_AStateLe hlePreEnd (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
      have hstep : (evalS P ext (n + 1) env (.case k mj alts ex c)).run (st, b0 + 1) =
          (do
            let mv ← evalMajorS P ext n env mj
            let (j, fields) ← liftM (select P k mv)
            let some alt := k.alts[j]? | liftM stuckM
            let some altT := alts[j]? | liftM stuckM
            let args := alt.args.toList.map fun fa => match fa with
              | FieldArg.field i => fields[i]?.getD (.imm .irr, false)
              | .irr => (.imm .irr, false)
              | .unit => (.imm .irr, false)
            let r ← applyAltS P ext n env altT args
            let exVs ← evalListS P ext n env ex.toList []
            applyAllS P ext n r exVs c).run (st, b0) := by
        conv => lhs; unfold evalS
        rw [MS_bind_run, MS_spend_succ]; dsimp only
        cases mj <;> rfl
      unfold TermPost; rw [hstep, MS_bind_run]
      have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (by omega) (AStateLe.refl _) hok hsim.2.2.1 (RegsFuture.refl _)
          (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
          (PreservesActiveEnv.refl _ _ _ _ _) hsim
      have henvNRF_pre : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDepPre := by
        intro i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps
        have hvI := ((hsimB.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
        exact henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
          (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hlePre.1, hbd⟩)
      obtain ⟨⟨hnoVMj, hokMj⟩, hconsPost⟩ := hmjIH hlcMj hcfdMj (B₀ := b0) (fuel := n) (by omega)
        (fun z hz => hfv z (.caseMj hz)) (StOk_mono (by omega) hst) hsimB hstat hFlt
        hnkPre hnspPre hIZero hHeadReg henvTaint henvNRF_pre hForbidLt hBadDepPre
      cases hevMj : (evalMajorS P ext n env mj).run (st, b0) with
      | error e =>
        refine ⟨fun k' hk' => by cases hk'; exact hnoVMj k' hevMj, fun _ _ _ h => by cases h⟩
      | ok pmj =>
        rcases pmj with ⟨mv_c, ⟨st₁, B₁⟩⟩; dsimp only
        obtain ⟨mvFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
          hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
          hvMv, hdisjMv, hnrfMv, _, _, hliveMv, _⟩ := hokMj mv_c st₁ B₁ hevMj
        have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
        have hSelect := evalS_caseTerm_select (k := k) hst₁ hidx hsim₁ henvNRF₁ hForbLt₁ hvMv hdisjMv hnrfMv hliveMv hconsPost
        rw [MS_bind_run, MS_liftM_run]
        rcases hSelect with hStS | ⟨cidx, out, st₂, hrunS, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂,
            hpres₂, honce₂, hssf₂, hst₂, hsim₂, henvNRF₂, hcaOk⟩
        · rw [hStS]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [hrunS]; dsimp only
          cases hca : k.alts[cidx]? with
          | none =>
            simp only [MS_liftM_run]; unfold stuckM; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          | some ca =>
            cases haltT : alts[cidx]? with
            | none =>
              simp only [MS_liftM_run]; unfold stuckM; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            | some altT =>
              have hcaList : k.alts.toList[cidx]? = some ca := by simpa using hca
              have haltList : alts.toList[cidx]? = some altT := by simpa using haltT
              obtain ⟨nextReg_j, r_j, post_j, σ_chk_j, σ_val_j, uniq_j, σ_u_j,
                hnrJ, haltD, haltIH, hnoOnceJ, hooRj, hvalRj, huniqRj, hsj, hvj⟩ :=
                haltsIH cidx ca altT hcaList haltList
              simp only [Nat.zero_add] at haltD haltIH
              obtain ⟨_, hσChkEq⟩ := Runs_notOnceSrc hnoOnceJ; subst σ_chk_j
              obtain ⟨_, hσValEq⟩ := Runs_valid hvalRj; subst σ_val_j
              obtain ⟨hσUEq, _⟩ := Runs_isUniq huniqRj; subst σ_u_j
              obtain ⟨hokPre', hlePre'⟩ := AStateOk_advance_nextRegion hokPre hnrJ
              obtain ⟨hokPost, hlePost, hregPost⟩ := AAlt_state_le hokPre' haltD
              have hlePrePost : AStateLe pre post_j := hlePre'.trans hlePost
              have hregPrePost : pre.regions = post_j.regions := hregPost.symm
              -- Restrict `NoKill` / `NoSpend` to `< pre.st.size` and add `StaticStrLoc st₂` to frame
              let Frame₂ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₂ l
              let NoKillPre : Nat → Prop := fun d => d < pre.st.size ∧ NoKill d
              let NoSpendPre : Nat → Prop := fun d => d < pre.st.size ∧ NoSpend d
              have hnkPost : NoKillOk NoKillPre post_j := fun d hnkD hdead => by
                have h2 := hsj.2.2.2.2.2.1 d hnkD.1
                rw [hdead] at h2
                cases h : σ_join.st[d]? with
                | none => rw [h] at h2; cases h2
                | some bj =>
                  rw [h] at h2
                  cases bj with
                  | live | shared => cases h2
                  | dead => exact hnkJoin d hnkD.2 h
              have hnspPost : NoSpendOk NoSpendPre post_j := fun d hnspD hsp => by
                have hltPreSp : d < pre.spent.size := by rw [← hokPre.2.1]; exact hnspD.1
                exact hnspJoin d hnspD.2 (hsj.2.2.2.2.2.2 d hltPreSp hsp)
              have hBadDepPost : ∀ d, BadDepPre d → post_j.st[d]? = some .live := fun d hbd => by
                have hlv := hBadDepJoin d hbd
                have h2 := hsj.2.2.2.2.2.1 d hbd.1
                rw [hlv] at h2
                cases h : post_j.st[d]? with
                | none => rw [h] at h2; cases h2
                | some bp =>
                  rw [h] at h2; cases bp with | live => rfl | shared | dead => cases h2
              have hIokPre' : InterpOk { pre with nextRegion := nextReg_j } st₂ I :=
                ⟨(fun rg hlt c hc => by
                  by_cases hltP : rg < pre.nextRegion
                  · exact hsim₂.2.2.1.1 rg hltP c hc
                  · have hge0 : σ.nextRegion ≤ rg := Nat.le_trans hlePre.2.1 (Nat.le_of_not_lt hltP)
                    rw [hIZero rg hge0] at hc; cases hc),
                 hsim₂.2.2.1.2⟩
              have hsim₂' : Sim P ext B₁ st₂ Frame₂ NoKillPre NoSpendPre Scope env aenv
                  { pre with nextRegion := nextReg_j } I envFoot :=
                Sim_step (Nat.le_refl B₁) hlePre' hokPre' hIokPre' (RegsFuture.refl _)
                  (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
                  (PreservesActiveEnv.refl _ _ _ _ _) (Sim_restrict_nk_nsp (Sim_add_staticStr hsim₂))
              have henvNRF₂' : EnvNoReachForbid st₂ Scope env aenv { pre with nextRegion := nextReg_j }
                  Forbid BadReg BadDepPre := henvNRF₂
              have hdistCa := hcfdDistinct ca (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hca))
              obtain ⟨hlenCargs, hmetaCargs, hargOkCargs⟩ := hcaOk ca hdistCa
              have hargOk₂' : ArgListOk P ext B₁ st₂ Frame₂ NoKillPre NoSpendPre Scope env aenv
                  { pre with nextRegion := nextReg_j } I envFoot Forbid BadReg BadDepPre
                  (((ca.args.toList.map fun fa => match fa with
                      | .field i => out[i]?.getD (.imm .irr, false)
                      | .irr => (.imm .irr, false)
                      | .unit => (.imm .irr, false)).zip (caseAltArgs P k mv consuming cidx ca)).map
                    fun ((v, _), (a0, er, _)) => if er then none else some (v, a0, fun (_ : Nat) => False)) := by
                have hbase := ArgListOk_restrict_nk_nsp (Sim_add_staticStr hsim₂) (ArgListOk_add_staticStr hargOkCargs)
                refine ⟨fun idx v av ft hg => ?_, hbase.2⟩
                obtain ⟨hv, hd, hnrf, hnv⟩ := hbase.1 idx v av ft hg
                exact ⟨VSim_step (Nat.le_refl B₁) hokPre hlePre' (RegsFuture.refl _) (PreservesOnceShell.refl _)
                    (StaticStrFresh.refl _) (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _) hv,
                  hd, hnrf, hnv⟩
              have hstat₂F : ∀ l, StaticStrLoc st₂ l → Frame₂ l := fun _ h => Or.inr h
              have hFlt₂ : ∀ l, Frame₂ l → l < st₂.heap.objs.size := fun l h =>
                h.elim (fun hF => Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) hsz₂)
                  (fun hss => StOk_staticStrLoc_lt hst₂ hss)
              have hForbLt₂ : ∀ l, Forbid l → l < st₂.heap.objs.size := fun l hF =>
                Nat.lt_of_lt_of_le (hForbLt₁ l hF) hsz₂
              have hIZeroPre' : ∀ rg, nextReg_j ≤ rg → I.reg rg = [] := fun rg hge =>
                hIZero rg (Nat.le_trans hlePre.2.1 (Nat.le_trans hnrJ hge))
              have hHeadReg₂ : st₂.regions.headD 0 = 0 ∨ st₂.regions.headD 0 ∈ I.reg (pre.regions.headD 1) := by
                rw [hrg₂, hr₁, hregPre]; exact hHeadReg
              have hTaint₂ : EnvTaintOk Scope env aenv st₂ I := henvTaint₁.step hrg₂ (hnr₂ ▸ Nat.le_refl _)
              have hAltMem : altT ∈ alts.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? haltT)
              obtain ⟨hnoVAlt, hokAlt⟩ := haltIH (hlcAlts altT hAltMem) (hcfdAlts altT hAltMem)
                (B₀ := B₁) (fuel := n) (by omega)
                (fun z hz => hfv z (.caseAlt hAltMem hz))
                hst₂ hsim₂' hstat₂F hFlt₂ hnkPost hnspPost hIZeroPre' hHeadReg₂ hTaint₂ henvNRF₂'
                hForbLt₂ hBadDepPost hlenCargs
                (caseAltArgs_nonCons fun hc => (hconsPost hc).2.2.1)
                hmetaCargs hargOk₂'
              rw [MS_bind_run]
              cases hevAlt : (applyAltS P ext n env altT (ca.args.toList.map fun fa => match fa with
                  | .field i => out[i]?.getD (.imm .irr, false)
                  | .irr => (.imm .irr, false)
                  | .unit => (.imm .irr, false))).run (st₂, B₁) with
              | error e =>
                refine ⟨fun k' hk' => by cases hk'; exact hnoVAlt k' hevAlt, fun _ _ _ h => by cases h⟩
              | ok palt =>
                rcases palt with ⟨rv_alt, ⟨st₃, B₃⟩⟩; dsimp only
                obtain ⟨altFoot, hB₃, hst₃, hsz₃, hcap₃, hr₃, hnr₃, hstat₃, hstr₃,
                  hpFrame₃, hpEnv₃, hpNum₃, honce₃, hssf₃, hsim₃, henvTaint₃, henvNRF₃,
                  hvAlt, hdisjAlt, hnrfAlt, _, _, _, _⟩ := hokAlt rv_alt st₃ B₃ hevAlt
                have hIZeroPre : ∀ rg, pre.nextRegion ≤ rg → I.reg rg = [] := fun rg hge =>
                  hIZero rg (Nat.le_trans hlePre.2.1 hge)
                have hdepsEnvPre : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
                    ∀ d ∈ (effVal ab).deps, d < pre.st.size := fun i ab hsc hab hne d hd => by
                  have hiE : i < env.length := by rw [hsim.1]; exact (List.getElem?_eq_some_iff.mp hab).1
                  exact Nat.lt_of_lt_of_le (((hsim.2.2.2.2.2.1 i env[i] ab hsc (List.getElem?_eq_getElem hiE) hab).2 hne).2.2.1 d hd) hlePre.1
                have hidsPre : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < pre.st.size := fun i ab hab =>
                  Nat.lt_of_lt_of_le (hsim.2.2.2.1 i ab hab) hlePre.1
                let r_join_v : AVal := { r_join with cls := r_j.cls }
                obtain ⟨_, _, hsimJ0, henvNRFJ0, hvJ0, hdisjJ, hnrfJ0, hnvJ, _, _, _⟩ :=
                  case_join_weaken hokPre hlePrePost hIZeroPre hregPrePost hsim₃ henvNRF₃
                    hdepsEnvPre hidsPre hvAlt hdisjAlt hnrfAlt hnoOnceJ hooRj hvalRj huniqRj
                    hsj hvj hrjSrc hrjOO hrjDeps hrjRegs hBadDepJoin
                have haRj : ActiveVal post_j r_j :=
                  ⟨(Runs_valid hvalRj).1, fun his => absurd his (Runs_notOnceSrc hnoOnceJ).1⟩
                have hliveAlt : ValBaseOk st₃ rv_alt ∧ CtorFieldsOk P ext B₃ st₃ rv_alt :=
                  ⟨(hvAlt.2.2.2.2 haRj).1, (hvAlt.2.2.2.2 haRj).2.2.1⟩
                let Frame₃ : Nat → Prop := fun l => Frame₂ l ∨ StaticStrLoc st₃ l
                have hsimJ : Sim P ext B₃ st₃ Frame₃ NoKill NoSpend Scope env aenv σ_join I envFoot :=
                  Sim_add_staticStr hsimJ0
                have hvJ : VSim P ext B₃ st₃ Frame₃ NoKill NoSpend σ_join I (fun (_ : Nat) => False) r_join_v rv_alt :=
                  VSim_add_staticStr hvJ0
                let BadDepEx : Nat → Prop := fun d => d < σ_ex.st.size ∧ BadDep d
                have hBadDepEx : ∀ d, BadDepEx d → σ_ex.st[d]? = some .live :=
                  BadDepLive_of_AStateLe hleEnd (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
                have henvNRFJ : EnvNoReachForbid st₃ Scope env aenv σ_join Forbid BadReg BadDepEx := by
                  intro i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps
                  exact henvNRFJ0 i b' ab' hsc' hbi' habi' hne' ha' hregs
                    (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hbd.1 hleJoin.1) hleEx.1, hbd.2⟩)
                have hnrfJ : ActiveVal σ_join r_join_v → NoReachForbid st₃ Forbid BadReg BadDepEx r_join_v rv_alt :=
                  fun ha' hregs hdeps => hnrfJ0 ha' hregs
                    (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hbd.1 hleJoin.1) hleEx.1, hbd.2⟩)
                let prefJ : List (Option (Val × AVal × (Nat → Prop))) := [some (rv_alt, r_join_v, fun (_ : Nat) => False)]
                have hArgPref : ArgListOk P ext B₃ st₃ Frame₃ NoKill NoSpend Scope env aenv σ_join I envFoot
                    Forbid BadReg BadDepEx prefJ := by
                  refine ⟨fun idx v av ft hg => ?_, fun i j _ _ _ _ _ _ hij hg₁ hg₂ => ?_⟩
                  · cases idx with
                    | zero => simp [prefJ] at hg; rcases hg with ⟨rfl, rfl, rfl⟩; exact ⟨hvJ, hdisjJ, hnrfJ, hnvJ⟩
                    | succ _ => simp [prefJ] at hg
                  · cases i with
                    | zero => cases j with | zero => exact absurd rfl hij | succ _ => simp [prefJ] at hg₂
                    | succ _ => simp [prefJ] at hg₁
                have hPrefSrcJ : PrefixSrcOk Scope aenv prefJ := fun idx v av ft hg id hs => by
                  cases idx with
                  | zero => simp [prefJ] at hg; rcases hg with ⟨_, rfl, _⟩; change r_join.src = some id at hs; rw [hrjSrc] at hs; cases hs
                  | succ _ => simp [prefJ] at hg
                have hArgsSrcJ : ArgsSrcOk prefJ := fun i _ _ _ _ _ _ _ _ hg₁ _ hs₁ _ => by
                  cases i with
                  | zero => simp [prefJ] at hg₁; rcases hg₁ with ⟨_, rfl, _⟩; change r_join.src = some _ at hs₁; rw [hrjSrc] at hs₁; cases hs₁
                  | succ _ => simp [prefJ] at hg₁
                have hstat₃F : ∀ l, StaticStrLoc st₃ l → Frame₃ l := fun _ h => Or.inr h
                have hFlt₃ : ∀ l, Frame₃ l → l < st₃.heap.objs.size := fun l h =>
                  h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt₂ l hF) hsz₃)
                    (fun hss => StOk_staticStrLoc_lt hst₃ hss)
                have hForbLt₃ : ∀ l, Forbid l → l < st₃.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbLt₂ l hF) hsz₃
                have hIZeroJoin : ∀ rg, σ_join.nextRegion ≤ rg → I.reg rg = [] := fun rg hge =>
                  hIZero rg (Nat.le_trans (hlePre.trans hleJoin).2.1 hge)
                have hHeadReg₃ : st₃.regions.headD 0 = 0 ∨ st₃.regions.headD 0 ∈ I.reg (σ_join.regions.headD 1) := by
                  rw [hr₃, hrg₂, hr₁, hregJoin, hregPre]; exact hHeadReg
                obtain ⟨hnoVEx, hokEvEx⟩ := hexIH hlcEx hcfdEx (B₀ := B₃) (fuel := n) (by omega)
                  (fun t ht z hz => hfv z (.caseEx ht hz))
                  hst₃ hsimJ hstat₃F hFlt₃ hnkEx hnspEx hIZeroJoin hHeadReg₃ henvTaint₃ henvNRFJ
                  hForbLt₃ hBadDepEx hArgPref hPrefSrcJ hArgsSrcJ
                rw [MS_bind_run]
                cases hevEx : (evalListS P ext n env ex.toList []).run (st₃, B₃) with
                | error e =>
                  refine ⟨fun k' hk' => by cases hk'; exact hnoVEx k' hevEx, fun _ _ _ h => by cases h⟩
                | ok pex =>
                  rcases pex with ⟨exVs, ⟨st₄, B₄⟩⟩; dsimp only
                  obtain ⟨exArgs, hexVsEq, hexAvsEq, hB₄, hst₄, hsz₄, hcap₄, hr₄, hnr₄, hstat₄, hstr₄,
                    hpFrame₄, hpEnv₄, hpNum₄, honce₄, hssf₄, hsim₄, henvTaint₄, henvNRF₄,
                    hArgList₄, _, hArgsSrc₄⟩ := hokEvEx exVs st₄ B₄ hevEx
                  let Frame₄ : Nat → Prop := fun l => Frame₃ l ∨ StaticStrLoc st₄ l
                  have hFlt₄ : ∀ l, Frame₄ l → l < st₄.heap.objs.size := fun l h =>
                    h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt₃ l hF) hsz₄)
                      (fun hss => StOk_staticStrLoc_lt hst₄ hss)
                  have hForbLt₄ : ∀ l, Forbid l → l < st₄.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbLt₃ l hF) hsz₄
                  have hstat₄F : ∀ l, StaticStrLoc st₄ l → Frame₄ l := fun _ h => Or.inr h
                  obtain ⟨hvF₄, hdisjF₄, hnrfF₄, hnvF₄⟩ := hArgList₄.1 0 rv_alt r_join_v (fun (_ : Nat) => False) rfl
                  have hArgTail₄ : ArgListOk P ext B₄ st₄ Frame₄ NoKill NoSpend Scope env aenv σ_ex I envFoot
                      Forbid BadReg BadDepEx (exArgs.map some) :=
                    ArgListOk_add_staticStr (ArgListOk_drop_prefix hArgList₄)
                  have hNilLive : exArgs = [] →
                      (ValBaseOk st₄ rv_alt ∧ CtorFieldsOk P ext B₄ st₄ rv_alt) ∨
                      (c = .val ∧ IsOnceSrc σ_ex r_join_v ∧ SpentOnceSafe st₄.heap rv_alt) := fun hnil => by
                    have hlenEx : ex.toList.length = 0 := by
                      have h1 := AEvals_length_eval hexD; rw [← hexAvsEq, hnil] at h1; simpa using h1.symm
                    have hexNil : ex.toList = [] := List.eq_nil_of_length_eq_zero hlenEx
                    rw [hexNil] at hevEx
                    have hpure : (evalListS P ext n env [] []).run (st₃, B₃) = .ok ([], (st₃, B₃)) := by
                      unfold evalListS; rfl
                    rw [hpure] at hevEx; cases hevEx
                    exact Or.inl hliveAlt
                  have hFvsA : ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop), exArgs[i]? = some (v, av, ft) →
                      (ActiveVal σ_ex av → Transferable σ_ex NoKill av → ActiveVal σ_ex r_join_v →
                        (∀ d, d ∈ av.deps → ¬ (d ∈ r_join_v.deps)) → ∀ l, OwnReach P st₄.heap v l → ¬ Reach st₄.heap rv_alt l) ∧
                      (ActiveVal σ_ex r_join_v → FootActive σ_ex r_join_v → ActiveVal σ_ex av →
                        (r_join_v.src = none ∨ r_join_v.src ≠ av.src) → ∀ l, False → ¬ Reach st₄.heap v l) ∧
                      (ActiveVal σ_ex av → FootActive σ_ex av → ActiveVal σ_ex r_join_v →
                        (av.src = none ∨ av.src ≠ r_join_v.src) → ∀ l, ft l → ¬ Reach st₄.heap rv_alt l) ∧
                      (∀ x, r_join_v.src = some x → av.src = some x → r_join_v.onceOnly = av.onceOnly) := by
                    intro i v av ft hgi
                    have hgi' : (prefJ ++ exArgs.map some)[i + 1]? = some (some (v, av, ft)) := by
                      simp [prefJ, hgi]
                    have hPair := hArgList₄.2 (i + 1) 0 v rv_alt av r_join_v ft (fun (_ : Nat) => False) (by omega) hgi' rfl
                    exact ⟨hPair.1, fun _ _ _ _ _ h => False.elim h, hPair.2,
                      fun x hs _ => by change r_join.src = some x at hs; rw [hrjSrc] at hs; cases hs⟩
                  have hPairSrc : ∀ (i j : Nat) (v₁ v₂ : Val) (av₁ av₂ : AVal) (ft₁ ft₂ : Nat → Prop) (x : Nat),
                      exArgs[i]? = some (v₁, av₁, ft₁) → exArgs[j]? = some (v₂, av₂, ft₂) →
                      av₁.src = some x → av₂.src = some x → av₁.onceOnly = av₂.onceOnly := by
                    intro i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ hs₁ hs₂
                    have hdrop := ArgsSrcOk_drop_prefix hArgsSrc₄
                    exact hdrop i j v₁ v₂ av₁ av₂ ft₁ ft₂ x (by simp [hg₁]) (by simp [hg₂]) hs₁ hs₂
                  have happs' : AApps r_join_v (exArgs.map (·.2.1)) c σ_ex res σ_end := by
                    rw [hexAvsEq]; exact AApps_change_cls happs
                  rw [← hexVsEq]
                  obtain ⟨hnoVApp, hokApp⟩ := applyAllS_bridge (fuel := n) happs'
                    (Sim_add_staticStr hsim₄) hst₄ hstat₄F hFlt₄ hnkEnd hnspEnd
                    (VSim_add_staticStr hvF₄) hdisjF₄ hnrfF₄ hnvF₄ hNilLive
                    hArgTail₄ hFvsA hPairSrc henvNRF₄ hForbLt₄
                  refine ⟨hnoVApp, fun rv_end st₅ B₅ hevApp => ?_⟩
                  obtain ⟨endFoot, hB₅, hst₅, hsz₅, hcap₅, hr₅, hnr₅, hstat₅, hstr₅,
                    hpFrame₅, hpEnv₅, hpNum₅, honce₅, hssf₅, hsim₅, henvNRF₅,
                    hvEnd, hdisjEnd, hnrfEnd, hnvEnd, hliveEnd⟩ := hokApp rv_end st₅ B₅ hevApp
                  have hresSrc : res.src = none := AApps_src_none hokEx hrjSrc happs
                  have hpresEnvAll : PreservesActiveEnv Scope env aenv σ_end st.heap st₅.heap := by
                    intro i b' ab' hsc' hbi' habi' hne' haEnd
                    have hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
                    have hdepsPre : ∀ d ∈ (effVal ab').deps, d < pre.st.size := fun d hd =>
                      Nat.lt_of_lt_of_le (hvI.2.1 d hd) hlePre.1
                    have hsrcPre : ∀ z, (effVal ab').src = some z → z < pre.st.size := fun z hz =>
                      Nat.lt_of_lt_of_le (hvI.2.2.1 z hz).1 hlePre.1
                    have haEx := ActiveVal.of_AStateLe hokEx hleEnd
                      (fun d hd => Nat.lt_of_lt_of_le (hdepsPre d hd) (hleJoin.trans hleEx).1)
                      (fun z hz => Nat.lt_of_lt_of_le (hsrcPre z hz) (hleJoin.trans hleEx).1) haEnd
                    have haJ := ActiveVal.of_AStateLe hokJoin hleEx
                      (fun d hd => Nat.lt_of_lt_of_le (hdepsPre d hd) hleJoin.1)
                      (fun z hz => Nat.lt_of_lt_of_le (hsrcPre z hz) hleJoin.1) haEx
                    have haPost : ActiveVal post_j (effVal ab') := by
                      refine ⟨fun d hd => ⟨Nat.lt_of_lt_of_le (hdepsPre d hd) hlePrePost.1, fun hdead => ?_⟩,
                        fun his d hd hoP => ?_⟩
                      · have h2 := hsj.2.2.2.2.2.1 d (hdepsPre d hd); rw [hdead] at h2
                        cases h : σ_join.st[d]? with
                        | none => rw [h] at h2; cases h2
                        | some bj => rw [h] at h2; cases bj with | live | shared => cases h2 | dead => exact (haJ.1 d hd).2 h
                      · obtain ⟨x, hx, hoX⟩ := his
                        have hxO : x < pre.once.size := by rw [← hokPre.1]; exact hsrcPre x hx
                        have hdO : d < pre.once.size := by rw [← hokPre.1]; exact hdepsPre d hd
                        have hoXJ : σ_join.once[x]? = some true := by rw [hsj.2.1, ← hlePrePost.2.2.2.1 x hxO]; exact hoX
                        have hoDJ : σ_join.once[d]? = some true := by rw [hsj.2.1, ← hlePrePost.2.2.2.1 d hdO]; exact hoP
                        have hsfJ := haJ.2 ⟨x, hx, hoXJ⟩ d hd hoDJ
                        have hltSpP : d < post_j.spent.size := by
                          have := hdepsPre d hd; have := hlePrePost.1; have := hokPost.2.1; omega
                        have hltPreSp : d < pre.spent.size := by rw [← hokPre.2.1]; exact hdepsPre d hd
                        cases hs : post_j.spent[d]? with
                        | none => exact absurd (Array.getElem?_eq_none_iff.mp hs) (Nat.not_le_of_lt hltSpP)
                        | some bb =>
                          cases bb with
                          | false => rfl
                          | true => rw [hsj.2.2.2.2.2.2 d hltPreSp hs] at hsfJ; cases hsfJ
                    have haPre := ActiveVal.of_AStateLe hokPre hlePrePost hdepsPre hsrcPre haPost
                    have hp1 := hpEnv₁ i b' ab' hsc' hbi' habi' hne' haPre
                    have hvI₁ := ((hsim₁.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
                    have hp2 : PreservesLocs (Reach st₁.heap b'.val) st₁.heap st₂.heap :=
                      hpres₂.mono fun _ hr => (hvI₁.2.2.2.2 haPre).1.1.reach_lt_size hr
                    have hp12 : PreservesLocs (Reach st.heap b'.val) st.heap st₂.heap :=
                      hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
                    have hp3 := hpEnv₃ i b' ab' hsc' hbi' habi' hne' haPost
                    have hp13 : PreservesLocs (Reach st.heap b'.val) st.heap st₃.heap :=
                      hp12.trans (hp3.mono fun l hr => (Reach_congr hp12 l).mpr hr)
                    have hp4 := hpEnv₄ i b' ab' hsc' hbi' habi' hne' haEx
                    have hp14 : PreservesLocs (Reach st.heap b'.val) st.heap st₄.heap :=
                      hp13.trans (hp4.mono fun l hr => (Reach_congr hp13 l).mpr hr)
                    have hp5 := hpEnv₅ i b' ab' hsc' hbi' habi' hne' haEnd
                    exact hp14.trans (hp5.mono fun l hr => (Reach_congr hp14 l).mpr hr)
                  have hpresF2 : PreservesLocs Frame st₁.heap st₂.heap :=
                    hpres₂.mono fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁
                  have hpresNum₂ : ∀ (l : Nat) (o : Obj) (num : Nat),
                      st₁.heap.objs[l]? = some o → o.cell = .num num → st₂.heap.objs[l]? = some o :=
                    PreservesLocs_old_num hpres₂
                  have hpresSS₂ : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap :=
                    hpres₂.mono fun l hss => StOk_staticStrLoc_lt hst₁ hss
                  have hssf02 : StaticStrFresh st st₂ := StaticStrFresh.trans hsz₁ hpresSS₂ hssf₁ hssf₂
                  have hssf03 : StaticStrFresh st st₃ :=
                    StaticStrFresh.trans (Nat.le_trans hsz₁ hsz₂) (hpFrame₃.mono fun l hss => Or.inr hss) hssf02 hssf₃
                  have hssf04 : StaticStrFresh st st₄ :=
                    StaticStrFresh.trans (Nat.le_trans (Nat.le_trans hsz₁ hsz₂) hsz₃) (hpFrame₄.mono fun l hss => Or.inr hss) hssf03 hssf₄
                  have hssf05 : StaticStrFresh st st₅ :=
                    StaticStrFresh.trans (Nat.le_trans (Nat.le_trans (Nat.le_trans hsz₁ hsz₂) hsz₃) hsz₄)
                      (hpFrame₅.mono fun l hss => Or.inr hss) hssf04 hssf₅
                  have henvNRFFinal : EnvNoReachForbid st₅ Scope env aenv σ_end Forbid BadReg BadDep :=
                    fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
                      henvNRF₅ i b' ab' hsc' hbi' habi' hne' ha' hregs
                        (fun dep hdep hbd => hdeps dep hdep hbd.2)
                  have hnrfFinal : ActiveVal σ_end res → NoReachForbid st₅ Forbid BadReg BadDep res rv_end :=
                    fun ha' hregs hdeps => hnrfEnd ha' hregs (fun dep hdep hbd => hdeps dep hdep hbd.2)
                  have hstat02 : ArrayExtends st.statics st₂.statics := by rw [hstat₂]; exact hstat₁
                  have hstr02 : ArrayExtends st.strs st₂.strs := by rw [hstr₂]; exact hstr₁
                  have hsimFinal : Sim P ext B₅ st₅ Frame NoKill NoSpend Scope env aenv σ_end I envFoot :=
                    Sim_shrink_frame (fun _ hF => Or.inl (Or.inl (Or.inl hF))) hsim₅
                  have hvEndFinal : VSim P ext B₅ st₅ Frame NoKill NoSpend σ_end I endFoot res rv_end :=
                    VSim_shrink_frame (fun _ hF => Or.inl (Or.inl (Or.inl hF))) hvEnd
                  exact ⟨endFoot, by omega, hst₅,
                    Nat.le_trans hsz₁ (Nat.le_trans hsz₂ (Nat.le_trans hsz₃ (Nat.le_trans hsz₄ hsz₅))),
                    Nat.le_trans hcap₁ (Nat.le_trans hcap₂ (Nat.le_trans hcap₃ (Nat.le_trans hcap₄ hcap₅))),
                    hr₅.trans (hr₄.trans (hr₃.trans (hrg₂.trans hr₁))),
                    Nat.le_trans hnr₁ (Nat.le_trans (hnr₂ ▸ Nat.le_refl _) (Nat.le_trans hnr₃ (Nat.le_trans hnr₄ hnr₅))),
                    ((hstat02.trans hstat₃).trans hstat₄).trans hstat₅,
                    ((hstr02.trans hstr₃).trans hstr₄).trans hstr₅,
                    hpFrame₁.trans (hpresF2.trans ((hpFrame₃.mono fun _ h => Or.inl h).trans
                      ((hpFrame₄.mono fun _ h => Or.inl (Or.inl h)).trans
                        (hpFrame₅.mono fun _ h => Or.inl (Or.inl (Or.inl h)))))),
                    hpresEnvAll,
                    fun l o num ho hc => hpNum₅ l o num (hpNum₄ l o num (hpNum₃ l o num (hpresNum₂ l o num (hpNum₁ l o num ho hc) hc) hc) hc) hc,
                    honce₁.trans (honce₂.trans (honce₃.trans (honce₄.trans honce₅))),
                    hssf05,
                    hsimFinal, henvTaint₄.step hr₅ hnr₅, henvNRFFinal,
                    hvEndFinal, hdisjEnd, hnrfFinal, hnvEnd,
                    taint_of_vsim_src_none hresSrc hvEndFinal,
                    hliveEnd, SrcOk_none hresSrc⟩

/-! ## 5. Complete Mutual Soundness of `ModeOk` (`evalS_checked_sound`) -/

theorem transfer_nonValSafe {P : Prog} {fuel : Nat} {toBorrowed : Bool} {st : St} {v : Val}
    (hnv : NonValSafe st.heap v) :
    (transfer P fuel toBorrowed v).run st = .error .outOfFuel ∨
    (transfer P fuel toBorrowed v).run st = .ok (v, st) := by
  rcases hnv with ⟨k, rfl⟩ | ⟨loc, cap, o, num, rfl, ho, hcap, hcell⟩
  · unfold transfer
    have hleaf : (isLeaf (.imm k)).run st = .ok (false, st) := rfl
    have hco : (confinedOpen (.imm k)).run st = .ok (false, st) := rfl
    rw [M_bind_run, hleaf]; dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [M_bind_run, hco]; dsimp only
    simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    cases fuel with
    | zero => exact Or.inl rfl
    | succ _ => exact Or.inr rfl
  · unfold transfer
    have hlr : LiveRef st.heap (.ref loc cap []) := ⟨o, ho, hcap⟩
    rw [M_bind_run, isLeaf_ok hlr]; dsimp only
    rw [ho]; dsimp only
    have his : o.cell.isNum = true := by rw [hcell]; rfl
    simp only [his, ↓reduceIte]; exact Or.inr rfl

theorem AApps_nonempty_src_none {f : AVal} {xs : List AVal} {c : Cls} {σ σ' : AState} {r : AVal}
    (hok : AStateOk σ) (hne : xs ≠ []) (h : AApps f xs c σ r σ') : r.src = none := by
  cases h with
  | nil => exact absurd rfl hne
  | consLast hr =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsrc, _⟩ := Runs_applyValue hok hr
    exact hsrc
  | consMore hr hrest =>
    obtain ⟨hok₁, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsrc, _⟩ := Runs_applyValue hok hr
    exact AApps_src_none hok₁ hsrc hrest

theorem Runs_anProj_src_deps {P : Prog} {s : Ref} {i : Nat} {v res : AVal} {c : Cls} {σ σ' : AState}
    (h : Runs (anProj P s i v c) σ res σ') :
    res.src = none ∧ ∀ d ∈ res.deps, d ∈ v.deps := by
  have hInfo := (Runs_anProj h).2
  unfold Runs anProj at h; dsimp only at h
  cases hcs0 : (P.ctorsOf s)[0]? with
  | none =>
    simp only [hcs0] at h
    have hnil : (#[] : Array Field)[i]? = none := by simp
    simp only [hnil, CM_pure_run] at h
    have hEq := (Prod.mk.inj (Except.ok.inj h)).1; rw [← hEq]; exact ⟨rfl, fun _ h => by cases h⟩
  | some ctor =>
    simp only [hcs0] at h
    cases hco : P.ctorOf? ctor with
    | none =>
      simp only [hco] at h
      have hnil : (#[] : Array Field)[i]? = none := by simp
      simp only [hnil, CM_pure_run] at h
      have hEq := (Prod.mk.inj (Except.ok.inj h)).1; rw [← hEq]; exact ⟨rfl, fun _ h => by cases h⟩
    | some q =>
      rcases q with ⟨ind, ci, nP, fields⟩
      simp only [hco] at h
      cases hf : fields[i]? with
      | none =>
        simp only [hf, CM_pure_run] at h
        have hEq := (Prod.mk.inj (Except.ok.inj h)).1; rw [← hEq]; exact ⟨rfl, fun _ h => by cases h⟩
      | some f =>
        obtain ⟨_, hirr, himm, hnv, hval⟩ := hInfo ctor ind ci nP fields f hcs0 hco hf
        by_cases h1 : f.cls = .irr ∨ c = .irr
        · rw [hirr h1]; exact ⟨rfl, fun _ h => by cases h⟩
        · have hfNe : f.cls ≠ .irr := fun heq => h1 (Or.inl heq)
          have hcNe : c ≠ .irr := fun heq => h1 (Or.inr heq)
          cases hc : c with
          | irr => exact absurd hc hcNe
          | imm => rw [himm hfNe (Or.inl hc)]; exact ⟨rfl, fun _ h => by cases h⟩
          | leaf => rw [himm hfNe (Or.inr hc)]; exact ⟨rfl, fun _ h => by cases h⟩
          | val =>
            by_cases hv : v.cls = .val
            · rw [hval hfNe hc hv]; exact ⟨rfl, fun _ hd => hd⟩
            · rw [hnv hfNe hc hv]; exact ⟨rfl, fun _ hd => hd⟩

theorem Runs_anCtor_sat_src_valid {nP : Nat} {fields : Array Field} {avs : Array (Option AVal)}
    {c : Cls} {σ σ' : AState} {res : AVal}
    (hok : AStateOk σ) (hsat : nP + fields.size ≤ avs.size)
    (h : Runs (anCtor nP fields avs c) σ res σ') :
    res.src = none ∧ ValidDeps σ' res.deps := by
  obtain ⟨_, _, hstSz, _, _, _, _, _, hsatInfo⟩ := Runs_anCtor hok h
  obtain ⟨hEmpty, hWrap, hAlloc⟩ := hsatInfo hsat
  let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
  by_cases hke : kept.isEmpty = true
  · obtain ⟨rfl, rfl⟩ := hEmpty hke; exact ⟨rfl, fun _ h => by cases h⟩
  · have hkeF : kept.isEmpty = false := Bool.eq_false_iff.mpr hke
    by_cases hwr : ((c == .imm || c == .leaf) && kept.size == 1) = true
    · obtain ⟨rfl, hmatch⟩ := hWrap hkeF hwr
      cases hget : avs[nP + kept[0]!]? with
      | none => rw [hget] at hmatch; rw [hmatch]; exact ⟨rfl, fun _ h => by cases h⟩
      | some opt =>
        cases opt with
        | none => rw [hget] at hmatch; rw [hmatch]; exact ⟨rfl, fun _ h => by cases h⟩
        | some v => rw [hget] at hmatch; rw [hmatch.2]; exact ⟨rfl, hmatch.1⟩
    · have hwrF : ((c == .imm || c == .leaf) && kept.size == 1) = false := Bool.eq_false_iff.mpr hwr
      obtain ⟨_, _, _, hsrc, hkept, _, hdepsSub, _, _, hstUpd⟩ := hAlloc hkeF hwrF
      refine ⟨hsrc, fun d hd => ?_⟩
      obtain ⟨k, hk, v, f, havk, hfk, _, _, hdv⟩ := hdepsSub d hd
      have hvdV := (hkept k hk v f havk hfk).1
      have hlt0 := (hvdV d hdv).1
      refine ⟨hstSz ▸ hlt0, fun hdead => ?_⟩
      have h1 := hstUpd d hlt0; rw [hdead] at h1
      split at h1
      · cases h1
      · exact (hvdV d hdv).2 h1.symm

theorem APrimArgs_valid_deps {avs : List (Option AVal)} {σ σ' : AState} {deps regs : List Nat}
    (hok : AStateOk σ) (hprim : APrimArgs avs σ [] [] deps regs σ') :
    ValidDeps σ' deps := by
  obtain ⟨_, _, hszSt, _, _, _, _, hnd, _⟩ := APrimArgs_info hok hprim
  obtain ⟨_, _, _, _, _, _, _, _, _, hperA, hdepsSub, _⟩ := APrimArgs_spec hok hprim
  intro d hd
  rcases hdepsSub d hd with h0 | ⟨a, ha, _, hda⟩
  · cases h0
  · have hvdA := (hperA a ha).1
    have hlt0 := (hvdA d hda).1
    exact ⟨hszSt ▸ hlt0, fun hdead => (hvdA d hda).2 (hnd d hlt0 hdead)⟩

theorem collect_acc_nonempty : ∀ (t : Term) (acc : List Term), acc ≠ [] → (collect t acc).2 ≠ []
  | .app f a _, acc, _ => collect_acc_nonempty f (a :: acc) (by simp)
  | .irr, _, h | .var .., _, h | .const .., _, h | .natLit _, _, h | .strLit _, _, h
  | .lam .., _, h | .letE .., _, h | .proj .., _, h | .case .., _, h => h

theorem evalS_var_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {i : Nat} {c : Cls} {σ σ' : AState} {v : AVal}
    (hr : Runs (readVar aenv i) σ v σ') :
    ATermProp P ext B aenv (.var i c) σ { v with cls := c } σ' := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt _ _ _ _ henvTaint henvNRF hForbidLt _
  have hsc : Scope i := hfv i (.var (Nat.zero_le i))
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (by omega) (AStateLe.refl _) hsim.2.1 hsim.2.2.1 (RegsFuture.refl _)
          (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
          (PreservesActiveEnv.refl _ _ _ _ _) hsim
      obtain ⟨hσEq, ⟨bc, ab, hbi, habi, hmodeEq, hneAb, hvEq⟩, hvar⟩ :=
        var_bridge (c := c) (StOk_mono (by omega) hst) hsimB henvNRF hFlt hForbidLt hsc hr
      subst σ'
      obtain ⟨ab', hab', _, _, hvd0, _⟩ := Runs_readVar hr
      rw [habi] at hab'; cases hab'
      have hvd : ValidDeps σ ({ v with cls := c } : AVal).deps := by rw [hvEq]; exact hvd0
      let mVar : M Val := do
        let some b := env[i]? | stuckM
        if b.mode == BinderMode.erased then violate .erasedRead
        live b.val
        conform c b.val
      have hstep : (evalS P ext (n + 1) env (.var i c)).run (st, b0 + 1) = (liftM mVar).run (st, b0) := by
        conv => lhs; unfold evalS
        rw [MS_bind_run, MS_spend_succ]; rfl
      unfold TermPost; rw [hstep, MS_liftM_run]
      rcases hvar with hSt | ⟨rv, st', hrun, hrg, hnr, hstat', hstr', hsz, hcap, hpresAll, hpresF,
        honce, hssf, hst', hsim', henvNRF', hv', hdisj', hnrf', hnv', _⟩
      · change mVar.run st = .error .stuck at hSt
        rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · change mVar.run st = .ok (rv, st') at hrun
        rw [hrun]
        refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
        cases hokEq
        have htaint : ValidDeps σ ({ v with cls := c } : AVal).deps →
            (∀ c' ∈ rv.taint, c' < st'.nextRegion) ∧ OpenUnder st'.regions (I.regsOf ({ v with cls := c } : AVal).regs) rv := by
          intro _
          by_cases hcV : c = .val
          · subst hcV
            have hbcNeB : (bc.mode == BinderMode.erased) = false := BinderMode_beq_false_of_ne (hmodeEq ▸ hneAb)
            have hliveBc : LiveRef st.heap bc.val := by
              by_cases hact : ActiveVal σ (effVal ab)
              · exact (((hsimB.2.2.2.2.2.1 i bc ab hsc hbi habi).2 hneAb).2.2.2.2.2 hact).1.1.self.1
              · have his : IsOnceSrc σ (effVal ab) :=
                  Classical.byContradiction fun hn => hact ⟨hvd0, fun h => absurd h hn⟩
                exact (((hsimB.2.2.2.2.2.1 i bc ab hsc hbi habi).2 hneAb).2.2.2.2.1 hvd0 his).liveRef
            dsimp only [mVar] at hrun
            simp only [hbi, hbcNeB, Bool.false_eq_true, ↓reduceIte, M_bind_run, live_ok hliveBc] at hrun
            have hconf : (conform .val bc.val).run st = .ok (bc.val, st) := rfl
            rw [hconf] at hrun; cases hrun
            rw [hvEq]; exact henvTaint i bc ab hsc hbi habi hneAb
          · obtain ⟨_, hnv⟩ := hnv' hvd hcV
            have htn := hnv.taint_nil
            exact ⟨(fun _ hc => by rw [htn] at hc; cases hc), (fun _ hc => by rw [htn] at hc; cases hc)⟩
        have hsrc : SrcOk Scope aenv σ σ { v with cls := c } := by
          intro id hs; rw [hvEq] at hs; dsimp only [effVal] at hs; cases hs
          exact Or.inl ⟨i, ab, hsc, habi, hneAb, rfl, by rw [hvEq]; rfl, fun d => by rw [hvEq]⟩
        exact ⟨if c == .val then envFoot i else fun (_ : Nat) => False, by omega, hst', hsz, hcap,
          hrg, hnr ▸ Nat.le_refl _, hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
          hpresF, Sim_preserves_of_old (AStateLe.refl _) hpresAll hsimB,
          PreservesLocs_old_num hpresAll, honce, hssf, hsim',
          henvTaint.step hrg (hnr ▸ Nat.le_refl _), henvNRF', hv', hdisj', hnrf', hnv',
          htaint, live_of_vsim_validDeps hv' hvd, hsrc⟩

theorem evalS_proj_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {s : Ref} {i : Nat} {e : Term} {c : Cls}
    {σ σ₁ σ₂ σ₃ : AState} {v res : AVal}
    (heIH : ATermProp P ext B aenv e σ v σ₁)
    (hval : Runs (valid v "a projection") σ₁ () σ₂)
    (hproj : Runs (anProj P s i v c) σ₂ res σ₃) :
    ATermProp P ext B aenv (.proj s i e c) σ res σ₃ := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  cases hlc with | proj hlcE =>
  cases hcfd with | proj hcfdE =>
  obtain ⟨hvdV, hσ₂Eq⟩ := Runs_valid hval; subst σ₂
  obtain ⟨hσ₃Eq, _⟩ := Runs_anProj hproj; subst σ₃
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (by omega) (AStateLe.refl _) hsim.2.1 hsim.2.2.1 (RegsFuture.refl _)
          (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
          (PreservesActiveEnv.refl _ _ _ _ _) hsim
      have hstep : (evalS P ext (n + 1) env (.proj s i e c)).run (st, b0 + 1) =
          (do let xv ← evalS P ext n env e; liftM (projTail P s i xv c)).run (st, b0) := by
        conv => lhs; unfold evalS
        rw [MS_bind_run, MS_spend_succ]; rfl
      unfold TermPost; rw [hstep, MS_bind_run]
      obtain ⟨hnoVE, hokE⟩ := heIH hlcE hcfdE (B₀ := b0) (fuel := n) (by omega)
        (fun z hz => hfv z (.proj hz)) (StOk_mono (by omega) hst) hsimB hstat hFlt
        hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
      cases hevE : (evalS P ext n env e).run (st, b0) with
      | error e' =>
        refine ⟨fun k hk => by cases hk; exact hnoVE k hevE, fun _ _ _ h => by cases h⟩
      | ok pe =>
        rcases pe with ⟨xv, ⟨st₁, B₁⟩⟩; dsimp only
        obtain ⟨xFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
          hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
          hvX, hdisjX, hnrfX, _, _, _, _⟩ := hokE xv st₁ B₁ hevE
        let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
        have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
          h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
        have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
        obtain ⟨_, hpb⟩ := proj_bridge hst₁ (Sim_add_staticStr hsim₁) henvNRF₁ hFlt₁ hForbLt₁ hvdV hproj
          (VSim_add_staticStr hvX) hdisjX hnrfX
        rw [MS_liftM_run]
        rcases hpb with hSt | ⟨rv, st₂, hrunP, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpresAll₂, hpresF₂,
          honce₂, hssf₂, hst₂, hsim₂, henvNRF₂, hvR, hdisjR, hnrfR, hnvR, _⟩
        · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [hrunP]
          refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
          cases hokEq
          obtain ⟨hresSrc, hresDeps⟩ := Runs_anProj_src_deps hproj
          have hvdRes : ValidDeps σ₁ res.deps := fun d hd => hvdV d (hresDeps d hd)
          have hpresEnv₂ : PreservesActiveEnv Scope env aenv σ₁ st₁.heap st₂.heap :=
            Sim_preserves_of_old (AStateLe.refl _) hpresAll₂ hsim₁
          have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₁ st.heap st₂.heap := fun k bk abk hsc hbk habk hne ha =>
            let hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha
            hp1.trans ((hpresEnv₂ k bk abk hsc hbk habk hne ha).mono fun l hr => (Reach_congr hp1 l).mpr hr)
          have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
          have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hvR
          exact ⟨fun (_ : Nat) => False, by omega, hst₂,
            Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
            hrg₂.trans hr₁, Nat.le_trans hnr₁ (hnr₂ ▸ Nat.le_refl _),
            by rw [hstat₂]; exact hstat₁, by rw [hstr₂]; exact hstr₁,
            hpFrame₁.trans (hpresF₂.mono fun _ h => Or.inl h), hpresEnvAll,
            fun l o num ho hc => PreservesLocs_old_num hpresAll₂ l o num (hpNum₁ l o num ho hc) hc,
            honce₁.trans honce₂,
            StaticStrFresh.trans hsz₁ (hpresF₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
            hsimFinal, henvTaint₁.step hrg₂ (hnr₂ ▸ Nat.le_refl _), henvNRF₂,
            hvFinal, hdisjR, hnrfR, hnvR,
            taint_of_vsim_src_none hresSrc hvFinal,
            live_of_vsim_validDeps hvFinal hvdRes,
            SrcOk_none hresSrc⟩

theorem evalS_appVal_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {f a h : Term} {c : Cls} {args : Array Term}
    {σ σ₁ σ₂ σ₃ : AState} {fv res : AVal} {avs : List AVal}
    (hsp : termSpine (.app f a c) = (h, args))
    (hne : ∀ r rc, h ≠ .const r rc)
    (hhD : ATerm P aenv h σ fv σ₁) (hhIH : ATermProp P ext B aenv h σ fv σ₁)
    (hevD : AEvals P aenv args.toList σ₁ avs σ₂) (hevIH : AEvalsProp P ext B aenv args.toList σ₁ avs σ₂)
    (happs : AApps fv avs c σ₂ res σ₃) :
    ATermProp P ext B aenv (.app f a c) σ res σ₃ := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  have hcol := termSpine_eq_collect (.app f a c)
  rw [hsp] at hcol; dsimp only at hcol
  obtain ⟨hhCol, hargsCol⟩ := hcol
  have hargsNe : args.toList ≠ [] := by rw [hargsCol]; exact collect_acc_nonempty f [a] (by simp)
  have hlcCol := collect_lamsClosed (.app f a c) [] hlc (fun _ h => by cases h)
  have hcfdCol := collect_caseFieldsDistinct (.app f a c) [] hcfd (fun _ h => by cases h)
  have hlcH : LamsClosed h := hhCol ▸ hlcCol.1
  have hlcArgs : ∀ t ∈ args.toList, LamsClosed t := fun t ht => hlcCol.2 t (hargsCol ▸ ht)
  have hcfdH : CaseFieldsDistinct h := hhCol ▸ hcfdCol.1
  have hcfdArgs : ∀ t ∈ args.toList, CaseFieldsDistinct t := fun t ht => hcfdCol.2 t (hargsCol ▸ ht)
  have hfvH : ∀ x, FreeVarIn 0 h x → Scope x := fun x hx =>
    hfv x ((collect_freeVarIn (.app f a c) [] 0 x).1 (hhCol ▸ hx))
  have hfvArgs : ∀ t ∈ args.toList, ∀ x, FreeVarIn 0 t x → Scope x := fun t ht x hx => by
    rcases (collect_freeVarIn (.app f a c) [] 0 x).2 t (hargsCol ▸ ht) hx with ⟨_, ha', _⟩ | h0
    · cases ha'
    · exact hfv x h0
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      cases n with
      | zero =>
        cases b0 with
        | zero =>
          exact TermPost.of_outOfFuel (by
            unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only
            unfold spineS; rw [MS_bind_run, MS_spend_zero])
        | succ b1 =>
          exact TermPost.of_outOfFuel (by
            unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only
            unfold spineS; rw [MS_bind_run, MS_spend_succ]; rfl)
      | succ m =>
        cases b0 with
        | zero =>
          exact TermPost.of_outOfFuel (by
            unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only
            unfold spineS; rw [MS_bind_run, MS_spend_zero])
        | succ b1 =>
          have hok := hsim.2.1
          obtain ⟨hok₁, hle₁, hreg₁⟩ := ATerm_state_le hok hhD
          obtain ⟨hok₂, hle₂, hreg₂⟩ := AEvals_state_le hok₁ hevD
          obtain ⟨hok₃, hle₃, _, _⟩ := AApps_state_le hok₂ happs
          have hnk₂ : NoKillOk NoKill σ₂ := NoKillOk_of_AStateLe hle₃ hnkEnd
          have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnk₂
          have hnsp₂ : NoSpendOk NoSpend σ₂ := NoSpendOk_of_AStateLe hle₃ hnspEnd
          have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnsp₂
          let BadDep₂ : Nat → Prop := fun d => d < σ₂.st.size ∧ BadDep d
          let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
          have hBadDep₂ : ∀ d, BadDep₂ d → σ₂.st[d]? = some .live :=
            BadDepLive_of_AStateLe hle₃ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
          have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
            BadDepLive_of_AStateLe (hle₂.trans hle₃) (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
          have hstep : (evalS P ext (m + 2) env (.app f a c)).run (st, b1 + 2) =
              (do
                let fv_c ← evalS P ext m env h
                let vs ← evalListS P ext m env args.toList []
                applyAllS P ext m fv_c vs c).run (st, b1) := by
            conv => lhs; unfold evalS
            rw [MS_bind_run, MS_spend_succ]; dsimp only
            rw [show collect (.app f a c) [] = (h, args.toList) from Prod.ext hhCol.symm hargsCol.symm]
            conv => lhs; unfold spineS
            rw [MS_bind_run, MS_spend_succ]; dsimp only
            cases h with
            | const r rc => exact absurd rfl (hne r rc)
            | irr | var _ _ | natLit _ | strLit _ | app _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ => rfl
          unfold TermPost; rw [hstep, MS_bind_run]
          have hsimB : Sim P ext b1 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
            Sim_step (by omega) (AStateLe.refl _) hok hsim.2.2.1 (RegsFuture.refl _)
              (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
              (PreservesActiveEnv.refl _ _ _ _ _) hsim
          have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
            let hvI := ((hsimB.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
            henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
              (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
          obtain ⟨hnoVH, hokH⟩ := hhIH hlcH hcfdH (B₀ := b1) (fuel := m) (by omega) hfvH
            (StOk_mono (by omega) hst) hsimB hstat hFlt hnk₁ hnsp₁ hIZero hHeadReg henvTaint
            henvNRF_bd₁ hForbidLt hBadDep₁
          cases hevH : (evalS P ext m env h).run (st, b1) with
          | error e' =>
            refine ⟨fun k hk => by cases hk; exact hnoVH k hevH, fun _ _ _ h => by cases h⟩
          | ok ph =>
            rcases ph with ⟨fv_c, ⟨st₁, B₁⟩⟩; dsimp only
            obtain ⟨fFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
              hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
              hvF₁, hdisjF₁, hnrfF₁, hnvF₁, _, _, hsrcF₁⟩ := hokH fv_c st₁ B₁ hevH
            let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
            have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
            have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
              h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
            have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
            have hIZero₁ : ∀ rg, σ₁.nextRegion ≤ rg → I.reg rg = [] := fun rg hge =>
              hIZero rg (Nat.le_trans hle₁.2.1 hge)
            have hHeadReg₁ : st₁.regions.headD 0 = 0 ∨ st₁.regions.headD 0 ∈ I.reg (σ₁.regions.headD 1) := by
              rw [hr₁, hreg₁]; exact hHeadReg
            have henvNRF₁' : EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep₂ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
              henvNRF₁ i b' ab' hsc' hbi' habi' hne' ha' hregs
                (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le hbd.1 hle₂.1, hbd.2⟩)
            have hnrfF₁' : ActiveVal σ₁ fv → NoReachForbid st₁ Forbid BadReg BadDep₂ fv fv_c := fun ha' hregs hdeps =>
              hnrfF₁ ha' hregs (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le hbd.1 hle₂.1, hbd.2⟩)
            let prefF : List (Option (Val × AVal × (Nat → Prop))) := [some (fv_c, fv, fFoot)]
            have hArgPref : ArgListOk P ext B₁ st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
                Forbid BadReg BadDep₂ prefF := by
              refine ⟨fun idx v av ft hg => ?_, fun i j _ _ _ _ _ _ hij hg₁ hg₂ => ?_⟩
              · cases idx with
                | zero => simp [prefF] at hg; rcases hg with ⟨rfl, rfl, rfl⟩; exact ⟨VSim_add_staticStr hvF₁, hdisjF₁, hnrfF₁', hnvF₁⟩
                | succ _ => simp [prefF] at hg
              · cases i with
                | zero => cases j with | zero => exact absurd rfl hij | succ _ => simp [prefF] at hg₂
                | succ _ => simp [prefF] at hg₁
            have hPrefSrcF : PrefixSrcOk Scope aenv prefF :=
              PrefixSrcOk_of_SrcOk hsim.2.2.2.1 hsim₁ hsrcF₁
            have hArgsSrcF : ArgsSrcOk prefF := fun i j _ _ _ _ _ _ _ hg₁ hg₂ _ _ => by
              cases i with
              | zero => cases j with | zero => simp [prefF] at hg₁ hg₂; rcases hg₁ with ⟨_, rfl, _⟩; rcases hg₂ with ⟨_, rfl, _⟩; rfl | succ _ => simp [prefF] at hg₂
              | succ _ => simp [prefF] at hg₁
            obtain ⟨hnoVArgs, hokArgs⟩ := hevIH hlcArgs hcfdArgs (B₀ := B₁) (fuel := m) (by omega)
              hfvArgs hst₁ (Sim_add_staticStr hsim₁) hstat₁F hFlt₁ hnk₂ hnsp₂ hIZero₁ hHeadReg₁
              henvTaint₁ henvNRF₁' hForbLt₁ hBadDep₂ hArgPref hPrefSrcF hArgsSrcF
            rw [MS_bind_run]
            cases hevArgs : (evalListS P ext m env args.toList []).run (st₁, B₁) with
            | error e' =>
              refine ⟨fun k hk => by cases hk; exact hnoVArgs k hevArgs, fun _ _ _ h => by cases h⟩
            | ok pargs =>
              rcases pargs with ⟨vs, ⟨st₂, B₂⟩⟩; dsimp only
              obtain ⟨exArgs, hvsEq, havsEq, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
                hpFrame₂, hpEnv₂, hpNum₂, honce₂, hssf₂, hsim₂, henvTaint₂, henvNRF₂,
                hArgList₂, _, hArgsSrc₂⟩ := hokArgs vs st₂ B₂ hevArgs
              let Frame₂ : Nat → Prop := fun l => Frame₁ l ∨ StaticStrLoc st₂ l
              have hstat₂F : ∀ l, StaticStrLoc st₂ l → Frame₂ l := fun _ h => Or.inr h
              have hFlt₂ : ∀ l, Frame₂ l → l < st₂.heap.objs.size := fun l h =>
                h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt₁ l hF) hsz₂) (fun hss => StOk_staticStrLoc_lt hst₂ hss)
              have hForbLt₂ : ∀ l, Forbid l → l < st₂.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbLt₁ l hF) hsz₂
              obtain ⟨hvF₂, hdisjF₂, hnrfF₂, hnvF₂⟩ := hArgList₂.1 0 fv_c fv fFoot rfl
              have hArgTail₂ := ArgListOk_add_staticStr (ArgListOk_drop_prefix hArgList₂)
              have hExNe : exArgs ≠ [] := fun hnil => by
                have h1 := AEvals_length_eval hevD; rw [← havsEq, hnil] at h1
                exact hargsNe (List.eq_nil_of_length_eq_zero (by simpa using h1.symm))
              have hFvsA : ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop), exArgs[i]? = some (v, av, ft) →
                  (ActiveVal σ₂ av → Transferable σ₂ NoKill av → ActiveVal σ₂ fv →
                    (∀ d, d ∈ av.deps → ¬ (d ∈ fv.deps)) → ∀ l, OwnReach P st₂.heap v l → ¬ Reach st₂.heap fv_c l) ∧
                  (ActiveVal σ₂ fv → FootActive σ₂ fv → ActiveVal σ₂ av →
                    (fv.src = none ∨ fv.src ≠ av.src) → ∀ l, fFoot l → ¬ Reach st₂.heap v l) ∧
                  (ActiveVal σ₂ av → FootActive σ₂ av → ActiveVal σ₂ fv →
                    (av.src = none ∨ av.src ≠ fv.src) → ∀ l, ft l → ¬ Reach st₂.heap fv_c l) ∧
                  (∀ x, fv.src = some x → av.src = some x → fv.onceOnly = av.onceOnly) := by
                intro i v av ft hgi
                have hgi' : (prefF ++ exArgs.map some)[i + 1]? = some (some (v, av, ft)) := by simp [prefF, hgi]
                have hPair0 := hArgList₂.2 0 (i + 1) fv_c v fv av fFoot ft (by omega) rfl hgi'
                have hPair1 := hArgList₂.2 (i + 1) 0 v fv_c av fv ft fFoot (by omega) hgi' rfl
                exact ⟨hPair1.1, hPair0.2, hPair1.2, fun x hs1 hs2 => hArgsSrc₂ 0 (i + 1) fv_c v fv av fFoot ft x rfl hgi' hs1 hs2⟩
              have hPairSrc : ∀ (i j : Nat) (v₁ v₂ : Val) (av₁ av₂ : AVal) (ft₁ ft₂ : Nat → Prop) (x : Nat),
                  exArgs[i]? = some (v₁, av₁, ft₁) → exArgs[j]? = some (v₂, av₂, ft₂) →
                  av₁.src = some x → av₂.src = some x → av₁.onceOnly = av₂.onceOnly := by
                intro i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ hs₁ hs₂
                exact ArgsSrcOk_drop_prefix hArgsSrc₂ i j v₁ v₂ av₁ av₂ ft₁ ft₂ x (by simp [hg₁]) (by simp [hg₂]) hs₁ hs₂
              have happs' : AApps fv (exArgs.map (·.2.1)) c σ₂ res σ₃ := by rw [havsEq]; exact happs
              rw [← hvsEq]
              obtain ⟨hnoVApp, hokApp⟩ := applyAllS_bridge (fuel := m) happs'
                (Sim_add_staticStr hsim₂) hst₂ hstat₂F hFlt₂ hnkEnd hnspEnd
                (VSim_add_staticStr hvF₂) hdisjF₂ hnrfF₂ hnvF₂ (fun hnil => absurd hnil hExNe)
                hArgTail₂ hFvsA hPairSrc henvNRF₂ hForbLt₂
              refine ⟨hnoVApp, fun rv_end st₃ B₃ hevApp => ?_⟩
              obtain ⟨endFoot, hB₃, hst₃, hsz₃, hcap₃, hr₃, hnr₃, hstat₃, hstr₃,
                hpFrame₃, hpEnv₃, hpNum₃, honce₃, hssf₃, hsim₃, henvNRF₃,
                hvEnd, hdisjEnd, hnrfEnd, hnvEnd, hliveEnd⟩ := hokApp rv_end st₃ B₃ hevApp
              have havsNe : avs ≠ [] := fun hnil => hargsNe (List.eq_nil_of_length_eq_zero (by have := AEvals_length_eval hevD; rw [hnil] at this; simpa using this.symm))
              have hresSrc : res.src = none := AApps_nonempty_src_none hok₂ havsNe happs
              have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₃ st.heap st₃.heap := by
                intro k bk abk hsc hbk habk hne ha₃
                have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
                have ha₂ := ActiveVal.of_AStateLe hok₂ hle₃
                  (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) (hle₁.trans hle₂).1)
                  (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 (hle₁.trans hle₂).1) ha₃
                have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
                  (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
                  (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
                have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
                have hp2 := hpEnv₂ k bk abk hsc hbk habk hne ha₂
                have hp3 := hpEnv₃ k bk abk hsc hbk habk hne ha₃
                have hp12 : PreservesLocs (Reach st.heap bk.val) st.heap st₂.heap :=
                  hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
                exact hp12.trans (hp3.mono fun l hr => (Reach_congr hp12 l).mpr hr)
              have hssf02 : StaticStrFresh st st₂ :=
                StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂
              have hssf03 : StaticStrFresh st st₃ :=
                StaticStrFresh.trans (Nat.le_trans hsz₁ hsz₂) (hpFrame₃.mono fun _ h => Or.inr h) hssf02 hssf₃
              have henvNRFFinal : EnvNoReachForbid st₃ Scope env aenv σ₃ Forbid BadReg BadDep :=
                fun k bk abk hsc hbk habk hne ha hregs hdeps =>
                  henvNRF₃ k bk abk hsc hbk habk hne ha hregs (fun dep hdep hbd => hdeps dep hdep hbd.2)
              have hnrfFinal : ActiveVal σ₃ res → NoReachForbid st₃ Forbid BadReg BadDep res rv_end :=
                fun ha hregs hdeps => hnrfEnd ha hregs (fun dep hdep hbd => hdeps dep hdep hbd.2)
              have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl (Or.inl hF)) hsim₃
              have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl (Or.inl hF)) hvEnd
              exact ⟨endFoot, by omega, hst₃,
                Nat.le_trans hsz₁ (Nat.le_trans hsz₂ hsz₃), Nat.le_trans hcap₁ (Nat.le_trans hcap₂ hcap₃),
                hr₃.trans (hr₂.trans hr₁), Nat.le_trans hnr₁ (Nat.le_trans hnr₂ hnr₃),
                (hstat₁.trans hstat₂).trans hstat₃, (hstr₁.trans hstr₂).trans hstr₃,
                hpFrame₁.trans ((hpFrame₂.mono fun _ h => Or.inl h).trans (hpFrame₃.mono fun _ h => Or.inl (Or.inl h))),
                hpresEnvAll,
                fun l o num ho hc => hpNum₃ l o num (hpNum₂ l o num (hpNum₁ l o num ho hc) hc) hc,
                honce₁.trans (honce₂.trans honce₃), hssf03,
                hsimFinal, henvTaint₂.step hr₃ hnr₃, henvNRFFinal,
                hvFinal, hdisjEnd, hnrfFinal, hnvEnd,
                taint_of_vsim_src_none hresSrc hvFinal, hliveEnd, SrcOk_none hresSrc⟩

theorem evalS_alt_nonLam_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {t : Term} {a0 : AVal} {er fromCell : Bool}
    {rest : List (AVal × Bool × Bool)} {σ σ₁ σ₂ : AState} {f res : AVal}
    (hne : ∀ p res rc fvs body, t ≠ .lam p res rc fvs body)
    (hnoEr : ((a0, er, fromCell) :: rest).any (·.2.1) = false)
    (htD : ATerm P aenv t σ f σ₁) (htIH : ATermProp P ext B aenv t σ f σ₁)
    (happs : AApps f (((a0, er, fromCell) :: rest).map (·.1)) .val σ₁ res σ₂) :
    AAltProp P ext B aenv t ((a0, er, fromCell) :: rest) σ res σ₂ := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep cargs
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    hlen _ hArgsMeta hArgList
  cases cargs with
  | nil => simp at hlen
  | cons hdC restC =>
    rcases hdC with ⟨a, er_c⟩
    have haAllFalse : ∀ x ∈ ((a0, er, fromCell) :: rest), x.2.1 = false := fun x hx => by
      cases h : x.2.1 with
      | false => rfl
      | true =>
        have h1 : ((a0, er, fromCell) :: rest).any (·.2.1) = true :=
          List.any_eq_true.mpr ⟨x, hx, h⟩
        rw [h1] at hnoEr; cases hnoEr
    have hcAnyFalse : ((a, er_c) :: restC).any (·.2) = false := by
      cases h : ((a, er_c) :: restC).any (·.2) with
      | false => rfl
      | true =>
        obtain ⟨x, hx, hxT⟩ := List.any_eq_true.mp h
        obtain ⟨idx, hltC, rfl⟩ := List.getElem_of_mem hx
        have hltA : idx < ((a0, er, fromCell) :: rest).length := by omega
        rcases he : ((a0, er, fromCell) :: rest)[idx]'hltA with ⟨a1, er1, fc1⟩
        have hErEq := (hArgsMeta idx (((a, er_c) :: restC)[idx]'hltC).1 (((a, er_c) :: restC)[idx]'hltC).2
          a1 er1 fc1 (List.getElem?_eq_getElem hltC) (by rw [List.getElem?_eq_getElem hltA, he])).1
        have hF1 : er1 = false := haAllFalse (a1, er1, fc1) (he ▸ List.getElem_mem hltA)
        rw [hF1] at hErEq; rw [hErEq] at hxT; cases hxT
    cases fuel with
    | zero =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ b0 => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_succ]; rfl)
    | succ n =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ b0 =>
        have hok := hsim.2.1
        obtain ⟨hok₁, hle₁, hreg₁⟩ := ATerm_state_le hok htD
        obtain ⟨hok₂, hle₂, _, _⟩ := AApps_state_le hok₁ happs
        have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnkEnd
        have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnspEnd
        let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
        have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
          BadDepLive_of_AStateLe hle₂ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
        have hstep : (applyAltS P ext (n + 1) env t ((a, er_c) :: restC)).run (st, b0 + 1) =
            (do
              let fv_c ← evalS P ext n env t
              applyAllS P ext n fv_c (((a, er_c) :: restC).map (·.1 : Val × Bool → Val)) .val).run (st, b0) := by
          conv => lhs; unfold applyAltS
          rw [MS_bind_run, MS_spend_succ]; dsimp only
          cases t with
          | lam p res rc fvs body => exact absurd rfl (hne p res rc fvs body)
          | irr | var _ _ | const _ _ | natLit _ | strLit _ | app _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ =>
            simp only [hcAnyFalse, Bool.false_eq_true, ↓reduceIte]
        unfold TermPost; rw [hstep, MS_bind_run]
        let rawArgs : List (Val × AVal × (Nat → Prop)) :=
          (((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map fun ((v, _), (a1, _, _)) => (v, a1, fun (_ : Nat) => False)
        have hArgListEq :
            ((((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map
              fun ((v, _), (a1, er1, _)) => if er1 then none else some (v, a1, fun (_ : Nat) => False)) =
            rawArgs.map some := by
          dsimp only [rawArgs]; rw [List.map_map]
          apply List.map_congr_left
          rintro ⟨⟨v, ec⟩, ⟨a1, er1, fc1⟩⟩ hmem
          have hmemA : (a1, er1, fc1) ∈ ((a0, er, fromCell) :: rest) := (List.of_mem_zip hmem).2
          have herF : er1 = false := haAllFalse _ hmemA
          simp [herF]
        have hArgList0 : ArgListOk P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot
            Forbid BadReg BadDep₁ (rawArgs.map some) := by
          rw [← hArgListEq]
          refine ⟨fun k v av ft hg => ?_, hArgList.2⟩
          obtain ⟨hv, hd, hnrf, hnv⟩ := hArgList.1 k v av ft hg
          exact ⟨VSim_step (by omega) hok (AStateLe.refl _) (RegsFuture.refl _) (PreservesOnceShell.refl _)
              (StaticStrFresh.refl _) (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _) hv,
            hd, fun ha hregs hdeps => hnrf ha hregs (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hv.2.1 dep hdep) hle₁.1, hbd⟩), hnv⟩
        have hrawSrcNone : ∀ (idx : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
            (rawArgs.map some)[idx]? = some (some (v, av, ft)) → av.src = none := by
          intro idx v av ft hg
          rw [← hArgListEq] at hg
          have hltZ : idx < (((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).length := by
            simp only [List.getElem?_map] at hg
            cases hz : (((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest))[idx]? with
            | none => rw [hz] at hg; cases hg
            | some _ => exact (List.getElem?_eq_some_iff.mp hz).1
          have hltC : idx < ((a, er_c) :: restC).length := by rw [List.length_zip] at hltZ; omega
          have hltA : idx < ((a0, er, fromCell) :: rest).length := by rw [List.length_zip] at hltZ; omega
          simp only [List.getElem?_map, List.getElem?_eq_getElem hltZ, List.getElem_zip] at hg
          rcases hc' : ((a, er_c) :: restC)[idx]'hltC with ⟨v', ec'⟩
          rcases ha' : ((a0, er, fromCell) :: rest)[idx]'hltA with ⟨a1', er1', fc1'⟩
          rw [hc', ha'] at hg
          have herF : er1' = false := haAllFalse _ (ha' ▸ List.getElem_mem hltA)
          simp [herF] at hg
          rcases hg with ⟨_, rfl, _⟩
          exact (hArgsMeta idx v' ec' a1' er1' fc1' (by rw [List.getElem?_eq_getElem hltC, hc'])
            (by rw [List.getElem?_eq_getElem hltA, ha'])).2.1
        have hPrefSrc0 : PrefixSrcOk Scope aenv (rawArgs.map some) := fun idx v av ft hg id hs => by
          rw [hrawSrcNone idx v av ft hg] at hs; cases hs
        have hArgsSrc0 : ArgsSrcOk (rawArgs.map some) := fun i _ _ _ _ _ _ _ _ hg₁ _ hs₁ _ => by
          rw [hrawSrcNone i _ _ _ hg₁] at hs₁; cases hs₁
        have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
          Sim_step (by omega) (AStateLe.refl _) hok hsim.2.2.1 (RegsFuture.refl _)
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _) hsim
        have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
          let hvI := ((hsimB.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
          henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
            (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
        obtain ⟨hnoVT, hokT⟩ := ArgListOk_push (m := evalS P ext n env t) (av₂ := f)
          hle₁ hsimB (StOk_mono (by omega) hst) hFlt hnk₁ hnsp₁ henvNRF_bd₁ hForbidLt hBadDep₁
          hArgList0 hPrefSrc0 hArgsSrc0
          (fun Frame' NoKill' NoSpend' Forbid' BadReg' BadDep' hsim' hstat' hFlt' hnk' hnsp' henvNRF' hForbLt' hBadDep' => by
            obtain ⟨hno, hok'⟩ := htIH hlc hcfd (B₀ := b0) (fuel := n) (by omega) hfv
              (StOk_mono (by omega) hst) hsim' hstat' hFlt' hnk' hnsp' hIZero hHeadReg
              henvTaint henvNRF' hForbLt' hBadDep'
            refine ⟨hno, fun v₂ st₁ B₁ hev => ?_⟩
            obtain ⟨ft₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, _, h16, h17, h18, h19, h20, _, _, h23⟩ :=
              hok' v₂ st₁ B₁ hev
            exact ⟨ft₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h16, h17, h18, h19, h20, h23⟩)
        cases hevT : (evalS P ext n env t).run (st, b0) with
        | error e' =>
          refine ⟨fun k hk => by cases hk; exact hnoVT k hevT, fun _ _ _ h => by cases h⟩
        | ok pt =>
          rcases pt with ⟨fv_c, ⟨st₁, B₁⟩⟩; dsimp only
          obtain ⟨fFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
            hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvNRF₁,
            hArgList₁, _, hArgsSrc₁⟩ := hokT fv_c st₁ B₁ hevT
          let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
          have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
          have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
            h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
          have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
          have hgetF : (rawArgs.map some ++ [some (fv_c, f, fFoot)])[rawArgs.length]? = some (some (fv_c, f, fFoot)) := by
            simp
          obtain ⟨hvF₁, hdisjF₁, hnrfF₁, hnvF₁⟩ := hArgList₁.1 rawArgs.length fv_c f fFoot hgetF
          have hArgRaw₁ : ArgListOk P ext B₁ st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
              Forbid BadReg BadDep₁ (rawArgs.map some) := by
            refine ArgListOk_add_staticStr ⟨fun k v av ft hg => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
            · have hltK : k < (rawArgs.map some).length := (List.getElem?_eq_some_iff.mp hg).1
              exact hArgList₁.1 k v av ft (by rw [List.getElem?_append_left hltK]; exact hg)
            · have hltI : i < (rawArgs.map some).length := (List.getElem?_eq_some_iff.mp hg₁).1
              have hltJ : j < (rawArgs.map some).length := (List.getElem?_eq_some_iff.mp hg₂).1
              exact hArgList₁.2 i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij
                (by rw [List.getElem?_append_left hltI]; exact hg₁) (by rw [List.getElem?_append_left hltJ]; exact hg₂)
          have hFvsA : ∀ (k : Nat) (v : Val) (av : AVal) (ft : Nat → Prop), rawArgs[k]? = some (v, av, ft) →
              (ActiveVal σ₁ av → Transferable σ₁ NoKill av → ActiveVal σ₁ f →
                (∀ d, d ∈ av.deps → ¬ (d ∈ f.deps)) → ∀ l, OwnReach P st₁.heap v l → ¬ Reach st₁.heap fv_c l) ∧
              (ActiveVal σ₁ f → FootActive σ₁ f → ActiveVal σ₁ av →
                (f.src = none ∨ f.src ≠ av.src) → ∀ l, fFoot l → ¬ Reach st₁.heap v l) ∧
              (ActiveVal σ₁ av → FootActive σ₁ av → ActiveVal σ₁ f →
                (av.src = none ∨ av.src ≠ f.src) → ∀ l, ft l → ¬ Reach st₁.heap fv_c l) ∧
              (∀ x, f.src = some x → av.src = some x → f.onceOnly = av.onceOnly) := by
            intro k v av ft hgk
            have hltK : k < rawArgs.length := (List.getElem?_eq_some_iff.mp hgk).1
            have hgk' : (rawArgs.map some ++ [some (fv_c, f, fFoot)])[k]? = some (some (v, av, ft)) := by
              rw [List.getElem?_append_left (by simp [hltK])]; simp [hgk]
            have hPairK := hArgList₁.2 k rawArgs.length v fv_c av f ft fFoot (by omega) hgk' hgetF
            have hPairF := hArgList₁.2 rawArgs.length k fv_c v f av fFoot ft (by omega) hgetF hgk'
            exact ⟨hPairK.1, hPairF.2, hPairK.2, fun x hs1 hs2 => hArgsSrc₁ rawArgs.length k fv_c v f av fFoot ft x hgetF hgk' hs1 hs2⟩
          have hPairSrc : ∀ (i j : Nat) (v₁ v₂ : Val) (av₁ av₂ : AVal) (ft₁ ft₂ : Nat → Prop) (x : Nat),
              rawArgs[i]? = some (v₁, av₁, ft₁) → rawArgs[j]? = some (v₂, av₂, ft₂) →
              av₁.src = some x → av₂.src = some x → av₁.onceOnly = av₂.onceOnly := by
            intro i j v₁ v₂ av₁ av₂ ft₁ ft₂ x hg₁ hg₂ hs₁ hs₂
            have hltI : i < rawArgs.length := (List.getElem?_eq_some_iff.mp hg₁).1
            have hltJ : j < rawArgs.length := (List.getElem?_eq_some_iff.mp hg₂).1
            exact hArgsSrc₁ i j v₁ v₂ av₁ av₂ ft₁ ft₂ x
              (by rw [List.getElem?_append_left (by simp [hltI])]; simp [hg₁])
              (by rw [List.getElem?_append_left (by simp [hltJ])]; simp [hg₂]) hs₁ hs₂
          have hrawMapV : rawArgs.map (·.1) = ((a, er_c) :: restC).map (·.1) := by
            dsimp only [rawArgs]; rw [List.map_map]
            have h1 : (((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map (fun x => x.1.1) =
                ((((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map Prod.fst).map (·.1) := by rw [List.map_map]; rfl
            change (((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map (fun x => x.1.1) = _
            rw [h1, List.map_fst_zip (by omega)]
          have hrawMapA : rawArgs.map (·.2.1) = ((a0, er, fromCell) :: rest).map (·.1) := by
            dsimp only [rawArgs]; rw [List.map_map]
            have h1 : (((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map (fun x => x.2.1) =
                ((((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map Prod.snd).map (·.1) := by rw [List.map_map]; rfl
            change (((a, er_c) :: restC).zip ((a0, er, fromCell) :: rest)).map (fun x => x.2.1) = _
            rw [h1, List.map_snd_zip (by omega)]
          have hrawNe : rawArgs ≠ [] := by simp [rawArgs]
          have happs' : AApps f (rawArgs.map (·.2.1)) .val σ₁ res σ₂ := by rw [hrawMapA]; exact happs
          rw [← hrawMapV]
          obtain ⟨hnoVApp, hokApp⟩ := applyAllS_bridge (fuel := n) happs'
            (Sim_add_staticStr hsim₁) hst₁ hstat₁F hFlt₁ hnkEnd hnspEnd
            (VSim_add_staticStr hvF₁) hdisjF₁ hnrfF₁ hnvF₁ (fun hnil => absurd hnil hrawNe)
            hArgRaw₁ hFvsA hPairSrc henvNRF₁ hForbLt₁
          refine ⟨hnoVApp, fun rv_end st₂ B₂ hevApp => ?_⟩
          obtain ⟨endFoot, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
            hpFrame₂, hpEnv₂, hpNum₂, honce₂, hssf₂, hsim₂, henvNRF₂,
            hvEnd, hdisjEnd, hnrfEnd, hnvEnd, hliveEnd⟩ := hokApp rv_end st₂ B₂ hevApp
          have hresSrc : res.src = none := AApps_nonempty_src_none hok₁ (by simp) happs
          have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₂ st.heap st₂.heap := by
            intro k bk abk hsc hbk habk hne ha₂
            have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
            have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
              (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
              (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
            have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
            have hp2 := hpEnv₂ k bk abk hsc hbk habk hne ha₂
            exact hp1.trans (hp2.mono fun l hr => (Reach_congr hp1 l).mpr hr)
          have hssf02 : StaticStrFresh st st₂ :=
            StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂
          have henvNRFFinal : EnvNoReachForbid st₂ Scope env aenv σ₂ Forbid BadReg BadDep :=
            fun k bk abk hsc hbk habk hne ha hregs hdeps =>
              henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun dep hdep hbd => hdeps dep hdep hbd.2)
          have hnrfFinal : ActiveVal σ₂ res → NoReachForbid st₂ Forbid BadReg BadDep res rv_end :=
            fun ha hregs hdeps => hnrfEnd ha hregs (fun dep hdep hbd => hdeps dep hdep hbd.2)
          have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
          have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hvEnd
          exact ⟨endFoot, by omega, hst₂,
            Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
            hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂,
            hstat₁.trans hstat₂, hstr₁.trans hstr₂,
            hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
            fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
            honce₁.trans honce₂, hssf02,
            hsimFinal, henvTaint.step (hr₂.trans hr₁) (Nat.le_trans hnr₁ hnr₂), henvNRFFinal,
            hvFinal, hdisjEnd, hnrfFinal, hnvEnd,
            taint_of_vsim_src_none hresSrc hvFinal, hliveEnd, SrcOk_none hresSrc⟩

theorem evalS_call_ctor_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {r ind : Ref} {ci nP : Nat} {fields : Array Field} {args : List Term} {c : Cls}
    {σ σ₁ σ₂ : AState} {avs : List (Option AVal)} {res : AVal}
    (hfind : P.find? r = some (.ctor ind ci nP fields))
    (hargsD : ACallArgs P (some (.ctor ind ci nP fields)) aenv 0 args σ avs σ₁)
    (hargsIH : ACallArgsProp P ext B (some (.ctor ind ci nP fields)) aenv 0 args σ avs σ₁)
    (hctor : Runs (anCtor nP fields avs.toArray c) σ₁ res σ₂) :
    ACallProp P ext B aenv r args c σ res σ₂ := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  have hok := hsim.2.1
  obtain ⟨hok₁, hle₁, hreg₁⟩ := ACallArgs_state_le hok hargsD
  obtain ⟨hok₂, hle₂, _, _, _, _, _, _, _⟩ := Runs_anCtor hok₁ hctor
  have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnkEnd
  have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnspEnd
  let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
  have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
    BadDepLive_of_AStateLe hle₂ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
  have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
    let hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
    henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
      (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
  unfold TermPost; rw [hfind, MS_bind_run]
  obtain ⟨hnoVA, hokA⟩ := hargsIH hlc hcfd (B₀ := B₀) (fuel := fuel) (pref := []) hB₀ hfv hst hsim hstat hFlt
    hnk₁ hnsp₁ hIZero hHeadReg henvTaint henvNRF_bd₁ hForbidLt hBadDep₁
    ⟨(fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩
    (fun _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ _ h => by cases h)
  cases hevA : (evalCallArgsS P ext fuel env (some (.ctor ind ci nP fields)) (args.zipIdx 0) []).run (st, B₀) with
  | error e =>
    refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
  | ok pa =>
    rcases pa with ⟨vs, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨cargs, hmatch, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
      hArgList₁, _, _⟩ := hokA vs st₁ B₁ hevA
    simp only [List.nil_append] at hArgList₁
    cases fuel with
    | zero =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, b1 + 1) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ n =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext (n + 1) r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        have hstep : (callWithS P ext (n + 1) r vs c).run (st₁, b1 + 1) =
            (if vs.length < nP + fields.size then liftM (makePap P n r #[] vs)
             else if vs.length > nP + fields.size then liftM stuckM
             else liftM (construct r fields (vs.drop nP) c)).run (st₁, b1) := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [hfind]
        rw [hstep]
        let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
        have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
        have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
          h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
        have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
        have hsim₁b : Sim P ext b1 st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot :=
          Sim_step (by omega) (AStateLe.refl _) hok₁ hsim₁.2.2.1 (RegsFuture.refl _)
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _) (Sim_add_staticStr hsim₁)
        have hArgList₁b : ArgListOk P ext b1 st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
            Forbid BadReg BadDep₁ cargs := by
          have h1 := ArgListOk_add_staticStr hArgList₁
          refine ⟨fun k v av ft hg => ?_, h1.2⟩
          obtain ⟨hv, hd, hnrf, hnv⟩ := h1.1 k v av ft hg
          exact ⟨VSim_step (by omega) hok₁ (AStateLe.refl _) (RegsFuture.refl _) (PreservesOnceShell.refl _)
              (StaticStrFresh.refl _) (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _) hv,
            hd, hnrf, hnv⟩
        by_cases hlt : vs.length < nP + fields.size
        · simp only [hlt, ↓reduceIte, MS_liftM_run]
          obtain ⟨hnoVP, hokP⟩ := ctor_pap_bridge (fuel := n) hfind hlt hmatch hctor
            hsim₁b (StOk_mono (by omega) hst₁) hstat₁F hFlt₁ hArgList₁b henvNRF₁ hForbLt₁
          cases hrunP : (makePap P n r #[] vs).run st₁ with
          | error e =>
            refine ⟨fun k hk => by cases hk; exact hnoVP k hrunP, fun _ _ _ h => by cases h⟩
          | ok pp =>
            rcases pp with ⟨rv, st₂⟩; dsimp only
            obtain ⟨hst₂, hsz₂, hcap₂, hrg₂, hnr₂, hstat₂, hstr₂, hpFrame₂, hpEnv₂, hpNum₂,
              honce₂, hssf₂, hsim₂, henvNRF₂, hv₂, hdisj₂, hnrf₂, hnv₂, hlive₂, _⟩ := hokP rv st₂ hrunP
            have hltA : avs.toArray.size < nP + fields.size := by
              have hlenEq : avs.length = vs.length := hmatch.2.1.symm.trans hmatch.1
              simpa [hlenEq] using hlt
            have hresSrc : res.src = none := ((Runs_anCtor hok₁ hctor).2.2.2.2.2.2.2.1 hltA).2.2.2.2.1
            have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₂ st.heap st₂.heap := by
              intro k bk abk hsc hbk habk hne ha₂
              have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
              have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
                (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
                (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
              have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
              exact hp1.trans ((hpEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
            have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
            have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hv₂
            refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
            cases hokEq
            exact ⟨fun (_ : Nat) => False, by omega, hst₂,
              Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hrg₂.trans hr₁, Nat.le_trans hnr₁ hnr₂,
              hstat₁.trans hstat₂, hstr₁.trans hstr₂,
              hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
              fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
              honce₁.trans honce₂,
              StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
              hsimFinal, henvTaint₁.step hrg₂ hnr₂,
              (fun k bk abk hsc hbk habk hne ha hregs hdeps => henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
              hvFinal, hdisj₂,
              (fun ha hregs hdeps => hnrf₂ ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
              hnv₂, taint_of_vsim_src_none hresSrc hvFinal, hlive₂, SrcOk_none hresSrc⟩
        · simp only [hlt, ↓reduceIte]
          by_cases hgt : vs.length > nP + fields.size
          · simp only [hgt, ↓reduceIte, MS_liftM_run]; unfold stuckM; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · simp only [hgt, ↓reduceIte, MS_liftM_run]
            have hsat : nP + fields.size ≤ cargs.length := by have := hmatch.1; omega
            have hsatA : nP + fields.size ≤ avs.toArray.size := by have := hmatch.1; have := hmatch.2.1; simp; omega
            have hkeptPres : ∀ (k : Nat) (f : Field), fields[k]? = some f → f.kept = true →
                ∃ v av ft, cargs[nP + k]? = some (some (v, av, ft)) := by
              intro k f hfk hkept
              have hltF : k < fields.size := (Array.getElem?_eq_some_iff.mp hfk).1
              have hltC : nP + k < cargs.length := by omega
              have hltA : nP + k < avs.length := hmatch.2.1 ▸ hltC
              cases hc : cargs[nP + k]? with
              | none => exact absurd (List.getElem?_eq_none_iff.mp hc) (Nat.not_le_of_lt hltC)
              | some opt =>
                cases opt with
                | some p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩
                | none =>
                  have hm := hmatch.2.2 (nP + k); rw [hc] at hm
                  have her := ((ACallArgs_erased_iff hargsD).2 (nP + k) hltA).mp hm.2
                  simp only [Nat.zero_add, erasedAt, show ¬ (nP + k < nP) by omega, ↓reduceIte,
                    Nat.add_sub_cancel_left, hfk, Option.map_some, Option.getD_some] at her
                  unfold Field.kept at hkept
                  cases hfM : f.mode <;> simp [hfM] at her hkept
            have hsync : ∀ (idx : Nat),
                (cargs[idx]? = some none → avs[idx]? = some none) ∧
                (∀ v av ft, cargs[idx]? = some (some (v, av, ft)) → vs[idx]? = some v ∧ avs[idx]? = some (some av)) := by
              intro idx
              have hm := hmatch.2.2 idx
              refine ⟨fun h => by rw [h] at hm; exact hm.2, fun v av ft h => by rw [h] at hm; exact hm⟩
            have hBadDep₂ : ∀ d, BadDep₁ d → σ₂.st[d]? = some .live := fun d hbd => hBadDepEnd d hbd.2
            rcases ctor_sat_bridge hfind (StOk_mono (by omega) hst₁) hsim₁b henvNRF₁ hFlt₁ hForbLt₁
                hBadDep₂ hmatch.1.symm hmatch.2.1.symm hsat hsync hkeptPres hArgList₁b hctor with hSt |
              ⟨rv, st₂, rFoot, hrunC, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpresAll₂, honce₂, hssf₂,
               hst₂, hsim₂, henvNRF₂, hv₂, hdisj₂, hnrf₂, hnv₂⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hrunC]
              refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
              cases hokEq
              obtain ⟨hresSrc, hvdRes⟩ := Runs_anCtor_sat_src_valid hok₁ hsatA hctor
              have hpresEnv₂ : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap :=
                Sim_preserves_of_old hle₂ hpresAll₂ hsim₁
              have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₂ st.heap st₂.heap := by
                intro k bk abk hsc hbk habk hne ha₂
                have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
                have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
                  (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
                  (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
                have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
                exact hp1.trans ((hpresEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
              have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
              have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hv₂
              exact ⟨rFoot, by omega, hst₂,
                Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hrg₂.trans hr₁,
                Nat.le_trans hnr₁ (hnr₂ ▸ Nat.le_refl _),
                by rw [hstat₂]; exact hstat₁, by rw [hstr₂]; exact hstr₁,
                hpFrame₁.trans (hpresAll₂.mono fun l hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁),
                hpresEnvAll,
                fun l o num ho hc => PreservesLocs_old_num hpresAll₂ l o num (hpNum₁ l o num ho hc) hc,
                honce₁.trans honce₂,
                StaticStrFresh.trans hsz₁ (hpresAll₂.mono fun l hss => StOk_staticStrLoc_lt hst₁ hss) hssf₁ hssf₂,
                hsimFinal, henvTaint₁.step hrg₂ (hnr₂ ▸ Nat.le_refl _),
                (fun k bk abk hsc hbk habk hne ha hregs hdeps => henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
                hvFinal, hdisj₂,
                (fun ha hregs hdeps => hnrf₂ ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
                hnv₂, taint_of_vsim_src_none hresSrc hvFinal,
                live_of_vsim_validDeps hvFinal hvdRes, SrcOk_none hresSrc⟩

theorem evalS_call_prim_case {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {r : Ref} {p : Prim} {args : List Term} {c : Cls}
    {σ σ₁ σ₂ : AState} {avs : List (Option AVal)} {deps regs : List Nat}
    (hfind : P.find? r = some (.prim p))
    (hargsD : ACallArgs P (some (.prim p)) aenv 0 args σ avs σ₁)
    (hargsIH : ACallArgsProp P ext B (some (.prim p)) aenv 0 args σ avs σ₁)
    (hprim : APrimArgs avs σ₁ [] [] deps regs σ₂) :
    ACallProp P ext B aenv r args c σ
      (if avs.length < p.arity then { cls := .val, deps, regs, skel := .unknown } else { cls := c }) σ₂ := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  have hok := hsim.2.1
  obtain ⟨hok₁, hle₁, hreg₁⟩ := ACallArgs_state_le hok hargsD
  obtain ⟨hok₂, hle₂, _, _, _, _, _, _, _⟩ := APrimArgs_info hok₁ hprim
  have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnkEnd
  have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnspEnd
  let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
  have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
    BadDepLive_of_AStateLe hle₂ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
  have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
    let hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
    henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
      (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
  unfold TermPost; rw [hfind, MS_bind_run]
  obtain ⟨hnoVA, hokA⟩ := hargsIH hlc hcfd (B₀ := B₀) (fuel := fuel) (pref := []) hB₀ hfv hst hsim hstat hFlt
    hnk₁ hnsp₁ hIZero hHeadReg henvTaint henvNRF_bd₁ hForbidLt hBadDep₁
    ⟨(fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩
    (fun _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ _ h => by cases h)
  cases hevA : (evalCallArgsS P ext fuel env (some (.prim p)) (args.zipIdx 0) []).run (st, B₀) with
  | error e =>
    refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
  | ok pa =>
    rcases pa with ⟨vs, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨cargs, hmatch, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
      hArgList₁, _, _⟩ := hokA vs st₁ B₁ hevA
    simp only [List.nil_append] at hArgList₁
    cases fuel with
    | zero =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, b1 + 1) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ n =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext (n + 1) r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        have hstep : (callWithS P ext (n + 1) r vs c).run (st₁, b1 + 1) =
            (if vs.length < p.arity then liftM (makePap P n r #[] vs)
             else if vs.length > p.arity then liftM stuckM
             else liftM do conform c (← prim p vs)).run (st₁, b1) := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [hfind]
        rw [hstep]
        have hlenEq : avs.length = vs.length := hmatch.2.1.symm.trans hmatch.1
        let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
        have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
          h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
        have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
        have hsim₁b : Sim P ext b1 st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot :=
          Sim_step (by omega) (AStateLe.refl _) hok₁ hsim₁.2.2.1 (RegsFuture.refl _)
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _) (Sim_add_staticStr hsim₁)
        have hArgList₁b : ArgListOk P ext b1 st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
            Forbid BadReg BadDep₁ cargs := by
          have h1 := ArgListOk_add_staticStr hArgList₁
          refine ⟨fun k v av ft hg => ?_, h1.2⟩
          obtain ⟨hv, hd, hnrf, hnv⟩ := h1.1 k v av ft hg
          exact ⟨VSim_step (by omega) hok₁ (AStateLe.refl _) (RegsFuture.refl _) (PreservesOnceShell.refl _)
              (StaticStrFresh.refl _) (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _) hv,
            hd, hnrf, hnv⟩
        by_cases hlt : vs.length < p.arity
        · have hltA : avs.length < p.arity := hlenEq ▸ hlt
          simp only [hlt, hltA, ↓reduceIte, MS_liftM_run]
          obtain ⟨hnoVP, hokP⟩ := prim_pap_bridge (fuel := n) hidx hext hih (by omega) hfind hmatch hprim
            hsim₁b (StOk_mono (by omega) hst₁) hFlt₁ hArgList₁b henvNRF₁ hForbLt₁
          cases hrunP : (makePap P n r #[] vs).run st₁ with
          | error e =>
            refine ⟨fun k hk => by cases hk; exact hnoVP k hrunP, fun _ _ _ h => by cases h⟩
          | ok pp =>
            rcases pp with ⟨rv, st₂⟩; dsimp only
            obtain ⟨hst₂, hsz₂, hcap₂, hrg₂, hnr₂, hstat₂, hstr₂, hpFrame₂, hpEnv₂, hpNum₂,
              honce₂, hssf₂, hsim₂, henvNRF₂, hv₂, hdisj₂, hnrf₂, hnv₂, _⟩ := hokP rv st₂ hrunP
            have hvdRes : ValidDeps σ₂ ({ cls := .val, deps, regs, skel := .unknown } : AVal).deps :=
              APrimArgs_valid_deps hok₁ hprim
            have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₂ st.heap st₂.heap := by
              intro k bk abk hsc hbk habk hne ha₂
              have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
              have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
                (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
                (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
              have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
              exact hp1.trans ((hpEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
            have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
            have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hv₂
            refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
            cases hokEq
            exact ⟨fun (_ : Nat) => False, by omega, hst₂,
              Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hrg₂.trans hr₁, Nat.le_trans hnr₁ hnr₂,
              hstat₁.trans hstat₂, hstr₁.trans hstr₂,
              hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
              fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
              honce₁.trans honce₂,
              StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
              hsimFinal, henvTaint₁.step hrg₂ hnr₂,
              (fun k bk abk hsc hbk habk hne ha hregs hdeps => henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
              hvFinal, hdisj₂,
              (fun ha hregs hdeps => hnrf₂ ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
              hnv₂, taint_of_vsim_src_none rfl hvFinal,
              live_of_vsim_validDeps hvFinal hvdRes, SrcOk_none rfl⟩
        · have hltA : ¬ (avs.length < p.arity) := by omega
          simp only [hlt, hltA, ↓reduceIte]
          by_cases hgt : vs.length > p.arity
          · simp only [hgt, ↓reduceIte, MS_liftM_run]; unfold stuckM; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
          · simp only [hgt, ↓reduceIte, MS_liftM_run]
            have hmapAvs : cargs.map (Option.map fun x => x.2.1) = avs := by
              apply List.ext_getElem?
              intro idx
              rw [List.getElem?_map]
              have hm := hmatch.2.2 idx
              cases hc : cargs[idx]? with
              | none => rw [hc] at hm; exact hm.2.symm
              | some opt =>
                cases opt with
                | none => rw [hc] at hm; exact hm.2.symm
                | some t => rw [hc] at hm; exact hm.2.symm
            have hNoneLive : ∀ (idx : Nat) v, cargs[idx]? = some none → vs[idx]? = some v → LiveRef st₁.heap v := by
              intro idx v hc _
              have hltC : idx < cargs.length := (List.getElem?_eq_some_iff.mp hc).1
              have hltA' : idx < avs.length := hmatch.2.1 ▸ hltC
              have hm := hmatch.2.2 idx; rw [hc] at hm
              have her := ((ACallArgs_erased_iff hargsD).2 idx hltA').mp hm.2
              simp [erasedAt] at her
            obtain ⟨_, _, _, hps⟩ := prim_sat_bridge (StOk_mono (by omega) hst₁) hsim₁b henvNRF₁ hFlt₁ hForbLt₁
              hArgList₁b hmatch.1.symm
              (fun idx v av ft hg => by have hm := hmatch.2.2 idx; rw [hg] at hm; exact hm.1)
              hNoneLive (hmapAvs.symm ▸ hprim)
            rcases hps with hSt | ⟨rv, st₂, hrunP, hrg₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpresAll₂, hpresF₂,
              honce₂, hssf₂, hst₂, hsim₂, henvNRF₂, hv₂, hdisj₂, hnrf₂, hnv₂, _⟩
            · rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
            · rw [hrunP]
              refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
              cases hokEq
              have hpresEnv₂ : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap :=
                Sim_preserves_of_old hle₂ hpresAll₂ hsim₁
              have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₂ st.heap st₂.heap := by
                intro k bk abk hsc hbk habk hne ha₂
                have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
                have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
                  (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
                  (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
                have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
                exact hp1.trans ((hpresEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
              have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
              have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hv₂
              exact ⟨fun (_ : Nat) => False, by omega, hst₂,
                Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hrg₂.trans hr₁,
                Nat.le_trans hnr₁ (hnr₂ ▸ Nat.le_refl _),
                by rw [hstat₂]; exact hstat₁, by rw [hstr₂]; exact hstr₁,
                hpFrame₁.trans (hpresF₂.mono fun _ h => Or.inl h), hpresEnvAll,
                fun l o num ho hc => PreservesLocs_old_num hpresAll₂ l o num (hpNum₁ l o num ho hc) hc,
                honce₁.trans honce₂,
                StaticStrFresh.trans hsz₁ (hpresF₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
                hsimFinal, henvTaint₁.step hrg₂ (hnr₂ ▸ Nat.le_refl _),
                (fun k bk abk hsc hbk habk hne ha hregs hdeps => henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
                hvFinal, hdisj₂,
                (fun ha hregs hdeps => hnrf₂ ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
                hnv₂, taint_of_vsim_src_none rfl hvFinal,
                live_of_vsim_validDeps hvFinal (fun _ h => by cases h), SrcOk_none rfl⟩

theorem evalS_call_ifacePap_case {P : Prog} {ext : ExternOracle} {B : Nat}
    (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {r : Ref} {d : RunDef} {ifc : Iface} {args : List Term} {c : Cls}
    {σ σ₁ σ₂ : AState} {avs : List (Option AVal)} {res : AVal}
    (hfind : P.find? r = some d) (hifc : ifaceOf? d = some ifc)
    (hargsD : ACallArgs P (some d) aenv 0 args σ avs σ₁)
    (hargsIH : ACallArgsProp P ext B (some d) aenv 0 args σ avs σ₁)
    (hlt : avs.length < ifc.params.size)
    (hpap : Runs (papVal ifc avs.toArray "a partial application") σ₁ res σ₂) :
    ACallProp P ext B aenv r args c σ res σ₂ := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  have hok := hsim.2.1
  obtain ⟨hok₁, hle₁, _⟩ := ACallArgs_state_le hok hargsD
  obtain ⟨hok₂, hle₂, _, _, _, _, _, _, _, hresSrc, _⟩ := Runs_papVal hok₁ hpap
  have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnkEnd
  have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnspEnd
  let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
  have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
    BadDepLive_of_AStateLe hle₂ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
  have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
    let hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
    henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
      (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
  unfold TermPost; rw [hfind, MS_bind_run]
  obtain ⟨hnoVA, hokA⟩ := hargsIH hlc hcfd (B₀ := B₀) (fuel := fuel) (pref := []) hB₀ hfv hst hsim hstat hFlt
    hnk₁ hnsp₁ hIZero hHeadReg henvTaint henvNRF_bd₁ hForbidLt hBadDep₁
    ⟨(fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩
    (fun _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ _ h => by cases h)
  cases hevA : (evalCallArgsS P ext fuel env (some d) (args.zipIdx 0) []).run (st, B₀) with
  | error e =>
    refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
  | ok pa =>
    rcases pa with ⟨vs, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨cargs, hmatch, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
      hArgList₁, _, _⟩ := hokA vs st₁ B₁ hevA
    simp only [List.nil_append] at hArgList₁
    cases fuel with
    | zero =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, b1 + 1) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ n =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext (n + 1) r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        have hltV : vs.length < ifc.params.size := by have := hmatch.1; have := hmatch.2.1; omega
        have hcallEq : (callWithS P ext (n + 1) r vs c).run (st₁, b1 + 1) = (liftM stuckM).run (st₁, b1) ∨
            (callWithS P ext (n + 1) r vs c).run (st₁, b1 + 1) = (liftM (makePap P n r ifc.params vs)).run (st₁, b1) := by
          cases d with
          | body ps resM rc rs body =>
            simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
            right; unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [hfind]; simp [hltV]
          | extern ps resM rc rs =>
            simp only [ifaceOf?, Option.some.injEq] at hifc; subst hifc
            right; unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [hfind]; simp [hltV]
          | stuck ps resM rc rs =>
            left; unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [hfind]
          | ind _ | ctor _ _ _ _ | prim _ | caseDef _ => simp [ifaceOf?] at hifc
        rcases hcallEq with hSt | hPap
        · rw [hSt, MS_liftM_run]; unfold stuckM; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
        · rw [hPap, MS_liftM_run]
          let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
          have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
          have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
            h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
          have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
          have hsim₁b : Sim P ext b1 st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot :=
            Sim_step (by omega) (AStateLe.refl _) hok₁ hsim₁.2.2.1 (RegsFuture.refl _)
              (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
              (PreservesActiveEnv.refl _ _ _ _ _) (Sim_add_staticStr hsim₁)
          have hArgList₁b : ArgListOk P ext b1 st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
              Forbid BadReg BadDep₁ cargs := by
            have h1 := ArgListOk_add_staticStr hArgList₁
            refine ⟨fun k v av ft hg => ?_, h1.2⟩
            obtain ⟨hv, hd, hnrf, hnv⟩ := h1.1 k v av ft hg
            exact ⟨VSim_step (by omega) hok₁ (AStateLe.refl _) (RegsFuture.refl _) (PreservesOnceShell.refl _)
                (StaticStrFresh.refl _) (fun _ _ _ h => h) (fun _ => PreservesLocs.refl _ _) hv,
              hd, hnrf, hnv⟩
          obtain ⟨hnoVP, hokP⟩ := papVal_bridge (fuel := n) hext hih (by omega) hfind hifc hltV hmatch
            (fun idx hltI => by simpa using (ACallArgs_erased_iff hargsD).2 idx hltI) hpap
            hsim₁b (StOk_mono (by omega) hst₁) hstat₁F hFlt₁ hnkEnd hnspEnd hArgList₁b henvNRF₁ hForbLt₁
            (fun x hbd => hBadDepEnd x hbd.2)
          cases hrunP : (makePap P n r ifc.params vs).run st₁ with
          | error e =>
            refine ⟨fun k hk => by cases hk; exact hnoVP k hrunP, fun _ _ _ h => by cases h⟩
          | ok pp =>
            rcases pp with ⟨rv, st₂⟩; dsimp only
            obtain ⟨resFoot, hst₂, hsz₂, hcap₂, hrg₂, hnr₂, hstat₂, hstr₂, hpFrame₂, hpEnv₂, hpNum₂,
              honce₂, hssf₂, hsim₂, henvNRF₂, hv₂, hdisj₂, hnrf₂, hnv₂, hlive₂, _⟩ := hokP rv st₂ hrunP
            have hpresEnvAll : PreservesActiveEnv Scope env aenv σ₂ st.heap st₂.heap := by
              intro k bk abk hsc hbk habk hne ha₂
              have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
              have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
                (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
                (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
              have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
              exact hp1.trans ((hpEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
            have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
            have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hv₂
            refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
            cases hokEq
            exact ⟨resFoot, by omega, hst₂,
              Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂, hrg₂.trans hr₁, Nat.le_trans hnr₁ hnr₂,
              hstat₁.trans hstat₂, hstr₁.trans hstr₂,
              hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
              fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
              honce₁.trans honce₂,
              StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
              hsimFinal, henvTaint₁.step hrg₂ hnr₂,
              (fun k bk abk hsc hbk habk hne ha hregs hdeps => henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
              hvFinal, hdisj₂,
              (fun ha hregs hdeps => hnrf₂ ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
              hnv₂, taint_of_vsim_src_none hresSrc hvFinal, hlive₂, SrcOk_none hresSrc⟩

theorem evalS_natLit_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {k : Nat} {σ : AState} :
    ATermProp P ext B aenv (.natLit k) σ { cls := natClass } σ := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ _ hst hsim _ hFlt _ _ _ _ henvTaint henvNRF _ _
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hstep : (evalS P ext (n + 1) env (.natLit k)).run (st, b0 + 1) = (liftM (natValue k)).run (st, b0) := by
        conv => lhs; unfold evalS
        rw [MS_bind_run, MS_spend_succ]
      unfold TermPost; rw [hstep, MS_liftM_run]
      obtain ⟨rv, st', hrun, hrg, hnr, hstat', hstr', hsz, hcap, hpres, hcaps', hdl, _, hacyc, _, hnum⟩ :=
        mkNum_ok natClass k st hst.1
      obtain ⟨loc, cap, o, rfl, ho, hcell, hocap, _⟩ := hnum (by decide)
      rw [show (natValue k).run st = .ok (.ref loc cap [], st') from hrun]
      refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
      cases hokEq
      have hst' : StOk P ext b0 st' :=
        StOk_of_preserves_old (StOk_mono (by omega) hst) hcaps' hrg (hnr ▸ Nat.le_refl _) hstat' hstr' hpres
      have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hrg
      have hIok' : InterpOk σ st' I := ⟨fun rg hlt c hc => hnr ▸ hsim.2.2.1.1 rg hlt c hc,
        fun c hc => hsim.2.2.1.2 c (hrg ▸ hc)⟩
      have honce' : PreservesOnceShell st.heap st'.heap :=
        PreservesOnceShell.of_preservesLocs (hpres.mono fun _ ⟨_, _, _, ho', _⟩ => (Array.getElem?_eq_some_iff.mp ho').1)
      have hssf' : StaticStrFresh st st' :=
        StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat' hstr' (hpres.mono fun _ h => h.1) (fun _ _ h => h)
      have hpEnv : PreservesActiveEnv Scope env aenv σ st.heap st'.heap :=
        Sim_preserves_of_old (AStateLe.refl _) hpres hsim
      have hsim' : Sim P ext b0 st' Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (Nat.le_succ b0) (AStateLe.refl _) hsim.2.1 hIok' hrf honce' hssf' (fun _ _ _ h => h) hpEnv hsim
      have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl _) (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) (hstr' ▸ ArrayExtends.refl _)
        (hpres.mono fun _ hss => StOk_staticStrLoc_lt hst hss) hpEnv henvNRF
      have hbv : ValBaseOk st' (.ref loc cap []) := ValBaseOk_of_deepLive hdl hacyc (DeepTaintsBounded_num ho hcell)
      have hnv : NonValSafe st'.heap (.ref loc cap []) := Or.inr ⟨loc, cap, o, k, rfl, ho, hocap, hcell⟩
      exact ⟨fun (_ : Nat) => False, by omega, hst', hsz, hcap, hrg, hnr ▸ Nat.le_refl _,
        hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
        hpres.mono fun l hF => hFlt l hF, hpEnv, PreservesLocs_old_num hpres, honce', hssf',
        hsim', henvTaint.step hrg (hnr ▸ Nat.le_refl _), henvNRF',
        VSim_nonValSafe (fun _ h => by cases h) (fun _ h => by cases h) rfl hbv hnv,
        ValEnvDisj_nonValSafe rfl hnv hsim',
        fun _ => NoReachForbid_nonValSafe hnv,
        fun _ _ => ⟨hbv, hnv⟩,
        fun _ => ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩,
        Or.inl ⟨hbv, hnv.ctorFieldsOk P ext b0 st'⟩, SrcOk_none rfl⟩

theorem evalS_strLit_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {s : String} {σ : AState} :
    ATermProp P ext B aenv (.strLit s) σ { cls := .val, skel := .data } σ := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ _ hst hsim _ hFlt _ _ _ _ henvTaint henvNRF hForbidLt _
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hstep : (evalS P ext (n + 1) env (.strLit s)).run (st, b0 + 1) = (liftM (strValue s)).run (st, b0) := by
        conv => lhs; unfold evalS
        rw [MS_bind_run, MS_spend_succ]
      unfold TermPost; rw [hstep, MS_liftM_run]
      obtain ⟨rv, st', hrun, hrg, hnr, hstat', hstrExt, hsz, hcap, hpres, honce', hssf', hst',
        hbv, hdou, hcf, hno, hfun, hreach⟩ := strValue_sound s (StOk_mono (Nat.le_succ b0) hst)
      rw [hrun]
      refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
      cases hokEq
      have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hrg
      have hIok' : InterpOk σ st' I := ⟨fun rg hlt c hc => hnr ▸ hsim.2.2.1.1 rg hlt c hc,
        fun c hc => hsim.2.2.1.2 c (hrg ▸ hc)⟩
      have hpEnv : PreservesActiveEnv Scope env aenv σ st.heap st'.heap :=
        Sim_preserves_of_old (AStateLe.refl _) hpres hsim
      have hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap := hpres.mono fun _ hss => StOk_staticStrLoc_lt hst hss
      have hsim' : Sim P ext b0 st' Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (Nat.le_succ b0) (AStateLe.refl _) hsim.2.1 hIok' hrf honce' hssf' (fun _ _ _ h => h) hpEnv hsim
      have henvNRF' := EnvNoReachForbid_step hsim.2.1 (AStateLe.refl _) (Sim_deps_lt hsim) hsim.2.2.2.1
        (hstat' ▸ ArrayExtends.refl _) hstrExt hpSS hpEnv henvNRF
      have hvStr : VSim P ext b0 st' Frame NoKill NoSpend σ I (fun (_ : Nat) => False) { cls := .val, skel := .data } rv :=
        ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ ⟨_, hs, _⟩ => by cases hs),
         fun _ => ⟨hbv, hdou, hcf, (fun _ hne => absurd rfl hne), (fun _ => ⟨hno, fun _ h => h, hfun⟩),
           (fun h => by cases h), (fun ⟨_, hs, _⟩ => by cases hs), (fun htr => by cases htr.2.1)⟩⟩
      have hdisjStr : ValEnvDisj P st' NoKill Scope env aenv σ envFoot (fun (_ : Nat) => False) { cls := .val, skel := .data } rv := by
        intro k bk abk hsc hbk habk hne
        have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
        refine ⟨(fun _ htr => by cases htr.2.1), fun haB htrB _ _ l hor hr => ?_,
          (fun _ _ _ _ _ h => False.elim h), fun haB hfB _ _ l hft hr => ?_,
          (fun _ _ hs => by cases hs), (fun hs => by cases hs), (fun _ hs => by cases hs)⟩
        · have hvKB := hvK.2.2.2.2 haB
          have hpK := hpEnv k bk abk hsc hbk habk hne haB
          have hor0 := (OwnReach_congr hpK l).mp hor
          rcases hreach l hr with hge | hss
          · exact Nat.not_lt_of_ge hge (hvKB.1.1.reach_lt_size (OwnReach_toReach hor0))
          · exact (hvKB.2.2.2.2.2.2.2 htrB).2 l hor0 |>.2 hss
        · have hvKB := hvK.2.2.2.2 haB
          have hftInfo : Reach st.heap bk.val l ∧ ¬ StaticStrLoc st l := by
            rcases hfB with hoo | ⟨his, _⟩
            · exact ⟨(hvKB.2.2.2.2.2.1 hoo).1 l hft |>.1, (hvKB.2.2.2.2.2.1 hoo).1 l hft |>.2.1⟩
            · exact ⟨(hvKB.2.2.2.2.2.2.1 his).1 l hft |>.1, (hvKB.2.2.2.2.2.2.1 his).1 l hft |>.2.1⟩
          rcases hreach l hr with hge | hss
          · exact Nat.not_lt_of_ge hge (hvKB.1.1.reach_lt_size hftInfo.1)
          · exact hftInfo.2 hss
      have hnrfStr : ActiveVal σ { cls := .val, skel := .data } → NoReachForbid st' Forbid BadReg BadDep { cls := .val, skel := .data } rv :=
        fun _ _ _ l hr hnotSS _ hF => by
          rcases hreach l hr with hge | hss
          · exact Nat.not_lt_of_ge hge (hForbidLt l hF)
          · exact hnotSS (StaticStrLoc_mono (hstat' ▸ ArrayExtends.refl _) hstrExt hpSS hss)
      exact ⟨fun (_ : Nat) => False, by omega, hst', hsz, hcap, hrg, hnr ▸ Nat.le_refl _,
        hstat' ▸ ArrayExtends.refl _, hstrExt,
        hpres.mono fun l hF => hFlt l hF, hpEnv, PreservesLocs_old_num hpres, honce', hssf',
        hsim', henvTaint.step hrg (hnr ▸ Nat.le_refl _), henvNRF', hvStr, hdisjStr, hnrfStr,
        (fun _ hne => absurd rfl hne),
        taint_of_vsim_src_none rfl hvStr, Or.inl ⟨hbv, hcf⟩, SrcOk_none rfl⟩

theorem evalS_letErased_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {d : Cls} {v b : Term} {σ σ' : AState} {r : AVal}
    (hbIH : ATermProp P ext B ({ id := σ.st.size, mode := .erased, val := { cls := .irr } } :: aenv)
      b (σ.pushBnd { cls := .irr } false).2 r σ') :
    ATermProp P ext B aenv (.letE (.value .erased) d v b) σ r σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  cases hlc with | letE _ hlcB =>
  cases hcfd with | letE _ hcfdB =>
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hstep : (evalS P ext (n + 1) env (.letE (.value .erased) d v b)).run (st, b0 + 1) =
          (evalS P ext n (⟨.imm .irr, .erased⟩ :: env) b).run (st, b0) := by
        conv => lhs; unfold evalS
        rw [MS_bind_run, MS_spend_succ]
      unfold TermPost; rw [hstep]
      have hok := hsim.2.1
      have hleP : AStateLe σ (σ.pushBnd { cls := .irr } false).2 := (hok.pushBnd _ _).2
      have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (Nat.le_succ b0) (AStateLe.refl _) hok hsim.2.2.1 (RegsFuture.refl _)
          (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
          (PreservesActiveEnv.refl _ _ _ _ _) hsim
      have hsimPush := Sim_congr_scope_foot (Scope₂ := shiftScope Scope)
        (envFoot₂ := fun i => match i with | 0 => fun _ => False | k + 1 => envFoot k)
        (fun i => by cases i <;> exact Iff.rfl) (fun i _ => by cases i <;> exact Iff.rfl)
        (Sim_push_erased hsimB)
      have henvNRFP : EnvNoReachForbid st (shiftScope Scope) (⟨.imm .irr, .erased⟩ :: env)
          ({ id := σ.st.size, mode := .erased, val := { cls := .irr } } :: aenv)
          (σ.pushBnd { cls := .irr } false).2 Forbid BadReg BadDep := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps => by
        cases i with
        | zero => simp at habi'; subst habi'; exact absurd rfl hne'
        | succ k =>
          have hvK := ((hsimB.2.2.2.2.2.1 k b' ab' hsc' hbi' habi').2 hne').2
          exact henvNRF k b' ab' hsc' hbi' habi' hne' (ActiveVal.of_AStateLe hok hleP hvK.2.1 (fun z hz => (hvK.2.2.1 z hz).1) ha') hregs hdeps
      obtain ⟨hnoVB, hokB⟩ := hbIH hlcB hcfdB (B₀ := b0) (fuel := n) (by omega)
        (shiftScope_of_freeVarIn fun z hz => hfv z (.letB hz))
        (StOk_mono (by omega) hst) hsimPush hstat hFlt hnkEnd hnspEnd hIZero hHeadReg
        (henvTaint.cons_erased rfl) henvNRFP hForbidLt hBadDepEnd
      refine ⟨hnoVB, fun rv st' B' hevB => ?_⟩
      obtain ⟨rFoot, hB', hst', hsz', hcap', hr', hnr', hstat', hstr', hpFrame', hpEnv', hpNum',
        honce', hssf', hsim', henvTaint', henvNRF', hv', hdisj', hnrf', hnv', htaint', hlive', hsrc'⟩ :=
        hokB rv st' B' hevB
      have hsimPop : Sim P ext B' st' Frame NoKill NoSpend Scope env aenv σ' I envFoot := by
        obtain ⟨hlenC, hokC, hIokC, hidsC, huniqC, hbndsC, hdisjC⟩ := hsim'
        exact ⟨by simpa using hlenC, hokC, hIokC, fun i ab' hab' => hidsC (i + 1) ab' hab',
          fun i j ab₁ ab₂ h1 h2 hid => Nat.succ.inj (huniqC (i + 1) (j + 1) ab₁ ab₂ h1 h2 hid),
          fun i b' ab' hsc' hbi' habi' => hbndsC (i + 1) b' ab' hsc' hbi' habi',
          fun i j b₁ b₂ ab₁ ab₂ hij hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂ =>
            hdisjC (i + 1) (j + 1) b₁ b₂ ab₁ ab₂ (by omega) hsc₁ hsc₂ hb₁ hb₂ hab₁ hab₂ hne₁ hne₂⟩
      have hsrcPop : SrcOk Scope aenv σ σ' r := fun id hs => by
        rcases hsrc' id hs with ⟨i, ab', hsc', hab', hne', hid', hoo', hdeps'⟩ | ⟨hge, hsp⟩
        · cases i with
          | zero => simp at hab'; subst hab'; exact absurd rfl hne'
          | succ k => exact Or.inl ⟨k, ab', hsc', hab', hne', hid', hoo', hdeps'⟩
        · exact Or.inr ⟨Nat.le_trans hleP.1 hge, fun hoId dep hdep hlt0 hoDep => hsp hoId dep hdep (Nat.lt_of_lt_of_le hlt0 hleP.1) hoDep⟩
      exact ⟨rFoot, by omega, hst', hsz', hcap', hr', hnr', hstat', hstr', hpFrame',
        (fun k bk abk hsc hbk habk hne ha => hpEnv' (k + 1) bk abk hsc hbk habk hne ha),
        hpNum', honce', hssf', hsimPop, henvTaint.step hr' hnr',
        (fun k bk abk hsc hbk habk hne ha => henvNRF' (k + 1) bk abk hsc hbk habk hne ha),
        hv', (fun k bk abk hsc hbk habk hne => hdisj' (k + 1) bk abk hsc hbk habk hne),
        hnrf', hnv', htaint', hlive', hsrcPop⟩

theorem evalS_evals_cons_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {t : Term} {rest : List Term} {σ σ₁ σ' : AState} {v : AVal} {vs_a : List AVal}
    (ht : ATerm P aenv t σ v σ₁) (htIH : ATermProp P ext B aenv t σ v σ₁)
    (hrest : AEvals P aenv rest σ₁ vs_a σ') (hrestIH : AEvalsProp P ext B aenv rest σ₁ vs_a σ') :
    AEvalsProp P ext B aenv (t :: rest) σ (v :: vs_a) σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep pref
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    hargP hpreSrc hargsSrc
  have hok := hsim.2.1
  obtain ⟨hok₁, hle₁, hreg₁⟩ := ATerm_state_le hok ht
  obtain ⟨hok₂, hle₂, _⟩ := AEvals_state_le hok₁ hrest
  have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnkEnd
  have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnspEnd
  let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
  have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
    BadDepLive_of_AStateLe hle₂ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
  have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
    let hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
    henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
      (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
  have hargP₁ : ArgListOk P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep₁ pref :=
    ⟨fun k w av ft hg => let ⟨hv, hd, hnrf, hnv⟩ := hargP.1 k w av ft hg
      ⟨hv, hd, fun ha hregs hdeps => hnrf ha hregs (fun d hd hbd => hdeps d hd ⟨Nat.lt_of_lt_of_le (hv.2.1 d hd) hle₁.1, hbd⟩), hnv⟩,
     hargP.2⟩
  obtain ⟨hnoVT, hokT⟩ := ArgListOk_push (m := evalS P ext fuel env t) (av₂ := v)
    hle₁ hsim hst hFlt hnk₁ hnsp₁ henvNRF_bd₁ hForbidLt hBadDep₁ hargP₁ hpreSrc hargsSrc
    (fun Frame' NoKill' NoSpend' Forbid' BadReg' BadDep' hsim' hstat' hFlt' hnk' hnsp' henvNRF' hForbLt' hBadDep' => by
      obtain ⟨hno, hok'⟩ := htIH (hlc t List.mem_cons_self) (hcfd t List.mem_cons_self)
        (B₀ := B₀) (fuel := fuel) hB₀ (hfv t List.mem_cons_self) hst hsim' hstat' hFlt'
        hnk' hnsp' hIZero hHeadReg henvTaint henvNRF' hForbLt' hBadDep'
      refine ⟨hno, fun v₂ st₁ B₁ hev => ?_⟩
      obtain ⟨ft₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, _, h16, h17, h18, h19, h20, _, _, h23⟩ :=
        hok' v₂ st₁ B₁ hev
      exact ⟨ft₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h16, h17, h18, h19, h20, h23⟩)
  have hstep : (evalListS P ext fuel env (t :: rest) []).run (st, B₀) =
      (do let vc ← evalS P ext fuel env t; let restVs ← evalListS P ext fuel env rest []; pure (vc :: restVs)).run (st, B₀) := by
    conv => lhs; unfold evalListS
    rw [MS_bind_run, MS_bind_run]
    cases (evalS P ext fuel env t).run (st, B₀) with
    | error _ => rfl
    | ok p =>
      dsimp only
      have hacc := evalListS_acc (P := P) (ext := ext) (n := fuel) (env := env) rest [p.1] [] p.2
      simp only [List.append_nil, List.nil_append] at hacc ⊢
      rw [hacc, MS_bind_run]
      cases (evalListS P ext fuel env rest []).run p.2 <;> rfl
  rw [hstep, MS_bind_run]
  cases hevT : (evalS P ext fuel env t).run (st, B₀) with
  | error e => refine ⟨fun k hk => by cases hk; exact hnoVT k hevT, fun _ _ _ h => by cases h⟩
  | ok pt =>
    rcases pt with ⟨vc, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨vFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvNRF₁,
      hArgList₁, hPrefSrc₁, hArgsSrc₁⟩ := hokT vc st₁ B₁ hevT
    let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
    have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
    have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
      h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
    have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
    have hIZero₁ : ∀ rg, σ₁.nextRegion ≤ rg → I.reg rg = [] := fun rg hge => hIZero rg (Nat.le_trans hle₁.2.1 hge)
    have hHeadReg₁ : st₁.regions.headD 0 = 0 ∨ st₁.regions.headD 0 ∈ I.reg (σ₁.regions.headD 1) := by
      rw [hr₁, hreg₁]; exact hHeadReg
    have henvNRF₁' : EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep :=
      fun k bk abk hsc hbk habk hne ha hregs hdeps =>
        henvNRF₁ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)
    have hArgList₁' : ArgListOk P ext B₁ st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
        Forbid BadReg BadDep (pref ++ [some (vc, v, vFoot)]) :=
      ArgListOk_add_staticStr ⟨fun k w av ft hg => let ⟨hv, hd, hnrf, hnv⟩ := hArgList₁.1 k w av ft hg
        ⟨hv, hd, fun ha hregs hdeps => hnrf ha hregs (fun d hd hbd => hdeps d hd hbd.2), hnv⟩, hArgList₁.2⟩
    obtain ⟨hnoVR, hokR⟩ := hrestIH (fun x hx => hlc x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcfd x (List.mem_cons_of_mem _ hx)) (B₀ := B₁) (fuel := fuel) (by omega)
      (fun x hx => hfv x (List.mem_cons_of_mem _ hx)) hst₁ (Sim_add_staticStr hsim₁) hstat₁F hFlt₁
      hnkEnd hnspEnd hIZero₁ hHeadReg₁ (henvTaint.step hr₁ hnr₁) henvNRF₁' hForbLt₁ hBadDepEnd
      hArgList₁' hPrefSrc₁ hArgsSrc₁
    rw [MS_bind_run]
    cases hevR : (evalListS P ext fuel env rest []).run (st₁, B₁) with
    | error e => refine ⟨fun k hk => by cases hk; exact hnoVR k hevR, fun _ _ _ h => by cases h⟩
    | ok pr =>
      rcases pr with ⟨restVs, ⟨st₂, B₂⟩⟩; dsimp only
      rw [MS_pure_run]
      refine ⟨(fun _ h => by cases h), fun vs0 st0 B0 hokEq => ?_⟩
      cases hokEq
      obtain ⟨rArgs, hvsEq, havsEq, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
        hpFrame₂, hpEnv₂, hpNum₂, honce₂, hssf₂, hsim₂, henvTaint₂, henvNRF₂,
        hArgList₂, hPrefSrc₂, hArgsSrc₂⟩ := hokR restVs st₂ B₂ hevR
      have hpresEnvAll : PreservesActiveEnv Scope env aenv σ' st.heap st₂.heap := by
        intro k bk abk hsc hbk habk hne ha₂
        have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
        have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
          (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
          (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
        have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
        exact hp1.trans ((hpEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
      have hAssoc : (pref ++ [some (vc, v, vFoot)]) ++ rArgs.map some = pref ++ ((vc, v, vFoot) :: rArgs).map some := by
        simp [List.append_assoc]
      have hArgFinal : ArgListOk P ext B₂ st₂ Frame NoKill NoSpend Scope env aenv σ' I envFoot
          Forbid BadReg BadDep (pref ++ ((vc, v, vFoot) :: rArgs).map some) := by
        rw [← hAssoc]
        exact ⟨fun k w av ft hg => let ⟨hv, hd, hnrf, hnv⟩ := hArgList₂.1 k w av ft hg
          ⟨VSim_shrink_frame (fun _ hF => Or.inl hF) hv, hd, hnrf, hnv⟩, hArgList₂.2⟩
      exact ⟨(vc, v, vFoot) :: rArgs, by simp [hvsEq], by simp [havsEq],
        by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
        hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂, hstat₁.trans hstat₂, hstr₁.trans hstr₂,
        hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
        fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
        honce₁.trans honce₂, StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
        Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂, henvTaint₂, henvNRF₂,
        hArgFinal, hAssoc ▸ hPrefSrc₂, hAssoc ▸ hArgsSrc₂⟩

theorem evalS_callArgs_consSkip_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {d? : Option RunDef} {aenv : List ABnd} {idx : Nat} {t : Term} {rest : List Term}
    {σ σ' : AState} {avs_r : List (Option AVal)}
    (hskip : (match d? with | some d => erasedAt d idx | none => false) = true)
    (hrestIH : ACallArgsProp P ext B d? aenv (idx + 1) rest σ avs_r σ') :
    ACallArgsProp P ext B d? aenv idx (t :: rest) σ (none :: avs_r) σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep pref
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    hargP hpreSrc hargsSrc
  have hstep : (evalCallArgsS P ext fuel env d? ((t :: rest).zipIdx idx) []).run (st, B₀) =
      (do let restVs ← evalCallArgsS P ext fuel env d? (rest.zipIdx (idx + 1)) []; pure (Val.imm .irr :: restVs)).run (st, B₀) := by
    rw [List.zipIdx_cons]
    conv => lhs; unfold evalCallArgsS
    cases d? with
    | none => cases hskip
    | some d =>
      dsimp only at hskip ⊢
      rw [hskip]; simp only [↓reduceIte, MS_bind_run, MS_pure_run]
      have hacc := evalCallArgsS_acc (P := P) (ext := ext) (n := fuel) (env := env) (d := some d) (rest.zipIdx (idx + 1)) [.imm .irr] [] (st, B₀)
      simp only [List.append_nil, List.nil_append] at hacc ⊢
      rw [hacc]
      cases (evalCallArgsS P ext fuel env (some d) (rest.zipIdx (idx + 1)) []).run (st, B₀) <;> rfl
  obtain ⟨hargP', hpreSrc', hargsSrc'⟩ := ArgListOk_push_none hargP hpreSrc hargsSrc
  obtain ⟨hnoVR, hokR⟩ := hrestIH (fun x hx => hlc x (List.mem_cons_of_mem _ hx))
    (fun x hx => hcfd x (List.mem_cons_of_mem _ hx)) (B₀ := B₀) (fuel := fuel) hB₀
    (fun x hx => hfv x (List.mem_cons_of_mem _ hx)) hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg
    henvTaint henvNRF hForbidLt hBadDepEnd hargP' hpreSrc' hargsSrc'
  rw [hstep, MS_bind_run]
  cases hevR : (evalCallArgsS P ext fuel env d? (rest.zipIdx (idx + 1)) []).run (st, B₀) with
  | error e => refine ⟨fun k hk => by cases hk; exact hnoVR k hevR, fun _ _ _ h => by cases h⟩
  | ok pr =>
    rcases pr with ⟨restVs, ⟨st', B'⟩⟩; dsimp only
    rw [MS_pure_run]
    refine ⟨(fun _ h => by cases h), fun vs0 st0 B0 hokEq => ?_⟩
    cases hokEq
    obtain ⟨rArgs, hmatch, hB', hst', hsz', hcap', hr', hnr', hstat', hstr',
      hpFrame', hpEnv', hpNum', honce', hssf', hsim', henvTaint', henvNRF',
      hArgList', hPrefSrc', hArgsSrc'⟩ := hokR restVs st' B' hevR
    have hAssoc : (pref ++ [none]) ++ rArgs = pref ++ (none :: rArgs) := by simp [List.append_assoc]
    exact ⟨none :: rArgs, ArgsMatch_cons_none hmatch, hB', hst', hsz', hcap', hr', hnr', hstat', hstr',
      hpFrame', hpEnv', hpNum', honce', hssf', hsim', henvTaint', henvNRF',
      hAssoc ▸ hArgList', hAssoc ▸ hPrefSrc', hAssoc ▸ hArgsSrc'⟩

theorem evalS_callArgs_consEval_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {d? : Option RunDef} {aenv : List ABnd} {idx : Nat} {t : Term} {rest : List Term}
    {σ σ₁ σ' : AState} {v : AVal} {avs_r : List (Option AVal)}
    (hkeep : (match d? with | some d => erasedAt d idx | none => false) = false)
    (ht : ATerm P aenv t σ v σ₁) (htIH : ATermProp P ext B aenv t σ v σ₁)
    (hrest : ACallArgs P d? aenv (idx + 1) rest σ₁ avs_r σ')
    (hrestIH : ACallArgsProp P ext B d? aenv (idx + 1) rest σ₁ avs_r σ') :
    ACallArgsProp P ext B d? aenv idx (t :: rest) σ (some v :: avs_r) σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep pref
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    hargP hpreSrc hargsSrc
  have hok := hsim.2.1
  obtain ⟨hok₁, hle₁, hreg₁⟩ := ATerm_state_le hok ht
  obtain ⟨hok₂, hle₂, _⟩ := ACallArgs_state_le hok₁ hrest
  have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnkEnd
  have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnspEnd
  let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
  have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
    BadDepLive_of_AStateLe hle₂ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
  have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
    let hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
    henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
      (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
  have hargP₁ : ArgListOk P ext B₀ st Frame NoKill NoSpend Scope env aenv σ I envFoot Forbid BadReg BadDep₁ pref :=
    ⟨fun k w av ft hg => let ⟨hv, hd, hnrf, hnv⟩ := hargP.1 k w av ft hg
      ⟨hv, hd, fun ha hregs hdeps => hnrf ha hregs (fun d hd hbd => hdeps d hd ⟨Nat.lt_of_lt_of_le (hv.2.1 d hd) hle₁.1, hbd⟩), hnv⟩,
     hargP.2⟩
  obtain ⟨hnoVT, hokT⟩ := ArgListOk_push (m := evalS P ext fuel env t) (av₂ := v)
    hle₁ hsim hst hFlt hnk₁ hnsp₁ henvNRF_bd₁ hForbidLt hBadDep₁ hargP₁ hpreSrc hargsSrc
    (fun Frame' NoKill' NoSpend' Forbid' BadReg' BadDep' hsim' hstat' hFlt' hnk' hnsp' henvNRF' hForbLt' hBadDep' => by
      obtain ⟨hno, hok'⟩ := htIH (hlc t List.mem_cons_self) (hcfd t List.mem_cons_self)
        (B₀ := B₀) (fuel := fuel) hB₀ (hfv t List.mem_cons_self) hst hsim' hstat' hFlt'
        hnk' hnsp' hIZero hHeadReg henvTaint henvNRF' hForbLt' hBadDep'
      refine ⟨hno, fun v₂ st₁ B₁ hev => ?_⟩
      obtain ⟨ft₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, _, h16, h17, h18, h19, h20, _, _, h23⟩ :=
        hok' v₂ st₁ B₁ hev
      exact ⟨ft₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h16, h17, h18, h19, h20, h23⟩)
  have hstep : (evalCallArgsS P ext fuel env d? ((t :: rest).zipIdx idx) []).run (st, B₀) =
      (do let vc ← evalS P ext fuel env t; let restVs ← evalCallArgsS P ext fuel env d? (rest.zipIdx (idx + 1)) []; pure (vc :: restVs)).run (st, B₀) := by
    rw [List.zipIdx_cons]
    have hrunBranch : (evalCallArgsS P ext fuel env d? ((t, idx) :: rest.zipIdx (idx + 1)) []).run (st, B₀) =
        (do let v ← evalS P ext fuel env t; evalCallArgsS P ext fuel env d? (rest.zipIdx (idx + 1)) ([] ++ [v])).run (st, B₀) := by
      conv => lhs; unfold evalCallArgsS
      cases d? with
      | none => simp only [Bool.false_eq_true, ↓reduceIte]
      | some d => dsimp only at hkeep ⊢; rw [hkeep]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hrunBranch, MS_bind_run, MS_bind_run]
    cases (evalS P ext fuel env t).run (st, B₀) with
    | error _ => rfl
    | ok p =>
      dsimp only
      have hacc := evalCallArgsS_acc (P := P) (ext := ext) (n := fuel) (env := env) (d := d?) (rest.zipIdx (idx + 1)) [p.1] [] p.2
      simp only [List.append_nil, List.nil_append] at hacc ⊢
      rw [hacc, MS_bind_run]
      cases (evalCallArgsS P ext fuel env d? (rest.zipIdx (idx + 1)) []).run p.2 <;> rfl
  rw [hstep, MS_bind_run]
  cases hevT : (evalS P ext fuel env t).run (st, B₀) with
  | error e => refine ⟨fun k hk => by cases hk; exact hnoVT k hevT, fun _ _ _ h => by cases h⟩
  | ok pt =>
    rcases pt with ⟨vc, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨vFoot, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvNRF₁,
      hArgList₁, hPrefSrc₁, hArgsSrc₁⟩ := hokT vc st₁ B₁ hevT
    let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
    have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
    have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
      h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
    have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
    have hIZero₁ : ∀ rg, σ₁.nextRegion ≤ rg → I.reg rg = [] := fun rg hge => hIZero rg (Nat.le_trans hle₁.2.1 hge)
    have hHeadReg₁ : st₁.regions.headD 0 = 0 ∨ st₁.regions.headD 0 ∈ I.reg (σ₁.regions.headD 1) := by
      rw [hr₁, hreg₁]; exact hHeadReg
    have henvNRF₁' : EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep :=
      fun k bk abk hsc hbk habk hne ha hregs hdeps =>
        henvNRF₁ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)
    have hArgList₁' : ArgListOk P ext B₁ st₁ Frame₁ NoKill NoSpend Scope env aenv σ₁ I envFoot
        Forbid BadReg BadDep (pref ++ [some (vc, v, vFoot)]) :=
      ArgListOk_add_staticStr ⟨fun k w av ft hg => let ⟨hv, hd, hnrf, hnv⟩ := hArgList₁.1 k w av ft hg
        ⟨hv, hd, fun ha hregs hdeps => hnrf ha hregs (fun d hd hbd => hdeps d hd hbd.2), hnv⟩, hArgList₁.2⟩
    obtain ⟨hnoVR, hokR⟩ := hrestIH (fun x hx => hlc x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcfd x (List.mem_cons_of_mem _ hx)) (B₀ := B₁) (fuel := fuel) (by omega)
      (fun x hx => hfv x (List.mem_cons_of_mem _ hx)) hst₁ (Sim_add_staticStr hsim₁) hstat₁F hFlt₁
      hnkEnd hnspEnd hIZero₁ hHeadReg₁ (henvTaint.step hr₁ hnr₁) henvNRF₁' hForbLt₁ hBadDepEnd
      hArgList₁' hPrefSrc₁ hArgsSrc₁
    rw [MS_bind_run]
    cases hevR : (evalCallArgsS P ext fuel env d? (rest.zipIdx (idx + 1)) []).run (st₁, B₁) with
    | error e => refine ⟨fun k hk => by cases hk; exact hnoVR k hevR, fun _ _ _ h => by cases h⟩
    | ok pr =>
      rcases pr with ⟨restVs, ⟨st₂, B₂⟩⟩; dsimp only
      rw [MS_pure_run]
      refine ⟨(fun _ h => by cases h), fun vs0 st0 B0 hokEq => ?_⟩
      cases hokEq
      obtain ⟨rArgs, hmatch, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
        hpFrame₂, hpEnv₂, hpNum₂, honce₂, hssf₂, hsim₂, henvTaint₂, henvNRF₂,
        hArgList₂, hPrefSrc₂, hArgsSrc₂⟩ := hokR restVs st₂ B₂ hevR
      have hpresEnvAll : PreservesActiveEnv Scope env aenv σ' st.heap st₂.heap := by
        intro k bk abk hsc hbk habk hne ha₂
        have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
        have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
          (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
          (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
        have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
        exact hp1.trans ((hpEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
      have hAssoc : (pref ++ [some (vc, v, vFoot)]) ++ rArgs = pref ++ (some (vc, v, vFoot) :: rArgs) := by
        simp [List.append_assoc]
      have hArgFinal : ArgListOk P ext B₂ st₂ Frame NoKill NoSpend Scope env aenv σ' I envFoot
          Forbid BadReg BadDep (pref ++ (some (vc, v, vFoot) :: rArgs)) := by
        rw [← hAssoc]
        exact ⟨fun k w av ft hg => let ⟨hv, hd, hnrf, hnv⟩ := hArgList₂.1 k w av ft hg
          ⟨VSim_shrink_frame (fun _ hF => Or.inl hF) hv, hd, hnrf, hnv⟩, hArgList₂.2⟩
      exact ⟨some (vc, v, vFoot) :: rArgs, ArgsMatch_cons_some hmatch,
        by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
        hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂, hstat₁.trans hstat₂, hstr₁.trans hstr₂,
        hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
        fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
        honce₁.trans honce₂, StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
        Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂, henvTaint₂, henvNRF₂,
        hArgFinal, hAssoc ▸ hPrefSrc₂, hAssoc ▸ hArgsSrc₂⟩

theorem evalS_call_ind_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {r : Ref} {ctors : Array Ref} {args : List Term} {c : Cls}
    {σ σ' : AState} {avs : List (Option AVal)}
    (hfind : P.find? r = some (.ind ctors))
    (hargsIH : ACallArgsProp P ext B (some (.ind ctors)) aenv 0 args σ avs σ') :
    ACallProp P ext B aenv r args c σ { cls := .irr } σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  unfold TermPost; rw [hfind, MS_bind_run]
  obtain ⟨hnoVA, hokA⟩ := hargsIH hlc hcfd (B₀ := B₀) (fuel := fuel) (pref := []) hB₀ hfv hst hsim hstat hFlt
    hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    ⟨(fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩
    (fun _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ _ h => by cases h)
  cases hevA : (evalCallArgsS P ext fuel env (some (.ind ctors)) (args.zipIdx 0) []).run (st, B₀) with
  | error e => refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
  | ok pa =>
    rcases pa with ⟨vs, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨_, _, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁, _, _, _⟩ := hokA vs st₁ B₁ hevA
    cases fuel with
    | zero =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        rw [show (callWithS P ext 0 r vs c).run (st₁, b1 + 1) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_succ]; rfl]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | succ n =>
      cases B₁ with
      | zero =>
        rw [show (callWithS P ext (n + 1) r vs c).run (st₁, 0) = .error .outOfFuel by unfold callWithS; rw [MS_bind_run, MS_spend_zero]]
        exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      | succ b1 =>
        have hstep : (callWithS P ext (n + 1) r vs c).run (st₁, b1 + 1) = .ok (.imm .irr, (st₁, b1)) := by
          unfold callWithS; rw [MS_bind_run, MS_spend_succ]; dsimp only; rw [hfind]; rfl
        rw [hstep]
        refine ⟨(fun _ h => by cases h), fun rv st0 B0 hokEq => ?_⟩
        cases hokEq
        have hsim₁b : Sim P ext b1 st₁ Frame NoKill NoSpend Scope env aenv σ' I envFoot :=
          Sim_step (Nat.le_succ b1) (AStateLe.refl _) hsim₁.2.1 hsim₁.2.2.1 (RegsFuture.refl _)
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _) hsim₁
        exact ⟨fun (_ : Nat) => False, by omega, StOk_mono (by omega) hst₁, hsz₁, hcap₁, hr₁, hnr₁,
          hstat₁, hstr₁, hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁b, henvTaint₁, henvNRF₁,
          VSim_imm_irr (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h),
          ValEnvDisj_imm_irr rfl, fun _ => NoReachForbid_imm_irr st₁ Forbid BadReg BadDep _,
          fun _ _ => ⟨ValBaseOk_imm st₁ .irr, Or.inl ⟨.irr, rfl⟩⟩,
          fun _ => ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩,
          Or.inl ⟨ValBaseOk_imm st₁ .irr, CtorFieldsOk_imm P ext b1 st₁ .irr⟩, SrcOk_none rfl⟩

theorem evalS_call_ifaceFullZero_case {P : Prog} {ext : ExternOracle} {B : Nat}
    (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {r : Ref} {d : RunDef} {ifc : Iface} {args : List Term} {c : Cls}
    {σ σ₁ σ' : AState} {avs : List (Option AVal)} {res : AVal}
    (hfind : P.find? r = some d) (hifc : ifaceOf? d = some ifc)
    (hargs : ACallArgs P (some d) aenv 0 args σ avs σ₁)
    (hargsIH : ACallArgsProp P ext B (some d) aenv 0 args σ avs σ₁)
    (hzero : ifc.params.size = 0)
    (happs : AApps { cls := ifc.resCls, skel := ifc.resSkel } (avs.filterMap id) c σ₁ res σ') :
    ACallProp P ext B aenv r args c σ res σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  have hok := hsim.2.1
  obtain ⟨hok₁, hle₁, _⟩ := ACallArgs_state_le hok hargs
  obtain ⟨hok₂, hle₂, _, _⟩ := AApps_state_le hok₁ happs
  have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₂ hnkEnd
  have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₂ hnspEnd
  let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
  have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
    BadDepLive_of_AStateLe hle₂ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
  have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
    let hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
    henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
      (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
  unfold TermPost; rw [hfind, MS_bind_run]
  obtain ⟨hnoVA, hokA⟩ := hargsIH hlc hcfd (B₀ := B₀) (fuel := fuel) (pref := []) hB₀ hfv hst hsim hstat hFlt
    hnk₁ hnsp₁ hIZero hHeadReg henvTaint henvNRF_bd₁ hForbidLt hBadDep₁
    ⟨(fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩
    (fun _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ _ h => by cases h)
  cases hevA : (evalCallArgsS P ext fuel env (some d) (args.zipIdx 0) []).run (st, B₀) with
  | error e => refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
  | ok pa =>
    rcases pa with ⟨vs, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨cargs, hmatch, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
      hArgList₁, _, hArgsSrc₁⟩ := hokA vs st₁ B₁ hevA
    simp only [List.nil_append] at hArgList₁ hArgsSrc₁
    let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
    have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
    have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
      h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
    have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
    obtain ⟨hnoVC, hokC⟩ := callResult_zero_bridge (fuel := fuel) hext hih (by omega) hfind hifc hzero hmatch
      (fun idx hltI => by simpa using (ACallArgs_erased_iff hargs).2 idx hltI) happs
      (Sim_add_staticStr hsim₁) hst₁ hstat₁F hFlt₁ hnkEnd hnspEnd
      (ArgListOk_add_staticStr hArgList₁) hArgsSrc₁ henvNRF₁ hForbLt₁
    refine ⟨hnoVC, fun rv st₂ B₂ hevC => ?_⟩
    obtain ⟨resFoot, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
      hpFrame₂, hpEnv₂, hpNum₂, honce₂, hssf₂, hsim₂, henvNRF₂,
      hv₂, hdisj₂, hnrf₂, hnv₂, hlive₂, _⟩ := hokC rv st₂ B₂ hevC
    have hresSrc : res.src = none := AApps_src_none hok₁ rfl happs
    have hpresEnvAll : PreservesActiveEnv Scope env aenv σ' st.heap st₂.heap := by
      intro k bk abk hsc hbk habk hne ha₂
      have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
      have ha₁ := ActiveVal.of_AStateLe hok₁ hle₂
        (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
        (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
      have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
      exact hp1.trans ((hpEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
    have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
    have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hv₂
    exact ⟨resFoot, by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
      hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂, hstat₁.trans hstat₂, hstr₁.trans hstr₂,
      hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
      fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
      honce₁.trans honce₂, StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
      hsimFinal, henvTaint₁.step hr₂ hnr₂,
      (fun k bk abk hsc hbk habk hne ha hregs hdeps => henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
      hvFinal, hdisj₂, (fun ha hregs hdeps => hnrf₂ ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
      hnv₂, taint_of_vsim_src_none hresSrc hvFinal, hlive₂, SrcOk_none hresSrc⟩

theorem evalS_call_ifaceFullPos_case {P : Prog} {ext : ExternOracle} {B : Nat}
    (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {r : Ref} {d : RunDef} {ifc : Iface} {args : List Term} {c : Cls}
    {σ σ₁ σ₂ σ' : AState} {avs : List (Option AVal)} {r0 res : AVal}
    (hfind : P.find? r = some d) (hifc : ifaceOf? d = some ifc)
    (hargs : ACallArgs P (some d) aenv 0 args σ avs σ₁)
    (hargsIH : ACallArgsProp P ext B (some d) aenv 0 args σ avs σ₁)
    (hpos : 0 < ifc.params.size) (hleLen : ifc.params.size ≤ avs.length)
    (hcall : Runs (callResult ifc (avs.toArray.extract 0 ifc.params.size) "a call") σ₁ r0 σ₂)
    (happs : AApps r0 ((avs.drop ifc.params.size).filterMap id) c σ₂ res σ') :
    ACallProp P ext B aenv r args c σ res σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  have hok := hsim.2.1
  obtain ⟨hok₁, hle₁, _⟩ := ACallArgs_state_le hok hargs
  obtain ⟨hok₂, hle₂, _, _, _, _, _, _, _, _, hr0Src, _⟩ := Runs_callResult hok₁ hcall
  obtain ⟨hok₃, hle₃, _, _⟩ := AApps_state_le hok₂ happs
  have hle₁₃ : AStateLe σ₁ σ' := hle₂.trans hle₃
  have hnk₁ : NoKillOk NoKill σ₁ := NoKillOk_of_AStateLe hle₁₃ hnkEnd
  have hnsp₁ : NoSpendOk NoSpend σ₁ := NoSpendOk_of_AStateLe hle₁₃ hnspEnd
  let BadDep₁ : Nat → Prop := fun d => d < σ₁.st.size ∧ BadDep d
  have hBadDep₁ : ∀ d, BadDep₁ d → σ₁.st[d]? = some .live :=
    BadDepLive_of_AStateLe hle₁₃ (fun d hbd => hBadDepEnd d hbd.2) (fun d hbd => hbd.1)
  have henvNRF_bd₁ : EnvNoReachForbid st Scope env aenv σ Forbid BadReg BadDep₁ := fun i b' ab' hsc' hbi' habi' hne' ha' hregs hdeps =>
    let hvI := ((hsim.2.2.2.2.2.1 i b' ab' hsc' hbi' habi').2 hne').2
    henvNRF i b' ab' hsc' hbi' habi' hne' ha' hregs
      (fun dep hdep hbd => hdeps dep hdep ⟨Nat.lt_of_lt_of_le (hvI.2.1 dep hdep) hle₁.1, hbd⟩)
  unfold TermPost; rw [hfind, MS_bind_run]
  obtain ⟨hnoVA, hokA⟩ := hargsIH hlc hcfd (B₀ := B₀) (fuel := fuel) (pref := []) hB₀ hfv hst hsim hstat hFlt
    hnk₁ hnsp₁ hIZero hHeadReg henvTaint henvNRF_bd₁ hForbidLt hBadDep₁
    ⟨(fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩
    (fun _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ _ h => by cases h)
  cases hevA : (evalCallArgsS P ext fuel env (some d) (args.zipIdx 0) []).run (st, B₀) with
  | error e => refine ⟨fun k hk => by cases hk; exact hnoVA k hevA, fun _ _ _ h => by cases h⟩
  | ok pa =>
    rcases pa with ⟨vs, ⟨st₁, B₁⟩⟩; dsimp only
    obtain ⟨cargs, hmatch, hB₁, hst₁, hsz₁, hcap₁, hr₁, hnr₁, hstat₁, hstr₁,
      hpFrame₁, hpEnv₁, hpNum₁, honce₁, hssf₁, hsim₁, henvTaint₁, henvNRF₁,
      hArgList₁, _, hArgsSrc₁⟩ := hokA vs st₁ B₁ hevA
    simp only [List.nil_append] at hArgList₁ hArgsSrc₁
    let Frame₁ : Nat → Prop := fun l => Frame l ∨ StaticStrLoc st₁ l
    have hstat₁F : ∀ l, StaticStrLoc st₁ l → Frame₁ l := fun _ h => Or.inr h
    have hFlt₁ : ∀ l, Frame₁ l → l < st₁.heap.objs.size := fun l h =>
      h.elim (fun hF => Nat.lt_of_lt_of_le (hFlt l hF) hsz₁) (fun hss => StOk_staticStrLoc_lt hst₁ hss)
    have hForbLt₁ : ∀ l, Forbid l → l < st₁.heap.objs.size := fun l hF => Nat.lt_of_lt_of_le (hForbidLt l hF) hsz₁
    have hleV : ifc.params.size ≤ vs.length := by have := hmatch.1; have := hmatch.2.1; omega
    obtain ⟨hnoVC, hokC⟩ := callResult_pos_bridge (fuel := fuel) hext hih (by omega) hfind hifc hpos hleV hmatch
      (fun idx hltI => by simpa using (ACallArgs_erased_iff hargs).2 idx hltI) hcall happs
      (Sim_add_staticStr hsim₁) hst₁ hstat₁F hFlt₁ hnkEnd hnspEnd
      (ArgListOk_add_staticStr hArgList₁) hArgsSrc₁ henvNRF₁ hForbLt₁ (fun x hbd => hBadDepEnd x hbd.2)
    refine ⟨hnoVC, fun rv st₂ B₂ hevC => ?_⟩
    obtain ⟨resFoot, hB₂, hst₂, hsz₂, hcap₂, hr₂, hnr₂, hstat₂, hstr₂,
      hpFrame₂, hpEnv₂, hpNum₂, honce₂, hssf₂, hsim₂, henvNRF₂,
      hv₂, hdisj₂, hnrf₂, hnv₂, hlive₂, _⟩ := hokC rv st₂ B₂ hevC
    have hresSrc : res.src = none := AApps_src_none hok₂ hr0Src happs
    have hpresEnvAll : PreservesActiveEnv Scope env aenv σ' st.heap st₂.heap := by
      intro k bk abk hsc hbk habk hne ha₂
      have hvK := ((hsim.2.2.2.2.2.1 k bk abk hsc hbk habk).2 hne).2
      have ha₁ := ActiveVal.of_AStateLe hok₁ hle₁₃
        (fun d hd => Nat.lt_of_lt_of_le (hvK.2.1 d hd) hle₁.1)
        (fun z hz => Nat.lt_of_lt_of_le (hvK.2.2.1 z hz).1 hle₁.1) ha₂
      have hp1 := hpEnv₁ k bk abk hsc hbk habk hne ha₁
      exact hp1.trans ((hpEnv₂ k bk abk hsc hbk habk hne ha₂).mono fun l hr => (Reach_congr hp1 l).mpr hr)
    have hsimFinal := Sim_shrink_frame (fun _ hF => Or.inl hF) hsim₂
    have hvFinal := VSim_shrink_frame (fun _ hF => Or.inl hF) hv₂
    exact ⟨resFoot, by omega, hst₂, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
      hr₂.trans hr₁, Nat.le_trans hnr₁ hnr₂, hstat₁.trans hstat₂, hstr₁.trans hstr₂,
      hpFrame₁.trans (hpFrame₂.mono fun _ h => Or.inl h), hpresEnvAll,
      fun l o num ho hc => hpNum₂ l o num (hpNum₁ l o num ho hc) hc,
      honce₁.trans honce₂, StaticStrFresh.trans hsz₁ (hpFrame₂.mono fun _ h => Or.inr h) hssf₁ hssf₂,
      hsimFinal, henvTaint₁.step hr₂ hnr₂,
      (fun k bk abk hsc hbk habk hne ha hregs hdeps => henvNRF₂ k bk abk hsc hbk habk hne ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
      hvFinal, hdisj₂, (fun ha hregs hdeps => hnrf₂ ha hregs (fun d hd hbd => hdeps d hd hbd.2)),
      hnv₂, taint_of_vsim_src_none hresSrc hvFinal, hlive₂, SrcOk_none hresSrc⟩

theorem evalS_major_varPlain_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {j : Nat} {mc : Cls} {b : ABnd} {σ pre : AState} {v : AVal}
    (hb : aenv[j]? = some b) (hr : Runs (readVar aenv j) σ v pre)
    (hdisj : b.mode.isUnique = false ∨ mc ≠ .val) :
    AMajorProp P ext B aenv (.var j mc) σ { v with cls := mc } false pre := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    _ hfv hst hsim _ hFlt _ _ _ _ henvTaint henvNRF hForbidLt _
  refine ⟨?_, fun hc => by cases hc⟩
  have hsc : Scope j := hfv j (.var (Nat.zero_le j))
  obtain ⟨hσEq, ⟨bc, ab, hbi, habi, hmodeEq, hneAb, hvEq⟩, hvar⟩ :=
    var_bridge (c := mc) hst hsim henvNRF hFlt hForbidLt hsc hr
  subst pre
  rw [hb] at habi; cases habi
  obtain ⟨ab', hab', _, _, hvd0, _⟩ := Runs_readVar hr
  rw [hb] at hab'; cases hab'
  have hvd : ValidDeps σ ({ v with cls := mc } : AVal).deps := by rw [hvEq]; exact hvd0
  have hbcNeB : (bc.mode == BinderMode.erased) = false := BinderMode_beq_false_of_ne (hmodeEq ▸ hneAb)
  let mVar : M Val := do
    let some b0 := env[j]? | stuckM
    if b0.mode == BinderMode.erased then violate .erasedRead
    live b0.val
    conform mc b0.val
  have hstep : (evalMajorS P ext fuel env (.var j mc)).run (st, B₀) =
      match (match mVar.run st with
        | .ok (rv0, st0) => if bc.mode.isUnique then (transfer P fuel bc.mode.isBorrowed rv0).run st0 else .ok (rv0, st0)
        | .error e => .error e) with
      | .ok (rv, st') => .ok (rv, (st', B₀))
      | .error e => .error e := by
    have hinner : (do
        let some b0 := env[j]? | stuckM
        if b0.mode == BinderMode.erased then violate .erasedRead
        live b0.val
        let v0 ← conform mc b0.val
        if b0.mode.isUnique then transfer P fuel b0.mode.isBorrowed v0 else pure v0).run st =
        match mVar.run st with
        | .ok (rv0, st0) => if bc.mode.isUnique then (transfer P fuel bc.mode.isBorrowed rv0).run st0 else .ok (rv0, st0)
        | .error e => .error e := by
      dsimp only [mVar]
      simp only [hbi, hbcNeB, Bool.false_eq_true, ↓reduceIte, M_bind_run]
      cases (live bc.val).run st with
      | error _ => rfl
      | ok pl =>
        dsimp only
        cases (conform mc bc.val).run pl.2 with
        | error _ => rfl
        | ok pc => dsimp only; cases bc.mode.isUnique <;> rfl
    unfold evalMajorS; rw [MS_liftM_run, hinner]
    cases (match mVar.run st with
      | .ok (rv0, st0) => if bc.mode.isUnique then (transfer P fuel bc.mode.isBorrowed rv0).run st0 else .ok (rv0, st0)
      | .error e => .error e) <;> rfl
  unfold TermPost; rw [hstep]
  rcases hvar with hSt | ⟨rv, st', hrun, hrg, hnr, hstat', hstr', hsz, hcap, hpresAll, hpresF,
    honce, hssf, hst', hsim', henvNRF', hv', hdisj', hnrf', hnv', _⟩
  · change mVar.run st = .error .stuck at hSt
    rw [hSt]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  · change mVar.run st = .ok (rv, st') at hrun
    rw [hrun]; dsimp only
    have hpost :
        (if bc.mode.isUnique then (transfer P fuel bc.mode.isBorrowed rv).run st' else .ok (rv, st')) = .error .outOfFuel ∨
        (if bc.mode.isUnique then (transfer P fuel bc.mode.isBorrowed rv).run st' else .ok (rv, st')) = .ok (rv, st') := by
      cases hbu : bc.mode.isUnique with
      | false => exact Or.inr rfl
      | true =>
        have hmcNe : mc ≠ .val := hdisj.resolve_left (by rw [← hmodeEq, hbu]; decide)
        exact transfer_nonValSafe (hnv' hvd hmcNe).2
    rcases hpost with hOOF | hOK
    · rw [hOOF]; exact ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    · rw [hOK]
      refine ⟨(fun _ h => by cases h), fun rv0 st0 B0 hokEq => ?_⟩
      cases hokEq
      have htaint : ValidDeps σ ({ v with cls := mc } : AVal).deps →
          (∀ c' ∈ rv.taint, c' < st'.nextRegion) ∧ OpenUnder st'.regions (I.regsOf ({ v with cls := mc } : AVal).regs) rv := by
        intro _
        by_cases hcV : mc = .val
        · subst hcV
          have hliveBc : LiveRef st.heap bc.val := by
            by_cases hact : ActiveVal σ (effVal b)
            · exact (((hsim.2.2.2.2.2.1 j bc b hsc hbi hb).2 hneAb).2.2.2.2.2 hact).1.1.self.1
            · have his : IsOnceSrc σ (effVal b) :=
                Classical.byContradiction fun hn => hact ⟨hvd0, fun h => absurd h hn⟩
              exact (((hsim.2.2.2.2.2.1 j bc b hsc hbi hb).2 hneAb).2.2.2.2.1 hvd0 his).liveRef
          dsimp only [mVar] at hrun
          simp only [hbi, hbcNeB, Bool.false_eq_true, ↓reduceIte, M_bind_run, live_ok hliveBc] at hrun
          have hconf : (conform .val bc.val).run st = .ok (bc.val, st) := rfl
          rw [hconf] at hrun; cases hrun
          rw [hvEq]; exact henvTaint j bc b hsc hbi hb hneAb
        · obtain ⟨_, hnv⟩ := hnv' hvd hcV
          have htn := hnv.taint_nil
          exact ⟨(fun _ hc => by rw [htn] at hc; cases hc), (fun _ hc => by rw [htn] at hc; cases hc)⟩
      have hsrc : SrcOk Scope aenv σ σ { v with cls := mc } := by
        intro id hs; rw [hvEq] at hs; dsimp only [effVal] at hs; cases hs
        exact Or.inl ⟨j, b, hsc, hb, hneAb, rfl, by rw [hvEq]; rfl, fun d => by rw [hvEq]⟩
      exact ⟨if mc == .val then envFoot j else fun (_ : Nat) => False, Nat.le_refl _, hst', hsz, hcap,
        hrg, hnr ▸ Nat.le_refl _, hstat' ▸ ArrayExtends.refl _, hstr' ▸ ArrayExtends.refl _,
        hpresF, Sim_preserves_of_old (AStateLe.refl _) hpresAll hsim,
        PreservesLocs_old_num hpresAll, honce, hssf, hsim',
        henvTaint.step hrg (hnr ▸ Nat.le_refl _), henvNRF', hv', hdisj', hnrf', hnv',
        htaint, live_of_vsim_validDeps hv' hvd, hsrc⟩

theorem evalS_irr_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {σ : AState} :
    ATermProp P ext B aenv .irr σ { cls := .irr } σ := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ _ hst hsim _ _ _ _ _ _ henvTaint henvNRF _ _
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      have hstep : (evalS P ext (n + 1) env .irr).run (st, b0 + 1) = .ok (.imm .irr, (st, b0)) := by
        unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl
      unfold TermPost; rw [hstep]
      refine ⟨(fun _ h => by cases h), fun rv st' B' hokEq => ?_⟩
      cases hokEq
      have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
        Sim_step (Nat.le_succ b0) (AStateLe.refl _) hsim.2.1 hsim.2.2.1 (RegsFuture.refl _)
          (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
          (PreservesActiveEnv.refl _ _ _ _ _) hsim
      exact ⟨fun (_ : Nat) => False, by omega, StOk_mono (by omega) hst, Nat.le_refl _, Nat.le_refl _,
        rfl, Nat.le_refl _, ArrayExtends.refl _, ArrayExtends.refl _, PreservesLocs.refl _ _,
        PreservesActiveEnv.refl _ _ _ _ _, (fun _ _ _ ho _ => ho), PreservesOnceShell.refl _,
        StaticStrFresh.refl _, hsimB, henvTaint, henvNRF,
        VSim_imm_irr (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h),
        ValEnvDisj_imm_irr rfl, fun _ => NoReachForbid_imm_irr st Forbid BadReg BadDep _,
        fun _ _ => ⟨ValBaseOk_imm st .irr, Or.inl ⟨.irr, rfl⟩⟩,
        fun _ => ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩,
        Or.inl ⟨ValBaseOk_imm st .irr, CtorFieldsOk_imm P ext b0 st .irr⟩, SrcOk_none rfl⟩

theorem evalS_constCall_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {r : Ref} {c : Cls} {σ σ' : AState} {res : AVal}
    (hcIH : ACallProp P ext B aenv r [] c σ res σ') :
    ATermProp P ext B aenv (.const r c) σ res σ' := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ _ hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      cases n with
      | zero =>
        cases b0 with
        | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; unfold spineS; rw [MS_bind_run, MS_spend_zero])
        | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; unfold spineS; rw [MS_bind_run, MS_spend_succ]; rfl)
      | succ m =>
        cases b0 with
        | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; unfold spineS; rw [MS_bind_run, MS_spend_zero])
        | succ b1 =>
          have hstep : (evalS P ext (m + 2) env (.const r c)).run (st, b1 + 2) =
              (do let vs ← evalCallArgsS P ext m env (P.find? r) (([] : List Term).zipIdx 0) []; callWithS P ext m r vs c).run (st, b1) := by
            conv => lhs; unfold evalS
            rw [MS_bind_run, MS_spend_succ]; dsimp only
            conv => lhs; unfold spineS
            rw [MS_bind_run, MS_spend_succ]
          have hsimB : Sim P ext b1 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
            Sim_step (by omega) (AStateLe.refl _) hsim.2.1 hsim.2.2.1 (RegsFuture.refl _)
              (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
              (PreservesActiveEnv.refl _ _ _ _ _) hsim
          obtain ⟨hnoV, hok⟩ := hcIH (fun _ h => by cases h) (fun _ h => by cases h)
            (B₀ := b1) (fuel := m) (by omega) (fun _ h => by cases h)
            (StOk_mono (by omega) hst) hsimB hstat hFlt hnkEnd hnspEnd hIZero hHeadReg
            henvTaint henvNRF hForbidLt hBadDepEnd
          unfold TermPost; rw [hstep]
          refine ⟨hnoV, fun rv st' B' hr => ?_⟩
          obtain ⟨ft, hB', rest⟩ := hok rv st' B' hr
          exact ⟨ft, by omega, rest⟩

theorem evalS_appConst_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {f a : Term} {c rc : Cls} {r : Ref} {args : Array Term}
    {σ σ' : AState} {res : AVal}
    (hsp : termSpine (.app f a c) = (.const r rc, args))
    (hcIH : ACallProp P ext B aenv r args.toList c σ res σ') :
    ATermProp P ext B aenv (.app f a c) σ res σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  have hcol := termSpine_eq_collect (.app f a c); rw [hsp] at hcol; dsimp only at hcol
  obtain ⟨hhCol, hargsCol⟩ := hcol
  have hlcCol := collect_lamsClosed (.app f a c) [] hlc (fun _ h => by cases h)
  have hcfdCol := collect_caseFieldsDistinct (.app f a c) [] hcfd (fun _ h => by cases h)
  have hlcArgs : ∀ t ∈ args.toList, LamsClosed t := fun t ht => hlcCol.2 t (hargsCol ▸ ht)
  have hcfdArgs : ∀ t ∈ args.toList, CaseFieldsDistinct t := fun t ht => hcfdCol.2 t (hargsCol ▸ ht)
  have hfvArgs : ∀ t ∈ args.toList, ∀ x, FreeVarIn 0 t x → Scope x := fun t ht x hx => by
    rcases (collect_freeVarIn (.app f a c) [] 0 x).2 t (hargsCol ▸ ht) hx with ⟨_, ha', _⟩ | h0
    · cases ha'
    · exact hfv x h0
  cases fuel with
  | zero =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; rfl)
  | succ n =>
    cases B₀ with
    | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_zero])
    | succ b0 =>
      cases n with
      | zero =>
        cases b0 with
        | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; unfold spineS; rw [MS_bind_run, MS_spend_zero])
        | succ _ => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; unfold spineS; rw [MS_bind_run, MS_spend_succ]; rfl)
      | succ m =>
        cases b0 with
        | zero => exact TermPost.of_outOfFuel (by unfold evalS; rw [MS_bind_run, MS_spend_succ]; dsimp only; unfold spineS; rw [MS_bind_run, MS_spend_zero])
        | succ b1 =>
          have hstep : (evalS P ext (m + 2) env (.app f a c)).run (st, b1 + 2) =
              (do let vs ← evalCallArgsS P ext m env (P.find? r) (args.toList.zipIdx 0) []; callWithS P ext m r vs c).run (st, b1) := by
            conv => lhs; unfold evalS
            rw [MS_bind_run, MS_spend_succ]; dsimp only
            rw [show collect (.app f a c) [] = (.const r rc, args.toList) from Prod.ext hhCol.symm hargsCol.symm]
            conv => lhs; unfold spineS
            rw [MS_bind_run, MS_spend_succ]
          have hsimB : Sim P ext b1 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
            Sim_step (by omega) (AStateLe.refl _) hsim.2.1 hsim.2.2.1 (RegsFuture.refl _)
              (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
              (PreservesActiveEnv.refl _ _ _ _ _) hsim
          obtain ⟨hnoV, hok⟩ := hcIH hlcArgs hcfdArgs (B₀ := b1) (fuel := m) (by omega) hfvArgs
            (StOk_mono (by omega) hst) hsimB hstat hFlt hnkEnd hnspEnd hIZero hHeadReg
            henvTaint henvNRF hForbidLt hBadDepEnd
          unfold TermPost; rw [hstep]
          refine ⟨hnoV, fun rv st' B' hr => ?_⟩
          obtain ⟨ft, hB', rest⟩ := hok rv st' B' hr
          exact ⟨ft, by omega, rest⟩

theorem evalS_alts_nil_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {k : CaseInfo} {mv : AVal} {consuming : Bool} {pre : AState}
    {j : Nat} {r_join : AVal} {σ_join : AState} :
    AAltsProp P ext B aenv k mv consuming pre j [] [] r_join σ_join :=
  fun _ _ _ hca _ => by cases hca

theorem evalS_alts_cons_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {k : CaseInfo} {mv : AVal} {consuming : Bool} {pre : AState}
    {j : Nat} {ca : CaseAlt} {cas : List CaseAlt} {altT : Term} {altTs : List Term}
    {r_j r_join : AVal} {post_j σ_chk_j σ_val_j σ_u_j σ_join : AState}
    {nextReg_j : Nat} {uniq_j : Bool}
    (hnr : pre.nextRegion ≤ nextReg_j)
    (halt : AAlt P aenv altT (caseAltArgs P k mv consuming j ca) { pre with nextRegion := nextReg_j } r_j post_j)
    (haltIH : AAltProp P ext B aenv altT (caseAltArgs P k mv consuming j ca) { pre with nextRegion := nextReg_j } r_j post_j)
    (hno : Runs (notOnceSrc r_j "a case alternative's result") post_j () σ_chk_j)
    (hoo : r_j.onceOnly = false)
    (hval : Runs (valid r_j "a case alternative's result") σ_chk_j () σ_val_j)
    (huniq : Runs (isUniq r_j) σ_val_j uniq_j σ_u_j)
    (hsj : StateJoinGe pre σ_u_j σ_join)
    (hvj : ValJoinGe pre.st.size { r_j with own := if r_j.own == Own.uniq && uniq_j then Own.uniq else Own.shared } r_join)
    (hrestIH : AAltsProp P ext B aenv k mv consuming pre (j + 1) cas altTs r_join σ_join) :
    AAltsProp P ext B aenv k mv consuming pre j (ca :: cas) (altT :: altTs) r_join σ_join := by
  intro offset ca' altT' hca' halt'
  cases offset with
  | zero =>
    simp at hca' halt'; subst hca' halt'
    exact ⟨nextReg_j, r_j, post_j, σ_chk_j, σ_val_j, uniq_j, σ_u_j,
      hnr, halt, haltIH, hno, hoo, hval, huniq, hsj, hvj⟩
  | succ m =>
    have h1 := hrestIH m ca' altT' hca' halt'
    have hidxEq : j + 1 + m = j + (m + 1) := by omega
    simpa [hidxEq] using h1

theorem evalS_evals_nil_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {σ : AState} :
    AEvalsProp P ext B aenv [] σ [] σ := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep pref
    _ _ hst hsim _ _ _ _ _ _ henvTaint henvNRF _ _ hargP hpreSrc hargsSrc
  have hrun : (evalListS P ext fuel env [] []).run (st, B₀) = .ok ([], (st, B₀)) := by unfold evalListS; rfl
  rw [hrun]
  refine ⟨(fun _ h => by cases h), fun vs st' B' hokEq => ?_⟩
  cases hokEq
  exact ⟨[], rfl, rfl, Nat.le_refl _, hst, Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _,
    ArrayExtends.refl _, ArrayExtends.refl _, PreservesLocs.refl _ _, PreservesActiveEnv.refl _ _ _ _ _,
    (fun _ _ _ ho _ => ho), PreservesOnceShell.refl _, StaticStrFresh.refl _,
    hsim, henvTaint, henvNRF, by simpa using hargP, by simpa using hpreSrc, by simpa using hargsSrc⟩

theorem evalS_callArgs_nil_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {d? : Option RunDef} {aenv : List ABnd} {idx : Nat} {σ : AState} :
    ACallArgsProp P ext B d? aenv idx [] σ [] σ := by
  intro _ _ B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep pref
    _ _ hst hsim _ _ _ _ _ _ henvTaint henvNRF _ _ hargP hpreSrc hargsSrc
  have hrun : (evalCallArgsS P ext fuel env d? (([] : List Term).zipIdx idx) []).run (st, B₀) = .ok ([], (st, B₀)) := by
    unfold evalCallArgsS; rfl
  rw [hrun]
  refine ⟨(fun _ h => by cases h), fun vs st' B' hokEq => ?_⟩
  cases hokEq
  exact ⟨[], ⟨rfl, rfl, fun i => by simp⟩, Nat.le_refl _, hst, Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _,
    ArrayExtends.refl _, ArrayExtends.refl _, PreservesLocs.refl _ _, PreservesActiveEnv.refl _ _ _ _ _,
    (fun _ _ _ ho _ => ho), PreservesOnceShell.refl _, StaticStrFresh.refl _,
    hsim, henvTaint, henvNRF, by simpa using hargP, by simpa using hpreSrc, by simpa using hargsSrc⟩

theorem evalS_major_nonVar_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {t : Term} {σ pre : AState} {mv : AVal}
    (hne : ∀ j mc, t ≠ .var j mc)
    (htIH : ATermProp P ext B aenv t σ mv pre) :
    AMajorProp P ext B aenv t σ mv false pre := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
  refine ⟨?_, fun hc => by cases hc⟩
  have hEq : evalMajorS P ext fuel env t = evalS P ext fuel env t := by
    cases t with
    | var j mc => exact absurd rfl (hne j mc)
    | irr | const _ _ | natLit _ | strLit _ | app _ _ _ | lam _ _ _ _ _ | letE _ _ _ _ | proj _ _ _ _ | case _ _ _ _ _ => rfl
  rw [hEq]
  exact htIH hlc hcfd hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg
    henvTaint henvNRF hForbidLt hBadDepEnd

theorem evalS_alt_nil_case {P : Prog} {ext : ExternOracle} {B : Nat}
    {aenv : List ABnd} {altT : Term} {σ σ' : AState} {r : AVal}
    (htIH : ATermProp P ext B aenv altT σ r σ') :
    AAltProp P ext B aenv altT [] σ r σ' := by
  intro hlc hcfd B₀ fuel st Frame NoKill NoSpend Scope env I envFoot Forbid BadReg BadDep cargs
    hB₀ hfv hst hsim hstat hFlt hnkEnd hnspEnd hIZero hHeadReg henvTaint henvNRF hForbidLt hBadDepEnd
    hlen _ _ _
  cases cargs with
  | cons _ _ => simp at hlen
  | nil =>
    cases fuel with
    | zero =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ _ => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_succ]; rfl)
    | succ n =>
      cases B₀ with
      | zero => exact TermPost.of_outOfFuel (by unfold applyAltS; rw [MS_bind_run, MS_spend_zero])
      | succ b0 =>
        have hstep : (applyAltS P ext (n + 1) env altT []).run (st, b0 + 1) = (evalS P ext n env altT).run (st, b0) := by
          unfold applyAltS; rw [MS_bind_run, MS_spend_succ]
        have hsimB : Sim P ext b0 st Frame NoKill NoSpend Scope env aenv σ I envFoot :=
          Sim_step (Nat.le_succ b0) (AStateLe.refl _) hsim.2.1 hsim.2.2.1 (RegsFuture.refl _)
            (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
            (PreservesActiveEnv.refl _ _ _ _ _) hsim
        obtain ⟨hnoV, hok⟩ := htIH hlc hcfd (B₀ := b0) (fuel := n) (by omega) hfv
          (StOk_mono (by omega) hst) hsimB hstat hFlt hnkEnd hnspEnd hIZero hHeadReg
          henvTaint henvNRF hForbidLt hBadDepEnd
        unfold TermPost; rw [hstep]
        refine ⟨hnoV, fun rv st' B' hr => ?_⟩
        obtain ⟨ft, hB', rest⟩ := hok rv st' B' hr
        exact ⟨ft, by omega, rest⟩

mutual

theorem evalS_checked_sound_term {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {t : Term} {σ σ' : AState} {r : AVal} :
    ATerm P aenv t σ r σ' → ATermProp P ext B aenv t σ r σ'
  | .irr => evalS_irr_case
  | .var hr => evalS_var_case hr
  | .natLit => evalS_natLit_case
  | .strLit => evalS_strLit_case
  | .constCall hc => evalS_constCall_case (evalS_checked_sound_call hidx hext hih hc)
  | .appConst hsp hc => evalS_appConst_case hsp (evalS_checked_sound_call hidx hext hih hc)
  | .appVal hsp hne hh hev happs =>
    evalS_appVal_case hsp hne hh (evalS_checked_sound_term hidx hext hih hh)
      hev (evalS_checked_sound_evals hidx hext hih hev) happs
  | .lam hcaps hbody hret hcons hEq =>
    evalS_lam_case hcaps hbody (evalS_checked_sound_term hidx hext hih hbody) hret hcons hEq
  | .letErased hb =>
    evalS_letErased_case (evalS_checked_sound_term hidx hext hih hb)
  | .letVal hneEr hv hbind hb hval hnotIn =>
    evalS_letVal_case hneEr hv (evalS_checked_sound_term hidx hext hih hv) hbind
      hb (evalS_checked_sound_term hidx hext hih hb) hval hnotIn
  | .proj he hval hproj =>
    evalS_proj_case (evalS_checked_sound_term hidx hext hih he) hval hproj
  | .caseTerm halSz hmj halts h0 hrjCls hrjSrc hrjOO hrjDeps hrjRegs hex happs =>
    evalS_caseTerm_case hidx halSz hmj (evalS_checked_sound_major hidx hext hih hmj)
      halts (evalS_checked_sound_alts hidx hext hih halts) h0 hrjCls hrjSrc hrjOO hrjDeps hrjRegs
      hex (evalS_checked_sound_evals hidx hext hih hex) happs

theorem evalS_checked_sound_alts {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {k : CaseInfo} {mv : AVal} {consuming : Bool} {pre : AState}
    {j : Nat} {cas : List CaseAlt} {altTs : List Term} {r_join : AVal} {σ_join : AState} :
    AAlts P aenv k mv consuming pre j cas altTs r_join σ_join →
    AAltsProp P ext B aenv k mv consuming pre j cas altTs r_join σ_join
  | .nil => evalS_alts_nil_case
  | .cons hnr halt hno hoo hval huniq hsj hvj hrest =>
    evalS_alts_cons_case hnr halt (evalS_checked_sound_alt hidx hext hih halt)
      hno hoo hval huniq hsj hvj (evalS_checked_sound_alts hidx hext hih hrest)

theorem evalS_checked_sound_evals {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {ts : List Term} {σ σ' : AState} {avs : List AVal} :
    AEvals P aenv ts σ avs σ' → AEvalsProp P ext B aenv ts σ avs σ'
  | .nil => evalS_evals_nil_case
  | .cons ht hrest =>
    evalS_evals_cons_case ht (evalS_checked_sound_term hidx hext hih ht)
      hrest (evalS_checked_sound_evals hidx hext hih hrest)

theorem evalS_checked_sound_callArgs {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {d? : Option RunDef} {aenv : List ABnd} {idx : Nat} {ts : List Term}
    {σ σ' : AState} {avs : List (Option AVal)} :
    ACallArgs P d? aenv idx ts σ avs σ' → ACallArgsProp P ext B d? aenv idx ts σ avs σ'
  | .nil => evalS_callArgs_nil_case
  | .consSkip hskip hrest =>
    evalS_callArgs_consSkip_case hskip (evalS_checked_sound_callArgs hidx hext hih hrest)
  | .consEval hkeep ht hrest =>
    evalS_callArgs_consEval_case hkeep ht (evalS_checked_sound_term hidx hext hih ht)
      hrest (evalS_checked_sound_callArgs hidx hext hih hrest)

theorem evalS_checked_sound_call {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {r : Ref} {args : List Term} {c : Cls}
    {σ σ' : AState} {res : AVal} :
    ACall P aenv r args c σ res σ' → ACallProp P ext B aenv r args c σ res σ'
  | .ind hfind hargs =>
    evalS_call_ind_case hfind (evalS_checked_sound_callArgs hidx hext hih hargs)
  | .ctor hfind hargs hctor =>
    evalS_call_ctor_case hfind hargs (evalS_checked_sound_callArgs hidx hext hih hargs) hctor
  | .prim hfind hargs hprim =>
    evalS_call_prim_case hidx hext hih hfind hargs (evalS_checked_sound_callArgs hidx hext hih hargs) hprim
  | .ifacePap hfind hifc hargs hlt hpap =>
    evalS_call_ifacePap_case hext hih hfind hifc hargs (evalS_checked_sound_callArgs hidx hext hih hargs) hlt hpap
  | .ifaceFullZero hfind hifc hargs hzero happs =>
    evalS_call_ifaceFullZero_case hext hih hfind hifc hargs
      (evalS_checked_sound_callArgs hidx hext hih hargs) hzero happs
  | .ifaceFullPos hfind hifc hargs hpos hleLen hcall happs =>
    evalS_call_ifaceFullPos_case hext hih hfind hifc hargs
      (evalS_checked_sound_callArgs hidx hext hih hargs) hpos hleLen hcall happs

theorem evalS_checked_sound_major {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {mj : Term} {σ pre : AState} {mv : AVal} {consuming : Bool} :
    AMajor P aenv mj σ mv consuming pre → AMajorProp P ext B aenv mj σ mv consuming pre
  | .varConsuming hb hr hu hmc hfl => evalS_major_varConsuming hb hr hu hmc hfl
  | .varPlain hb hr hdisj => evalS_major_varPlain_case hb hr hdisj
  | .nonVar hne ht => evalS_major_nonVar_case hne (evalS_checked_sound_term hidx hext hih ht)

theorem evalS_checked_sound_alt {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {altT : Term} {aargs : List (AVal × Bool × Bool)}
    {σ σ' : AState} {r : AVal} :
    AAlt P aenv altT aargs σ r σ' → AAltProp P ext B aenv altT aargs σ r σ'
  | .nil ht => evalS_alt_nil_case (evalS_checked_sound_term hidx hext hih ht)
  | .lamErased halt hret =>
    evalS_alt_lamErased halt (evalS_checked_sound_alt hidx hext hih halt) hret
  | .lamKept hadm hbind halt hret =>
    evalS_alt_lamKept hadm hbind halt (evalS_checked_sound_alt hidx hext hih halt) hret
  | .nonLam hne hnoEr ht happs =>
    evalS_alt_nonLam_case hne hnoEr ht (evalS_checked_sound_term hidx hext hih ht) happs

end

/-- Main exported simulation soundness theorem for checked bodies: any step-free `ATerm` derivation
simulates `evalS` at any budget `B₀ ≤ B + 1` with full heap, region, frame, taint, and alias invariants. -/
theorem evalS_checked_sound {P : Prog} {ext : ExternOracle} {B : Nat}
    (hidx : CtorsIndexed P) (hext : ExternOk P ext) (hih : FullIH P ext B)
    {aenv : List ABnd} {t : Term} {σ σ' : AState} {r : AVal}
    (hder : ATerm P aenv t σ r σ') :
    ATermProp P ext B aenv t σ r σ' :=
  evalS_checked_sound_term hidx hext hih hder

end IxC.Resource.Proof
