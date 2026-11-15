import IxC.Kernel.Model.Restrict

/-! # Model restriction with literal-sensitive support

`Expr.Supports` records the constructor keys of literals where they occur. A model can therefore
be restricted without retaining string-support roles when none of the selected terms uses a
string literal. Projection tables are preserved, and the natural-number basis remains available
for the model's arithmetic laws.
-/

set_option maxHeartbeats 800000

namespace Ix.Kernel

universe w

/-- Keys needed to interpret an expression, including constructor forms of its literals. -/
def Expr.Supports (K : Key md → Prop) : Expr md → Prop
  | .bvar _ | .fvar _ _ | .sort _ => True
  | .const n _ => K n
  | .app f a => f.Supports K ∧ a.Supports K
  | .lam ty b _ | .forallE ty b _ => ty.Supports K ∧ b.Supports K
  | .letE ty v b _ => ty.Supports K ∧ v.Supports K ∧ b.Supports K
  | .lit (.natVal _) => K natZeroName ∧ K natSuccName
  | .lit (.strVal _) => LitKeys K
  | .proj _ _ e => e.Supports K

theorem supports_natLit {K : Key md → Prop} (hnat : K natZeroName ∧ K natSuccName) :
    ∀ n : Nat, (natLitToConstructor n : Expr md).Supports K
  | 0 => hnat.1
  | _ + 1 => ⟨hnat.2, hnat⟩

theorem supports_strLit {K : Key md → Prop} (hlit : LitKeys K) (s : String) :
    (strLitToConstructor s : Expr md).Supports K := by
  obtain ⟨hzero, hsucc, hso, hnil, hcons, hchar, hofNat⟩ := hlit
  unfold strLitToConstructor
  simp only [Expr.Supports]
  refine ⟨hso, ?_⟩
  generalize s.toList = chars
  induction chars with
  | nil => simp only [List.foldr, Expr.Supports]; exact ⟨hnil, hchar⟩
  | cons c cs ih =>
    simp only [List.foldr, Expr.Supports] at ih ⊢
    exact ⟨⟨⟨hcons, hchar⟩, ⟨hofNat, hzero, hsucc⟩⟩, ih⟩

variable {V : Type w} [SetTheory V]

theorem Denotes.mono_env_supported {cval : Key md → (LevelParam → Nat) → V} {env env' : Env md}
    {φ : LevelParam → Nat} {K : Key md → Prop}
    (hfind : ∀ n, K n → env'.find? n = env.find? n)
    (hproj : ∀ T i, env'.findProj? T i = env.findProj? T i)
    :
    ∀ {ρ : BVarIdx → V} {e : Expr md} {v : V},
      Denotes cval env φ ρ e v → e.Supports K → Denotes cval env' φ ρ e v := by
  intro ρ e v h
  induction h with
  | bvar => exact fun _ => .bvar
  | sort => exact fun _ => .sort
  | const hf hlen =>
    intro hK
    exact .const (by rw [hfind _ hK]; exact hf) hlen
  | app _ _ ihf iha =>
    intro hK
    simp only [Expr.Supports] at hK
    exact .app (ihf hK.1) (iha hK.2)
  | lam _ _ hP ihA ihF =>
    intro hK
    simp only [Expr.Supports] at hK
    exact .lam (ihA hK.1) (fun x hx => ihF x hx hK.2) hP
  | pi _ _ hP ihA ihB =>
    intro hK
    simp only [Expr.Supports] at hK
    exact .pi (ihA hK.1) (fun x hx => ihB x hx hK.2) hP
  | proj_table ht _ ih =>
    intro hK
    simp only [Expr.Supports] at hK
    exact .proj_table (by rw [hproj]; exact ht) (ih hK)
  | proj_fst ht _ ih =>
    intro hK
    simp only [Expr.Supports] at hK
    exact .proj_fst (by rw [hproj]; exact ht) (ih hK)
  | proj_snd ht _ ih =>
    intro hK
    simp only [Expr.Supports] at hK
    exact .proj_snd (by rw [hproj]; exact ht) (ih hK)
  | natLit _ ih => exact fun hK => .natLit (ih (supports_natLit hK _))
  | strLit _ ih => exact fun hK => .strLit (ih (supports_strLit hK _))

/-- **A list denotation transports** as `Denotes.mono_env_supported` does. -/
theorem DenotesList.mono_env_supported {cval : Key md → (LevelParam → Nat) → V} {env env' : Env md}
    {φ : LevelParam → Nat} {K : Key md → Prop}
    (hfind : ∀ n, K n → env'.find? n = env.find? n)
    (hproj : ∀ T i, env'.findProj? T i = env.findProj? T i)
    {ρ : BVarIdx → V} :
    ∀ {es : List (Expr md)} {vs : List V}, DenotesList cval env φ ρ es vs →
      (∀ e ∈ es, e.Supports K) → DenotesList cval env' φ ρ es vs := by
  intro es vs h
  induction h with
  | nil => exact fun _ => .nil
  | cons he _ ih =>
    intro hK
    exact .cons (Denotes.mono_env_supported hfind hproj he (hK _ (by simp)))
      (ih fun e he' => hK e (by simp [he']))

/-- **A telescope fit transports** as `Denotes.mono_env_supported` does, and what remains of the
telescope mentions only the keys the telescope does. -/
theorem Fits.mono_env_supported {cval : Key md → (LevelParam → Nat) → V} {env env' : Env md}
    {φ : LevelParam → Nat} {K : Key md → Prop}
    (hfind : ∀ n, K n → env'.find? n = env.find? n)
    (hproj : ∀ T i, env'.findProj? T i = env.findProj? T i)
    :
    ∀ {ρ ρ' : BVarIdx → V} {T R : Expr md} {xs : List V},
      Fits cval env φ ρ T xs ρ' R → T.Supports K → Fits cval env' φ ρ T xs ρ' R ∧ R.Supports K := by
  intro ρ ρ' T R xs h
  induction h with
  | nil => exact fun hK => ⟨.nil, hK⟩
  | cons hA hx _ ih =>
    intro hK
    simp only [Expr.Supports] at hK
    obtain ⟨h1, h2⟩ := ih hK.2
    exact ⟨.cons (Denotes.mono_env_supported hfind hproj hA hK.1) hx h1, h2⟩

/-- **A graded reading transports** as `Denotes.mono_env_supported` does: the grading reads
denotations at its applications (forward) and at its binders' domains (backward), and
the two environments agree on both sides. -/
theorem GradedBy.mono_env_supported {cval : Key md → (LevelParam → Nat) → V} {env env' : Env md}
    {φ : LevelParam → Nat} {K : Key md → Prop}
    (hfind : ∀ n, K n → env'.find? n = env.find? n)
    (hproj : ∀ T i, env'.findProj? T i = env.findProj? T i)
    :
    ∀ {e : Expr md} {ρ : BVarIdx → V},
      GradedBy (Denotes cval env φ) ρ e → e.Supports K → GradedBy (Denotes cval env' φ) ρ e := by
  have hfind' : ∀ n, K n → env.find? n = env'.find? n := fun n h => (hfind n h).symm
  have hproj' : ∀ T i, env.findProj? T i = env'.findProj? T i := fun T i => (hproj T i).symm
  intro e
  induction e with
  | app f a ihf iha =>
    intro ρ h hK
    simp only [GradedBy] at h ⊢
    simp only [Expr.Supports] at hK
    obtain ⟨hf, ha, r, A, F, X, B, hF, hX, hmem, hx, h0⟩ := h
    exact ⟨ihf hf hK.1, iha ha hK.2, r, A, F, X, B, Denotes.mono_env_supported hfind hproj hF hK.1,
      Denotes.mono_env_supported hfind hproj hX hK.2, hmem, hx, h0⟩
  | lam ty b m ihty ihb =>
    intro ρ h hK
    simp only [GradedBy] at h ⊢
    simp only [Expr.Supports] at hK
    exact ⟨ihty h.1 hK.1, fun A hA x hx =>
      ihb (h.2 A (Denotes.mono_env_supported hfind' hproj' hA hK.1) x hx) hK.2⟩
  | forallE ty b m ihty ihb =>
    intro ρ h hK
    simp only [GradedBy] at h ⊢
    simp only [Expr.Supports] at hK
    exact ⟨ihty h.1 hK.1, fun A hA x hx =>
      ihb (h.2 A (Denotes.mono_env_supported hfind' hproj' hA hK.1) x hx) hK.2⟩
  | proj s i e ih =>
    intro ρ h hK
    simp only [GradedBy] at h ⊢
    simp only [Expr.Supports] at hK
    exact ih h hK
  | bvar _ => intro _ _ _; exact True.intro
  | fvar _ _ _ => intro _ _ _; exact True.intro
  | sort _ => intro _ _ _; exact True.intro
  | const _ _ => intro _ _ _; exact True.intro
  | letE _ _ _ _ _ _ _ => intro _ _ _; exact True.intro
  | lit _ => intro _ _ _; exact True.intro

theorem Expr.Supports.instantiateLevelParams {K : Key md → Prop} (ks : List LevelParam)
    (us : List Level) : ∀ {e : Expr md}, e.Supports K → (e.instantiateLevelParams ks us).Supports K := by
  intro e
  induction e <;> simp_all [Expr.Supports, Expr.instantiateLevelParams]

/-- A spine's arguments mention only the keys the spine does. -/
theorem Expr.Supports.getAppArgs {K : Key md → Prop} :
    ∀ {e : Expr md}, e.Supports K → ∀ x ∈ e.getAppArgs, x.Supports K := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    simp only [Expr.Supports] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h.1 x hx
    · exact h.2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

/-- Restrict a model using the support of retained terms. Natural literals used by the
model's arithmetic laws require the natural-number constructor basis; string support is needed
only when it occurs in a retained term. -/
def Model.restrict_supported {env env' : Env md} (M : Model V env) {K : Key md → Prop}
    (hfind : ∀ n, K n → env'.find? n = env.find? n)
    (hproj : ∀ T i, env'.findProj? T i = env.findProj? T i)
    (hnat : K natZeroName ∧ K natSuccName)
    (hsub : ∀ c ∈ env'.consts, c ∈ env.consts)
    (hname : ∀ c ∈ env'.consts, K c.name)
    (htype : ∀ c ∈ env'.consts, c.toConstantVal.type.Supports K)
    (hvalue : ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ env'.consts →
      value.Supports K)
    (hrhs : ∀ cv mI rP rules, ConstantInfo.recInfo cv mI rP rules ∈ env'.consts →
      ∀ rl ∈ rules, rl.rhs.Supports K)
    (hF : K falseName) (hE : K eqName)
    (hbool : K boolTrueName ∧ K boolFalseName)
    (hctor : ∀ T i entry, env'.findProj? T i = some entry → K T → K entry.ctor)
    (hbody : ∀ T i entry, env'.findProj? T i = some entry → K T → entry.body.Supports K) :
    Model V env' where
  cval := M.cval
  mem := fun c hc φ ρ =>
    let ⟨T, hT, hm⟩ := M.mem c (hsub c hc) φ ρ
    ⟨T, Denotes.mono_env_supported hfind hproj hT (htype c hc), hm⟩
  false_empty := fun φ ρ F h => M.false_empty φ ρ F (Denotes.const_back (hfind _ hF) h)
  eq_equality := fun u φ ρ E A a b h =>
    M.eq_equality u φ ρ E A a b (Denotes.const_back (hfind _ hE) h)
  punit_unit := by
    intro us vs φ ψ ρ ρ' P Q x y hP hQ hx hy
    obtain ⟨ci, hf⟩ := hP.const_stored
    have hK : K punitName := by
      have h := hname _ (List.mem_of_find?_eq_some hf)
      rwa [show ci.name = punitName from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == punitName) hf]
        at h
    exact M.punit_unit us vs φ ψ ρ ρ' P Q x y (Denotes.const_back (hfind _ hK) hP)
      (Denotes.const_back (hfind _ hK) hQ) hx hy
  defn_value := fun cv value hint hc φ ρ =>
    Denotes.mono_env_supported hfind hproj (M.defn_value cv value hint (hsub _ hc) φ ρ)
      (hvalue cv value hint hc)
  cval_params := fun n ci h φ₁ φ₂ agree => by
    have hK : K n := by
      have hn := hname _ (List.mem_of_find?_eq_some h)
      rwa [show ci.name = n from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == n) h] at hn
    exact M.cval_params n ci (by rw [← hfind n hK]; exact h) φ₁ φ₂ agree
  iota_rule := by
    intro r cv mI rP rules rl hf hrl cvC nP nF hC us φ ρ σ σC xs ys dom body RC m D ls R K' X
      hus hxs hys hR hfitR hdomFn hX hK hfitC hmaj hpar hidx
    have hfind' : ∀ n, K n → env.find? n = env'.find? n := fun n h => (hfind n h).symm
    have hproj' : ∀ T i, env.findProj? T i = env'.findProj? T i := fun T i => (hproj T i).symm
    have hmR := List.mem_of_find?_eq_some hf
    have hmC := List.mem_of_find?_eq_some hC
    have hKr : K r := by
      have h := hname _ hmR
      rwa [show (ConstantInfo.recInfo cv mI rP rules).name = r from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == r) hf] at h
    have hKc : K rl.ctor := by
      have h := hname _ hmC
      rwa [show (ConstantInfo.ctorInfo cvC nP nF).name = rl.ctor from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == rl.ctor) hC] at h
    obtain ⟨hfitR', hresR⟩ := Fits.mono_env_supported hfind' hproj' hfitR
      (Expr.Supports.instantiateLevelParams _ _ (htype _ hmR))
    have hdomK : dom.Supports K := hresR.1
    obtain ⟨hfitC', hresC⟩ := Fits.mono_env_supported hfind' hproj' hfitC
      (Expr.Supports.instantiateLevelParams _ _ (htype _ hmC))
    obtain ⟨H, hH, hgH, hspH, heq⟩ := M.iota_rule r cv mI rP rules rl
      (by rw [← hfind r hKr]; exact hf) hrl
      cvC nP nF
      (by rw [← hfind _ hKc]; exact hC) us φ ρ σ σC xs ys dom body RC m D ls R K' X
      hus hxs hys (Denotes.mono_env_supported hfind' hproj' hR hKr) hfitR' hdomFn
      (Denotes.mono_env_supported hfind' hproj' hX hdomK)
      (Denotes.mono_env_supported hfind' hproj' hK hKc) hfitC' hmaj
      (fun hc => DenotesList.mono_env_supported hfind' hproj' (hpar hc)
        (fun e he => Expr.Supports.getAppArgs hdomK e (List.mem_of_mem_take he)))
      (fun hm => DenotesList.mono_env_supported hfind' hproj' (hidx hm)
        (fun e he => Expr.Supports.getAppArgs hresC e (List.mem_of_mem_drop he)))
    have hrefs := Expr.Supports.instantiateLevelParams cv.levelParams us
      (hrhs cv mI rP rules hmR rl hrl)
    exact ⟨H, Denotes.mono_env_supported hfind hproj hH hrefs,
      GradedBy.mono_env_supported hfind hproj hgH hrefs, hspH, heq⟩
  unit_like := by
    intro T cvT caps hf hu us φ ρ σ ts R F x y hus hts hF hfit hx hy
    have hfind' : ∀ n, K n → env.find? n = env'.find? n := fun n h => (hfind n h).symm
    have hproj' : ∀ T i, env.findProj? T i = env'.findProj? T i := fun T i => (hproj T i).symm
    have hmT := List.mem_of_find?_eq_some hf
    have hKT : K T := by
      have h := hname _ hmT
      rwa [show (ConstantInfo.indInfo cvT caps).name = T from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == T) hf] at h
    obtain ⟨hfit', -⟩ := Fits.mono_env_supported hfind' hproj' hfit
      (Expr.Supports.instantiateLevelParams _ _ (htype _ hmT))
    exact M.unit_like T cvT caps (by rw [← hfind T hKT]; exact hf) hu us φ ρ σ ts R F x y
      hus hts (Denotes.mono_env_supported hfind' hproj' hF hKT) hfit' hx hy
  proj_law := by
    intro T i entry cvT capsT hfP hfT
    have hfind' : ∀ n, K n → env.find? n = env'.find? n := fun n h => (hfind n h).symm
    have hproj' : ∀ T i, env.findProj? T i = env'.findProj? T i := fun T i => (hproj T i).symm
    have hmT := List.mem_of_find?_eq_some hfT
    have hKT : K T := by
      have h := hname _ hmT
      rwa [show (ConstantInfo.indInfo cvT capsT).name = T from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == T) hfT] at h
    have hKC := hctor T i entry hfP hKT
    obtain ⟨hlpsT, hsortT, cvC, hfC, hlpsC, hresC, hlaws⟩ := M.proj_law T i entry cvT capsT
      (by rw [← hproj]; exact hfP) (by rw [← hfind T hKT]; exact hfT)
    have hfC' : env'.find? entry.ctor = some (.ctorInfo cvC entry.numParams entry.numFields) := by
      rw [hfind _ hKC]; exact hfC
    have hmC := List.mem_of_find?_eq_some hfC'
    refine ⟨hlpsT, hsortT, cvC, hfC', hlpsC, hresC, ?_⟩
    intro us φ ρ Fd Kd hus hFd hKd
    obtain ⟨hι, hη⟩ := hlaws us φ ρ Fd Kd hus (Denotes.mono_env_supported hfind' hproj' hFd hKT)
      (Denotes.mono_env_supported hfind' hproj' hKd hKC)
    refine ⟨fun hg σ R ys hys hfit => hι hg σ R ys hys ?_,
      fun σ R ts x hts hfit hx => hη σ R ts x hts ?_ hx⟩
    · exact (Fits.mono_env_supported hfind' hproj' hfit
        (Expr.Supports.instantiateLevelParams _ _ (htype _ hmC))).1
    · exact (Fits.mono_env_supported hfind' hproj' hfit
        (Expr.Supports.instantiateLevelParams _ _ (htype _ hmT))).1
  proj_type := by
    intro T i entry hfP us φ ρ F ts x hus hF hg hts hok hx
    obtain ⟨ci, hfT⟩ := hF.const_stored
    have hKT : K T := by
      have h := hname _ (List.mem_of_find?_eq_some hfT)
      rwa [show ci.name = T from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == T) hfT] at h
    obtain ⟨B, hB, hgB, hmB⟩ := M.proj_type T i entry (by rw [← hproj]; exact hfP) us φ ρ F ts x
      hus (Denotes.const_back (hfind _ hKT) hF) hg hts hok hx
    have hK := Expr.Supports.instantiateLevelParams entry.levelParams us (hbody T i entry hfP hKT)
    exact ⟨B, Denotes.mono_env_supported hfind hproj hB hK, GradedBy.mono_env_supported hfind hproj hgB hK,
      hmB⟩
  eta_fn := by
    intro T cvT caps C hf heta hres hC hresC hCst hslots us φ ρ σ R ts x hus hts hfit hx
    have hfind' : ∀ n, K n → env.find? n = env'.find? n := fun n h => (hfind n h).symm
    have hproj' : ∀ T i, env.findProj? T i = env'.findProj? T i := fun T i => (hproj T i).symm
    have hKof : ∀ {n : Key md} {ci : ConstantInfo md}, env'.find? n = some ci → K n := by
      intro n ci hf
      have h := hname _ (List.mem_of_find?_eq_some hf)
      rwa [show ci.name = n from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == n) hf] at h
    obtain ⟨cvC, nP, nF, hfC⟩ := hCst
    obtain ⟨hfit', -⟩ := Fits.mono_env_supported hfind' hproj' hfit
      (Expr.Supports.instantiateLevelParams _ _ (htype _ (List.mem_of_find?_eq_some hf)))
    exact M.eta_fn T cvT caps C (by rw [← hfind _ (hKof hf)]; exact hf) heta hres hC hresC
      ⟨cvC, nP, nF, by rw [← hfind _ (hKof hfC)]; exact hfC⟩
      (fun j hj => by
        obtain ⟨cv, mI, rP, rules, hj'⟩ := hslots j hj
        exact ⟨cv, mI, rP, rules, by rw [← hfind _ (hKof hj')]; exact hj'⟩)
      us φ ρ σ R ts x hus hts hfit' hx
  lit_ops := by
    have hfind' : ∀ n, K n → env.find? n = env'.find? n := fun n h => (hfind n h).symm
    have hproj' : ∀ T i, env.findProj? T i = env'.findProj? T i := fun T i => (hproj T i).symm
    have hKof : ∀ {n : Key md} {ci : ConstantInfo md}, env'.find? n = some ci → K n := by
      intro n ci hf
      have h := hname _ (List.mem_of_find?_eq_some hf)
      rwa [show ci.name = n from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == n) hf] at h
    obtain ⟨hpred, harith, hcmp⟩ := M.lit_ops
    refine ⟨fun cv v hint hf φ ρ a X h => ?_, fun c f hc cv v hint hf φ ρ a b X h => ?_,
      fun c f hc cv v hint hf φ ρ a b X h => ?_⟩
    · have hK := hKof hf
      exact Denotes.mono_env_supported hfind hproj hlit
        (hpred cv v hint (by rw [← hfind _ hK]; exact hf) φ ρ a X
          (Denotes.mono_env_supported hfind' hproj' h
            (by exact ⟨hK, hnat⟩)))
        (by exact hnat)
    · have hK := hKof hf
      exact Denotes.mono_env_supported hfind hproj hlit
        (harith c f hc cv v hint (by rw [← hfind _ hK]; exact hf) φ ρ a b X
          (Denotes.mono_env_supported hfind' hproj' h
            (by exact ⟨⟨hK, hnat⟩, hnat⟩)))
        (by exact hnat)
    · have hK := hKof hf
      refine Denotes.mono_env_supported hfind hproj hlit
        (hcmp c f hc cv v hint (by rw [← hfind _ hK]; exact hf) φ ρ a b X
          (Denotes.mono_env_supported hfind' hproj' h
            (by exact ⟨⟨hK, hnat⟩, hnat⟩))) ?_
      show K (if f a b = true then boolTrueName else boolFalseName)
      split
      · exact hbool.1
      · exact hbool.2

  nat_add := by
    have hfind' : ∀ n, K n → env.find? n = env'.find? n := fun n h => (hfind n h).symm
    have hproj' : ∀ T i, env.findProj? T i = env'.findProj? T i := fun T i => (hproj T i).symm
    have hKof : ∀ {n : Key md} {ci : ConstantInfo md}, env'.find? n = some ci → K n := by
      intro n ci hf
      have h := hname _ (List.mem_of_find?_eq_some hf)
      rwa [show ci.name = n from
        by simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == n) hf] at h
    have hKc : ∀ {φ : LevelParam → Nat} {ρ : BVarIdx → V} {n : Key md} {us : List Level} {X : V},
        Denotes M.cval env' φ ρ (.const n us) X → K n := by
      intro φ ρ n us X h
      cases h with
      | const hf _ => exact hKof hf
    intro cv v hint hf φ ρ N Z S A hN hZ hS hA
    exact M.nat_add cv v hint (by rw [← hfind _ (hKof hf)]; exact hf) φ ρ N Z S A
      (Denotes.mono_env_supported hfind' hproj' hN (hKc hN))
      (Denotes.mono_env_supported hfind' hproj' hZ (hKc hZ))
      (Denotes.mono_env_supported hfind' hproj' hS (hKc hS))
      (Denotes.mono_env_supported hfind' hproj' hA (hKc hA))
  graded := by
    intro c hc φ ρ
    obtain ⟨hty, hval⟩ := M.graded c (hsub c hc) φ ρ
    refine ⟨GradedBy.mono_env_supported hfind hproj hty (htype c hc), ?_⟩
    intro cv value hint hceq
    subst hceq
    exact GradedBy.mono_env_supported hfind hproj (hval cv value hint rfl) (hvalue cv value hint hc)

end Ix.Kernel
