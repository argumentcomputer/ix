import IxCCGrounding.RootInst

/-!
# Typing at refused sites from #678's `graded` field (`IxCCGrounding.Graded`)

Every root theorem assumes `SitesOkRes`: typing (`SiteOk`) at the application sites the syntactic
direct route refuses. #678's model has a field, `graded` (`GradedLaw`, copied verbatim in
`IxCCGrounding.Laws`), saying that every stored type and every stored definition value has a graded
reading: at every application node, under every binder at every member of its domain, the function
denotes a member of some product `piR r A B` whose domain holds the argument. Walked down the sites
SrcEval evaluates (`graded_sites`; an `eqn` body through its stored theorem's type,
`runPair_graded`), that is `SiteOk` less `r ≠ 0`.

**The `r ≠ 0` gap, and what closes it.** `r = 0` forces the function to be the proof point
(`eq_pt_of_mem_piR_zero`), and `pt` lies in no positive-regime product (`not_pt_mem_piR_pos`). So it
suffices that the function lies in some positive-regime product, which the head's stored type gives
(`head_pos`): **`HeadRegimeAt`** reads, for the spine `k.{us} a₁ … aₙ` at the site's function, the
binder data (`BinderMeta.pw`) of the first `n + 1` `∀`s of `k`'s stored type **as written** (no
reduction, no conversion, no argument check), and asks each not to hold at the head's assignment
(`Level.substFn φ lps us`, i.e. at the enclosing constant's profile through `Level.substPW` at the
head's levels, which is what `headRegimeB` decides). Along the spine, `graded`'s product at each
node and the type's product share the function, both positive, so they have one domain
(`piR_dom_unique`), the argument lies in the type's domain, and the next application lies in the
next product (`app_mem_piR_pos`). When binder data move into the record format at the #678 ingest,
`headRegimeB` reads them from there.

**Why not relax `SiteOk` at regime 0.** At a closure applied in regime 0 the fundamental lemma reads
the body at the argument, which `Denotes.lam` gives only for arguments in the λ's own domain; a
regime-0 product (`{pt}`-valued) carries no domain to supply that. So the gap is closed on the head,
not by weakening `SiteOk`.

**Scope.** Only at the sites the direct route refuses (`HeadRegimeRes`): there the direct route keeps
the rest (on the corpus the syntactic reading is narrower than the direct route at 70 sites, where
the head's type is a `∀` only after δ). Not covered: the sites of recursor rule bodies (`RecSites`),
which `graded` does not speak of (a rule is neither a stored type nor a value) and which stay with the
check. `graded` is a separate hypothesis beside `Laws678`: the theorems here assume six of #678's
fields, the `_678` family five.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-! ## The head's regime, as written -/

/-- The `n`-th binder's datum of a telescope, as written. -/
def nthMeta : Nat → KExpr → Option BinderMeta
  | 0, .forallE _ _ m => some m
  | n + 1, .forallE _ b _ => nthMeta n b
  | _, _ => none

theorem piBody_of_nthMeta : ∀ (n : Nat) (T : KExpr) {m : BinderMeta}, nthMeta n T = some m →
    ∃ d b, piBody n T = .forallE d b m := by
  intro n
  induction n with
  | zero =>
    intro T m h
    cases T <;> simp [nthMeta] at h
    subst h
    exact ⟨_, _, rfl⟩
  | succ n ih =>
    intro T m h
    cases T <;> simp [nthMeta] at h
    simpa [piBody] using ih _ h

theorem piBody_succ : ∀ (n : Nat) (T d b : KExpr) (m : BinderMeta),
    piBody n T = .forallE d b m → piBody (n + 1) T = b := by
  intro n
  induction n with
  | zero =>
    intro T d b m h
    simp only [piBody] at h
    subst h
    rfl
  | succ n ih =>
    intro T d b m h
    cases T with
    | forallE d' b' m' =>
      simp only [piBody] at h ⊢
      exact ih _ _ _ _ h
    | _ => simp [piBody] at h

/-- **The head's regime at a site's function `f`**: `f` is a spine `k.{us} a₁ … aₙ` over a stored
constant, and the first `n + 1` binders of `k`'s stored type, as written, are `∀`s whose data do not
hold at the head's assignment. -/
def HeadRegimeAt (env : KEnv) (φ : LevelParam → Nat) (f : KExpr) : Prop :=
  ∃ (k : KKey) (us : List Level) (ci : ConstantInfo .anon),
    f.getAppFn = .const k us ∧ env.find? k = some ci ∧
    us.length = ci.toConstantVal.levelParams.length ∧
    ∀ j ≤ f.getAppArgs.length, ∃ m, nthMeta j ci.toConstantVal.type = some m ∧
      m.pw.holds (Level.substFn φ ci.toConstantVal.levelParams us) = false

/-- **`HeadRegime` at the sites the direct route refuses**, at every `Ok` instance. -/
def HeadRegimeRes (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  ∀ c ls t e, S c → Ok p ann c ls → RunPair p env κ c t e →
    ∀ φ, LvAt φ (lpsOf c) ls → ∀ s ∈ evalSites ls [] t e, s ∈ runRefused p env lpsOf ann c t e →
      HeadRegimeAt env φ s.2.1

/-- `HeadRegimeAt`, decided at a profile `prof` of the enclosing constant's parameters `lps`: each
datum, substituted at the head's levels (`Level.substPW`), read at the profile (`pwAt`). -/
def headRegimeB (tab : KTab) (lps : List Nat) (prof : IxCC.Src.Profile) (f : KExpr) : Bool :=
  match f.getAppFn with
  | .const k us =>
    match tab[k]? with
    | some ci =>
      us.length == ci.toConstantVal.levelParams.length &&
      (List.range (f.getAppArgs.length + 1)).all fun j =>
        match nthMeta j ci.toConstantVal.type with
        | some m =>
          pwAt lps prof (Level.substPW ci.toConstantVal.levelParams us m.pw) == some false
        | none => false
    | none => false
  | _ => false

/-- `headRegimeResB` at one constant, its level parameters `lps` computed once (read once per
datum, an `lpsOf` that searches the reading costs the reading's length per check). -/
def headRegimeResB1 (tab : KTab) (lps : List Nat) (p : Program) (env : KEnv) (κ : CId → KKey)
    (lpsOf : CId → List Nat) (ann : IxCC.Src.Relevance.Ann) (c : CId) : Bool :=
  (runPairsB p env κ c).all fun x =>
    (runRefusedT tab p lpsOf ann c x.1 x.2).all fun s =>
      (profiles (lvlsOf p c)).all fun prof => headRegimeB tab lps prof s.2.1

/-- **`HeadRegimeRes`, decided**: at every site the direct route refuses in a run pair of `Sl`, at
every profile of the constant's level parameters. -/
def headRegimeResB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  let tab := KTab.of env
  Sl.all fun c => headRegimeResB1 tab (lpsOf c) p env κ lpsOf ann c

theorem headRegimeAt_of_check {env : KEnv} {φ : LevelParam → Nat} {lps : List Nat}
    {prof : IxCC.Src.Profile} (hφ : ProfAt φ lps prof) {f : KExpr}
    (h : headRegimeB (KTab.of env) lps prof f = true) : HeadRegimeAt env φ f := by
  unfold headRegimeB at h
  split at h
  · rename_i k us hfn
    rw [KTab.get_of] at h
    split at h
    · rename_i ci hci
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
      refine ⟨k, us, ci, hfn, hci, h.1, fun j hj => ?_⟩
      have h2 := h.2 j (by omega)
      split at h2
      · rename_i m hm
        refine ⟨m, hm, ?_⟩
        rw [← holds_substPW]
        exact holds_of_pwAt hφ (beq_iff_eq.mp h2)
      · cases h2
    · cases h
  · cases h

/-- **`headRegimeResB` is sound** (with the check, which puts each run pair among those the
decision enumerates and gives the level count). -/
theorem headRegimeRes_of_check {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (h : headRegimeResB p env κ lpsOf ann Sl = true) :
    HeadRegimeRes p env κ lpsOf ann (· ∈ Sl) := by
  intro c ls t e hS hOk hrp φ hlv s _ hres
  have hpair := runPair_mem_of_check hchk hS hrp
  have hG := groundFacts_of_check hchk
  have hlen : ls.length = (lpsOf c).length := hOk.1.trans (hG.faith.lvls c hS)
  have hprof : IxCC.Src.profileOf ls ∈ profiles (lvlsOf p c) :=
    mem_profiles _ _ (by simp [IxCC.Src.profileOf, hOk.1])
  simp only [headRegimeResB, headRegimeResB1, List.all_eq_true] at h
  exact headRegimeAt_of_check (profAt_of_lvAt hlv hlen)
    (h c hS (t, e) hpair s hres _ hprof)

/-! ## The walk -/

section Walk

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- `GradedBy` passes to a copy with no binder between (a live `let`'s value's sites are read at
its copy, `SubAt0`). -/
theorem gradedBy_of_subAt0 {D : (BVarIdx → V) → KExpr → V → Prop} {ρ : BVarIdx → V} {v : KExpr} :
    ∀ {e : KExpr}, SubAt0 v e → GradedBy D ρ e → GradedBy D ρ v
  | _, .refl, h => h
  | _, .appL hs, h => gradedBy_of_subAt0 hs (by simp only [GradedBy] at h; exact h.1)
  | _, .appR hs, h => gradedBy_of_subAt0 hs (by simp only [GradedBy] at h; exact h.2.1)
  | _, .proj hs, h => gradedBy_of_subAt0 hs (by simpa only [GradedBy] using h)

/-- **A graded reading reaches every evaluated site** (no law): below a term whose reading is
graded in every environment satisfying `Γ`, the application node of every site `evalSites` lists is
graded in every environment satisfying the site's context (`GradedBy`'s λ clause is `CtxSat`'s cons
case). -/
theorem graded_sites (M : Model V env) {φ : LevelParam → Nat} {ls : Levels} :
    ∀ (t : Term) (Γ : List KExpr) (e : KExpr),
      (∀ ρ, CtxSat M φ Γ ρ → GradedBy (Denotes M.cval env φ) ρ e) →
      ∀ s ∈ evalSites ls Γ t e, ∀ ρ, CtxSat M φ s.1 ρ →
        GradedBy (Denotes M.cval env φ) ρ (.app s.2.1 s.2.2) := by
  intro t
  induction t with
  | app f a md r ihf iha =>
    intro Γ e hg s hs
    cases e with
    | app f' a' =>
      simp only [evalSites, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · exact hg
      · exact ihf Γ f' (fun ρ hρ => by
          have h1 := hg ρ hρ
          simp only [GradedBy] at h1
          exact h1.1) s hs
      · by_cases hirr : r.irrAt ls = true
        · simp [hirr] at hs
        · simp [hirr] at hs
          exact iha Γ a' (fun ρ hρ => by
            have h1 := hg ρ hρ
            simp only [GradedBy] at h1
            exact h1.2.1) s hs
    | _ => simp [evalSites] at hs
  | lam b d body ihd ihb =>
    intro Γ e hg s hs
    cases e with
    | lam d' body' mb =>
      simp only [evalSites] at hs
      refine ihb (d' :: Γ) body' (fun ρ hρ => ?_) s hs
      cases hρ with
      | cons hΓ hX hmem =>
        have h1 := hg _ hΓ
        simp only [GradedBy] at h1
        have h2 := h1.2 _ hX _ hmem
        have hpush : push (ρ 0) (fun i => ρ (i + 1)) = ρ := by funext i; cases i <;> rfl
        rwa [hpush] at h2
    | _ => simp [evalSites] at hs
  | proj s0 i e0 ih =>
    intro Γ e hg s hs
    cases e with
    | proj _ _ e' =>
      simp only [evalSites] at hs
      exact ih Γ e' (fun ρ hρ => by
        have h1 := hg ρ hρ
        simp only [GradedBy] at h1
        exact h1) s hs
    | _ => simp [evalSites] at hs
  | letE c r ty v b _ ihv ihb =>
    intro Γ e hg s hs
    simp only [evalSites, List.mem_append] at hs
    rcases hs with hs | hs
    · cases hz : zcopy b e with
      | none => simp [hz] at hs
      | some v' =>
        simp only [hz] at hs
        cases hsub : subAt0B v' e
        · simp [hsub] at hs
        · simp only [hsub, Bool.not_true, Bool.or_false] at hs
          split at hs
          · simp at hs
          · exact ihv Γ v' (fun ρ hρ => gradedBy_of_subAt0 (subAt0_of_check hsub) (hg ρ hρ)) s hs
    · exact ihb Γ e hg s hs
  | _ => intro Γ e _ s hs; cases e <;> simp [evalSites] at hs

/-- `GradedBy` of a `∀`-telescope gives `GradedBy` of the `λ`-telescope over the same domains (the
two clauses have one form; binder data are not read), given the step at the bodies. -/
theorem graded_lam_of_pi {D : (BVarIdx → V) → KExpr → V → Prop} {X Y : KExpr}
    (hXY : ∀ ρ, GradedBy D ρ X → GradedBy D ρ Y) :
    ∀ (bs : List (KExpr × BinderMeta)) (ms : List BinderMeta) (ρ : BVarIdx → V),
      bs.length = ms.length → GradedBy D ρ (piTele bs X) →
      GradedBy D ρ (lamTele (bs.zipWith (fun b m => (b.1, m)) ms) Y)
  | [], [], ρ, _, h => hXY ρ h
  | (A, m) :: bs, m' :: ms, ρ, hl, h => by
    simp only [piTele, GradedBy] at h
    simp only [List.zipWith_cons_cons, lamTele, GradedBy]
    exact ⟨h.1, fun A' hA x hx => graded_lam_of_pi hXY bs ms _ (by simpa using hl) (h.2 A' hA x hx)⟩
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- **Every run term's kernel term is graded**, under `graded`: a definition's stored value (the
law's second conjunct); an `eqn` body `λ Ds. rhs` (the stored theorem's type `∀ Ds, @Eq T lhs rhs`
is graded, and so its right-hand side under the same binders). -/
theorem runPair_graded (M : Model V env) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {c : CId} {t : Term} {e : KExpr} (hrp : RunPair p env κ c t e)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) : GradedBy (Denotes M.cval env φ) ρ e := by
  cases hrp with
  | value _ _ hf => exact (hgr _ (find_mem hf) φ ρ).2 _ _ _ rfl
  | @eqn thm body d _ hsh =>
    obtain ⟨-, ciF, cvT, pf, -, hfT, hlen, -, hty, -⟩ := hsh
    have h1 := (hgr _ (find_mem hfT) φ ρ).1
    simp only [ConstantInfo.toConstantVal] at h1
    rw [hty] at h1
    exact graded_lam_of_pi (fun ρ' h => by
      simp only [Expr.mkAppN, GradedBy] at h
      exact h.2.1) d.Ds d.ms ρ hlen h1

theorem exists_snoc {α : Type _} : ∀ (l : List α), l ≠ [] → ∃ xs x, l = xs ++ [x]
  | [], h => absurd rfl h
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: l, _ => by
    obtain ⟨xs, z, h⟩ := exists_snoc (y :: l) (by simp)
    exact ⟨x :: xs, z, by rw [h]; rfl⟩

/-- **Along a spine over a stored constant, the function lies in the product its stored type gives**
at the head's assignment, while the type's binders up to there are not propositions (`graded` at each
node puts the argument in the type's domain). -/
theorem spine_mem (M : Model V env) {φ : LevelParam → Nat} {ρ : BVarIdx → V} {k : KKey}
    {us : List Level} {ci : ConstantInfo .anon} (hci : env.find? k = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    ∀ (args : List KExpr) (F : V), Denotes M.cval env φ ρ (Expr.mkAppN (.const k us) args) F →
      GradedBy (Denotes M.cval env φ) ρ (Expr.mkAppN (.const k us) args) →
      (∀ j < args.length, ∃ m, nthMeta j ci.toConstantVal.type = some m ∧
        m.pw.holds (Level.substFn φ ci.toConstantVal.levelParams us) = false) →
      ∃ (σ : BVarIdx → V) (TT : V),
        Denotes M.cval env (Level.substFn φ ci.toConstantVal.levelParams us) σ
          (piBody args.length ci.toConstantVal.type) TT ∧ F ∈ˢ TT := by
  intro args
  generalize hn : args.length = n
  induction n generalizing args with
  | zero =>
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    intro F hF _ _
    have h0 : Denotes M.cval env φ ρ (.const k us)
        (M.cval k (Level.substFn φ ci.toConstantVal.levelParams us)) := Denotes.const hci hlen
    have hFe : F = M.cval k (Level.substFn φ ci.toConstantVal.levelParams us) :=
      Denotes_functional hF h0
    obtain ⟨T, hT, hm⟩ := mem_key M hci (Level.substFn φ ci.toConstantVal.levelParams us) ρ
    exact ⟨ρ, T, hT, hFe ▸ hm⟩
  | succ n ih =>
    have hne : args ≠ [] := by rintro rfl; simp at hn
    obtain ⟨xs, x, rfl⟩ := exists_snoc args hne
    have hxs : xs.length = n := by simpa using hn

    intro F hF hgr hH
    rw [mkAppN_append] at hF hgr
    obtain ⟨F', X, hF', hX, rfl⟩ := den_app.mp hF
    simp only [GradedBy] at hgr
    obtain ⟨hgf, -, r, A, F'', X', B, hF'', hX', hmem, hXA, -⟩ := hgr
    rw [Denotes_functional hF'' hF'] at hmem
    rw [Denotes_functional hX' hX] at hXA
    obtain ⟨σ, TT, hTT, hFT⟩ := ih xs hxs F' hF' hgf (fun j hj => hH j (by omega))
    obtain ⟨m, hm, hpw⟩ := hH n (by omega)
    obtain ⟨d, b, hpb⟩ := piBody_of_nthMeta _ _ hm
    rw [hpb] at hTT
    obtain ⟨Ad, Bf, -, hBf, -, rfl⟩ := den_pi.mp hTT
    have hv : regime (Level.substFn φ ci.toConstantVal.levelParams us) m.pw ≠ 0 := by
      simp [regime, hpw]
    have hr : r ≠ 0 := by
      rintro rfl
      exact not_pt_mem_piR_pos hv (eq_pt_of_mem_piR_zero hmem ▸ hFT)
    have hA : A = Ad := piR_dom_unique hr hv hmem hFT
    rw [hA] at hXA
    refine ⟨push X σ, Bf X, ?_, app_mem_piR_pos hv hFT hXA⟩
    rw [piBody_succ _ _ _ _ _ hpb]
    exact hBf X hXA

/-- **The head's regime puts the function in a positive-regime product.** -/
theorem head_pos (M : Model V env) {φ : LevelParam → Nat} {ρ : BVarIdx → V} {f : KExpr} {F : V}
    (hH : HeadRegimeAt env φ f) (hF : Denotes M.cval env φ ρ f F)
    (hg : GradedBy (Denotes M.cval env φ) ρ f) :
    ∃ (v : Nat) (A : V) (B : V → V), v ≠ 0 ∧ F ∈ˢ piR v A B := by
  obtain ⟨k, us, ci, hfn, hci, hlen, hall⟩ := hH
  have he : Expr.mkAppN (.const k us) f.getAppArgs = f := by rw [← hfn]; exact mkAppN_getApp f
  rw [← he] at hF hg
  obtain ⟨σ, TT, hTT, hFT⟩ := spine_mem M hci hlen f.getAppArgs F hF hg
    (fun j hj => hall j (Nat.le_of_lt hj))
  obtain ⟨m, hm, hpw⟩ := hall f.getAppArgs.length (Nat.le_refl _)
  obtain ⟨d, b, hpb⟩ := piBody_of_nthMeta _ _ hm
  rw [hpb] at hTT
  obtain ⟨Ad, Bf, -, -, -, rfl⟩ := den_pi.mp hTT
  exact ⟨_, Ad, Bf, by simp [regime, hpw], hFT⟩

/-- **The residue from `graded`**: `SitesOkRes` from `graded` and the head's regime at the refused
sites (laws: `graded`, and `Model.mem` for the head). -/
theorem sitesOkRes_of_graded {M : Model V env} (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    (hH : HeadRegimeRes p env κ lpsOf ann S) : SitesOkRes M p κ lpsOf ann S := by
  intro c ls t e hS hOk hrp φ hlv s hs hres ρ hρ
  have hg := graded_sites M t [] e (fun ρ' _ => runPair_graded M hgr hrp φ ρ') s hs ρ hρ
  simp only [GradedBy] at hg
  obtain ⟨hgf, -, r, A, F, X, B, hF, hX, hmem, hXA, -⟩ := hg
  obtain ⟨v, A', B', hv, hFv⟩ := head_pos M (hH c ls t e hS hOk hrp φ hlv s hs hres) hF hgf
  have hr : r ≠ 0 := by
    rintro rfl
    exact not_pt_mem_piR_pos hv (eq_pt_of_mem_piR_zero hmem ▸ hFv)
  exact ⟨F, X, r, A, B, hF, hX, hr, hmem, hXA⟩

end Walk

/-! ## The root theorem with no typing hypothesis -/

section Root

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **`rootSound_678A` with no typing hypothesis**: `SitesOkRes` replaced by #678's `graded` field
(`GradedLaw`, a sixth field beside `Laws678`) and the head's regime at the refused sites
(`HeadRegimeRes`). Its conclusion is `rootSound_678A`'s, hence `rootSound_678`'s, word for word. -/
theorem rootSound_678G (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hH : HeadRegimeRes p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678A hL hG hC hNC hLD hI hU hroot hR (sitesOkRes_of_graded hgr hH) hA hrun hrb hRT
    hO φ ρ X hX

/-- **The same from the Boolean checks**: `groundCheck`, `noCanonAB`, `litDefsB`, `instCheckB` with
the root as its seed, `headRegimeResB`, and the root's facts; no typing hypothesis. -/
theorem rootSound_678G_of_check (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hhr : headRegimeResB p env κ lpsOf ann Sl = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678A_of_check hL hchk hnc hld hinst hR
    (sitesOkRes_of_graded hgr (headRegimeRes_of_check hchk hhr)) hA hrun hrb hRT hO φ ρ X hX

end Root

end IxCC.Grounding
