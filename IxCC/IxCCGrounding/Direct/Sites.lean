import IxCCGrounding.Direct.Sound
import IxCCGrounding.Runs
import IxCCGrounding.Check

/-!
# What `SitesOk` becomes (`IxCCGrounding.Direct.Sites`)

**Part G.** The walk's accepted sites are typed (`spine_sound`, `termRefused_sound`); the typing
hypothesis is needed only at the sites the check refuses (`SitesOkRes`, which `SitesOk` implies);
where the check refuses none (`DirectFacts`, decided by `sitesDirectB`), it holds outright.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **The sites of a spine the walk accepts are `SiteOk`**, when the spine denotes. -/
theorem spine_sound (hL : Laws M) (hN : NatBasis env) {x : DCtx} (hx : x.Reads env)
    {φ : LevelParam → Nat} (hφ : AtProf φ x) {n : Nat} {Γ : List KExpr} {h : KExpr}
    {args : List KExpr} (hD : DenotesIn M φ Γ (Expr.mkAppN h args)) :
    ∀ s ∈ (spineSites Γ h args).take (spineAccepted x n Γ h args),
      SiteOk M φ s.1 s.2.1 s.2.2 := by
  have DS := direct_sound hL hN hx hφ n
  have hstep : ∀ T a T', dStep x n true Γ T a = some T' → ∀ F, HasTy M φ Γ F T →
      HasTy M φ Γ (.app F a) T' ∧ (DenotesIn M φ Γ (.app F a) → SiteOk M φ Γ F a) :=
    fun T a T' hs F hF => ⟨(step_of hφ DS true Γ T a T' hs F hF).1,
      (step_of hφ DS true Γ T a T' hs F hF).2 rfl⟩
  cases args with
  | nil => intro s hs; simp [spineSites] at hs
  | cons a1 rest =>
    intro s hs
    cases h with
    | lam D b m =>
      simp only [spineAccepted] at hs
      split at hs
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        have hchk := DS.check Γ a1 D hc.2
        have hreg := regime_of_pwFalse hφ hc.1
        have hD1 : DenotesIn M φ Γ (.app (.lam D b m) a1) := denotesIn_mkAppN_head rest hD
        have hsite1 := siteOk_of_lam hchk hreg hD1
        cases rest with
        | nil =>
          simp only [spineSites, List.take_succ_cons, List.take_zero, List.mem_singleton] at hs
          subst hs
          exact hsite1
        | cons a2 rest' =>
          simp only at hs
          split at hs
          · rename_i T hT
            simp only [spineSites, List.take_succ_cons, List.mem_cons] at hs
            rcases hs with rfl | hs
            · exact hsite1
            · have hT1 : HasTy M φ Γ (.app (.lam D b m) a1) T :=
                hasTy_of_reduct (DS.infer Γ _ T hT) (reduces_beta [] hchk)
              exact walkCount_sites hstep (a2 :: rest') _ T hT1 hD s hs
          · simp only [spineSites, List.take_succ_cons, List.take_zero, List.mem_singleton] at hs
            subst hs
            exact hsite1
      · simp at hs
    | _ =>
      simp only [spineAccepted] at hs
      split at hs
      · rename_i T hT
        exact walkCount_sites hstep (a1 :: rest) _ T (DS.infer Γ _ T hT) hD s hs
      · simp at hs

/-- A site the spine walk does not refuse is typed. -/
theorem spineRefused_sound (hL : Laws M) (hN : NatBasis env) {x : DCtx} (hx : x.Reads env)
    {φ : LevelParam → Nat} (hφ : AtProf φ x) {n : Nat} {Γ : List KExpr} {h : KExpr}
    {args : List KExpr} (hD : DenotesIn M φ Γ (Expr.mkAppN h args)) :
    ∀ s ∈ spineSites Γ h args, s ∉ spineRefused x n Γ h args → SiteOk M φ s.1 s.2.1 s.2.2 := by
  intro s hs hn
  have hs' := hs
  rw [← List.take_append_drop (spineAccepted x n Γ h args) (spineSites Γ h args)] at hs'
  rcases List.mem_append.mp hs' with h1 | h2
  · exact spine_sound hL hN hx hφ hD s h1
  · exact absurd h2 hn

/-- **A site of a run term the walk does not refuse is `SiteOk`**: at a level instantiation whose
profile is in the walk's set, every site `evalSites` lists, and every pending site of the
enclosing applications (`spineSites Γ e acc`), is refused or typed. -/
theorem termRefused_sound (hL : Laws M) (hN : NatBasis env) {tab : KTab}
    (htab : ∀ k, tab[k]? = env.find? k) {lps : List Nat} {n : Nat}
    {ls : Levels} {φ : LevelParam → Nat} (hφ : ProfAt φ lps (IxCC.Src.profileOf ls)) :
    ∀ (t : Term) (P : List IxCC.Src.Profile) (Γ : List KExpr) (e : KExpr) (acc : List KExpr),
      IxCC.Src.profileOf ls ∈ P → DenotesIn M φ Γ (Expr.mkAppN e acc) →
      ∀ s, (s ∈ evalSites ls Γ t e ∨ s ∈ spineSites Γ e acc) →
        s ∉ termRefused tab lps n P Γ t e acc → SiteOk M φ s.1 s.2.1 s.2.2 := by
  have spine : ∀ (P : List IxCC.Src.Profile) (Γ : List KExpr) (h : KExpr) (acc : List KExpr),
      IxCC.Src.profileOf ls ∈ P → DenotesIn M φ Γ (Expr.mkAppN h acc) →
      ∀ s ∈ spineSites Γ h acc, s ∉ spineRefused { tab, lps, profs := P } n Γ h acc →
        SiteOk M φ s.1 s.2.1 s.2.2 :=
    fun P Γ h acc hP hD =>
      spineRefused_sound (x := { tab, lps, profs := P }) hL hN htab ⟨_, hP, hφ⟩ hD
  intro t
  induction t with
  | app f a mo r ihf iha =>
    intro P Γ e acc hP hD s hs hn
    cases e with
    | app f' a' =>
      simp only [termRefused, List.mem_append, not_or] at hn
      obtain ⟨hna, hnf⟩ := hn
      have hDf : DenotesIn M φ Γ (Expr.mkAppN f' (a' :: acc)) := hD
      rcases hs with hs | hs
      · simp only [evalSites, List.mem_cons, List.mem_append] at hs
        rcases hs with rfl | hs | hs
        · exact ihf P Γ f' (a' :: acc) hP hDf _ (Or.inr (by simp [spineSites])) hnf
        · exact ihf P Γ f' (a' :: acc) hP hDf s (Or.inl hs) hnf
        · split at hs
          · simp at hs
          · rename_i hr
            have hP' : IxCC.Src.profileOf ls ∈ P.filter (fun prof => !r.irrP prof) := by
              rw [irrAt_profile] at hr
              simp [hP, hr]
            have hne : (P.filter (fun prof => !r.irrP prof)).isEmpty = false := by
              cases hq : P.filter (fun prof => !r.irrP prof) with
              | nil => rw [hq] at hP'; simp at hP'
              | cons _ _ => rfl
            simp only [hne, Bool.false_eq_true, ↓reduceIte] at hna
            have hDa : DenotesIn M φ Γ (Expr.mkAppN a' []) :=
              denotesIn_app_right (denotesIn_mkAppN_head acc hD)
            exact iha _ Γ a' [] hP' hDa s (Or.inl hs) hna
      · exact ihf P Γ f' (a' :: acc) hP hDf s
          (Or.inr (by simp only [spineSites, List.mem_cons]; exact Or.inr hs)) hnf
    | _ =>
      simp only [termRefused] at hn
      rcases hs with hs | hs
      · simp [evalSites] at hs
      · exact spine P Γ _ acc hP hD s hs hn
  | lam bi d body ihd ihb =>
    intro P Γ e acc hP hD s hs hn
    cases e with
    | lam d' body' m =>
      simp only [termRefused, List.mem_append, not_or] at hn
      rcases hs with hs | hs
      · simp only [evalSites] at hs
        have hDb : DenotesIn M φ (d' :: Γ) (Expr.mkAppN body' []) :=
          denotesIn_lam_body (denotesIn_mkAppN_head acc hD)
        exact ihb P (d' :: Γ) body' [] hP hDb s (Or.inl hs) hn.2
      · exact spine P Γ _ acc hP hD s hs hn.1
    | _ =>
      simp only [termRefused] at hn
      rcases hs with hs | hs
      · simp [evalSites] at hs
      · exact spine P Γ _ acc hP hD s hs hn
  | proj sc i t iht =>
    intro P Γ e acc hP hD s hs hn
    cases e with
    | proj sk j e' =>
      simp only [termRefused, List.mem_append, not_or] at hn
      rcases hs with hs | hs
      · simp only [evalSites] at hs
        have hDe : DenotesIn M φ Γ (Expr.mkAppN e' []) :=
          denotesIn_proj (denotesIn_mkAppN_head acc hD)
        exact iht P Γ e' [] hP hDe s (Or.inl hs) hn.2
      · exact spine P Γ _ acc hP hD s hs hn.1
    | _ =>
      simp only [termRefused] at hn
      rcases hs with hs | hs
      · simp [evalSites] at hs
      · exact spine P Γ _ acc hP hD s hs hn
  | _ =>
    intro P Γ e acc hP hD s hs hn
    simp only [termRefused] at hn
    rcases hs with hs | hs
    · simp [evalSites] at hs
    · exact spine P Γ _ acc hP hD s hs hn

/-- Every site `evalSites` lists is among all the run term's application sites. -/
theorem evalSites_sub_allSites (ls : Levels) :
    ∀ (t : Term) (Γ : List KExpr) (e : KExpr), ∀ s ∈ evalSites ls Γ t e, s ∈ allSites Γ t e := by
  intro t
  induction t with
  | app f a _ r ihf iha =>
    intro Γ e s hs
    cases e with
    | app f' a' =>
      simp only [evalSites, allSites, List.mem_cons, List.mem_append] at hs ⊢
      rcases hs with rfl | hs | hs
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (ihf Γ f' s hs))
      · split at hs
        · simp at hs
        · exact Or.inr (Or.inr (iha Γ a' s hs))
    | _ => simp [evalSites] at hs
  | lam _ _ body _ ihb =>
    intro Γ e s hs
    cases e with
    | lam d' body' _ => simp only [evalSites, allSites] at hs ⊢; exact ihb _ _ s hs
    | _ => simp [evalSites] at hs
  | proj _ _ t iht =>
    intro Γ e s hs
    cases e with
    | proj _ _ e' => simp only [evalSites, allSites] at hs ⊢; exact iht _ _ s hs
    | _ => simp [evalSites] at hs
  | _ => intro Γ e s hs; simp [evalSites] at hs

/-- **A run pair is one the check enumerates**, on a closure the check passes. -/
theorem runPair_mem_of_check {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} (hchk : groundCheck p env κ lpsOf ann Sl = true)
    {c : CId} {t : Term} {e : KExpr} (hc : c ∈ Sl) (hrp : RunPair p env κ c t e) :
    (t, e) ∈ runPairsB p env κ c := by
  cases hrp with
  | value hr hd hf => simp [runPairsB, hr, hd, hf]
  | @eqn thm body d hr hsh =>
    have hE := eqBasis_of_check (part_of (name := "eqBasis") (b := eqBasisB env) hchk
      (by simp [checkParts, checkPartsWith]))
    have h1 := List.all_eq_true.mp (part_of (name := "eqnShape") (b := Sl.all (eqnShapeOkB p env κ))
      hchk (by simp [checkParts, checkPartsWith])) c hc
    simp only [eqnShapeOkB, hr] at h1
    split at h1
    · rename_i d' hd'
      have hb := eqnShape_body hsh (eqnShape_of_check hE h1)
      simp [runPairsB, hr, hd', hb]
    · cases h1

/-- **The residue hypothesis**: `SitesOk` at the sites the check refuses. -/
def SitesOkRes (M : Model V env) (p : Program) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  ∀ c ls t e, S c → Ok p ann c ls → RunPair p env κ c t e →
    ∀ φ, LvAt φ (lpsOf c) ls → ∀ s ∈ evalSites ls [] t e,
      s ∈ runRefused p env lpsOf ann c t e → SiteOk M φ s.1 s.2.1 s.2.2

/-- `SitesOk` implies the residue hypothesis: a theorem over `SitesOkRes` is stronger. -/
theorem sitesOkRes_of_sitesOk {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} (h : SitesOk M p κ lpsOf ann S) :
    SitesOkRes M p κ lpsOf ann S :=
  fun c ls t e hS hOk hrp φ hlv s hs _ => h c ls t e hS hOk hrp φ hlv s hs

/-- **The residue hypothesis gives `SitesOk`**: at a site the check does not refuse, the walk
typed it (`termRefused_sound`), the run term denoting by δ or the `eqn` lemma. -/
theorem sitesOk_of_res (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} (hG : GroundFacts p env κ lpsOf ann S)
    (hR : SitesOkRes M p κ lpsOf ann S) : SitesOk M p κ lpsOf ann S := by
  intro c ls t e hS hOk hrp φ hlv s hs
  by_cases hin : s ∈ runRefused p env lpsOf ann c t e
  · exact hR c ls t e hS hOk hrp φ hlv s hs hin
  · obtain ⟨hlen, r, hr, hirr⟩ := hOk
    have hφ : ProfAt φ (lpsOf c) (IxCC.Src.profileOf ls) :=
      profAt_of_lvAt hlv (by rw [hlen, hG.faith.lvls c hS])
    have hden : DenotesIn M φ [] e := by
      intro ρ _
      cases hrp with
      | value _ _ hf => exact ⟨_, hL.defn_value _ _ _ (find_mem hf) φ ρ⟩
      | eqn _ hsh => exact ⟨_, eqn_den M hsh φ ρ⟩
    have hP : IxCC.Src.profileOf ls ∈ okProfiles p ann c := by
      simp only [okProfiles, hr, List.mem_filter]
      refine ⟨mem_profiles _ _ (by rw [IxCC.Src.profileOf, List.length_map, hlen]), ?_⟩
      rw [← irrAt_profile, hirr]
      rfl
    unfold runRefused runRefusedT at hin
    split at hin
    · cases hPq : okProfiles p ann c with
      | nil => rw [hPq] at hP; simp at hP
      | cons q qs =>
        rw [hPq] at hin hP
        exact termRefused_sound hL hG.natBasis (KTab.get_of env) hφ t (q :: qs) [] e [] hP hden s
          (Or.inl hs) hin
    · exact absurd (evalSites_sub_allSites ls t [] e s hs) hin

/-- **The check refuses no site** (decided by `sitesDirectB`). -/
def DirectFacts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  ∀ c ls t e, S c → Ok p ann c ls → RunPair p env κ c t e →
    ∀ s ∈ evalSites ls [] t e, s ∉ runRefused p env lpsOf ann c t e

/-- **`sitesDirect` is sound.** -/
theorem directFacts_of_check {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (hD : sitesDirectB p env κ lpsOf ann Sl = true) : DirectFacts p env κ lpsOf ann (· ∈ Sl) := by
  intro c ls t e hc _ hrp s _ hin
  unfold runRefused at hin
  have hD' : Sl.all (fun c => (runPairsB p env κ c).all fun (t, e) =>
      (runRefusedT (KTab.of env) p lpsOf ann c t e).isEmpty) = true := hD
  have h1 := List.all_eq_true.mp hD' c hc
  have h2 := List.all_eq_true.mp h1 (t, e) (runPair_mem_of_check hchk hc hrp)
  simp only [List.isEmpty_iff] at h2
  rw [h2] at hin
  simp at hin

/-- Where the check refuses no site, the residue hypothesis holds outright. -/
theorem sitesOkRes_of_direct {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} (hD : DirectFacts p env κ lpsOf ann S) :
    SitesOkRes M p κ lpsOf ann S :=
  fun c ls t e hS hOk hrp _ _ s hs hr => absurd hr (hD c ls t e hS hOk hrp s hs)

end Sem

end IxCC.Grounding
