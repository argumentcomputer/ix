import IxCCGrounding.Eqn
import IxCCGrounding.Hyps
import IxCCGrounding.Ok

/-!
# The run terms run (`IxCCGrounding.Runs`)

**The typing hypothesis here is `SitesOk`**: at every instance `Ok` admits of every constant of
`S` that SrcEval unfolds (by δ, or by its `eqn` entry), every application site SrcEval may
evaluate in the run term (`evalSites`) is in the graph regime with its argument in the domain.
The root theorems assume less: typing only at the sites the direct route refuses (`SitesOkRes`),
from which `sitesOk_of_res` (`IxCCGrounding.Direct.Sites`) derives `SitesOk`.

Everything else the fundamental lemma asks of a run term (`Runs`) is derived here
(`runs_of_sites`):

* the correspondence with the stored kernel term (its ζ-reduct: a `let`'s variable stands for its
  value's copy, `TermCorrS` at `σ = []`) is checked (`GroundFacts.values`, `GroundFacts.eqns`);
  a live `let`'s copy occurs with no binder between, so it denotes wherever the stored term does
  (`denotesIn_of_subAt0`);
* `Ok` at every constant node SrcEval may unfold is `Ok`'s closure, checked
  (`GroundFacts.okClosed`);
* every position SrcEval skips (an irrelevant argument, a type, a λ, a constant) denotes: the
  whole stored value denotes by δ (`Laws.defn_value`), an equation body by the `eqn` lemma, and
  a subterm of a term that denotes in every environment satisfying its context denotes in every
  environment satisfying its own (`denotesIn_*`).

So the fundamental lemma's hypotheses follow from the laws, the checked facts, `SitesOk` and
F5's meaning at each `case` constant (`fundHyps_of`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **The typing hypothesis**: at every `Ok` instance of every constant of `S` SrcEval unfolds,
every application site it may evaluate in the run term is `SiteOk`. -/
def SitesOk (M : Model V env) (p : Program) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  ∀ c ls t e, S c → Ok p ann c ls → RunPair p env κ c t e →
    ∀ φ, LvAt φ (lpsOf c) ls → ∀ s ∈ evalSites ls [] t e, SiteOk M φ s.1 s.2.1 s.2.2

variable {M : Model V env}

/-! ## Subterms of a term that denotes -/

theorem denotesIn_app_left {φ : LevelParam → Nat} {Γ : List KExpr} {f a : KExpr}
    (h : DenotesIn M φ Γ (.app f a)) : DenotesIn M φ Γ f := fun ρ hρ => by
  obtain ⟨X, hX⟩ := h ρ hρ
  obtain ⟨F, _, hF, _, _⟩ := den_app.mp hX
  exact ⟨F, hF⟩

theorem denotesIn_app_right {φ : LevelParam → Nat} {Γ : List KExpr} {f a : KExpr}
    (h : DenotesIn M φ Γ (.app f a)) : DenotesIn M φ Γ a := fun ρ hρ => by
  obtain ⟨X, hX⟩ := h ρ hρ
  obtain ⟨_, A, _, hA, _⟩ := den_app.mp hX
  exact ⟨A, hA⟩

theorem denotesIn_proj {φ : LevelParam → Nat} {Γ : List KExpr} {s : KKey} {i : Nat} {e : KExpr}
    (h : DenotesIn M φ Γ (.proj s i e)) : DenotesIn M φ Γ e := fun ρ hρ => by
  obtain ⟨X, hX⟩ := h ρ hρ
  cases hX with
  | proj_table _ he => exact ⟨_, he⟩
  | proj_fst _ he => exact ⟨_, he⟩
  | proj_snd _ he => exact ⟨_, he⟩

omit [Ix.Kernel.SetTheory V] in
theorem push_head_tail (ρ : BVarIdx → V) : push (ρ 0) (fun i => ρ (i + 1)) = ρ := by
  funext i; cases i <;> rfl

theorem denotesIn_lam_body {φ : LevelParam → Nat} {Γ : List KExpr} {d b : KExpr} {m : BinderMeta}
    (h : DenotesIn M φ Γ (.lam d b m)) : DenotesIn M φ (d :: Γ) b := fun ρ hρ => by
  cases hρ with
  | cons hΓ hA hx =>
    obtain ⟨L, hL⟩ := h _ hΓ
    obtain ⟨Ad, F, hAd, hF, _, _⟩ := den_lam.mp hL
    obtain rfl := Denotes_functional hA hAd
    have hb := hF _ hx
    rw [push_head_tail] at hb
    exact ⟨_, hb⟩

/-- **A copy with no binder between denotes** wherever the term holding it does. -/
theorem denotesIn_of_subAt0 {φ : LevelParam → Nat} {Γ : List KExpr} {v : KExpr} :
    ∀ {e : KExpr}, SubAt0 v e → DenotesIn M φ Γ e → DenotesIn M φ Γ v := by
  intro e h hd
  induction h with
  | refl => exact hd
  | appL _ ih => exact ih (denotesIn_app_left hd)
  | appR _ ih => exact ih (denotesIn_app_right hd)
  | proj _ ih => exact ih (denotesIn_proj hd)

/-! ## The construction of `Runs` -/

/-- **A corresponding term that denotes runs**, at every site `SiteOk`, every constant node `Ok'`:
no closedness premise (the substitution gives every variable its kernel term); at a live `let` the
copy denotes because it occurs with no binder between (`denotesIn_of_subAt0`), and the value's
sites and constants are among the walks' (`evalSites`, `evalConsts`). -/
theorem runs_of_corr {κ : CId → KKey} {lps : List Nat} {ls : Levels} {φ : LevelParam → Nat}
    {Ok' : CId → Levels → Prop} {σ : Sig} {t : Term} {e : KExpr} (hc : TermCorrS κ lps σ t e) :
    ∀ {Γ : List KExpr}, DenotesIn M φ Γ e →
      (∀ s ∈ evalSites ls Γ t e, SiteOk M φ s.1 s.2.1 s.2.2) →
      (∀ d us, (d, us) ∈ evalConsts ls t → Ok' d (us.map (IxCC.Src.evalUniv ls))) →
      Runs M κ Ok' lps ls φ σ Γ t e := by
  induction hc with
  | var h => intro Γ _ _ _; exact .var h
  | sort hu => intro Γ _ _ _; exact .sort hu
  | const hlen hu =>
    intro Γ hd _ hok
    exact .const (.const hlen hu) (hok _ _ (by simp [evalConsts])) hd
  | @app σ f a m r f' a' hf ha ihf iha =>
    intro Γ hd hs hok
    refine .app (ihf (denotesIn_app_left hd) (fun s h => hs s ?_) (fun d us h => hok d us ?_))
      (fun hr => iha (denotesIn_app_right hd) (fun s h => hs s ?_) (fun d us h => hok d us ?_))
      (fun _ => ⟨ha, denotesIn_app_right hd⟩) (hs (Γ, f', a') ?_)
    · simp [evalSites, h]
    · simp [evalConsts, h]
    · simp [evalSites, hr, h]
    · simp [evalConsts, hr, h]
    · simp [evalSites]
  | @lam σ b d body d' body' mb hd' _ _ ihb =>
    intro Γ hd hs hok
    exact .lam hd' (ihb (denotesIn_lam_body hd)
      (fun s h => hs s (by simpa [evalSites] using h))
      (fun d us h => hok d us (by simpa [evalConsts] using h))) hd
  | pi hd' hc' => intro Γ hd _ _; exact .pi (.pi hd' hc') hd
  | @proj σ s i e e' _ ih =>
    intro Γ hd hs hok
    exact .proj (ih (denotesIn_proj hd)
      (fun s h => hs s (by simpa [evalSites] using h))
      (fun d us h => hok d us (by simpa [evalConsts] using h))) hd
  | natLit => intro Γ hd _ _; exact .natLit hd
  | @letLive σ c r ty v b e v' hz hsub hv _ ihv ihb =>
    intro Γ hd hs hok
    have hdv : DenotesIn M φ Γ v' := denotesIn_of_subAt0 (subAt0_of_check hsub) hd
    have hrb := ihb hd (fun s h => hs s (by simp [evalSites, h]))
      (fun d us h => hok d us (by simp [evalConsts, h]))
    cases hr : r.irrAt ls with
    | false =>
      refine .letRel hr hz (ihv hdv (fun s h => hs s ?_) (fun d us h => hok d us ?_)) hrb
      · simp [evalSites, hz, hr, hsub, h]
      · simp [evalConsts, hr, h]
    | true => exact .letIrr hr hz hv hdv hrb
  | letDead hz _ ihb =>
    intro Γ hd hs hok
    exact .letDead hz (ihb hd (fun s h => hs s (by simp [evalSites, hz, h]))
      (fun d us h => hok d us (by simp [evalConsts, h])))

/-- **The run terms run**: every constant of `S` SrcEval unfolds, at every `Ok` instance, runs
its value (or its equation body), from the laws, the checked facts and `SitesOk`. -/
theorem runs_of_sites (hL : LawsCore M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} (hG : GroundFacts p env κ lpsOf ann S)
    (hT : SitesOk M p κ lpsOf ann S) {c : CId} {ls : Levels} {t : Term} {e : KExpr} (hS : S c)
    (hOk : Ok p ann c ls) (hrp : RunPair p env κ c t e) {φ : LevelParam → Nat}
    (hlv : LvAt φ (lpsOf c) ls) : Runs M κ (Ok p ann) (lpsOf c) ls φ [] [] t e := by
  have hcorr : TermCorrS κ (lpsOf c) [] t e := by
    cases hrp with
    | value hr hd hf => exact hG.values c _ _ _ _ _ _ hS hr hd hf
    | eqn hr hsh => exact (hG.eqns c _ _ hS hr).2 _ hsh
  have hden : DenotesIn M φ [] e := by
    intro ρ _
    cases hrp with
    | value _ _ hf => exact ⟨_, hL.defn_value _ _ _ (find_mem hf) φ ρ⟩
    | eqn _ hsh => exact ⟨_, eqn_den M hsh φ ρ⟩
  have hterm : t ∈ runTerms p c := by
    cases hrp with
    | value hr hd _ => simp [runTerms, hr, hd]
    | eqn hr _ => simp [runTerms, hr]
  exact runs_of_corr hcorr hden (hT c ls t e hS hOk hrp φ hlv)
    (fun d us h => hG.okClosed c ls hS hOk t hterm d us h)

/-- **The fundamental lemma's hypotheses, from the laws other than canonicity**, the recursors'
canonicity (the law, or no constructor with level parameters), the checked facts, `SitesOk` and F5's
meaning at each `case` constant. -/
theorem fundHyps_of_core (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    (hcanon : CtorCanon M ∨ ∀ r, S r →
      (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
        RecNoLevels env (κ r))
    (hG : GroundFacts p env κ lpsOf ann S) (hT : SitesOk M p κ lpsOf ann S)
    (hcases : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r = some .ordinary → CaseFires M p κ lpsOf S (Ok p ann) c) :
    FundHyps M p κ lpsOf S (Ok p ann) where
  laws := hL
  canon := hcanon
  natBasis := hG.natBasis
  faith := hG.faith
  cases := hcases
  eqn := fun c thm body hS hr => by
    obtain ⟨⟨d, hsh⟩, _⟩ := hG.eqns c thm body hS hr
    exact ⟨d.body, fun φ ρ X hX => Denotes_functional (eqn_den M hsh φ ρ) hX,
      fun ls φ hOk hlv => runs_of_sites hL hG hT hS hOk (.eqn hr hsh) hlv⟩
  value := fun c ls _ _ _ _ _ _ hS hOk hr hd hf φ hlv =>
    runs_of_sites hL hG hT hS hOk (.value hr hd hf) hlv

/-- **The fundamental lemma's hypotheses**, from the laws, the checked facts, `SitesOk` and F5's
meaning at each `case` constant (canonicity from the laws). -/
theorem fundHyps_of (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop} (hG : GroundFacts p env κ lpsOf ann S)
    (hT : SitesOk M p κ lpsOf ann S)
    (hcases : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r = some .ordinary → CaseFires M p κ lpsOf S (Ok p ann) c) :
    FundHyps M p κ lpsOf S (Ok p ann) :=
  fundHyps_of_core (lawsCore_of_laws hL) (.inl hL.ctor_canon) hG hT hcases

end Sem

end IxCC.Grounding
