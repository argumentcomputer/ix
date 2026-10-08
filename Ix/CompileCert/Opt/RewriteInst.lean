import Ix.CompileCert.Opt.RewriteTotal

/-!
# Instantiated expansion conversion and rewrite lifting

`InstExpansionRel` compares raw and rewritten stored expansion values after every caller
universe substitution. It preserves arbitrary caller spines and the original rewrite theorem
conclusions without requiring every rule in the conversion environment to be level-closed.
The existing conditional `LevelClosed` theorems are unchanged.

`expansionOfP_instLookup_of_stored` isolates the remaining construction obligation: successful
rewrites of stored values must convert after each substitution. This is proof infrastructure,
not a new final compiler law. Deriving it from the original compiler/source domain still needs
referenced-spine arity, declaration universe scope, mapped hook/development conversion, and
the capture-avoidance and executable/core refinement work. No successful-construction predicate
is asserted to supply these facts.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)
open Ix.Compile.Pass (Expansion)

/-- The same expansion metadata and conversion at every caller universe argument, rather than
conversion of the two generic values alone. Caller spines are not restricted. -/
def InstExpansionRel (Γ : Env) (x' x : Expansion) : Prop :=
  x'.levelParams = x.levelParams ∧ x'.arity = x.arity ∧
    ∀ us, ExprConv Γ (substLevels x'.levelParams us x'.value)
      (substLevels x.levelParams us x.value)

theorem InstExpansionRel.refl (Γ : Env) (x : Expansion) : InstExpansionRel Γ x x :=
  ⟨rfl, rfl, fun _ => .refl _⟩

theorem InstExpansionRel.trans {Γ : Env} {x₂ x₁ x₀ : Expansion}
    (h₂₁ : InstExpansionRel Γ x₂ x₁) (h₁₀ : InstExpansionRel Γ x₁ x₀) :
    InstExpansionRel Γ x₂ x₀ :=
  ⟨h₂₁.1.trans h₁₀.1, h₂₁.2.1.trans h₁₀.2.1,
    fun us => .trans (h₂₁.2.2 us) (h₁₀.2.2 us)⟩

theorem InstExpansionRel.of_levelClosed {Γ : Env} {x' x : Expansion}
    (hlv : LevelClosed Γ) (hlp : x'.levelParams = x.levelParams)
    (har : x'.arity = x.arity) (hv : ExprConv Γ x'.value x.value) :
    InstExpansionRel Γ x' x := by
  refine ⟨hlp, har, fun us => ?_⟩
  rw [hlp]
  exact conv_substLevels hlv x.levelParams us hv

/-- Pointwise relation between the raw and computed lookups. It must be proved for the actual
`expansionOfP`; assuming it here only exposes the exact lifting boundary. -/
def InstExpansionLookup (Γ : Env)
    (raw computed : Name → Except String (Option Expansion)) : Prop :=
  ∀ n x', computed n = .ok (some x') →
    ∃ x, raw n = .ok (some x) ∧ InstExpansionRel Γ x' x

/-- The spine proof needs pointwise conversion of computed expansions; it does not need closure
of every rule in Γ under every universe map. This preserves the original spine conclusion. -/
theorem spineP_faithful_inst {Γ : Env} {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hH : HeadLaws Γ expansion?) (hF : HookFaithful Γ opt?)
    (hS : HookSiteStable opt?) {rec : Expr → Except String Expr}
    {expOf : Name → Except String (Option Expansion)}
    (hrec : ∀ a r, rec a = .ok r → ExprConv Γ r a)
    (hexp : InstExpansionLookup Γ expansion? expOf)
    {site : Option Name} {e r : Expr} (h : spineP opt? false rec expOf site e = .ok r) :
    ExprConv Γ r e := by
  have hargs : ∀ {l l' : List Expr}, l.mapM rec = .ok l' → Forall2 (Conv Γ) (l'.map er) (l.map er) :=
    fun hl => forall2_of_mapM_conv hrec hl
  have hspine := er_getAppFnArgs e
  unfold ExprConv
  unfold spineP at h
  split at h
  · rename_i n us hsh args heq
    rw [heq] at hspine
    obtain ⟨xo, hxo, h⟩ := except_bind_ok h
    cases xo with
    | none =>
      obtain ⟨args', hargs', h⟩ := except_bind_ok h
      have := except_pure_ok' h
      subst this
      rw [hspine, er_mkAppN, List.toList_toArray]
      exact Conv.appN_args _ (hargs hargs')
    | some x' =>
      obtain ⟨x, hx, hrel⟩ := hexp n x' hxo
      obtain ⟨args', hargs', h⟩ := except_bind_ok h
      have hc := hargs hargs'
      rw [hspine]
      have hhead : er (Expr.const n us hsh) = .const n us := rfl
      rw [hhead]
      split at h
      · have := except_pure_ok' h
        subst this
        rw [er_mkAppN, er_mkConst, List.toList_toArray]
        exact Conv.appN_args _ hc
      · split at h
        · rename_i e₁ hres
          have := except_pure_ok' h
          subst this
          have h1 := hookRes_faithful hF hS hres
          unfold ExprConv at h1
          rw [er_occTerm, List.toList_toArray] at h1
          exact .trans h1 (Conv.appN_args _ hc)
        · have h1 := instantiateP_conv Γ h
          unfold ExprConv at h1
          rw [er_mkAppN, List.toList_toArray] at h1
          have h2 := hrel.2.2 us
          unfold ExprConv at h2
          have hδ := hH n x hx us
          refine .trans h1 (.trans (Conv.appN h2 (Conv.forall₂_refl _)) ?_)
          exact .trans (Conv.appN (.symm (.step (.ax hδ))) (Conv.forall₂_refl _)) (Conv.appN_args _ hc)
  · rename_i hd args _ heq
    rw [heq] at hspine
    obtain ⟨h', hh', h⟩ := except_bind_ok h
    obtain ⟨args', hargs', h⟩ := except_bind_ok h
    have := except_pure_ok' h
    subst this
    rw [hspine, er_mkAppN, List.toList_toArray]
    exact Conv.appN (hrec hd h' hh') (hargs hargs')

/-- An additive rewrite lifting lemma with the same unrestricted term conclusion. The actual
computed-lookup relation is an internal induction obligation, not a final source-domain axiom. -/
theorem rwP_faithful_inst {Γ : Env}
    {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hH : HeadLaws Γ expansion?) (hF : HookFaithful Γ opt?) (hS : HookSiteStable opt?)
    (hexp : ∀ fuel, InstExpansionLookup Γ expansion?
      (expansionOfP expansion? opt? false fuel)) :
    ∀ fuel site e r, rwP expansion? opt? false fuel site e = .ok r → ExprConv Γ r e
  | 0, _, _, _, h => by simp only [rwP] at h; cases h
  | fuel + 1, site, e, r, h => by
    have IH := rwP_faithful_inst hH hF hS hexp fuel
    cases e
    case app f a hh =>
      simp only [rwP] at h
      exact spineP_faithful_inst hH hF hS (fun a r ha => IH site a r ha) (hexp fuel) h
    case const n us hh =>
      simp only [rwP] at h
      exact spineP_faithful_inst hH hF hS (fun a r ha => IH site a r ha) (hexp fuel) h
    case lam n t b bi hh =>
      simp only [rwP] at h
      obtain ⟨t', ht, h⟩ := except_bind_ok h
      obtain ⟨b', hb, h⟩ := except_bind_ok h
      have := except_pure_ok' h; subst this
      unfold ExprConv
      simp only [er_mkLam, er]
      exact .lam (IH _ _ _ ht) (IH _ _ _ hb)
    case forallE n t b bi hh =>
      simp only [rwP] at h
      obtain ⟨t', ht, h⟩ := except_bind_ok h
      obtain ⟨b', hb, h⟩ := except_bind_ok h
      have := except_pure_ok' h; subst this
      unfold ExprConv
      simp only [er_mkForallE, er]
      exact .pi (IH _ _ _ ht) (IH _ _ _ hb)
    case letE n t v b nd hh =>
      simp only [rwP] at h
      obtain ⟨t', ht, h⟩ := except_bind_ok h
      obtain ⟨v', hv, h⟩ := except_bind_ok h
      obtain ⟨b', hb, h⟩ := except_bind_ok h
      have := except_pure_ok' h; subst this
      unfold ExprConv
      simp only [er_mkLetE, er]
      exact .letE (IH _ _ _ ht) (IH _ _ _ hv) (IH _ _ _ hb)
    case proj s i x hh =>
      simp only [rwP] at h
      obtain ⟨x', hx, h⟩ := except_bind_ok h
      have := except_pure_ok' h; subst this
      unfold ExprConv
      simp only [er_mkProj, er]
      exact .proj _ _ (IH _ _ _ hx)
    case mdata md x hh =>
      simp only [rwP] at h
      obtain ⟨x', hx, h⟩ := except_bind_ok h
      have := except_pure_ok' h; subst this
      unfold ExprConv
      simp only [er_mkMData, er]
      exact IH _ _ _ hx
    all_goals
      simp only [rwP] at h
      have := except_pure_ok' h; subst this
      exact Conv.refl _

/-- The existing constant conclusion lifted through the pointwise rewrite result. -/
theorem rewriteConstP_faithful_inst {Γ : Env} {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hH : HeadLaws Γ expansion?) (hF : HookFaithful Γ opt?) (hS : HookSiteStable opt?)
    (hexp : ∀ fuel, InstExpansionLookup Γ expansion?
      (expansionOfP expansion? opt? false fuel))
    {ci ci' : ConstantInfo} (h : rewriteConstP expansion? opt? false ci = .ok ci') :
    ExprConv Γ ci'.getCnst.type ci.getCnst.type ∧
    (∀ v v', ci = .defnInfo v → ci' = .defnInfo v' → ExprConv Γ v'.value v.value) := by
  have hrw := fun site e r (h : rwP expansion? opt? false Ix.Compile.Pass.rewriteFuel site e = .ok r) =>
    rwP_faithful_inst hH hF hS hexp Ix.Compile.Pass.rewriteFuel site e r h
  unfold rewriteConstP at h
  cases ci with
  | defnInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    obtain ⟨val, hval, h⟩ := except_bind_ok h
    cases except_pure_ok' h
    refine ⟨hrw _ _ _ ht, ?_⟩
    intro w w' hw hw'
    cases hw
    cases hw'
    exact hrw _ _ _ hval
  | thmInfo v | opaqueInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    obtain ⟨val, -, h⟩ := except_bind_ok h
    cases except_pure_ok' h
    exact ⟨hrw _ _ _ ht, fun _ _ hw => by cases hw⟩
  | recInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    obtain ⟨rules, -, h⟩ := except_bind_ok h
    cases except_pure_ok' h
    exact ⟨hrw _ _ _ ht, fun _ _ hw => by cases hw⟩
  | axiomInfo v | quotInfo v | inductInfo v | ctorInfo v =>
    dsimp only at h
    obtain ⟨c, hc, h⟩ := except_bind_ok h
    obtain ⟨t, ht, rfl⟩ := cnst_type hc
    cases except_pure_ok' h
    exact ⟨hrw _ _ _ ht, fun _ _ hw => by cases hw⟩

/-- The remaining expansion-construction obligation, stated only for actual successful raw
lookups and successful rewrites of their stored values. No runtime commutation is assumed. -/
theorem expansionOfP_instLookup_of_stored {Γ : Env}
    {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hstored : ∀ fuel n x v, expansion? n = .ok (some x) → x.needsRewrite = true →
      rwP expansion? opt? false fuel none x.value = .ok v →
      ∀ us, ExprConv Γ (substLevels x.levelParams us v)
        (substLevels x.levelParams us x.value)) :
    ∀ fuel, InstExpansionLookup Γ expansion? (expansionOfP expansion? opt? false fuel)
  | 0 => by intro n x' h; simp only [expansionOfP] at h; cases h
  | fuel + 1 => by
    intro n x' h
    simp only [expansionOfP] at h
    obtain ⟨xo, hxo, h⟩ := except_bind_ok h
    cases xo with
    | none => cases h
    | some x =>
      simp only at h
      split at h
      · rename_i hrewrite
        obtain ⟨v, hv, h⟩ := except_bind_ok h
        have := except_pure_ok' h
        cases this
        exact ⟨x, hxo, rfl, rfl, hstored fuel n x v hxo hrewrite hv⟩
      · have := except_pure_ok' h
        have hx : x = x' := Option.some.inj this
        subst hx
        exact ⟨x, hxo, InstExpansionRel.refl Γ x⟩

end Ix.CompileCert.Opt
