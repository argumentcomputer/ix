import Ix.CompileCert.Opt.Engine

/-!
# M7 L3-def: the call-site rewrite (`Ix/Compile/Pass/Translate.lean`, `rw`, `expansionOf`)

`Translate.rw` runs in `RwM`, a state of tables (`cache` of rewritten subterms keyed by
`(Expr × Bool × Option Name)` under the hash `BEq`, `declineCache`, `levelCache`, `exps`, the
development's `dev` tables) and records (`sources`, `needed`, `declines`, `canon`, `pjFired`,
`pjPasses`, `pjForms`). As for X1's `Develop` (its refactor R-1; this one is R-2), a table hit is
the entry of the same term only if no two terms met by the run collide, so the theorems are
about the **core** without the tables: `rwP`, `expansionOfP`, the same recursion clause by clause,
the records dropped, the decompile placeholder `mdata` omitted (the erasure `er` drops `mdata`
anyway), X1's table-free development `instantiateP` for the inline. That the executable equals the
core up to erasure is checked by the test `opt-census` (`Tests/Ix/Compile/OptCensus.lean`).

* **`rwP_faithful`**: every rewritten term converts to its input, given the δ-rules of the heads
  (`HeadLaws`: the expansion the rewrite reads, at every universe argument — decision 3, Def 3.5),
  rules closed under the universe instantiations (`LevelClosed Γ`, design D-1 (a): a rewritten
  Def 3.5 value is instantiated at each occurrence's levels) and a hook that is faithful with no
  site and site-stable (`HookFaithful`, `HookSiteStable`: `hook_faithful`, `hook_siteStable` for
  `Driver.optLookup`), at a Lean name (`inPlace = false`);
* **`rwP_lean_name`** (decision 5, D1, as an equation): at a Lean name the proof-justified passes
  have no effect on the result: the rewrite equals the rewrite whose hook is the site-free one;
* `expansionOfP_faithful`: a rewritten expansion converts to the raw one.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)
open Ix.Compile.Pass (Expansion)

/-- The hook's type (`RwState.opt?`). -/
abbrev Hook := Option Name → Name → Array Level → Array Expr → Option (Expr × Array ConstantInfo × Option String)

/-- What the rewrite takes from the hook at a full application (`Translate.rw`'s `res`). -/
def hookRes (opt? : Hook) (inPlace : Bool) (site : Option Name) (n : Name) (us : Array Level)
    (args : Array Expr) : Option Expr :=
  match opt? site n us args with
  | some (e, _, none) => some e
  | some (e, _, some _) => if inPlace then some e else (opt? none n us args).map (·.1)
  | none => none

/-- The rewrite of an application spine or a constant (`Translate.rw`'s first case), given the
rewrite of subterms `rec` and the expansion lookup `expOf`. -/
def spineP (opt? : Hook) (inPlace : Bool) (rec : Expr → Except String Expr)
    (expOf : Name → Except String (Option Expansion)) (site : Option Name) (e : Expr) :
    Except String Expr :=
  match getAppFnArgs e with
  | (.const n us hsh, args) => do
    match ← expOf n with
    | some x => do
      let args' ← args.toList.mapM rec
      if args.size < x.arity then pure (mkAppN (Expr.mkConst n us) args'.toArray)
      else
        match hookRes opt? inPlace site n us args'.toArray with
        | some e' => pure e'
        | none => instantiateP (substLevels x.levelParams us x.value) args'.toArray
    | none => do
      let args' ← args.toList.mapM rec
      pure (mkAppN (.const n us hsh) args'.toArray)
  | (h, args) => do
    let h' ← rec h
    let args' ← args.toList.mapM rec
    pure (mkAppN h' args'.toArray)

section
variable (expansion? : Name → Except String (Option Expansion)) (opt? : Hook) (inPlace : Bool)

mutual
/-- `Translate.expansionOf` without its table. -/
def expansionOfP : Nat → Name → Except String (Option Expansion)
  | 0, _ => throw "Pass 3 rewrite: recursion bound exhausted"
  | fuel + 1, n => do
    match ← expansion? n with
    | none => pure none
    | some x =>
      if x.needsRewrite then do
        let v ← rwP fuel none x.value
        pure (some { x with value := v, needsRewrite := false })
      else pure (some x)

/-- `Translate.rw` without its tables and records. -/
def rwP : Nat → Option Name → Expr → Except String Expr
  | 0, _, _ => throw "Pass 3 rewrite: recursion bound exhausted"
  | fuel + 1, site, e =>
    match e with
    | .app .. => spineP opt? inPlace (rwP fuel site) (expansionOfP fuel) site e
    | .const .. => spineP opt? inPlace (rwP fuel site) (expansionOfP fuel) site e
    | .lam n t b bi _ => do pure (Expr.mkLam n (← rwP fuel site t) (← rwP fuel site b) bi)
    | .forallE n t b bi _ => do pure (Expr.mkForallE n (← rwP fuel site t) (← rwP fuel site b) bi)
    | .letE n t v b nd _ => do
      pure (Expr.mkLetE n (← rwP fuel site t) (← rwP fuel site v) (← rwP fuel site b) nd)
    | .proj s i x _ => do pure (Expr.mkProj s i (← rwP fuel site x))
    | .mdata md x _ => do pure (Expr.mkMData md (← rwP fuel site x))
    | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. => pure e
end

end


/-! ## Laws of the rewrite -/

/-- **`HeadLaws`** (decision 3, Def 3.4–3.5): every head the rewrite expands δ-reduces to its
expansion, at every universe argument. -/
def HeadLaws (Γ : Env) (expansion? : Name → Except String (Option Expansion)) : Prop :=
  ∀ n x, expansion? n = .ok (some x) → ∀ us, Γ.ax (.const n us) (er (substLevels x.levelParams us x.value))

/-- **`LevelClosed Γ`** (design D-1 (a)): the rules are closed under the universe instantiations
`substLevel ps us` (δ up to universe-level equivalence; the composition lemma for `substLevel`
would make it plain δ for `Env.ofExpansions`). -/
def LevelClosed (Γ : Env) : Prop :=
  ∀ (ps : Array Name) (us : Array Level) (l r : Tm), Γ.ax l r →
    Γ.ax (Tm.mapC (fun c vs => (c, vs.map (Ix.Compile.Canon.substLevel ps us))) (Ix.Compile.Canon.substLevel ps us) l)
      (Tm.mapC (fun c vs => (c, vs.map (Ix.Compile.Canon.substLevel ps us))) (Ix.Compile.Canon.substLevel ps us) r)

/-- A conversion survives a universe instantiation. -/
theorem conv_substLevels {Γ : Env} (hlv : LevelClosed Γ) (ps : Array Name) (us : Array Level)
    {a b : Expr} (h : ExprConv Γ a b) : ExprConv Γ (substLevels ps us a) (substLevels ps us b) := by
  unfold ExprConv at h ⊢
  rw [er_substLevels, er_substLevels]
  split
  · exact h
  · exact Conv.mapC _ _ (fun _ _ _ hp => hp) (fun l r hl => hlv ps us l r hl) h

/-- The hook's site-free results are untagged. -/
def HookUntagged (opt? : Hook) : Prop :=
  ∀ n us args e cs t, opt? none n us args = some (e, cs, t) → t = none

theorem hook_untagged {Γ : Env} {opt? : Hook} (hF : HookFaithful Γ opt?) : HookUntagged opt? :=
  fun n us args e cs t h => (hF n us args e cs t h).1

/-- **What the rewrite takes from the hook converts to the occurrence** (at a Lean name). -/
theorem hookRes_faithful {Γ : Env} {opt? : Hook} (hF : HookFaithful Γ opt?) (hS : HookSiteStable opt?)
    {site : Option Name} {n : Name} {us : Array Level} {args : Array Expr} {e : Expr}
    (h : hookRes opt? false site n us args = some e) : ExprConv Γ e (occTerm ⟨n, us, args, none⟩) := by
  unfold hookRes at h
  cases hs : opt? site n us args with
  | none => rw [hs] at h; cases h
  | some r =>
    rw [hs] at h
    obtain ⟨e₁, cs₁, t₁⟩ := r
    cases t₁ with
    | none =>
      simp only [Option.some.injEq] at h
      subst h
      cases site with
      | none => exact (hF n us args e₁ cs₁ none hs).2
      | some c => exact (hF n us args e₁ cs₁ none (hS.1 c n us args e₁ cs₁ hs)).2
    | some p =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨e₂, cs₂, t₂⟩, h₂, rfl⟩ := omap_some h
      exact (hF n us args e₂ cs₂ t₂ h₂).2

/-- **D1 at the hook**: at a Lean name, the hook's contribution is the site-free hook's. -/
theorem hookRes_lean_name {opt? : Hook} (hU : HookUntagged opt?) (hS : HookSiteStable opt?)
    (site : Option Name) (n : Name) (us : Array Level) (args : Array Expr) :
    hookRes opt? false site n us args = hookRes (fun _ => opt? none) false site n us args := by
  have rhs : hookRes (fun _ => opt? none) false site n us args = (opt? none n us args).map (·.1) := by
    unfold hookRes
    dsimp only
    cases h0 : opt? none n us args with
    | none => rfl
    | some r =>
      obtain ⟨e, cs, t⟩ := r
      have := hU n us args e cs t h0
      subst this
      rfl
  rw [rhs]
  unfold hookRes
  cases hs : opt? site n us args with
  | none =>
    cases site with
    | none => rw [hs]; rfl
    | some c => rw [hS.2 c n us args hs]; rfl
  | some r =>
    obtain ⟨e, cs, t⟩ := r
    cases t with
    | none =>
      cases site with
      | none => rw [hs]; rfl
      | some c => rw [hS.1 c n us args e cs hs]; rfl
    | some p => rfl

/-! ## Faithfulness -/

theorem except_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem except_pure_ok' {α : Type} {a b : α} (h : (pure a : Except String α) = .ok b) : a = b := by
  cases h; rfl

/-- The arguments, rewritten one by one, convert to the originals. -/
theorem forall2_of_mapM_conv {Γ : Env} {f : Expr → Except String Expr}
    (hf : ∀ a r, f a = .ok r → ExprConv Γ r a) :
    ∀ {l l' : List Expr}, l.mapM f = .ok l' → Forall2 (Conv Γ) (l'.map er) (l.map er)
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure] at h
    cases h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    obtain ⟨bs, hbs, h⟩ := except_bind_ok h
    have := except_pure_ok' h
    subst this
    exact .cons (hf a b hb) (forall2_of_mapM_conv hf hbs)

/-- **An application spine or a constant, rewritten, converts to itself** (given that the
rewrite of the subterms and of the expansions does). -/
theorem spineP_faithful {Γ : Env} {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hH : HeadLaws Γ expansion?) (hlv : LevelClosed Γ) (hF : HookFaithful Γ opt?)
    (hS : HookSiteStable opt?) {rec : Expr → Except String Expr}
    {expOf : Name → Except String (Option Expansion)}
    (hrec : ∀ a r, rec a = .ok r → ExprConv Γ r a)
    (hexp : ∀ n x', expOf n = .ok (some x') →
      ∃ x, expansion? n = .ok (some x) ∧ x'.levelParams = x.levelParams ∧ x'.arity = x.arity ∧
        ExprConv Γ x'.value x.value)
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
      obtain ⟨x, hx, hlp, -, hxv⟩ := hexp n x' hxo
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
          rw [er_mkAppN, List.toList_toArray, hlp] at h1
          have h2 := conv_substLevels hlv x.levelParams us hxv
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

/-- **The rewrite is faithful** (and so is the rewrite of an expansion), at a Lean name. -/
theorem rwP_faithful {Γ : Env} {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hH : HeadLaws Γ expansion?) (hlv : LevelClosed Γ) (hF : HookFaithful Γ opt?)
    (hS : HookSiteStable opt?) : ∀ fuel : Nat,
    (∀ n x', expansionOfP expansion? opt? false fuel n = .ok (some x') →
      ∃ x, expansion? n = .ok (some x) ∧ x'.levelParams = x.levelParams ∧ x'.arity = x.arity ∧
        ExprConv Γ x'.value x.value) ∧
    (∀ site e r, rwP expansion? opt? false fuel site e = .ok r → ExprConv Γ r e)
  | 0 => ⟨fun n x' h => (by simp only [expansionOfP] at h; cases h),
          fun site e r h => (by simp only [rwP] at h; cases h)⟩
  | fuel + 1 => by
    have IH := rwP_faithful hH hlv hF hS fuel
    refine ⟨fun n x' h => ?_, fun site e r h => ?_⟩
    · simp only [expansionOfP] at h
      obtain ⟨xo, hxo, h⟩ := except_bind_ok h
      cases xo with
      | none => cases h
      | some x =>
        simp only at h
        split at h
        · obtain ⟨v, hv, h⟩ := except_bind_ok h
          have := except_pure_ok' h
          cases this
          exact ⟨x, hxo, rfl, rfl, IH.2 none x.value v hv⟩
        · have := except_pure_ok' h
          have hx : x = x' := Option.some.inj this
          subst hx
          exact ⟨x, hxo, rfl, rfl, Conv.refl _⟩
    · cases e
      case app f a hh =>
        simp only [rwP] at h
        exact spineP_faithful hH hlv hF hS (fun a r ha => IH.2 site a r ha) IH.1 h
      case const n us hh =>
        simp only [rwP] at h
        exact spineP_faithful hH hlv hF hS (fun a r ha => IH.2 site a r ha) IH.1 h
      case lam n t b bi hh =>
        simp only [rwP] at h
        obtain ⟨t', ht, h⟩ := except_bind_ok h
        obtain ⟨b', hb, h⟩ := except_bind_ok h
        have := except_pure_ok' h; subst this
        unfold ExprConv
        simp only [er_mkLam, er]
        exact .lam (IH.2 _ _ _ ht) (IH.2 _ _ _ hb)
      case forallE n t b bi hh =>
        simp only [rwP] at h
        obtain ⟨t', ht, h⟩ := except_bind_ok h
        obtain ⟨b', hb, h⟩ := except_bind_ok h
        have := except_pure_ok' h; subst this
        unfold ExprConv
        simp only [er_mkForallE, er]
        exact .pi (IH.2 _ _ _ ht) (IH.2 _ _ _ hb)
      case letE n t v b nd hh =>
        simp only [rwP] at h
        obtain ⟨t', ht, h⟩ := except_bind_ok h
        obtain ⟨v', hv, h⟩ := except_bind_ok h
        obtain ⟨b', hb, h⟩ := except_bind_ok h
        have := except_pure_ok' h; subst this
        unfold ExprConv
        simp only [er_mkLetE, er]
        exact .letE (IH.2 _ _ _ ht) (IH.2 _ _ _ hv) (IH.2 _ _ _ hb)
      case proj s i x hh =>
        simp only [rwP] at h
        obtain ⟨x', hx, h⟩ := except_bind_ok h
        have := except_pure_ok' h; subst this
        unfold ExprConv
        simp only [er_mkProj, er]
        exact .proj _ _ (IH.2 _ _ _ hx)
      case mdata md x hh =>
        simp only [rwP] at h
        obtain ⟨x', hx, h⟩ := except_bind_ok h
        have := except_pure_ok' h; subst this
        unfold ExprConv
        simp only [er_mkMData, er]
        exact IH.2 _ _ _ hx
      all_goals
        simp only [rwP] at h
        have := except_pure_ok' h; subst this
        exact Conv.refl _

/-! ## D1: the Lean name's form -/

/-- **D1 as an equation**: at a Lean name (`inPlace = false`) the rewrite with the hook is the
rewrite with the site-free hook: the proof-justified passes, which fire only at a site, leave no
trace in the Lean name's form. -/
theorem rwP_lean_name {expansion? : Name → Except String (Option Expansion)} {opt? : Hook}
    (hU : HookUntagged opt?) (hS : HookSiteStable opt?) : ∀ fuel : Nat,
    (∀ n, expansionOfP expansion? opt? false fuel n = expansionOfP expansion? (fun _ => opt? none) false fuel n) ∧
    (∀ site e, rwP expansion? opt? false fuel site e = rwP expansion? (fun _ => opt? none) false fuel site e)
  | 0 => ⟨fun _ => by simp only [expansionOfP], fun _ _ => by simp only [rwP]⟩
  | fuel + 1 => by
    have IH := rwP_lean_name (expansion? := expansion?) hU hS fuel
    have hfun : rwP expansion? opt? false fuel = rwP expansion? (fun _ => opt? none) false fuel := by
      funext site e; exact IH.2 site e
    have hexp : expansionOfP expansion? opt? false fuel = expansionOfP expansion? (fun _ => opt? none) false fuel := by
      funext n; exact IH.1 n
    have hres : hookRes opt? false = hookRes (fun _ => opt? none) false := by
      funext site n us args; exact hookRes_lean_name hU hS site n us args
    have hsp : ∀ rec expOf site e, spineP opt? false rec expOf site e =
        spineP (fun _ => opt? none) false rec expOf site e := by
      intro rec expOf site e
      unfold spineP
      rw [hres]
    refine ⟨fun n => ?_, fun site e => ?_⟩
    · simp only [expansionOfP, hfun]
    · cases e <;> simp only [rwP, hfun, hexp, hsp]

end Ix.CompileCert.Opt

