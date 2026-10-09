import Ix.CompileCert.Conv.Develop
import Ix.CompileCert.Conv.Stable
import Ix.CompileCert.Canon.Rename

/-!
# M7 X1: the developments of the image path, and the δ-environment of the expansions

* `Env.ofExpansions`: the δ-rules of a set of expansions (`n.{us} ⟶ value[params := us]`): the
  image constants (Def 3.4, decision 3: the Lean name of an image-kind auxiliary denotes its
  image) and Lean's own auxiliaries over images (Def 3.5), as `Ix.Compile.Pass.Expansion`s.
  Closed under lifting and substitution when the values are closed (`ofExpansions_liftClosed`,
  `ofExpansions_instClosed`), as images are (λs over Lean's whole telescope).
* `expansion_inline_conv`: **the inline rewrite of a full application of an expansion is
  convertible to the application** in the δ-environment of that expansion (§4.5, Def 3.6):
  δ, then the development.
* `substFVarsP_conv` (P3a, the canonical minor types with the motives substituted and the rule
  statements): the developed substitution of free variables is convertible to the plain one.
* `etaReduce_conv`: the η-contraction of the image's wrappers (§4.3 item 1, `Expr.eta`).
* `exprConv_of_eRen`: the term equality the Canon proofs use (`ERen` at the identity renaming:
  hashes, binder names, binder infos and `letE` flags arbitrary) is contained in `ExprConv`.
-/

open private Ix.Compile.Image.hasLooseBVar.go from Ix.Compile.Image.Expr

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)
open Ix.Compile.Image (Created)

/-! ## The δ-environment of the expansions -/

/-- `n.{us} ⟶ value[levelParams := us]` for every expansion `n ↦ (levelParams, value)`. -/
def Env.ofExpansions (exp? : Name → Option (Array Name × Expr)) : Env where
  ax l r := ∃ n lps val us, exp? n = some (lps, val) ∧ l = .const n us ∧
    r = er (substLevels lps us val)

theorem Tm.range_mapC (g : Name → Array Level → Name × Array Level) (h : Level → Level) :
    ∀ (t : Tm), Tm.range (Tm.mapC g h t) = Tm.range t
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .app f a => by simp only [Tm.mapC, Tm.range, Tm.range_mapC g h f, Tm.range_mapC g h a]
  | .lam t b => by simp only [Tm.mapC, Tm.range, Tm.range_mapC g h t, Tm.range_mapC g h b]
  | .pi t b => by simp only [Tm.mapC, Tm.range, Tm.range_mapC g h t, Tm.range_mapC g h b]
  | .letE t v b => by
    simp only [Tm.mapC, Tm.range, Tm.range_mapC g h t, Tm.range_mapC g h v, Tm.range_mapC g h b]
  | .proj s i e => by simp only [Tm.mapC, Tm.range, Tm.range_mapC g h e]

theorem range_substLevels (lps : Array Name) (us : Array Level) (val : Expr) :
    Tm.range (er (substLevels lps us val)) = Tm.range (er val) := by
  rw [er_substLevels]; split
  · rfl
  · exact Tm.range_mapC _ _ _

theorem ofExpansions_closed {exp? : Name → Option (Array Name × Expr)}
    (hc : ∀ n lps val, exp? n = some (lps, val) → looseRangeP val = 0) :
    ∀ l r, (Env.ofExpansions exp?).ax l r → l.range = 0 ∧ r.range = 0 := by
  rintro l r ⟨n, lps, val, us, he, rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  rw [range_substLevels, ← looseRangeP_eq]; exact hc n lps val he

theorem ofExpansions_liftClosed {exp? : Name → Option (Array Name × Expr)}
    (hc : ∀ n lps val, exp? n = some (lps, val) → looseRangeP val = 0) :
    (Env.ofExpansions exp?).LiftClosed :=
  Env.liftClosed_of_closed (ofExpansions_closed hc)

theorem ofExpansions_instClosed {exp? : Name → Option (Array Name × Expr)}
    (hc : ∀ n lps val, exp? n = some (lps, val) → looseRangeP val = 0) :
    (Env.ofExpansions exp?).InstClosed :=
  Env.instClosed_of_closed (ofExpansions_closed hc)

/-- **The inline rewrite of an expansion's full application is a conversion** of the
application, in any environment with the expansion's δ-rule (Translate's `rw` at a full
application: `instantiate (substLevels x.levelParams us x.value) args'`, here its core). -/
theorem expansion_inline_conv {Γ : Env} {exp? : Name → Option (Array Name × Expr)}
    (hΓ : ∀ l r, (Env.ofExpansions exp?).ax l r → Γ.ax l r) {n : Name} {lps : Array Name}
    {val : Expr} (hx : exp? n = some (lps, val)) {us : Array Level} {args : Array Expr} {r : Expr}
    (h : instantiateP (substLevels lps us val) args = .ok r) :
    ExprConv Γ r (mkAppN (Expr.mkConst n us) args) :=
  inline_conv Γ (hΓ _ _ ⟨n, lps, val, us, hx, rfl, rfl⟩) h

/-- `Image.inline` without the development's tables. -/
def imageInlineP (img : Ix.Compile.Image.Image) (us : Array Level) (args : Array Expr) :
    Except String (Option Expr) :=
  if args.size < img.arity then pure none
  else some <$> instantiateP (substLevels img.levelParams us img.value) args

/-- An image's inline form at a full application is convertible to the application of the
image constant, given the image constant's δ-rule. -/
theorem imageInlineP_conv {Γ : Env} {img : Ix.Compile.Image.Image} {us : Array Level}
    {args : Array Expr} {r : Expr}
    (hδ : Γ.ax (.const img.name us) (er (substLevels img.levelParams us img.value)))
    (h : imageInlineP img us args = .ok (some r)) :
    ExprConv Γ r (mkAppN (Expr.mkConst img.name us) args) := by
  unfold imageInlineP at h
  split at h
  · cases h
  · obtain ⟨r', hr', hrr⟩ := map_ok h
    cases hrr
    exact inline_conv Γ hδ hr'

/-! ## P3a: the developed substitution of free variables -/

theorem foldl_inst_conv {Γ : Env} (hΓ : Γ.InstClosed) : ∀ (l : List Expr) {a b : Tm},
    Conv Γ a b → Conv Γ (l.foldl (fun t v => Tm.inst (er v) 0 t) a)
      (l.foldl (fun t v => Tm.inst (er v) 0 t) b)
  | [], _, _, h => h
  | _ :: l, _, _, h => foldl_inst_conv hΓ l (h.inst hΓ _ 0)

theorem foldlM_conv {fuel : Nat} : ∀ (l : List Expr) (acc r : Expr),
    l.foldlM (fun acc v => Prod.fst <$> hinstP fuel v 0 acc) acc = .ok r →
    Conv Env.empty (er r) (l.foldl (fun t v => Tm.inst (er v) 0 t) (er acc))
  | [], acc, r, h => by cases h; exact .refl _
  | v :: l, acc, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h2⟩ := bind_ok h
    obtain ⟨⟨a, c⟩, ha, rfl⟩ := map_ok h1
    exact .trans (foldlM_conv l a r h2)
      (foldl_inst_conv Env.empty_instClosed l (hinstP_conv Env.empty ha))

/-- **The developed substitution of free variables is a conversion** of the plain one: the
free variables abstracted, then the values substituted one by one, the last first (as
`substFVars` does). -/
theorem substFVarsP_conv (Γ : Env) {xs : Array Name} {vs : Array Expr} {e r : Expr}
    (h : substFVarsP xs vs e = .ok r) :
    Conv Γ (er r) (vs.toList.reverse.foldl (fun t v => Tm.inst (er v) 0 t)
      (Tm.abstractF xs (er e) 0)) := by
  unfold substFVarsP at h
  split at h
  · cases h
  · have := foldlM_conv _ _ _ h
    rw [er_abstractFVars] at this
    exact Conv.mono (fun _ _ hl => False.elim hl) this

/-! ## η of the wrappers -/

theorem hasLooseBVar_go_eq : ∀ (e : Expr) (k : Nat),
    Ix.Compile.Image.hasLooseBVar.go e k = Tm.occ (er e) k
  | .bvar j _, k => rfl
  | .app f a _, k => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, er, Tm.occ, hasLooseBVar_go_eq f k,
      hasLooseBVar_go_eq a k]
  | .lam _ t b _ _, k => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, er, Tm.occ, hasLooseBVar_go_eq t k,
      hasLooseBVar_go_eq b (k + 1)]
  | .forallE _ t b _ _, k => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, er, Tm.occ, hasLooseBVar_go_eq t k,
      hasLooseBVar_go_eq b (k + 1)]
  | .letE _ t v b _ _, k => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, er, Tm.occ, hasLooseBVar_go_eq t k,
      hasLooseBVar_go_eq v k, hasLooseBVar_go_eq b (k + 1)]
  | .proj _ _ s _, k => by
    simp only [Ix.Compile.Image.hasLooseBVar.go, er, Tm.occ, hasLooseBVar_go_eq s k]
  | .mdata _ s _, k => by simp only [Ix.Compile.Image.hasLooseBVar.go, er, hasLooseBVar_go_eq s k]
  | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _ | .lit .., _ => rfl

theorem hasLooseBVar_eq (e : Expr) (k : Nat) :
    Ix.Compile.Image.hasLooseBVar e k = Tm.occ (er e) k := hasLooseBVar_go_eq e k

/-- **`etaReduce` is a conversion** (η-steps under the leading λs). -/
theorem etaReduce_conv (Γ : Env) : ∀ (e : Expr), Conv Γ (er (Ix.Compile.Image.etaReduce e)) (er e)
  | .lam n d b bi hh => by
    have ih := etaReduce_conv Γ b
    simp only [Ix.Compile.Image.etaReduce]
    generalize hb' : Ix.Compile.Image.etaReduce b = b' at ih
    have hcl : Conv Γ (.lam (er d) (er b')) (er (.lam n d b bi hh)) := by
      simp only [er]; exact .lam (.refl _) ih
    match b', hb', ih, hcl with
    | .app f (.bvar 0 h1) h2, _, ih, hcl =>
      simp only
      split
      · rename_i hocc
        have hocc' : Tm.occ (er f) 0 = false := by
          rw [← hasLooseBVar_eq]; simpa using hocc
        rw [Ix.CompileCert.Conv.er_lowerLoose]
        refine .trans (.symm (.step (.eta (er d) (er f) hocc'))) ?_
        simp only [er] at hcl; exact hcl
      · simp only [er_mkLam]; exact hcl
    | .bvar .., _, _, hcl | .fvar .., _, _, hcl | .mvar .., _, _, hcl | .sort .., _, _, hcl
    | .const .., _, _, hcl | .lam .., _, _, hcl | .forallE .., _, _, hcl | .letE .., _, _, hcl
    | .lit .., _, _, hcl | .mdata .., _, _, hcl | .proj .., _, _, hcl =>
      simp only [er_mkLam]; exact hcl
    | .app _ (.bvar (_ + 1) _) _, _, _, hcl | .app _ (.fvar ..) _, _, _, hcl
    | .app _ (.mvar ..) _, _, _, hcl | .app _ (.sort ..) _, _, _, hcl | .app _ (.const ..) _, _, _, hcl
    | .app _ (.app ..) _, _, _, hcl | .app _ (.lam ..) _, _, _, hcl | .app _ (.forallE ..) _, _, _, hcl
    | .app _ (.letE ..) _, _, _, hcl | .app _ (.lit ..) _, _, _, hcl | .app _ (.mdata ..) _, _, _, hcl
    | .app _ (.proj ..) _, _, _, hcl =>
      simp only [er_mkLam]; exact hcl
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .app .. | .forallE .. | .letE ..
  | .lit .. | .mdata .. | .proj .. => .refl _

/-! ## The Canon proofs' term equality -/

theorem er_eq_of_eRen {S : Name → Prop} : ∀ {e e' : Expr},
    Ix.CompileCert.Canon.ERen id S e e' → er e = er e' := by
  intro e e' h
  induction h with
  | bvar | fvar | mvar | sort | lit => rfl
  | const n us h h' _ => rfl
  | app h h' _ _ ih1 ih2 => simp only [er, ih1, ih2]
  | lam n n' bi bi' h h' _ _ ih1 ih2 => simp only [er, ih1, ih2]
  | forallE n n' bi bi' h h' _ _ ih1 ih2 => simp only [er, ih1, ih2]
  | letE n n' nd h h' _ _ _ ih1 ih2 ih3 => simp only [er, ih1, ih2, ih3]
  | mdata d h h' _ ih => simp only [er, ih]
  | proj n i h h' _ _ ih => simp only [er, ih]; rfl

/-- **The Canon proofs' equality is a conversion**: two expressions related by `ERen` at the
identity renaming (hashes, binder names and infos, `letE` flags arbitrary) are convertible in
every environment. -/
theorem exprConv_of_eRen (Γ : Env) {S : Name → Prop} {e e' : Expr}
    (h : Ix.CompileCert.Canon.ERen id S e e') : ExprConv Γ e e' := by
  unfold ExprConv; rw [er_eq_of_eRen h]; exact .refl _

end Ix.CompileCert.Conv
