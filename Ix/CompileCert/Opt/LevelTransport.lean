import Ix.CompileCert.Opt.Rewrite

/-!
# Scalar normalization and conversion through a level substitution

The scalar helper `substLevel` normalizes a level even with an empty parameter or argument
array, and on every parameter-free level. The term helper `substLevels` instead bypasses
traversal when either array is empty. These exact facts explain why literal substitution
composition needs more than universe-spine arity and parameter scope. Source ingestion and
raw stored expansions do not supply a blanket normalization theorem.

`Conv.mapC_viaConv` permits a mapped rule to be justified by a conversion, preserving the
existing `Conv.mapC` theorem. `conv_substLevels_viaConv` lifts that intermediate obligation
through a selected universe substitution. No semantic level-equivalence rule is added to Γ,
and no such rule is assumed as a final compiler law. Deriving the mapped conversion from the
original source/image construction, with the helper and runtime refinements, remains open.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (substLevel substLevels normalizeLevel)

/-- The scalar helper still visits smart constructors with an empty parameter list. -/
theorem substLevel_empty_params (us : Array Level) : ∀ l : Level,
    substLevel #[] us l = normalizeLevel l
  | .zero _ | .mvar .. => rfl
  | .param _ _ => by simp only [substLevel, normalizeLevel, Array.map_empty, Array.idxOf?_empty]
  | .succ l _ => by simp only [substLevel, normalizeLevel, substLevel_empty_params us l]
  | .max a b _ => by
    simp only [substLevel, normalizeLevel, substLevel_empty_params us a, substLevel_empty_params us b]
  | .imax a b _ => by
    simp only [substLevel, normalizeLevel, substLevel_empty_params us a, substLevel_empty_params us b]

/-- Missing scalar arguments preserve each parameter leaf but still normalize the level tree. -/
theorem substLevel_empty_univs (ps : Array Name) : ∀ l : Level,
    substLevel ps #[] l = normalizeLevel l
  | .zero _ | .mvar .. => rfl
  | .param n h => by
    simp only [substLevel, normalizeLevel]
    cases (ps.map Ix.Compile.Canon.keyName).idxOf? (Ix.Compile.Canon.keyName n) <;> rfl
  | .succ l _ => by simp only [substLevel, normalizeLevel, substLevel_empty_univs ps l]
  | .max a b _ => by
    simp only [substLevel, normalizeLevel, substLevel_empty_univs ps a, substLevel_empty_univs ps b]
  | .imax a b _ => by
    simp only [substLevel, normalizeLevel, substLevel_empty_univs ps a, substLevel_empty_univs ps b]

/-- A syntax predicate used only to state the exact scalar operation, not a compiler domain. -/
def LevelParamFree : Level → Prop
  | .param .. => False
  | .succ l _ => LevelParamFree l
  | .max a b _ | .imax a b _ => LevelParamFree a ∧ LevelParamFree b
  | .zero _ | .mvar .. => True

/-- Every scalar substitution acts as normalization on a level with no parameter leaves.
This uses no cached-equality or name-faithfulness premise. -/
theorem substLevel_paramFree (ps : Array Name) (us : Array Level) :
    ∀ l : Level, LevelParamFree l → substLevel ps us l = normalizeLevel l
  | .zero _, _ | .mvar .., _ => rfl
  | .param .., h => False.elim h
  | .succ l _, h => by
    simp only [substLevel, normalizeLevel, substLevel_paramFree ps us l h]
  | .max a b _, h => by
    simp only [substLevel, normalizeLevel, substLevel_paramFree ps us a h.1,
      substLevel_paramFree ps us b h.2]
  | .imax a b _, h => by
    simp only [substLevel, normalizeLevel, substLevel_paramFree ps us a h.1,
      substLevel_paramFree ps us b h.2]

/-- In contrast, the term helper bypasses traversal when its parameter array is empty. -/
theorem substLevels_empty_params (us : Array Level) (e : Expr) : substLevels #[] us e = e := by
  simp only [substLevels, Array.isEmpty_empty, Bool.true_or, ↓reduceIte]

/-- The same bypass occurs for an empty universe-argument array. -/
theorem substLevels_empty_univs (ps : Array Name) (e : Expr) : substLevels ps #[] e = e := by
  simp only [substLevels, Array.isEmpty_empty, Bool.or_true, ↓reduceIte]

end Ix.CompileCert.Opt

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)

/-- A mapped rule may be justified by several conversion steps. This additive variant keeps
`Conv.mapC` unchanged and does not assume any extra rule in either conversion environment. -/
theorem Conv.mapC_viaConv {Γ Γ' : Env}
    (g : Name → Array Level → Name × Array Level) (h : Level → Level)
    (hp : ∀ s c us, pairName s c = true → pairName s (g c us).1 = true)
    (hax : ∀ l r, Γ.ax l r → Conv Γ' (Tm.mapC g h l) (Tm.mapC g h r))
    {a b : Tm} (hc : Conv Γ a b) : Conv Γ' (Tm.mapC g h a) (Tm.mapC g h b) := by
  induction hc with
  | refl a => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | step s =>
    cases s with
    | beta t b a =>
      rw [Tm.mapC_inst]; exact .step (.beta _ _ _)
    | eta t f hf =>
      rw [Tm.mapC_lower g h f hf]
      exact .step (.eta _ _ (by rw [Tm.occ_mapC]; exact hf))
    | proj0 s c us α β a b hpn =>
      simp only [Tm.mapC, Tm.mapC_appN, List.map_cons, List.map_nil]
      exact .step (.proj0 _ _ _ _ _ _ _ (hp s c us hpn))
    | proj1 s c us α β a b hpn =>
      simp only [Tm.mapC, Tm.mapC_appN, List.map_cons, List.map_nil]
      exact .step (.proj1 _ _ _ _ _ _ _ (hp s c us hpn))
    | ax hl => exact hax _ _ hl
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | pi _ _ ih1 ih2 => exact .pi ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | proj s i _ ih => exact .proj s i ih

end Ix.CompileCert.Conv

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (substLevel substLevels)

/-- Transport through one chosen universe substitution, provided the mapped rules actually
convert. The premise isolates the semantic level step still to derive from source; it is not
a new final law and is not asserted of `Env.ofExpansions` here. -/
theorem conv_substLevels_viaConv {Γ : Env} (ps : Array Name) (us : Array Level)
    (hax : ∀ l r, Γ.ax l r →
      Conv Γ (Tm.mapC (fun c vs => (c, vs.map (substLevel ps us))) (substLevel ps us) l)
        (Tm.mapC (fun c vs => (c, vs.map (substLevel ps us))) (substLevel ps us) r))
    {a b : Expr} (hc : ExprConv Γ a b) :
    ExprConv Γ (substLevels ps us a) (substLevels ps us b) := by
  unfold ExprConv at hc ⊢
  rw [er_substLevels, er_substLevels]
  split
  · exact hc
  · exact Conv.mapC_viaConv _ _ (fun _ _ _ hp => hp) hax hc

end Ix.CompileCert.Opt
