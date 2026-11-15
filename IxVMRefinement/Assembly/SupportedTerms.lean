import IxVMRefinement.Assembly.ModelSupport
import Ix.IxVM.Consistency.Statement
import IxC.Kernel.Model.StoreCompanions

/-! # Support of stored reader terms

Annotations, substitution, and projection-table construction preserve the constant and literal
support of reader terms. These facts connect the raw declarations to selected final constants.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel (Mode)

/-- Monotonicity of `Expr.Supports` in the key predicate. -/
theorem supports_mono {md : Mode} {K₁ K₂ : Ix.Kernel.Key md → Prop}
    (h : ∀ k, K₁ k → K₂ k) : ∀ {e : Ix.Kernel.Expr md}, e.Supports K₁ → e.Supports K₂ := by
  intro e
  induction e with
  | bvar _ | fvar _ _ | sort _ => intro _; trivial
  | lit l =>
    cases l with
    | natVal _ => intro ⟨hz, hs⟩; exact ⟨h _ hz, h _ hs⟩
    | strVal _ =>
      intro ⟨hz, hs, hso, hnil, hcons, hc, hof⟩
      exact ⟨h _ hz, h _ hs, h _ hso, h _ hnil, h _ hcons, h _ hc, h _ hof⟩
  | const n _ => exact h n
  | app _ _ ihf iha => intro ⟨hf, ha⟩; exact ⟨ihf hf, iha ha⟩
  | lam _ _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | forallE _ _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | letE _ _ _ _ iht ihv ihb => intro ⟨ht, hv, hb⟩; exact ⟨iht ht, ihv hv, ihb hb⟩
  | proj _ _ _ ihe => exact ihe

/-- Lifting loose bound variables preserves `Expr.Supports`. -/
theorem supports_liftLooseBVars {md : Mode} {K : Ix.Kernel.Key md → Prop} (amt : Nat) :
    ∀ (e : Ix.Kernel.Expr md) (cut : Nat), e.Supports K →
      (Ix.Kernel.Expr.liftLooseBVars amt cut e).Supports K
  | .bvar _, cut, _ => by
    rw [Ix.Kernel.Expr.liftLooseBVars]
    split <;> trivial
  | .fvar _ _, _, _ | .sort _, _, _ => trivial
  | .lit _, _, h => h
  | .const _ _, _, hk => hk
  | .app f a, cut, ⟨hf, ha⟩ =>
    ⟨supports_liftLooseBVars amt f cut hf, supports_liftLooseBVars amt a cut ha⟩
  | .lam ty b _, cut, ⟨ht, hb⟩ =>
    ⟨supports_liftLooseBVars amt ty cut ht, supports_liftLooseBVars amt b (cut + 1) hb⟩
  | .forallE ty b _, cut, ⟨ht, hb⟩ =>
    ⟨supports_liftLooseBVars amt ty cut ht, supports_liftLooseBVars amt b (cut + 1) hb⟩
  | .letE ty v b _, cut, ⟨ht, hv, hb⟩ =>
    ⟨supports_liftLooseBVars amt ty cut ht, supports_liftLooseBVars amt v cut hv,
      supports_liftLooseBVars amt b (cut + 1) hb⟩
  | .proj _ _ e, cut, he => supports_liftLooseBVars amt e cut he

/-- Capture-avoiding single substitution (`instantiate1Lift`) preserves `Expr.Supports`. -/
theorem supports_instantiate1Lift {md : Mode} {K : Ix.Kernel.Key md → Prop}
    {v : Ix.Kernel.Expr md} (hv : v.Supports K) :
    ∀ (e : Ix.Kernel.Expr md) (d : Nat), e.Supports K → (e.instantiate1Lift v d).Supports K
  | .bvar _, d, _ => by
    rw [Ix.Kernel.Expr.instantiate1Lift]
    split
    · exact supports_liftLooseBVars d v 0 hv
    · split <;> trivial
  | .fvar _ _, _, _ | .sort _, _, _ => trivial
  | .lit _, _, h => h
  | .const _ _, _, hk => hk
  | .app f a, d, ⟨hf, ha⟩ =>
    ⟨supports_instantiate1Lift hv f d hf, supports_instantiate1Lift hv a d ha⟩
  | .lam ty b _, d, ⟨ht, hb⟩ =>
    ⟨supports_instantiate1Lift hv ty d ht, supports_instantiate1Lift hv b (d + 1) hb⟩
  | .forallE ty b _, d, ⟨ht, hb⟩ =>
    ⟨supports_instantiate1Lift hv ty d ht, supports_instantiate1Lift hv b (d + 1) hb⟩
  | .letE ty val b _, d, ⟨ht, hval, hb⟩ =>
    ⟨supports_instantiate1Lift hv ty d ht, supports_instantiate1Lift hv val d hval,
      supports_instantiate1Lift hv b (d + 1) hb⟩
  | .proj _ _ e, d, he => supports_instantiate1Lift hv e d he

/-- **`Annotates` preserves `Expr.Supports`** (including ζ-reduction of `letE` binders). -/
theorem annotates_supports {K : Ix.Kernel.Key .anon → Prop}
    {e' e : Ix.Kernel.Expr .anon} (h : IxVM.Consistency.Annotates e' e) :
    e.Supports K → e'.Supports K := by
  induction h with
  | bvar | fvar _ _ | sort => intro _; trivial
  | lit => intro h; exact h
  | const => intro hk; exact hk
  | app _ _ ihf iha => intro ⟨hf, ha⟩; exact ⟨ihf hf, iha ha⟩
  | lam _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | forallE _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | proj _ ihe => intro he; exact ihe he
  | letE _ ih =>
    intro ⟨_, hv, hb⟩
    exact ih (supports_instantiate1Lift hv _ 0 hb)

/-- Telescope instantiation (`instPisAtLift`) preserves `Expr.Supports`. -/
theorem supports_instPisAtLift {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (as : List (Ix.Kernel.Expr md)) :
    ∀ {e r : Ix.Kernel.Expr md},
      (∀ a ∈ as, a.Supports K) → e.Supports K →
      Ix.Kernel.Expr.instPisAtLift as e = some r → r.Supports K := by
  induction as with
  | nil =>
    intro e r _ he h
    simp only [Ix.Kernel.Expr.instPisAtLift, Option.some.injEq] at h
    rwa [← h]
  | cons a as ih =>
    intro e r has he h
    cases e with
    | forallE _ body _ =>
      exact ih (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (supports_instantiate1Lift (has a List.mem_cons_self) body 0 he.2) h
    | _ => cases h

/-- `structProjBodiesGo` produces exactly `k` field bodies, each satisfying `Expr.Supports K`. -/
theorem supports_structProjBodiesGo {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (T : Ix.Kernel.Key md) (k : Nat) :
    ∀ (i : Nat) {r : Ix.Kernel.Expr md} {bs : List (Ix.Kernel.Expr md)},
      r.Supports K → Ix.Kernel.structProjBodiesGo T k i r = some bs →
      bs.length = k ∧ ∀ b ∈ bs, b.Supports K := by
  induction k with
  | zero =>
    intro _ _ bs _ h
    simp only [Ix.Kernel.structProjBodiesGo, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hm => nomatch hm⟩
  | succ k ih =>
    intro i r bs hr h
    cases r with
    | forallE fdom body _ =>
      obtain ⟨hfdom, hbody⟩ := hr
      simp only [Ix.Kernel.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨bs₀, hgo, rfl⟩ := h
      have harg : (Ix.Kernel.structProjArgP T i).Supports K := trivial
      obtain ⟨hlen, hall⟩ :=
        ih (i + 1) (supports_instantiate1Lift harg body 0 hbody) hgo
      refine ⟨by simp [hlen], fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | htl
      · exact hfdom
      · exact hall b htl
    | _ => cases h

/-- **`structProjBodies` specification**: returns `nF` field bodies, each inheriting `Expr.Supports K`
from the constructor's type `cty`. -/
theorem supports_structProjBodies {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (T : Ix.Kernel.Key md) (nP nF : Nat) {cty : Ix.Kernel.Expr md}
    {bodies : Array (Ix.Kernel.Expr md)}
    (hcty : cty.Supports K)
    (hbodies : Ix.Kernel.structProjBodies T nP nF cty = some bodies) :
    bodies.size = nF ∧ ∀ b ∈ bodies.toList, b.Supports K := by
  unfold Ix.Kernel.structProjBodies at hbodies
  cases hinst : Ix.Kernel.Expr.instPisAtLift (Ix.Kernel.structProjPs nP) cty with
  | none => rw [hinst] at hbodies; cases hbodies
  | some r =>
    rw [hinst, Option.map_eq_some_iff] at hbodies
    obtain ⟨bs, hgo, rfl⟩ := hbodies
    have hps : ∀ a ∈ Ix.Kernel.structProjPs (md := md) nP, a.Supports K := by
      intro a ha
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
      trivial
    have hr := supports_instPisAtLift (Ix.Kernel.structProjPs nP) hps hcty hinst
    obtain ⟨hlen, hall⟩ := supports_structProjBodiesGo T nF 0 hr hgo
    simpa using ⟨hlen, hall⟩

/-- Support required by the final model for one selected stored constant. -/
def SupportedConstant (K : Ix.Kernel.Key .anon → Prop)
    (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  K ci.name ∧ ci.toConstantVal.type.Supports K ∧
    match ci with
    | .defnInfo _ value _ => value.Supports K
    | .recInfo _ _ _ rules => ∀ rl ∈ rules, rl.rhs.Supports K
    | _ => True

private theorem forall₂_support_mem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hm => nomatch hm
  | _, _, .cons hr htail, x, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hxy⟩ := forall₂_support_mem htail x hm
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

/-- Installing annotations cannot introduce an unsupported constant or literal dependency. -/
theorem storedAs_supports {K : Ix.Kernel.Key .anon → Prop}
    {ci ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hst : IxVM.Consistency.StoredAs ci ci₀) (hs : SupportedConstant K ci₀) :
    SupportedConstant K ci := by
  refine ⟨?_, annotates_supports hst.1.2.2 hs.2.1, ?_⟩
  · rw [hst.name_eq]
    exact hs.1
  · cases ci with
    | defnInfo cv value hint =>
      cases ci₀ with
      | defnInfo cv₀ value₀ hint₀ => exact annotates_supports hst.2.1 hs.2.2
      | _ => exact hst.2.elim
    | recInfo cv mI rP rules =>
      cases ci₀ with
      | recInfo cv₀ mI₀ rP₀ rules₀ =>
        intro rl hrl
        obtain ⟨rl₀, hrl₀, hstored⟩ := forall₂_support_mem hst.2.2.2 rl hrl
        exact annotates_supports hstored.2.2 (hs.2.2 rl₀ hrl₀)
      | _ => exact hst.2.elim
    | _ => trivial

end IxVM.Refinement.Assembly
