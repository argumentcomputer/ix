import Ix.CompileCert.Pj.Graded

/-!
# M7 L3-pj: Π-telescopes in the model

The generic induction reader (`Pj/RecRead.lean`) reads an installed recursor's type as a chain of
Π-telescopes. This module holds what the reader's soundness needs about telescopes, generically:

* `piJoin` (a telescope from its binders) and its round trip with IxC's `Expr.stripPis`;
* `denotes_unlift`: the converse of the lane's `denotes_lift` (a lifted term read at the larger
  valuation is the original read at the smaller one), so syntactic lifts of installed pieces can be
  read both ways;
* `tele_inhabited`: a telescope's reading is inhabited when its body's reading is, at every typed
  tuple of the binders (either regime);
* `tele_predicate`: a telescope ending in `Sort s` with graph-regime binders and `s` at `0` holds,
  for **any** meta-level predicate `Q` on the binders' values, a member whose application to every
  typed tuple is `truthVal (Q tuple)` (X2's `predMotive`, for any number of binders: indexed
  motives).
-/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (InstalledTelescope pushArguments ValuationLift)

universe u

/-! ## Telescopes as binder lists -/

/-- The Π-telescope over `bs` (outermost first) with body `b`. -/
def piJoin : List (Kernel.Expr × Kernel.BinderMeta) → Kernel.Expr → Kernel.Expr
  | [], b => b
  | (t, m) :: bs, b => .forallE t (piJoin bs b) m

theorem stripPis_piJoin : ∀ (bs : List (Kernel.Expr × Kernel.BinderMeta)) (b : Kernel.Expr),
    (piJoin bs b).stripPis bs.length = some (bs, b)
  | [], b => rfl
  | (t, m) :: bs, b => by
    simp only [piJoin, List.length_cons, Kernel.Expr.stripPis, stripPis_piJoin bs b, Option.map_some]

theorem piJoin_of_stripPis : ∀ (n : Nat) (e : Kernel.Expr) (bs : List (Kernel.Expr × Kernel.BinderMeta))
    (b : Kernel.Expr), e.stripPis n = some (bs, b) → e = piJoin bs b ∧ bs.length = n
  | 0, e, bs, b, h => by
    simp only [Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, e, bs, b, h => by
    cases e with
    | forallE t body m =>
      simp only [Kernel.Expr.stripPis] at h
      cases hs : body.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        obtain ⟨bs', b'⟩ := p
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, hl⟩ := piJoin_of_stripPis n body bs' b' hs
        exact ⟨rfl, by simp [hl]⟩
    | _ => simp [Kernel.Expr.stripPis] at h

theorem piJoin_append (bs cs : List (Kernel.Expr × Kernel.BinderMeta)) (b : Kernel.Expr) :
    piJoin (bs ++ cs) b = piJoin bs (piJoin cs b) := by
  induction bs with
  | nil => rfl
  | cons p bs ih => obtain ⟨t, m⟩ := p; simp [piJoin, ih]

section Reading

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- **Unlifting**: a lifted term read at the larger valuation is the term read at the smaller one
(the converse of the lane's `denotes_lift`). -/
theorem denotes_unlift (amount : Nat) : ∀ (e : Kernel.Expr) {cutoff : Nat} {ρ target : Nat → V}
    {X : V}, ValuationLift amount cutoff ρ target →
    Kernel.Denotes cval env φ target (e.liftLooseBVars amount cutoff) X →
    Kernel.Denotes cval env φ ρ e X := by
  intro e
  induction e with
  | bvar i =>
    intro cutoff ρ target X rel h
    have hr := rel i
    by_cases hc : i ≥ cutoff
    · simp only [hc, ↓reduceIte] at hr
      have : X = target (i + amount) := by
        have h' : Kernel.Denotes cval env φ target (.bvar (i + amount)) X := by
          simpa [Kernel.Expr.liftLooseBVars, hc] using h
        exact Bridge.denotes_bvar_inv h'
      rw [this, hr]; exact .bvar
    · simp only [hc, ↓reduceIte] at hr
      have : X = target i := by
        have h' : Kernel.Denotes cval env φ target (.bvar i) X := by
          simpa [Kernel.Expr.liftLooseBVars, hc] using h
        exact Bridge.denotes_bvar_inv h'
      rw [this, hr]; exact .bvar
  | fvar i t _ => intro cutoff ρ target X rel h; cases h
  | sort l => intro cutoff ρ target X rel h; cases h; exact .sort
  | const n us => intro cutoff ρ target X rel h; cases h with | const hf hlen => exact .const hf hlen
  | app f a ihf iha =>
    intro cutoff ρ target X rel h
    cases h with
    | app hf ha => exact .app (ihf rel hf) (iha rel ha)
  | lam t b m iht ihb =>
    intro cutoff ρ target X rel h
    cases h with
    | lam hA hF hP =>
      exact .lam (iht rel hA) (fun x hx => ihb (rel.push x) (hF x hx)) hP
  | forallE t b m iht ihb =>
    intro cutoff ρ target X rel h
    cases h with
    | pi hA hB hP =>
      exact .pi (iht rel hA) (fun x hx => ihb (rel.push x) (hB x hx)) hP
  | letE t v b _ _ _ => intro cutoff ρ target X rel h; cases h
  | lit l =>
    intro cutoff ρ target X rel h
    have h' : Kernel.Denotes cval env φ target (.lit l) X := by
      simpa [Kernel.Expr.liftLooseBVars] using h
    cases h' with
    | natLit hn =>
      exact .natLit (Ix.CompileCert.denotes_valuation hn
        (Kernel.natLitToConstructor_looseBVars _) (fun _ h => absurd h (Nat.not_lt_zero _)))
    | strLit hs =>
      exact .strLit (Ix.CompileCert.denotes_valuation hs
        (Kernel.strLitToConstructor_looseBVars _ _) (fun _ h => absurd h (Nat.not_lt_zero _)))
  | proj s i e ih =>
    intro cutoff ρ target X rel h
    cases h with
    | proj_table ht he => exact .proj_table ht (ih rel he)
    | proj_fst ht he => exact .proj_fst ht (ih rel he)
    | proj_snd ht he => exact .proj_snd ht (ih rel he)

/-! ## Inhabited telescopes -/

/-- A telescope's reading is inhabited when, at every typed tuple of its binders, its body's
reading is (either regime). -/
theorem tele_inhabited : ∀ (bs : List (Kernel.Expr × Kernel.BinderMeta)) {b : Kernel.Expr}
    {ρ : Nat → V} {T : V}, Kernel.Denotes cval env φ ρ (piJoin bs b) T →
    (∀ args finalρ, args.length = bs.length →
      InstalledTelescope cval env φ ρ (piJoin bs b) args finalρ b →
      ∃ B, Kernel.Denotes cval env φ finalρ b B ∧ ∃ y, y ∈ˢ B) →
    ∃ y, y ∈ˢ T
  | [], b, ρ, T, hT, h => by
    obtain ⟨B, hB, y, hy⟩ := h [] ρ rfl .nil
    rw [Kernel.Denotes_functional hT hB]; exact ⟨y, hy⟩
  | (t, m) :: bs, b, ρ, T, hT, h => by
    obtain ⟨A, B, hA, hB, -, rfl⟩ := Bridge.denotes_pi_inv hT
    refine Bridge.piR_inhabited fun x hx => tele_inhabited bs (hB x hx) fun args finalρ hl typed =>
      h (x :: args) finalρ (by simp [hl]) (.cons hA hx typed)

/-- The members of a telescope's reading, applied to a typed tuple, land in the body's reading. -/
theorem tele_apply {bs : List (Kernel.Expr × Kernel.BinderMeta)} {b : Kernel.Expr}
    {ρ finalρ : Nat → V} {T f : V} {args : List V}
    (hT : Kernel.Denotes cval env φ ρ (piJoin bs b) T) (hf : f ∈ˢ T)
    (typed : InstalledTelescope cval env φ ρ (piJoin bs b) args finalρ b)
    (_hl : args.length = bs.length) :
    ∃ B, Kernel.Denotes cval env φ finalρ b B ∧ args.foldl app f ∈ˢ B := by
  obtain ⟨B, hB, hm⟩ := typed.apply hT hf
  exact ⟨B, hB, hm⟩

/-- **Predicates as members of a sort-valued telescope.** For a telescope ending in `Sort s` whose
binders are all in the graph regime and whose `s` reads `0`, every meta-level predicate on the
binders' values has a member whose application to every typed tuple is the predicate's truth
value. -/
theorem tele_predicate : ∀ (bs : List (Kernel.Expr × Kernel.BinderMeta)) {s : Kernel.Level}
    {ρ : Nat → V} {T : V},
    (∀ p ∈ bs, Kernel.regime φ p.2.pw ≠ 0) → Kernel.Level.eval φ s = 0 →
    Kernel.Denotes cval env φ ρ (piJoin bs (.sort s)) T →
    ∀ Q : List V → Prop, ∃ M, M ∈ˢ T ∧ ∀ args finalρ,
      InstalledTelescope cval env φ ρ (piJoin bs (.sort s)) args finalρ (.sort s) →
      args.length = bs.length → args.foldl app M = truthVal (Q args)
  | [], s, ρ, T, _, hs, hT, Q => by
    rw [show T = univ 0 by rw [Bridge.denotes_sort_inv hT, hs]]
    refine ⟨truthVal (Q []), by rw [univ_zero]; exact truthVal_mem_univZero _, ?_⟩
    intro args finalρ _ hl
    cases args with
    | nil => rfl
    | cons _ _ => simp at hl
  | (t, m) :: bs, s, ρ, T, hreg, hs, hT, Q => by
    obtain ⟨A, B, hA, hB, -, rfl⟩ := Bridge.denotes_pi_inv hT
    have hr : Kernel.regime φ m.pw ≠ 0 := hreg (t, m) (List.mem_cons_self ..)
    have hreg' : ∀ p ∈ bs, Kernel.regime φ p.2.pw ≠ 0 := fun p hp => hreg p (List.mem_cons_of_mem _ hp)
    have hex : ∀ x, x ∈ˢ A → ∃ M, M ∈ˢ B x ∧ ∀ args finalρ,
        InstalledTelescope cval env φ (Kernel.push x ρ) (piJoin bs (.sort s)) args finalρ (.sort s) →
        args.length = bs.length → args.foldl app M = truthVal (Q (x :: args)) :=
      fun x hx => tele_predicate bs hreg' hs (hB x hx) (fun as => Q (x :: as))
    classical
    let F : V → V := fun x => if hx : x ∈ˢ A then Classical.choose (hex x hx) else empty
    have hF : ∀ x (hx : x ∈ˢ A), F x = Classical.choose (hex x hx) := fun x hx => by
      simp only [F, hx, ↓reduceDIte]
    refine ⟨lamR (Kernel.regime φ m.pw) A F, lamR_mem fun x hx => ?_, ?_⟩
    · rw [hF x hx]; exact (Classical.choose_spec (hex x hx)).1
    · intro args finalρ typed hl
      cases typed with
      | @cons _ _ _ _ x A' args' _ _ hA' hx rest =>
        obtain rfl := Kernel.Denotes_functional hA' hA
        simp only [List.foldl_cons]
        rw [app_lamR_pos hr hx, hF x hx]
        exact (Classical.choose_spec (hex x hx)).2 args' finalρ rest (by simpa using hl)

end Reading

end Ix.CompileCert.Pj
