module

public import ConLeche.Model.IndGrade
import ConLeche.Model.Annot.BitInst
public section

/-!
# The instantiated domains are graded (task #161, IND TIER part 4)

The second half of the part-4 grading bill, and the one that is
**genuinely new content** rather than a transposition.

`defEqAt_of_run` fires a recorded comparison only against *both*
sides' gradings.  Every iota walk compares a statement-frame opener's
annotation against a domain of an `instPisAt` run — the recursor's
prefix domains (`rdoms`), the constructor's field domains (`cdoms`),
the rule's λ-domains (`ldomsL`).  The **a**-side is a slot of the
stored `iota_j` theorem's own tower and is graded by `hokA_padded`.
The **b**-side is a slot of a *different* stored type's tower,
instantiated at the statement frame, and nothing in the checker's run
record types it: `checkIotaThm` compares domains with `checkDefEqList`
and never infers them (`Inductives/Modeled.lean:109-135`), so the P tier's
general grading producer — `InferClaim` from an `inferTypeCore`
run — has nothing to consume.

So the b-side's grading has to come from its **own type's** tower, and
this file is the lemma that walks it: an `instPisAt` run's domains are
graded whenever the type's reading is, the spine's readings are, and
each spine element's value inhabits the domain it is substituted into.
The last premise is the load-bearing one and is where the walks come
back in — which is why the stage that consumes this runs an induction
on the frame position, spending the equality at position `i` to earn
the grading at position `i + 1`.

**Why the spine premise is cheap where it is used.**  On a `.plain`
fire every spine element is a frame *opener*, and an opener reads to a
`.bvar` (`denoteMeta_fvar`), which is graded by definition — so the
`WellDenotedV` premise costs nothing there.  On a `.nested` fire the spine
is the instantiated pins, and `RecRuleLaw` already carries their open
readings **graded** (the ratified iota-seal repair, `Annot/EnvModelM.lean`)
— the conjunct that was added for the pins' own sake turns out to be
exactly what this lemma asks for.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The `.pi` split, in the P currency -/

/-- A `.pi` reading's domain is graded when the reading is. -/
theorem WellDenotedV_pi_dom {ρ : Nat → V} {u v : Nat} {A B : AnnotTerm}
    (h : WellDenotedV V ρ (.pi u v A B)) : WellDenotedV V ρ A :=
  ⟨((WellDenoted_pi V ρ u v A B) ▸ h.1).1,
    ((AnnotValid_pi V ρ u v A B) ▸ h.2).1⟩

/-- A `.pi` reading's body is graded at every extension by an element
of the domain. -/
theorem WellDenotedV_pi_body {ρ : Nat → V} {u v : Nat} {A B : AnnotTerm}
    (h : WellDenotedV V ρ (.pi u v A B)) {x : V}
    (hx : x ∈ˢ interp V ρ A) : WellDenotedV V (cons x ρ) B :=
  ⟨((WellDenoted_pi V ρ u v A B) ▸ h.1).2 x hx,
    ((AnnotValid_pi V ρ u v A B) ▸ h.2).2.1 x hx⟩

/-! ## The instantiated domains -/

set_option maxHeartbeats 1600000 in
/-- **An `instPisAt` run's domains are graded**, given the type's own
grading, the spine's gradings, and — the load-bearing premise — that
each spine element's value inhabits the domain it goes into.

The induction is the checker's own order: the head domain is the
type's `.pi` domain, and the tail is the run on the β-reduct, whose
reading is the body's reading substituted (`denoteMeta_beta`) and whose
grading is `WellDenotedV_inst0` at the head membership.

**The membership premise is bounded by the index** (task #161, ind
tier part 5).  Part 4 stated it over the *whole* spine, which is what
the prefix branch happens to have; the field branch does not and
cannot — the position induction earns position `i`'s grading from the
equalities at positions `< i`, and a premise over the whole spine
would ask it for the equalities it has not proved yet.  The proof
never needed more: descending past the head spends exactly the head's
membership, so the bound `i₀ < i` is the induction's own. -/
theorem instPisAt_doms_graded {ρ' : Nat → V}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat} {T : AnnotTerm} (i : Nat),
      (∀ (i₀ : Nat) (x : Expr), i₀ ≤ i → sp[i₀]? = some x →
        Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      denoteMeta acval env φ D ty = some T →
      WellDenotedV V ρ' T →
      (∀ (i₀ : Nat) (x : Expr), i₀ < i → sp[i₀]? = some x →
        ∃ w, denoteMeta acval env φ D x = some w ∧ WellDenotedV V ρ' w ∧
          ∀ dw, denoteMeta acval env φ D (ds.getD i₀ default) = some dw →
            interp V ρ' w ∈ˢ interp V ρ' dw) →
      i < sp.length → ∀ dw : AnnotTerm,
        denoteMeta acval env φ D (ds.getD i default) = some dw →
        WellDenotedV V ρ' dw := by
  intro sp
  induction sp with
  | nil => intro ty ds rs h D T i _ _ _ _ _ _ hi; exact absurd hi (by simp)
  | cons a sp ih =>
    intro ty ds rs h D T i hsp hfb hb hT hokT hmem hi
    obtain ⟨hwsa, hba⟩ := hsp 0 a (Nat.zero_le _) rfl
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      rw [denoteMeta_forallE] at hT
      cases hA : denoteMeta acval env φ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denoteMeta acval env φ (D + 1)
          (body.instantiate1 (.fvar D dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      rw [hB] at hT
      obtain rfl : T = .pi 0 (pwBit φ mb.pw) A B :=
        (Option.some.inj hT).symm
      have hdom0 : (dom :: p.1).getD 0 default = dom := rfl
      match i with
      | 0 =>
        intro dw hdw
        rw [hdom0, hA] at hdw
        obtain rfl := Option.some.inj hdw
        exact WellDenotedV_pi_dom hokT
      | i + 1 =>
        intro dw hdw
        obtain ⟨w, hw, hokw, hmem0⟩ := hmem 0 a (by omega) rfl
        -- the head domain
        have hmemA : interp V ρ' w ∈ˢ interp V ρ' A :=
          hmem0 A (by rw [hdom0]; exact hA)
        -- the tail: the run on the β-reduct
        have hTI : denoteMeta acval env φ D (body.instantiate1 a)
            = some (B.inst w 0) := by
          rw [denoteMeta_beta hacl hainst (ty := dom) hfb'.2
            hwsa hba hw 0, hB]
          rfl
        have hokBI : WellDenotedV V ρ' (B.inst w 0) :=
          (WellDenotedV_inst0 hokw).mpr (WellDenotedV_pi_body hokT hmemA)
        refine ih h1 i
          (fun i₀ x hle hx => hsp (i₀ + 1) x (by omega) (by simpa using hx))
          (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
          (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2)
          hTI hokBI ?_ (by simpa using hi) dw (by simpa using hdw)
        intro i₀ x hlt hx
        obtain ⟨w0, hw0, hok0, hm0⟩ :=
          hmem (i₀ + 1) x (by omega) (by simpa using hx)
        exact ⟨w0, hw0, hok0, fun dw0 hdw0 =>
          hm0 dw0 (by simpa using hdw0)⟩

set_option maxHeartbeats 1600000 in
/-- **An `instPisAt` run's residual is graded** — the same descent as
`instPisAt_doms_graded`, read off at the end instead of at an index.
The membership premise is over the whole spine here, and that costs
nothing: the residual comes *after* every position, so a consumer of
this lemma has already earned them all (task #161, ind tier part 5 —
the point stage's index walk compares the residual's own
arguments). -/
theorem instPisAt_res_graded {ρ' : Nat → V}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat} {T : AnnotTerm},
      (∀ (i : Nat) (x : Expr), sp[i]? = some x →
        Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      denoteMeta acval env φ D ty = some T →
      WellDenotedV V ρ' T →
      (∀ (i : Nat) (x : Expr), sp[i]? = some x →
        ∃ w, denoteMeta acval env φ D x = some w ∧ WellDenotedV V ρ' w ∧
          ∀ dw, denoteMeta acval env φ D (ds.getD i default) = some dw →
            interp V ρ' w ∈ˢ interp V ρ' dw) →
      ∀ rw : AnnotTerm, denoteMeta acval env φ D rs = some rw →
        WellDenotedV V ρ' rw := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D T _ _ _ hT hokT _ rw hrw
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [hT] at hrw
    obtain rfl := Option.some.inj hrw
    exact hokT
  | cons a sp ih =>
    intro ty ds rs h D T hsp hfb hb hT hokT hmem rw hrw
    obtain ⟨hwsa, hba⟩ := hsp 0 a rfl
    obtain ⟨w, hw, hokw, hmem0⟩ := hmem 0 a rfl
    match ty, h with
    | .forallE dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      rw [denoteMeta_forallE] at hT
      cases hA : denoteMeta acval env φ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denoteMeta acval env φ (D + 1)
          (body.instantiate1 (.fvar D dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      rw [hB] at hT
      obtain rfl : T = .pi 0 (pwBit φ mb.pw) A B :=
        (Option.some.inj hT).symm
      have hdom0 : (dom :: p.1).getD 0 default = dom := rfl
      have hmemA : interp V ρ' w ∈ˢ interp V ρ' A :=
        hmem0 A (by rw [hdom0]; exact hA)
      have hTI : denoteMeta acval env φ D (body.instantiate1 a)
          = some (B.inst w 0) := by
        rw [denoteMeta_beta hacl hainst (ty := dom) hfb'.2
          hwsa hba hw 0, hB]
        rfl
      have hokBI : WellDenotedV V ρ' (B.inst w 0) :=
        (WellDenotedV_inst0 hokw).mpr (WellDenotedV_pi_body hokT hmemA)
      refine ih h1 (fun i x hx => hsp (i + 1) x (by simpa using hx))
        (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
        (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2)
        hTI hokBI ?_ rw hrw
      intro i x hx
      obtain ⟨w0, hw0, hok0, hm0⟩ := hmem (i + 1) x (by simpa using hx)
      exact ⟨w0, hw0, hok0, fun dw0 hdw0 => hm0 dw0 (by simpa using hdw0)⟩

/-! ## Application spines, graded backwards

`wellDenotedV_mkAppN_of_fitA` (`Steps/IotaKit.lean`) builds an
application's grading from a fit; the point stage needs the *inverse*,
because the index walk compares arguments of a spine whose whole
grading it already has (the checker's own `inferTypeCore` verdict on
the statement's left-hand side).  `WellDenoted`/`AnnotValid` are
conjunctive at `.app`, so both directions are one projection. -/

/-- An application's function part is graded when the application
is. -/
theorem WellDenotedV_app_fn {ρ : Nat → V} {g a : AnnotTerm}
    (h : WellDenotedV V ρ (.app g a)) : WellDenotedV V ρ g :=
  ⟨((WellDenoted_app V ρ g a) ▸ h.1).1, ((AnnotValid_app V ρ g a) ▸ h.2).1⟩

/-- An application's argument is graded when the application is. -/
theorem WellDenotedV_app_arg {ρ : Nat → V} {g a : AnnotTerm}
    (h : WellDenotedV V ρ (.app g a)) : WellDenotedV V ρ a :=
  ⟨((WellDenoted_app V ρ g a) ▸ h.1).2.1,
    ((AnnotValid_app V ρ g a) ▸ h.2).2⟩

/-- The head of a graded application spine is graded. -/
theorem WellDenotedV_mkAppN_head {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {g : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN g as) → WellDenotedV V ρ g := by
  intro as
  induction as with
  | nil => intro g h; exact h
  | cons x xs ih => intro g h; exact WellDenotedV_app_fn (ih (g := .app g x) h)

/-- **Every argument of a graded application spine is graded.** -/
theorem WellDenotedV_mkAppN_args {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {g : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN g as) → ∀ a ∈ as, WellDenotedV V ρ a := by
  intro as
  induction as with
  | nil => intro g _ a ha; exact nomatch ha
  | cons x xs ih =>
    intro g h a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact WellDenotedV_app_arg (WellDenotedV_mkAppN_head xs h)
    · exact ih (g := .app g x) h a ha'

end ConLeche.Model
