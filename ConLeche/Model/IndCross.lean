module

public import ConLeche.Model.IndStageKit
public import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Annot.BitInst

public section

/-!
# The cross-frame instantiation, at the reading (task #161, part 4)

`instPisAt_fvar_denote_defined` and `instPisAt_denote_cross`
(`Verify/Denote/IndFrame.lean`) at `denoteMeta`/`AnnotTerm` — the two facts
the zipper's **field** branch turns on.

The situation they describe is the one the modeled-iota kit is built
around: the checker instantiates the constructor's type at a run of
*scattered* frame variables (parameter positions and field positions
interleaved, at any indices below the frame), and the stage must read
the resulting domain list against the constructor tower's own domains
at the **mixed** value spine.  `instPisAt_denoteMeta_cross` is the
identity that crosses them.

Both are **V-free**: they are statements about `denoteMeta` and
`AnnotTerm.instSeq` only, with no `SetTheory` in sight, so they take the
carrier's two leaf equations (`acval_closed`, the `inst` analogue)
rather than an `EnvModel`.  That is also why they transpose move for
move — the only currency deltas are `AnnotTerm.instSeq` for
`Term.instSeq` and the binder numerals `denoteMeta_forallE` puts on the
`.pi` node, which `PiTeleAV.cons` carries without reading.

The `Expr`-only halves of v1's kit — `instPisAt_length`,
`instPisAt_take`, `instPisAt_leaves` — are **reused verbatim**: they
mention no valuation at all, so there is nothing to transpose.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name BinderMeta)

universe w

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- **The residual of an `instPisAt` run reads** when the type and
every spine element do (`instPisAt_fvar_denote_defined`). -/
theorem instPisAt_denoteMeta_defined
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat},
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        (∃ w, denoteMeta acval env φ D x = some w) ∧ Expr.WScoped D x ∧
          x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      ∀ {T : AnnotTerm}, denoteMeta acval env φ D ty = some T →
      ∃ vRs, denoteMeta acval env φ D rs = some vRs := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D _ _ _ T hT
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨T, hT⟩
  | cons a sp ih =>
    intro ty ds rs h D hsp hfb hb T hT
    obtain ⟨⟨w0, hw0⟩, hwsa, hba⟩ := hsp 0 a rfl
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
      have hTI : denoteMeta acval env φ D (body.instantiate1 a)
          = some (B.inst w0 0) := by
        rw [denoteMeta_beta hacl hainst (ty := dom) hfb'.2 hwsa
          hba hw0 0, hB]
        rfl
      exact ih h1
        (fun j x hx => hsp (j + 1) x (by simpa using hx))
        (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
        (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2) hTI

set_option maxHeartbeats 1600000 in
/-- **The cross-frame instantiation, at the reading**
(`instPisAt_denote_cross`).  An `instPisAt` run at scattered frame
variables, read at the frame and instantiated along the frame's full
value spine, is the walk of the (spine-instantiated) read tower at the
values the openers map to. -/
theorem instPisAt_denoteMeta_cross
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat} {vals : List AnnotTerm}, vals.length = D →
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      ∀ {T : AnnotTerm}, denoteMeta acval env φ D ty = some T →
      ∀ {vRs : AnnotTerm}, denoteMeta acval env φ D rs = some vRs →
      ∀ {ws : List AnnotTerm}, ws.length = sp.length →
      (∀ (j : Nat) (x : Expr), sp[j]? = some x →
        ∃ w0, denoteMeta acval env φ D x = some w0 ∧
          ws[j]? = some (AnnotTerm.instSeq vals (D - 1) w0)) →
      ∀ {Γ : List AnnotTerm} {R : AnnotTerm},
        PiTeleAV sp.length (AnnotTerm.instSeq vals (D - 1) T) Γ R →
        AnnotTerm.instSeq vals (D - 1) vRs
          = AnnotTerm.instSeq ws (ws.length - 1) R := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h D vals hvlen hsp hfb hb T hT vRs hRs ws hwlen hws
      Γ R hp
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl : T = vRs := by rw [hT] at hRs; exact Option.some.inj hRs
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hwlen
    cases hp
    rfl
  | cons a sp ih =>
    intro ty ds rs h D vals hvlen hsp hfb hb T hT vRs hRs ws hwlen hws
      Γ R hp
    obtain ⟨hwsa, hba⟩ := hsp 0 a rfl
    obtain ⟨w0, hw0den, hw0⟩ := hws 0 a rfl
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
      have hbeta := denoteMeta_beta hacl hainst (ty := dom)
        hfb'.2 hwsa hba hw0den 0
      match ws, hwlen with
      | w :: ws', hwlen => ?_
      have hw : w = AnnotTerm.instSeq vals (D - 1) w0 := by
        simpa using hw0
      rw [show AnnotTerm.instSeq vals (D - 1)
            (AnnotTerm.pi 0 (pwBit φ mb.pw) A B)
          = .pi 0 (pwBit φ mb.pw) (AnnotTerm.instSeq vals (D - 1) A)
              (AnnotTerm.instSeq vals D B) from by
        rw [instSeqAV_pi _ _ _ _ _ _ (by omega)]
        congr 1
        rcases Nat.eq_zero_or_pos D with h0 | h0
        · obtain rfl : vals = [] := by
            rw [h0] at hvlen
            exact List.eq_nil_of_length_eq_zero hvlen
          rfl
        · rw [show D - 1 + 1 = D from by omega]] at hp
      cases hp with
      | @cons _ _ _ _ _ _ Γ' hp' => ?_
      have hfbI : Expr.fvarsBelow D (body.instantiate1 a) :=
        Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2
      have hbI : (body.instantiate1 a).looseBVarsBounded 0 = true :=
        Expr.looseBVarsBounded_instantiate1_gen hba hb'.2
      have hTI : denoteMeta acval env φ D (body.instantiate1 a)
          = some (B.inst w0 0) := by
        rw [hbeta, hB]
        rfl
      have hp2 := hp'.inst w 0
      rw [Nat.zero_add] at hp2
      have hrec := ih h1 hvlen
        (fun j x hx => hsp (j + 1) x (by simpa using hx))
        hfbI hbI hTI hRs (by simpa using hwlen)
        (fun j x hj => by
          obtain ⟨w1, hd1, hg1⟩ := hws (j + 1) x (by simpa using hj)
          exact ⟨w1, hd1, by simpa using hg1⟩)
        (Γ := ctxInstAtAV w 0 Γ') (R := R.inst w sp.length) ?_
      · have hlen' : ws'.length = sp.length := by simpa using hwlen
        rw [hrec, show (w :: ws').length - 1 = ws'.length from by simp,
          AnnotTerm.instSeq_cons, hlen']
      · have hID : AnnotTerm.instSeq vals (D - 1) (B.inst w0 0)
            = (AnnotTerm.instSeq vals D B).inst w 0 := by
          rcases Nat.eq_zero_or_pos D with h0 | h0
          · obtain rfl : vals = [] := by
              rw [h0] at hvlen
              exact List.eq_nil_of_length_eq_zero hvlen
            simp only [AnnotTerm.instSeq_nil] at hw ⊢
            rw [hw]
          · rw [instSeqAV_inst0 vals (D - 1) B w0 (by omega),
              show D - 1 + 1 = D from by omega, ← hw]
        rw [hID]
        exact hp2

/-! ## Sharpening the scope

`denoteMeta_lift` takes `WScoped` where v1's `denote_lift` takes
`fvarsBelow` — the annotations have to be scoped too, hereditarily
(`Annot/BitInst.lean`'s own note).  So every place v1's stages sharpen
a *bound* from the leaves, the P stages have to sharpen a `WScoped`,
and this is the lemma that does it: `WScoped` mentions its depth in
exactly one place, the leaf index bounds, so a term already scoped at
some depth is scoped at any depth its leaves fit under.

This is the P-side cost of the reading's stronger scope discipline,
and it is one induction. -/

/-- **`WScoped` sharpens along the leaves**: the depth appears only in
the leaf index bounds, so a scoped term is scoped at any bound its
leaves respect. -/
theorem WScoped_sharpen : ∀ {e : Expr} {d d' : Nat}, Expr.WScoped d e →
    (∀ l ∈ e.fvarLeaves, l.1 < d') → Expr.WScoped d' e := by
  intro e
  induction e with
  | bvar i => intro d d' _ _; simp [Expr.WScoped]
  | sort u => intro d d' _ _; simp [Expr.WScoped]
  | const c us => intro d d' _ _; simp [Expr.WScoped]
  | lit l => intro d d' _ _; simp [Expr.WScoped]
  | fvar idx ty _ih =>
    intro d d' h hl
    simp only [Expr.WScoped] at h ⊢
    exact ⟨hl (idx, ty) (by simp [Expr.fvarLeaves]), h.2⟩
  | app f a ihf iha =>
    intro d d' h hl
    simp only [Expr.WScoped] at h ⊢
    exact ⟨ihf h.1 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl'])),
      iha h.2 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl']))⟩
  | lam ty body mb ihty ihbody =>
    intro d d' h hl
    simp only [Expr.WScoped] at h ⊢
    exact ⟨ihty h.1 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl'])),
      ihbody h.2 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl']))⟩
  | forallE ty body mb ihty ihbody =>
    intro d d' h hl
    simp only [Expr.WScoped] at h ⊢
    exact ⟨ihty h.1 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl'])),
      ihbody h.2 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl']))⟩
  | letE ty val body ihty ihval ihbody =>
    intro d d' h hl
    simp only [Expr.WScoped] at h ⊢
    exact ⟨ihty h.1 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl'])),
      ihval h.2.1 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl'])),
      ihbody h.2.2 (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl']))⟩
  | proj s i e ih =>
    intro d d' h hl
    simp only [Expr.WScoped] at h ⊢
    exact ih h (fun l hl' => hl l (by simp [Expr.fvarLeaves, hl']))

end ConLeche.Model
