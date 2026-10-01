module

public import ConLeche.Model.Inductives.FixData
public import ConLeche.Model.Inductives.FixNoBVar
public section

/-!
# The shadow context: a recursive constructor's entries graded off the
recursive slots (task #188)

The functor of a recursive family is graded at every family `X` over
the index tuples, so a constructor's ordinary domains must be graded at
frames whose recursive slots hold an arbitrary member of `X`'s fibre —
not of the block's own.  The checker's claims grade a reading only at
frames satisfying the context it was inferred in, which pins the
recursive slots to the block's fibre (possibly empty).  What licenses
the transfer is that no ordinary domain (nor the residual) mentions a
recursive variable (`nativeOpenedOk`), so the claims' context can
be the **shadow context** `shadowCtx`: the constructor's context with
every recursive binder replaced by `Sort 0` — a context satisfied by
the point at those slots — which `CtxOk` accepts because it
constrains a context only at the leaves of the term read.  The rows
(`ClaimsAt.sortRow`) at the shadow context grade every entry, and the
residual, at every frame satisfying it (`fixShadowGrading`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The shadow context -/

/-- Binder `b` (the parameters first) is a recursive field. -/
@[expose] def recAt (nP : Nat) (ks : List RecFieldKind) (b : Nat) : Prop :=
  nP ≤ b ∧ (ks.getD (b - nP) .ordinary = .recursive ∨ ks.getD (b - nP) .ordinary = .reflexive)

instance (nP : Nat) (ks : List RecFieldKind) (b : Nat) : Decidable (recAt nP ks b) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- The shadow context: the reversed context `Γ` (list position `p` is
binder `k - 1 - p`) with `Sort 0` at the recursive binders. -/
def shadowCtx (nP : Nat) (ks : List RecFieldKind) (k : Nat) (Γ : List AnnotTerm) : List AnnotTerm :=
  (List.range k).map fun p => if recAt nP ks (k - 1 - p) then .sort 0 else Γ.getD p default

/-- The shadow openers: the opened variables with the recursive ones
annotated by `Sort 0`. -/
def shadowFvs (nP : Nat) (ks : List RecFieldKind) (k : Nat) (fvs : List Expr) : List Expr :=
  (List.range k).map fun i =>
    if recAt nP ks i then Expr.fvar i (.sort .zero) else fvs.getD i default

section Kit

variable {nP k : Nat} {ks : List RecFieldKind} {Γ : List AnnotTerm} {fvs : List Expr}

omit [SetTheory V] in
theorem shadowCtx_length : (shadowCtx nP ks k Γ).length = k := by simp [shadowCtx]

omit [SetTheory V] in
theorem shadowCtx_getElem? {p : Nat} (hp : p < k) :
    (shadowCtx nP ks k Γ)[p]?
      = some (if recAt nP ks (k - 1 - p) then .sort 0 else Γ.getD p default) := by
  simp [shadowCtx, List.getElem?_map, List.getElem?_range hp]

omit [SetTheory V] in
theorem shadowCtx_getD {p : Nat} (hp : p < k) :
    (shadowCtx nP ks k Γ).getD p default
      = if recAt nP ks (k - 1 - p) then .sort 0 else Γ.getD p default := by
  rw [List.getD_eq_getElem?_getD, shadowCtx_getElem? hp]; rfl

omit [SetTheory V] in
/-- Below the parameters the shadow context is the context. -/
theorem shadowCtx_drop_params {b : Nat} (hΓ : Γ.length = k) (hb : b ≤ nP) :
    (shadowCtx nP ks k Γ).drop (k - b) = Γ.drop (k - b) := by
  apply List.ext_getElem?
  intro q
  rw [List.getElem?_drop, List.getElem?_drop]
  by_cases hq : k - b + q < k
  · rw [shadowCtx_getElem? hq, if_neg, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    · rfl
    · intro h
      have := h.1
      omega
  · rw [List.getElem?_eq_none (by rw [shadowCtx_length]; omega),
      List.getElem?_eq_none (by rw [hΓ]; omega)]

omit [SetTheory V] in
theorem shadowFvs_getElem? {i : Nat} (hi : i < k) :
    (shadowFvs nP ks k fvs)[i]?
      = some (if recAt nP ks i then Expr.fvar i (.sort .zero)
          else fvs.getD i default) := by
  simp [shadowFvs, List.getElem?_map, List.getElem?_range hi]

omit [SetTheory V] in
theorem mentionsFvar_false {q : Nat} {e : Expr} (h : e.mentionsFvar q = false) :
    ∀ l ∈ e.fvarLeaves, l.1 ≠ q := by
  intro l hl
  unfold Expr.mentionsFvar at h
  rw [List.any_eq_false] at h
  simpa using h l hl

end Kit

/-! ## The shadow context is a context for a leaf-free term -/

/-- `CtxOk` at the shadow context for a term whose leaves avoid the
recursive variables, from the grading of the non-recursive entries at
the shadow context below it. -/
theorem shadowCtxOk {m : EnvModel V env} {ψ : Name → Nat} {k : Nat} {e : Expr}
    {fvs : List Expr} {o : Expr} {Γ : List AnnotTerm} {R : AnnotTerm}
    (hO : Opened m ψ k e fvs o Γ R) (hlenF : fvs.length = k)
    {nP : Nat} {ks : List RecFieldKind}
    {b : Nat} (hb : b ≤ k) {x : Expr} (hwx : Expr.WScoped b x)
    (hleaf : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hnorec : ∀ l ∈ x.fvarLeaves, ¬ recAt nP ks l.1)
    (hok : ∀ i, i < b → ¬ recAt nP ks i → ∀ ρ : Nat → V,
      Sat V ((shadowCtx nP ks k Γ).drop (k - i)) ρ →
      WellDenotedV V ρ (Γ.getD (k - 1 - i) default)) :
    CtxOk m ψ b ((shadowCtx nP ks k Γ).drop (k - b)) x := by
  have hidx : ∀ i x, fvs[i]? = some x → ∃ ty, x = Expr.fvar i ty :=
    fun i x hx => (hO.var i x hx).1
  -- a leaf's opener sits at its own position
  have hpos : ∀ l ∈ x.fvarLeaves, fvs[l.1]? = some (Expr.fvar l.1 l.2) := by
    intro l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem (hleaf l hl)
    obtain ⟨ty, hx⟩ := hidx p _ hp
    obtain ⟨rfl, -⟩ : l.1 = p ∧ l.2 = ty := by
      injection hx with a b
      exact ⟨a, b⟩
    exact hp
  have hgetD : ∀ j, (hj : j < k) → fvs.getD j default = fvs[j]'(by rw [hlenF]; exact hj) := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenF]; exact hj)]
    rfl
  refine ctxOk_of_openers m.acval_closed (fvs := (shadowFvs nP ks k fvs).take b)
    (Aa := fun j => (shadowCtx nP ks k Γ).getD (k - 1 - j) default)
    (Δa := (shadowCtx nP ks k Γ).drop (k - b))
    (by rw [List.length_drop, shadowCtx_length]; omega) ?_ ?_ ?_ (e := x) (n := b) ?_
    (Expr.fvarLeaves_lt_of_wscoped hwx) ?_ ?_
  · intro j y hy
    have hj : j < b := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj, shadowFvs_getElem? (by omega)] at hy
    obtain rfl := Option.some.inj hy
    split
    · exact ⟨_, rfl⟩
    · rw [hgetD j (by omega)]
      exact hidx j _ (List.getElem?_eq_getElem (by omega))
  · intro y hy
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
    have hji : j < b := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hji, shadowFvs_getElem? (by omega)] at hj
    obtain rfl := Option.some.inj hj
    split
    · simp only [Expr.WScoped]
      exact ⟨hji, trivial⟩
    · rw [hgetD j (by omega)]
      obtain ⟨⟨ty, hx⟩, hw, -, -, -⟩ := hO.var j _ (List.getElem?_eq_getElem (by omega))
      rw [hx] at hw ⊢
      simp only [Expr.fvarTypeD] at hw
      simp only [Expr.WScoped]
      exact ⟨hji, hw⟩
  · intro j y hy
    have hj : j < b := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj, shadowFvs_getElem? (by omega)] at hy
    obtain rfl := Option.some.inj hy
    rw [shadowCtx_getD (by omega), show k - 1 - (k - 1 - j) = j from by omega]
    split
    · simp only [Expr.fvarTypeD]
      rw [denoteMeta]
      rfl
    · rw [hgetD j (by omega)]
      exact hO.doms j _ (List.getElem?_eq_getElem (by omega))
  · intro l hl
    have hlt := Expr.fvarLeaves_lt_of_wscoped hwx l hl
    refine List.mem_of_getElem? (i := l.1) ?_
    rw [List.getElem?_take_of_lt hlt, shadowFvs_getElem? (by omega), if_neg (hnorec l hl),
      List.getD_eq_getElem?_getD, hpos l hl]
    rfl
  · intro j hj
    rw [List.getElem?_drop, show k - b + (b - 1 - j) = k - 1 - j from by omega,
      shadowCtx_getElem? (by omega), shadowCtx_getD (by omega)]
  · intro j hj ρ hρ
    have hd := Sat_drop hρ (b - j)
    rw [List.drop_drop, show k - b + (b - j) = k - j from by omega] at hd
    have e : (fun l => ρ (l + (b - 1 - j) + 1)) = fun l => ρ (l + (b - j)) := by
      funext l; congr 1; omega
    rw [e, shadowCtx_getD (by omega), show k - 1 - (k - 1 - j) = j from by omega]
    split
    · exact ⟨by simp, by simp⟩
    · next hr => exact hok j (by omega) hr _ hd

/-! ## The entries, graded at the shadow context -/

/-- **The shadow grading**: every entry of a recursive constructor's
context is graded at every frame satisfying the shadow context below
it (a non-recursive field entry moreover in the family's universe when
that is not `Prop`), and so is the residual at the full shadow
context. -/
theorem fixShadowGrading (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    (ψ : Name → Nat) :
    (∀ b, b < nP + nF → ∀ ρ : Nat → V,
      Sat V ((shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - b)) ρ →
      WellDenotedV V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default) ∧
      (nP ≤ b → ¬ recAt nP ks b → resSort.eval ψ ≠ 0 →
        interp V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default)
          ∈ˢ (univ (resSort.eval ψ) : V))) ∧
    (∀ ρ : Nat → V, Sat V (shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)) ρ →
      WellDenotedV V ρ (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))) := by
  -- the run's pieces
  obtain ⟨⟨_, hccv⟩, -, fvsP', crest', tfvs, trest, xFvs', idxArgs', hopC, -, -, hopX, -, -, -,
    hsorts⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨crest, hopP, hopXX⟩ := hD.opens
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopC))
  obtain ⟨rfl, hxrest⟩ := Prod.mk.inj (Option.some.inj (hopXX.symm.trans hopX))
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', -, -, hst, hens, hcv⟩ :=
    ConLeche.checkConstantVal_inv hccv
  obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have htyEq : cvCa.type = type' := by rw [hcv]
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  rw [← htyEq] at htf' hbt' hst
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopXX)
  obtain ⟨F', tb, vb, hib, hensb, -, -⟩ := piBits_of_infer hμ (nP + nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  have hO : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll htf' hbt' (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  have hlenAll : (fvsP ++ xFvs).length = nP + nF := by
    rw [List.length_append, hD.pLen, hD.xLen]
  have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by simp [hD.len ψ]
  have hc := claimsAt_of hμ mp ψ F
  -- a recursive variable is a leaf of no later domain nor of the residual
  have hrecGet : ∀ i, recAt nP ks (nP + i) → i < nF → ∃ x, xFvs[i]? = some x ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false := by
    intro i hr hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    rcases hk with hk | hk
    · obtain ⟨-, -, -, -, hlater, hres⟩ := hD.opened.recF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, hlater, hres⟩ := hD.opened.reflF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
  -- the entries, by strong induction on the binder
  have key : ∀ b, b < nP + nF → ∀ ρ : Nat → V,
      Sat V ((shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop (nP + nF - b)) ρ →
      WellDenotedV V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default) ∧
      (nP ≤ b → ¬ recAt nP ks b → resSort.eval ψ ≠ 0 →
        interp V ρ ((((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - b) default)
          ∈ˢ (univ (resSort.eval ψ) : V)) := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
    intro hb ρ hρ
    by_cases hbP : b < nP
    · rw [shadowCtx_drop_params hΓlen (by omega)] at hρ
      exact ⟨hO.okΓ b hb ρ hρ, fun h => absurd hbP (by omega)⟩
    · obtain ⟨fv, ty, u, hfv, -, hi, hens', hleq, -⟩ := hfields (b - nP) (by omega)
      have hfvA : (fvsP ++ xFvs)[b]? = some fv := by
        rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen]
        exact hfv
      obtain ⟨-, hws, hbnd, hL, hleaf⟩ := hO.var b fv hfvA
      rw [show nP + (b - nP) = b from by omega] at hi hens'
      have hnorec : ∀ l ∈ fv.fvarTypeD.fvarLeaves, ¬ recAt nP ks l.1 := by
        intro l hl hr
        have hge := hr.1
        have hlt : l.1 < b := Expr.fvarLeaves_lt_of_wscoped hws l hl
        obtain ⟨x, hx, hlater, -⟩ := hrecGet (l.1 - nP)
          (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
        have hmem : fv ∈ xFvs.drop (l.1 - nP + 1) := by
          refine List.mem_of_getElem? (i := b - nP - (l.1 - nP + 1)) ?_
          rw [List.getElem?_drop, show l.1 - nP + 1 + (b - nP - (l.1 - nP + 1)) = b - nP from by
            omega]
          exact hfv
        exact mentionsFvar_false (hlater fv hmem) l hl (by omega)
      have hC := shadowCtxOk hO hlenAll (nP := nP) (ks := ks) (by omega) hws hleaf hnorec
        (fun i hi' hr ρ' hρ' => (ih i hi' (by omega) ρ' hρ').1)
      have hread := hO.doms b fv hfvA
      have hrow := hc.sortRow hi hens' hws hbnd hL hC hread ρ hρ
      refine ⟨hrow.1, fun _ _ hw => ?_⟩
      by_cases hnp : isProp = true
      · exfalso
        have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hProp hnp)) ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ hrow.2
  refine ⟨key, ?_⟩
  -- the residual
  intro ρ hρ
  have hnorecR : ∀ l ∈ xrest.fvarLeaves, ¬ recAt nP ks l.1 := by
    intro l hl hr
    have hge := hr.1
    have hlt : l.1 < nP + nF := Expr.fvarLeaves_lt_of_wscoped hO.bodyScoped.1 l hl
    obtain ⟨-, -, -, hres⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    exact mentionsFvar_false hres l hl (by omega)
  have hCR := shadowCtxOk hO hlenAll (nP := nP) (ks := ks) (Nat.le_refl _) hO.bodyScoped.1
    hO.bodyScoped.2.2.2 hnorecR (fun i hi' hr ρ' hρ' => (key i hi' ρ' hρ').1)
  rw [Nat.sub_self, List.drop_zero] at hCR
  have hrow := (claimsAt_of hμ mp ψ F').sortRow hib hensb hO.bodyScoped.1 hO.bodyScoped.2.1
    hO.bodyScoped.2.2.1 hCR hO.body ρ hρ
  exact hrow.1

end ConLeche.Model
