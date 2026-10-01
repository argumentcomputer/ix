module

public import ConLeche.Model.IndParamGrade
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.Denote.OpenRevDenote
public section

/-!
# The field domains, graded and fired (task #161, IND TIER part 5)

**The half part 4 could not run.**  `prefixGradeFire` closed the
statement frame's prefix positions on the rows `IotaRuns` already
carried; this file closes the *field* positions, and it is the theorem
the second widening was applied for.

The shape is the same position induction, at the same padded frame,
with one structural difference that is the whole content of part 4's
second exposure: the b-side here is a domain of the **constructor's**
`instPisAt` run, and grading it walks that run's own tower past *every*
earlier position — including the `i < cnP` parameter positions, which
no walk at this frame compares.  Those come in as the abstract premise
`hpar`, and its two suppliers are the two fire modes:

* `.plain` — `paramGradeFire` at the recursor-frame context, carried
  across by the prefix positions' equalities and the block renaming;
* `.nested` — the pins' recorded `TypedListOk` run (the second
  widening's other row) against `RecRuleLaw`'s carried graded pins.

Everything else is `prefixGradeFire`'s bookkeeping one branch over:
the a-side is again a statement-tower slot (`hokA_padded`), the
equality is again `defEqAt_of_run` — this time on `hdeFld` — and the
field spine positions below `n` are earned from the induction's own
earlier steps against `Sat`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name isDefEqCore DefEqListOk)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

set_option maxHeartbeats 3200000 in
/-- **The field walk's gradings and equalities, by position** —
`prefixGradeFire`'s field twin.  See the module docstring; the
parameter positions of the constructor run enter as `hpar`, which is
where the two fire modes differ and nothing else does. -/
theorem fieldGradeFire {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {rP cnP cnF : Nat}
    -- the statement frame
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvs)
    (hlbFvs : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ fvs → ty.looseBVarsBounded 0 = true)
    {Tstmt : AnnotTerm} {Γs : List AnnotTerm} {Rbody : AnnotTerm}
    (htowerS : PiTeleAV (rP + cnF) Tstmt Γs Rbody)
    (hokTst : ∀ σ : Nat → V, WellDenotedV V σ Tstmt)
    (hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    -- the constructor's run at the statement frame
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : AnnotTerm}
    (hTVjK : denoteMeta m.acval env φ (rP + cnF) ctyR = some TVj)
    (hokTVj : ∀ σ : Nat → V, WellDenotedV V σ TVj)
    {sp : List Expr} (hsplen : sp.length = cnP + cnF)
    (hspScope : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true)
    (hspFld : ∀ j, j < cnF → sp[cnP + j]? = fvs[rP + j]?)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    -- the field domains' scope and leaves (`zipFieldTermEq`'s first
    -- two conjuncts, which the zipper computes anyway)
    (hwsCd : ∀ j, j < cnF →
      Expr.WScoped (rP + j) (cdoms.getD (cnP + j) default))
    (hleafCd : ∀ j, j < cnF →
      ∀ l ∈ (cdoms.getD (cnP + j) default).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + j)
    -- the recorded field run
    (hdeFld : DefEqListOk μ F env (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- the padding level
    {N : Nat} (hN : N ≤ rP + cnF)
    -- the parameter positions of the constructor run, supplied
    (hpar : ∀ q, q < cnP → ∀ ρ' : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ' →
      ∃ w, denoteMeta m.acval env φ (rP + cnF) (sp.getD q default)
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta m.acval env φ (rP + cnF)
            (cdoms.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw) :
    ∀ n, n ≤ N → rP ≤ n → n < rP + cnF → ∀ ρ' : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ' →
      ∀ dw : AnnotTerm,
        denoteMeta m.acval env φ (rP + cnF)
          (cdoms.getD (cnP + (n - rP)) default) = some dw →
        WellDenotedV V ρ' dw ∧
          interp V (fun j => ρ' (j + (rP + cnF - n)))
              (Γs.getD (rP + cnF - 1 - n) default)
            = interp V ρ' dw := by
  have hΓslen : Γs.length = (rP + cnF) := htowerS.length
  have hcdlen : cdoms.length = cnP + cnF := by
    have h := instPisAt_length _ hcinst
    omega
  -- the padded context, named once
  have hΔlen : (List.replicate (rP + cnF - N) (AnnotTerm.sort 0)
      ++ Γs.drop (rP + cnF - N)).length = (rP + cnF) := by
    rw [List.length_append, List.length_replicate, List.length_drop,
      hΓslen]
    omega
  -- above the padding the padded context is the tower's
  have hent : ∀ i, i < N →
      (List.replicate (rP + cnF - N) (AnnotTerm.sort 0)
        ++ Γs.drop (rP + cnF - N))[(rP + cnF) - 1 - i]?
        = some (Γs.getD ((rP + cnF) - 1 - i) default) := by
    intro i hi
    rw [List.getElem?_append_right
      (by rw [List.length_replicate]; omega),
      List.length_replicate, List.getElem?_drop,
      show (rP + cnF) - N + ((rP + cnF) - 1 - i - ((rP + cnF) - N))
        = (rP + cnF) - 1 - i from by omega,
      List.getD]
    rcases hg : Γs[(rP + cnF) - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  -- the a-side gradings, from the statement type's own
  have hokAll : ∀ i, i ≤ N → i < rP + cnF → ∀ ρ' : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (AnnotTerm.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ' →
      WellDenotedV V (fun j => ρ' (j + ((rP + cnF) - 1 - i) + 1))
        (Γs.getD ((rP + cnF) - 1 - i) default) := by
    intro i hi hiK ρ' hsat
    refine wellDenotedV_tower_slot (rP + cnF) htowerS (hokTst _)
      ((rP + cnF) - 1 - i) (by omega) (fun q hq1 hq2 => ?_)
    exact hsat q (Γs.getD q default)
      (by
        rw [List.getElem?_append_right
          (by rw [List.length_replicate]; omega),
          List.length_replicate, List.getElem?_drop,
          show (rP + cnF) - N + (q - ((rP + cnF) - N)) = q from by omega,
          List.getD]
        rcases hg : Γs[q]? with _ | A
        · rw [List.getElem?_eq_none_iff] at hg; omega
        · rfl)
  have hfvsAt : ∀ n, n < (rP + cnF) →
      ∃ ty, fvs[n]? = some (.fvar n ty) := by
    intro n hn
    rcases hx : fvs[n]? with _ | x
    · rw [List.getElem?_eq_none_iff] at hx; omega
    · obtain ⟨ty, rfl⟩ := hshapeS n x hx
      exact ⟨_, rfl⟩
  -- the field domains' bvar bound
  have hbCdAll : ∀ j, j < cnF →
      (cdoms.getD (cnP + j) default).looseBVarsBounded 0 = true := by
    intro j hj
    have hmem : cdoms.getD (cnP + j) default ∈ cdoms := by
      rw [List.getD]
      rcases hr : cdoms[cnP + j]? with _ | r
      · rw [List.getElem?_eq_none_iff] at hr; omega
      · exact List.mem_of_getElem? hr
    refine (instPisAt_bounded _ hcinst hCbR ?_).1 _ hmem
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    exact (hspScope q a hq).2
  have hfbCty : Expr.fvarsBelow (rP + cnF) ctyR := by
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCwR] at hl
    exact nomatch hl
  have hshiftEnv : ∀ (p : Nat) (ρ0 : Nat → V),
      shiftE ((rP + cnF) - p) 0 ρ0
        = (fun j => ρ0 (j + ((rP + cnF) - p))) := by
    intro p ρ0
    funext j
    show (if j < 0 then ρ0 j else ρ0 (j + ((rP + cnF) - p))) = _
    rw [if_neg (Nat.not_lt_zero j)]
  -- the strong induction on the field position
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro hnN hrPn hnK
  obtain ⟨ty, hx⟩ := hfvsAt n (by omega)
  have hmemFvs : Expr.fvar n ty ∈ fvs := List.mem_of_getElem? hx
  have hwsTy : Expr.WScoped n ty := by
    have h' := hwsFvs _ hmemFvs
    simp only [Expr.WScoped] at h'
    exact h'.2
  have hleafTy : ∀ l ∈ ty.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    exact hleafClosed l ⟨_, hmemFvs, by
      rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl⟩
  have hltTy : ∀ l ∈ ty.fvarLeaves, l.1 < n :=
    Expr.fvarLeaves_lt_of_wscoped hwsTy
  have hbTy : ty.looseBVarsBounded 0 = true := hlbFvs n ty hmemFvs
  have hjlt : n - rP < cnF := by omega
  have hnj : rP + (n - rP) = n := by omega
  -- the a-side reading at the frame depth
  have hdomTy : denoteMeta m.acval env φ n ty
      = some (Γs.getD ((rP + cnF) - 1 - n) default) := hdomsS0 n _ hx
  have hAv : denoteMeta m.acval env φ (rP + cnF) ty
      = some ((Γs.getD ((rP + cnF) - 1 - n) default).liftN
          ((rP + cnF) - n) 0) := by
    rw [denoteMeta_lift m.acval_closed hwsTy (rP + cnF) (by omega), hdomTy]
    rfl
  -- **the b-side grading, at every satisfying environment**
  have hgbAll : ∀ ρ0 : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (AnnotTerm.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ0 → ∀ dw : AnnotTerm,
      denoteMeta m.acval env φ (rP + cnF)
        (cdoms.getD (cnP + (n - rP)) default) = some dw →
      WellDenotedV V ρ0 dw := by
    intro ρ0 hρ0 dw hdw
    refine instPisAt_doms_graded (ρ' := ρ0) m.acval_closed
      (fun nm' ψ y k => AVExprSubst.inst_eq_self_of_closed
        (fun k' => m.acval_closed nm' ψ k') y k)
      _ hcinst (cnP + (n - rP))
      (fun i₀ x _ hx' => hspScope i₀ x hx')
      hfbCty hCbR hTVjK (hokTVj _) ?_ (by omega) dw hdw
    intro i₀ x hlt hx'
    have hgetD : sp.getD i₀ default = x := by
      rw [List.getD, hx']
      rfl
    rcases Nat.lt_or_ge i₀ cnP with hi₀ | hi₀
    · -- a parameter position: supplied
      obtain ⟨w, hw, hokw, hmw⟩ := hpar i₀ hi₀ ρ0 hρ0
      rw [hgetD] at hw
      exact ⟨w, hw, hokw, hmw⟩
    · -- an earlier field position: the induction's own
      obtain ⟨j', rfl⟩ : ∃ j', i₀ = cnP + j' := ⟨i₀ - cnP, by omega⟩
      have hj'lt : j' < n - rP := by omega
      have hxf : fvs[rP + j']? = some x := by
        rw [← hspFld j' (by omega)]
        exact hx'
      obtain ⟨ty', hx''⟩ := hfvsAt (rP + j') (by omega)
      obtain rfl : x = Expr.fvar (rP + j') ty' := by
        rw [hxf] at hx''
        exact Option.some.inj hx''
      refine ⟨.bvar ((rP + cnF) - 1 - (rP + j')),
        denoteMeta_fvar _ _ _ _, ⟨by simp, by simp⟩, ?_⟩
      intro dw0 hdw0
      have hIH := ihn (rP + j') (by omega) (by omega) (by omega)
        (by omega) ρ0 hρ0 dw0 (by
          rw [show rP + j' - rP = j' from by omega]
          exact hdw0)
      have hsatm := hρ0 ((rP + cnF) - 1 - (rP + j'))
        (Γs.getD ((rP + cnF) - 1 - (rP + j')) default)
        (hent (rP + j') (by omega))
      rw [show (fun j => ρ0 (j + ((rP + cnF) - 1 - (rP + j')) + 1))
          = (fun j => ρ0 (j + ((rP + cnF) - (rP + j')))) from by
        funext j; congr 1; omega] at hsatm
      rw [hIH.2] at hsatm
      exact hsatm
  intro ρ' hsat dw hdw
  refine ⟨hgbAll ρ' hsat dw hdw, ?_⟩
  -- the equality: fire the recorded field run at the padded frame
  have hrun : isDefEqCore μ env F (rP + cnF) ty
      (cdoms.getD (cnP + (n - rP)) default) = .ok true := by
    have h := defEqListOk_getD hdeFld (n - rP)
      (by rw [List.length_map, List.length_drop, hfvslen]; omega)
    rw [show ((fvs.drop rP).map Expr.fvarTypeD).getD (n - rP) default
        = ty from by
      rw [List.getD, List.getElem?_map, List.getElem?_drop, hnj, hx]
      rfl,
      show (cdoms.drop cnP).getD (n - rP) default
        = cdoms.getD (cnP + (n - rP)) default from by
      rw [List.getD, List.getD, List.getElem?_drop]] at h
    exact h
  have hLbTy : Expr.LeavesBounded ty := fun l hl =>
    hlbFvs l.1 l.2 (hleafTy l hl)
  have hLbCd : Expr.LeavesBounded (cdoms.getD (cnP + (n - rP)) default) :=
    fun l hl => hlbFvs l.1 l.2
      (hleafCd (n - rP) hjlt l hl).1
  have hfire := defEqAt_of_run (m := m) hclaims (k := (rP + cnF))
    (fvs := fvs) (Aa := fun i => Γs.getD ((rP + cnF) - 1 - i) default)
    (Δa := (List.replicate (rP + cnF - N) (AnnotTerm.sort 0)
      ++ Γs.drop (rP + cnF - N))) hΔlen
    hshapeS hwsFvs (fun i x hix => hdomsS0 i x hix) (n := n)
    (fun i hi => hent i (by omega))
    (fun i hi ρ0 hρ0 => hokAll i (by omega) (by omega) ρ0 hρ0)
    hrun (hwsTy.mono (by omega)) hbTy hLbTy
    (((hwsCd (n - rP) hjlt).mono (by omega) : Expr.WScoped (rP + cnF) _))
    (hbCdAll (n - rP) hjlt) hLbCd
    hleafTy hltTy (fun l hl => (hleafCd (n - rP) hjlt l hl).1)
    (fun l hl => by
      have := (hleafCd (n - rP) hjlt l hl).2
      omega)
    hAv hdw
    (fun ρ0 hρ0 => (WellDenotedV_liftN V ((rP + cnF) - n) _ 0 ρ0).mpr (by
      rw [hshiftEnv n ρ0]
      have h := hokAll n (by omega) (by omega) ρ0 hρ0
      rw [show (fun j => ρ0 (j + ((rP + cnF) - 1 - n) + 1))
          = (fun j => ρ0 (j + ((rP + cnF) - n))) from by
        funext j; congr 1; omega] at h
      exact h))
    (fun ρ0 hρ0 => hgbAll ρ0 hρ0 dw hdw)
    hsat
  rw [interp_liftN, hshiftEnv n ρ'] at hfire
  exact hfire

end ConLeche.Model
