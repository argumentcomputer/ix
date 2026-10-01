module

public import ConLeche.Model.IndDomGrade
public import ConLeche.Model.IndRuns
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.Denote.OpenRevDenote
public section

/-!
# The constructor's parameter domains, graded and fired (task #161,
IND TIER part 5)

The **second** position induction, and the one the second widening
unblocked.  `prefixGradeFire` (part 4) walks the *statement* frame's
prefix positions against the recursor's own domains; this file walks
the **public** frame's first `cnP` positions against the constructor's
own parameter domains — the `hdePars` row, recorded by the lead's
second widening precisely so that this induction has rows to run on.

**Why it lives at its own context, and why that is a saving.**  The
comparison `hdePars` records is between the *recursor* frame's openers
(`fvsP`, from `openPisAtFvars rP tyA 0`) and `cdomsP`, whose leaves are
those same openers.  It cannot be fired at the statement frame's
context at all — `CtxOk` identifies a leaf's *annotation* with the
context entry, and the statement frame's openers carry the statement
type's domains, not the recursor's.  So this ladder runs at the
recursor-frame context `Δb` (any context of the ambient depth whose
slot `K - 1 - i` is the recursor tower's `ΓP` slot), and its consumer
transports into it — which the field branch can do, because
`prefixGradeFire` has already proved the two contexts' slots
interp-equal.

The payoff of the separate context is that the ladder needs **no
external input**: `Sat V Δb` alone grades every `ΓP` slot
(`wellDenotedV_tower_slot` at the recursor tower, whose memberships *are*
`Δb`'s satisfaction), so the induction is self-feeding — grading at
`q` from the memberships below `q`, membership at `q` from the fired
equality and `Sat`.
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
/-- **The parameter walk's gradings and memberships, by position.**
At every `ρ'` satisfying the recursor-frame context, the constructor
run's `q`-th parameter domain reads to a *graded* annotation whose
value contains the frame's own `q`-th slot value.  Both conclusions
come out of one strong induction, because the membership at `q` is the
`instPisAt` descent's premise at `q + 1`. -/
theorem paramGradeFire {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {K rP cnP : Nat} (hcnP : cnP ≤ rP) (hrPK : rP ≤ K)
    -- the public (recursor) frame
    {fvsP : List Expr} (hfvsPlen : fvsP.length = rP)
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x)
    (hleafClosedP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvsP)
    (hlbFvsP : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ fvsP → ty.looseBVarsBounded 0 = true)
    {TV : AnnotTerm} {ΓP : List AnnotTerm} {RP : AnnotTerm}
    (htowerP : PiTeleAV rP TV ΓP RP)
    (hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV)
    (hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    -- the constructor type, read at the ambient depth
    {ctyP : Expr} (hCw : ctyP.hasFvar = false)
    (hCb : ctyP.looseBVarsBounded 0 = true)
    {TVjP : AnnotTerm} (hTVjP : denoteMeta m.acval env φ K ctyP = some TVjP)
    (hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP)
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt (fvsP.take cnP) ctyP
      = some (cdomsP, crestP))
    -- the recorded run (the second widening's first row)
    (hdePars : DefEqListOk μ F env K
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    -- the recursor-frame context
    {Δb : List AnnotTerm} (hΔblen : Δb.length = K)
    (hΔbent : ∀ i, i < rP →
      Δb[K - 1 - i]? = some (ΓP.getD (rP - 1 - i) default)) :
    ∀ q, q < cnP → ∀ ρ' : Nat → V, Sat V Δb ρ' →
      ∀ dw : AnnotTerm,
        denoteMeta m.acval env φ K (cdomsP.getD q default) = some dw →
        WellDenotedV V ρ' dw ∧ ρ' (K - 1 - q) ∈ˢ interp V ρ' dw := by
  have hΓPlen : ΓP.length = rP := htowerP.length
  have hspLen : (fvsP.take cnP).length = cnP := by
    rw [List.length_take, hfvsPlen]; omega
  have hcdlen : cdomsP.length = cnP := by
    have h := instPisAt_length _ hcinstP
    rw [hspLen] at h
    exact h
  -- the frame's per-index data
  have hfvsPAt : ∀ n, n < rP →
      ∃ ty, fvsP[n]? = some (.fvar n ty) := by
    intro n hn
    rcases hx : fvsP[n]? with _ | x
    · rw [List.getElem?_eq_none_iff] at hx; omega
    · obtain ⟨ty, rfl⟩ := hshapeP n x hx
      exact ⟨_, rfl⟩
  -- the tower's slots are graded by satisfaction alone
  have hokAll : ∀ i, i < rP → ∀ ρ0 : Nat → V, Sat V Δb ρ0 →
      WellDenotedV V (fun j => ρ0 (j + (K - 1 - i) + 1))
        (ΓP.getD (rP - 1 - i) default) := by
    intro i hi ρ0 hρ0
    have hbase : WellDenotedV V
        (fun j => (fun t => ρ0 (t + (K - rP))) (j + rP)) TV := by
      have h := hokTV (fun j => ρ0 (j + K))
      refine cast (by congr 1; funext j; congr 1; omega) h
    refine cast ?_ (wellDenotedV_tower_slot rP htowerP
      (ρ' := fun t => ρ0 (t + (K - rP))) hbase (rP - 1 - i) (by omega)
      (fun q hq1 hq2 => ?_))
    · congr 1
      funext j
      show ρ0 (j + (rP - 1 - i) + 1 + (K - rP)) = ρ0 (j + (K - 1 - i) + 1)
      congr 1
      omega
    · have hsatm := hρ0 (K - 1 - (rP - 1 - q))
        (ΓP.getD (rP - 1 - (rP - 1 - q)) default)
        (hΔbent (rP - 1 - q) (by omega))
      show (fun t => ρ0 (t + (K - rP))) q ∈ˢ _
      rw [show (fun t => ρ0 (t + (K - rP))) q
          = ρ0 (K - 1 - (rP - 1 - q)) from by
          show ρ0 (q + (K - rP)) = _
          congr 1
          omega,
        show (fun j => (fun t => ρ0 (t + (K - rP))) (j + q + 1))
          = (fun j => ρ0 (j + (K - 1 - (rP - 1 - q)) + 1)) from by
          funext j
          show ρ0 (j + q + 1 + (K - rP)) = _
          congr 1
          omega,
        show ΓP.getD q default
          = ΓP.getD (rP - 1 - (rP - 1 - q)) default from by
          congr 1
          omega]
      exact hsatm
  -- the spine's per-index scope and leaves
  have hspScope : ∀ (i₀ : Nat) (x : Expr), (fvsP.take cnP)[i₀]? = some x →
      Expr.WScoped K x ∧ x.looseBVarsBounded 0 = true := by
    intro i₀ x hx
    have hi₀ : i₀ < cnP := by
      rcases Nat.lt_or_ge i₀ cnP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hx
        exact nomatch hx
    rw [List.getElem?_take_of_lt hi₀] at hx
    obtain ⟨ty, rfl⟩ := hshapeP i₀ x hx
    have hw := hwsFvsP _ (List.mem_of_getElem? hx)
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨⟨by omega, hw.2⟩, rfl⟩
  -- the constructor type is fvar-free
  have hfbCty : Expr.fvarsBelow K ctyP := by
    refine Expr.fvarsBelow_of_fvarLeaves fun l hl => ?_
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl
    exact nomatch hl
  -- the run's per-index scope, leaves and bounds
  have hwsCdAll : ∀ q, q < cnP →
      Expr.WScoped q (cdomsP.getD q default) := by
    intro q hq
    have h1 := instPisAt_index_WScoped (fvsP.take cnP) (d := 0) hcinstP
      (Expr.WScoped.of_not_hasFvar hCw) ?_ q (cdomsP.getD q default) ?_
    · simpa using h1
    · intro i a ha
      have hi : i < cnP := by
        rcases Nat.lt_or_ge i cnP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by omega)] at ha
          exact nomatch ha
      rw [List.getElem?_take_of_lt hi] at ha
      obtain ⟨ty', rfl⟩ := hshapeP i a ha
      have h'' := hwsFvsP _ (List.mem_of_getElem? ha)
      simp only [Expr.WScoped] at h'' ⊢
      exact ⟨by omega, h''.2⟩
    · rw [List.getD]
      rcases hr : cdomsP[q]? with _ | r
      · rw [List.getElem?_eq_none_iff] at hr; omega
      · rfl
  have hleafCdAll : ∀ q, q < cnP →
      ∀ l ∈ (cdomsP.getD q default).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvsP ∧ l.1 < cnP := by
    intro q hq l hl
    have hmem : cdomsP.getD q default ∈ cdomsP := by
      rw [List.getD]
      rcases hr : cdomsP[q]? with _ | r
      · rw [List.getElem?_eq_none_iff] at hr; omega
      · exact List.mem_of_getElem? hr
    rcases instPisAt_leaves _ hcinstP l (Or.inl ⟨_, hmem, hl⟩) with
      hty' | ⟨a, ha, hla⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCw] at hty'
      exact nomatch hty'
    · obtain ⟨q', hq'⟩ := List.getElem?_of_mem ha
      have hq'lt : q' < cnP := by
        rcases Nat.lt_or_ge q' cnP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by omega)] at hq'
          exact nomatch hq'
      rw [List.getElem?_take_of_lt hq'lt] at hq'
      obtain ⟨ty', rfl⟩ := hshapeP q' _ hq'
      rw [Expr.fvarLeaves] at hla
      rcases List.mem_cons.mp hla with rfl | hla'
      · exact ⟨List.mem_of_getElem? hq', hq'lt⟩
      · refine ⟨hleafClosedP l ⟨_, List.mem_of_getElem? hq', by
          rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hla'⟩, ?_⟩
        have hws := hwsFvsP _ (List.mem_of_getElem? hq')
        simp only [Expr.WScoped] at hws
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l hla'
        omega
  have hbCdAll : ∀ q, q < cnP →
      (cdomsP.getD q default).looseBVarsBounded 0 = true := by
    intro q hq
    have hmem : cdomsP.getD q default ∈ cdomsP := by
      rw [List.getD]
      rcases hr : cdomsP[q]? with _ | r
      · rw [List.getElem?_eq_none_iff] at hr; omega
      · exact List.mem_of_getElem? hr
    refine (instPisAt_bounded _ hcinstP hCb ?_).1 _ hmem
    intro a ha
    obtain ⟨q', hq'⟩ := List.getElem?_of_mem ha
    exact (hspScope q' a hq').2
  -- the strong induction on the parameter position
  intro q
  induction q using Nat.strongRecOn with
  | _ q ihq =>
  intro hq
  obtain ⟨tyP, hxP⟩ := hfvsPAt q (by omega)
  have hmemFvsP : Expr.fvar q tyP ∈ fvsP := List.mem_of_getElem? hxP
  have hwsTyP : Expr.WScoped q tyP := by
    have h' := hwsFvsP _ hmemFvsP
    simp only [Expr.WScoped] at h'
    exact h'.2
  have hleafTyP : ∀ l ∈ tyP.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsP := by
    intro l hl
    exact hleafClosedP l ⟨_, hmemFvsP, by
      rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl⟩
  have hltTyP : ∀ l ∈ tyP.fvarLeaves, l.1 < q :=
    Expr.fvarLeaves_lt_of_wscoped hwsTyP
  have hbTyP : tyP.looseBVarsBounded 0 = true :=
    hlbFvsP q tyP hmemFvsP
  -- the a-side reading at the ambient depth
  have hdomTyP : denoteMeta m.acval env φ q tyP
      = some (ΓP.getD (rP - 1 - q) default) := hdomsP0 q _ hxP
  have hAv : denoteMeta m.acval env φ K tyP
      = some ((ΓP.getD (rP - 1 - q) default).liftN (K - q) 0) := by
    rw [denoteMeta_lift m.acval_closed hwsTyP K (by omega), hdomTyP]
    rfl
  have hshiftEnv : ∀ ρ0 : Nat → V,
      shiftE (K - q) 0 ρ0 = (fun j => ρ0 (j + (K - q))) := by
    intro ρ0
    funext j
    show (if j < 0 then ρ0 j else ρ0 (j + (K - q))) = _
    rw [if_neg (Nat.not_lt_zero j)]
  -- **the b-side grading, at every satisfying environment**
  have hgbAll : ∀ ρ0 : Nat → V, Sat V Δb ρ0 → ∀ dw : AnnotTerm,
      denoteMeta m.acval env φ K (cdomsP.getD q default) = some dw →
      WellDenotedV V ρ0 dw := by
    intro ρ0 hρ0 dw hdw
    refine instPisAt_doms_graded (ρ' := ρ0) m.acval_closed
      (fun n ψ y k => AVExprSubst.inst_eq_self_of_closed
        (fun k' => m.acval_closed n ψ k') y k)
      _ hcinstP q (fun i₀ x _ hx => hspScope i₀ x hx)
      hfbCty hCb hTVjP (hokTVjP _) ?_
      (by omega) dw hdw
    intro i₀ x hlt hx
    have hi₀ : i₀ < cnP := by omega
    rw [List.getElem?_take_of_lt hi₀] at hx
    obtain ⟨ty₀, rfl⟩ := hshapeP i₀ x hx
    refine ⟨.bvar (K - 1 - i₀), denoteMeta_fvar _ _ _ _, ?_, ?_⟩
    · exact ⟨by simp, by simp⟩
    · intro dw0 hdw0
      exact (ihq i₀ hlt (by omega) ρ0 hρ0 dw0 hdw0).2
  intro ρ' hsat dw hdw
  refine ⟨hgbAll ρ' hsat dw hdw, ?_⟩
  -- the equality: fire the recorded run at the recursor frame
  have hrun : isDefEqCore μ env F K tyP (cdomsP.getD q default)
      = .ok true := by
    have h := defEqListOk_getD hdePars q (by
      rw [List.length_map]; omega)
    rw [show ((fvsP.take cnP).map Expr.fvarTypeD).getD q default
        = tyP from by
      rw [List.getD, List.getElem?_map, List.getElem?_take_of_lt hq,
        hxP]
      rfl] at h
    exact h
  have hLbTyP : Expr.LeavesBounded tyP := fun l hl =>
    hlbFvsP l.1 l.2 (hleafTyP l hl)
  have hLbCd : Expr.LeavesBounded (cdomsP.getD q default) := fun l hl =>
    hlbFvsP l.1 l.2 (hleafCdAll q hq l hl).1
  have hfire := defEqAt_of_run (m := m) hclaims (k := K) (fvs := fvsP)
    (Aa := fun i => ΓP.getD (rP - 1 - i) default) (Δa := Δb) hΔblen
    hshapeP (fun x hx => (hwsFvsP x hx).mono (by omega))
    (fun i x hix => hdomsP0 i x hix) (n := cnP)
    (fun i hi => hΔbent i (by omega))
    (fun i hi ρ0 hρ0 => hokAll i (by omega) ρ0 hρ0)
    hrun (hwsTyP.mono (by omega)) hbTyP hLbTyP
    ((hwsCdAll q hq).mono (by omega)) (hbCdAll q hq) hLbCd
    hleafTyP (fun l hl => Nat.lt_trans (hltTyP l hl) hq)
    (fun l hl => (hleafCdAll q hq l hl).1)
    (fun l hl => (hleafCdAll q hq l hl).2) hAv hdw
    (fun ρ0 hρ0 => (WellDenotedV_liftN V (K - q) _ 0 ρ0).mpr (by
      rw [hshiftEnv ρ0]
      have h := hokAll q (by omega) ρ0 hρ0
      rw [show (fun j => ρ0 (j + (K - 1 - q) + 1))
          = (fun j => ρ0 (j + (K - q))) from by
        funext j; congr 1; omega] at h
      exact h))
    (fun ρ0 hρ0 => hgbAll ρ0 hρ0 dw hdw)
    hsat
  rw [interp_liftN, hshiftEnv ρ'] at hfire
  -- the membership: the frame's own slot, across the fired equality
  have hsatq := hsat (K - 1 - q) (ΓP.getD (rP - 1 - q) default)
    (hΔbent q (by omega))
  rw [show (fun j => ρ' (j + (K - 1 - q) + 1))
      = (fun j => ρ' (j + (K - q))) from by
    funext j; congr 1; omega] at hsatq
  rw [hfire] at hsatq
  exact hsatq

end ConLeche.Model
