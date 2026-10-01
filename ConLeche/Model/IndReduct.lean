module

public import ConLeche.Model.IndTowerRead
public section

/-!
# The reduct stage, at the reading (task #161, IND TIER part 5)

`reductS`'s transpose: the checked statement's right-hand side, read at
the fired chain, **is** the rule's own right-hand side applied to the
fired spine.  The recorded rhs run fires at the full frame, the applied
form's head runs back to the closed rule reading (`denoteMeta_renameConsts`
then `denoteMeta_depth_of_closed`), and the opener spine reads off the
chain.

**One premise is the third exposure's, and it is named as such.**
`DefEqClaim` converts the rhs run only against *both* comparands'
gradings.  The a-side is the statement's own right-hand side and its
grading is `IotaRuns`'s own `inferTypeCore rhsS` run through
`InferClaim`; the b-side is the *applied form*, whose grading needs
`Ra`'s — the row `IotaRuleR` does not carry (see the third-exposure
entry in DESIGN.md).  So it enters here as `hokApp`, in the `∀ ba`
form the reading's existence is derived in, and the stage is otherwise
complete: once the row lands, `hokApp` is the truthfulness transport's
own output at the frame's openers.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- A spine every element of which reads, reads as a spine. -/
theorem denoteMetaSpine_of_all {d : Nat} :
    ∀ (as : List Expr),
      (∀ a ∈ as, ∃ v, denoteMeta acval env φ d a = some v) →
      ∃ vs, DenoteMetaSpine acval env φ d as vs := by
  intro as
  induction as with
  | nil => intro _; exact ⟨[], .nil⟩
  | cons a as ih =>
    intro h
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    obtain ⟨vs, hvs⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨v :: vs, .cons hv hvs⟩

/-- The forward direction of `denoteMeta_mkAppN_inv`. -/
theorem denoteMeta_mkAppN_of {d : Nat} :
    ∀ (as : List Expr) {e : Expr} {ea : AnnotTerm} {vs : List AnnotTerm},
      denoteMeta acval env φ d e = some ea →
      DenoteMetaSpine acval env φ d as vs →
      denoteMeta acval env φ d (Expr.mkAppN e as)
        = some (AnnotTerm.mkAppN ea vs) := by
  intro as
  induction as with
  | nil =>
    intro e ea vs he hsp
    cases hsp
    exact he
  | cons a as ih =>
    intro e ea vs he hsp
    cases hsp with
    | @cons _ v _ vs' ha hsp' =>
      have hstep : denoteMeta acval env φ d (.app e a) = some (.app ea v) := by
        rw [denoteMeta_app, he, ha]
        rfl
      exact ih (ea := .app ea v) hstep hsp'

set_option maxHeartbeats 3200000 in
/-- **The reduct stage, at the reading** (`reductS`). -/
theorem reduct {m : EnvModel V env} {F : Nat} {ψ' : Name → Nat}
    (hclaims : DefEqClaim μ m ψ' F)
    {f : Name → Name} (hroT : RenameOk m.acval env f)
    {rP cnF : Nat} {fvs : List Expr}
    (hfvslen : fvs.length = rP + cnF)
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
      denoteMeta m.acval env ψ' i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default))
    {Δa : List AnnotTerm} (hΔalen : Δa.length = rP + cnF)
    (hΔaent : ∀ i, i < rP + cnF →
      Δa[rP + cnF - 1 - i]? = some (Γs.getD (rP + cnF - 1 - i) default))
    -- the rule's right-hand side, closed
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {RV : AnnotTerm} (hRV : denoteMeta m.acval env ψ' 0 rhsA = some RV)
    -- the statement's right-hand side
    {rhsS : Expr} {vR : AnnotTerm}
    (hvR : denoteMeta m.acval env ψ' (rP + cnF) rhsS = some vR)
    (hwsR : Expr.WScoped (rP + cnF) rhsS)
    (hbR : rhsS.looseBVarsBounded 0 = true)
    (hleafR : ∀ l ∈ rhsS.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltR : ∀ l ∈ rhsS.fvarLeaves, l.1 < rP + cnF)
    (hokR : ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ vR)
    -- the recorded rhs run, and the applied form's grading (the third
    -- exposure's row is what discharges the latter)
    (hdeRhs : isDefEqCore μ env F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    (hokApp : ∀ σ : Nat → V, Sat V Δa σ → ∀ ba : AnnotTerm,
      denoteMeta m.acval env ψ' (rP + cnF)
        (Expr.mkAppN (rhsA.renameConsts f) fvs) = some ba →
      WellDenotedV V σ ba)
    {zs : List AnnotTerm} {ρ : Nat → V} (hzslen : zs.length = rP + cnF)
    (hsat : Sat V Δa (chain V ρ zs)) :
    interp V (chain V ρ zs) vR
      = interp V ρ (AnnotTerm.mkAppN RV zs) := by
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  -- the openers' gradings at the ambient context
  have hokAll : ∀ i, i < rP + cnF → ∀ σ : Nat → V, Sat V Δa σ →
      WellDenotedV V (fun j => σ (j + (rP + cnF - 1 - i) + 1))
        (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i hi σ hσ
    refine wellDenotedV_tower_slot (rP + cnF) htowerS (hokTst _)
      (rP + cnF - 1 - i) (by omega) (fun q hq1 hq2 => ?_)
    refine hσ q (Γs.getD q default) ?_
    have h := hΔaent (rP + cnF - 1 - q) (by omega)
    rw [show rP + cnF - 1 - (rP + cnF - 1 - q) = q from by omega] at h
    exact h
  -- the applied form's leaves, scope and bound
  have hrhsRw : (rhsA.renameConsts f).hasFvar = false :=
    (ConLeche.hasFvar_renameConsts f rhsA).trans hrhsw
  have hleafApp : ∀ l ∈ (Expr.mkAppN (rhsA.renameConsts f)
      fvs).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    rcases fvarLeaves_mkAppN hl with hf | ⟨x, hx, hlx⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hf
      exact nomatch hf
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := hshapeS q x hq
      rw [Expr.fvarLeaves] at hlx
      rcases List.mem_cons.mp hlx with rfl | hlx'
      · exact hx
      · exact hleafClosed l ⟨_, hx, by
          rw [Expr.fvarLeaves]
          exact List.mem_cons_of_mem _ hlx'⟩
  have hltApp : ∀ l ∈ (Expr.mkAppN (rhsA.renameConsts f)
      fvs).fvarLeaves, l.1 < rP + cnF := by
    intro l hl
    rcases fvarLeaves_mkAppN hl with hf | ⟨x, hx, hlx⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hf
      exact nomatch hf
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
      have hqK : q < rP + cnF := by
        rcases Nat.lt_or_ge q (rP + cnF) with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by omega)] at hq
          exact nomatch hq
      obtain ⟨ty, rfl⟩ := hshapeS q x hq
      rw [Expr.fvarLeaves] at hlx
      rcases List.mem_cons.mp hlx with rfl | hlx'
      · exact hqK
      · have hw := hwsFvs _ hx
        have hw' : Expr.WScoped q ty := by
          simp only [Expr.WScoped] at hw
          exact hw.2
        have := Expr.fvarLeaves_lt_of_wscoped hw' l hlx'
        omega
  have hwsApp : Expr.WScoped (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    refine ConLeche.Expr.WScoped.mkAppN ?_ (fun x hx => hwsFvs x hx)
    exact Expr.WScoped.of_not_hasFvar hrhsRw
  have hbApp : (Expr.mkAppN (rhsA.renameConsts f)
      fvs).looseBVarsBounded 0 = true := by
    refine ConLeche.looseBVarsBounded_mkAppN ?_ ?_
    · rw [looseBVarsBounded_renameConsts]
      exact hrhsb
    · intro x hx
      obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
      obtain ⟨ty, rfl⟩ := hshapeS q x hq
      rfl
  -- the head runs back to the closed rule reading
  have hRVcl : ∀ k : Nat, RV.liftN 1 k = RV :=
    fun k => denoteMeta_closed m.acval_erase m.cval_closed hrhsw hrhsb
      hRV 1 k
  have hheadK : denoteMeta m.acval env ψ' (rP + cnF)
      (rhsA.renameConsts f) = some RV := by
    rw [denoteMeta_renameConsts hroT rhsA (rP + cnF)]
    exact denoteMeta_depth_of_closed m.acval_closed hrhsw hRVcl hRV
      (rP + cnF)
  -- the opener spine reads
  obtain ⟨vsp, hspine⟩ := denoteMetaSpine_of_all (acval := m.acval)
    (env := env) (φ := ψ') (d := rP + cnF) fvs (by
      intro a ha
      obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      obtain ⟨ty, rfl⟩ := hshapeS q a hq
      exact ⟨_, denoteMeta_fvar _ _ _ _⟩)
  have hAppRead : denoteMeta m.acval env ψ' (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs)
      = some (AnnotTerm.mkAppN RV vsp) :=
    denoteMeta_mkAppN_of fvs hheadK hspine
  -- fire the recorded run
  have hfire := defEqAt_of_run (m := m) hclaims (k := rP + cnF)
    (fvs := fvs) (Aa := fun i => Γs.getD (rP + cnF - 1 - i) default)
    (Δa := Δa) hΔalen hshapeS hwsFvs
    (fun i x hx => hdomsS0 i x hx) (n := rP + cnF)
    (fun i hi => hΔaent i hi)
    (fun i hi σ hσ => hokAll i hi σ hσ)
    hdeRhs hwsR hbR (fun l hl => hlbFvs l.1 l.2 (hleafR l hl))
    hwsApp hbApp
    (fun l hl => hlbFvs l.1 l.2 (hleafApp l hl))
    hleafR hltR hleafApp hltApp hvR hAppRead hokR
    (fun σ hσ => hokApp σ hσ _ hAppRead) hsat
  rw [hfire]
  -- the spine's values are the chain's
  have hsplen : vsp.length = rP + cnF := by
    rw [← hspine.length, hfvslen]
  have hRVbb : ConLeche.Term.Term.bvarsBelow 0 RV.erase :=
    denote_closed m.cval_closed hrhsw hrhsb
      (denoteMeta_erase m.acval_erase 0 rhsA hRV)
  rw [interp_mkAppN_map, interp_mkAppN_map,
    interp_closed (V := V) hRVbb (chain V ρ zs) ρ]
  congr 1
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge i (rP + cnF) with hiK | hiK
  · rcases hx : fvs[i]? with _ | x
    · rw [List.getElem?_eq_none_iff, hfvslen] at hx
      omega
    obtain ⟨ty, rfl⟩ := hshapeS i x hx
    obtain ⟨v, hvspi, hdv⟩ := denoteMetaSpine_getElem?' hspine i _ hx
    rw [denoteMeta_fvar] at hdv
    obtain rfl : AnnotTerm.bvar (rP + cnF - 1 - i) = v :=
      Option.some.inj hdv
    rcases hz : zs[i]? with _ | z
    · rw [List.getElem?_eq_none_iff, hzslen] at hz
      omega
    have hgz : zs.getD i default = z := by rw [List.getD, hz]; rfl
    rw [hvspi, Option.map_some, Option.map_some, interp_bvar,
      chain_lt (by rw [hzslen]; omega), hzslen,
      show rP + cnF - 1 - (rP + cnF - 1 - i) = i from by omega, hgz]
  · rw [List.getElem?_eq_none (by rw [hsplen]; omega),
      List.getElem?_eq_none (by rw [hzslen]; omega)]
    rfl

end ConLeche.Model
