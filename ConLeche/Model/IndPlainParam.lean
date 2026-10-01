module

public import ConLeche.Model.IndFieldGrade
public import ConLeche.Model.IndPrefixGrade
public section

/-!
# The `.plain` fire's parameter supply (task #161, IND TIER part 5)

`fieldGradeFire`'s `hpar` premise, discharged for a canonical rule.
It is the composition part 4 named and could not run, in three moves
and no new mathematics:

1. **the context swap.**  `hdePars` compares the *recursor* frame's
   openers against `cdomsP`, so `paramGradeFire` runs at the
   recursor-frame context `Δb`.  A `ρ'` satisfying the statement
   frame's padded context satisfies `Δb` too, because `Δb` differs
   from it only in the top `rP` slots and `prefixGradeFire` has
   already proved those slots interp-equal.  (`Δb` is literally the
   padded context's low half with `ΓP` on top: `K - rP = cnF`.)
2. **the ladder**, `paramGradeFire`, at `Δb`;
3. **the renaming.**  `cdomsP` is the run at the public frame on the
   *unrenamed* constructor type; `cdoms`' first `cnP` domains are the
   run at the statement frame on the renamed one.  `instPisAt_renEq`
   relates them pointwise (the two spines are openers at equal
   indices, `RenEqT.fvar`), and `RenEqT.denoteMeta` turns that into
   equality of *readings* — so the grading and the membership cross
   with nothing to prove.

The `.nested` fire's supply is a different theorem: its spine's
parameter positions are the instantiated pins, and the row that types
them is `IotaThmNR`'s `TypedListOk`, not a `DefEqListOk`.
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
/-- **The canonical rule's parameter positions, supplied** — exactly
`fieldGradeFire`'s `hpar`. -/
theorem plainParamSupply {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {rP cnP cnF N : Nat} (hcnP : cnP ≤ rP) (hrPN : rP ≤ N)
    -- the statement frame
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    {Γs : List AnnotTerm} (hΓslen : Γs.length = rP + cnF)
    -- the public (recursor) frame and its tower
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
    -- the ambient (statement-frame) context
    {Δa : List AnnotTerm} (hΔalen : Δa.length = rP + cnF)
    (hΔaent : ∀ i, i < N →
      Δa[(rP + cnF) - 1 - i]? = some (Γs.getD ((rP + cnF) - 1 - i) default))
    -- the prefix positions, already fired (`prefixGradeFire`)
    (hpre : ∀ n, n ≤ N → n < rP → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      WellDenotedV V (fun j => ρ' (j + (rP + cnF - n)))
          (ΓP.getD (rP - 1 - n) default) ∧
        interp V (fun j => ρ' (j + (rP + cnF - n)))
            (Γs.getD (rP + cnF - 1 - n) default)
          = interp V (fun j => ρ' (j + (rP + cnF - n)))
              (ΓP.getD (rP - 1 - n) default))
    -- the constructor type at the public frame, and its run there
    {ctyP : Expr} (hCw : ctyP.hasFvar = false)
    (hCb : ctyP.looseBVarsBounded 0 = true)
    {TVjP : AnnotTerm}
    (hTVjP : denoteMeta m.acval env φ (rP + cnF) ctyP = some TVjP)
    (hokTVjP : ∀ σ : Nat → V, WellDenotedV V σ TVjP)
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt (fvsP.take cnP) ctyP
      = some (cdomsP, crestP))
    (hdePars : DefEqListOk μ F env (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    -- the statement-frame run, whose parameter spine is the frame's
    {sp : List Expr} (hsplen : sp.length = cnP + cnF)
    (hspPar : ∀ q, q < cnP → sp[q]? = fvs[q]?)
    {ctyR : Expr} {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    -- the renaming between the two runs' types
    {f : Name → Name} (hro : RenameOk m.acval env f)
    (hrenCty : RenEqT f ctyP ctyR) :
    ∀ q, q < cnP → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      ∃ w, denoteMeta m.acval env φ (rP + cnF) (sp.getD q default)
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta m.acval env φ (rP + cnF)
            (cdoms.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw := by
  have hΓPlen : ΓP.length = rP := htowerP.length
  -- the recursor-frame context: the ambient context's low half with the
  -- recursor tower on top (`K - rP = cnF`)
  have hΔblen : (Δa.take cnF ++ ΓP).length = rP + cnF := by
    rw [List.length_append, List.length_take, hΓPlen, hΔalen]
    omega
  have hΔblow : ∀ q, q < cnF → (Δa.take cnF ++ ΓP)[q]? = Δa[q]? := by
    intro q hq
    rw [List.getElem?_append_left
      (by rw [List.length_take, hΔalen]; omega),
      List.getElem?_take_of_lt hq]
  have hΔbent : ∀ i, i < rP →
      (Δa.take cnF ++ ΓP)[(rP + cnF) - 1 - i]?
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i hi
    rw [List.getElem?_append_right
      (by rw [List.length_take, hΔalen]; omega),
      List.length_take, hΔalen,
      show (rP + cnF) - 1 - i - min cnF (rP + cnF) = rP - 1 - i from by
        omega,
      List.getD]
    rcases hg : ΓP[rP - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  -- satisfaction transports, on the prefix equalities
  have hsatB : ∀ ρ' : Nat → V, Sat V Δa ρ' →
      Sat V (Δa.take cnF ++ ΓP) ρ' := by
    intro ρ' hsat i Ai hi
    have hiK : i < rP + cnF := by
      rcases Nat.lt_or_ge i (rP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hi
        exact nomatch hi
    rcases Nat.lt_or_ge i cnF with hic | hic
    · exact hsat i Ai (by rw [← hΔblow i hic]; exact hi)
    · -- the top `rP` slots: the recursor tower's, across the equalities
      have hp : (rP + cnF) - 1 - ((rP + cnF) - 1 - i) = i := by omega
      have hplt : (rP + cnF) - 1 - i < rP := by omega
      obtain rfl : Ai = ΓP.getD (rP - 1 - ((rP + cnF) - 1 - i)) default := by
        have h := hΔbent ((rP + cnF) - 1 - i) hplt
        rw [hp] at h
        rw [h] at hi
        exact (Option.some.inj hi).symm
      have hsatA := hsat i (Γs.getD i default) (by
        have h := hΔaent ((rP + cnF) - 1 - i) (by omega)
        rw [hp] at h
        exact h)
      have heq := (hpre ((rP + cnF) - 1 - i) (by omega) hplt ρ' hsat).2
      rw [hp] at heq
      rw [show (fun j => ρ' (j + i + 1))
          = (fun j => ρ' (j + ((rP + cnF) - ((rP + cnF) - 1 - i)))) from by
        funext j; congr 1; omega] at hsatA ⊢
      rw [← heq]
      exact hsatA
  -- the ladder at the recursor frame
  have hladder := paramGradeFire (m := m) hclaims (K := rP + cnF) hcnP
    (by omega) hfvsPlen hshapeP hwsFvsP hleafClosedP hlbFvsP htowerP
    hokTV hdomsP0 hCw hCb hTVjP hokTVjP hcinstP hdePars hΔblen hΔbent
  -- the renaming bridge between the two runs' domains
  obtain ⟨mid, htake, -⟩ := instPisAt_take sp cnP hcinst
  have hcdlen : cdoms.length = cnP + cnF := by
    have h := instPisAt_length _ hcinst
    omega
  have hcdPlen : cdomsP.length = cnP := by
    have h := instPisAt_length _ hcinstP
    rw [List.length_take, hfvsPlen] at h
    omega
  have hbridge : ∀ q, q < cnP →
      denoteMeta m.acval env φ (rP + cnF) (cdoms.getD q default)
        = denoteMeta m.acval env φ (rP + cnF) (cdomsP.getD q default) := by
    intro q hq
    have hargs : ∀ (i : Nat) (a a' : Expr),
        (fvsP.take cnP)[i]? = some a → (sp.take cnP)[i]? = some a' →
        RenEqT f a a' := by
      intro i a a' ha ha'
      have hi : i < cnP := by
        rcases Nat.lt_or_ge i cnP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none
            (by rw [List.length_take, hfvsPlen]; omega)] at ha
          exact nomatch ha
      rw [List.getElem?_take_of_lt hi] at ha ha'
      obtain ⟨tyP, rfl⟩ := hshapeP i a ha
      rw [hspPar i hi] at ha'
      obtain ⟨ty, rfl⟩ := hshapeS i a' ha'
      exact RenEqT.fvar
    have hlen : (fvsP.take cnP).length = (sp.take cnP).length := by
      rw [List.length_take, List.length_take, hfvsPlen, hsplen]
      omega
    obtain ⟨hds, -⟩ := instPisAt_renEq (f := f) (fvsP.take cnP)
      (sp.take cnP) hcinstP htake hrenCty hargs hlen
    rcases hxP : cdomsP[q]? with _ | xP
    · rw [List.getElem?_eq_none_iff] at hxP; omega
    rcases hxR : (cdoms.take cnP)[q]? with _ | xR
    · rw [List.getElem?_take_of_lt hq, List.getElem?_eq_none_iff] at hxR
      omega
    have hrq := hds q xP xR hxP hxR
    rw [List.getElem?_take_of_lt hq] at hxR
    rw [List.getD, hxR, List.getD, hxP]
    exact RenEqT.denoteMeta hro hrq (rP + cnF)
  -- assemble
  intro q hq ρ' hsat
  have hqlt : q < rP + cnF := by omega
  rcases hxq : fvs[q]? with _ | x
  · rw [List.getElem?_eq_none_iff] at hxq; omega
  obtain ⟨ty, rfl⟩ := hshapeS q x hxq
  have hspq : sp.getD q default = Expr.fvar q ty := by
    rw [List.getD, hspPar q hq, hxq]
    rfl
  refine ⟨.bvar ((rP + cnF) - 1 - q), by
    rw [hspq]; exact denoteMeta_fvar _ _ _ _, ⟨by simp, by simp⟩, ?_⟩
  intro dw hdw
  rw [hbridge q hq] at hdw
  have h := (hladder q hq ρ' (hsatB ρ' hsat) dw hdw).2
  simpa using h

end ConLeche.Model
