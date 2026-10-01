module

public import ConLeche.Model.IndAnnotKit
import ConLeche.Model.Annot.BitInst
public section

/-!
# The transport's layer memberships (task #161, IND TIER part 5)

`annotPFrameEqS` and `annotMemS` at the reading — the last two stages
of the `annotS` cluster, and `lamTowerStep`'s `hmem` input.

* **`annotPFrameEq`** is the per-position annotation identification:
  at every frame position the statement opener's annotation reads to
  the same value as the *public* frame opener's.  At P this is not a
  new walk — the two position ladders (`prefixGradeFire`,
  `fieldGradeFire`) have already fired the frame walks, so all this
  stage does is compose their equalities with the *renaming* identity
  of the two runs' domains (`instPisAt_renEq` + `RenEqT.denoteMeta`,
  again free because the two spines' field openers sit at equal
  indices).  It also carries the public annotation's grading, which
  the same ladders produce.
* **`annotMem`** is one more position induction of the now-familiar
  shape: at position `k`, the earlier positions' equalities transport
  `Sat`'s memberships into the λ-tower's slots, `wellDenotedV_lamTower_slot`
  grades slot `k` out of the rule right-hand side's own grading, and
  the recorded lam walk fires — at the **statement** frame's context,
  because `CtxOk`'s per-leaf obligation is semantic and
  `annotPFrameEq` is exactly the equation it asks for
  (`ctxOk_of_walked_openers`).

The rule right-hand side's grading enters as `hokRa`.  It is the third
exposure's row — see the DESIGN.md entry — and it is the *only*
outstanding input of the whole transport.
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
/-- **The per-position annotation identification, at the reading**
(`annotPFrameEqS`): the public frame's opener annotations read to the
statement tower's slots, and are graded. -/
theorem annotPFrameEq {m : EnvModel V env}
    {f : Name → Name} (hroT : RenameOk m.acval env f)
    {rP cnP cnF : Nat}
    {Γs : List AnnotTerm}
    -- the public frame: the recursor prefix and the constructor fields
    {tyA : Expr} {fvsPl : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsPl, restP))
    {ΓP : List AnnotTerm}
    (hdomsP0 : ∀ (i : Nat) (x : Expr), fvsPl[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    {cvjty cvjR : Expr} (hrenCvj : RenEqT f cvjty cvjR)
    {psP psR : List Expr}
    (hpsPlen : psP.length = cnP) (hpsRlen : psR.length = cnP)
    (hpsRen : ∀ (i : Nat) (a a' : Expr), psP[i]? = some a →
      psR[i]? = some a' → RenEqT f a a')
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt psP cvjty = some (cdomsP, crestP))
    {xFvsP : List Expr} {ldoms : Expr}
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    (hwsX : ∀ x ∈ xFvsP, Expr.WScoped (rP + cnF) x)
    (hwsPl : ∀ x ∈ fvsPl, Expr.WScoped rP x)
    {Γx : List AnnotTerm}
    (hdomsX0 : ∀ (i : Nat) (x : Expr), xFvsP[i]? = some x →
      denoteMeta m.acval env φ (rP + i) (Expr.fvarTypeD x)
        = some (Γx.getD (cnF - 1 - i) default))
    -- the statement frame's runs
    {fvs : List Expr} (hfvslen : fvs.length = rP + cnF)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt (psR ++ fvs.drop rP) cvjR
      = some (cdoms, cres))
    (hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    -- the two ladders, fired at the ambient context
    {Δa : List AnnotTerm}
    (hpre : ∀ n, n < rP → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      WellDenotedV V (fun j => ρ' (j + (rP + cnF - n)))
          (ΓP.getD (rP - 1 - n) default) ∧
        interp V (fun j => ρ' (j + (rP + cnF - n)))
            (Γs.getD (rP + cnF - 1 - n) default)
          = interp V (fun j => ρ' (j + (rP + cnF - n)))
              (ΓP.getD (rP - 1 - n) default))
    (hfld : ∀ n, rP ≤ n → n < rP + cnF → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      ∀ dw, denoteMeta m.acval env φ (rP + cnF)
          (cdoms.getD (cnP + (n - rP)) default) = some dw →
        WellDenotedV V ρ' dw ∧
          interp V (fun j => ρ' (j + (rP + cnF - n)))
              (Γs.getD (rP + cnF - 1 - n) default)
            = interp V ρ' dw) :
    ∀ i, i < rP + cnF → ∃ Bi : AnnotTerm,
      denoteMeta m.acval env φ (rP + cnF)
        (Expr.fvarTypeD ((fvsPl ++ xFvsP).getD i default)) = some Bi ∧
      ∀ ρ' : Nat → V, Sat V Δa ρ' →
        WellDenotedV V ρ' Bi ∧
          interp V (fun j => ρ' (j + (rP + cnF - i)))
              (Γs.getD (rP + cnF - 1 - i) default)
            = interp V ρ' Bi := by
  have hfvsPlen : fvsPl.length = rP := openPisAtFvars_length _ hopenP
  have hxlen : xFvsP.length = cnF := openPisAtFvars_length _ hopenXP
  have hPlen : (fvsPl ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPlen, hxlen]
  -- the two runs' domains agree up to the renaming
  have hPx : Expr.instPisAt xFvsP crestP
      = some (xFvsP.map Expr.fvarTypeD, ldoms) :=
    openPisAtFvars_instPisAt _ hopenXP
  have hPfld : Expr.instPisAt (psP ++ xFvsP) cvjty
      = some (cdomsP ++ xFvsP.map Expr.fvarTypeD, ldoms) :=
    Expr.instPisAt_append _ hcinstP hPx
  have hcdomsPlen : cdomsP.length = cnP := by
    have h := instPisAt_length _ hcinstP
    rw [hpsPlen] at h
    exact h
  have hargs : ∀ (i : Nat) (a a' : Expr), (psP ++ xFvsP)[i]? = some a →
      (psR ++ fvs.drop rP)[i]? = some a' → RenEqT f a a' := by
    intro i a a' ha ha'
    rcases Nat.lt_or_ge i cnP with hi | hi
    · rw [List.getElem?_append_left (by omega)] at ha
      rw [List.getElem?_append_left (by omega)] at ha'
      exact hpsRen i a a' ha ha'
    · rw [List.getElem?_append_right (by omega), hpsPlen] at ha
      rw [List.getElem?_append_right (by omega), hpsRlen] at ha'
      obtain ⟨ty, ha2⟩ := openPisAtFvars_index _ _ _ hopenXP (i - cnP) a ha
      rw [List.getElem?_drop] at ha'
      obtain ⟨ty', rfl⟩ := hshapeS (rP + (i - cnP)) a' ha'
      rw [ha2]
      exact RenEqT.fvar
  have hlenA : (psP ++ xFvsP).length = (psR ++ fvs.drop rP).length := by
    rw [List.length_append, List.length_append, List.length_drop,
      hpsPlen, hpsRlen, hxlen, hfvslen]
    omega
  obtain ⟨hds, -⟩ := instPisAt_renEq (f := f) (psP ++ xFvsP)
    (psR ++ fvs.drop rP) hPfld hcinst hrenCvj hargs hlenA
  have hcdlen : cdoms.length = cnP + cnF := by
    have h := instPisAt_length _ hcinst
    rw [List.length_append, List.length_drop, hpsRlen, hfvslen] at h
    omega
  have hbridge : ∀ (j : Nat), j < cnF → ∀ d : Nat,
      denoteMeta m.acval env φ d (cdoms.getD (cnP + j) default)
        = denoteMeta m.acval env φ d
            (Expr.fvarTypeD (xFvsP.getD j default)) := by
    intro j hj d
    rcases hxj : xFvsP[j]? with _ | xj
    · rw [List.getElem?_eq_none_iff, hxlen] at hxj; omega
    rcases hcj : cdoms[cnP + j]? with _ | cj
    · rw [List.getElem?_eq_none_iff, hcdlen] at hcj; omega
    have hleft : (cdomsP ++ xFvsP.map Expr.fvarTypeD)[cnP + j]?
        = some (Expr.fvarTypeD xj) := by
      rw [List.getElem?_append_right (by omega), hcdomsPlen,
        Nat.add_sub_cancel_left, List.getElem?_map, hxj]
      rfl
    have hrq := hds (cnP + j) _ _ hleft hcj
    rw [List.getD, hcj, List.getD, hxj]
    exact RenEqT.denoteMeta hroT hrq d
  -- position by position
  intro i hiK
  rcases Nat.lt_or_ge i rP with hi | hi
  · -- prefix: the public opener's annotation lifts the recursor slot
    rcases hp : fvsPl[i]? with _ | px
    · rw [List.getElem?_eq_none_iff, hfvsPlen] at hp; omega
    obtain ⟨ty, hp2⟩ := openPisAtFvars_index _ _ _ hopenP i px hp
    rw [Nat.zero_add] at hp2
    have hgetP : (fvsPl ++ xFvsP).getD i default = px := by
      rw [List.getD, List.getElem?_append_left (by omega), hp]
      rfl
    have hwsTy : Expr.WScoped i ty := by
      have hw := hwsPl _ (List.mem_of_getElem? hp)
      rw [hp2] at hw
      simp only [Expr.WScoped] at hw
      exact hw.2
    have hdomI : denoteMeta m.acval env φ i ty
        = some (ΓP.getD (rP - 1 - i) default) := by
      have h := hdomsP0 i px hp
      rw [hp2] at h
      exact h
    refine ⟨(ΓP.getD (rP - 1 - i) default).liftN (rP + cnF - i) 0, ?_, ?_⟩
    · rw [hgetP, hp2,
        show Expr.fvarTypeD (Expr.fvar i ty) = ty from rfl,
        denoteMeta_lift m.acval_closed hwsTy (rP + cnF) (by omega), hdomI]
      rfl
    · intro ρ' hρ'
      obtain ⟨hokP, heqP⟩ := hpre i hi ρ' hρ'
      have hshiftEnv : shiftE (rP + cnF - i) 0 ρ'
          = (fun j => ρ' (j + (rP + cnF - i))) := by
        funext j
        show (if j < 0 then ρ' j else ρ' (j + (rP + cnF - i))) = _
        rw [if_neg (Nat.not_lt_zero j)]
      refine ⟨(WellDenotedV_liftN V (rP + cnF - i) _ 0 ρ').mpr ?_, ?_⟩
      · rw [hshiftEnv]
        exact hokP
      · rw [interp_liftN, hshiftEnv]
        exact heqP
  · -- fields: the public opener's annotation is the crossed domain
    obtain ⟨j, rfl⟩ : ∃ j, i = rP + j := ⟨i - rP, by omega⟩
    have hjc : j < cnF := by omega
    rcases hxj : xFvsP[j]? with _ | xj
    · rw [List.getElem?_eq_none_iff, hxlen] at hxj; omega
    obtain ⟨ty, hx2⟩ := openPisAtFvars_index _ _ _ hopenXP j xj hxj
    have hgetX : (fvsPl ++ xFvsP).getD (rP + j) default = xj := by
      rw [List.getD, List.getElem?_append_right (by omega), hfvsPlen,
        Nat.add_sub_cancel_left, hxj]
      rfl
    have hwsTy : Expr.WScoped (rP + j) ty := by
      have hw := hwsX _ (List.mem_of_getElem? hxj)
      rw [hx2] at hw
      simp only [Expr.WScoped] at hw
      exact hw.2
    have hdomI : denoteMeta m.acval env φ (rP + j) ty
        = some (Γx.getD (cnF - 1 - j) default) := by
      have h := hdomsX0 j xj hxj
      rw [hx2] at h
      exact h
    have hBiden : denoteMeta m.acval env φ (rP + cnF)
        (Expr.fvarTypeD ((fvsPl ++ xFvsP).getD (rP + j) default))
        = some ((Γx.getD (cnF - 1 - j) default).liftN
            (rP + cnF - (rP + j)) 0) := by
      rw [hgetX, hx2,
        show Expr.fvarTypeD (Expr.fvar (rP + j) ty) = ty from rfl,
        denoteMeta_lift m.acval_closed hwsTy (rP + cnF) (by omega), hdomI]
      rfl
    refine ⟨(Γx.getD (cnF - 1 - j) default).liftN
      (rP + cnF - (rP + j)) 0, hBiden, ?_⟩
    intro ρ' hρ'
    have hcd : denoteMeta m.acval env φ (rP + cnF)
        (cdoms.getD (cnP + (rP + j - rP)) default)
        = some ((Γx.getD (cnF - 1 - j) default).liftN
            (rP + cnF - (rP + j)) 0) := by
      rw [show rP + j - rP = j from by omega, hbridge j hjc (rP + cnF),
        show Expr.fvarTypeD (xFvsP.getD j default)
          = Expr.fvarTypeD ((fvsPl ++ xFvsP).getD (rP + j) default) from by
          rw [hgetX, List.getD, hxj]
          rfl]
      exact hBiden
    obtain ⟨hokd, heqd⟩ := hfld (rP + j) (by omega) (by omega) ρ' hρ' _ hcd
    exact ⟨hokd, heqd⟩

set_option maxHeartbeats 6400000 in
/-- **The layer memberships, at the reading** (`annotMemS`): at every
frame position the statement tower's slot and the rule λ-tower's slot
read to the same value, and the λ slot is graded.  One more position
induction: the earlier positions' equalities carry `Sat`'s
memberships into the λ tower, `wellDenotedV_lamTower_slot` grades slot `k`
out of `hokRa`, and the recorded lam walk fires at the statement
frame's own context through `ctxOk_of_walked_openers`. -/
theorem annotMem {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {K : Nat}
    -- the public frame
    {pfvs : List Expr} (hPlen : pfvs.length = K)
    (hPshape : ∀ (i : Nat) (x : Expr), pfvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hPws : ∀ x ∈ pfvs, Expr.WScoped K x)
    (hPleafClosed : ∀ l, (∃ x ∈ pfvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ pfvs)
    (hlbP : ∀ (i : Nat) (ty : Expr),
      Expr.fvar i ty ∈ pfvs → ty.looseBVarsBounded 0 = true)
    -- the statement tower and the ambient context
    {Γs : List AnnotTerm} {Δa : List AnnotTerm} (hΔalen : Δa.length = K)
    (hΔaent : ∀ i, i < K →
      Δa[K - 1 - i]? = some (Γs.getD (K - 1 - i) default))
    -- the per-position identification (`annotPFrameEq`)
    (hIdent : ∀ i, i < K → ∃ Bi : AnnotTerm,
      denoteMeta m.acval env φ K
        (Expr.fvarTypeD (pfvs.getD i default)) = some Bi ∧
      ∀ ρ' : Nat → V, Sat V Δa ρ' →
        WellDenotedV V ρ' Bi ∧
          interp V (fun j => ρ' (j + (K - i)))
              (Γs.getD (K - 1 - i) default) = interp V ρ' Bi)
    -- the rule's right-hand side and its λ-tower
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {Ra : AnnotTerm} (hokRa : ∀ σ : Nat → V, WellDenotedV V σ Ra)
    {ldomsL : List Expr} {lrest2 : Expr}
    (hinstLam : Expr.instLamsAt pfvs rhsA = some (ldomsL, lrest2))
    {Γlam : List AnnotTerm} {C : AnnotTerm} (htowerLam : LamTele K Ra Γlam C)
    (hdomsLam : ∀ (i : Nat) (x : Expr), ldomsL[i]? = some x →
      denoteMeta m.acval env φ i x = some (Γlam.getD (K - 1 - i) default))
    -- the recorded lam walk
    (hdeLam : DefEqListOk μ F env K (pfvs.map Expr.fvarTypeD) ldomsL) :
    ∀ k, k < K → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      WellDenotedV V (fun j => ρ' (j + (K - k)))
          (Γlam.getD (K - 1 - k) default) ∧
        interp V (fun j => ρ' (j + (K - k)))
            (Γs.getD (K - 1 - k) default)
          = interp V (fun j => ρ' (j + (K - k)))
              (Γlam.getD (K - 1 - k) default) := by
  have hldlen : ldomsL.length = K := by
    rw [instLamsAt_length _ hinstLam, hPlen]
  -- the frame's own bounds
  have hPlt : ∀ l : Nat × Expr,
      Expr.fvar l.1 l.2 ∈ pfvs → l.1 < K := by
    intro l hl
    have hw := hPws _ hl
    simp only [Expr.WScoped] at hw
    exact hw.1
  have hPbnd : ∀ a ∈ pfvs, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hPshape q a hq
    rfl
  -- the walk datum `ctxOk_of_walked_openers` reads
  have hwalk : ∀ (i : Nat) (x : Expr), pfvs[i]? = some x →
      ∃ tya, denoteMeta m.acval env φ K (Expr.fvarTypeD x) = some tya ∧
        (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ tya
            = interp V (fun j => ρ (j + (K - 1 - i) + 1))
                (Γs.getD (K - 1 - i) default)) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ tya) := by
    intro i x hx
    have hiK : i < K := by
      have h := (List.getElem?_eq_some_iff.mp hx).1
      rw [hPlen] at h
      exact h
    obtain ⟨Bi, hBi, hBiP⟩ := hIdent i hiK
    have hgx : pfvs.getD i default = x := by
      rw [List.getD, hx]
      rfl
    rw [hgx] at hBi
    refine ⟨Bi, hBi, fun ρ hρ => ?_, fun ρ hρ => (hBiP ρ hρ).1⟩
    rw [show (fun j => ρ (j + (K - 1 - i) + 1))
        = (fun j => ρ (j + (K - i))) from by
      funext j; congr 1; omega]
    exact ((hBiP ρ hρ).2).symm
  -- the strong induction on the position
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro hkK
  -- the λ tower's slot, graded at every satisfying environment
  have hgrall : ∀ ρ0 : Nat → V, Sat V Δa ρ0 →
      WellDenotedV V (fun j => ρ0 (j + (K - k)))
        (Γlam.getD (K - 1 - k) default) := by
    intro ρ0 hρ0
    refine cast ?_ (wellDenotedV_lamTower_slot K htowerLam (ρ' := ρ0)
      (hokRa _) (K - 1 - k) (by omega) (fun q hq1 hq2 => ?_))
    · congr 1
      funext j
      congr 1
      omega
    · obtain ⟨-, heq⟩ := ihk (K - 1 - q) (by omega) (by omega) ρ0 hρ0
      have hsatm := hρ0 q (Γs.getD q default) (by
        have h := hΔaent (K - 1 - q) (by omega)
        rw [show K - 1 - (K - 1 - q) = q from by omega] at h
        exact h)
      show ρ0 q ∈ˢ interp V (fun j => ρ0 (j + q + 1))
        (Γlam.getD q default)
      rw [show Γlam.getD q default
            = Γlam.getD (K - 1 - (K - 1 - q)) default from by
          congr 1
          omega,
        show (fun j => ρ0 (j + q + 1))
            = (fun j => ρ0 (j + (K - (K - 1 - q)))) from by
          funext j
          congr 1
          omega,
        ← heq,
        show Γs.getD (K - 1 - (K - 1 - q)) default
            = Γs.getD q default from by
          congr 1
          omega,
        show (fun j => ρ0 (j + (K - (K - 1 - q))))
            = (fun j => ρ0 (j + q + 1)) from by
          funext j
          congr 1
          omega]
      exact hsatm
  intro ρ' hρ'
  refine ⟨hgrall ρ' hρ', ?_⟩
  -- the two comparands at position `k`
  obtain ⟨Bk, hBk, hBkP⟩ := hIdent k hkK
  rcases hpk : pfvs[k]? with _ | pk
  · rw [List.getElem?_eq_none_iff, hPlen] at hpk; omega
  obtain ⟨ty, rfl⟩ := hPshape k pk hpk
  have hgpk : pfvs.getD k default = Expr.fvar k ty := by
    rw [List.getD, hpk]
    rfl
  rcases hld : ldomsL[k]? with _ | ld
  · rw [List.getElem?_eq_none_iff, hldlen] at hld; omega
  have hgld : ldomsL.getD k default = ld := by
    rw [List.getD, hld]
    rfl
  -- the run at position `k`
  have hrun : isDefEqCore μ env F K ty ld = .ok true := by
    have h := defEqListOk_getD hdeLam k (by
      rw [List.length_map, hPlen]; omega)
    rw [show (pfvs.map Expr.fvarTypeD).getD k default = ty from by
      rw [List.getD, List.getElem?_map, hpk]
      rfl, hgld] at h
    exact h
  -- the b-side's reading at the frame depth
  have hwsLd : Expr.WScoped k ld := by
    have h1 := instLamsAt_index_WScoped pfvs (d := 0) hinstLam
      (Expr.WScoped.of_not_hasFvar hrhsw) ?_ k ld hld
    · simpa using h1
    · intro i a ha
      obtain ⟨ty', rfl⟩ := hPshape i a ha
      have hw := hPws _ (List.mem_of_getElem? ha)
      simp only [Expr.WScoped] at hw ⊢
      exact ⟨by omega, hw.2⟩
  have hLkden : denoteMeta m.acval env φ K ld
      = some ((Γlam.getD (K - 1 - k) default).liftN (K - k) 0) := by
    rw [denoteMeta_lift m.acval_closed hwsLd K (by omega),
      hdomsLam k ld hld]
    rfl
  -- leaves and frames of the two comparands
  have hmemPk : Expr.fvar k ty ∈ pfvs := List.mem_of_getElem? hpk
  have hleafA : ∀ l ∈ ty.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ pfvs := by
    intro l hl
    exact hPleafClosed l ⟨_, hmemPk, by
      rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl⟩
  have hleafB : ∀ l ∈ ld.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ pfvs := by
    intro l hl
    rcases instLamsAt_leaves _ hinstLam l
      (Or.inl ⟨_, List.mem_of_getElem? hld, hl⟩) with h0 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at h0
      exact nomatch h0
    · exact hPleafClosed l ⟨a, ha, hla⟩
  have hwsA : Expr.WScoped k ty := by
    have hw := hPws _ hmemPk
    simp only [Expr.WScoped] at hw
    exact hw.2
  have hbA : ty.looseBVarsBounded 0 = true := hlbP k ty hmemPk
  have hbB : ld.looseBVarsBounded 0 = true :=
    (instLamsAt_bounded _ hinstLam hrhsb hPbnd).1 _
      (List.mem_of_getElem? hld)
  -- the contexts, walked
  have hctxA : CtxOk m φ K Δa ty :=
    ctxOk_of_walked_openers (m := m) hΔalen hPshape hPws hwalk
      (n := K) hleafA (fun l hl => hPlt l (hleafA l hl)) hΔaent
  have hctxB : CtxOk m φ K Δa ld :=
    ctxOk_of_walked_openers (m := m) hΔalen hPshape hPws hwalk
      (n := K) hleafB (fun l hl => hPlt l (hleafB l hl)) hΔaent
  have hBk' : denoteMeta m.acval env φ K ty = some Bk := by
    rw [hgpk] at hBk
    exact hBk
  have hshiftEnv : ∀ ρ0 : Nat → V,
      shiftE (K - k) 0 ρ0 = (fun j => ρ0 (j + (K - k))) := by
    intro ρ0
    funext j
    show (if j < 0 then ρ0 j else ρ0 (j + (K - k))) = _
    rw [if_neg (Nat.not_lt_zero j)]
  have hfire := hclaims hrun (hwsA.mono (by omega)) hbA
    (fun l hl => hlbP l.1 l.2 (hleafA l hl))
    (hwsLd.mono (by omega)) hbB
    (fun l hl => hlbP l.1 l.2 (hleafB l hl))
    hctxA hctxB hBk' hLkden
    (fun ρ0 hρ0 => (hBkP ρ0 hρ0).1)
    (fun ρ0 hρ0 => (WellDenotedV_liftN V (K - k) _ 0 ρ0).mpr (by
      rw [hshiftEnv ρ0]
      exact hgrall ρ0 hρ0))
    ρ' hρ'
  rw [interp_liftN, hshiftEnv ρ'] at hfire
  rw [(hBkP ρ' hρ').2, hfire]

end ConLeche.Model
