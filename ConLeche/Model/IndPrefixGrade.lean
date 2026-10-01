module

public import ConLeche.Model.IndDomGrade
import ConLeche.Model.IndRuns
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Annot.BitInst
public section

/-!
# The prefix domains, graded and fired (task #161, IND TIER part 4)

**The position induction, mechanized on the prefix branch.**  The
part-4 entry above names the shape the surviving stages need: at a
*fixed* padded frame and for *every* satisfying `ρ'`, walk the frame
positions upward, spending position `i`'s checked equality to earn
position `i + 1`'s b-side grading.  This file runs that induction for
the recursor-prefix walk (`hdePre`), which is the branch whose rows
`IotaRuns` already carries.

It is here for two reasons.  It is the zipper's prefix half and the
successor keeps it; and it **mechanizes the part-4 finding's positive
half** — the claim "the prefix branch closes on the recorded rows, the
field branch does not" is now a theorem on one side rather than an
argument on both.

The induction's two outputs are inseparable, which is the whole point:

* `WellDenotedV V (fun j => ρ' (j + (K - n))) (ΓP.getD (rP - 1 - n))` — the
  b-side grading at position `n`, walked out of the **recursor's own**
  tower by `wellDenotedV_tower_slot`, whose membership premises are the
  *earlier* positions' equalities;
* `interp … (Γs.getD (K - 1 - n)) = interp … (ΓP.getD (rP - 1 - n))`
  — position `n`'s equality, fired from the recorded run by
  `defEqAt_of_run` against that grading and `hokA_padded`.

The environment bookkeeping is all pointwise: `ρ''` for the recursor
tower is `ρ'` shifted by `K - rP`, so its slot `q` is `ρ' (q + K - rP)`
and slot `rP - 1 - m` lands on `ρ' (K - 1 - m)` — the statement frame's
own slot for opener `m`.  That coincidence is what lets `Sat` at the
statement frame feed the recursor tower's descent at all.
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
/-- **The prefix walk's gradings and equalities, by position.**  See
the module docstring; the two conclusions are proved by one strong
induction because each feeds the other one step later. -/
theorem prefixGradeFire {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {rP cnF : Nat}
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
    -- the public (recursor) frame
    {fvsP : List Expr} (hfvsPlen : fvsP.length = rP)
    (hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    {TV : AnnotTerm} {ΓP : List AnnotTerm} {RP : AnnotTerm}
    (htowerP : PiTeleAV rP TV ΓP RP)
    (hokTV : ∀ σ : Nat → V, WellDenotedV V σ TV)
    (hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default))
    -- the renamed recursor run and its identification
    {f : Name → Name} (hroT : RenameOk m.acval env f)
    {tyAR : Expr} (htyRw : tyAR.hasFvar = false)
    (htyRb : tyAR.looseBVarsBounded 0 = true)
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) tyAR = some (rdoms, rrest))
    (hrenP : ∀ n, n < rP →
      RenEqT f ((fvsP.map Expr.fvarTypeD).getD n default)
        (rdoms.getD n default))
    -- the recorded run
    (hdePre : DefEqListOk μ F env (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    {N : Nat} (hN : N ≤ rP + cnF) :
    ∀ n, n ≤ N → n < rP → ∀ ρ' : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ' →
      WellDenotedV V (fun j => ρ' (j + (rP + cnF - n)))
          (ΓP.getD (rP - 1 - n) default) ∧
        interp V (fun j => ρ' (j + (rP + cnF - n)))
            (Γs.getD (rP + cnF - 1 - n) default)
          = interp V (fun j => ρ' (j + (rP + cnF - n)))
              (ΓP.getD (rP - 1 - n) default) := by
  have hΓslen : Γs.length = (rP + cnF) := htowerS.length
  have hΓPlen : ΓP.length = rP := htowerP.length
  have hrdomslen : rdoms.length = rP := by
    have h := instPisAt_length _ hrinst
    rw [List.length_take, hfvslen] at h
    omega
  -- the padded context, named once
  have hΔlen : (List.replicate (rP + cnF - N) (AnnotTerm.sort 0) ++ Γs.drop (rP + cnF - N)).length = (rP + cnF) := by
    rw [List.length_append, List.length_replicate, List.length_drop,
      hΓslen]
    omega
  -- above the padding the padded context is the tower's
  have hent : ∀ i, i < N → (List.replicate (rP + cnF - N) (AnnotTerm.sort 0) ++ Γs.drop (rP + cnF - N))[(rP + cnF) - 1 - i]? = some
      (Γs.getD ((rP + cnF) - 1 - i) default) := by
    intro i hi
    rw [List.getElem?_append_right
      (by rw [List.length_replicate]; omega),
      List.length_replicate, List.getElem?_drop,
      show (rP + cnF) - N + ((rP + cnF) - 1 - i - ((rP + cnF) - N)) = (rP + cnF) - 1 - i from by omega,
      List.getD]
    rcases hg : Γs[(rP + cnF) - 1 - i]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  -- the a-side gradings, from the statement type's own
  have hokAll : ∀ i, i ≤ N → i < rP + cnF → ∀ ρ' : Nat → V, Sat V (List.replicate (rP + cnF - N) (AnnotTerm.sort 0) ++ Γs.drop (rP + cnF - N)) ρ' →
      WellDenotedV V (fun j => ρ' (j + ((rP + cnF) - 1 - i) + 1))
        (Γs.getD ((rP + cnF) - 1 - i) default) := by
    intro i hi hiK ρ' hsat
    refine wellDenotedV_tower_slot (rP + cnF) htowerS (hokTst _) ((rP + cnF) - 1 - i)
      (by omega) (fun q hq1 hq2 => ?_)
    exact hsat q (Γs.getD q default)
      (by
        rw [List.getElem?_append_right
          (by rw [List.length_replicate]; omega),
          List.length_replicate, List.getElem?_drop,
          show (rP + cnF) - N + (q - ((rP + cnF) - N)) = q from by omega, List.getD]
        rcases hg : Γs[q]? with _ | A
        · rw [List.getElem?_eq_none_iff] at hg; omega
        · rfl)
  -- the frame's per-index data
  have hfvsAt : ∀ n, n < (rP + cnF) → ∃ ty, fvs[n]? = some (.fvar n ty) := by
    intro n hn
    rcases hx : fvs[n]? with _ | x
    · rw [List.getElem?_eq_none_iff] at hx; omega
    · obtain ⟨ty, rfl⟩ := hshapeS n x hx
      exact ⟨_, rfl⟩
  have hfvsPAt : ∀ n, n < rP →
      ∃ ty, fvsP[n]? = some (.fvar n ty) := by
    intro n hn
    rcases hx : fvsP[n]? with _ | x
    · rw [List.getElem?_eq_none_iff] at hx; omega
    · obtain ⟨ty, rfl⟩ := hshapeP n x hx
      exact ⟨_, rfl⟩
  -- the recursor run's per-index scope
  have hwsRdAll : ∀ n, n < rP → Expr.WScoped n (rdoms.getD n default) := by
    intro n hn
    have h1 := instPisAt_index_WScoped (fvs.take rP) (d := 0) hrinst
      (Expr.WScoped.of_not_hasFvar htyRw) ?_ n (rdoms.getD n default) ?_
    · simpa using h1
    · intro i a ha
      have hi : i < rP := by
        rcases Nat.lt_or_ge i rP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none
            (by rw [List.length_take]; omega)] at ha
          exact nomatch ha
      rw [List.getElem?_take_of_lt hi] at ha
      obtain ⟨ty', rfl⟩ := hshapeS i a ha
      have h'' := hwsFvs _ (List.mem_of_getElem? ha)
      simp only [Expr.WScoped] at h'' ⊢
      exact ⟨by omega, h''.2⟩
    · rw [List.getD]
      rcases hr : rdoms[n]? with _ | r
      · rw [List.getElem?_eq_none_iff] at hr; omega
      · rfl
  have hleafRdAll : ∀ n, n < rP →
      ∀ l ∈ (rdoms.getD n default).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs := by
    intro n hn l hl
    have hmem : rdoms.getD n default ∈ rdoms := by
      rw [List.getD]
      rcases hr : rdoms[n]? with _ | r
      · rw [List.getElem?_eq_none_iff] at hr; omega
      · exact List.mem_of_getElem? hr
    rcases instPisAt_leaves _ hrinst l (Or.inl ⟨_, hmem, hl⟩) with
      hty' | ⟨a, ha, hla⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyRw] at hty'
      exact nomatch hty'
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      have hqrP : q < rP := by
        rcases Nat.lt_or_ge q rP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none
            (by rw [List.length_take]; omega)] at hq
          exact nomatch hq
      rw [List.getElem?_take_of_lt hqrP] at hq
      obtain ⟨ty', rfl⟩ := hshapeS q _ hq
      rw [Expr.fvarLeaves] at hla
      rcases List.mem_cons.mp hla with rfl | hla'
      · exact List.mem_of_getElem? hq
      · exact hleafClosed l ⟨_, List.mem_of_getElem? hq, by
          rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hla'⟩
  -- the recursor run's per-index bvar bound
  have hbRdAll : ∀ n, n < rP →
      (rdoms.getD n default).looseBVarsBounded 0 = true := by
    intro n hn
    have hmem : rdoms.getD n default ∈ rdoms := by
      rw [List.getD]
      rcases hr : rdoms[n]? with _ | r
      · rw [List.getElem?_eq_none_iff] at hr; omega
      · exact List.mem_of_getElem? hr
    refine (instPisAt_bounded _ hrinst htyRb ?_).1 _ hmem
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    have hqrP : q < rP := by
      rcases Nat.lt_or_ge q rP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hq
        exact nomatch hq
    rw [List.getElem?_take_of_lt hqrP] at hq
    obtain ⟨ty', rfl⟩ := hshapeS q _ hq
    rfl
  -- the strong induction on the position: the grading and the
  -- equality, both at EVERY satisfying environment, because the
  -- run conversion consumes the grading in ∀-form
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro hnN hnrP
  obtain ⟨ty, hx⟩ := hfvsAt n (by omega)
  obtain ⟨tyP, hxP⟩ := hfvsPAt n hnrP
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
  have hwsRd : Expr.WScoped n (rdoms.getD n default) := hwsRdAll n hnrP
  have hleafRd : ∀ l ∈ (rdoms.getD n default).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs := hleafRdAll n hnrP
  have hltRd : ∀ l ∈ (rdoms.getD n default).fvarLeaves, l.1 < n :=
    Expr.fvarLeaves_lt_of_wscoped hwsRd
  -- the two readings at the frame depth
  have hdomTy : denoteMeta m.acval env φ n ty
      = some (Γs.getD ((rP + cnF) - 1 - n) default) := hdomsS0 n _ hx
  have hrdden : denoteMeta m.acval env φ n (rdoms.getD n default)
      = some (ΓP.getD (rP - 1 - n) default) := by
    have h1 := RenEqT.denoteMeta (acval := m.acval) (φ := φ) hroT
      (hrenP n hnrP) n
    rw [show (fvsP.map Expr.fvarTypeD).getD n default = tyP from by
      rw [List.getD, List.getElem?_map, hxP]
      rfl] at h1
    rw [h1]
    exact hdomsP0 n _ hxP
  have hAv : denoteMeta m.acval env φ (rP + cnF) ty
      = some ((Γs.getD ((rP + cnF) - 1 - n) default).liftN ((rP + cnF) - n) 0) := by
    rw [denoteMeta_lift m.acval_closed hwsTy (rP + cnF) (by omega), hdomTy]
    rfl
  have hBv : denoteMeta m.acval env φ (rP + cnF) (rdoms.getD n default)
      = some ((ΓP.getD (rP - 1 - n) default).liftN ((rP + cnF) - n) 0) := by
    rw [denoteMeta_lift m.acval_closed hwsRd (rP + cnF) (by omega), hrdden]
    rfl
  -- **the b-side grading, at every satisfying environment**: the
  -- recursor's own tower, descended by `wellDenotedV_tower_slot`, whose
  -- membership premises are the earlier positions' equalities
  have hgrBall : ∀ ρ0 : Nat → V, Sat V (List.replicate (rP + cnF - N) (AnnotTerm.sort 0) ++ Γs.drop (rP + cnF - N)) ρ0 →
      WellDenotedV V (fun j => ρ0 (j + ((rP + cnF) - n)))
        (ΓP.getD (rP - 1 - n) default) := by
    intro ρ0 hρ0
    have hbase : WellDenotedV V
        (fun j => (fun t => ρ0 (t + ((rP + cnF) - rP))) (j + rP)) TV := by
      have h := hokTV (fun j => ρ0 (j + (rP + cnF)))
      refine cast (by congr 1; funext j; congr 1; omega) h
    refine cast ?_ (wellDenotedV_tower_slot rP htowerP
      (ρ' := fun t => ρ0 (t + ((rP + cnF) - rP))) hbase (rP - 1 - n) (by omega)
      (fun q hq1 hq2 => ?_))
    · congr 1
      funext j
      show ρ0 (j + (rP - 1 - n) + 1 + ((rP + cnF) - rP)) = ρ0 (j + ((rP + cnF) - n))
      congr 1
      omega
    · obtain ⟨-, heq⟩ := ihn (rP - 1 - q) (by omega) (by omega)
        (by omega) ρ0 hρ0
      have hsatm := hρ0 ((rP + cnF) - 1 - (rP - 1 - q))
        (Γs.getD ((rP + cnF) - 1 - (rP - 1 - q)) default)
        (hent (rP - 1 - q) (by omega))
      rw [show (fun j => ρ0 (j + ((rP + cnF) - 1 - (rP - 1 - q)) + 1))
          = (fun j => ρ0 (j + ((rP + cnF) - (rP - 1 - q)))) from by
        funext j; congr 1; omega] at hsatm
      rw [heq] at hsatm
      show (fun t => ρ0 (t + ((rP + cnF) - rP))) q ∈ˢ _
      rw [show (fun t => ρ0 (t + ((rP + cnF) - rP))) q
          = ρ0 ((rP + cnF) - 1 - (rP - 1 - q)) from by
        show ρ0 (q + ((rP + cnF) - rP)) = _
        congr 1
        omega,
        show (fun j => (fun t => ρ0 (t + ((rP + cnF) - rP))) (j + q + 1))
          = (fun j => ρ0 (j + ((rP + cnF) - (rP - 1 - q)))) from by
        funext j
        show ρ0 (j + q + 1 + ((rP + cnF) - rP)) = _
        congr 1
        omega,
        show ΓP.getD q default
          = ΓP.getD (rP - 1 - (rP - 1 - q)) default from by
        congr 1
        omega]
      exact hsatm
  intro ρ' hsat
  refine ⟨hgrBall ρ' hsat, ?_⟩
  -- the equality: fire the recorded run at the padded frame
  have hrun : isDefEqCore μ env F (rP + cnF) ty (rdoms.getD n default)
      = .ok true := by
    have h := defEqListOk_getD hdePre n
      (by rw [List.length_map, List.length_take, hfvslen]; omega)
    rw [show ((fvs.take rP).map Expr.fvarTypeD).getD n default = ty from by
      rw [List.getD, List.getElem?_map, List.getElem?_take_of_lt hnrP,
        hx]
      rfl] at h
    exact h
  have hLbTy : Expr.LeavesBounded ty := fun l hl =>
    hlbFvs l.1 l.2 (hleafTy l hl)
  have hLbRd : Expr.LeavesBounded (rdoms.getD n default) := fun l hl =>
    hlbFvs l.1 l.2 (hleafRd l hl)
  have hbTy : ty.looseBVarsBounded 0 = true := hlbFvs n ty hmemFvs
  have hbRd : (rdoms.getD n default).looseBVarsBounded 0 = true :=
    hbRdAll n hnrP
  have hshiftEnv : ∀ ρ0 : Nat → V,
      shiftE ((rP + cnF) - n) 0 ρ0 = (fun j => ρ0 (j + ((rP + cnF) - n))) := by
    intro ρ0
    funext j
    show (if j < 0 then ρ0 j else ρ0 (j + ((rP + cnF) - n))) = _
    rw [if_neg (Nat.not_lt_zero j)]
  have hfire := defEqAt_of_run (m := m) hclaims (k := (rP + cnF)) (fvs := fvs)
    (Aa := fun i => Γs.getD ((rP + cnF) - 1 - i) default) (Δa := (List.replicate (rP + cnF - N) (AnnotTerm.sort 0) ++ Γs.drop (rP + cnF - N))) hΔlen
    hshapeS hwsFvs (fun i x hix => hdomsS0 i x hix) (n := n)
    (fun i hi => hent i (by omega))
    (fun i hi ρ0 hρ0 => hokAll i (by omega) (by omega) ρ0 hρ0)
    hrun (hwsTy.mono (by omega)) hbTy hLbTy
    (hwsRd.mono (by omega)) hbRd hLbRd
    hleafTy hltTy hleafRd hltRd hAv hBv
    (fun ρ0 hρ0 => (WellDenotedV_liftN V ((rP + cnF) - n) _ 0 ρ0).mpr (by
      rw [hshiftEnv ρ0]
      have h := hokAll n (by omega) (by omega) ρ0 hρ0
      rw [show (fun j => ρ0 (j + ((rP + cnF) - 1 - n) + 1))
          = (fun j => ρ0 (j + ((rP + cnF) - n))) from by
        funext j; congr 1; omega] at h
      exact h))
    (fun ρ0 hρ0 => (WellDenotedV_liftN V ((rP + cnF) - n) _ 0 ρ0).mpr (by
      rw [hshiftEnv ρ0]
      exact hgrBall ρ0 hρ0))
    hsat
  rw [interp_liftN, interp_liftN, hshiftEnv ρ'] at hfire
  exact hfire

end ConLeche.Model
