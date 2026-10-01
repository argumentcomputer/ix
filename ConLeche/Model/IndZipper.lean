module

public import ConLeche.Model.IndPlainParam
import ConLeche.Model.IndZipField
import ConLeche.Model.IndStageKit
import ConLeche.Model.Annot.BitInst
public section

/-!
# The zipper, at the reading (task #161, IND TIER part 5)

`zipperS`'s transpose, and the stage the whole part-4/part-5 supply
layer was built for: the fired statement spine `xs.take rP ++
ys.drop cnP` **satisfies** the checked `iota_j` statement's context and
**fits** its telescope.

The construction is v1's — one strong induction on the frame position,
introducing the padded satisfaction at each step (`sat_pad_of_mems`)
and stripping it again (`padE2_shiftE`) — with the *firing* replaced.
Where v1 instantiates a `DefEqAtW` derivation and reads it through
`DefEq.sound`, the P tier spends the position inductions:

* the prefix positions are `prefixGradeFire` (part 4), whose equality
  identifies the statement tower's slot with the recursor tower's, so
  the prefix fit's own chain membership crosses;
* the field positions are `fieldGradeFire` (part 5), whose equality
  identifies the statement tower's slot with the constructor run's
  crossed domain, so the mixed fit's chain membership crosses through
  `zipFieldTermEq`'s term identity.

The parameter positions of the constructor run enter abstractly, as
`hpar` — that is where `.plain` and `.nested` differ and where nothing
else does (`plainParamSupply` is the canonical rule's supplier).  The
constructor's run spine `sp` and the mixed value spine `mix` stay
abstract exactly as in v1.
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

set_option maxHeartbeats 6400000 in
/-- **The zipper, at the reading** (`zipperS`): the fired statement
spine satisfies and fits the checked statement's telescope. -/
theorem zipper {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {f : Name → Name} (hroT : RenameOk m.acval env f)
    {rP cnP cnF mI : Nat} {xs ys : List AnnotTerm} {ρ : Nat → V}
    (hrPmI : rP ≤ mI) (hlenX : xs.length = mI)
    (hlenY : ys.length = cnP + cnF)
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
    {tyAR : Expr} (htyRw : tyAR.hasFvar = false)
    (htyRb : tyAR.looseBVarsBounded 0 = true)
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) tyAR = some (rdoms, rrest))
    (hrenP : ∀ n, n < rP →
      RenEqT f ((fvsP.map Expr.fvarTypeD).getD n default)
        (rdoms.getD n default))
    -- the constructor's run at the statement frame
    {ctyR : Expr} (hCwR : ctyR.hasFvar = false)
    (hCbR : ctyR.looseBVarsBounded 0 = true)
    {TVj : AnnotTerm}
    (hTVjK : denoteMeta m.acval env φ (rP + cnF) ctyR = some TVj)
    (hokTVj : ∀ σ : Nat → V, WellDenotedV V σ TVj)
    (hTVjcl : ∀ k : Nat, TVj.liftN 1 k = TVj)
    {Γj : List AnnotTerm} {Rj : AnnotTerm}
    (htowerJ : PiTeleAV (cnP + cnF) TVj Γj Rj)
    {sp : List Expr} (hsplen : sp.length = cnP + cnF)
    (hspLeaf : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP))
    (hspScope : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true)
    (hspFld : ∀ j, j < cnF → sp[cnP + j]? = fvs[rP + j]?)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt sp ctyR = some (cdoms, cres))
    {mix : List AnnotTerm} (hmixlen : mix.length = cnP + cnF)
    (hmixsp : ∀ (q : Nat) (x : Expr), sp[q]? = some x →
      ∃ w0, denoteMeta m.acval env φ (rP + cnF) x = some w0 ∧
        mix[q]? = some (AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP)
          (rP + cnF - 1) w0))
    (hmixFldEq : ∀ j, j < cnF →
      mix.getD (cnP + j) default = ys.getD (cnP + j) default)
    (hmixPar : ∀ q, q < cnP →
      interp V ρ (mix.getD q default) = interp V ρ (ys.getD q default))
    -- the two fits
    {restRpre restC : AnnotTerm}
    (hfitRpre : TeleFitPA V ρ TV (xs.take rP) restRpre)
    (hfitC : TeleFitPA V ρ TVj ys restC)
    -- the recorded runs
    (hdePre : DefEqListOk μ F env (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk μ F env (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- the constructor run's parameter positions, at every padding
    -- (the padding level is bounded below by `rP`: the field branch is
    -- the only consumer, and its supplier — `plainParamSupply` —
    -- transports the *prefix* equalities, which need the tower's whole
    -- prefix present in the context.  Part 7's bottom, the first
    -- caller, is what exposed this.)
    (hpar : ∀ N, rP ≤ N → N ≤ rP + cnF → ∀ q, q < cnP → ∀ ρ' : Nat → V,
      Sat V (List.replicate (rP + cnF - N) (.sort 0)
        ++ Γs.drop (rP + cnF - N)) ρ' →
      ∃ w, denoteMeta m.acval env φ (rP + cnF) (sp.getD q default)
          = some w ∧ WellDenotedV V ρ' w ∧
        ∀ dw, denoteMeta m.acval env φ (rP + cnF)
            (cdoms.getD q default) = some dw →
          interp V ρ' w ∈ˢ interp V ρ' dw) :
    Sat V Γs (chain V ρ (xs.take rP ++ ys.drop cnP)) ∧
    TeleFitPA V ρ Tstmt (xs.take rP ++ ys.drop cnP)
      (AnnotTerm.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
        Rbody) := by
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hΓPlen : ΓP.length = rP := htowerP.length
  have hΓjlen : Γj.length = cnP + cnF := htowerJ.length
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, hxtlen, List.length_drop, hlenY]
    omega
  -- `zs` element access
  have hzsPre : ∀ n, n < rP →
      (xs.take rP ++ ys.drop cnP).getD n default
        = xs.getD n default := by
    intro n hn
    rw [List.getD, List.getElem?_append_left (by rw [hxtlen]; omega),
      List.getElem?_take_of_lt hn]
    rfl
  have hzsFld : ∀ j, j < cnF →
      (xs.take rP ++ ys.drop cnP).getD (rP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right (by rw [hxtlen]; omega),
      hxtlen, List.getElem?_drop,
      show rP + j - rP = j from by omega]
    rfl
  -- the mixed values read as the constructor's own spine, pointwise
  have hmixVal : ∀ q, q < cnP + cnF →
      interp V ρ (mix.getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · exact hmixPar q hqc
    · rw [show q = cnP + (q - cnP) from by omega]
      exact congrArg _ (hmixFldEq (q - cnP) (by omega))
  -- the mixed chain memberships
  have hchainC := teleFitPA_to_chain (cnP + cnF) htowerJ hlenY hfitC
  have hchainEnvEq : ∀ q, q ≤ cnP + cnF →
      chain V ρ (mix.take q) = chain V ρ (ys.take q) := by
    intro q hq
    funext i
    have htq : (mix.take q).length = q := by
      rw [List.length_take, hmixlen]
      omega
    have htq' : (ys.take q).length = q := by
      rw [List.length_take, hlenY]
      omega
    by_cases hiq : i < q
    · rw [chain_lt (by omega), chain_lt (by omega), htq, htq']
      have hlt : q - 1 - i < q := by omega
      rw [show (mix.take q).getD (q - 1 - i) default
          = mix.getD (q - 1 - i) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt],
        show (ys.take q).getD (q - 1 - i) default
          = ys.getD (q - 1 - i) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt]]
      exact hmixVal _ (by omega)
    · rw [chain_ge (by omega), chain_ge (by omega), htq, htq']
  have hmixMem : ∀ q, q < cnP + cnF →
      interp V ρ (mix.getD q default)
        ∈ˢ interp V (chain V ρ (mix.take q))
          (Γj.getD (cnP + cnF - 1 - q) default) := by
    intro q hq
    have h1 := hchainC q hq
    rw [hchainEnvEq q (by omega), hmixVal q hq]
    exact h1
  -- the prefix chain memberships
  have hchainP := teleFitPA_to_chain rP htowerP hxtlen hfitRpre
  -- the field domains' scope and leaves, once for all positions
  have hzipAll : ∀ j, j < cnF →
      Expr.WScoped (rP + j) (cdoms.getD (cnP + j) default) ∧
      (∀ l ∈ (cdoms.getD (cnP + j) default).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ fvs ∧ l.1 < rP + j) ∧
      ∃ vdomLow,
        denoteMeta m.acval env φ (rP + j) (cdoms.getD (cnP + j) default)
          = some vdomLow ∧
        AnnotTerm.instSeq ((xs.take rP ++ ys.drop cnP).take (rP + j))
            (rP + j - 1) vdomLow
          = AnnotTerm.instSeq (mix.take (cnP + j)) (cnP + j - 1)
              (Γj.getD (cnP + cnF - 1 - (cnP + j)) default) := fun j hj =>
    zipFieldTermEq m.acval_closed
      (fun n ψ y k => AVExprSubst.inst_eq_self_of_closed
        (fun k' => m.acval_closed n ψ k') y k)
      hCwR hCbR hTVjK hTVjcl htowerJ hsplen hspLeaf hspScope hcinst
      hzslen hmixlen hmixsp hj
  -- the strong induction on the fitted prefix
  have hall : ∀ n, n ≤ rP + cnF → ∀ p, p < n →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD p default)
        ∈ˢ interp V (chain V ρ ((xs.take rP ++ ys.drop cnP).take p))
          (Γs.getD (rP + cnF - 1 - p) default) := by
    intro n
    induction n with
    | zero => intro _ p hp; exact nomatch hp
    | succ n ihn =>
      intro hn p hp
      rcases Nat.lt_or_ge p n with hpn | hpn
      · exact ihn (by omega) p hpn
      · obtain rfl : n = p := by omega
        -- the padded satisfaction from the memberships so far
        have hsat := sat_pad_of_mems htowerS hzslen
          (n := n) (by omega) (fun p' hp' => ihn (by omega) p' hp')
        have hstrip : (fun j => padE2 V (rP + cnF - n)
              (chain V ρ ((xs.take rP ++ ys.drop cnP).take n))
              (j + (rP + cnF - n)))
            = chain V ρ ((xs.take rP ++ ys.drop cnP).take n) := by
          have h := padE2_shiftE (V := V) (rP + cnF - n)
            (chain V ρ ((xs.take rP ++ ys.drop cnP).take n))
          funext j
          have := congrFun h j
          simpa [shiftE] using this
        rcases Nat.lt_or_ge n rP with hnrP | hnrP
        · -- the prefix step
          have hfire := prefixGradeFire (m := m) hclaims hfvslen
            hshapeS hwsFvs hleafClosed hlbFvs htowerS hokTst hdomsS0
            hfvsPlen hshapeP htowerP hokTV hdomsP0 hroT htyRw htyRb
            hrinst hrenP hdePre (N := n) (by omega) n (Nat.le_refl _)
            hnrP _ hsat
          rw [hstrip] at hfire
          have h1 := hchainP n hnrP
          rw [show (xs.take rP).take n
              = (xs.take rP ++ ys.drop cnP).take n from by
            rw [List.take_append_of_le_length (by omega)]] at h1
          rw [hzsPre n hnrP]
          rw [show (xs.take rP).getD n default = xs.getD n default from by
              rw [List.getD, List.getD, List.getElem?_take_of_lt hnrP]]
            at h1
          rw [← hfire.2] at h1
          exact h1
        · -- the field step
          obtain ⟨hwsDom, hleafDom, vdomLow, hvdlow, hterm⟩ :=
            hzipAll (n - rP) (by omega)
          have hnj : rP + (n - rP) = n := by omega
          -- the crossed domain's reading at the frame depth
          have hdw : denoteMeta m.acval env φ (rP + cnF)
              (cdoms.getD (cnP + (n - rP)) default)
              = some (vdomLow.liftN ((rP + cnF) - n) 0) := by
            have hd := denoteMeta_lift (env := env) (φ := φ)
              m.acval_closed
              (e := cdoms.getD (cnP + (n - rP)) default)
              (p := rP + (n - rP)) hwsDom (rP + cnF) (by omega)
            rw [hvdlow] at hd
            rw [hnj] at hd
            exact hd
          have hfire := fieldGradeFire (m := m) hclaims hfvslen hshapeS
            hwsFvs hleafClosed hlbFvs htowerS hokTst hdomsS0 hCwR hCbR
            hTVjK hokTVj hsplen hspScope hspFld hcinst
            (fun j hj => (hzipAll j hj).1)
            (fun j hj => (hzipAll j hj).2.1) hdeFld
            (N := n) (by omega) (hpar n hnrP (by omega))
            n (Nat.le_refl _) hnrP (by omega) _ hsat _ hdw
          rw [hstrip, interp_liftN,
            show shiftE ((rP + cnF) - n) 0 (padE2 V (rP + cnF - n)
                (chain V ρ ((xs.take rP ++ ys.drop cnP).take n)))
              = chain V ρ ((xs.take rP ++ ys.drop cnP).take n) from
              padE2_shiftE _ _] at hfire
          -- the fire-side membership, crossed to the statement chain
          have h1 := hmixMem (cnP + (n - rP)) (by omega)
          have htake1 : (mix.take (cnP + (n - rP))).length
              = cnP + (n - rP) := by
            rw [List.length_take, hmixlen]
            omega
          rw [show interp V (chain V ρ (mix.take (cnP + (n - rP))))
              (Γj.getD (cnP + cnF - 1 - (cnP + (n - rP))) default)
            = interp V ρ (AnnotTerm.instSeq (mix.take (cnP + (n - rP)))
                (cnP + (n - rP) - 1)
                (Γj.getD (cnP + cnF - 1 - (cnP + (n - rP))) default))
            from by rw [← interp_instSeq, htake1]] at h1
          rw [hnj] at hterm
          rw [← hterm] at h1
          have htake2 : ((xs.take rP ++ ys.drop cnP).take n).length
              = n := by
            rw [List.length_take, hzslen]
            omega
          rw [show interp V ρ (AnnotTerm.instSeq
              ((xs.take rP ++ ys.drop cnP).take n) (n - 1) vdomLow)
            = interp V (chain V ρ
                ((xs.take rP ++ ys.drop cnP).take n)) vdomLow from by
              rw [← interp_instSeq, htake2]] at h1
          have hval : interp V ρ (mix.getD (cnP + (n - rP)) default)
              = interp V ρ ((xs.take rP ++ ys.drop cnP).getD n
                default) := by
            have hz := hzsFld (n - rP) (by omega)
            rw [hnj] at hz
            rw [hmixFldEq (n - rP) (by omega), hz]
          rw [hval] at h1
          rw [← hfire.2] at h1
          exact h1
  have hallK := hall (rP + cnF) (Nat.le_refl _)
  exact ⟨sat_of_tower htowerS hzslen hallK,
    teleFitPA_of_tower (rP + cnF) htowerS hzslen hallK⟩

end ConLeche.Model
