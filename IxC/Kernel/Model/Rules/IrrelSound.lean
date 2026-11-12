module

public import IxC.Kernel.Model.Rules.Inputs
import IxC.Kernel.Model.Rules.DefEqSoundKit
import IxC.Kernel.Model.Rules.IotaSoundKit
import IxC.Kernel.Model.Rules.RedSoundKit
import IxC.Kernel.Model.CtxOkKit
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Model.Annot.BitClosed
import IxC.Kernel.Model.Annot.BitShift
import IxC.Kernel.Semantics.DefEqStep
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.PinnedShapes

public section

/-!
# Proof irrelevance, structure η and unit-likeness at a compared type

IxVM decides these moves by comparing the two sides' io-inferred types, where the
kernel's checker normalises and inspects each side on its own (`DefEq.proofIrrel`,
`DefEq.structEta`, `DefEq.unitLike`, `DefEq.structUnit`):

* `DefEq.proofIrrelTy`: `a`'s type is a proposition and `b`'s type is definitionally
  equal to it. Both sides are members of one truth value, hence its one proof
  (`mem_univ_zero`).
* `DefEq.structEtaTy`: `a` is a fully applied constructor of a tower-backed η-capable
  structure, `a`'s type reduces to the structure at `a`'s parameters, `b`'s type is
  definitionally equal to `a`'s, and `b`'s projections are `a`'s fields. The tower η law
  writes `b` as the constructor at those parameters and its projections.
* `DefEq.unitLikeTy`: `a`'s type head-normalises to a unit-like family at its parameter
  count, and `b`'s type is definitionally equal to `a`'s. Both sides are members of the
  one family instance. At a stored family that instance has one member by the family's
  unit law (`CapsOk`), at the parameters the licensed telescope certificate fits; at the
  basis `PUnit` (`isUnitLikeTy`) it is `{pt}`.

The subject of each `DefEq` premise is an inferred type, so the rules keep the
discipline `Rel.lean` states for `DefEq`.
-/

namespace Ix.Kernel.Model.Rules
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key ConstantVal ConstantInfo)
open Ix.Kernel.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {m : EnvModel V env}
  {φ : LevelParam → Nat}

/-- **`DefEq.proofIrrelTy` is sound**: `a` is a member of its type, a truth value, and
`b` is a member of its own type, which interprets as `a`'s. -/
theorem DefEq.proofIrrelTy_sound {d : Nat} {a ta tta b tb : Expr md} {u : Level}
    (hta : InferSemIO m φ d a ta) (htta : InferSemIO m φ d ta tta)
    (hu : RedSem m φ d tta (.sort u)) (hu0 : ∀ φ, Level.eval φ u = 0)
    (htb : InferSemIO m φ d b tb) (hd : DefEqSem m φ d ta tb) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba hga hgb ρ hρ
  obtain ⟨hfta, hsub1, taa, htaa, hgta, hmemA⟩ := hta hfa hCa haa hga
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsub1
  obtain ⟨hftta, hsub2, ttaa, httaa, hgtta, hmemT⟩ := htta hfta hCta htaa hgta
  have hCtta : CtxOk m φ d Δa tta := hCta.of_subset hsub2
  obtain ⟨-, -, sa, hsa, -, heqS⟩ := hu hftta hCtta httaa hgtta
  rw [denoteMeta_sort] at hsa
  obtain rfl : sa = AnnotTerm.sort (u.eval φ) := (Option.some.inj hsa).symm
  obtain ⟨hftb, hsub3, tba, htba, hgtb, hmemB⟩ := htb hfb hCb hba hgb
  have hCtb : CtxOk m φ d Δa tb := hCb.of_subset hsub3
  have heqT : interp V ρ taa = interp V ρ tba :=
    hd hfta hftb hCta hCtb htaa htba hgta hgtb ρ hρ
  have hT := hmemT ρ hρ
  rw [heqS ρ hρ, interp_sort, hu0 φ] at hT
  have hB : interp V ρ ba ∈ˢ interp V ρ taa := by
    rw [heqT]; exact hmemB ρ hρ
  exact (mem_univ_zero hT (hmemA ρ hρ)).trans (mem_univ_zero hT hB).symm

/-- A member of the reading of the basis unit type is the point
(`unit_side_pt'`'s second half). -/
theorem unit_mem_pt {d : Nat} {wta : Expr md} {wtaa : AnnotTerm}
    (hu : Ix.Kernel.isUnitLikeTy env wta = true)
    (hwtaa : denoteMeta m.acval env φ d wta = some wtaa)
    {ρ : Nat → V} {x : V} (hx : x ∈ˢ interp V ρ wtaa) : x = (pt : V) := by
  obtain ⟨us, rfl, hfind⟩ := Ix.Kernel.Verify.unitLike_eq_punit m.basis_pinned hu
  rw [denoteMeta, hfind] at hwtaa
  dsimp only at hwtaa
  split at hwtaa
  case isFalse => exact nomatch hwtaa
  case isTrue hlen =>
  obtain rfl : wtaa = m.acval Ix.Kernel.punitName
      (Level.substFn φ (Ix.Kernel.punitA (md := md)).toConstantVal.levelParams us) :=
    (Option.some.inj hwtaa).symm
  have hpin : m.cvalE Ix.Kernel.punitName
      (Level.substFn φ (Ix.Kernel.punitA (md := md)).toConstantVal.levelParams us)
      = Ix.Kernel.Term.punitT
        (Level.substFn φ (Ix.Kernel.punitA (md := md)).toConstantVal.levelParams us
          Ix.Kernel.uN) :=
    (m.basis_pinned Ix.Kernel.punitName _ hfind (by (cases md <;> decide))).2 _ _ rfl
  have hleaf : m.acval Ix.Kernel.punitName
      (Level.substFn φ (Ix.Kernel.punitA (md := md)).toConstantVal.levelParams us)
      = .const .punit
        [Level.substFn φ (Ix.Kernel.punitA (md := md)).toConstantVal.levelParams us
          Ix.Kernel.uN] :=
    erase_eq_const (by rw [m.acval_erase, hpin]; rfl)
  rw [hleaf, interp_const] at hx
  exact mem_unitSet hx

/-- **`DefEq.unitLikeTy` is sound**: both sides are members of `a`'s reduced type; at a
stored family its unit law identifies them (the licensed certificate fits the
parameters to the family's telescope), at the basis `PUnit` both are the point. -/
theorem DefEq.unitLikeTy_sound (hin : RulesInputs V m φ) {d : Nat}
    {a ta wta b tb : Expr md} {T : Key md} {us : List Level}
    {cvT : ConstantVal md} {caps : IndCaps md}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta)
    (hthead : wta.getAppFn = .const T us)
    (hind : env.find? T = some (.indInfo cvT caps))
    (hunit : caps.unitlike = true)
    (htlen : wta.getAppArgs.length = caps.unitParams)
    (hcerts : CertsSem m φ d true
      (cvT.type.instantiateLevelParams cvT.levelParams us) wta.getAppArgs)
    (hkind : Ix.Kernel.reservedBasisNames.contains T = false ∨
      Ix.Kernel.isUnitLikeTy env wta = true)
    (htb : InferSemIO m φ d b tb) (hd : DefEqSem m φ d ta tb) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb hokA hokB ρ hρ
  -- both sides are members of `a`'s reduced type
  obtain ⟨hfta, hsuba, taa, htaa, hokTa, hmemA⟩ := hta hfa hCa hda hokA
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsuba
  obtain ⟨hfWA, hsubWA, wtaa, hwtaa, hokWA, heqWA⟩ := hwta hfta hCta htaa hokTa
  have hCwa : CtxOk m φ d Δa wta := hCta.of_subset hsubWA
  obtain ⟨hftb, hsubb, tba, htba, hokTb, hmemB⟩ := htb hfb hCb hdb hokB
  have hCtb : CtxOk m φ d Δa tb := hCb.of_subset hsubb
  have hEq : interp V ρ taa = interp V ρ tba :=
    hd hfta hftb hCta hCtb htaa htba hokTa hokTb ρ hρ
  have hmemAW : interp V ρ aa ∈ˢ interp V ρ wtaa := by
    rw [← heqWA ρ hρ]; exact hmemA ρ hρ
  have hmemBW : interp V ρ ba ∈ˢ interp V ρ wtaa := by
    rw [← heqWA ρ hρ, hEq]; exact hmemB ρ hρ
  by_cases hres : Ix.Kernel.reservedBasisNames.contains T = false
  case neg =>
    -- the basis unit type: both are the point
    have hU := hkind.resolve_left hres
    exact (unit_mem_pt hU hwtaa hmemAW).trans (unit_mem_pt hU hwtaa hmemBW).symm
  -- a stored family: the reduct is the family applied to its parameters
  rw [show wta = Expr.mkAppN wta.getAppFn wta.getAppArgs from
    (Ix.Kernel.Expr.mkAppN_getApp wta).symm, hthead] at hwtaa
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv hwtaa
  rw [denoteMeta, hind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue hlv =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us) :=
    (Option.some.inj hvT).symm
  -- the family's stored type: read at every depth, graded, the leaf a member
  obtain ⟨Ta, hTa, hokT, hmemT, hnfT, hbdT⟩ := constTy_pkg hin.const_ty hind rfl hlv
  -- the family's unit law, at the same reading
  obtain ⟨TVa, hTVa, -, hlaw⟩ := hin.caps_ok.2 T cvT caps hind hunit hres φ us hlv
  have hTVeq : TVa = Ta := Option.some.inj (hTVa.symm.trans (hTa 0))
  subst hTVeq
  have hTF : Frame d (cvT.type.instantiateLevelParams cvT.levelParams us) :=
    ⟨Ix.Kernel.Expr.WScoped.of_not_hasFvar hnfT, hbdT,
      Ix.Kernel.Expr.LeavesBounded.of_not_hasFvar hnfT⟩
  have hTC : CtxOk m φ d Δa (cvT.type.instantiateLevelParams cvT.levelParams us) :=
    ⟨hCa.1, fun l hl => by
      rw [Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfT] at hl
      exact nomatch hl⟩
  -- the former's telescope arity, from the environment invariant
  have hstrip : (cvT.type.stripPis caps.unitParams).isSome = true :=
    (m.wf.indCaps hind).1 hunit
  have hpcT : PiChain wta.getAppArgs.length TVa := by
    rw [htlen]
    exact piChain_of_stripPis caps.unitParams
      (Ix.Kernel.Expr.stripPis_instantiateLevelParams_isSome
        cvT.levelParams us caps.unitParams hstrip) (hTa d)
  obtain ⟨-, hoT⟩ := hoist_spine tsa hokWA
  -- the licensed certificate fits the parameters to the family's telescope
  obtain ⟨resta, hfitPA, -⟩ :=
    hcerts (fa := m.acval T (Level.substFn φ cvT.levelParams us)) hTF hTC (hTa d)
      (fun σ _ => hokT σ) (frame_spine hfWA hCwa) hspt hoT
      (fun _ => ⟨hokWA, fun σ _ => hmemT σ⟩)
  have hfitT : TeleFit V ρ TVa (tsa.map (interp V ρ)) (interp V ρ resta) :=
    teleFit_of_teleFitPA (by rw [← hspt.length]; exact hpcT) (hfitPA ρ hρ)
  -- both members, at the folded family instance
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  have hmx : interp V ρ aa
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us))) := by
    have := hmemAW
    rwa [interp_mkAppN, hfold] at this
  have hmy : interp V ρ ba
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us))) := by
    have := hmemBW
    rwa [interp_mkAppN, hfold] at this
  have hlenTs : (tsa.map (interp V ρ)).length = caps.unitParams := by
    rw [List.length_map, ← hspt.length, htlen]
  exact hlaw ρ (tsa.map (interp V ρ)) (interp V ρ resta) (interp V ρ aa)
    (interp V ρ ba) hlenTs hfitT hmx hmy

/-- **`DefEq.structEtaTy` is sound**: `b` is a member of `a`'s reduced type, the
structure at `a`'s levels and parameters, which the licensed certificate fits to the
structure's telescope. The structure's tower η law (slot 0's entry) writes `b` as the
constructor at those parameters and `b`'s projections, the field premise identifies the
projections with `a`'s fields, and the entry's constructor is `a`'s head. -/
theorem DefEq.structEtaTy_sound (hin : RulesInputs V m φ) {d : Nat}
    {a b ta tb : Expr md} {c : Key md} {us : List Level} {cvc : ConstantVal md}
    {cnP cnF : Nat} {T : Key md} {cvT : ConstantVal md} {caps : IndCaps md}
    (hhead : a.getAppFn = .const c us)
    (hctor : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : a.getAppArgs.length = cnP + cnF)
    (hind : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true) (hetaCtor : caps.etaCtor = some c)
    (hpos : 0 < cnF) (htow : Ix.Kernel.towerSlotsAll env T cnF = true)
    (hta : InferSemIO m φ d a ta)
    (hwta : RedSem m φ d ta (Expr.mkAppN (.const T us) (a.getAppArgs.take cnP)))
    (hcerts : CertsSem m φ d true
      (cvT.type.instantiateLevelParams cvT.levelParams us) (a.getAppArgs.take cnP))
    (htb : InferSemIO m φ d b tb) (hd : DefEqSem m φ d tb ta)
    (hfields : DefEqListSem m φ d ((List.range cnF).map fun i => Expr.proj T i b)
      (a.getAppArgs.drop cnP)) :
    DefEqSem m φ d b a := by
  intro hfb hfa Δa ba aa hCb hCa hdb hda hokB hokA ρ hρ
  -- `b` is a member of `a`'s reduced type
  obtain ⟨hfta, hsubta, taa, htaa, hokTa, -⟩ := hta hfa hCa hda hokA
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsubta
  obtain ⟨-, -, wtaa, hwtaa, hokW, heqW⟩ := hwta hfta hCta htaa hokTa
  obtain ⟨hftb, hsubtb, tba, htba, hokTb, hmemB0⟩ := htb hfb hCb hdb hokB
  have hCtb : CtxOk m φ d Δa tb := hCb.of_subset hsubtb
  have heqT := hd hftb hfta hCtb hCta htba htaa hokTb hokTa
  have hmemB : ∀ σ : Nat → V, Sat V Δa σ → interp V σ ba ∈ˢ interp V σ wtaa :=
    fun σ hσ => by rw [← heqW σ hσ, ← heqT σ hσ]; exact hmemB0 σ hσ
  -- the slot-0 entry ties the structure, its constructor and its tables
  obtain ⟨e0, hfe0⟩ := Ix.Kernel.towerSlotsAll_slot htow 0 hpos
  obtain ⟨-, -, -, ⟨cvT', capsT', hfT', hlpsT', himp'⟩, -, cvC, hfC, hlpsC, -, hetaL⟩ :=
    hin.tower_ok T 0 e0 hfe0
  have hcvT' : cvT' = cvT := by
    rw [hind] at hfT'
    exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).1.symm
  have hcapsT' : capsT' = caps := by
    rw [hind] at hfT'
    exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).2.symm
  obtain ⟨-, hctr', hpar', -⟩ := himp' (by rw [hcapsT']; exact heta)
  rw [hcvT'] at hlpsT'
  rw [hcapsT'] at hctr' hpar'
  have hce : e0.ctor = c := Option.some.inj (hctr'.symm.trans hetaCtor)
  rw [hce] at hfC
  obtain ⟨hcv, hnP, hnF⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hctor.symm.trans hfC))
  have hlps : cvc.levelParams = cvT.levelParams := by rw [hcv, hlpsC, ← hlpsT']
  have hcP : caps.etaParams = cnP := by rw [hpar', hnP]
  have hlenP : (a.getAppArgs.take cnP).length = cnP := by
    rw [List.length_take, hlen, Nat.min_eq_left (Nat.le_add_right _ _)]
  -- `a` is the constructor applied to its arguments
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (Ix.Kernel.Expr.mkAppN_getApp a).symm, hhead] at hda
  obtain ⟨vf, asa, hvf, hspa, rfl⟩ := denoteMeta_mkAppN_inv hda
  rw [denoteMeta, hctor] at hvf
  dsimp only at hvf
  split at hvf
  case isFalse => exact nomatch hvf
  case isTrue hlvc =>
  obtain rfl : vf = m.acval c (Level.substFn φ cvc.levelParams us) :=
    (Option.some.inj hvf).symm
  have hlvT : us.length = cvT.levelParams.length := by rw [← hlps]; exact hlvc
  -- `a`'s reduced type reads as the structure at `a`'s parameters
  have hheadT : denoteMeta m.acval env φ d (.const T us)
      = some (m.acval T (Level.substFn φ cvT.levelParams us)) :=
    denoteMeta_const hind
      (show us.length = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
        from hlvT)
  have hwD : denoteMeta m.acval env φ d (Expr.mkAppN (.const T us) (a.getAppArgs.take cnP))
      = some (AnnotTerm.mkAppN (m.acval T (Level.substFn φ cvT.levelParams us))
        (asa.take cnP)) :=
    denoteMeta_mkAppN (hspa.take cnP) hheadT
  obtain rfl := Option.some.inj (hwtaa.symm.trans hwD)
  -- the structure's stored type: read at every depth, graded, the leaf a member
  obtain ⟨Ta, hTa, hokT, hmemT, hnfT, hbdT⟩ := constTy_pkg hin.const_ty hind rfl hlvT
  have hTF : Frame d (cvT.type.instantiateLevelParams cvT.levelParams us) :=
    ⟨Ix.Kernel.Expr.WScoped.of_not_hasFvar hnfT, hbdT,
      Ix.Kernel.Expr.LeavesBounded.of_not_hasFvar hnfT⟩
  have hTC : CtxOk m φ d Δa (cvT.type.instantiateLevelParams cvT.levelParams us) :=
    ⟨hCa.1, fun l hl => by
      rw [Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfT] at hl
      exact nomatch hl⟩
  obtain ⟨-, hoA⟩ := hoist_spine asa hokA
  have hoP : ∀ x ∈ asa.take cnP, Graded V Δa x := fun x hx => hoA x (List.mem_of_mem_take hx)
  -- the licensed certificate fits the parameters to the structure's telescope
  have hstrip : (cvT.type.stripPis caps.etaParams).isSome = true :=
    (m.wf.indCaps hind).2 heta
  have hpcT : PiChain (a.getAppArgs.take cnP).length Ta := by
    rw [hlenP, ← hcP]
    exact piChain_of_stripPis caps.etaParams
      (Ix.Kernel.Expr.stripPis_instantiateLevelParams_isSome
        cvT.levelParams us caps.etaParams hstrip) (hTa d)
  obtain ⟨resta, hfitPA, -⟩ :=
    hcerts (fa := m.acval T (Level.substFn φ cvT.levelParams us)) hTF hTC (hTa d)
      (fun σ _ => hokT σ) (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_take hx))
      (hspa.take cnP) hoP (fun _ => ⟨hokW, fun σ _ => hmemT σ⟩)
  -- the tower η law at slot 0
  obtain ⟨TVa, hTVa, -, hlaw⟩ := hetaL cvT caps hind us (by rw [← hlpsT']; exact hlvT)
  have hTVeq : TVa = Ta := Option.some.inj (hTVa.symm.trans (hTa 0))
  subst hTVeq
  have hfitT : TeleFit V ρ TVa ((asa.take cnP).map (interp V ρ)) (interp V ρ resta) :=
    teleFit_of_teleFitPA (by rw [← (hspa.take cnP).length]; exact hpcT) (hfitPA ρ hρ)
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  have hlenTs : ((asa.take cnP).map (interp V ρ)).length = e0.numParams := by
    rw [List.length_map, ← (hspa.take cnP).length, hlenP, hnP]
  have hb := hlaw ρ ((asa.take cnP).map (interp V ρ)) (interp V ρ resta) (interp V ρ ba)
    hlenTs hfitT (by
      have := hmemB ρ hρ
      rw [interp_mkAppN, hfold] at this
      rw [← hlpsT']; exact this)
  -- every field slot is a tower entry, at the structure's levels
  have hslotE : ∀ j, j < cnF → ∃ entry : ProjEntry md,
      env.findProj? T j = some entry ∧ entry.levelParams = cvT.levelParams := by
    intro j hj
    obtain ⟨entry, hfe⟩ := Ix.Kernel.towerSlotsAll_slot htow j hj
    obtain ⟨-, -, -, ⟨cvT'', capsT'', hfT'', hlpsT'', -⟩, -⟩ := hin.tower_ok T j entry hfe
    have hcvT'' : cvT'' = cvT := by
      rw [hind] at hfT''
      exact (ConstantInfo.indInfo.inj (Option.some.inj hfT'')).1.symm
    exact ⟨entry, hfe, by rw [← hlpsT'', hcvT'']⟩
  have hoffE : ∀ j entry, env.findProj? T j = some entry → entry.off = e0.off :=
    fun j entry hfe => Ix.Kernel.Env.findProj?_off_eq hfe hfe0
  -- `b`'s projections read, and are graded by each entry's typing law
  have hprojden : ∀ j ∈ List.range cnF,
      denoteMeta m.acval env φ d (.proj T j b) = some (projAV (j + e0.off) ba) := by
    intro j hj
    obtain ⟨entry, hfe, -⟩ := hslotE j (List.mem_range.mp hj)
    rw [← hoffE j entry hfe]
    exact denoteMeta_proj_tower hfe hdb
  have hokProj : ∀ x ∈ (List.range cnF).map (fun j => projAV (j + e0.off) ba),
      Graded V Δa x := by
    intro x hx σ hσ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨entry, hfe, hlpe⟩ := hslotE j (List.mem_range.mp hj)
    rw [← hoffE j entry hfe]
    obtain ⟨-, -, -, ⟨cvTj, capsTj, hfTj, -, himpj⟩, hO5j, _, -, -, hlawj, -⟩ :=
      hin.tower_ok T j entry hfe
    have hcapsTj : capsTj = caps := by
      rw [hind] at hfTj
      exact (ConstantInfo.indInfo.inj (Option.some.inj hfTj)).2.symm
    obtain ⟨hnpj, -, hparj, -⟩ := himpj (by rw [hcapsTj]; exact heta)
    rw [hcapsTj] at hparj
    have hgj : TowerGuardAt φ entry us :=
      towerGuardAt_of hO5j (fun hp => by rw [hp] at hnpj; exact nomatch hnpj)
    obtain ⟨⟨Tj, hTj, hA⟩, -⟩ := hlawj us (by rw [hlpe]; exact hlvT)
    obtain ⟨hTjd, -⟩ := towerEntry_tele_at_depth hfe hTj
    have hlenVs : (asa.take cnP).length = entry.numParams := by
      rw [← (hspa.take cnP).length, hlenP, ← hcP, hparj]
    have hpc : PiChain ((asa.take cnP) ++ [ba]).length Tj := by
      rw [List.length_append, List.length_singleton, hlenVs]
      exact piChain_of_stripPis _
        (by rw [Ix.Kernel.projTele_stripPis]; rfl) (hTjd d)
    obtain ⟨restj, hpeel⟩ := peelPis_of_piChain _ hpc
    rw [hlpe] at hA
    exact (hA hgj σ (asa.take cnP) ba restj hlenVs (hokW σ hσ) (hokB σ hσ)
      (hmemB σ hσ) hpeel).1
  have hframeProj : ∀ x ∈ (List.range cnF).map (fun j => Expr.proj T j b),
      Frame d x ∧ CtxOk m φ d Δa x := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨by simpa [Expr.WScoped] using hfb.1,
        by simpa [Expr.looseBVarsBounded] using hfb.2.1,
        fun l hl => hfb.2.2 l (by simpa [Expr.fvarLeaves] using hl)⟩,
      ⟨hCb.1, fun l hl => hCb.2 l (by simpa [Expr.fvarLeaves] using hl)⟩⟩
  -- the field premise: `b`'s projections are `a`'s fields
  have hdrop : ((List.range cnF).map fun j => projAV (j + e0.off) ba).map (interp V ρ)
      = (asa.drop cnP).map (interp V ρ) :=
    hfields.2 hframeProj (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_drop hx))
      (DenoteMetaSpine.map_list _ hprojden) (hspa.drop cnP) hokProj
      (fun x hx => hoA x (List.mem_of_mem_drop hx)) ρ hρ
  have hsplit : asa.map (interp V ρ)
      = (asa.take cnP).map (interp V ρ) ++ (asa.drop cnP).map (interp V ρ) := by
    rw [← List.map_append, List.take_append_drop]
  have hprojs : (asa.drop cnP).map (interp V ρ)
      = (List.range e0.numFields).map
          (fun j => Ix.Kernel.SetTheory.Tower.projS (j + e0.off) (interp V ρ ba)) := by
    rw [← hdrop, List.map_map, ← hnF]
    refine List.map_congr_left fun j _ => ?_
    rw [Function.comp_apply, projAV_interp]
  rw [hb, interp_mkAppN, hfold, hsplit, hprojs, hce, ← hlpsC, ← hcv]

end Ix.Kernel.Model.Rules
