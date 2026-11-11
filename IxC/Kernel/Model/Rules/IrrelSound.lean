module

public import IxC.Kernel.Model.Rules.Inputs
import IxC.Kernel.Model.Rules.DefEqSoundKit
import IxC.Kernel.Model.Rules.IotaSoundKit
import IxC.Kernel.Model.Rules.RedSoundKit
import IxC.Kernel.Model.CtxOkKit
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Model.Annot.BitClosed
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.PinnedShapes

public section

/-!
# Proof irrelevance and unit-likeness at a compared type

IxVM decides both moves by comparing the two sides' io-inferred types, where the
kernel's checker normalises and inspects each side on its own (`DefEq.proofIrrel`,
`DefEq.unitLike`, `DefEq.structUnit`):

* `DefEq.proofIrrelTy`: `a`'s type is a proposition and `b`'s type is definitionally
  equal to it. Both sides are members of one truth value, hence its one proof
  (`mem_univ_zero`).
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

end Ix.Kernel.Model.Rules
