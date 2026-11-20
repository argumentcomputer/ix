import IxVMRefinement.Assembly.NativeBlockCtorOuts

/-! # The constructor stage of a native block, with the raw constructor types named

`Typing.stagedCtorLoads_of_block_named` and `Typing.ctorOuts_of_member_named` choose the raw
constructor types the admission checks (`rawTypes`, one per slot) once and hide them. The
theorems here are the same proofs with that choice exposed:

* `stagedCtorLoads_of_block_raw`: each raw type is the raw image of the slot's reading under the
  record's binder plan at the constructor's root (`canonRawAnn`), with the constructor's level
  parameters renamed to positions (`posOf`);
* `ctorOuts_of_member_raw`: `ctorOuts_of_member_named` with, besides, the bound on the
  constructor count, the same link for each slot, and one load of each slot in the member
  check's calls.

The admission's residual (`Decl.NativeCtorOut.residual`) fixes the shape of the raw type it
checks: literal binders and then an application spine over the family's constant. Through the
link this is a fact about the record, which every later load of the constructor reads exactly
(`LoadedReads.ctor_load_canon`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open LoadedReads (canonAnn canonRawAnn)

universe u

/-- **The constructor family of a native block, with the raw types named**:
`stagedCtorLoads_of_block_named`, where besides each raw type is the raw image of the slot's
reading under the record's binder plan at the constructor's root, with the constructor's level
parameters renamed to positions. -/
theorem stagedCtorLoads_of_block_raw {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {c : Core.Ctx} {cs_root : List (Call F)} (hgood : Core.Good c cs_root)
    {b₀ : Bytes.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf c.E (Core.ixAddr b₀) = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hsafe : ∀ ct ∈ ind.ctors.toList, ct.isUnsafe = false)
    (hcount : ind.ctors.size < 72057594037927936)
    {nP : Nat} {ctors : List (Ix.Kernel.ConstantVal .anon × Nat)}
    (hlen : ctors.length = ind.ctors.size)
    (hctors : ∀ j cv, ctors[j]? = some cv → ∃ ct : Ixon.Constructor,
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.params.toNat = nP ∧
      cv.1.levelParams = List.range ct.lvls.toNat ∧ cv.2 = ct.fields.toNat ∧
      (exprReader t (fun x => c.E.blobs.get? x) cb id
        (blockSelf t (Core.ixAddr b₀) #[.indc ind])).read ct.typ = .ok cv.1.type ∧
      cv.1.type.looseBVarsBounded 0 = true ∧
      cv.1.type.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hslots : ∀ j < ind.ctors.size, ∃ (bp ptr : SourceValue F) (h h' : Heap F)
      (cs : List (Call F)),
      ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field 0, .field (j : F)] h ptr h' cs ∧
      (∀ cl ∈ cs, cl ∈ cs_root) ∧ Bytes.RepAddressRef Core.addrTy h b₀ bp) :
    ∃ (ctorsA : List (Ix.Kernel.ConstantVal .anon × Nat))
      (rawTypes : List (Ix.Kernel.Expr .anon)),
      (∀ j cv, ctors[j]? = some cv → ∃ (ct : Ixon.Constructor) (ty' : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧
        canonAnn cb (List.range ct.lvls.toNat)
          (((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) :
            Nat) : F) + 1 + ((j : Nat) : F)) ct.typ cv.1.type = some ty' ∧
        ctorsA[j]? = some (⟨cv.1.name, cv.1.levelParams, ty'⟩, cv.2)) ∧
      (∀ j cv, ctors[j]? = some cv → ∃ (ct : Ixon.Constructor) (R' : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧
        canonRawAnn cb (List.range ct.lvls.toNat)
          (((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) :
            Nat) : F) + 1 + ((j : Nat) : F)) ct.typ cv.1.type = some R' ∧
        rawTypes[j]? = some (Core.posOf (List.range ct.lvls.toNat) R')) ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ Ingress.blockRecurAddrs (Core.ixAddr b₀) (#[.indc ind] : Array Ixon.MutConst).toList,
          κ x = Core.keyOf t x) →
        Decl.StagedCtorLoads κ t b₀ nP 0 cs_root ctors ctorsA rawTypes := by
  let root : Nat → F := fun j =>
    ((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) : Nat) : F)
      + 1 + ((j : Nat) : F)
  let annOf : Nat → Ix.Kernel.ConstantVal .anon × Nat → Ix.Kernel.Expr .anon := fun j cv =>
    ((ind.ctors[j]?).bind fun ct => canonAnn cb cv.1.levelParams (root j) ct.typ cv.1.type).getD
      default
  let rawOf : Nat → Ix.Kernel.ConstantVal .anon × Nat → Ix.Kernel.Expr .anon := fun j cv =>
    Core.posOf cv.1.levelParams (((ind.ctors[j]?).bind fun ct =>
      canonRawAnn cb cv.1.levelParams (root j) ct.typ cv.1.type).getD default)
  have hcanonA : ∀ j cv, ctors[j]? = some cv →
      ∃ (ct : Ixon.Constructor) (ty' : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧
        canonAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cv.1.type = some ty' ∧
        (ctors.mapIdx fun j cv => ((⟨cv.1.name, cv.1.levelParams, annOf j cv⟩ :
            Ix.Kernel.ConstantVal .anon), cv.2))[j]? =
          some (⟨cv.1.name, cv.1.levelParams, ty'⟩, cv.2) := by
    intro j cv hc
    have hj : j < ctors.length := (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨ct, hct, hcidx, hnp, hlps, hnf, hty, hlbb, hdef⟩ := hctors j cv hc
    have hjsize : j < ind.ctors.size := by
      rw [← hlen]
      exact hj
    have hjval : ZMod.val ((j : Nat) : F) = j :=
      ZMod.val_natCast_of_lt (Nat.lt_trans (show j < 72057594037927936 by omega) (by decide))
    have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val (0 : F)]? = some (.indc ind) := by
      rw [ZMod.val_zero]
      rfl
    have hct' : ind.ctors[ZMod.val ((j : Nat) : F)]? = some ct := by
      rw [hjval]
      exact hct
    have hcidx' : ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
      rw [hjval]
      exact hcidx
    obtain ⟨bp₀, ptr₀, h₀, h₀', cs₀, ev₀, hsub₀, hbp₀⟩ := hslots j hjsize
    have hg₀ := hgood.sub hsub₀
    obtain ⟨-, -, -, ty'₀, -, -, -, -, -, -, -, hcanon₀, -, -, -, -⟩ :=
      LoadedReads.ctor_load_canon ht hg₀.1 hg₀.2 hbp₀ ev₀ hblock hmuts hmem hct' hcidx' hty hlbb
        hdef
    have hcanon₀' : canonAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cv.1.type =
        some ty'₀ := hcanon₀
    refine ⟨ct, ty'₀, hct, hcanon₀', ?_⟩
    have hann : annOf j cv = ty'₀ := by
      show ((ind.ctors[j]?).bind fun ct' => canonAnn cb cv.1.levelParams (root j) ct'.typ
        cv.1.type).getD default = ty'₀
      rw [hct, hlps]
      show (canonAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cv.1.type).getD default = ty'₀
      rw [hcanon₀']
      rfl
    rw [List.getElem?_mapIdx, hc]
    show some ((⟨cv.1.name, cv.1.levelParams, annOf j cv⟩ : Ix.Kernel.ConstantVal .anon), cv.2) = _
    rw [hann]
  have hcanonR : ∀ j cv, ctors[j]? = some cv →
      ∃ (ct : Ixon.Constructor) (R' : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧
        canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cv.1.type = some R' ∧
        (ctors.mapIdx rawOf)[j]? = some (Core.posOf (List.range ct.lvls.toNat) R') := by
    intro j cv hc
    have hj : j < ctors.length := (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨ct, hct, hcidx, hnp, hlps, hnf, hty, hlbb, hdef⟩ := hctors j cv hc
    have hjsize : j < ind.ctors.size := by
      rw [← hlen]
      exact hj
    have hjval : ZMod.val ((j : Nat) : F) = j :=
      ZMod.val_natCast_of_lt (Nat.lt_trans (show j < 72057594037927936 by omega) (by decide))
    have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val (0 : F)]? = some (.indc ind) := by
      rw [ZMod.val_zero]
      rfl
    have hct' : ind.ctors[ZMod.val ((j : Nat) : F)]? = some ct := by
      rw [hjval]
      exact hct
    have hcidx' : ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
      rw [hjval]
      exact hcidx
    obtain ⟨bp₀, ptr₀, h₀, h₀', cs₀, ev₀, hsub₀, hbp₀⟩ := hslots j hjsize
    have hg₀ := hgood.sub hsub₀
    obtain ⟨-, -, -, -, R'₀, -, -, -, -, -, -, -, hrcanon₀, -, -, -⟩ :=
      LoadedReads.ctor_load_canon ht hg₀.1 hg₀.2 hbp₀ ev₀ hblock hmuts hmem hct' hcidx' hty hlbb
        hdef
    have hrcanon₀' : canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cv.1.type =
        some R'₀ := hrcanon₀
    refine ⟨ct, R'₀, hct, hrcanon₀', ?_⟩
    have hraw : rawOf j cv = Core.posOf (List.range ct.lvls.toNat) R'₀ := by
      show Core.posOf cv.1.levelParams (((ind.ctors[j]?).bind fun ct' =>
        canonRawAnn cb cv.1.levelParams (root j) ct'.typ cv.1.type).getD default) = _
      rw [hct, hlps]
      show Core.posOf (List.range ct.lvls.toNat)
        ((canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cv.1.type).getD default) = _
      rw [hrcanon₀']
      rfl
    rw [List.getElem?_mapIdx, hc]
    show some (rawOf j cv) = _
    rw [hraw]
  refine ⟨ctors.mapIdx fun j cv => (⟨cv.1.name, cv.1.levelParams, annOf j cv⟩, cv.2),
    ctors.mapIdx rawOf, hcanonA, hcanonR, fun κ hused hrecur => ⟨by simp, fun j hj => ?_⟩⟩
  obtain ⟨cv, hc⟩ : ∃ cv, ctors[j]? = some cv := ⟨ctors[j], List.getElem?_eq_getElem hj⟩
  obtain ⟨ct, hct, hcidx, hnp, hlps, hnf, hty, hlbb, hdef⟩ := hctors j cv hc
  rcases cv with ⟨⟨cn, clp, cty⟩, cnf⟩
  dsimp only at hlps hnf hty hlbb hdef
  subst hlps hnf
  have hjsize : j < ind.ctors.size := by
    rw [← hlen]
    exact hj
  have hjval : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (show j < 72057594037927936 by omega) (by decide))
  have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val (0 : F)]? = some (.indc ind) := by
    rw [ZMod.val_zero]
    rfl
  have hct' : ind.ctors[ZMod.val ((j : Nat) : F)]? = some ct := by
    rw [hjval]
    exact hct
  have hcidx' : ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
    rw [hjval]
    exact hcidx
  have hctm : ct ∈ ind.ctors.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hct)
  -- the slot's annotation and raw image, from one load of the slot
  obtain ⟨bp₀, ptr₀, h₀, h₀', cs₀, ev₀, hsub₀, hbp₀⟩ := hslots j hjsize
  have hg₀ := hgood.sub hsub₀
  obtain ⟨-, -, -, ty'₀, R'₀, -, -, -, -, -, -, hcanon₀, hrcanon₀, hann₀, -, -⟩ :=
    LoadedReads.ctor_load_canon ht hg₀.1 hg₀.2 hbp₀ ev₀ hblock hmuts hmem hct' hcidx' hty hlbb hdef
  have hann_eq : annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat) = ty'₀ := by
    show ((ind.ctors[j]?).bind fun ct' => canonAnn cb (List.range ct.lvls.toNat) (root j) ct'.typ
      cty).getD default = ty'₀
    rw [hct]
    show (canonAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty).getD default = ty'₀
    have hcanon₀' : canonAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty = some ty'₀ :=
      hcanon₀
    rw [hcanon₀']
    rfl
  have hraw_eq : rawOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat) =
      Core.posOf (List.range ct.lvls.toNat) R'₀ := by
    show Core.posOf (List.range ct.lvls.toNat) (((ind.ctors[j]?).bind fun ct' =>
      canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct'.typ cty).getD default) = _
    rw [hct]
    show Core.posOf (List.range ct.lvls.toNat)
      ((canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty).getD default) = _
    have hrcanon₀' : canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty = some R'₀ :=
      hrcanon₀
    rw [hrcanon₀']
    rfl
  have hgetRaw : (ctors.mapIdx rawOf).getD j default =
      rawOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, hc]
    rfl
  refine ⟨_, ⟨cn, List.range ct.lvls.toNat,
    annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat)⟩, hc, ?_, ⟨rfl, rfl, ?_⟩, ?_⟩
  · rw [List.getElem?_mapIdx, hc]
    rfl
  · rw [hann_eq]
    exact hann₀
  intro bp ptr h h' cs hsub hbp ev
  have hg := hgood.sub hsub
  obtain ⟨tyPtr, blkPtr, b', ty', R', hld, hb', hbeq, hlv, hp56, hf56, hcanon, hrcanon, -,
    hrawE, hκ⟩ :=
    LoadedReads.ctor_load_canon ht hg.1 hg.2 hbp ev hblock hmuts hmem hct' hcidx' hty hlbb hdef
  have hty'eq : ty' = ty'₀ := Option.some.inj (hcanon.symm.trans hcanon₀)
  have hR'eq : R' = R'₀ := Option.some.inj (hrcanon.symm.trans hrcanon₀)
  rw [hty'eq, hR'eq] at hrawE
  rw [hty'eq] at hκ
  refine ⟨.field (ct.lvls.toNat : F), tyPtr, blkPtr, .field (ct.params.toNat : F),
    .field (ct.fields.toNat : F), b', ?_, hb', hbeq, ?_, ?_, ?_, rfl⟩
  · rw [hld, hsafe ct hctm]
    rfl
  · intro d Γ
    rw [hgetRaw, hraw_eq]
    show Decl.RawTmExact (Core.keyOf t) d Γ h' 0 _
      (Core.posOf (List.range ct.lvls.toNat)
        (annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat))) tyPtr
    rw [hann_eq]
    exact hrawE d Γ
  · refine ⟨by simp, by simpa using hlv, by simp, ?_⟩
    show Decl.TmCExact κ h' (Core.posOf (List.range ct.lvls.toNat)
      (annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat))) tyPtr
    rw [hann_eq]
    exact hκ κ hused hrecur
  · rw [hnp]

/-- **The constructor stage of a native block, from its walked check, with the raw types named**:
`ctorOuts_of_member_named`, where besides the record has fewer than `2^56` constructors, each raw
type the admission checks (`rawTypes`, read by the residual of `Decl.NativeCtorOut`) is the raw
image of the slot's reading under the record's binder plan at the constructor's root, with the
level parameters renamed to positions, and the member check loads each slot of the block. -/
theorem ctorOuts_of_member_raw {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    ∃ (ty₀ ty' : Ix.Kernel.Expr .anon) (cvS : ConstantVal .anon)
      (bsT : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta))
      (ctorsA : List (ConstantVal .anon × Nat)) (rawTypes : List (Ix.Kernel.Expr .anon)),
      (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ =
        some ty' ∧
      p₀.cvT = ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩ ∧
      cvS = ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ ∧
      p₀.nP = ind.params.toNat ∧ p₀.nIdx = ind.indices.toNat ∧
      p₀.ctors.length = ind.ctors.size ∧
      (∀ j c, p₀.ctors[j]? = some c → ∃ (ct : Ixon.Constructor) (cty' : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.params.toNat = ind.params.toNat ∧
        ct.lvls.toNat = ind.lvls.toNat ∧
        c.1.name = keyOf t (ctorAddr B 0 j) ∧ c.1.levelParams = List.range ct.lvls.toNat ∧
        c.2 = ct.fields.toNat ∧
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok c.1.type ∧
        c.1.type.looseBVarsBounded 0 = true ∧
        c.1.type.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
        LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
          (((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) :
            Nat) : F) + 1 + ((j : Nat) : F)) ct.typ c.1.type = some cty' ∧
        ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2)) ∧
      Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT cvS ∧
      cvS.type.stripPis (p₀.nP + p₀.nIdx) = some (bsT, .sort p₀.resSort) ∧
      cvS.name = p₀.cvT.name ∧ ctorsA.length = p₀.ctors.length ∧
      (∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
        sortss.length = p₀.ctors.length ∧
        ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
          sortss[j]? = some sorts ∧
          Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
              (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩
            p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx p₀.resSort cvS.type
            (rawTypes.getD j default) c cA sorts) ∧
      (∀ cA ∈ ctorsA, ∀ cbs body, cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
        ∀ i < cA.2,
          (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
           Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
          Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) ∧
      ind.ctors.size < 72057594037927936 ∧
      (∀ j c, p₀.ctors[j]? = some c → ∃ (ct : Ixon.Constructor) (R' : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧
        canonRawAnn cb (List.range ct.lvls.toNat)
          (((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) :
            Nat) : F) + 1 + ((j : Nat) : F)) ct.typ c.1.type = some R' ∧
        rawTypes[j]? = some (Core.posOf (List.range ct.lvls.toNat) R')) ∧
      (∀ j < ind.ctors.size, ∃ (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
        (b : Bytes.Address),
        ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field 0, .field (j : F)] h ptr h' cs ∧
        (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧ Core.ixAddr b = B) := by
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  obtain ⟨hlbb, hdef, hfv⟩ := former_scope hbound hS hrec hchk hty
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hprojE : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  have htyE : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀ :=
    ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreeT : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0)) :=
    hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hinlogic : ind.isUnsafe = false ∧ ∀ ct ∈ ind.ctors.toList, ct.isUnsafe = false := by
    have h := hrec.logic
    unfold InLogic at h
    rw [hrec.muts] at h
    exact h (.indc ind) (by simp)
  -- the recogniser
  obtain ⟨caps₀, hshape, hnP, -, -, hlps_ctors, ⟨bs₀, hst₀⟩, -⟩ := Decl.nativePartsNoRec?_inv hp₀
  injection hshape with hhead hcs_eq
  injection hhead with hcv _
  have hcvT : p₀.cvT = ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩ :=
    hcv.symm
  obtain ⟨bsF, sF, htF⟩ := htele ty₀ hty
  have hnIdx : p₀.nIdx = ind.indices.toNat := nIdx_of_tele hp₀ (by rw [hcvT]; exact htF)
  have hlenP : p₀.ctors.length = ind.ctors.size := by
    rw [← hlen, hcs_eq, List.length_map]
  have hctor : ∀ j c, p₀.ctors[j]? = some c → ∃ ct : Ixon.Constructor,
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
      ct.params.toNat = ind.params.toNat ∧
      c.1 = ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, c.1.type⟩ ∧
      c.2 = ct.fields.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ct.typ = .ok c.1.type := by
    intro j c hc
    have hcsj : cs[j]? = some (.ctorInfo c.1 p₀.nP c.2) := by
      rw [hcs_eq]
      simp [hc]
    obtain ⟨ct, tyj, h1, h2, h3, h4, h5, hceq, -⟩ := hcs j _ hcsj
    injection hceq with hc1 _ hc3
    refine ⟨ct, h1, h2, h3, h4, ?_, hc3, ?_⟩
    · rw [hc1]
    · rw [hc1]
      exact h5
  have hjlt : ∀ {j c}, p₀.ctors[j]? = some c → j < ind.ctors.size := fun {j c} hc => by
    rw [← hlenP]
    exact (List.getElem?_eq_some_iff.mp hc).1
  -- the navigation of the member's check
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk (by rfl)
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre,
    ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchkA
  obtain ⟨a, ha, hax⟩ := ha_pre
  have hg_ld : Core.Good ⟨E, env, t, some n⟩ cs_load := hgood.sub hsub_ld
  have hg_chk : Core.Good ⟨E, env, t, some n⟩ cs_chk := hgood.sub hsub_chk
  have h0' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := Ingress.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hprojE
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrecA
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B 0 (.indc ind) := by
    rw [hb, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold Ingress.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblockE
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj (hcb.symm.trans hrec.muts))
  subst hmsEq
  rw [h0'] at hms planned hraw
  have hiEq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape₀, trace⟩ := hlev
  injection shape₀ with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst typePtr
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hg_ld.1 hhp t
  obtain ⟨ty'₁, hcT₁, -, htmT⟩ :=
    LoadedReads.annotation_canon_exact ht hlvls (LoadedReads.blockSelf_key t B #[.indc ind])
      hagree rty built planned trace htyE hlbb hdef
  -- the former, checked at the prefix
  obtain ⟨ty', hcT, hann, hcheck, -⟩ := formerChecked_of_member ht hst hinv hblockE hrec.muts
    hprojE hchk htyE hlbb hdef hfv hstored hfreshT hfreeT
  have hty'₁ : ty'₁ = ty' := Option.some.inj (hcT₁.symm.trans hcT)
  rw [hty'₁] at htmT
  have hst₀' : ty₀.stripPis (p₀.nP + p₀.nIdx) = some (bs₀, .sort p₀.resSort) := by
    have h := hst₀
    rw [hcvT] at h
    exact h
  obtain ⟨bsT, hstT, -⟩ := Decl.stripPis_sort_of_annotates _ hann hst₀'
  have hcheckT : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ := by
    rw [hcvT]
    exact hcheck
  obtain ⟨ty'', ⟨-, -, -, -, -, -, -, hlpd', hcr', -⟩, hcv'⟩ := hcheck
  have hty'' : ty' = ty'' := congrArg Ix.Kernel.ConstantVal.type hcv'
  have htype : ty'.hasFvar = false ∧
      ty'.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
      ty'.constsResolve env = true ∧ ty'.looseBVarsBounded 0 = true := by
    refine ⟨Decl.annotates_hasFvar_false hann hfv, ?_, ?_,
      Decl.annotates_looseBVarsBounded hann 0 hlbb⟩
    · rw [hty'']
      exact hlpd'
    · rw [hty'']
      exact hcr'
  -- the dispatch is native
  have hsafeF : Ingress.repBoolField ind.isUnsafe = .field 0 := by
    rw [hinlogic.1]
    rfl
  rw [hsafeF, Nat.cast_zero] at ev_chk
  rcases Decl.native_induct_dispatch ev_chk with hnative | modeled
  rotate_left
  · exfalso
    obtain ⟨before, result, after, children, obs, hne, hext, -, hsubc⟩ := modeled
    exact hne (hnat blkPtr result before after children b obs
      (fun cl hcl => hsub_chk cl (hsubc cl hcl))
      (Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb_rep) hb_eq)
  obtain ⟨native⟩ := hnative
  obtain ⟨shape⟩ := Decl.native_shape_calls native.observed native.subset
  have e_sort : Heap.Extends m_chk native.before := native.initialToShape
  have e_ctor : Heap.Extends m_chk shape.ctorBefore :=
    native.initialToShape.trans shape.initial_to_ctors
  have ctorRun₀ := shape.ctorRun
  have hbRepCtor : Bytes.RepAddressRef Core.addrTy shape.ctorBefore b blkPtr :=
    Bytes.repAddressRef_heapMono₂ Core.addrTy e_ctor hb_rep
  have hblockB : recordOf E (Core.ixAddr b) = some cb := by
    rw [hb_eq]
    exact hblockE
  -- the constructor count, from the former's direct load
  obtain ⟨srcA, hsrcA⟩ := canonicalRecord_value hst.decoded hrecA
  have hshapeA : srcA.value.info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := by
    rw [hsrcA]
    rfl
  obtain ⟨par, parArg, mid, inner, hparEq, -, hparRep, hdirect, hinner, -⟩ :=
    Ingress.get_ci_iPrj_subcall (base := ⟨E, env, t, some n⟩) srcA hshapeA ha hg_ld ev_ld
  rw [h0', Nat.cast_zero] at hdirect
  have hblockPar : recordOf E (Core.ixAddr par) = some cb := by
    rw [hparEq]
    exact hblockE
  obtain ⟨srcB, hsrcB⟩ := canonicalRecord_value hst.decoded hblockPar
  obtain ⟨-, -, -, hc39⟩ := Ingress.get_ci_iprj_header_bounds (base := ⟨E, env, t, some n⟩) (i := 0)
    (members := #[.indc ind]) srcB (by rw [hsrcB]; exact hrec.muts)
    (by rw [ZMod.val_zero]; rfl) (hg_ld.sub hinner) hparRep hdirect
  -- each slot of the loop loads its constructor and scopes its type
  have hscope : ∀ j < ind.ctors.size, Nonempty (Assembly.CtorScopeRead b 0 ((j : Nat) : F) 0
      ind.params.toNat ind.lvls.toNat cs_chk) := by
    intro j hj
    simpa only [Nat.zero_add] using
      Assembly.native_ctor_scope_reads hc39 ind.ctors.size 0 (by omega) hbRepCtor
        shape.ctorSubset ctorRun₀ j hj
  have hjval : ∀ {j : Nat}, j < ind.ctors.size → ZMod.val ((j : Nat) : F) = j := fun {j} hj =>
    ZMod.val_natCast_of_lt (Nat.lt_trans (show j < 72057594037927936 by omega) (by decide))
  have hmem0 : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val (0 : F)]? = some (.indc ind) := by
    rw [ZMod.val_zero]
    rfl
  have hclosed : ∀ j (ct : Ixon.Constructor) (cty : Ix.Kernel.Expr .anon), j < ind.ctors.size →
      ind.ctors[j]? = some ct →
      (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ct.typ = .ok cty →
      cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true := by
    intro j ct cty hj hct hcty
    obtain ⟨checked⟩ := hscope j hj
    exact LoadedReads.ctor_scope_closed ht hg_chk checked hblockB hrec.muts hmem0
      (by rw [hjval hj]; exact hct) (by rw [hb_eq]; exact hcty)
  have hctysE : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
        cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true := by
    intro k ct hct
    have hk : k < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
    have hkc : k < cs.length := by
      rw [hlen]
      exact hk
    obtain ⟨ct', tyj, h1, h2, -, -, h5, -, -⟩ := hcs k cs[k] (List.getElem?_eq_getElem hkc)
    have hctEq : ct' = ct := Option.some.inj (h1.symm.trans hct)
    rw [hctEq] at h2 h5
    have h5E := ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5
    exact ⟨h2, tyj, h5E, hclosed k ct tyj hk hct h5E⟩
  -- the constructor family, chosen once
  obtain ⟨ctorsA, rawTypes, hcanonA, hcanonR, hcload_gen⟩ :=
    stagedCtorLoads_of_block_raw (nP := p₀.nP) ht hg_chk
    hblockB hrec.muts hinlogic.2 hc56 hlenP (by
      intro j cv hcv
      obtain ⟨ct, h1, h2, -, h4, hc1, hc2, h5⟩ := hctor j cv hcv
      have h5E := ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5
      obtain ⟨hl, hd⟩ := hclosed j ct cv.1.type (hjlt hcv) h1 h5E
      refine ⟨ct, h1, h2, h4.trans hnP.symm, congrArg ConstantVal.levelParams hc1, hc2, ?_, hl, hd⟩
      rw [hb_eq]
      exact h5E)
    (fun j hj => by
      obtain ⟨checked⟩ := hscope j hj
      exact ⟨_, _, _, _, _, checked.loaded, checked.loadSubset, checked.blockRep⟩)
  have hcloadT := hcload_gen (Core.keyOf t) (fun i hi x hx => ⟨rfl, inferInstance⟩)
    (fun x hx => rfl)
  -- the stage's keying on the block's cells
  have hnt : ∀ T : Core.KKey, Core.keyOf t (Core.iprjAddr B 0) ≠ Ix.Kernel.projTableName T :=
    fun _ => Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  let cvS : ConstantVal .anon := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
  have hused : ∀ caps₁ : Ix.Kernel.IndCaps .anon, ∀ i ∈ usedRefIdxs cb, ∀ x,
      cb.refs.toList[i]? = some x →
      (Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁).κ x = Core.keyOf t x ∧
        Core.ProjPermitted (Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁).κ x := by
    intro caps₁ i hi x hx
    obtain ⟨ci, hci⟩ := hstored i hi x hx
    exact ctorStage_of_find (cvF := cvS) hfreshT hnt hci
  have hrecur : ∀ caps₁ : Ix.Kernel.IndCaps .anon,
      ∀ x ∈ Ingress.blockRecurAddrs B (#[.indc ind] : Array Ixon.MutConst).toList,
      (Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁).κ x = Core.keyOf t x := by
    intro caps₁ x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨m, hm, rfl⟩ := LoadedReads.blockRecurAddrs_get hk
    have hk0 : k = 0 := by
      have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
      omega
    subst hk0
    have hmm : m = .indc ind := by simpa using hm.symm
    subst hmm
    rw [LoadedReads.memberAddr_indc]
    exact ctorStage_former (cvF := cvS) rfl
  have hTname : p₀.cvT.name = Core.keyOf t (Core.iprjAddr B 0) := by
    rw [hcvT]
  have hbaseT : p₀.cvT.name.base = p₀.cvT.name := by
    rw [hTname]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hfnTbl : env.find? (Ix.Kernel.projTableName p₀.cvT.name) = none :=
    haux.fresh_of_base_none (by
      show env.find? p₀.cvT.name.base = none
      rw [hbaseT, hTname]
      exact hfreshT)
  -- the constructors' keys
  have hT_ctor : ∀ j, j < ind.ctors.size →
      Core.keyOf t (Core.iprjAddr B 0) ≠ keyOf t (ctorAddr B 0 j) := by
    intro j hj e
    have ha' : ctorAddr B 0 j = memberAddr B 0 (.indc ind) := (Core.keyOf_inj htwf e).symm
    have h1 := hrec.ctors j hj
    rw [ha', hrec.former] at h1
    have hinfo' := congrArg Ixon.Constant.info (Option.some.inj h1)
    simp [memberProjection, constructorProjection] at hinfo'
  -- the raw facts of the walked trace, at the prefix's store
  have hcovChk : Ingress.CanonicalHashCoverage E cs_chk := fun bytes value hh hsz hdec =>
    hcov bytes value (Core.hashed_mono hsub_chk hh) hsz hdec
  have hraw_at : ∀ env' : Ix.Kernel.Env .anon,
      Core.RawRecordFacts (Ingress.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk) ∧
      Decl.OneTypePeerReads (Ingress.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk) b p₀.cvT.name
        p₀.cvT.levelParams.length p₀.nP p₀.nIdx p₀.ctors.length 0 := by
    intro env'
    refine ⟨Ingress.rawRecordFacts_of_hashed_trace (base := ⟨E, env', t, some n⟩) ev_chk hg_chk hcovChk,
      ?_⟩
    obtain ⟨srcF, hsrcF⟩ := canonicalRecord_value hst.decoded
      (show recordOf E (Core.iprjAddr (Core.ixAddr b) (ZMod.val (0 : F))) =
        some (memberProjection B 0 (.indc ind)) by rw [ZMod.val_zero, hb_eq]; exact hprojE)
    obtain ⟨srcB', hsrcB'⟩ := canonicalRecord_value hst.decoded hblockB
    have hpeer := Assembly.native_peer_reads (raw := Ingress.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk)
      (block := b) (i := 0) srcB' srcF
      (by rw [hsrcF, ZMod.val_zero, hb_eq]; rfl) (by rw [hsrcB']; exact hrec.muts) hmem0
      (Assembly.native_inductives_singleton (Nat.le_of_eq rfl) hmem0) htwf
    have hT : (Ingress.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk).κ
        (Core.iprjAddr (Core.ixAddr b) (ZMod.val (0 : F))) = p₀.cvT.name := by
      rw [hcvT, ZMod.val_zero, hb_eq]
      rfl
    have hL : ind.lvls.toNat = p₀.cvT.levelParams.length := by
      rw [hcvT]
      simp
    rw [hT, hL, ← hnP, ← hnIdx, ← hlenP] at hpeer
    exact hpeer
  -- the constructors' outputs at the stage, at every recursion flag
  have hlpsL : ind.lvls.toNat = p₀.cvT.levelParams.length := by
    rw [hcvT]
    simp
  have hrun_at : ∀ a₁ a₂ a₃ a₄ : Nat, a₁ = ind.params.toNat → a₂ = ind.indices.toNat →
      a₃ = ind.ctors.size → a₄ = ind.lvls.toNat →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [rc, tyPtr, .field (a₁ : F), .field (a₂ : F), .field (a₃ : F), .field (a₄ : F), blkPtr,
          .field 0, shape.sortLevel, .field 0, .field 0]
        shape.ctorBefore shape.result shape.after shape.ctorCalls := by
    intro a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄
    subst h₁ h₂ h₃ h₄
    exact ctorRun₀
  have ctorRun := hrun_at p₀.nP p₀.nIdx p₀.ctors.length p₀.cvT.levelParams.length hnP hnIdx
    hlenP hlpsL.symm
  have h256 : (2 : Nat) ^ 56 = 72057594037927936 := by norm_num
  have houts : ∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
      sortss.length = p₀.ctors.length ∧
      ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
        sortss[j]? = some sorts ∧
        Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx p₀.resSort cvS.type
          (rawTypes.getD j default) c cA sorts := by
    intro isRec
    have hunit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
        (∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0) →
        (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort p₀.resSort) isRec).unitlike =
          true ∧
        (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort p₀.resSort) isRec).unitParams =
          ind.params.toNat := by
      intro h0 h1 hf
      have hl : p₀.ctors.length = 1 := hlenP.trans h1
      obtain ⟨c, hc⟩ : ∃ c, p₀.ctors = [c] := by
        cases hm : p₀.ctors with
        | nil =>
          rw [hm] at hl
          simp at hl
        | cons c rest =>
          cases rest with
          | nil => exact ⟨c, rfl⟩
          | cons c' rest' =>
            rw [hm] at hl
            simp at hl
      have hc0 : p₀.ctors[0]? = some c := by
        rw [hc]
        rfl
      obtain ⟨ct, hct, -, -, -, -, hc2, -⟩ := hctor 0 c hc0
      have hcP : (p₀.toInductiveShape.withSort p₀.resSort).ctors = [c] := hc
      have hnP0 : (p₀.toInductiveShape.withSort p₀.resSort).nIdx = 0 := hnIdx.trans h0
      have hnF0 : c.2 = 0 := by
        rw [hc2]
        exact hf ct hct
      have hu : (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort p₀.resSort) isRec).unitlike =
            true ∧
          (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort p₀.resSort) isRec).unitParams =
            (p₀.toInductiveShape.withSort p₀.resSort).nP := by
        simp [Ix.Kernel.nativeCapsAt, hcP, hc, hnP0, hnF0, hnIdx, h0]
      exact ⟨hu.1, hu.2.trans hnP⟩
    have hcore := ctorStageCoreFacts_of_block (p := p₀.toInductiveShape.withSort p₀.resSort)
      (isRec := isRec) ht hinv hst.decoded hP hkeys hblockE hrec.muts hprojE
      ⟨by rw [h256]; exact hp56, by rw [h256]; exact hi56, by rw [h256]; exact hc56⟩
      htyE hlbb hdef hctysE hstored hcT hfreshT hunit hfreeT.1 htype hstT
    let caps₁ := Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort p₀.resSort) isRec
    let cS := Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁
    have hcload := hcload_gen cS.κ (hused caps₁) (by rw [hb_eq]; exact hrecur caps₁)
    -- the former's type at the stage
    have htmS : Decl.TmCExact cS.κ m_chk (Core.posOf (List.range ind.lvls.toNat) ty') tyPtr := by
      refine TmCExact.rekey htmT (fun a' hin => ?_) (fun a' hp _ => ?_)
      · rcases rty.addrIn_used a' hin with hu | hr
        · obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
          · refine (hused caps₁ i ?_ _ hr).1
            unfold usedRefIdxs
            rw [hrec.muts]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.indc ind,
              List.mem_singleton.mpr rfl, by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
          · refine (hused caps₁ i ?_ _ hr).1
            unfold usedRefIdxs
            exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
        · exact hrecur caps₁ _ hr
      · obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := rty.projIn_used a' hp
        · refine (hused caps₁ i ?_ _ hr).2
          unfold usedRefIdxs
          rw [hrec.muts]
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.indc ind,
            List.mem_singleton.mpr rfl, by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
        · refine (hused caps₁ i ?_ _ hr).2
          unfold usedRefIdxs
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
    have hformer : Core.Tm cS.κ 0 (fun _ => default) m_chk 0 ty' tyPtr := by
      have h := (htmS 0 (fun _ => default)).toTm
      rwa [Decl.posOf_range] at h
    -- the result sort
    obtain ⟨ind_lvl, hlvRep, hsame⟩ := shape.resultSort_staged (c := cS) (type := ty')
      (by omega) (hrc_m.toRCRep.mono e_sort) (hformer.mono e_sort) hcore.1
      (Core.CoreGood.ofRaw (hg_chk.sub shape.sortSubset) (fun _ _ => trivial)) hcore.2
    have hlveq : Core.LvEq p₀.resSort ind_lvl :=
      hsame bsT p₀.resSort (by rw [← hnP, ← hnIdx]; exact hstT)
    -- the loop at the stage
    have hfnF : ∀ c ∈ p₀.ctors, c.2 < 72057594037927936 := by
      intro c hc
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, h1, h2, -, -, hc1, hc2, h5⟩ := hctor j c hj
      have hjs := hjlt hj
      obtain ⟨checked⟩ := hscope j hjs
      have h5E := ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5
      obtain ⟨hl, hd⟩ := hclosed j ct c.1.type hjs h1 h5E
      have hg := hg_chk.sub checked.loadSubset
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hf56, -⟩ :=
        LoadedReads.ctor_load_canon ht hg.1 hg.2 checked.blockRep checked.loaded hblockB
          hrec.muts hmem0 (by rw [hjval hjs]; exact h1) (by rw [hjval hjs]; exact h2)
          (by rw [hb_eq]; exact h5E) hl hd
      rw [hc2]
      exact hf56
    obtain ⟨sortss, hlen_s, hout⟩ := Decl.native_ctor_staged IxVM.Refinement.Levels.levels
      (cS := cS) (fun _ => trivial) (T := p₀.cvT.name) (lps := p₀.cvT.levelParams)
      (nP := p₀.nP) (nIdx := p₀.nIdx) (ta := ty') (resSort := p₀.resSort) (ind_lvl := ind_lvl)
      (cs_root := cs_chk) (ctors := p₀.ctors) (ctorsA := ctorsA) (ctorRawTypes := rawTypes)
      (indIndex := 0) (b₀ := b)
      (by rw [hcvT]; simp) (by rw [hcvT]; simpa using hlvls) (by rw [hnP]; exact hp56)
      (by rw [hnIdx]; exact hi56) (by rw [hlenP]; exact hc39) hfnF hlveq hcload
      (fun c hc => (hlps_ctors c hc).1)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, h1, -, -, -, -, -, h5⟩ := hctor j c hj
        exact (hclosed j ct c.1.type (hjlt hj) h1
          (ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5)).1)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, -, -, h5⟩ := hctor j c hj
        exact Assembly.memberReader_read_noFvar h5)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, hc1, -, -⟩ := hctor j c hj
        show (Ix.Kernel.Env.mk (ConstantInfo.indInfo cvS caps₁ :: env.consts)).find? c.1.name = none
        rw [Decl.find?_cons_ne (by rw [hc1]; exact hT_ctor j (hjlt hj)), hc1]
        exact hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl,
          Or.inr ⟨ind, j, rfl, hjlt hj, rfl⟩⟩))
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, hc1, -, -⟩ := hctor j c hj
        rw [hc1]
        exact (hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl,
          Or.inr ⟨ind, j, rfl, hjlt hj, rfl⟩⟩)).1)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, hc1, -, -⟩ := hctor j c hj
        rw [hc1]
        exact Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _))
      (fun i => Ix.Kernel.Env.findProj?_none_of_fresh (by
        show (Ix.Kernel.Env.mk (ConstantInfo.indInfo cvS caps₁ :: env.consts)).find?
          (Ix.Kernel.projTableName p₀.cvT.name) = none
        rw [Decl.find?_cons_ne (by rw [hcvT]; exact hnt _)]
        exact hfnTbl) i)
      hcore.1.store hcore.1 hcore.2
      (hraw_at ⟨ConstantInfo.indInfo cvS caps₁ :: env.consts⟩).1
      (hraw_at ⟨ConstantInfo.indInfo cvS caps₁ :: env.consts⟩).2 shape.ctorSubset
      (hg_chk.sub shape.ctorSubset) (hrc_m.toRCRep.mono e_ctor) (hformer.mono e_ctor)
      hbRepCtor hlvRep ctorRun
    exact ⟨sortss, hlen_s, hout⟩
  have hctorsCanon : ∀ j c, p₀.ctors[j]? = some c →
      ∃ (ct : Ixon.Constructor) (cty' : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.params.toNat = ind.params.toNat ∧
        ct.lvls.toNat = ind.lvls.toNat ∧
        c.1.name = keyOf t (ctorAddr B 0 j) ∧ c.1.levelParams = List.range ct.lvls.toNat ∧
        c.2 = ct.fields.toNat ∧
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok c.1.type ∧
        c.1.type.looseBVarsBounded 0 = true ∧
        c.1.type.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
        LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
          (((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) :
            Nat) : F) + 1 + ((j : Nat) : F)) ct.typ c.1.type = some cty' ∧
        ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) := by
    intro j c hc
    obtain ⟨ct, h1, h2, h3, h4, hc1, hc2, h5⟩ := hctor j c hc
    obtain ⟨ct', cty', hct', hcanon', hA⟩ := hcanonA j c hc
    have hctEq : ct' = ct := Option.some.inj (hct'.symm.trans h1)
    subst hctEq
    have h5E := ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5
    obtain ⟨hl, hd⟩ := hclosed j ct' c.1.type (hjlt hc) h1 h5E
    exact ⟨ct', cty', h1, h2, h4, h3, congrArg ConstantVal.name hc1,
      congrArg ConstantVal.levelParams hc1, hc2, h5E, hl, hd, hcanon', hA⟩
  refine ⟨ty₀, ty', cvS, bsT, ctorsA, rawTypes, htyE, hlbb, hdef, hcT, hcvT, rfl, hnP, hnIdx, hlenP,
    hctorsCanon, hcheckT, hstT, hTname.symm, hcloadT.1, houts, ?_, hc56, hcanonR, ?_⟩
  -- one load of each slot, in the member check's calls
  rotate_left
  · intro j hj
    obtain ⟨checked⟩ := hscope j hj
    exact ⟨_, _, _, _, _, b, checked.loaded, fun cl hcl => hsub_chk cl (checked.loadSubset cl hcl),
      checked.blockRep, hb_eq⟩
  -- the later-use condition, from the loop's positivity scans
  intro cA hcA cbs body hstrip i hi hkind
  obtain ⟨j, hjA⟩ := List.mem_iff_getElem?.mp hcA
  have hjP : j < p₀.ctors.length := by
    rw [← hcloadT.1]
    exact (List.getElem?_eq_some_iff.mp hjA).1
  obtain ⟨c, cvCa₀, hc, hcA', hvs, hload⟩ := hcloadT.2 j hjP
  rw [hjA] at hcA'
  injection hcA' with hcAeq
  subst hcAeq
  obtain ⟨sortss, -, hout⟩ := houts false
  obtain ⟨c', cA', sorts, hc', hcA'', -, hout_j⟩ := hout j hjP
  rw [hc] at hc'
  injection hc' with hceq
  subst hceq
  rw [hjA] at hcA''
  injection hcA'' with hcAeq'
  subst hcAeq'
  obtain ⟨rcbs, rargs, cbs', es, hstR, -, hstA, -, -, -, -, -⟩ := hout_j.residual
  have hstrip' : (cvCa₀, c.2).1.type.stripPis (p₀.nP + c.2) = some (cbs, body) := hstrip
  rw [hstA] at hstrip'
  injection hstrip' with hcbs
  injection hcbs with hcbs _
  subst hcbs
  have hmen : (cbs'.getD (p₀.nP + i) default).1.mentionsConst p₀.cvT.name = true := by
    cases hm : (cbs'.getD (p₀.nP + i) default).1.mentionsConst p₀.cvT.name with
    | true => rfl
    | false =>
      exfalso
      have hord : Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs'.getD (p₀.nP + i) default).1 = .ordinary := by
        unfold Ix.Kernel.recFieldKind
        rw [hm]
        simp
      rcases hkind with h | h <;> rw [hord] at h <;> cases h
  have hjs : j < ind.ctors.size := by
    rw [← hlenP]
    exact hjP
  obtain ⟨bp, ptr', h1, h1', cs1, nl, tyv, pb, mi, sl, np, nf, us, h2, h2', r, cs2, ev_load,
    hsub1, hbp, hldv, e12, ev_pos, hsub2⟩ :=
    Decl.native_ctor_positivity_slots (b := b) (nP := ind.params.toNat) (i := 0) hc56
      ind.ctors.size 0 (by omega) shape.ctorSubset hbRepCtor ctorRun₀ j (Nat.zero_le _) hjs
  obtain ⟨nl', cty, cblk, cnp, cnf, b_c, hld', -, -, hrawT, -, -, -⟩ :=
    hload bp ptr' h1 h1' cs1 hsub1 hbp ev_load
  have hval := Except.ok.inj (hldv.symm.trans hld')
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hval
  obtain ⟨-, htyv, -⟩ := hval
  have hlpsA : cvCa₀.levelParams = List.range ind.lvls.toNat := by
    rw [hvs.2.1, (hlps_ctors c (List.mem_of_getElem? hc)).1, hcvT]
  have hcty : Decl.RawTmExact (Ingress.traceRecordCtx ⟨E, env, t, some n⟩ cs_chk).κ 0
      (fun _ => default) h2 0 (rawTypes.getD j default) cvCa₀.type tyv := by
    have h := (hrawT 0 (fun _ => default)).mono e12
    rw [hlpsA, Decl.posOf_range, ← htyv] at h
    exact h
  rw [← hnP] at ev_pos
  exact Decl.check_positivity_later_spec (c := Ingress.traceRecordCtx ⟨E, env, t, some n⟩ cs_chk)
    (by rw [hnP]; omega) (hraw_at env).2 (hraw_at env).1 (hg_chk.sub hsub2)
    (Ingress.traceRecordCtx_coverage _ hsub2) hcty hout_j.noProj hstR hstA
    (Bytes.repAddressRef_heapMono₂ Core.addrTy (ev_load.heap_extends.trans e12) hbp) ev_pos
    i hi hmen

end IxVM.Refinement.Typing
