import IxVMRefinement.Assembly.TypingBasisLoads

/-! # The unit-like and η-ι fields at the environment of the pins

The fields `unitLike`, `unitLikeRaw` and `etaIota` of the load contract at the prefix context
of the environment of the pins. Each starts from a load at a stored address that returns an
inductive with one constructor and no index. The store holds the committed row there (the
calls hash no collision with it), so the loaded counts are the row's member's; among the five
inductive rows only `PUnit`'s has one constructor and no index (`basis_unitRows`, decided), and
its first constructor's projection record is the row of `PUnit.unit` (`unit_load`). The fields
are then facts about the pins of `PUnit` and `PUnit.unit`: its capabilities, the unit-like
test of the kernel, and η typing (`basisEnv_etaStable`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open IxVM.Refinement.TableInhabit (basisEnv)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- At an inductive row whose member has one constructor and no index (as field elements),
the row is `PUnit`'s, its member has no parameter, and its first constructor's projection
record is the row of `PUnit.unit`. -/
def unitRowB (e : RowReader.Row) : Bool :=
  match e.2.info with
  | .iPrj ip =>
    match RowReader.blockOf StoreInhabit.basisRows ip.block with
    | some eb =>
      match eb.2.info with
      | .muts ms =>
        match ms[ip.idx.toNat]? with
        | some (.indc ind) =>
          !((((ind.indices.toNat : Nat) : F) == 0) && (((ind.ctors.size : Nat) : F) == 1)) ||
            ((keyOf ctab e.1 == Ix.Kernel.Key.role .punit) &&
              (((ind.params.toNat : Nat) : F) == 0) &&
              ((RowReader.findProjOf StoreInhabit.basisRows
                (IxVM.Consistency.constructorProjection ip.block ip.idx.toNat 0)).map
                  (fun e' => keyOf ctab e'.1) == some (Ix.Kernel.Key.role .punitUnit)))
        | _ => true
      | _ => true
    | none => true
  | _ => true

set_option maxHeartbeats 4000000 in
theorem basis_unitRows : StoreInhabit.basisRows.all unitRowB = true := by
  decide +kernel

private theorem toUInt64_toNat_u {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- **A load at a stored address that returns an inductive with one constructor and no index
reads `PUnit`'s row**: the address is `PUnit`'s, the parameter count is `0`, and the first
constructor of the loaded block's member is keyed as `PUnit.unit`. -/
theorem unit_load {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E) {lim : Option Nat}
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    {nl ty u blk : SourceValue F} {p i : F} {b : Bytes.Address}
    (ev : ObsFn W "Ingress::get_ci" [ap] h ptr h' cs) (hg : Good (bctx E lim).stored.toCtx cs)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (hld : loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]))
    (hb : Bytes.RepAddressRef addrTy h' b blk)
    (hres : (bctx E lim).stored.κ (ixAddr a) ≠ unresolvedKey) :
    keyOf ctab (ixAddr a) = Ix.Kernel.Key.role .punit ∧ p = 0 ∧
      keyOf ctab (cprjAddr (ixAddr b) (ZMod.val i) 0) = Ix.Kernel.Key.role .punitUnit := by
  obtain ⟨cm₀, hmem₀, hrec₀⟩ := stored_row hE hres (ixAddr_not_marker a)
  obtain ⟨rawBytes, blkBytes, cm, cb, xs, ind, b', i', hhA, haA, hexA, -, hhB, haB, hexB, -,
    hbrep, hidx, hi56, hinfo, hcb, hxs⟩ := L1.inductRecord_raw_of_get_ci ev hg.2 ha hld
  have hcm : cm = cm₀ := record_escape hE.1 hg.1 hrec₀ hhA haA hexA
  subst hcm
  have hbb : b = b' := addr_det hb hbrep
  subst hbb
  have hii : i = i' := Value.field.inj hidx
  subst hii
  -- the block row
  have hown := List.all_eq_true.mp StoreInhabit.owners_in _ hmem₀
  have hownEq : Ix.Cert.ownerOf (ixAddr a) cm = ixAddr b := by
    simp [Ix.Cert.ownerOf, hinfo]
  simp only [hownEq] at hown
  obtain ⟨cbr, hcbr⟩ := Option.isSome_iff_exists.mp (StoreInhabit.isSome_of_hasKey hown)
  have hrecB : Ix.Cert.recordAt E (ixAddr b) = some cbr := hE.2.1 _ _ hcbr
  have hcbEq : cb = cbr := record_escape hE.1 hg.1 hrecB hhB haB hexB
  subst hcbEq
  have hB : (ixAddr b, cb) ∈ StoreInhabit.basisRows := StoreInhabit.store_record_inv hcbr
  have hidxN : ((ZMod.val i).toUInt64).toNat = ZMod.val i :=
    toUInt64_toNat_u (lt_trans hi56 (by norm_num))
  have hxs' : xs[((ZMod.val i).toUInt64).toNat]? = some (.indc ind) := by
    rw [hidxN]
    exact hxs
  -- the loaded counts are the member's
  obtain ⟨nl', ty', u', blk', b'', hl, -, -, -, hsize⟩ :=
    basis_indRecord hE.1 lim ap ptr h h' cs a cm cb ⟨(ZMod.val i).toUInt64, ixAddr b⟩ xs ind ev hg
      ha hrec₀ hinfo hrecB hcb hxs'
  rw [hld] at hl
  injection hl with hv
  injection hv with _ _ hargs
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨-, -, hp, hz, hc, -, -, -⟩ := hargs
  have hpF : p = ((ind.params.toNat : Nat) : F) := Value.field.inj hp
  have hzF : (0 : F) = ((ind.indices.toNat : Nat) : F) := Value.field.inj hz
  have hcF : (1 : F) = ((ind.ctors.size : Nat) : F) := Value.field.inj hc
  -- the decided fact at the row
  have hrow := List.all_eq_true.mp basis_unitRows _ hmem₀
  have hblk := blockOf_of_mem hB
  simp only [unitRowB, hinfo, hblk, hcb, hxs', ← hzF, ← hcF, beq_self_eq_true, Bool.and_self,
    Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hrow
  obtain ⟨⟨hkey, hpar⟩, hproj⟩ := hrow
  refine ⟨hkey, hpF.trans hpar, ?_⟩
  -- the first constructor's projection record
  have hpos : 0 < ind.ctors.size := by
    rcases Nat.eq_zero_or_pos ind.ctors.size with h0 | hpos
    · rw [h0, Nat.cast_zero] at hcF
      exact absurd hcF one_ne_zero
    · exact hpos
  have hexp := RowReader.mem_expected hB hcb hxs' _ (RowReader.ctor_in_projs (j := 0) hpos)
  cases hfp : RowReader.findProjOf StoreInhabit.basisRows
      (IxVM.Consistency.constructorProjection (ixAddr b) ((ZMod.val i).toUInt64).toNat 0) with
  | none =>
    rw [hfp] at hproj
    cases hproj
  | some e' =>
    rw [hfp] at hproj
    have hk : keyOf ctab e'.1 = Ix.Kernel.Key.role .punitUnit := Option.some.inj hproj
    obtain ⟨-, -, h3⟩ := RowReader.found_spec BasisReads.basisRowStore hexp hfp
    rw [h3, hidxN] at hk
    exact hk

/-- `PUnit` is unit-like at the environment of the pins, at every level (decided). -/
theorem punit_unitLike (us : List KLevel) :
    Ix.Kernel.isUnitLikeTy basisEnv (.const (Ix.Kernel.Key.role .punit) us) = true := by
  rw [show Ix.Kernel.isUnitLikeTy basisEnv (.const (Ix.Kernel.Key.role .punit) us) =
    Ix.Kernel.isUnitLikeTy basisEnv (.const (Ix.Kernel.Key.role .punit) []) from rfl]
  decide +kernel

theorem basisEnv_find_punit :
    basisEnv.find? (Ix.Kernel.Key.role .punit) = some Ix.Kernel.punitA :=
  basisEnv_find_self (TableInhabit.basisEnv_pins .punitK _ List.mem_cons_self)

theorem basisEnv_find_punitUnit :
    basisEnv.find? (Ix.Kernel.Key.role .punitUnit) = some Ix.Kernel.punitUnitA :=
  basisEnv_find_self
    (TableInhabit.basisEnv_pins .punitK _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The unit-like conclusion, at `PUnit`. -/
theorem punit_unit_concl {E : Ixon.Env} {lim : Option Nat} {a : Bytes.Address} {p : F}
    {cvT : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hk : keyOf ctab (ixAddr a) = Ix.Kernel.Key.role .punit) (hp : p = 0)
    (hres : (bctx E lim).stored.κ (ixAddr a) ≠ unresolvedKey)
    (hfT : (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (ixAddr a)) =
      some (.indInfo cvT caps)) :
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains ((bctx E lim).stored.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (bctx E lim).stored.env
          (.const ((bctx E lim).stored.κ (ixAddr a)) us) = true)) := by
  have e : (bctx E lim).stored.κ (ixAddr a) = Ix.Kernel.Key.role .punit :=
    ((bctx E lim).stored.key_eq hres).trans hk
  rw [e] at hfT ⊢
  have hfT' : basisEnv.find? (Ix.Kernel.Key.role .punit) = some (.indInfo cvT caps) := hfT
  rw [basisEnv_find_punit] at hfT'
  have hpin : Ix.Kernel.punitA = Ix.Kernel.ConstantInfo.indInfo cvT caps := Option.some.inj hfT'
  cases hpin
  subst hp
  exact ⟨rfl, ZMod.val_zero.symm, Or.inr ⟨ZMod.val_zero, punit_unitLike⟩⟩

section
variable {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E) (lim : Option Nat)
include hE

theorem basis_unitLike :
    ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cvC : Ix.Kernel.ConstantVal .anon) (nPc : Nat),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good (bctx E lim).stored.toCtx cs →
    Bytes.RepAddressRef addrTy h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (ixAddr a)) =
      some (.indInfo cvT caps) →
    FewInductives (bctx E lim).stored.toCtx (ixAddr b) →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvC nPc 0) →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains ((bctx E lim).stored.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (bctx E lim).stored.env
          (.const ((bctx E lim).stored.κ (ixAddr a)) us) = true)) := by
  intro ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc ev hg ha hld hb hfT _ _
  have hres := basis_findRes E lim _ _ hfT
  obtain ⟨hk, hp, -⟩ := unit_load hE ev hg ha hld hb hres
  exact punit_unit_concl hk hp hres hfT

theorem basis_unitLikeRaw :
    ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs →
    (bctx E lim).stored.allowedTop "Ingress::get_ci" [ap] h →
    (bctx E lim).stored.κ (ixAddr a) ≠ unresolvedKey →
    Good (bctx E lim).stored.toCtx cs → Bytes.RepAddressRef addrTy h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (ixAddr a)) =
      some (.indInfo cvT caps) →
    FewInductives (bctx E lim).stored.toCtx (ixAddr b) →
    ZeroFieldCtorLoad (bctx E lim).stored b i → NonrecursiveLoad (bctx E lim).stored a →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains ((bctx E lim).stored.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (bctx E lim).stored.env
          (.const ((bctx E lim).stored.κ (ixAddr a)) us) = true)) := by
  intro ap ptr h h' cs a nl ty u blk p i b cvT caps ev _ hres hg ha hld hb hfT _ _ _
  obtain ⟨hk, hp, -⟩ := unit_load hE ev hg ha hld hb hres
  exact punit_unit_concl hk hp hres hfT

theorem basis_etaIota :
    ∀ (pp ptr nl ty u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (pa b : Bytes.Address) (i m : F) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel),
    ObsFn W "Ingress::get_ci" [pp] h1 ptr h2 cs1 → Good (bctx E lim).stored.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 pa pp →
    loadValue h2 ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field m, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (ixAddr pa)) =
      some (.indInfo cvT caps) →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvc cnP cnF) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧
        Good (bctx E lim).stored.toCtx cs3 ∧ Bytes.RepAddressRef addrTy h3 b bq) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧
        Good (bctx E lim).stored.toCtx cs5 ∧ Bytes.RepAddressRef addrTy h5 pa sp) →
    piSortAt (ZMod.val m) (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (caps.eta = true ∧
      caps.etaCtor = some ((bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) ∧
      caps.etaFields = cnF ∧ caps.etaParams = cnP ∧ cnP = ZMod.val m ∧
      cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts (bctx E lim).stored.env ((bctx E lim).stored.κ (ixAddr pa))
      ((bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) cvT caps cnP cnF := by
  intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev hg hpa hld hb hfT hfC
    _ _ _ _
  have hresT := basis_findRes E lim _ _ hfT
  have hresC := basis_findRes E lim _ _ hfC
  obtain ⟨hk, hm, hkc⟩ := unit_load hE ev hg hpa hld hb hresT
  have eT : (bctx E lim).stored.κ (ixAddr pa) = Ix.Kernel.Key.role .punit :=
    ((bctx E lim).stored.key_eq hresT).trans hk
  have eC : (bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0) =
      Ix.Kernel.Key.role .punitUnit :=
    ((bctx E lim).stored.key_eq hresC).trans hkc
  rw [eT] at hfT ⊢
  rw [eC] at hfC ⊢
  have hfT' : basisEnv.find? (Ix.Kernel.Key.role .punit) = some (.indInfo cvT caps) := hfT
  have hfC' : basisEnv.find? (Ix.Kernel.Key.role .punitUnit) = some (.ctorInfo cvc cnP cnF) := hfC
  have hη := basisEnv_etaStable (Ix.Kernel.Key.role .punit) (Ix.Kernel.Key.role .punitUnit) cvT
    cvc caps cnP cnF hfT'
  rw [basisEnv_find_punit] at hfT'
  rw [basisEnv_find_punitUnit] at hfC'
  have hpT : Ix.Kernel.punitA = Ix.Kernel.ConstantInfo.indInfo cvT caps := Option.some.inj hfT'
  have hpC : Ix.Kernel.punitUnitA = Ix.Kernel.ConstantInfo.ctorInfo cvc cnP cnF :=
    Option.some.inj hfC'
  cases hpT
  cases hpC
  subst hm
  refine ⟨⟨rfl, rfl, rfl, rfl, ZMod.val_zero.symm, rfl⟩, ⟨rfl, ⟨[], _, rfl, rfl⟩, ?_⟩⟩
  intro d us' args ty' hlen hcl hinf
  exact hη rfl rfl basisEnv_find_punitUnit basisEnv (Ix.Kernel.EnvExt.refl _) d us' args ty' hlen
    hcl hinf

end

end IxVM.Refinement.Typing
