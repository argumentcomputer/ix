import IxVMRefinement.Assembly.TypingBasisFacts
import IxVMRefinement.Assembly.TypingDefnInhabit
import IxVMRefinement.L1.HashedBlock
import IxVMRefinement.L1.Hashed

/-! # The projection fields at the environment of the pins

The six fields of the load contract that relate a block to a stored constant through the
address of one of its projection records (`getCprj`, `getIprj`, `eta`, `projTables`,
`projTablesAt`, `ctorIndRes`), at the prefix context of the environment of the pins, from one
hypothesis about the store:

* `ProjectionsHeldAt E b`: the record `E` holds at `Core.iprjAddr b i`, if any, is the inductive
  projection of `(b, i)`, and the record at `Core.cprjAddr b i j`, if any, is the constructor
  projection of `(b, i, j)`, for every index.
* `HashedBlockProjectionsHeld E`: that, at every block a run hashed (`Core.HashedBlockAt`: the
  hash of bytes that decode exactly to a `muts` record, in bounded calls that hash no collision
  with `E`). This is the only form the fields use; `ProjectionsHeld E` (every block) implies it.

With it the block of each field is a block of the basis store, and:

* `getIprj`, `getCprj`, and the constructor load of `projTables`: the load represents the pin
  stored at the projection address (`iprjRow?`, `cprjRow?`: per row, the reading of the member
  or constructor and its canonical constant against the pin, evaluated; then
  `LoadedReads.get_ci_iprj_load_canon`, `LoadedReads.get_ci_cprj_load_canon`).
* `eta`, `projTablesAt`, the table clause of `projTables`: vacuous. The run loaded a member with
  one constructor and no index, and the only such member of the basis store is `PUnit`, whose
  constructor has no field and a type that is not a `∀` (`unit_ctor`).
* `ctorIndRes`: the record at the constructor's address names the block, whose member is a
  stored inductive.

`basis_loads` is the load contract, `basis_facts` is `Facts` on the six basis groups, and
`def_step_at_basis_of_projections` is the step of the definition record at the pins, each with
the predicate as its one hypothesis beyond the store and limit conditions.

`ProjectionCollision` and `hashedBlockProjectionsHeld_of_noProjectionCollision` give the
predicate from a collision clause: a record the store holds differs from, and has the same
hash as, the canonical projection record of a block the calls hashed, at some index.
-/

universe u

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.TableInhabit (basisEnv)
open Ix.Kernel (ConstantInfo ConstantVal Key Role)

set_option linter.unusedVariables false

/-! ## The predicate -/

/-- **The records the store holds at the projection addresses of the block `b` are those
projections**: the record at `Core.iprjAddr b i`, if any, is the inductive projection of member
`i` of `b`, and the record at `Core.cprjAddr b i j`, if any, is the constructor projection of
constructor `j` of member `i` of `b`, at every index. -/
def ProjectionsHeldAt (E : Ixon.Env) (b : _root_.Address) : Prop :=
  (∀ (i : Nat) (cm : Ixon.Constant), Ix.Cert.recordAt E (Core.iprjAddr b i) = some cm →
    cm.info = .iPrj ⟨i.toUInt64, b⟩) ∧
  (∀ (i j : Nat) (cm : Ixon.Constant), Ix.Cert.recordAt E (Core.cprjAddr b i j) = some cm →
    cm.info = .cPrj ⟨i.toUInt64, j.toUInt64, b⟩)

/-- The predicate at every block address. -/
def ProjectionsHeld (E : Ixon.Env) : Prop := ∀ b, ProjectionsHeldAt E b

/-- **The predicate at every block a run hashed**: the form the fields use. -/
def HashedBlockProjectionsHeld (E : Ixon.Env) : Prop :=
  ∀ b, Core.HashedBlockAt E b → ProjectionsHeldAt E b

theorem ProjectionsHeld.hashed {E : Ixon.Env} (h : ProjectionsHeld E) :
    HashedBlockProjectionsHeld E := fun b _ => h b

/-! ## Small facts -/

private theorem valU64 (i : F) : ((ZMod.val i).toUInt64).toNat = ZMod.val i := by
  simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]
  have : ZMod.val i < 18446744069414584321 := ZMod.val_lt i
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem valSmall {m : Nat} (hm : m < 72057594037927936) : ZMod.val (m : F) = m :=
  ZMod.val_natCast_of_lt (Nat.lt_of_lt_of_le hm (by decide))

theorem nat_of_field_zero {n : Nat} (hn : n < 72057594037927936)
    (h : (Value.field (0 : F) : SourceValue F) = .field (n : F)) : n = 0 := by
  injection h with h
  have h2 := congrArg ZMod.val h
  rw [ZMod.val_zero, valSmall hn] at h2
  exact h2.symm

theorem nat_of_field_one {n : Nat} (hn : n < 72057594037927936)
    (h : (Value.field (1 : F) : SourceValue F) = .field (n : F)) : n = 1 := by
  injection h with h
  have h1 : ((1 : Nat) : F) = (n : F) := by rw [Nat.cast_one]; exact h
  have h2 := congrArg ZMod.val h1
  rw [valSmall (m := 1) (by decide), valSmall hn] at h2
  exact h2.symm

private theorem defnValShape_ne_induct' (d : Ixon.Definition)
    (tyPtr valPtr hint nl ty np ni nc u blk idx : SourceValue F) :
    L1.defnValShape d tyPtr valPtr hint ≠
      .construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx] := by
  cases hk : d.kind <;> simp [L1.defnValShape, hk]

/-- **A load returning an inductive reads the member of a block it hashed**, with the member's
index and its index and constructor counts. -/
theorem induct_counts {cs : List (Call F)} (hbound : IxVM.Consistency.Bounded cs)
    {a b : Bytes.Address} {addr ptr nl ty np ni nc u blk idx : SourceValue F} {h h' : Heap F}
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]))
    (hb : Bytes.RepAddressRef Core.addrTy h' b blk) :
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive) (i : F),
      Hashed cs blkBytes ∧ Address.blake3Pure blkBytes = Core.ixAddr b ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧ cb.info = .muts ms ∧ idx = .field i ∧
      ms[ZMod.val i]? = some (.indc ind) ∧ ni = .field (ind.indices.toNat : F) ∧
      nc = .field (ind.ctors.size : F) ∧ ind.indices.toNat < 72057594037927936 ∧
      ind.ctors.size < 72057594037927936 := by
  obtain ⟨_, rawBytes, cm, _, _, _, _, _, _, _, hres⟩ := L1.get_ci_spec hbound ha ev
  unfold L1.GetCIRawResult at hres
  cases hinfo : cm.info with
  | defn d =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (L1.ok_inj (hld'.symm.trans hld))
      (defnValShape_ne_induct' d _ _ _ _ _ _ _ _ _ _ _)
  | axio _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, rfl, _⟩ := hres
    have heq := L1.ok_inj (hld'.symm.trans hld)
    simp at heq
  | quot _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, rfl, _⟩ := hres
    have heq := L1.ok_inj (hld'.symm.trans hld)
    simp at heq
  | recr _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := L1.ok_inj (hld'.symm.trans hld)
    simp at heq
  | dPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, d, _, _, _, _, _, _, _, hld', _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (L1.ok_inj (hld'.symm.trans hld))
      (defnValShape_ne_induct' d _ _ _ _ _ _ _ _ _ _ _)
  | cPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hld',
      _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hres
    have heq := L1.ok_inj (hld'.symm.trans hld)
    simp at heq
  | rPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hld',
      _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := L1.ok_inj (hld'.symm.trans hld)
    simp at heq
  | muts _ =>
    rw [hinfo] at hres
    exact False.elim hres
  | iPrj p =>
    rw [hinfo] at hres
    obtain ⟨hidx56, blkBytes, cb, xs, ind, _, hhB, haB, hexB, _, hcb, hxs, hld',
      _, _, hi, hc, _, _, blkPtr, b', hb_eq, hb_rep, rfl, _⟩ := hres
    have hv := L1.ok_inj (hld'.symm.trans hld)
    injection hv with _ _ hl
    injection hl with _ hl
    injection hl with _ hl
    injection hl with _ hl
    injection hl with hni hl
    injection hl with hnc hl
    injection hl with _ hl
    injection hl with hblk hl
    injection hl with hidx _
    subst hblk
    have e : b' = b := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb_rep hb
    subst e
    refine ⟨blkBytes, cb, xs, ind, ((p.idx.toNat : Nat) : F), hhB, ?_, hexB, hcb, hidx.symm, ?_,
      hni.symm, hnc.symm, hi, hc⟩
    · rw [hb_eq]
      exact haB
    · rw [valSmall hidx56, ← Array.getElem?_toList]
      exact hxs

/-- **A direct load of an inductive member reads the member of the block it hashed**, with its
index and constructor counts. -/
theorem iprj_counts {cs : List (Call F)} (hbound : IxVM.Consistency.Bounded cs)
    {b : Bytes.Address} {bp ptr : SourceValue F} {i : F} {h h' : Heap F}
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs)
    {nl ty np ni nc u blk idx : SourceValue F}
    (hld : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx])) :
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive),
      Hashed cs blkBytes ∧ Address.blake3Pure blkBytes = Core.ixAddr b ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧ cb.info = .muts ms ∧
      ms[ZMod.val i]? = some (.indc ind) ∧ ni = .field (ind.indices.toNat : F) ∧
      nc = .field (ind.ctors.size : F) ∧ ind.indices.toNat < 72057594037927936 ∧
      ind.ctors.size < 72057594037927936 := by
  obtain ⟨_, _, blkBytes, cb, ms, ind, _, v, hh, ha, hex, _, hms, hmem, _, hldv, hraw, _⟩ :=
    L1.get_ci_iprj_origin_spec hbound hb ev
  obtain ⟨_, _, hi, hc, _, _, _, _, _, _, rfl, _⟩ := hraw
  have hv := L1.ok_inj (hldv.symm.trans hld)
  injection hv with _ _ hl
  injection hl with _ hl
  injection hl with _ hl
  injection hl with _ hl
  injection hl with hni hl
  injection hl with hnc _
  refine ⟨blkBytes, cb, ms, ind, hh, ha, hex, hms, ?_, hni.symm, hnc.symm, hi, hc⟩
  rw [← Array.getElem?_toList]
  exact hmem

/-! ## The checks of the projection rows -/

/-- Every direct load of the member an inductive-projection row names represents the pin at
the row's key. -/
def IprjLoads (a : _root_.Address) (p : Ixon.InductiveProj) : Prop :=
  ∀ (E : Ixon.Env), RecordsFor StoreInhabit.basisStore E → ∀ (lim : Option Nat)
    (b : Bytes.Address) (i : F) (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
    Core.ixAddr b = p.block → ZMod.val i = p.idx.toNat →
    a = Core.iprjAddr (Core.ixAddr b) (ZMod.val i) →
    ¬ View.HashedCollision { env := E } [] cs → IxVM.Consistency.Bounded cs →
    Bytes.RepAddressRef Core.addrTy h b bp →
    ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs →
    ∃ ci, basisEnv.find? (Core.keyOf ctab a) = some ci ∧
      Core.CIPtrRep (bctx E lim).stored.κ h' ptr ci

/-- The facts of an inductive-projection row: its member is an inductive of a block row, and
its loads represent its pin. -/
def IprjRow (a : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∀ p, c.info = .iPrj p →
    (∃ eb ms ind, RowReader.blockOf StoreInhabit.basisRows p.block = some eb ∧
      eb.2.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind)) ∧ IprjLoads a p

/-- Every direct load of the constructor a constructor-projection row names represents the pin
at the row's key. -/
def CprjLoads (a : _root_.Address) (p : Ixon.ConstructorProj) : Prop :=
  ∀ (E : Ixon.Env), RecordsFor StoreInhabit.basisStore E → ∀ (lim : Option Nat)
    (b : Bytes.Address) (i j : F) (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
    Core.ixAddr b = p.block → ZMod.val i = p.idx.toNat → ZMod.val j = p.cidx.toNat →
    a = Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j) →
    ¬ View.HashedCollision { env := E } [] cs → IxVM.Consistency.Bounded cs →
    Bytes.RepAddressRef Core.addrTy h b bp →
    ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs →
    ∃ cv nP nF, basisEnv.find? (Core.keyOf ctab a) = some (.ctorInfo cv nP nF) ∧
      Core.CIPtrRep (bctx E lim).stored.κ h' ptr (.ctorInfo cv nP nF)

/-- The facts of a constructor-projection row: its constructor is one of an inductive member of
a block row; if that member has one constructor and no index, the pin has no field and a type
that is not a `∀`; and its loads represent its pin. -/
def CprjRow (a : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∀ p, c.info = .cPrj p →
    (∃ eb ms ind ct, RowReader.blockOf StoreInhabit.basisRows p.block = some eb ∧
      eb.2.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind) ∧
      ind.ctors[p.cidx.toNat]? = some ct ∧
      (ind.ctors.size = 1 → ind.indices.toNat = 0 →
        ∃ cv nP, basisEnv.find? (Core.keyOf ctab a) = some (.ctorInfo cv nP 0) ∧
          (cv.type.stripPis 1).isSome = false)) ∧ CprjLoads a p

/-- The check of an inductive-projection row. -/
def iprjRow? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (IprjRow a c)) :=
  match hinfo : c.info with
  | .iPrj p =>
    match hb : RowReader.blockOf StoreInhabit.basisRows p.block with
    | none => none
    | some eb =>
      match hms : eb.2.info with
      | .muts ms =>
        match hm : ms[p.idx.toNat]? with
        | some (.indc ind) =>
          match ExprReader.sharesCheck (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms)
              eb.2.sharing.toList with
          | none => none
          | some sh =>
            match ExprReader.readCheck (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms)
                sh ind.typ with
            | none => none
            | some ty =>
              if h1 : ty.1.looseBVarsBounded 0 = true ∧
                  ty.1.allLevelParamsDefined (List.range ind.lvls.toNat) = true then
                match hp : basisEnv.find? (Core.keyOf ctab a) with
                | some (ConstantInfo.indInfo cv caps) =>
                  if h3 : canonAnnC eb.2 (List.range ind.lvls.toNat)
                      ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) ind.typ ty.1 =
                        some cv.type ∧
                      cv = ⟨Core.keyOf ctab a, List.range ind.lvls.toNat, cv.type⟩ then
                    some ⟨fun p' hinfo' => by
                      have e : p = p' := by
                        rw [hinfo] at hinfo'
                        exact Ixon.ConstantInfo.iPrj.inj hinfo'
                      subst e
                      refine ⟨⟨eb, ms, ind, hb, hms, hm⟩, ?_⟩
                      intro E hE lim b i bp ptr h h' cs hbB hiI ha hnc hbd hbp ev
                      have hblock : IxVM.Consistency.recordOf E (Core.ixAddr b) = some eb.2 := by
                        rw [hbB]
                        exact recordOf_of_row hE (RowReader.blockOf_mem hb)
                      have hmem : ms[ZMod.val i]? = some (.indc ind) := by
                        rw [hiI]
                        exact hm
                      obtain ⟨ty', hcT, -, -, hrepS⟩ :=
                        LoadedReads.get_ci_iprj_load_canon RoleVal.committedDefaultRoleTable_check
                          hnc hbd hbp ev hblock hms hmem
                          (by rw [hbB]; exact read_mono hE ty.2) h1.1 h1.2
                      rw [hiI] at hcT
                      have e2 : cv.type = ty' :=
                        Option.some.inj ((canonAnn_of_C h3.1).symm.trans hcT)
                      subst e2
                      have hrep := hrepS basisEnv lim (row_usedRefs (RowReader.blockOf_mem hb))
                        (by rw [hbB]; exact row_blockStored (RowReader.blockOf_mem hb) hms) caps
                      rw [← ha, ← h3.2] at hrep
                      exact ⟨_, hp, hrep⟩⟩
                  else none
                | _ => none
              else none
        | _ => none
      | _ => none
  | _ => none

/-- The check of a constructor-projection row. -/
def cprjRow? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (CprjRow a c)) :=
  match hinfo : c.info with
  | .cPrj p =>
    match hb : RowReader.blockOf StoreInhabit.basisRows p.block with
    | none => none
    | some eb =>
      match hms : eb.2.info with
      | .muts ms =>
        match hm : ms[p.idx.toNat]? with
        | some (.indc ind) =>
          match hct : ind.ctors[p.cidx.toNat]? with
          | none => none
          | some ct =>
            if hcx : ct.cidx.toNat = p.cidx.toNat then
              match ExprReader.sharesCheck
                  (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms)
                  eb.2.sharing.toList with
              | none => none
              | some sh =>
                match ExprReader.readCheck
                    (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms) sh ct.typ with
                | none => none
                | some ty =>
                  if h1 : ty.1.looseBVarsBounded 0 = true ∧
                      ty.1.allLevelParamsDefined (List.range ct.lvls.toNat) = true then
                    match hp : basisEnv.find? (Core.keyOf ctab a) with
                    | some (ConstantInfo.ctorInfo cv nP nF) =>
                      if h3 : canonAnnC eb.2 (List.range ct.lvls.toNat)
                          (((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1 +
                            ((p.cidx.toNat : Nat) : F)) ct.typ ty.1 = some cv.type ∧
                          cv = ⟨Core.keyOf ctab a, List.range ct.lvls.toNat, cv.type⟩ ∧
                          nP = ct.params.toNat ∧ nF = ct.fields.toNat then
                        let mk : ((ind.ctors.size = 1 ∧ ind.indices.toNat = 0) →
                            nF = 0 ∧ (cv.type.stripPis 1).isSome = false) →
                            PLift (CprjRow a c) := fun hu => ⟨fun p' hinfo' => by
                          have e : p = p' := by
                            rw [hinfo] at hinfo'
                            exact Ixon.ConstantInfo.cPrj.inj hinfo'
                          subst e
                          refine ⟨⟨eb, ms, ind, ct, hb, hms, hm, hct, fun hs hi => ?_⟩, ?_⟩
                          · obtain ⟨hnF, hst⟩ := hu ⟨hs, hi⟩
                            rw [hnF] at hp
                            exact ⟨cv, nP, hp, hst⟩
                          · intro E hE lim b i j bp ptr h h' cs hbB hiI hjI ha hnc hbd hbp ev
                            have hblock : IxVM.Consistency.recordOf E (Core.ixAddr b) =
                                some eb.2 := by
                              rw [hbB]
                              exact recordOf_of_row hE (RowReader.blockOf_mem hb)
                            have hmem : ms[ZMod.val i]? = some (.indc ind) := by
                              rw [hiI]
                              exact hm
                            have hct' : ind.ctors[ZMod.val j]? = some ct := by
                              rw [hjI]
                              exact hct
                            have hcidx : ct.cidx.toNat = ZMod.val j := by
                              rw [hjI]
                              exact hcx
                            have hp' : basisEnv.find? (Core.keyOf ctab
                                (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) =
                                  some (.ctorInfo cv nP nF) := by
                              rw [← ha]
                              exact hp
                            obtain ⟨ty', hcT, -, -, hrepS⟩ :=
                              LoadedReads.get_ci_cprj_load_canon
                                RoleVal.committedDefaultRoleTable_check hnc hbd hbp ev hblock hms
                                hmem hct' hcidx (by rw [hbB]; exact read_mono hE ty.2) h1.1 h1.2
                            rw [hiI, hjI] at hcT
                            have e2 : cv.type = ty' :=
                              Option.some.inj ((canonAnn_of_C h3.1).symm.trans hcT)
                            subst e2
                            obtain ⟨-, hcv, hnP, hnF⟩ := h3
                            have hrep := hrepS basisEnv lim
                              (row_usedRefs (RowReader.blockOf_mem hb))
                              (by rw [hbB]; exact row_blockStored (RowReader.blockOf_mem hb) hms)
                              ⟨_, hp'⟩
                            rw [← ha, ← hcv, ← hnP, ← hnF] at hrep
                            exact ⟨cv, nP, nF, hp, hrep⟩⟩
                        if hsz : ind.ctors.size = 1 ∧ ind.indices.toNat = 0 then
                          if hz : nF = 0 ∧ (cv.type.stripPis 1).isSome = false then
                            some (mk fun _ => hz)
                          else none
                        else some (mk fun h => absurd h hsz)
                      else none
                    | _ => none
                  else none
            else none
        | _ => none
      | _ => none
  | _ => none

/-- An inductive projection. -/
def isIPrj : Ixon.ConstantInfo → Bool
  | .iPrj _ => true
  | _ => false

/-- A constructor projection. -/
def isCPrj : Ixon.ConstantInfo → Bool
  | .cPrj _ => true
  | _ => false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Every inductive-projection row passes its check** (decided). -/
theorem basis_iprjRows :
    StoreInhabit.basisRows.attach.all (fun x =>
      !isIPrj x.1.2.info || (iprjRow? x.1.1 x.1.2 x.2).isSome) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Every constructor-projection row passes its check** (decided). -/
theorem basis_cprjRows :
    StoreInhabit.basisRows.attach.all (fun x =>
      !isCPrj x.1.2.info || (cprjRow? x.1.1 x.1.2 x.2).isSome) = true := by
  decide +kernel

theorem iprj_row {a : _root_.Address} {c : Ixon.Constant}
    (hrow : (a, c) ∈ StoreInhabit.basisRows) {p : Ixon.InductiveProj}
    (hinfo : c.info = .iPrj p) :
    (∃ eb ms ind, RowReader.blockOf StoreInhabit.basisRows p.block = some eb ∧
      eb.2.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind)) ∧ IprjLoads a p := by
  have h1 := List.all_eq_true.mp basis_iprjRows ⟨(a, c), hrow⟩ (List.mem_attach _ _)
  have hi : isIPrj c.info = true := by rw [hinfo]; rfl
  simp only [hi, Bool.not_true, Bool.false_or] at h1
  obtain ⟨⟨hrl⟩, -⟩ := Option.isSome_iff_exists.mp h1
  exact hrl p hinfo

theorem cprj_row {a : _root_.Address} {c : Ixon.Constant}
    (hrow : (a, c) ∈ StoreInhabit.basisRows) {p : Ixon.ConstructorProj}
    (hinfo : c.info = .cPrj p) :
    (∃ eb ms ind ct, RowReader.blockOf StoreInhabit.basisRows p.block = some eb ∧
      eb.2.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind) ∧
      ind.ctors[p.cidx.toNat]? = some ct ∧
      (ind.ctors.size = 1 → ind.indices.toNat = 0 →
        ∃ cv nP, basisEnv.find? (Core.keyOf ctab a) = some (.ctorInfo cv nP 0) ∧
          (cv.type.stripPis 1).isSome = false)) ∧ CprjLoads a p := by
  have h1 := List.all_eq_true.mp basis_cprjRows ⟨(a, c), hrow⟩ (List.mem_attach _ _)
  have hi : isCPrj c.info = true := by rw [hinfo]; rfl
  simp only [hi, Bool.not_true, Bool.false_or] at h1
  obtain ⟨⟨hrl⟩, -⟩ := Option.isSome_iff_exists.mp h1
  exact hrl p hinfo

/-- The row of an expected projection record is at its hash. -/
theorem row_of_expected {p : Ixon.Constant}
    (hp : p ∈ RowReader.expectedProjsOf StoreInhabit.basisRows) {x : _root_.Address}
    (hx : x = Address.blake3Pure (Ixon.serConstant p)) : (x, p) ∈ StoreInhabit.basisRows := by
  subst hx
  have h1 : (RowReader.findProjOf StoreInhabit.basisRows p).map (·.2) = some p :=
    BasisReads.basisRowStore.projs p hp
  cases hf : RowReader.findProjOf StoreInhabit.basisRows p with
  | none =>
    rw [hf] at h1
    cases h1
  | some e' =>
    obtain ⟨hmem, he2, he1⟩ := RowReader.found_spec BasisReads.basisRowStore hp hf
    have e : e' = (Address.blake3Pure (Ixon.serConstant p), p) := Prod.ext he1 he2
    rw [← e]
    exact hmem

/-- **The block a store of the basis records holds at a block address is the block bytes a
run hashed there**, in calls that hash no collision with the store. -/
theorem hashed_block_eq {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    {cs : List (Call F)} (hnc : ¬ View.HashedCollision { env := E } [] cs) {blk : ByteArray}
    {cb : Ixon.Constant} {B : _root_.Address} {eb : RowReader.Row} (hh : Hashed cs blk)
    (ha : Address.blake3Pure blk = B) (hex : Ixon.deConstantExact blk = .ok cb)
    (hb : RowReader.blockOf StoreInhabit.basisRows B = some eb) : cb = eb.2 :=
  record_escape hE.1 hnc
    (hE.2.1 B eb.2 (StoreInhabit.store_record_of_mem (RowReader.blockOf_mem hb))) hh ha hex

/-! ## The fields -/

section
open IxVM.Refinement.Core

variable {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
  (hP : HashedBlockProjectionsHeld E) {lim : Option Nat}

include hE in
/-- **A family stored under a projection address of a block whose projections the store holds
names a block row.** -/
theorem fam_block {B : _root_.Address} (hB : ProjectionsHeldAt E B) {i : Nat}
    (hfam : (bctx E lim).stored.FamAt B i) :
    ∃ eb, RowReader.blockOf StoreInhabit.basisRows B = some eb := by
  rcases hfam with ⟨cv, caps, hf⟩ | ⟨j, cv, nP, nF, hf⟩
  · have hres := basis_findRes E lim _ _ hf
    obtain ⟨cm, hrow, hrec⟩ := stored_row hE hres (iprjAddr_not_marker _ _)
    obtain ⟨⟨eb, _, _, heb, _, _⟩, -⟩ := iprj_row hrow (hB.1 i cm hrec)
    exact ⟨eb, heb⟩
  · have hres := basis_findRes E lim _ _ hf
    obtain ⟨cm, hrow, hrec⟩ := stored_row hE hres (cprjAddr_not_marker _ _ _)
    obtain ⟨⟨eb, _, _, _, heb, _, _, _, _⟩, -⟩ := cprj_row hrow (hB.2 i j cm hrec)
    exact ⟨eb, heb⟩

include hE hP in
/-- **A constructor stored under a projection address of a hashed block is at a row** whose
record is that projection. -/
theorem ctor_row_of_found {B : _root_.Address} (hbh : HashedBlockAt E B) {i j : Nat}
    {ci : ConstantInfo .anon}
    (hf : (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (cprjAddr B i j)) = some ci) :
    ∃ cm, (cprjAddr B i j, cm) ∈ StoreInhabit.basisRows ∧
      cm.info = .cPrj ⟨i.toUInt64, j.toUInt64, B⟩ := by
  have hres := basis_findRes E lim _ _ hf
  obtain ⟨cm, hrow, hrec⟩ := stored_row hE hres (cprjAddr_not_marker _ _ _)
  exact ⟨cm, hrow, (hP B hbh).2 i j cm hrec⟩

include hE hP in
/-- **A constructor stored under a projection address of a member a run loaded with one
constructor and no index has no field and a type that is not a `∀`.** -/
theorem unit_ctor {cs : List (Call F)} (hnc : ¬ View.HashedCollision { env := E } [] cs)
    (hbd : IxVM.Consistency.Bounded cs) {blkBytes : ByteArray} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {ind : Ixon.Inductive} {b : Bytes.Address} {i : F}
    (hh : Hashed cs blkBytes) (ha : Address.blake3Pure blkBytes = ixAddr b)
    (hex : Ixon.deConstantExact blkBytes = .ok cb) (hms : cb.info = .muts ms)
    (hmem : ms[ZMod.val i]? = some (.indc ind)) (hsz : ind.ctors.size = 1)
    (hix : ind.indices.toNat = 0) {j : Nat} {cv : ConstantVal .anon} {nP nF : Nat}
    (hf : (bctx E lim).stored.env.find? ((bctx E lim).stored.κ
      (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cv nP nF)) :
    nF = 0 ∧ (cv.type.stripPis 1).isSome = false := by
  have hbh : HashedBlockAt E (ixAddr b) := ⟨cs, blkBytes, cb, ms, hnc, hbd, hh, hex, hms, ha⟩
  obtain ⟨cm, hrow, hinfo⟩ := ctor_row_of_found hE hP hbh hf
  obtain ⟨⟨eb, ms₀, ind₀, ct, heb, hms₀, hmem₀, -, hU⟩, -⟩ := cprj_row hrow hinfo
  have hcb : cb = eb.2 := hashed_block_eq hE hnc hh ha hex heb
  subst hcb
  have hmsEq : ms = ms₀ := Ixon.ConstantInfo.muts.inj (hms.symm.trans hms₀)
  subst hmsEq
  have hmem₁ : ms[ZMod.val i]? = some (.indc ind₀) := by
    rw [← valU64 i]
    exact hmem₀
  have hindEq : ind = ind₀ := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hmem₁))
  subst hindEq
  obtain ⟨cv', nP', hf', hst⟩ := hU hsz hix
  have hres := basis_findRes E lim _ _ hf
  have hk : (bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) j) =
      Core.keyOf ctab (cprjAddr (ixAddr b) (ZMod.val i) j) :=
    (bctx E lim).stored.key_eq hres
  rw [hk] at hf
  have e := hf.symm.trans hf'
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj e)
  exact ⟨rfl, hst⟩

include hE hP in
/-- **A direct load of a constructor of a stored family represents the constructor stored at
its projection address.** -/
theorem basis_cprj_core {bp ptr : SourceValue F} {i j : F} {h h' : Heap F} {cs : List (Call F)}
    {b : Bytes.Address} (ev : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs)
    (hfam : (bctx E lim).stored.FamAt (ixAddr b) (ZMod.val i))
    (hg : Good (bctx E lim).stored.toCtx cs) (hb : Bytes.RepAddressRef addrTy h b bp) :
    ∃ cv nP nF, (bctx E lim).stored.env.find? ((bctx E lim).stored.κ
        (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) = some (.ctorInfo cv nP nF) ∧
      CIPtrRep (bctx E lim).stored.κ h' ptr (.ctorInfo cv nP nF) := by
  have hbh : HashedBlockAt E (ixAddr b) := L1.hashedBlockAt_of_get_ci_cprj hg hb ev
  obtain ⟨eb, heb⟩ := fam_block hE (hP _ hbh) hfam
  obtain ⟨_, _, _, blkBytes, cb, ms, ind, ct, _, _, hh, ha, hex, _, hms, hmem, hct, _⟩ :=
    L1.get_ci_cprj_origin_spec hg.2 hb ev
  have hcb : cb = eb.2 := hashed_block_eq hE hg.1 hh ha hex heb
  subst hcb
  have hmem' : ms[ZMod.val i]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hmem
  have hct' : ind.ctors[ZMod.val j]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hct
  have hjlt : ZMod.val j < ind.ctors.size := by
    rcases Nat.lt_or_ge (ZMod.val j) ind.ctors.size with hl | hge
    · exact hl
    · rw [Array.getElem?_eq_none hge] at hct'
      cases hct'
  have hp := RowReader.mem_expected (RowReader.blockOf_mem heb) hms hmem' _
    (RowReader.ctor_in_projs hjlt)
  have hrow := row_of_expected hp (x := cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j)) rfl
  obtain ⟨-, hload⟩ := cprj_row hrow (p := ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩)
    rfl
  obtain ⟨cv, nP, nF, hci, hrep⟩ := hload E hE lim b i j bp ptr h h' cs rfl (valU64 i).symm
    (valU64 j).symm rfl hg.1 hg.2 hb ev
  have hres := basis_storedRes E lim _ _ hci
  have hk : (bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j)) =
      Core.keyOf ctab (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j)) :=
    (bctx E lim).stored.key_eq hres
  refine ⟨cv, nP, nF, ?_, hrep⟩
  rw [hk]
  exact hci

include hE hP in
/-- **A direct load of a member of a stored family represents the inductive stored at its
projection address.** -/
theorem basis_iprj_core {bp ptr : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    {b : Bytes.Address} (ev : ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs)
    (hfam : (bctx E lim).stored.FamAt (ixAddr b) (ZMod.val i))
    (hg : Good (bctx E lim).stored.toCtx cs) (hb : Bytes.RepAddressRef addrTy h b bp) :
    ∃ ci, (bctx E lim).stored.env.find? ((bctx E lim).stored.κ
        (iprjAddr (ixAddr b) (ZMod.val i))) = some ci ∧
      CIPtrRep (bctx E lim).stored.κ h' ptr ci := by
  have hbh : HashedBlockAt E (ixAddr b) := L1.hashedBlockAt_of_get_ci_iprj hg hb ev
  obtain ⟨eb, heb⟩ := fam_block hE (hP _ hbh) hfam
  obtain ⟨_, _, blkBytes, cb, ms, ind, _, _, hh, ha, hex, _, hms, hmem, _⟩ :=
    L1.get_ci_iprj_origin_spec hg.2 hb ev
  have hcb : cb = eb.2 := hashed_block_eq hE hg.1 hh ha hex heb
  subst hcb
  have hmem' : ms[ZMod.val i]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hmem
  have hp := RowReader.mem_expected (RowReader.blockOf_mem heb) hms hmem' _ List.mem_cons_self
  have hrow := row_of_expected hp (x := iprjAddr (ixAddr b) (ZMod.val i)) rfl
  obtain ⟨-, hload⟩ := iprj_row hrow (p := ⟨(ZMod.val i).toUInt64, ixAddr b⟩) rfl
  obtain ⟨ci, hci, hrep⟩ := hload E hE lim b i bp ptr h h' cs rfl (valU64 i).symm rfl hg.1 hg.2
    hb ev
  have hres := basis_storedRes E lim _ _ hci
  have hk : (bctx E lim).stored.κ (iprjAddr (ixAddr b) (ZMod.val i)) =
      Core.keyOf ctab (iprjAddr (ixAddr b) (ZMod.val i)) :=
    (bctx E lim).stored.key_eq hres
  refine ⟨ci, ?_, hrep⟩
  rw [hk]
  exact hci

include hE hP in
/-- **The `ctorIndRes` field**: the record at a stored constructor's address names the block of
a hashed block address, whose member is a stored inductive. -/
theorem basis_ctorIndRes : ∀ (b : _root_.Address) (i j : Nat) (cv : ConstantVal .anon)
    (nP nF : Nat), HashedBlockAt (bctx E lim).stored.E b →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (cprjAddr b i j)) =
      some (.ctorInfo cv nP nF) →
    (bctx E lim).stored.κ (iprjAddr b i) ≠ unresolvedKey := by
  intro b i j cv nP nF hbh hf
  obtain ⟨cm, hrow, hinfo⟩ := ctor_row_of_found hE hP hbh hf
  obtain ⟨⟨eb, ms, ind, ct, heb, hms, hmem, -, -⟩, -⟩ := cprj_row hrow hinfo
  have hp := RowReader.mem_expected (RowReader.blockOf_mem heb) hms hmem _ List.mem_cons_self
  have hu : (i.toUInt64.toNat).toUInt64 = i.toUInt64 := UInt64.ofNat_toNat
  have hs := proj_stored hp rfl (x := iprjAddr b i) (by
    show iprjAddr b i = Address.blake3Pure
      (Ixon.serConstant ⟨.iPrj ⟨(i.toUInt64.toNat).toUInt64, b⟩, #[], #[], #[], #[]⟩)
    rw [hu]
    rfl)
  rw [← LoadedReads.keyOf_eq] at hs
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
  exact basis_storedRes E lim _ ci hci

include hE hP in
/-- **The load contract at the environment of the pins**, for every store of the basis records
whose projections at hashed blocks are those projections, at every limit within the six basis
groups. -/
theorem basis_loads (hlim : LimWithin (fun g => g < 6) ctab lim) :
    ScopedLoadFacts (bctx E lim).stored where
  getCI := basis_getCI hE lim
  getCprj := by
    intro bp ptr i j h h' cs b ev _ hfam hg hb
    obtain ⟨cv, nP, nF, hf, hrep⟩ := basis_cprj_core hE hP ev hfam hg.raw hb
    refine ⟨⟨_, hrep⟩, fun cv' nP' nF' hf' => ?_⟩
    have e := hf'.symm.trans hf
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj e)
    exact hrep
  getIprj := by
    intro bp ptr i h h' cs b ev _ hfam hg hb
    exact basis_iprj_core hE hP ev hfam hg.raw hb
  indRecord := basis_indRecord hE.1 lim
  inductRecord := basis_inductRecord hE lim
  projTables := by
    intro bp ip ptr h h' cs b i ev _ hg hb hip hfam _
    subst hip
    obtain ⟨v, mid, cs_assert, cs_load, ev_assert, ev_load, hcalls⟩ :=
      Obs.«KernelModeled::proj_ctor».obs ev
    obtain ⟨cv, nP, nF, hf, hrep⟩ := basis_cprj_core hE hP ev_load hfam
      (hg.sub fun cl hcl => by simp [hcalls, hcl])
      (Bytes.repAddressRef_heapMono₂ addrTy ev_assert.heap_extends hb)
    refine ⟨⟨_, by simpa only [ZMod.val_zero] using hf, hrep⟩, ?_⟩
    intro sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP' nF' hctor hbind
    exfalso
    obtain ⟨blkBytes, cb, ms, ind, i', hh, ha, hex, hms, hidx, hmem, hni, hnc, hi56, hc56⟩ :=
      induct_counts gS.2 evS hsS hldS hbS
    have hii : i = i' := Value.field.inj hidx
    subst hii
    have hst := unit_ctor hE hP gS.1 gS.2 hh ha hex hms hmem (nat_of_field_one hc56 hnc)
      (nat_of_field_zero hi56 hni) hctor
    rw [hst.2] at hbind
    cases hbind
  projTablesAt := by
    intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG hs hld hblk
      j cvC nP nF hctor hnF
    exfalso
    obtain ⟨blkBytes, cb, ms, ind, i', hh, ha, hex, hms, hidx, hmem, hni, hnc, hi56, hc56⟩ :=
      induct_counts hgG.2 evG hs hld hblk
    have hii : i = i' := Value.field.inj hidx
    subst hii
    have hst := unit_ctor hE hP hgG.1 hgG.2 hh ha hex hms hmem (nat_of_field_one hc56 hnc)
      (nat_of_field_zero hi56 hni) hctor
    rw [hst.1] at hnF
    exact Nat.lt_irrefl 0 hnF
  unitLike := basis_unitLike hE lim
  unitLikeRaw := basis_unitLikeRaw hE lim
  eta := by
    intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1 hC hname hpos
      ev good hb hld hT hmod hsort hnz hrec haddr
    exfalso
    obtain ⟨blkBytes, cb, ms, ind, hh, ha, hex, hms, hmem, hni, hnc, hi56, hc56⟩ :=
      iprj_counts good.2 hb ev hld
    have hnC : cvc.name = (bctx E lim).stored.κ (ixAddr ac) := WhnfAux.name_of_find hC
    have hfC : (bctx E lim).stored.env.find? ((bctx E lim).stored.κ
        (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvc cnP cnF) := by
      rw [← hname, hnC]
      exact hC
    have hst := unit_ctor hE hP good.1 good.2 hh ha hex hms hmem (nat_of_field_one hc56 hnc)
      (nat_of_field_zero hi56 hni) hfC
    rw [hst.1] at hpos
    exact Nat.lt_irrefl 0 hpos
  etaIota := basis_etaIota hE lim
  recordShape := basis_recordShape hE.1 lim
  inductBlock := basis_inductBlock hE lim
  projTablesGuard := basis_projTablesGuard E lim
  canonical := basis_canonical hE.1 lim
  storedRes := basis_storedRes E lim
  findRes := basis_findRes E lim
  ctorIndRes := basis_ctorIndRes hE hP
  ctorIndPerm := basis_ctorIndPerm E lim
  roleRes := basis_roleRes E lim hlim

end

/-! ## `Facts` and the definition step at the basis -/

/-- **`Facts` on the six basis groups at the environment of the pins**, for the stores of the
basis records whose projections at hashed blocks are those projections. -/
theorem basis_facts
    (hP : ∀ E, RecordsFor StoreInhabit.basisStore E → HashedBlockProjectionsHeld E) :
    Facts.{u} ctab (fun g => g < 6) StoreInhabit.basisStore basisEnv :=
  basis_facts_of_loads fun E hE _ hlim => basis_loads hE (hP E hE) hlim

/-- A limit at most six is within the six basis groups. -/
theorem limWithin_six {n : Nat} (hn : n ≤ 6) : LimWithin (fun g => g < 6) ctab (some n) :=
  fun _ _ hr => Nat.lt_of_lt_of_le (hr n rfl) hn

section
open IxVM.Consistency
open IxVM.Refinement.RoleVal IxVM.Refinement.DefInhabit

/-- **The step of the real definition record at the environment of the pins**, with the prefix
invariant there given by `basis_loads`: what remains is the run, the store of the step holding
the basis records, the limit within the six basis groups, and the predicate. -/
theorem def_step_at_basis_of_projections {X : Ix.Kernel.Env .anon → Prop} (hX : KeepsValues X)
    {calls : List (Call F)} {E₀ E : Ixon.Env} {bAddr : _root_.Address} {n : Nat}
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls committedDefaultRoleTable E₀ E)
    (hc : recordOf E₀ defAddr = some defRecord)
    (hchk : CheckedAtFullAt calls bAddr committedDefaultRoleTable defAddr n)
    (hnat : NeedOk E₀ natAddr) (hzero : NeedOk E₀ zeroAddr)
    (hE : RecordsFor StoreInhabit.basisStore E) (hlim : LimWithin (fun g => g < 6) ctab (some n))
    (hP : HashedBlockProjectionsHeld E) (hXb : X TableInhabit.basisEnv) :
    ∃ new : List (Ix.Kernel.ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, TableInhabit.basisEnv.find? ci.name = none) ∧
      Decl.PrefixInv.{u} E committedDefaultRoleTable (some n)
        ⟨new ++ TableInhabit.basisEnv.consts⟩ ∧
      X ⟨new ++ TableInhabit.basisEnv.consts⟩ ∧
      (∀ x, ConstAddrOf defAddr defRecord x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf committedDefaultRoleTable x ∧
          Reads committedDefaultRoleTable E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, ConstAddrOf defAddr defRecord x ∧
        ci.name = keyOf committedDefaultRoleTable x) ∨ ∃ k s, ci.name = .aux k s :=
  def_step_at_basis hX hS hst hc hchk hnat hzero
    (basis_prefixInv_of_loads hE hlim (basis_loads hE hP hlim)) hXb

end

/-! ## The predicate from a collision clause -/

private theorem blake3Pure_hash_size' (b : ByteArray) :
    (Address.blake3Pure b).hash.size = 32 := by
  cases b with
  | mk arr =>
    have h := L1.blake3Pure_eq arr.toList
    simp only [Array.toArray_toList] at h
    rw [h]
    exact (Blake3.Pure.digest arr.toList).size_toArray

/-- **The collision clause**: a record the view holds (its record bytes, nothing else it holds)
differs from, and has the same hash as,
the canonical projection record, at some index, of a block the calls hashed (bytes that decode
exactly to a `muts` record). -/
def ProjectionCollision (V : View) (calls : List (Call F)) : Prop :=
  ∃ (blk : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (info : Ixon.ConstantInfo) (x : _root_.Address) (held : ByteArray),
    Hashed calls blk ∧ Ixon.deConstantExact blk = .ok cb ∧ cb.info = .muts ms ∧
    ((∃ i : UInt64, info = .iPrj ⟨i, Address.blake3Pure blk⟩) ∨
      ∃ i j : UInt64, info = .cPrj ⟨i, j, Address.blake3Pure blk⟩) ∧
    (∃ lc, V.env.consts.get? x = some lc ∧ lc.rawBytes = held) ∧
    Address.blake3Pure (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩) = x ∧
    held ≠ Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩

/-- **Without the collision, the store holds the projections of a hashed block**, for a store
whose records decode. -/
theorem projectionsHeldAt_of_noProjectionCollision {E : Ixon.Env} (hdec : L1.EnvDecoded E)
    {cs : List (Call F)} (hnp : ¬ ProjectionCollision { env := E } cs) {blk : ByteArray}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hh : Hashed cs blk)
    (hex : Ixon.deConstantExact blk = .ok cb) (hms : cb.info = .muts ms) :
    ProjectionsHeldAt E (Address.blake3Pure blk) := by
  have hsz := blake3Pure_hash_size' blk
  refine ⟨fun i cm hrec => ?_, fun i j cm hrec => ?_⟩
  · have hrec' : (E.consts.get? (Core.iprjAddr (Address.blake3Pure blk) i)).bind (·.get?) =
        some cm := hrec
    cases hg : E.consts.get? (Core.iprjAddr (Address.blake3Pure blk) i) with
    | none =>
      rw [hg] at hrec'
      cases hrec'
    | some lc =>
      rw [hg] at hrec'
      have hlc : lc.get? = some cm := hrec'
      have hraw : lc.rawBytes =
          Ixon.serConstant ⟨.iPrj ⟨i.toUInt64, Address.blake3Pure blk⟩, #[], #[], #[], #[]⟩ := by
        by_contra hne
        exact hnp ⟨blk, cb, ms, .iPrj ⟨i.toUInt64, Address.blake3Pure blk⟩,
          Core.iprjAddr (Address.blake3Pure blk) i, lc.rawBytes, hh, hex, hms,
          Or.inl ⟨i.toUInt64, rfl⟩, ⟨lc, hg, rfl⟩, rfl, hne⟩
      have hwf : (⟨.iPrj ⟨i.toUInt64, Address.blake3Pure blk⟩, #[], #[], #[], #[]⟩ :
          Ixon.Constant).wireWF := by
        rw [L1.emptyTablesConstant_wireWF]
        show (Address.blake3Pure blk).hash.size = 32
        exact hsz
      exact L1.canonical_of_wireWF hdec hwf hg hraw hlc
  · have hrec' : (E.consts.get? (Core.cprjAddr (Address.blake3Pure blk) i j)).bind (·.get?) =
        some cm := hrec
    cases hg : E.consts.get? (Core.cprjAddr (Address.blake3Pure blk) i j) with
    | none =>
      rw [hg] at hrec'
      cases hrec'
    | some lc =>
      rw [hg] at hrec'
      have hlc : lc.get? = some cm := hrec'
      have hraw : lc.rawBytes = Ixon.serConstant
          ⟨.cPrj ⟨i.toUInt64, j.toUInt64, Address.blake3Pure blk⟩, #[], #[], #[], #[]⟩ := by
        by_contra hne
        exact hnp ⟨blk, cb, ms, .cPrj ⟨i.toUInt64, j.toUInt64, Address.blake3Pure blk⟩,
          Core.cprjAddr (Address.blake3Pure blk) i j, lc.rawBytes, hh, hex, hms,
          Or.inr ⟨i.toUInt64, j.toUInt64, rfl⟩, ⟨lc, hg, rfl⟩, rfl, hne⟩
      have hwf : (⟨.cPrj ⟨i.toUInt64, j.toUInt64, Address.blake3Pure blk⟩, #[], #[], #[], #[]⟩ :
          Ixon.Constant).wireWF := by
        rw [L1.emptyTablesConstant_wireWF]
        show (Address.blake3Pure blk).hash.size = 32
        exact hsz
      exact L1.canonical_of_wireWF hdec hwf hg hraw hlc

/-- **The predicate from the collision clause**: if no calls that hash no collision with the
store hash a projection collision, the store holds the projections of every hashed block. -/
theorem hashedBlockProjectionsHeld_of_noProjectionCollision {E : Ixon.Env}
    (hdec : L1.EnvDecoded E)
    (hnp : ∀ cs : List (Call F), ¬ View.HashedCollision { env := E } [] cs →
      ¬ ProjectionCollision { env := E } cs) :
    HashedBlockProjectionsHeld E := by
  rintro b ⟨cs, blk, cb, ms, hnc, -, hh, hex, hms, rfl⟩
  exact projectionsHeldAt_of_noProjectionCollision hdec (hnp cs hnc) hh hex hms

/-! ## The collision clause and the public projection-image alternative -/

section
open IxVM.Consistency

/-- **The collision clause is an instance of the public alternative**: a record the view holds
at the hash of a projection image of a block the calls hashed, with other bytes, is a
`ProjImageCollision` with the view's data. So the negation of the public alternative gives the
negation of the clause. -/
theorem projImageCollision_of_projectionCollision {V : View} {calls : List (Call F)}
    {extra : List ByteArray} (h : ProjectionCollision V calls) :
    ProjImageCollision V extra calls := by
  obtain ⟨blk, cb, ms, info, x, held, hh, hex, hms, hinfo, hheld, hx, hne⟩ := h
  refine ⟨x, held, Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩, Or.inl (Or.inl hheld),
    ⟨blk, cb, ms, hh, hex, hms, ?_⟩, fun he => hne he.symm, hx⟩
  rcases hinfo with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, j, rfl⟩

/-- **The typing statement's alternative excludes the collision clause at the store a typing
run is read against**: with no projection-image collision in the sense of the typing half
(`ProjImageCollisionWith`, compared with the committed images), the run's calls hash no
`ProjectionCollision` with a store that merges the run's records, the witness's and the
committed prelude rows (`Merged`). -/
theorem Merged.noProjectionCollision {E₀ R E : Ixon.Env} {calls : List (Call F)} {V : View}
    {extra : List ByteArray} (hM : Merged E₀ R E) (hload : LoadedBy calls E₀)
    (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnp : ¬ ProjImageCollisionWith V extra R calls) :
    ¬ ProjectionCollision { env := E } calls := by
  intro h
  obtain ⟨blk, cb, ms, info, x, held, hh, hex, hms, hinfo, hheld, hx, hne⟩ := h
  have himg : HashedBlockProjImage calls (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩) := by
    refine ⟨blk, cb, ms, hh, hex, hms, ?_⟩
    rcases hinfo with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, j, rfl⟩
  have hne' : Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ ≠ held := fun he => hne he.symm
  apply hnp
  rcases hM.preimage hload (Or.inl hheld) with hrun | hR | ⟨p, hp, hp1, hp2⟩
  · exact Or.inl ⟨x, held, _, Or.inr (Or.inr hrun), himg, hne', hx⟩
  · exact Or.inr ⟨x, held, _, hR, himg, hne', hx⟩
  · have hhash : Address.blake3Pure p.2 = p.1 := ClosedFacts.committedRows_hashed p hp
    have hmem : held ∈ extra := by
      rw [← hp2]
      exact hextra _ (committedRows_footprint hp)
    have hheld_x : Address.blake3Pure held = x := by
      rw [← hp2, hhash, hp1]
    exact Or.inl ⟨x, held, _, Or.inr (Or.inl ⟨hmem, hheld_x⟩), himg, hne', hx⟩

/-- **`Facts` at the basis from the public alternative**: if no calls that hash no collision
with a store of the basis records hash a projection-image collision with it
(`ProjImageCollision`, the case of the public alternative), `Facts` holds on the six basis
groups at the environment of the pins. The hypothesis is about every run and every such store;
`Facts` quantifies over every run that is `Core.Good` for the store, and `Core.Good` excludes
only `View.HashedCollision`. -/
theorem basis_facts_of_noProjImageCollision
    (h : ∀ E, RecordsFor StoreInhabit.basisStore E → ∀ cs : List (Call F),
      ¬ View.HashedCollision { env := E } [] cs → ¬ ProjImageCollision { env := E } [] cs) :
    Facts.{u} ctab (fun g => g < 6) StoreInhabit.basisStore basisEnv :=
  basis_facts fun E hE => hashedBlockProjectionsHeld_of_noProjectionCollision hE.1
    fun cs hnc hpc => h E hE cs hnc (projImageCollision_of_projectionCollision hpc)

end

end IxVM.Refinement.Typing
