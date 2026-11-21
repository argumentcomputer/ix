import IxVMRefinement.Assembly.TypingBasisInv

/-! # Load-contract fields at the environment of the pins

The scoped load contract `Core.ScopedLoadFacts` at the prefix context of the environment of the
pins, `(bctx E lim).stored`, field by field, for the fields that the records of the basis store
and the nineteen pins give. Every theorem here states one field of the contract at that
context, word for word.

* `basis_storedRes`, `basis_findRes`, `basis_ctorIndPerm`: the keying facts. A stored key
  resolves; the unresolved key is not stored.
* `basis_roleRes`: a fabricated role in force at a limit within the six basis groups is a
  basis role (`fabricated_basis`), whose pin is stored.
* `basis_indRecord`, `basis_recordShape`, `basis_canonical`: the record facts of every decoded
  store (`Decl.prefixLoadFacts_of_empty`'s, which do not read the environment).
* `basis_projCtorTele`, `basis_projFire`: vacuous, no projection table is stored.
* `basis_inductRecord`, `basis_inductBlock`: a load at a stored address reads the committed
  row there (the store holds it, and the calls hash no collision with the store), and the
  block that row names is a row too.
* `basis_whole`: the `whole` clause of `Facts`: a stored basis role's record names a block
  whose members and constructors are all stored.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open IxVM.Refinement.TableInhabit (basisEnv)

set_option linter.unusedVariables false

/-- **The prefix context of the environment of the pins**, for the store `E` and the limit
`lim`. -/
abbrev bctx (E : Ixon.Env) (lim : Option Nat) : Ctx := ⟨E, basisEnv, ctab, lim⟩

/-! ## Rows at stored addresses -/

/-- **An address the prefix keying resolves is a basis role's, with a committed row** that
every store of the basis records holds. -/
theorem stored_row {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E) {lim : Option Nat}
    {x : _root_.Address} (hres : (bctx E lim).stored.κ x ≠ unresolvedKey)
    (hm : ¬ IsProjMarker x) :
    ∃ cm, (x, cm) ∈ StoreInhabit.basisRows ∧ Ix.Cert.recordAt E x = some cm := by
  obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hres hm
  obtain ⟨r, hr, hk⟩ := basisEnv_find_role hci
  exact basis_role_record hE hr hk

/-- **A record loaded at an address the store holds is the store's record there**, in calls
that hash no collision with the store. -/
theorem record_escape {E : Ixon.Env} (hdec : Ingress.EnvDecoded E) {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {x : _root_.Address}
    {cm₀ cm : Ixon.Constant} (hrec : Ix.Cert.recordAt E x = some cm₀) {raw : ByteArray}
    (hh : Hashed cs raw) (ha : Address.blake3Pure raw = x)
    (hex : Ixon.deConstantExact raw = .ok cm) : cm = cm₀ := by
  have hrec' : (E.consts.get? x).bind (·.get?) = some cm₀ := hrec
  cases hg : E.consts.get? x with
  | none =>
    rw [hg] at hrec'
    exact absurd hrec' (by simp)
  | some lc =>
    rw [hg] at hrec'
    have hlc : lc.get? = some cm₀ := hrec'
    have hesc := load_escape hg hnc raw hh ha
    obtain ⟨c', hget', hex'⟩ := hdec x lc hg
    rw [hlc] at hget'
    have e1 : cm₀ = c' := Option.some.inj hget'
    rw [hesc, hex'] at hex
    exact (Except.ok.inj hex).symm.trans e1.symm

/-! ## The keying fields -/

section
variable (E : Ixon.Env) (lim : Option Nat)

theorem basis_storedRes : ∀ (a : _root_.Address) (ci : Ix.Kernel.ConstantInfo .anon),
    (bctx E lim).stored.env.find? (keyOf (bctx E lim).stored.t a) = some ci →
      (bctx E lim).stored.κ a ≠ unresolvedKey := by
  intro a ci hf
  rw [Ctx.stored_key_of_find (c := bctx E lim) hf]
  exact Resolved.ne

theorem basis_findRes : ∀ (a : _root_.Address) (ci : Ix.Kernel.ConstantInfo .anon),
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ a) = some ci →
      (bctx E lim).stored.κ a ≠ unresolvedKey := by
  intro a ci hf he
  rw [he] at hf
  have hf' : basisEnv.find? unresolvedKey = some ci := hf
  rw [basisEnv_unresolved] at hf'
  cases hf'

theorem basis_ctorIndPerm : ∀ (a b : _root_.Address) (i j : Nat)
    (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
    (cv : Ix.Kernel.ConstantVal .anon) (nP nF : Nat), HashedBlockAt (bctx E lim).stored.E b →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ a) = some (.indInfo cvT caps) →
    cvT.name = (bctx E lim).stored.κ (iprjAddr b i) →
    (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (cprjAddr b i j)) =
      some (.ctorInfo cv nP nF) → ProjPermitted (bctx E lim).stored.κ a := by
  intro a b i j cvT caps cv nP nF _ hf _ _
  have hr := basis_findRes E lim a _ hf
  have e : (bctx E lim).stored.κ a = keyOf ctab a := (bctx E lim).stored.key_eq hr
  rw [e] at hf
  exact Ctx.stored_projPermitted_of_find (c := bctx E lim) hf

/-- **A fabricated role in force is stored**, at a limit within the six basis groups. -/
theorem basis_roleRes (hlim : LimWithin (fun g => g < 6) ctab lim) :
    ∀ (r : Ix.Kernel.Role) (a : _root_.Address), (bctx E lim).stored.inForce r →
      fabricatedRole r = true →
      (bctx E lim).stored.t.addressOf? r = some a → (bctx E lim).stored.κ a ≠ unresolvedKey := by
  intro r a hf hfab ha
  have hg : Ix.SpecDigest.groupOf r < 6 := hlim r hf.1 hf.2
  obtain ⟨ci, hci, -⟩ := StoreInhabit.basisEnv_find (fabricated_basis r hfab hg)
  have hk : keyOf ctab a = Ix.Kernel.Key.role r := keyOf_of_addressOf committedTable_wf ha
  have hci' : basisEnv.find? (keyOf ctab a) = some ci := by
    rw [hk]
    exact hci
  rw [Ctx.stored_key_of_find (c := bctx E lim) hci']
  exact Resolved.ne

end

/-! ## The record fields of a decoded store -/

/-- The empty prefix context with no call selected. -/
abbrev emptyScope (E : Ixon.Env) (lim : Option Nat) : ScopedCtx where
  toCtx := ⟨E, Ix.Kernel.Env.empty, ctab, lim⟩
  allowed := fun _ => False

/-- The record fields hold for every decoded store at every scope (the empty prefix's
contract, whose record fields do not read the environment). -/
theorem decoded_loads {E : Ixon.Env} (hdec : Ingress.EnvDecoded E) (lim : Option Nat) :
    ScopedLoadFacts (emptyScope E lim) :=
  Decl.prefixLoadFacts_of_empty (c := ⟨E, Ix.Kernel.Env.empty, ctab, lim⟩) hdec (fun _ => rfl)
    (fun _ => False) (Decl.ScopeResolved.of_no_loads fun _ h => h.elim)

theorem basis_indRecord {E : Ixon.Env} (hdec : Ingress.EnvDecoded E) (lim : Option Nat) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (cm cb : Ixon.Constant) (p : Ixon.InductiveProj) (xs : Array Ixon.MutConst)
      (ind : Ixon.Inductive),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good (bctx E lim).stored.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr →
    Ix.Cert.recordAt (bctx E lim).stored.E (ixAddr a) = some cm → cm.info = .iPrj p →
    Ix.Cert.recordAt (bctx E lim).stored.E p.block = some cb → cb.info = .muts xs →
    xs[p.idx.toNat]? = some (.indc ind) →
    ∃ (nl ty u blk : SourceValue F) (b : Bytes.Address),
      loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, .field (ind.params.toNat : F),
        .field (ind.indices.toNat : F), .field (ind.ctors.size : F), u, blk,
        .field (p.idx.toNat : F)]) ∧
      Bytes.RepAddressRef addrTy h' b blk ∧ ixAddr b = p.block ∧
      p.idx.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56 :=
  (decoded_loads hdec lim).indRecord

theorem basis_recordShape {E : Ixon.Env} (hdec : Ingress.EnvDecoded E) (lim : Option Nat) :
    ∀ (ap r : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (cst : Ixon.Constant),
    ObsFn W "Ingress::load_verified_constant" [ap] h r h' cs → Good (bctx E lim).stored.toCtx cs →
    Bytes.RepAddressRef addrTy h a ap →
    Ix.Cert.recordAt (bctx E lim).stored.E (ixAddr a) = some cst →
    Specs.Callees.ConstShapeRep h' cst r :=
  (decoded_loads hdec lim).recordShape

theorem basis_canonical {E : Ixon.Env} (hdec : Ingress.EnvDecoded E) (lim : Option Nat) :
    ∀ (x : _root_.Address) (lc : Ixon.LazyConstant) (info : Ixon.ConstantInfo),
    (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF →
    (bctx E lim).stored.E.consts.get? x = some lc →
    lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ →
      ∀ cm, lc.get? = some cm → cm.info = info :=
  (decoded_loads hdec lim).canonical

/-! ## No projection table is stored -/

theorem basisEnv_noTowers : basisEnv.consts.all (fun ci => !ci.isTowerEntry) = true := by
  decide +kernel

theorem basisEnv_noTable {k : Ix.Kernel.Key .anon} {tbl : Ix.Kernel.ProjTable .anon}
    (h : basisEnv.find? k = some (.projInfo tbl)) : False := by
  have h1 := List.all_eq_true.mp basisEnv_noTowers _ (basisEnv_find_mem h).1
  exact absurd h1 (by simp [Ix.Kernel.ConstantInfo.isTowerEntry])

theorem basis_projCtorTele (E : Ixon.Env) (lim : Option Nat) :
    ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs → Good (bctx E lim).stored.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp → ip = .field i →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat)
      (tbl : Ix.Kernel.ProjTable .anon),
      (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) =
        some (.ctorInfo cvC nP nF) →
      (bctx E lim).stored.env.find?
          (Ix.Kernel.projTableName ((bctx E lim).stored.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
        some (.projInfo tbl) →
      Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true := by
  intro bp ip ptr h h' cs b i _ _ _ _ j cvC nP nF tbl _ htbl
  exact (basisEnv_noTable htbl).elim

/-- Every projection table the environment of the pins stores fires: it stores none. -/
theorem basis_projFire (E : Ixon.Env) (lim : Option Nat) :
    ProjTablesFire (bctx E lim).stored.t (bctx E lim).stored.E (bctx E lim).stored.env :=
  projTablesFire_of_noTable fun _ _ h => basisEnv_noTable h

/-! ## Loads at stored addresses -/

theorem basis_inductRecord {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    (lim : Option Nat) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty np ni nc u blk idx : SourceValue F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
      (bctx E lim).stored.allowedTop "Ingress::get_ci" [addr] h →
      (bctx E lim).stored.κ (ixAddr a) ≠ unresolvedKey → Good (bctx E lim).stored.toCtx cs →
      Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt (bctx E lim).stored.E (ixAddr a) = some cm ∧
      Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩ := by
  intro addr ptr h h' cs a nl ty np ni nc u blk idx ev _ hres hg ha hld
  obtain ⟨cm₀, -, hrec₀⟩ := stored_row hE hres (ixAddr_not_marker a)
  obtain ⟨rawBytes, blkBytes, cm, cb, xs, ind, b, i, hhA, haA, hexA, -, -, -, -, -, hbrep,
    hidx, -, hinfo, -, -⟩ := Ingress.inductRecord_raw_of_get_ci ev hg.2 ha hld
  have hcm : cm = cm₀ := record_escape hE.1 hg.1 hrec₀ hhA haA hexA
  subst hcm
  exact ⟨cm, b, i, hrec₀, hbrep, hidx, hinfo⟩

theorem basis_inductBlock {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    (lim : Option Nat) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a b : Bytes.Address) (nl ty np ni nc u blk : SourceValue F) (i : F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
      (bctx E lim).stored.allowedTop "Ingress::get_ci" [addr] h →
      (bctx E lim).stored.κ (ixAddr a) ≠ unresolvedKey → Good (bctx E lim).stored.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    ∃ (cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt (bctx E lim).stored.E (ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind) := by
  intro addr ptr h h' cs a b nl ty np ni nc u blk i ev _ hres hg ha hld hb
  obtain ⟨cm₀, hmem₀, hrec₀⟩ := stored_row hE hres (ixAddr_not_marker a)
  obtain ⟨rawBytes, blkBytes, cm, cb, xs, ind, b', i', hhA, haA, hexA, -, hhB, haB, hexB, -,
    hbrep, hidx, -, hinfo, hcb, hxs⟩ := Ingress.inductRecord_raw_of_get_ci ev hg.2 ha hld
  have hcm : cm = cm₀ := record_escape hE.1 hg.1 hrec₀ hhA haA hexA
  subst hcm
  have hbb : b = b' := addr_det hb hbrep
  subst hbb
  have hii : i = i' := Value.field.inj hidx
  subst hii
  have hown := List.all_eq_true.mp StoreInhabit.owners_in _ hmem₀
  have hownEq : Ix.Cert.ownerOf (ixAddr a) cm = ixAddr b := by
    simp [Ix.Cert.ownerOf, hinfo]
  simp only [hownEq] at hown
  obtain ⟨cbr, hcbr⟩ := Option.isSome_iff_exists.mp (StoreInhabit.isSome_of_hasKey hown)
  have hrecB : Ix.Cert.recordAt E (ixAddr b) = some cbr := hE.2.1 _ _ hcbr
  have hcbEq : cb = cbr := record_escape hE.1 hg.1 hrecB hhB haB hexB
  subst hcbEq
  exact ⟨cb, xs, ind, hrecB, hcb, hxs⟩

/-! ## Blocks stored whole -/

/-- Every row that is not a block has its key stored (decided). -/
theorem basis_rowsStored :
    StoreInhabit.basisRows.all (fun e => StoreInhabit.isMutsInfo e.2.info ||
      (basisEnv.find? (keyOf ctab e.1)).isSome) = true := by
  decide +kernel

/-- **A projection record of a block of the basis store has its key stored**, at the hash of
its canonical bytes. -/
theorem proj_stored {p : Ixon.Constant}
    (hp : p ∈ RowReader.expectedProjsOf StoreInhabit.basisRows)
    (hnm : StoreInhabit.isMutsInfo p.info = false) {x : _root_.Address}
    (hx : x = Address.blake3Pure (Ixon.serConstant p)) :
    (basisEnv.find? (IxVM.Consistency.keyOf ctab x)).isSome = true := by
  subst hx
  rw [← LoadedReads.keyOf_eq]
  have h1 : (RowReader.findProjOf StoreInhabit.basisRows p).map (·.2) = some p :=
    BasisReads.basisRowStore.projs p hp
  cases hf : RowReader.findProjOf StoreInhabit.basisRows p with
  | none =>
    rw [hf] at h1
    cases h1
  | some e' =>
    obtain ⟨hmem, he2, he1⟩ := RowReader.found_spec BasisReads.basisRowStore hp hf
    have h2 := List.all_eq_true.mp basis_rowsStored e' hmem
    simp only [he2, hnm, Bool.false_or] at h2
    rw [← he1]
    exact h2

/-- **The `whole` clause of `Facts` at the environment of the pins**: the record at a stored
address names a block of the store whose members and constructors are all stored. -/
theorem basis_whole : ∀ E, RecordsFor StoreInhabit.basisStore E →
    ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (basisEnv.find? (IxVM.Consistency.keyOf ctab a)).isSome = true →
      Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored ctab basisEnv B ms := by
  intro E hE a B c cb ms hst hrec hown _ hrecB hms
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hst
  obtain ⟨r, hr, hk⟩ := basisEnv_find_role hci
  obtain ⟨c₀, hmem₀, hrec₀⟩ := basis_role_record hE hr hk
  have hc : c = c₀ := Option.some.inj (hrec.symm.trans hrec₀)
  subst hc
  have hownK := List.all_eq_true.mp StoreInhabit.owners_in _ hmem₀
  have hownK' : StoreInhabit.hasKey B = true := by simpa [hown] using hownK
  obtain ⟨cb₀, hcb₀⟩ := Option.isSome_iff_exists.mp (StoreInhabit.isSome_of_hasKey hownK')
  have hcbEq : cb = cb₀ := Option.some.inj (hrecB.symm.trans (hE.2.1 _ _ hcb₀))
  subst hcbEq
  have hB : (B, cb) ∈ StoreInhabit.basisRows := StoreInhabit.store_record_inv hcb₀
  intro i m hm
  refine ⟨?_, fun ind j hmi hj => ?_⟩
  · have hp := RowReader.mem_expected hB hms hm _ List.mem_cons_self
    have hnm : StoreInhabit.isMutsInfo (IxVM.Consistency.memberProjection B i m).info = false := by
      cases m <;> rfl
    exact proj_stored hp hnm rfl
  · subst hmi
    have hp := RowReader.mem_expected hB hms hm _ (RowReader.ctor_in_projs hj)
    exact proj_stored hp rfl rfl

end IxVM.Refinement.Typing
