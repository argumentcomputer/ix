import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Claim.ClaimSeam
import Ix.IxVM.Consistency.ReadsKeys

/-! # From a record the circuit loaded to its reading

The record-loading layer proves, for a `get_ci` on an address, that the run hashed bytes with
that address and that the heap holds the circuit's conversion of the record they decode to
(`Ingress.LoadedRecords`, `Ingress.RawCIRep`). The public statement speaks of what the record at an address
declares (`IxVM.Consistency.ReadsIn`): the kernel reader's own conversion of the record's
expressions, in a context that keys every address by the role table.

This module goes from the first to the second, kind by kind, with no run of the kernel's
stream reader:

* the circuit converted the record's expressions, so the kernel reader converts them
  (`exprReader_read_ok`: every address resolves in the reading context, the run hashed every
  literal blob, and a `recur` the circuit accepted is one the reading resolves);
* so the record has a reading (`ReadsIn`), over any store that holds the record (and, for a
  block member, its block and projection record) and any blob lookup that answers the blobs
  the run hashed;
* and where the reading is well scoped (no loose bound variable, every level parameter
  declared), the heap constant represents an annotation of that reading (`StoredAs`,
  `Core.CIRep`), by the record-loading layer's own conversion theorems, instantiated at the
  reading context.

Well-scopedness is not a fact of the load: the circuit establishes it when it checks the
constant (`KernelCheck::validate_expr_well_scoped`, the first step of every arm of
`KernelCheck::check_const`). A reading is a function of the record, so the fact holds of every
later load of the same record.

The store is the run's one store of hashed records (`RunStore`): what the claim phase builds
(`Claim.WalkedClaim`). In it two byte strings the run hashed under one address are equal, so two
loads of an address read one record, and a per-load store's blobs and blocks are the run
store's.

Kinds: a standalone definition, theorem or opaque (`defn_reading`); an axiom (`axio_reading`);
an inductive type and a constructor through their projection records (`ind_reading`,
`ctor_reading`); a member of a definition block (`dprj_reading`); a recursor, standalone or a
block member, given the inductives heading its first motive and its major premise and its
rule count (`recrPayload_reading`, `recr_reading`, `rprj_reading`); a quotient record, given
that it matches the kernel's pin (`quot_reading`).
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-! ## Keys and constant addresses: the two layers agree -/

/-- The core's key of an address is the statement's. -/
theorem keyOf_eq (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    Core.keyOf t a = keyOf t a := rfl

/-- A block member's constant address is the address the circuit computes for its
projection record. -/
theorem memberAddr_eq_projAddr (B : _root_.Address) (i : Nat) (m : Ixon.MutConst) :
    memberAddr B i m = Core.projAddr (Core.Specs.Callees.memberProjInfo B i m) := by
  cases m <;> rfl

theorem memberAddr_defn (B : _root_.Address) (i : Nat) (d : Ixon.Definition) :
    memberAddr B i (.defn d) = Core.dprjAddr B i := rfl

theorem memberAddr_indc (B : _root_.Address) (i : Nat) (ind : Ixon.Inductive) :
    memberAddr B i (.indc ind) = Core.iprjAddr B i := rfl

theorem memberAddr_recr (B : _root_.Address) (i : Nat) (rc : Ixon.Recursor) :
    memberAddr B i (.recr rc) = Core.rprjAddr B i := rfl

theorem ctorAddr_eq_cprjAddr (B : _root_.Address) (i j : Nat) :
    ctorAddr B i j = Core.cprjAddr B i j := rfl

private theorem toUInt64_toNat {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- The `i`-th entry of the circuit's table of a block's member addresses is member `i`'s
constant address. -/
theorem blockRecurAddrs_get {B : _root_.Address} {ms : Array Ixon.MutConst} {i : Nat}
    {x : _root_.Address} (h : (Ingress.blockRecurAddrs B ms.toList)[i]? = some x) :
    ∃ m, ms[i]? = some m ∧ x = memberAddr B i m := by
  rw [Ingress.blockRecurAddrs_eq_mapIdx, List.getElem?_mapIdx] at h
  cases hm : ms.toList[i]? with
  | none =>
    rw [hm] at h
    cases h
  | some m =>
    rw [hm] at h
    have hx : Core.projAddr (Core.Specs.Callees.memberProjInfo B i m) = x := Option.some.inj h
    refine ⟨m, ?_, hx.symm.trans (memberAddr_eq_projAddr B i m).symm⟩
    rw [← Array.getElem?_toList]
    exact hm

/-- A `recur` the circuit accepted in a block is one the reading resolves. -/
theorem blockSelf_ok (t : Ix.Kernel.RoleTable) (B : _root_.Address) (ms : Array Ixon.MutConst) :
    ∀ i x, (Ingress.blockRecurAddrs B ms.toList)[i]? = some x →
      ∃ m k, blockSelf t B ms i = some m ∧ m = .ok k := by
  intro i x hx
  obtain ⟨m₀, hm₀, -⟩ := blockRecurAddrs_get hx
  refine ⟨.ok (keyOf t (memberAddr B i m₀)), keyOf t (memberAddr B i m₀), ?_, rfl⟩
  unfold blockSelf
  rw [hm₀]
  rfl

/-- The reading's `recur k` in a block is the key of the address the circuit's table holds
at `k`. -/
theorem blockSelf_key (t : Ix.Kernel.RoleTable) (B : _root_.Address) (ms : Array Ixon.MutConst) :
    ∀ i x m k, (Ingress.blockRecurAddrs B ms.toList)[i]? = some x → blockSelf t B ms i = some m →
      m = .ok k → k = Core.keyOf t x := by
  intro i x m k hx hs hm
  obtain ⟨m₀, hm₀, rfl⟩ := blockRecurAddrs_get hx
  unfold blockSelf at hs
  rw [hm₀] at hs
  have h2 : (Except.ok (keyOf t (memberAddr B i m₀)) :
      Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) = m := Option.some.inj hs
  rw [hm] at h2
  exact (Except.ok.inj h2).symm

/-- The reading context's key of an address is the core's key of it. -/
theorem readCtx_keyAt_inv {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    (blob : _root_.Address → Option ByteArray) :
    ∀ x k, (readCtx t blob).keyAt x = .ok k → k = Core.keyOf t x := by
  intro x k hk
  rw [readCtx_keyAt ht blob x] at hk
  exact (Except.ok.inj hk).symm

/-! ## The run's store -/

/-- **The one store of a run**: every record and blob is a byte string the run hashed, under
its address (`LoadedBy`); every stored record's decoded cache is the exact decoding of its
bytes; and every byte string the run hashed is stored as a blob under its address. The last
makes the hash injective on what the run hashed, so the collision alternative has already
been split off where such a store exists. The claim phase's store is one
(`RunStore.of_walkedClaim`). -/
structure RunStore (calls : List (Call F)) (E : Ixon.Env) : Prop where
  loaded : LoadedBy calls E
  decoded : ∀ a lc, E.consts.get? a = some lc →
    ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c
  blobs : ∀ bytes, Hashed calls bytes → E.blobs.get? (Address.blake3Pure bytes) = some bytes

/-- The claim phase's store is a run store. -/
theorem RunStore.of_walkedClaim {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {seeds : List _root_.Address} (hload : LoadedBy calls E₀)
    (hw : Claim.WalkedClaim calls t E₀ seeds) : RunStore calls E₀ := by
  obtain ⟨bAddr, -, -, hex, hbl, -, -⟩ := hw
  refine ⟨hload, fun a lc hget => ?_, hbl⟩
  obtain ⟨-, c, hc, -, hce⟩ := hex a lc hget
  exact ⟨c, hc, hce⟩

section Store

variable {calls : List (Call F)} {E : Ixon.Env}

/-- **Two byte strings the run hashed under one address are equal.** -/
theorem RunStore.hashed_inj (hS : RunStore calls E) {b₁ b₂ : ByteArray}
    (h₁ : Hashed calls b₁) (h₂ : Hashed calls b₂)
    (he : Address.blake3Pure b₁ = Address.blake3Pure b₂) : b₁ = b₂ := by
  have e₁ := hS.blobs b₁ h₁
  have e₂ := hS.blobs b₂ h₂
  rw [he] at e₁
  exact Option.some.inj (e₁.symm.trans e₂)

/-- A run store holds no blob and record with different bytes at one address. -/
theorem RunStore.no_internal_collision (hS : RunStore calls E) :
    ¬ Ingress.EnvInternalCollision E := by
  rintro ⟨x, d, lc, hb, hc, hne⟩
  obtain ⟨hh_c, ha_c⟩ := hS.loaded.1 x lc hc
  obtain ⟨hh_b, ha_b⟩ := hS.loaded.2 x d hb
  exact hne (hS.hashed_inj hh_b hh_c (ha_b.trans ha_c.symm))

/-- In a run store the exact decoding of the stored bytes is the decoded cache. -/
theorem RunStore.recordOf_eq_recordAt (hS : RunStore calls E) (a : _root_.Address) :
    recordOf E a = Ix.Cert.recordAt E a := by
  unfold recordOf Ix.Cert.recordAt
  cases hget : E.consts.get? a with
  | none => rfl
  | some lc =>
    obtain ⟨c, hc, hce⟩ := hS.decoded a lc hget
    show (Ixon.deConstantExact lc.rawBytes).toOption = lc.get?
    rw [hce, hc]
    rfl

theorem RunStore.recordOf_of_recordAt (hS : RunStore calls E) {a : _root_.Address}
    {c : Ixon.Constant} (h : Ix.Cert.recordAt E a = some c) : recordOf E a = some c := by
  rw [hS.recordOf_eq_recordAt]
  exact h

/-- **Two loads of one address read one record**: bytes the run hashed under an address the
store holds decode to the stored record. -/
theorem RunStore.record_eq (hS : RunStore calls E) {a : _root_.Address} {c c' : Ixon.Constant}
    {bytes : ByteArray} (hrec : Ix.Cert.recordAt E a = some c) (hh : Hashed calls bytes)
    (ha : Address.blake3Pure bytes = a) (hde : Ixon.deConstantExact bytes = .ok c') :
    c' = c := by
  unfold Ix.Cert.recordAt at hrec
  cases hget : E.consts.get? a with
  | none =>
    rw [hget] at hrec
    cases hrec
  | some lc =>
    rw [hget] at hrec
    obtain ⟨hh₀, ha₀⟩ := hS.loaded.1 a lc hget
    obtain ⟨c₀, hc₀, hce₀⟩ := hS.decoded a lc hget
    have hb : bytes = lc.rawBytes := hS.hashed_inj hh hh₀ (ha.trans ha₀.symm)
    rw [hb, hce₀] at hde
    have h1 : c₀ = c' := Except.ok.inj hde
    have h2 : lc.get? = some c := hrec
    rw [hc₀] at h2
    rw [← h1]
    exact Option.some.inj h2

/-- **The blobs a load hashed are the run store's**: a per-load store's blob table, read in
the run's store. -/
theorem RunStore.blob_of_table (hS : RunStore calls E) {cs : List (Call F)} {E_ld : Ixon.Env}
    {blobs : List (_root_.Address × ByteArray)} (hload : LoadedBy cs E_ld)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (hb : Ingress.BlobTableLoaded E_ld blobs) :
    ∀ x bs, (x, bs) ∈ blobs → E.blobs.get? x = some bs := by
  intro x bs hm
  rcases hb with hok | ⟨y, d, lc, hbl, hco, hne⟩
  · obtain ⟨hget, ha⟩ := hok x bs hm
    obtain ⟨hh, -⟩ := hload.2 x bs hget
    have hrun := hS.blobs bs (Core.hashed_mono hsub hh)
    rw [ha] at hrun
    exact hrun
  · obtain ⟨hh_c, ha_c⟩ := hload.1 y lc hco
    obtain ⟨hh_b, ha_b⟩ := hload.2 y d hbl
    exact absurd (hS.hashed_inj (Core.hashed_mono hsub hh_b) (Core.hashed_mono hsub hh_c)
      (ha_b.trans ha_c.symm)) hne

end Store

/-! ## A loaded projection record is the canonical one -/

/-- A loaded projection record has empty tables. -/
theorem proj_record_eq {c : Ixon.Constant} (htv : Ingress.ConstantTablesValid c)
    (hproj : Assembly.IsProjInfo c.info) : c = ⟨c.info, #[], #[], #[], #[]⟩ := by
  have h : c.sharing = #[] ∧ c.refs = #[] ∧ c.univs = #[] ∧ c.binders = #[] := by
    unfold Ingress.ConstantTablesValid at htv
    cases hi : c.info with
    | dPrj p => rw [hi] at htv; exact htv
    | iPrj p => rw [hi] at htv; exact htv
    | cPrj p => rw [hi] at htv; exact htv
    | rPrj p => rw [hi] at htv; exact htv
    | defn x => rw [hi] at hproj; exact False.elim hproj
    | axio x => rw [hi] at hproj; exact False.elim hproj
    | quot x => rw [hi] at hproj; exact False.elim hproj
    | recr x => rw [hi] at hproj; exact False.elim hproj
    | muts x => rw [hi] at hproj; exact False.elim hproj
  obtain ⟨info, sh, rf, un, bd⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h1' : sh = #[] := h1
  have h2' : rf = #[] := h2
  have h3' : un = #[] := h3
  have h4' : bd = #[] := h4
  subst h1' h2' h3' h4'
  rfl

/-- The bytes of a loaded projection record are its canonical serialization. -/
theorem proj_bytes_eq {bytes : ByteArray} {c : Ixon.Constant}
    (hde : Ixon.deConstantExact bytes = .ok c) (htv : Ingress.ConstantTablesValid c)
    (hproj : Assembly.IsProjInfo c.info) :
    bytes = Ixon.serConstant ⟨c.info, #[], #[], #[], #[]⟩ := by
  have hc := proj_record_eq htv hproj
  have hemp : Ix.Kernel.Reader.emptyTables c = true := by
    rw [hc]
    rfl
  have hb := (Assembly.deConstantExact_proj_eq_serConstant hde hemp hproj).1
  rw [← hc]
  exact hb

/-- **A loaded inductive projection record is the member's projection record, at the
member's constant address.** -/
theorem iprj_canonical {bytes : ByteArray} {c : Ixon.Constant} {p : Ixon.InductiveProj}
    (ind : Ixon.Inductive) (hde : Ixon.deConstantExact bytes = .ok c)
    (htv : Ingress.ConstantTablesValid c) (hinfo : c.info = .iPrj p) :
    c = memberProjection p.block p.idx.toNat (.indc ind) ∧
      Address.blake3Pure bytes = memberAddr p.block p.idx.toNat (.indc ind) := by
  have hproj : Assembly.IsProjInfo c.info := by rw [hinfo]; trivial
  have hc := proj_record_eq htv hproj
  have hb := proj_bytes_eq hde htv hproj
  have hu : p.idx.toNat.toUInt64 = p.idx := UInt64.ofNat_toNat
  have hmp : memberProjection p.block p.idx.toNat (.indc ind) = ⟨c.info, #[], #[], #[], #[]⟩ := by
    rw [hinfo]
    exact congrArg
      (fun x => (⟨.iPrj ⟨x, p.block⟩, #[], #[], #[], #[]⟩ : Ixon.Constant)) hu
  refine ⟨hc.trans hmp.symm, ?_⟩
  unfold memberAddr
  rw [hmp, ← hb]

/-- A loaded definition projection record is the member's projection record, at the member's
constant address. -/
theorem dprj_canonical {bytes : ByteArray} {c : Ixon.Constant} {p : Ixon.DefinitionProj}
    (d : Ixon.Definition) (hde : Ixon.deConstantExact bytes = .ok c)
    (htv : Ingress.ConstantTablesValid c) (hinfo : c.info = .dPrj p) :
    c = memberProjection p.block p.idx.toNat (.defn d) ∧
      Address.blake3Pure bytes = memberAddr p.block p.idx.toNat (.defn d) := by
  have hproj : Assembly.IsProjInfo c.info := by rw [hinfo]; trivial
  have hc := proj_record_eq htv hproj
  have hb := proj_bytes_eq hde htv hproj
  have hu : p.idx.toNat.toUInt64 = p.idx := UInt64.ofNat_toNat
  have hmp : memberProjection p.block p.idx.toNat (.defn d) = ⟨c.info, #[], #[], #[], #[]⟩ := by
    rw [hinfo]
    exact congrArg
      (fun x => (⟨.dPrj ⟨x, p.block⟩, #[], #[], #[], #[]⟩ : Ixon.Constant)) hu
  refine ⟨hc.trans hmp.symm, ?_⟩
  unfold memberAddr
  rw [hmp, ← hb]

/-- A loaded recursor projection record is the member's projection record, at the member's
constant address. -/
theorem rprj_canonical {bytes : ByteArray} {c : Ixon.Constant} {p : Ixon.RecursorProj}
    (rc : Ixon.Recursor) (hde : Ixon.deConstantExact bytes = .ok c)
    (htv : Ingress.ConstantTablesValid c) (hinfo : c.info = .rPrj p) :
    c = memberProjection p.block p.idx.toNat (.recr rc) ∧
      Address.blake3Pure bytes = memberAddr p.block p.idx.toNat (.recr rc) := by
  have hproj : Assembly.IsProjInfo c.info := by rw [hinfo]; trivial
  have hc := proj_record_eq htv hproj
  have hb := proj_bytes_eq hde htv hproj
  have hu : p.idx.toNat.toUInt64 = p.idx := UInt64.ofNat_toNat
  have hmp : memberProjection p.block p.idx.toNat (.recr rc) = ⟨c.info, #[], #[], #[], #[]⟩ := by
    rw [hinfo]
    exact congrArg
      (fun x => (⟨.rPrj ⟨x, p.block⟩, #[], #[], #[], #[]⟩ : Ixon.Constant)) hu
  refine ⟨hc.trans hmp.symm, ?_⟩
  unfold memberAddr
  rw [hmp, ← hb]

/-- A loaded constructor projection record is the constructor's projection record, at the
constructor's constant address. -/
theorem cprj_canonical {bytes : ByteArray} {c : Ixon.Constant} {p : Ixon.ConstructorProj}
    (hde : Ixon.deConstantExact bytes = .ok c) (htv : Ingress.ConstantTablesValid c)
    (hinfo : c.info = .cPrj p) :
    c = constructorProjection p.block p.idx.toNat p.cidx.toNat ∧
      Address.blake3Pure bytes = ctorAddr p.block p.idx.toNat p.cidx.toNat := by
  have hproj : Assembly.IsProjInfo c.info := by rw [hinfo]; trivial
  have hc := proj_record_eq htv hproj
  have hb := proj_bytes_eq hde htv hproj
  have hu : p.idx.toNat.toUInt64 = p.idx := UInt64.ofNat_toNat
  have hv : p.cidx.toNat.toUInt64 = p.cidx := UInt64.ofNat_toNat
  have hmp : constructorProjection p.block p.idx.toNat p.cidx.toNat =
      ⟨c.info, #[], #[], #[], #[]⟩ := by
    rw [hinfo]
    exact (congrArg
      (fun x => (⟨.cPrj ⟨x, p.cidx.toNat.toUInt64, p.block⟩, #[], #[], #[], #[]⟩ :
        Ixon.Constant)) hu).trans
      (congrArg (fun y => (⟨.cPrj ⟨p.idx, y, p.block⟩, #[], #[], #[], #[]⟩ : Ixon.Constant)) hv)
  refine ⟨hc.trans hmp.symm, ?_⟩
  unfold ctorAddr
  rw [hmp, ← hb]

/-! ## The circuit converted it, so the reader reads it -/

section Reading

variable {t : Ix.Kernel.RoleTable} {store : Ix.Kernel.Reader.Store}
  {blob : _root_.Address → Option ByteArray}

/-- **An expression the circuit converted is one the kernel reader converts in the reading
context**: every address resolves there, the blobs the load hashed are answered, and every
`recur` the circuit's table holds is one `self` resolves. -/
theorem exprReader_read_ok (ht : t.check = .ok ()) {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : Ingress.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (hself : ∀ i x, recurAddrs[i]? = some x → ∃ m k, self i = some m ∧ m = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs) :
    ∃ v : Ix.Kernel.Expr .anon, (exprReader t blob src param self).read e = .ok v :=
  Assembly.memberReader_read_ok_of_rawConvExpr (cx := readCtx t blob) (param := param)
    (self := self) raw hself hblob (fun _ _ x _ => ⟨keyOf t x, readCtx_keyAt ht blob x⟩)

/-! ### Definitions, theorems, opaques -/

/-- The constant a definition record declares, by its kind, under the reducibility hint
`hn` (`DefnShape`). -/
def defnConst (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint) :
    Ix.Kernel.ConstantInfo .anon :=
  match kind with
  | .defn => .defnInfo cv value hn
  | .thm => .thmInfo cv value
  | .opaq => .axiomInfo cv

theorem defnShape_defnConst (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint) :
    DefnShape kind cv value (defnConst kind cv value hn) := by
  cases kind with
  | defn => exact ⟨hn, rfl⟩
  | thm => exact rfl
  | opaq => exact rfl

/-- **A definition payload the circuit converted with no `recur` in scope**: its type and
value read, under every hint the payload declares the constant, and where the readings are
well scoped the heap value represents an annotation of it. -/
theorem defnPayload_reading (ht : t.check = .ok ()) {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {name : Ix.Kernel.Key .anon} {d : Ixon.Definition}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {v : SourceValue F}
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawDefnValRep src.refs.toList [] src.univs.toList src.sharing.toList blobs h d v) :
    ∃ ty₀ val₀ : Ix.Kernel.Expr .anon,
      (exprReader t blob src id self).read d.typ = .ok ty₀ ∧
      (exprReader t blob src id self).read d.value = .ok val₀ ∧
      (∀ hn, DefnReads (exprReader t blob src id self) name d
        (defnConst d.kind ⟨name, List.range d.lvls.toNat, ty₀⟩ val₀ hn)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        val₀.looseBVarsBounded 0 = true →
        val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        ∀ hn, ∃ ci, StoredAs ci (defnConst d.kind ⟨name, List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
          Core.CIRep (Core.keyOf t) h v ci) := by
  have raw0 := raw
  obtain ⟨-, tyPtr, valPtr, hint, -, rty, rval⟩ := raw0
  have hself : ∀ i x, ([] : List _root_.Address)[i]? = some x →
      ∃ m k, self i = some m ∧ m = .ok k := fun i x hx => by simp at hx
  obtain ⟨ty₀, hty⟩ := exprReader_read_ok ht (param := id) (self := self) rty hself hblob
  obtain ⟨val₀, hval⟩ := exprReader_read_ok ht (param := id) (self := self) rval hself hblob
  refine ⟨ty₀, val₀, hty, hval, fun hn => ⟨ty₀, val₀, hty, hval, defnShape_defnConst _ _ _ hn⟩,
    fun hty_lbb hty_def hval_lbb hval_def hn => ?_⟩
  have hselfk : ∀ i x m k, ([] : List _root_.Address)[i]? = some x → self i = some m →
      m = .ok k → k = Core.keyOf t x := fun i x m k hx => by simp at hx
  have hty' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  have hval' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ := by
    rw [Assembly.recParam_range]
    exact hval
  cases hk : d.kind with
  | defn =>
    exact raw.toCIRep_defn (name := name) hk (by simp) (by simp) (readCtx_keyAt_inv ht blob)
      hselfk hblob hn hty' hty_lbb hty_def hval' hval_lbb hval_def
  | thm =>
    exact raw.toCIRep_thm (name := name) hk (by simp) (by simp) (readCtx_keyAt_inv ht blob)
      hselfk hblob hty' hty_lbb hty_def hval' hval_lbb hval_def
  | opaq =>
    exact raw.toCIRep_opaq (name := name) hk (by simp) (by simp) (readCtx_keyAt_inv ht blob)
      hselfk hblob hty' hty_lbb hty_def

/-- **A standalone definition, theorem or opaque record the circuit loaded.** The store
holds the record at `a`, in Lean's logic. Then its type and value read; under every hint
`hn` the record declares the constant (`ReadsIn`); and where the readings are well scoped
(`KernelCheck::validate_expr_well_scoped`, in `KernelCheck::check_const`) the heap value
represents an annotation of it. -/
theorem defn_reading (ht : t.check = .ok ()) {a : _root_.Address} {c : Ixon.Constant}
    {d : Ixon.Definition} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {v : SourceValue F} (hstore : store a = some c) (hinfo : c.info = .defn d)
    (hlogic : InLogic c) (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawDefnValRep c.refs.toList (Ingress.defnRecurAddrs d a) c.univs.toList
      c.sharing.toList blobs h d v) :
    Ingress.RawDefnValRep c.refs.toList [] c.univs.toList c.sharing.toList blobs h d v ∧
    ∃ ty₀ val₀ : Ix.Kernel.Expr .anon,
      (exprReader t blob c id (soloSelf t a)).read d.typ = .ok ty₀ ∧
      (exprReader t blob c id (soloSelf t a)).read d.value = .ok val₀ ∧
      (∀ hn, ReadsIn t store blob a
        (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        val₀.looseBVarsBounded 0 = true →
        val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        ∀ hn, ∃ ci,
          StoredAs ci (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
          Core.CIRep (Core.keyOf t) h v ci) := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  have hrec : Ingress.defnRecurAddrs d a = [] := by
    have hf := (Ingress.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [Ingress.defnRecurAddrs, hf]
  rw [hrec] at raw
  obtain ⟨ty₀, val₀, hty, hval, hreads, hrep⟩ :=
    defnPayload_reading (blob := blob) (self := soloSelf t a) (name := keyOf t a) ht hblob raw
  exact ⟨raw, ty₀, val₀, hty, hval,
    fun hn => ReadsIn.of_defn hstore hinfo hlogic (hreads hn), hrep⟩

/-- A definition member's reading, at its projection record's address. -/
theorem readsIn_of_dprj {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i : Nat} {d : Ixon.Definition} {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hi : i < UInt64.size) (hs : store B = some cb) (hinfo : cb.info = .muts ms)
    (hm : ms[i]? = some (.defn d)) (hl : InLogic cb)
    (hp : store (memberAddr B i (.defn d)) = some (memberProjection B i (.defn d)))
    (hr : DefnReads (exprReader t blob cb id (blockSelf t B ms))
      (keyOf t (memberAddr B i (.defn d))) d ci₀) :
    ReadsIn t store blob (memberAddr B i (.defn d)) ci₀ := by
  unfold ReadsIn
  refine ⟨memberProjection B i (.defn d), hp, ?_⟩
  show ∃ cb' ms' d',
    MemberAt store (memberAddr B i (.defn d)) (memberProjection B i (.defn d)) B cb' ms'
      i.toUInt64.toNat (.defn d') ∧
    DefnReads (exprReader t blob cb' id (blockSelf t B ms'))
      (keyOf t (memberAddr B i (.defn d))) d' ci₀
  rw [toUInt64_toNat hi]
  exact ⟨cb, ms, d,
    And.intro hs (And.intro hinfo (And.intro hm (And.intro rfl (And.intro rfl hl)))), hr⟩

/-- **A member of a definition block the circuit loaded through its projection record.** The
store holds the block at `B`, in Lean's logic, and the member's projection record. -/
theorem dprj_reading (ht : t.check = .ok ()) {B : _root_.Address} {i : Nat}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {d : Ixon.Definition}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {v : SourceValue F}
    (hi : i < UInt64.size) (hblock : store B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i]? = some (.defn d)) (hlogic : InLogic cb)
    (hproj : store (memberAddr B i (.defn d)) = some (memberProjection B i (.defn d)))
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawDefnValRep cb.refs.toList (Ingress.defnMemberRecurAddrs d B ms.toList)
      cb.univs.toList cb.sharing.toList blobs h d v) :
    Ingress.RawDefnValRep cb.refs.toList [] cb.univs.toList cb.sharing.toList blobs h d v ∧
    ∃ ty₀ val₀ : Ix.Kernel.Expr .anon,
      (exprReader t blob cb id (blockSelf t B ms)).read d.typ = .ok ty₀ ∧
      (exprReader t blob cb id (blockSelf t B ms)).read d.value = .ok val₀ ∧
      (∀ hn, ReadsIn t store blob (memberAddr B i (.defn d))
        (defnConst d.kind
          ⟨keyOf t (memberAddr B i (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        val₀.looseBVarsBounded 0 = true →
        val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        ∀ hn, ∃ ci,
          StoredAs ci (defnConst d.kind
            ⟨keyOf t (memberAddr B i (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
          Core.CIRep (Core.keyOf t) h v ci) := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hmuts] at hl
    have hmem' : Ixon.MutConst.defn d ∈ ms.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
    exact hl (.defn d) hmem'
  have hrec : Ingress.defnMemberRecurAddrs d B ms.toList = [] := by
    have hf := (Ingress.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [Ingress.defnMemberRecurAddrs, hf]
  rw [hrec] at raw
  obtain ⟨ty₀, val₀, hty, hval, hreads, hrep⟩ :=
    defnPayload_reading (blob := blob) (self := blockSelf t B ms)
      (name := keyOf t (memberAddr B i (.defn d))) ht hblob raw
  exact ⟨raw, ty₀, val₀, hty, hval,
    fun hn => readsIn_of_dprj hi hblock hmuts hmem hlogic hproj (hreads hn), hrep⟩

/-! ### Axioms -/

/-- An axiom at an address no inert role is bound to has a key that is not inert. -/
theorem inertKey_false_of_not_inertAt (ht : t.check = .ok ()) {a : _root_.Address}
    (h : ¬ InertAt t a) : inertKey (keyOf t a) = false := by
  rcases keyOf_cases t a with ⟨hk, -⟩ | ⟨r, hr, hk⟩
  · rw [hk]
    rfl
  · rw [hk]
    cases hin : r.inert with
    | false => exact hin
    | true =>
      exact absurd ⟨r, hin, Ix.Cert.ReadingKeys.addressOf_of_bound ht hr⟩ h

/-- **An axiom record the circuit loaded.** The store holds the record at `a`, in Lean's
logic, and `a` is not the address of an inert role. -/
theorem axio_reading (ht : t.check = .ok ()) {a : _root_.Address} {c : Ixon.Constant}
    {ax : Ixon.Axiom} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {v : SourceValue F} (hstore : store a = some c) (hinfo : c.info = .axio ax)
    (hlogic : InLogic c) (hinert : inertKey (keyOf t a) = false)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawAxioValRep c.refs.toList [] c.univs.toList c.sharing.toList blobs h ax v) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t blob c id (fun _ => none)).read ax.typ = .ok ty₀ ∧
      ReadsIn t store blob a (.axiomInfo ⟨keyOf t a, List.range ax.lvls.toNat, ty₀⟩) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ax.lvls.toNat) = true →
        ∃ ci, StoredAs ci (.axiomInfo ⟨keyOf t a, List.range ax.lvls.toNat, ty₀⟩) ∧
          Core.CIRep (Core.keyOf t) h v ci) := by
  have raw0 := raw
  obtain ⟨-, tyPtr, -, rty⟩ := raw0
  have hself : ∀ i x, ([] : List _root_.Address)[i]? = some x →
      ∃ m k, (fun _ => none : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))) i =
        some m ∧ m = .ok k := fun i x hx => by simp at hx
  obtain ⟨ty₀, hty⟩ := exprReader_read_ok ht (param := id) (self := fun _ => none) rty hself hblob
  refine ⟨ty₀, hty, ReadsIn.of_axio hstore hinfo hlogic ⟨hinert, ty₀, hty, rfl⟩,
    fun hty_lbb hty_def => ?_⟩
  have hty' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) c
      (Ix.Kernel.Reader.recParam (List.range ax.lvls.toNat)) (fun _ => none)).read ax.typ =
      .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  exact raw.toCIRep (name := Core.keyOf t a) (by simp) (by simp) (readCtx_keyAt_inv ht blob)
    (fun _ _ _ _ hx => by simp at hx) hblob hty' hty_lbb hty_def

/-! ### Inductive types and constructors -/

/-- **An inductive type the circuit loaded**, member `i` of the block at `B`. The store holds
the block, in Lean's logic, and the member's projection record. -/
theorem ind_reading (ht : t.check = .ok ()) {B : _root_.Address} {i : Nat}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {v : SourceValue F}
    (hi : i < UInt64.size) (hblock : store B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i]? = some (.indc ind)) (hlogic : InLogic cb)
    (hproj : store (memberAddr B i (.indc ind)) = some (memberProjection B i (.indc ind)))
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawInductValRep cb.refs.toList (Ingress.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h ind B i v) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t blob cb id (blockSelf t B ms)).read ind.typ = .ok ty₀ ∧
      (∀ caps, ReadsIn t store blob (memberAddr B i (.indc ind))
        (.indInfo ⟨keyOf t (memberAddr B i (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true →
        ∀ caps, ∃ ci,
          StoredAs ci (.indInfo
            ⟨keyOf t (memberAddr B i (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps) ∧
          Decl.CIRepExact (Core.keyOf t) h v ci) := by
  have raw0 := raw
  obtain ⟨-, -, -, -, -, tyPtr, blkPtr, b, -, -, -, rty⟩ := raw0
  obtain ⟨ty₀, hty⟩ := exprReader_read_ok ht (param := id) (self := blockSelf t B ms) rty
    (blockSelf_ok t B ms) hblob
  refine ⟨ty₀, hty,
    fun caps => ReadsIn.of_ind hi hblock hmuts hmem hlogic hproj ⟨ty₀, caps, hty, rfl⟩,
    fun hty_lbb hty_def caps => ?_⟩
  have hty' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) cb
      (Ix.Kernel.Reader.recParam (List.range ind.lvls.toNat)) (blockSelf t B ms)).read ind.typ =
      .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  exact raw.toCIRepExact (name := Core.keyOf t (memberAddr B i (.indc ind)))
    (congrArg (Core.keyOf t) (memberAddr_indc B i ind)) (by simp) (by simp)
    (readCtx_keyAt_inv ht blob) (blockSelf_key t B ms) hblob caps hty' hty_lbb hty_def

/-- **A constructor the circuit loaded**, constructor `j` of member `i` of the block at `B`.
The store holds the block, in Lean's logic, and the constructor's projection record; the
constructor's stored index is its position (the circuit asserts it when it checks the
inductive: `KernelCheck::check_inductive_shape_ctors`, `check_modeled_ctors`). -/
theorem ctor_reading (ht : t.check = .ok ()) {B : _root_.Address} {i j : Nat}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    {ct : Ixon.Constructor} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {v : SourceValue F} (hi : i < UInt64.size) (hj : j < UInt64.size)
    (hblock : store B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i]? = some (.indc ind)) (hct : ind.ctors[j]? = some ct)
    (hcidx : ct.cidx.toNat = j) (hlogic : InLogic cb)
    (hproj : store (ctorAddr B i j) = some (constructorProjection B i j))
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawCtorValRep cb.refs.toList (Ingress.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h ct B i v) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t blob cb id (blockSelf t B ms)).read ct.typ = .ok ty₀ ∧
      ReadsIn t store blob (ctorAddr B i j)
        (.ctorInfo ⟨keyOf t (ctorAddr B i j), List.range ct.lvls.toNat, ty₀⟩ ct.params.toNat
          ct.fields.toNat) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true →
        ∃ ci,
          StoredAs ci (.ctorInfo ⟨keyOf t (ctorAddr B i j), List.range ct.lvls.toNat, ty₀⟩
            ct.params.toNat ct.fields.toNat) ∧
          Decl.CIRepExact (Core.keyOf t) h v ci) := by
  have raw0 := raw
  obtain ⟨-, -, -, -, -, tyPtr, blkPtr, b, -, -, -, rty⟩ := raw0
  obtain ⟨ty₀, hty⟩ := exprReader_read_ok ht (param := id) (self := blockSelf t B ms) rty
    (blockSelf_ok t B ms) hblob
  refine ⟨ty₀, hty,
    ReadsIn.of_ctor hi hj hblock hmuts hmem hct hcidx hlogic hproj ⟨ty₀, hty, rfl⟩,
    fun hty_lbb hty_def => ?_⟩
  have hty' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) cb
      (Ix.Kernel.Reader.recParam (List.range ct.lvls.toNat)) (blockSelf t B ms)).read ct.typ =
      .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  have hname : Core.keyOf t (ctorAddr B i j) =
      Core.keyOf t (Core.cprjAddr B i ct.cidx.toNat) := by
    rw [hcidx]
    exact congrArg (Core.keyOf t) (ctorAddr_eq_cprjAddr B i j)
  exact raw.toCIRepExact (name := Core.keyOf t (ctorAddr B i j)) hname (by simp) (by simp)
    (readCtx_keyAt_inv ht blob) (blockSelf_key t B ms) hblob hty' hty_lbb hty_def

/-! ### Recursors -/

/-- The rules of a recursor the circuit converted read, one for one: rule `k` (from `j`)
names constructor `k` of member `im` of the block at `Bm`. -/
theorem rules_reading (ht : t.check = .ok ()) {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} (hself : ∀ i x, recurAddrs[i]? = some x → ∃ m k, self i = some m ∧ m = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs) (Bm : _root_.Address) (im : Nat)
    {j : Nat} {rus : List Ixon.RecursorRule} {p : SourceValue F}
    (raw : Ingress.RawRulesRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h j rus p) :
    ∃ rules : List (Ix.Kernel.RecRule .anon),
      List.Forall₂ (RuleReads t (exprReader t blob src param self) Bm im) (rus.zipIdx j) rules ∧
      List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
        (exprReader t blob src param self).read ru.rhs = .ok rl₀.rhs) rus rules := by
  induction raw with
  | nil cell => exact ⟨[], .nil, .nil⟩
  | @cons j addr v rest ru rus cell hr rs ih =>
    obtain ⟨rules, h1, h2⟩ := ih
    obtain ⟨-, rhsPtr, -, rrhs⟩ := hr
    obtain ⟨rhs, hrhs⟩ := exprReader_read_ok ht (param := param) (self := self) rrhs hself hblob
    refine ⟨Ix.Kernel.RecRule.mk (keyOf t (ctorAddr Bm im j)) ru.fields.toNat 0 .inert rhs
      false false false :: rules, ?_, ?_⟩
    · show List.Forall₂ (RuleReads t (exprReader t blob src param self) Bm im)
        ((ru, j) :: rus.zipIdx (j + 1)) _
      exact .cons ⟨rhs, hrhs, rfl⟩ h1
    · exact .cons ⟨rfl, hrhs⟩ h2

/-- The level parameters a recursor record declares, given the inductive heading its first
motive: that inductive's, behind one more for a large eliminator. -/
def recPs (rc : Ixon.Recursor) (ind : Ixon.Inductive) : List Ix.Kernel.LevelParam :=
  Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
    (List.range ind.lvls.toNat)

/-- A recursor with its family inductive's level count, or one more, declares as many level
parameters as its record counts. -/
theorem recPs_length {rc : Ixon.Recursor} {ind : Ixon.Inductive}
    (hl : rc.lvls.toNat = ind.lvls.toNat ∨ rc.lvls.toNat = ind.lvls.toNat + 1) :
    (recPs rc ind).length = rc.lvls.toNat := by
  rcases hl with h | h <;> simp [recPs, Ix.Kernel.Reader.recLps, h]

/-- Those level parameters are the positions, in some order. -/
theorem recPs_perm {rc : Ixon.Recursor} {ind : Ixon.Inductive}
    (hl : rc.lvls.toNat = ind.lvls.toNat ∨ rc.lvls.toNat = ind.lvls.toNat + 1) :
    (recPs rc ind).Perm (List.range (recPs rc ind).length) := by
  rcases hl with h | h
  · have hps : recPs rc ind = List.range ind.lvls.toNat := by
      simp [recPs, Ix.Kernel.Reader.recLps, h]
    rw [hps]
    simp
  · have hps : recPs rc ind = ind.lvls.toNat :: List.range ind.lvls.toNat := by
      simp [recPs, Ix.Kernel.Reader.recLps, h]
    rw [hps, List.length_cons, List.length_range, List.range_succ]
    exact (List.perm_append_singleton _ _).symm

/-- **A recursor payload the circuit converted.** Its type reads with positional level
parameters (`tyP`). Given the inductives whose keys head its first motive's last binder
domain and its major premise's domain on `tyP` (`familyKey`, `majorKey`, `IndKeyAt`: the
circuit finds both by the same plain walk, `KernelModeled::rec_family_block` and
`KernelCheck::rec_to_parent_addr`, and loads both), and that it has one rule for each
constructor of the major premise's inductive, the payload declares a recursor (`RecReads`):
its level parameters are `recPs`, and its type and rules read under them. -/
theorem recrPayload_reading (ht : t.check = .ok ()) {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} (name : Ix.Kernel.Key .anon) {rc : Ixon.Recursor}
    {blkAddr : _root_.Address} {recIdx : Nat} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {v : SourceValue F}
    (hself : ∀ i x, recurAddrs[i]? = some x → ∃ m k, self i = some m ∧ m = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawRecrValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList
      blobs h rc blkAddr recIdx v) :
    ∃ tyP : Ix.Kernel.Expr .anon,
      (exprReader t blob src id self).read rc.typ = .ok tyP ∧
      ∀ (kF kM : Ix.Kernel.Key .anon) (B Bm : _root_.Address) (i im : Nat)
        (ind indM : Ixon.Inductive),
        familyKey rc tyP = some kF → IndKeyAt t store kF B i ind →
        majorKey rc tyP = some kM → IndKeyAt t store kM Bm im indM →
        rc.rules.size = indM.ctors.size →
        ∃ (ty₀ : Ix.Kernel.Expr .anon) (rules₀ : List (Ix.Kernel.RecRule .anon)),
          RecReads t store blob src self name rc
            (.recInfo ⟨name, recPs rc ind, ty₀⟩
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀) ∧
          (exprReader t blob src (Ix.Kernel.Reader.recParam (recPs rc ind)) self).read rc.typ =
            .ok ty₀ ∧
          List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
            (exprReader t blob src (Ix.Kernel.Reader.recParam (recPs rc ind)) self).read ru.rhs =
              .ok rl₀.rhs) rc.rules.toList rules₀ := by
  obtain ⟨-, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, b, -, -, -, rty, rrules⟩ := raw
  have hself0 : ∀ i x, ([] : List _root_.Address)[i]? = some x →
      ∃ m k, self i = some m ∧ m = .ok k := fun i x hx => by simp at hx
  obtain ⟨tyP, htyP⟩ := exprReader_read_ok ht (param := id) (self := self) rty hself0 hblob
  refine ⟨tyP, htyP, ?_⟩
  intro kF kM B Bm i im ind indM hF hIF hM hIM hcount
  obtain ⟨ty₀, hty₀⟩ := exprReader_read_ok ht
    (param := Ix.Kernel.Reader.recParam (recPs rc ind)) (self := self) rty hself0 hblob
  obtain ⟨rules₀, hr1, hr2⟩ := rules_reading ht
    (param := Ix.Kernel.Reader.recParam (recPs rc ind)) hself hblob Bm im rrules
  exact ⟨ty₀, rules₀,
    ⟨tyP, ty₀, kF, kM, B, Bm, i, im, ind, indM, recPs rc ind, rules₀, htyP, hF, hIF, hM, hIM,
      rfl, hty₀, hcount, hr1, rfl⟩, hty₀, hr2⟩

/-- **The heap value of a recursor the circuit converted represents an annotation of its
reading**, where the reading's level parameters are as many as the record counts, in some
order of the positions, the readings are well scoped, and a recursor that declares K has one
rule. The name is the key of the record's own address or of the member's projection record,
the two forms the core reads. -/
theorem recrPayload_rep (ht : t.check = .ok ()) {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {name : Ix.Kernel.Key .anon} {rc : Ixon.Recursor}
    {blkAddr : _root_.Address} {recIdx : Nat} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {v : SourceValue F} {ps : List Ix.Kernel.LevelParam}
    {ty₀ : Ix.Kernel.Expr .anon} {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hname : name = Core.keyOf t blkAddr ∨ name = Core.keyOf t (Core.rprjAddr blkAddr recIdx))
    (hlen : ps.length = rc.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawRecrValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList
      blobs h rc blkAddr recIdx v)
    (hty : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1) :
    ∃ ci, StoredAs ci (.recInfo ⟨name, ps, ty₀⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀) ∧
      Core.CIRep (Core.keyOf t) h v ci :=
  raw.toCIRep (cx := readCtx t blob) hname hlen hperm (readCtx_keyAt_inv ht blob) hselfk hblob
    hty hty_lbb hty_def hrules hk

/-- `recur 0` in a standalone record is the record's own key, which the reading resolves. -/
theorem soloSelf_ok (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    ∀ i x, ([a] : List _root_.Address)[i]? = some x →
      ∃ m k, soloSelf t a i = some m ∧ m = .ok k := by
  intro i x hx
  cases i with
  | zero => exact ⟨.ok (keyOf t a), keyOf t a, rfl, rfl⟩
  | succ n => simp at hx

theorem soloSelf_key (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    ∀ i x m k, ([a] : List _root_.Address)[i]? = some x → soloSelf t a i = some m →
      m = .ok k → k = Core.keyOf t x := by
  intro i x m k hx hs hm
  cases i with
  | zero =>
    have hxa : a = x := by simpa using hx
    have h2 : (Except.ok (keyOf t a) : Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) = m :=
      Option.some.inj hs
    rw [hm] at h2
    rw [← hxa]
    exact (Except.ok.inj h2).symm
  | succ n => simp at hx

/-- **A standalone recursor record the circuit loaded.** The store holds the record at `a`,
in Lean's logic. Given the family and major inductives and the rule count
(`recrPayload_reading`), the record declares a recursor under its own key. -/
theorem recr_reading (ht : t.check = .ok ()) {a : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {v : SourceValue F} (hstore : store a = some c) (hinfo : c.info = .recr rc)
    (hlogic : InLogic c) (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawRecrValRep c.refs.toList [a] c.univs.toList c.sharing.toList blobs h rc a 0 v) :
    ∃ tyP : Ix.Kernel.Expr .anon,
      (exprReader t blob c id (soloSelf t a)).read rc.typ = .ok tyP ∧
      ∀ (kF kM : Ix.Kernel.Key .anon) (B Bm : _root_.Address) (i im : Nat)
        (ind indM : Ixon.Inductive),
        familyKey rc tyP = some kF → IndKeyAt t store kF B i ind →
        majorKey rc tyP = some kM → IndKeyAt t store kM Bm im indM →
        rc.rules.size = indM.ctors.size →
        ∃ (ty₀ : Ix.Kernel.Expr .anon) (rules₀ : List (Ix.Kernel.RecRule .anon)),
          ReadsIn t store blob a
            (.recInfo ⟨keyOf t a, recPs rc ind, ty₀⟩
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀) ∧
          (exprReader t blob c (Ix.Kernel.Reader.recParam (recPs rc ind))
            (soloSelf t a)).read rc.typ = .ok ty₀ ∧
          List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
            (exprReader t blob c (Ix.Kernel.Reader.recParam (recPs rc ind))
              (soloSelf t a)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules₀ := by
  obtain ⟨tyP, htyP, hrest⟩ :=
    recrPayload_reading (store := store) (blob := blob) (self := soloSelf t a) ht (keyOf t a)
      (soloSelf_ok t a) hblob raw
  refine ⟨tyP, htyP, ?_⟩
  intro kF kM B Bm i im ind indM hF hIF hM hIM hcount
  obtain ⟨ty₀, rules₀, hrr, hty₀, hr2⟩ := hrest kF kM B Bm i im ind indM hF hIF hM hIM hcount
  refine ⟨ty₀, rules₀, ?_, hty₀, hr2⟩
  unfold ReadsIn
  refine ⟨c, hstore, ?_⟩
  rw [hinfo]
  exact And.intro hlogic hrr

/-- **A recursor member of a block the circuit loaded through its projection record.** The
store holds the block at `B`, in Lean's logic, and the member's projection record. -/
theorem rprj_reading (ht : t.check = .ok ()) {B : _root_.Address} {i₀ : Nat}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {rc : Ixon.Recursor}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {v : SourceValue F}
    (hi : i₀ < UInt64.size) (hblock : store B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i₀]? = some (.recr rc)) (hlogic : InLogic cb)
    (hproj : store (memberAddr B i₀ (.recr rc)) = some (memberProjection B i₀ (.recr rc)))
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawRecrValRep cb.refs.toList (Ingress.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h rc B i₀ v) :
    ∃ tyP : Ix.Kernel.Expr .anon,
      (exprReader t blob cb id (blockSelf t B ms)).read rc.typ = .ok tyP ∧
      ∀ (kF kM : Ix.Kernel.Key .anon) (Bf Bm : _root_.Address) (i im : Nat)
        (ind indM : Ixon.Inductive),
        familyKey rc tyP = some kF → IndKeyAt t store kF Bf i ind →
        majorKey rc tyP = some kM → IndKeyAt t store kM Bm im indM →
        rc.rules.size = indM.ctors.size →
        ∃ (ty₀ : Ix.Kernel.Expr .anon) (rules₀ : List (Ix.Kernel.RecRule .anon)),
          ReadsIn t store blob (memberAddr B i₀ (.recr rc))
            (.recInfo ⟨keyOf t (memberAddr B i₀ (.recr rc)), recPs rc ind, ty₀⟩
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀) ∧
          (exprReader t blob cb (Ix.Kernel.Reader.recParam (recPs rc ind))
            (blockSelf t B ms)).read rc.typ = .ok ty₀ ∧
          List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
            (exprReader t blob cb (Ix.Kernel.Reader.recParam (recPs rc ind))
              (blockSelf t B ms)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules₀ := by
  obtain ⟨tyP, htyP, hrest⟩ :=
    recrPayload_reading (store := store) (blob := blob) (self := blockSelf t B ms) ht
      (keyOf t (memberAddr B i₀ (.recr rc))) (blockSelf_ok t B ms) hblob raw
  refine ⟨tyP, htyP, ?_⟩
  intro kF kM Bf Bm i im ind indM hF hIF hM hIM hcount
  obtain ⟨ty₀, rules₀, hrr, hty₀, hr2⟩ := hrest kF kM Bf Bm i im ind indM hF hIF hM hIM hcount
  refine ⟨ty₀, rules₀, ?_, hty₀, hr2⟩
  unfold ReadsIn
  refine ⟨memberProjection B i₀ (.recr rc), hproj, ?_⟩
  show ∃ cb' ms' rc',
    MemberAt store (memberAddr B i₀ (.recr rc)) (memberProjection B i₀ (.recr rc)) B cb' ms'
      i₀.toUInt64.toNat (.recr rc') ∧
    RecReads t store blob cb' (blockSelf t B ms') (keyOf t (memberAddr B i₀ (.recr rc))) rc' _
  rw [toUInt64_toNat hi]
  exact ⟨cb, ms, rc,
    And.intro hblock (And.intro hmuts (And.intro hmem (And.intro rfl (And.intro rfl hlogic)))),
    hrr⟩

/-! ### Quotient records -/

/-- **A quotient record the circuit loaded.** Its type reads. Where the reading matches the
kernel's pinned quotient constant of the record's kind (`Ix.Kernel.quotPinHit`), the record
declares that pin. Nothing the circuit checks on the record gives the match: it holds because
the table binds the quotient roles at the committed prelude records. -/
theorem quot_reading (ht : t.check = .ok ()) {a : _root_.Address} {c : Ixon.Constant}
    {q : Ixon.Quotient} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {v : SourceValue F} (hstore : store a = some c) (hinfo : c.info = .quot q)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : Ingress.RawQuotValRep c.refs.toList [] c.univs.toList c.sharing.toList blobs h q v) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t blob c id (fun _ => none)).read q.typ = .ok ty₀ ∧
      ∀ ci₀ : Ix.Kernel.ConstantInfo .anon,
        Ix.Kernel.quotPinHit (quotSlot q.kind)
          (⟨keyOf t a, List.range q.lvls.toNat, ty₀⟩ : Ix.Kernel.ConstantVal .anon) = true →
        (Ix.Kernel.BasisKind.quotK.declsA : List (Ix.Kernel.ConstantInfo .anon))[
          (quotSlot q.kind).slot]? = some ci₀ →
        ReadsIn t store blob a ci₀ := by
  obtain ⟨-, tyPtr, -, rty⟩ := raw
  have hself : ∀ i x, ([] : List _root_.Address)[i]? = some x →
      ∃ m k, (fun _ => none : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))) i =
        some m ∧ m = .ok k := fun i x hx => by simp at hx
  obtain ⟨ty₀, hty⟩ := exprReader_read_ok ht (param := id) (self := fun _ => none) rty hself hblob
  refine ⟨ty₀, hty, fun ci₀ hhit hslot => ?_⟩
  unfold ReadsIn
  refine ⟨c, hstore, ?_⟩
  rw [hinfo]
  exact ⟨ty₀, hty, hhit, hslot⟩

end Reading

/-! ## Reducibility hints

A hint enters the representation of a loaded constant in one place, the `Defn` case, and is
constrained nowhere: the heap cell's hint field (what the prover supplied for this load) and
the kernel constant's hint are both free there. So a loaded definition represents the
kernel definition under every hint, and no fact about a later load of the record depends on
the hint either load was given. -/

/-- **A loaded definition's representation does not read the kernel hint.** -/
theorem ciRep_defn_hint {κ : _root_.Address → Core.KKey} {h : Heap F} {v : SourceValue F}
    {cv : Ix.Kernel.ConstantVal .anon} {V : Ix.Kernel.Expr .anon}
    {hn : Ix.Kernel.ReducibilityHint} (hn' : Ix.Kernel.ReducibilityHint)
    (r : Core.CIRep κ h v (.defnInfo cv V hn)) : Core.CIRep κ h v (.defnInfo cv V hn') := by
  cases r with
  | defn hv hV => exact .defn hv hV
  | quot hv hk =>
    rcases hk with ⟨-, _, _, h0⟩ | ⟨-, _, _, _, h0⟩ | ⟨-, _, _, _, _, h0⟩ |
      ⟨-, _, _, _, _, h0⟩ <;> cases h0

/-- The pointer form of `ciRep_defn_hint`. -/
theorem ciPtrRep_defn_hint {κ : _root_.Address → Core.KKey} {h : Heap F} {p : SourceValue F}
    {cv : Ix.Kernel.ConstantVal .anon} {V : Ix.Kernel.Expr .anon}
    {hn : Ix.Kernel.ReducibilityHint} (hn' : Ix.Kernel.ReducibilityHint)
    (r : Core.CIPtrRep κ h p (.defnInfo cv V hn)) : Core.CIPtrRep κ h p (.defnInfo cv V hn') := by
  obtain ⟨v, hl, hr⟩ := r
  exact ⟨v, hl, ciRep_defn_hint hn' hr⟩

/-- A stored definition keeps the declared hint: the public relation compares it. -/
theorem storedAs_defn_hint {ci : Ix.Kernel.ConstantInfo .anon}
    {cv₀ : Ix.Kernel.ConstantVal .anon} {v₀ : Ix.Kernel.Expr .anon}
    {hn : Ix.Kernel.ReducibilityHint} (h : StoredAs ci (.defnInfo cv₀ v₀ hn)) :
    ∃ cv v, ci = .defnInfo cv v hn ∧ ValStored cv cv₀ ∧ Annotates v v₀ := by
  obtain ⟨hv, hm⟩ := h
  cases ci with
  | defnInfo cv v h' =>
    obtain ⟨hann, hh⟩ := hm
    subst hh
    exact ⟨cv, v, rfl, hv, hann⟩
  | axiomInfo _ => exact False.elim hm
  | thmInfo _ _ => exact False.elim hm
  | indInfo _ _ => exact False.elim hm
  | ctorInfo _ _ _ => exact False.elim hm
  | recInfo _ _ _ _ => exact False.elim hm
  | projInfo _ => exact False.elim hm

/-! ## From the record layer's evidence for a load

The record-loading layer's conclusion for a `get_ci` at `a` (`Ingress.LoadedRecords` over the load's own
store `E_ld`, with the bytes it hashed), read against the run's store `E`. The record at `a`
(and, for a projection record, its block) is one the store holds: the claim walk gives that
for every address it checks. -/

section Loaded

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E : Ixon.Env}

/-- **A load of `a` decodes the record the run's store holds at `a`.** -/
theorem loadedRecords_record (hS : RunStore calls E) {cs_ld : List (Call F)} {E_ld : Ixon.Env}
    {h : Heap F} {ptr : SourceValue F} {bytes : ByteArray} {a : _root_.Address}
    {c : Ixon.Constant} (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) (hh : Hashed cs_ld bytes)
    (ha : Address.blake3Pure bytes = a) (hl : Ingress.LoadedRecords E_ld h ptr bytes)
    (hrec : Ix.Cert.recordAt E a = some c) :
    Ixon.deConstantExact bytes = .ok c ∧ Ingress.ConstantTablesValid c ∧
      Ingress.RawCIPtrRep E_ld h ptr a c := by
  obtain ⟨c', hex, -, htv, hptr⟩ := hl
  have hc : c' = c := hS.record_eq hrec (Core.hashed_mono hsub hh) ha hex
  subst hc
  rw [ha] at hptr
  exact ⟨hex, htv, hptr⟩

/-- **A loaded standalone definition, theorem or opaque**: the record at `a` has a reading
under every hint, and where the reading is well scoped the pointer represents an annotation
of it, under every hint. The readings `ty₀`, `val₀` are the kernel reader's conversions in
the reading context, so they are the same for every load of `a`. -/
theorem loadedRecords_defn_reads (ht : t.check = .ok ()) (hS : RunStore calls E)
    {cs_ld : List (Call F)} {E_ld : Ixon.Env} {h : Heap F} {ptr : SourceValue F}
    {bytes : ByteArray} {a : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hload : LoadedBy cs_ld E_ld) (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) (hh : Hashed cs_ld bytes)
    (ha : Address.blake3Pure bytes = a) (hl : Ingress.LoadedRecords E_ld h ptr bytes)
    (hrec : Ix.Cert.recordAt E a = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c) :
    ∃ ty₀ val₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.typ = .ok ty₀ ∧
      (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value = .ok val₀ ∧
      (∀ hn, Reads t E a (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        val₀.looseBVarsBounded 0 = true →
        val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        ∀ hn, ∃ ci,
          StoredAs ci (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
          Core.CIPtrRep (Core.keyOf t) h ptr ci) := by
  obtain ⟨-, -, v, hld, hraw⟩ := loadedRecords_record hS hsub hh ha hl hrec
  unfold Ingress.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨blobs, hb, raw⟩ := hraw
  have hblob := hS.blob_of_table hload hsub hb
  obtain ⟨-, ty₀, val₀, hty, hval, hreads, hrep⟩ :=
    defn_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic hblob raw
  refine ⟨ty₀, val₀, hty, hval, hreads, fun h1 h2 h3 h4 hn => ?_⟩
  obtain ⟨ci, hst, hci⟩ := hrep h1 h2 h3 h4 hn
  exact ⟨ci, hst, v, hld, hci⟩

/-- **A loaded axiom**, at an address no inert role is bound to. -/
theorem loadedRecords_axio_reads (ht : t.check = .ok ()) (hS : RunStore calls E)
    {cs_ld : List (Call F)} {E_ld : Ixon.Env} {h : Heap F} {ptr : SourceValue F}
    {bytes : ByteArray} {a : _root_.Address} {c : Ixon.Constant} {ax : Ixon.Axiom}
    (hload : LoadedBy cs_ld E_ld) (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) (hh : Hashed cs_ld bytes)
    (ha : Address.blake3Pure bytes = a) (hl : Ingress.LoadedRecords E_ld h ptr bytes)
    (hrec : Ix.Cert.recordAt E a = some c) (hinfo : c.info = .axio ax) (hlogic : InLogic c)
    (hinert : ¬ InertAt t a) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E.blobs.get? x) c id (fun _ => none)).read ax.typ = .ok ty₀ ∧
      Reads t E a (.axiomInfo ⟨keyOf t a, List.range ax.lvls.toNat, ty₀⟩) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ax.lvls.toNat) = true →
        ∃ ci, StoredAs ci (.axiomInfo ⟨keyOf t a, List.range ax.lvls.toNat, ty₀⟩) ∧
          Core.CIPtrRep (Core.keyOf t) h ptr ci) := by
  obtain ⟨-, -, v, hld, hraw⟩ := loadedRecords_record hS hsub hh ha hl hrec
  unfold Ingress.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨blobs, hb, raw⟩ := hraw
  have hblob := hS.blob_of_table hload hsub hb
  obtain ⟨ty₀, hty, hreads, hrep⟩ :=
    axio_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic (inertKey_false_of_not_inertAt ht hinert)
      hblob raw
  refine ⟨ty₀, hty, hreads, fun h1 h2 => ?_⟩
  obtain ⟨ci, hst, hci⟩ := hrep h1 h2
  exact ⟨ci, hst, v, hld, hci⟩

/-- **A loaded member of a definition block**, through its projection record at `a`. The
store holds the block, in Lean's logic. -/
theorem loadedRecords_dprj_reads (ht : t.check = .ok ()) (hS : RunStore calls E)
    {cs_ld : List (Call F)} {E_ld : Ixon.Env} {h : Heap F} {ptr : SourceValue F}
    {bytes : ByteArray} {a : _root_.Address} {c cb : Ixon.Constant} {p : Ixon.DefinitionProj}
    (hload : LoadedBy cs_ld E_ld) (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) (hh : Hashed cs_ld bytes)
    (ha : Address.blake3Pure bytes = a) (hl : Ingress.LoadedRecords E_ld h ptr bytes)
    (hrec : Ix.Cert.recordAt E a = some c) (hinfo : c.info = .dPrj p)
    (hrecB : Ix.Cert.recordAt E p.block = some cb) (hlogic : InLogic cb) :
    ∃ (ms : Array Ixon.MutConst) (d : Ixon.Definition) (ty₀ val₀ : Ix.Kernel.Expr .anon),
      cb.info = .muts ms ∧ ms[p.idx.toNat]? = some (.defn d) ∧
      a = memberAddr p.block p.idx.toNat (.defn d) ∧
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t p.block ms)).read d.typ =
        .ok ty₀ ∧
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t p.block ms)).read d.value =
        .ok val₀ ∧
      (∀ hn, Reads t E a (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        val₀.looseBVarsBounded 0 = true →
        val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true →
        ∀ hn, ∃ ci,
          StoredAs ci (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
          Core.CIPtrRep (Core.keyOf t) h ptr ci) := by
  obtain ⟨hex, htv, v, hld, hraw⟩ := loadedRecords_record hS hsub hh ha hl hrec
  unfold Ingress.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨hidx, lcB, cb', ms, d, blobs, hgetB, -, -, hexB, -, hcb, hms, hb, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload.1 p.block lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
  subst hcb_eq
  have hblob := hS.blob_of_table hload hsub hb
  obtain ⟨hc_eq, ha_eq⟩ := dprj_canonical d hex htv hinfo
  rw [ha] at ha_eq
  subst ha_eq
  have hmem : ms[p.idx.toNat]? = some (.defn d) := by
    rw [← Array.getElem?_toList]
    exact hms
  have hi : p.idx.toNat < UInt64.size := by
    show p.idx.toNat < 18446744073709551616
    omega
  have hproj : recordOf E (memberAddr p.block p.idx.toNat (.defn d)) =
      some (memberProjection p.block p.idx.toNat (.defn d)) := by
    rw [← hc_eq]
    exact hS.recordOf_of_recordAt hrec
  obtain ⟨-, ty₀, val₀, hty, hval, hreads, hrep⟩ :=
    dprj_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht hi
      (hS.recordOf_of_recordAt hrecB) hcb hmem hlogic hproj hblob raw
  refine ⟨ms, d, ty₀, val₀, hcb, hmem, rfl, hty, hval, hreads, fun h1 h2 h3 h4 hn => ?_⟩
  obtain ⟨ci, hst, hci⟩ := hrep h1 h2 h3 h4 hn
  exact ⟨ci, hst, v, hld, hci⟩

/-- **A loaded inductive type**, through its projection record at `a`. The store holds the
block, in Lean's logic. -/
theorem loadedRecords_ind_reads (ht : t.check = .ok ()) (hS : RunStore calls E)
    {cs_ld : List (Call F)} {E_ld : Ixon.Env} {h : Heap F} {ptr : SourceValue F}
    {bytes : ByteArray} {a : _root_.Address} {c cb : Ixon.Constant} {p : Ixon.InductiveProj}
    (hload : LoadedBy cs_ld E_ld) (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) (hh : Hashed cs_ld bytes)
    (ha : Address.blake3Pure bytes = a) (hl : Ingress.LoadedRecords E_ld h ptr bytes)
    (hrec : Ix.Cert.recordAt E a = some c) (hinfo : c.info = .iPrj p)
    (hrecB : Ix.Cert.recordAt E p.block = some cb) (hlogic : InLogic cb) :
    ∃ (ms : Array Ixon.MutConst) (ind : Ixon.Inductive) (ty₀ : Ix.Kernel.Expr .anon),
      cb.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind) ∧
      a = memberAddr p.block p.idx.toNat (.indc ind) ∧
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t p.block ms)).read ind.typ =
        .ok ty₀ ∧
      (∀ caps, Reads t E a (.indInfo ⟨keyOf t a, List.range ind.lvls.toNat, ty₀⟩ caps)) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true →
        ∀ caps, ∃ ci,
          StoredAs ci (.indInfo ⟨keyOf t a, List.range ind.lvls.toNat, ty₀⟩ caps) ∧
          Core.CIPtrRep (Core.keyOf t) h ptr ci) := by
  obtain ⟨hex, htv, v, hld, hraw⟩ := loadedRecords_record hS hsub hh ha hl hrec
  unfold Ingress.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨hidx, lcB, cb', ms, ind, blobs, hgetB, -, -, hexB, -, hcb, hms, hb, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload.1 p.block lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
  subst hcb_eq
  have hblob := hS.blob_of_table hload hsub hb
  obtain ⟨hc_eq, ha_eq⟩ := iprj_canonical ind hex htv hinfo
  rw [ha] at ha_eq
  subst ha_eq
  have hmem : ms[p.idx.toNat]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hms
  have hi : p.idx.toNat < UInt64.size := by
    show p.idx.toNat < 18446744073709551616
    omega
  have hproj : recordOf E (memberAddr p.block p.idx.toNat (.indc ind)) =
      some (memberProjection p.block p.idx.toNat (.indc ind)) := by
    rw [← hc_eq]
    exact hS.recordOf_of_recordAt hrec
  obtain ⟨ty₀, hty, hreads, hrep⟩ :=
    ind_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht hi
      (hS.recordOf_of_recordAt hrecB) hcb hmem hlogic hproj hblob raw
  refine ⟨ms, ind, ty₀, hcb, hmem, rfl, hty, hreads, fun h1 h2 caps => ?_⟩
  obtain ⟨ci, hst, hci⟩ := hrep h1 h2 caps
  exact ⟨ci, hst, v, hld, hci.toCIRep⟩

/-- **A loaded constructor**, through its projection record at `a`. The store holds the
block, in Lean's logic, and the block's constructors are stored at their positions (`hcidx`:
`Assembly.indBlockCtorIdx_of_exact_noCollision`, for a walked block). -/
theorem loadedRecords_ctor_reads (ht : t.check = .ok ()) (hS : RunStore calls E)
    {cs_ld : List (Call F)} {E_ld : Ixon.Env} {h : Heap F} {ptr : SourceValue F}
    {bytes : ByteArray} {a : _root_.Address} {c cb : Ixon.Constant} {p : Ixon.ConstructorProj}
    (hload : LoadedBy cs_ld E_ld) (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) (hh : Hashed cs_ld bytes)
    (ha : Address.blake3Pure bytes = a) (hl : Ingress.LoadedRecords E_ld h ptr bytes)
    (hrec : Ix.Cert.recordAt E a = some c) (hinfo : c.info = .cPrj p)
    (hrecB : Ix.Cert.recordAt E p.block = some cb) (hlogic : InLogic cb)
    (hcidx : ∀ (ms : Array Ixon.MutConst) (ind : Ixon.Inductive) (ct : Ixon.Constructor),
      cb.info = .muts ms → ms[p.idx.toNat]? = some (.indc ind) →
      ind.ctors[p.cidx.toNat]? = some ct → ct.cidx.toNat = p.cidx.toNat) :
    ∃ (ms : Array Ixon.MutConst) (ind : Ixon.Inductive) (ct : Ixon.Constructor)
      (ty₀ : Ix.Kernel.Expr .anon),
      cb.info = .muts ms ∧ ms[p.idx.toNat]? = some (.indc ind) ∧
      ind.ctors[p.cidx.toNat]? = some ct ∧
      a = ctorAddr p.block p.idx.toNat p.cidx.toNat ∧
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t p.block ms)).read ct.typ =
        .ok ty₀ ∧
      Reads t E a (.ctorInfo ⟨keyOf t a, List.range ct.lvls.toNat, ty₀⟩ ct.params.toNat
        ct.fields.toNat) ∧
      (ty₀.looseBVarsBounded 0 = true →
        ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true →
        ∃ ci,
          StoredAs ci (.ctorInfo ⟨keyOf t a, List.range ct.lvls.toNat, ty₀⟩ ct.params.toNat
            ct.fields.toNat) ∧
          Core.CIPtrRep (Core.keyOf t) h ptr ci) := by
  obtain ⟨hex, htv, v, hld, hraw⟩ := loadedRecords_record hS hsub hh ha hl hrec
  unfold Ingress.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨hidx, hcidx56, lcB, cb', ms, ind, ct, blobs, hgetB, -, -, hexB, -, hcb, hms, hct, hb,
    raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload.1 p.block lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
  subst hcb_eq
  have hblob := hS.blob_of_table hload hsub hb
  obtain ⟨hc_eq, ha_eq⟩ := cprj_canonical hex htv hinfo
  rw [ha] at ha_eq
  subst ha_eq
  have hmem : ms[p.idx.toNat]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hms
  have hct' : ind.ctors[p.cidx.toNat]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hct
  have hi : p.idx.toNat < UInt64.size := by
    show p.idx.toNat < 18446744073709551616
    omega
  have hj : p.cidx.toNat < UInt64.size := by
    show p.cidx.toNat < 18446744073709551616
    omega
  have hproj : recordOf E (ctorAddr p.block p.idx.toNat p.cidx.toNat) =
      some (constructorProjection p.block p.idx.toNat p.cidx.toNat) := by
    rw [← hc_eq]
    exact hS.recordOf_of_recordAt hrec
  obtain ⟨ty₀, hty, hreads, hrep⟩ :=
    ctor_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht hi hj
      (hS.recordOf_of_recordAt hrecB) hcb hmem hct' (hcidx ms ind ct hcb hmem hct') hlogic hproj
      hblob raw
  refine ⟨ms, ind, ct, ty₀, hcb, hmem, hct', rfl, hty, hreads, fun h1 h2 => ?_⟩
  obtain ⟨ci, hst, hci⟩ := hrep h1 h2
  exact ⟨ci, hst, v, hld, hci.toCIRep⟩

end Loaded

end IxVM.Refinement.LoadedReads
