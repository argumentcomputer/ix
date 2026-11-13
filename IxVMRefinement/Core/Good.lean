import IxVMRefinement.Core.Ctx
import Ix.IxVM.Consistency.Statement
import IxC.Kernel.Inductives.StructParts
import IxC.Kernel.Verify.EnvPreds

/-! # Good calls, the collision escape, and the loads

`Good c calls`: the calls hashed no collision with the records `c.E` (the escape of the
statement's `Core`, `View.HashedCollision { env := c.E } [] calls`), and they are **bounded**:
some valid ROM of at most `2^39` addresses carries them (the statement's `Bounded`, which L0
provides), so every list their arguments hold is shorter than `2^39`. Every registry spec is conditional on `Good` of its own calls, and `Good`
passes to sub-derivations (`Good.sub`): a callee's calls are among its caller's.

`LoadFacts c`: the record loads the core makes read the environment: a load at an address the
table keys as `k` returns a constant representing `env`'s constant at `k`. This is the
L1 ↔ L7 interface: L1 (`Records`) says what a load returns in terms of the bytes it hashed;
L7 (with L5) says the environment stores, at each record's key, the constant those bytes read
as. The registry specs of `Ingress::get_ci`, `get_ci_cprj` and `get_ci_iprj` are discharged from
it. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-- **The calls are good**: no hashed collision with the records `c.E`, and bounded. -/
def Good (c : Ctx) (calls : List (Call F)) : Prop :=
  ¬ View.HashedCollision { env := c.E } [] calls ∧ IxVM.Consistency.Bounded calls

theorem hashed_mono {calls₁ calls₂ : List (Call F)} (hsub : ∀ x ∈ calls₁, x ∈ calls₂)
    {b : ByteArray} (h : Hashed calls₁ b) : Hashed calls₂ b := by
  obtain ⟨cl, hm, rest⟩ := h
  exact ⟨cl, hsub cl hm, rest⟩

theorem collision_mono {V : View} {calls₁ calls₂ : List (Call F)}
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) (h : V.HashedCollision [] calls₁) :
    V.HashedCollision [] calls₂ := by
  rcases h with ⟨x, held, bytes, hpre, hh, hne, hx⟩ | ⟨bytes, hpre, hx⟩
  · refine .inl ⟨x, held, bytes, ?_, hashed_mono hsub hh, hne, hx⟩
    rcases hpre with hp | hp | ⟨hh', hx'⟩
    · exact .inl hp
    · exact .inr (.inl hp)
    · exact .inr (.inr ⟨hashed_mono hsub hh', hx'⟩)
  · refine .inr ⟨bytes, ?_, hx⟩
    rcases hpre with hp | hp
    · exact .inl hp
    · exact .inr (hashed_mono hsub hp)

theorem bounded_sub {calls₁ calls₂ : List (Call F)} (hsub : ∀ x ∈ calls₁, x ∈ calls₂)
    (b : IxVM.Consistency.Bounded calls₂) : IxVM.Consistency.Bounded calls₁ := by
  obtain ⟨rom, hv, hb, hc⟩ := b
  exact ⟨rom, hv, hb, fun cl hcl => hc cl (hsub cl hcl)⟩

/-- **Good passes to sub-derivations.** -/
theorem Good.sub {c : Ctx} {calls₁ calls₂ : List (Call F)} (g : Good c calls₂)
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) : Good c calls₁ :=
  ⟨fun h => g.1 (collision_mono hsub h), bounded_sub hsub g.2⟩

/-- **The record-load escape**: with no hashed collision, every byte string the run hashed to a
stored address is the records' data at that address. -/
theorem load_escape {E : Ixon.Env} {calls : List (Call F)} {x : _root_.Address}
    {lc : Ixon.LazyConstant} (hst : E.consts.get? x = some lc)
    (nc : ¬ View.HashedCollision { env := E } [] calls) :
    ∀ bytes, Hashed calls bytes → Address.blake3Pure bytes = x → bytes = lc.rawBytes := by
  intro bytes hh hx
  by_cases heq : bytes = lc.rawBytes
  · exact heq
  · exact absurd (.inl ⟨x, lc.rawBytes, bytes, .inl (.inl ⟨lc, hst, rfl⟩), hh, heq, hx⟩) nc

/-! ## The loads -/

/-- An inductive block member. -/
def isIndc : Ixon.MutConst → Bool
  | .indc _ => true
  | _ => false

/-- **The record at `a` in `c.E` is no block of two or more inductives** (what
`block_is_multi`'s and `block_is_modeled`'s answer `0` establish; the latter's nested-occurrence
scan is not read). -/
def FewInductives (c : Ctx) (a : _root_.Address) : Prop :=
  ∀ cst ms, Ix.Cert.recordAt c.E a = some cst → cst.info = .muts ms →
    (ms.toList.filter isIndc).length ≤ 1

/-- The sort a `∀`-telescope ends in after exactly `n` binders. -/
def piSortAt : Nat → KExpr → Option KLevel
  | 0, .sort l => some l
  | n + 1, .forallE _ b _ => piSortAt n b
  | _, _ => none

/-- **The loads read the environment** (module docstring): every good derivation of
`Ingress::get_ci` at an address `a` returns a constant representing `env`'s constant at
`κ a`; and so do the projection loaders the core calls directly, `get_ci_cprj(block, i, j)` and
`get_ci_iprj(block, i)`, at the key of the projection record they stand for. An inductive
projection record loads as its block member, with the member's counts (`indRecord`), and an
inductive loads only from such a record (`inductRecord`). A native structure IxVM projects from
has its projection table (`projTables`).
Owed by the record conversion and the assembly. -/
structure LoadFacts (c : Ctx) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr →
      ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧ CIPtrRep c.κ h' ptr ci
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) = some ci ∧
        CIPtrRep c.κ h' ptr ci
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some ci ∧ CIPtrRep c.κ h' ptr ci
  /-- **An inductive projection record loads as its member**: `get_ci` at an address whose
  record in `c.E` is the inductive projection `p` of a block member `ind` returns an inductive
  whose counts are `ind`'s and whose block and index fields are `p`'s. -/
  indRecord : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (cm cb : Ixon.Constant) (p : Ixon.InductiveProj) (xs : Array Ixon.MutConst)
      (ind : Ixon.Inductive),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs → Bytes.RepAddressRef addrTy h a addr →
    Ix.Cert.recordAt c.E (ixAddr a) = some cm → cm.info = .iPrj p →
    Ix.Cert.recordAt c.E p.block = some cb → cb.info = .muts xs →
    xs[p.idx.toNat]? = some (.indc ind) →
    ∃ (nl ty u blk : SourceValue F) (b : Bytes.Address),
      loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, .field (ind.params.toNat : F),
        .field (ind.indices.toNat : F), .field (ind.ctors.size : F), u, blk,
        .field (p.idx.toNat : F)]) ∧
      Bytes.RepAddressRef addrTy h' b blk ∧ ixAddr b = p.block ∧
      p.idx.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56
  /-- (L1, L7) **A loaded inductive comes from its projection record**: an inductive `get_ci`
  returns at `a` is read from the record at `a` in `c.E`, the inductive projection of member
  `idx` of the block `blk` (the converse of `indRecord`; the loader converts only that record
  shape to an inductive). -/
  inductRecord : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty np ni nc u blk idx : SourceValue F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs → Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (ixAddr a) = some cm ∧ Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩
  /-- **A native structure's projection table**, for `Red.proj` and `Infer.proj`: a good
  derivation of `KernelModeled::proj_ctor(block, idx)` (which asserts that IxVM does not model the
  block and loads member `idx`'s constructor) means the inductive at the member's key `S` is
  stored with its table. For every stored constructor of the member (at any index `j`; there is
  one), the table names that constructor at its counts and level parameters, its parameter count
  being the member's in the block record (which `indRecord` makes the loaded inductive's);
  every entry below the field count is found and has its head data (`TowerHead`: the constructor and the structure
  stored at the entry's counts and level parameters, the structure's type after its parameters
  the sort `structSort`); the bodies are `structProjBodies`' at the constructor's type (so
  `entry.typeAt` is the field type IxVM computes) and the guards `structProjGuards`' at some
  field sorts (`FireSem`); and the constructor's binders carry the zero-ness of that sort (its
  arguments' `Certs` are `never` skips where the sort is never zero).

  Owed: the table's existence where IxVM's route is native, and the constructor's binder data,
  by the declaration layer (it installs natively exactly where IxVM checked the block natively,
  and its shape check ties the constructor's parameter count to the inductive's;
  `block_is_modeled` is a function of the record); the head data by the store invariant
  (`EnvFacts.store`, `ProjOkT.towerHead`); the bodies and guards by
  `Ix.Kernel.Model.TableBodies` (`IxC/Kernel/Model/StoreCompanions.lean`,
  `tableBodies_declsRunJ`). Still owed by the declaration layer: that the guards' `sorts` are the
  fields' sorts. -/
  projTables : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp → ip = .field i →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) ∧
        tbl.structName = c.κ (iprjAddr (ixAddr b) (ZMod.val i)) ∧
        tbl.ctor = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) ∧ tbl.numParams = nP ∧
        tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
        (∀ cb xs ind, Ix.Cert.recordAt c.E (ixAddr b) = some cb → cb.info = .muts xs →
          xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
        (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort
  /-- **`projTables` at the route test `red_proj` makes**: the same conclusions, keyed on a good
  derivation of `KernelModeled::block_is_modeled(block)` answering `0` and a good `get_ci` loading
  an inductive of member `i` of that block with no index and one constructor, as the loaded
  counts read (`red_proj` tests the block and loads the constructor itself; `k_infer_proj` and the io projection arm go through `proj_ctor`). Owed as
  `projTables`. -/
  projTablesAt : ∀ (bp sap ptr nl ty np u blk : SourceValue F) (h h' h1 h2 : Heap F)
      (cs cs1 : List (Call F)) (b s : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp →
    ObsFn W "Ingress::get_ci" [sap] h1 ptr h2 cs1 → Good c cs1 →
    Bytes.RepAddressRef addrTy h1 s sap →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) ∧
        tbl.structName = c.κ (iprjAddr (ixAddr b) (ZMod.val i)) ∧
        tbl.ctor = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) ∧ tbl.numParams = nP ∧
        tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
        (∀ cb xs ind, Ix.Cert.recordAt c.E (ixAddr b) = some cb → cb.info = .muts xs →
          xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
        (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort
  /-- (L5) **Unit-likeness**: an inductive that `get_ci` loads with no index and one constructor
  (whose stored constructor, at the first constructor record of its member, has no field), at a
  block with at most one inductive, is unit-like at its loaded parameter count; at a reserved
  basis key it is the pinned `PUnit` (no parameter, `isUnitLikeTy`). Owed by the declaration
  layer: the native install's capabilities (`nativeCapsAt`: `unitlike`, `unitParams`) and the
  pinned basis. -/
  unitLike : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cvC : Ix.Kernel.ConstantVal .anon) (nPc : Nat),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c cs → Bytes.RepAddressRef addrTy h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    c.env.find? (c.κ (ixAddr a)) = some (.indInfo cvT caps) →
    FewInductives c (ixAddr b) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvC nPc 0) →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (c.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const (c.κ (ixAddr a)) us) = true))
  /-- (L5, L7) **Structure η**: the inductive member `i` of the block `b`, as `get_ci_iprj` loads
  it with no index and one constructor, whose block `block_is_modeled` answers `0`, whose sort
  after the constructor's parameters is never zero at some levels, and whose projection record
  `struct_is_rec` does not find recursive, is η-capable through the constructor `c.κ ac` (a
  stored constructor of that member with at least one field), with that constructor's field and
  parameter counts, and the constructor is stored at the inductive's level parameters. Owed by the
  declaration layer (`nativeCapsAt`: `eta`, `etaCtor`, `etaFields`, `etaParams`) and, for the level
  parameters, by the reader (a block's members share its level parameters). With `EnvFacts.recEta`
  this gives the η rescue's `rl.eta = true` at the recursor IxVM fires. -/
  eta : ∀ (ac b sa : Bytes.Address) (i : F) (j : Nat) (cvc cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel)
      (bp ptr nl ty np u blk idx : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F)),
    c.env.find? (c.κ (ixAddr ac)) = some (.ctorInfo cvc cnP cnF) →
    cvc.name = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) → 0 < cnF →
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h1 ptr h2 cs1 → Good c cs1 →
    Bytes.RepAddressRef addrTy h1 b bp →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, idx]) →
    c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_modeled" [bq] h3 (.field 0) h4 cs3 ∧ Good c cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    piSortAt cnP (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c cs5 ∧
        Bytes.RepAddressRef addrTy h5 sa sp) →
    ixAddr sa = iprjAddr (ixAddr b) (ZMod.val i) →
    caps.eta = true ∧ caps.etaCtor = some (c.κ (ixAddr ac)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cvc.levelParams = cvT.levelParams
  /-- (L5, L7) **Structure η at the observations ι's η route makes** (`try_struct_eta_iota`,
  `eta_iota_fab`): an inductive `get_ci` loads at `pa` with no index and one constructor, in a
  block with at most one inductive (`block_is_multi` answering `0`), not found recursive by
  `struct_is_rec`, whose sort after its loaded parameter count is never zero at some levels, and
  whose first constructor is stored, is η-capable through that constructor, with its field and
  parameter counts, the constructor at the inductive's level parameters. The store's η bit
  (`nativeCapsAt`: no index, not a proposition, no recursive field) asks nothing of the field
  count, so no field is required. The two tests imply the native route: with no member mentioned
  by any field there is no nested occurrence either. Owed by the declaration layer, and by the
  loader for the loaded parameter count being the record's (`cnP = ZMod.val m`, which needs the
  record's count below the field's size). -/
  etaIota : ∀ (pp ptr nl ty u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (pa b : Bytes.Address) (i m : F) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel),
    ObsFn W "Ingress::get_ci" [pp] h1 ptr h2 cs1 → Good c cs1 →
    Bytes.RepAddressRef addrTy h1 pa pp →
    loadValue h2 ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field m, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    c.env.find? (c.κ (ixAddr pa)) = some (.indInfo cvT caps) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvc cnP cnF) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧ Good c cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c cs5 ∧
        Bytes.RepAddressRef addrTy h5 pa sp) →
    piSortAt (ZMod.val m) (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    caps.eta = true ∧
      caps.etaCtor = some (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cnP = ZMod.val m ∧ cvc.levelParams = cvT.levelParams
  /-- (L1) **A stored record decodes as the record whose bytes it holds**: a record of `c.E`
  whose raw bytes are the serialization of a constant with empty tables (any kind) reads as
  that constant's payload. `Good` gives only the raw bytes (a held record at an address the run
  hashed has the hashed bytes, `load_escape`); `LazyConstant.get?` reads the cache and its byte
  window, which the loader layer builds by decoding those bytes: the claim's canonical store
  (`Ix.Cert.Stream.StoredCanonical`) and `serConstant`'s injectivity on wire-valid constants. -/
  canonical : ∀ (x : _root_.Address) (lc : Ixon.LazyConstant) (info : Ixon.ConstantInfo),
    c.E.consts.get? x = some lc → lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[]⟩ →
      ∀ cm, lc.get? = some cm → cm.info = info

/-! ## Specs -/

/-- **A spec**: a predicate on an observed derivation of a function (its arguments, the heap
before, the result, the heap after, its calls), relative to a context. Every function of the
registry has one (`Registry.lean`). -/
abbrev SpecFn : Type :=
  Ctx → List (SourceValue F) → Heap F → SourceValue F → Heap F → List (Call F) → Prop

/-- **The facts a step lemma may use about its context**: the environment invariant and the
loads. `S0.ctx` gives both. -/
structure CoreFacts (c : Ctx) : Prop where
  env : EnvFacts c
  loads : LoadFacts c

end IxVM.Refinement.Core
