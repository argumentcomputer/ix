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
  one), the table names that constructor at its counts and level parameters; every entry below
  the field count is found and has its head data (`TowerHead`: the constructor and the structure
  stored at the entry's counts and level parameters, the structure's type after its parameters
  the sort `structSort`); the bodies are `structProjBodies`' at the constructor's type (so
  `entry.typeAt` is the field type IxVM computes) and the guards `structProjGuards`' at some
  field sorts (`FireSem`); and the constructor's binders carry the zero-ness of that sort (its
  arguments' `Certs` are `never` skips where the sort is never zero).

  Owed: the table's existence where IxVM's route is native, and the constructor's binder data,
  by the declaration layer (it installs natively exactly where IxVM checked the block natively;
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
        (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort

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
