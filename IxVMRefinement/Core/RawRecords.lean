import IxVMRefinement.Core.CallScope
import IxVMRefinement.Core.Det

/-! # Raw record identity at selected calls

Declaration metadata queries need the decoded record and its parent block. They do not need
an installed semantic constant. The exact function, input arguments, and input heap remain
part of the selected scope.
-/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library

/-- Canonical record identities at selected successful inductive metadata queries. -/
structure RawRecordFacts (c : ScopedCtx) : Prop where
  inductiveRead : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty np ni nc u blk idx : SourceValue F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
    c.allowedTop "Ingress::get_ci" [addr] h → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
    ∃ (cm cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive)
      (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (ixAddr a) = some cm ∧
      Bytes.RepAddressRef addrTy h' b blk ∧ idx = .field i ∧
      cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩ ∧
      Ix.Cert.recordAt c.E (ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind)

theorem RawRecordFacts.inductRecord {c : ScopedCtx} (facts : RawRecordFacts c)
    (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
    (nl ty np ni nc u blk idx : SourceValue F)
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (allowed : c.allowedTop "Ingress::get_ci" [addr] h) (good : Good c.toCtx cs)
    (ha : Bytes.RepAddressRef addrTy h a addr)
    (loaded : loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx])) :
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (ixAddr a) = some cm ∧ Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩ := by
  obtain ⟨cm, _, _, _, b, i, hcm, hb, hi, hp, _⟩ :=
    facts.inductiveRead addr ptr h h' cs a nl ty np ni nc u blk idx ev allowed good ha loaded
  exact ⟨cm, b, i, hcm, hb, hi, hp⟩

theorem RawRecordFacts.inductBlock {c : ScopedCtx} (facts : RawRecordFacts c)
    (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a b : Bytes.Address)
    (nl ty np ni nc u blk : SourceValue F) (i : F)
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (allowed : c.allowedTop "Ingress::get_ci" [addr] h) (good : Good c.toCtx cs)
    (ha : Bytes.RepAddressRef addrTy h a addr)
    (loaded : loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, np, ni, nc, u, blk, .field i]))
    (hb : Bytes.RepAddressRef addrTy h' b blk) :
    ∃ (cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt c.E (ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind) := by
  obtain ⟨_, cb, xs, ind, b', i', _, hb', hi, _, hcb, hxs, hind⟩ :=
    facts.inductiveRead addr ptr h h' cs a nl ty np ni nc u blk (.field i) ev allowed good ha loaded
  have hbEq := addr_det hb hb'
  have hiEq := Value.field.inj hi
  cases hbEq
  cases hiEq
  exact ⟨cb, xs, ind, hcb, hxs, hind⟩

/-- The semantic core's load contract also supplies its raw query identities. -/
theorem ScopedLoadFacts.rawRecords {c : ScopedCtx} (facts : ScopedLoadFacts c) :
    RawRecordFacts c where
  inductiveRead := by
    intro addr ptr h h' cs a nl ty np ni nc u blk idx ev allowed good ha loaded
    obtain ⟨cm, b, i, hcm, hb, hi, hp⟩ :=
      facts.inductRecord addr ptr h h' cs a nl ty np ni nc u blk idx ev allowed good ha loaded
    cases hi
    obtain ⟨cb, xs, ind, hcb, hxs, hind⟩ :=
      facts.inductBlock addr ptr h h' cs a b nl ty np ni nc u blk i ev allowed good ha loaded hb
    exact ⟨cm, cb, xs, ind, b, i, hcm, hb, rfl, hp, hcb, hxs, hind⟩

end IxVM.Refinement.Core
