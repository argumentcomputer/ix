import IxVMRefinement.Ingress.Records
import IxVMRefinement.Core.CallScope

/-! # Block addresses a run hashed

Every load that reaches a block member hashes the block record it reads: `Ingress::get_ci_cprj`,
`Ingress::get_ci_iprj`, `KernelModeled::proj_ctor` (through `get_ci_cprj`), and `Ingress::get_ci`
returning an inductive or a constructor. In calls that are `Good`, the block's address is then
a `Core.HashedBlockAt` address. -/

set_option maxRecDepth 100000

namespace IxVM.Refinement.Ingress

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Obs

/-- A direct load of a constructor hashes its block. -/
theorem hashedBlockAt_of_get_ci_cprj {c : Core.Ctx} {cs : List (Call F)} (hg : Core.Good c cs)
    {b : Bytes.Address} {bp ptr : SourceValue F} {i j : F} {h h' : Heap F}
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs) :
    Core.HashedBlockAt c.E (Core.ixAddr b) := by
  obtain ⟨_, _, _, blkBytes, cb, ms, _, _, _, _, hh, ha, hex, _, hms, _⟩ :=
    get_ci_cprj_origin_spec hg.2 hb ev
  exact Core.HashedBlockAt.of_good hg hh hex hms ha

/-- A direct load of an inductive member hashes its block. -/
theorem hashedBlockAt_of_get_ci_iprj {c : Core.Ctx} {cs : List (Call F)} (hg : Core.Good c cs)
    {b : Bytes.Address} {bp ptr : SourceValue F} {i : F} {h h' : Heap F}
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs) :
    Core.HashedBlockAt c.E (Core.ixAddr b) := by
  obtain ⟨_, _, blkBytes, cb, ms, _, _, _, hh, ha, hex, _, hms, _⟩ :=
    get_ci_iprj_origin_spec hg.2 hb ev
  exact Core.HashedBlockAt.of_good hg hh hex hms ha

/-- A load returning an inductive hashes the block its value names. -/
theorem hashedBlockAt_of_get_ci_induct {c : Core.Ctx} {cs : List (Call F)} (hg : Core.Good c cs)
    {a b : Bytes.Address} {addr ptr nl ty np ni nc u blk idx : SourceValue F} {h h' : Heap F}
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]))
    (hb : Bytes.RepAddressRef Core.addrTy h' b blk) :
    Core.HashedBlockAt c.E (Core.ixAddr b) := by
  obtain ⟨_, blkBytes, _, cb, xs, _, b', _, _, _, _, _, hh, ha', hex, _, hb', _, _, _, hms, _⟩ :=
    inductRecord_raw_of_get_ci ev hg.2 ha hld
  have e : b' = b := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb' hb
  subst e
  exact Core.HashedBlockAt.of_good hg hh hex hms ha'

private theorem defnValShape_ne_ctor (d : Ixon.Definition)
    (tyPtr valPtr hint nl ty blk ind cidx np nf u : SourceValue F) :
    defnValShape d tyPtr valPtr hint ≠
      .construct Core.kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u] := by
  cases hk : d.kind <;> simp [defnValShape, hk]

/-- A load returning a constructor hashes the block its value names. -/
theorem hashedBlockAt_of_get_ci_ctor {c : Core.Ctx} {cs : List (Call F)} (hg : Core.Good c cs)
    {a b : Bytes.Address} {addr ptr nl ty blk ind cidx np nf u : SourceValue F} {h h' : Heap F}
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u]))
    (hb : Bytes.RepAddressRef Core.addrTy h' b blk) :
    Core.HashedBlockAt c.E (Core.ixAddr b) := by
  obtain ⟨_, rawBytes, cm, _, _, _, _, _, _, _, hres⟩ := get_ci_spec hg.2 ha ev
  unfold GetCIRawResult at hres
  cases hinfo : cm.info with
  | defn d =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (ok_inj (hld'.symm.trans hld)) (defnValShape_ne_ctor d _ _ _ _ _ _ _ _ _ _ _)
  | axio _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, rfl, _⟩ := hres
    have heq := ok_inj (hld'.symm.trans hld)
    simp at heq
  | quot _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, rfl, _⟩ := hres
    have heq := ok_inj (hld'.symm.trans hld)
    simp at heq
  | recr _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld', _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := ok_inj (hld'.symm.trans hld)
    simp at heq
  | dPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, d, _, _, _, _, _, _, _, hld', _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (ok_inj (hld'.symm.trans hld)) (defnValShape_ne_ctor d _ _ _ _ _ _ _ _ _ _ _)
  | rPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hld',
      _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := ok_inj (hld'.symm.trans hld)
    simp at heq
  | muts _ =>
    rw [hinfo] at hres
    exact False.elim hres
  | iPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hld',
      _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hres
    have heq := ok_inj (hld'.symm.trans hld)
    simp at heq
  | cPrj p =>
    rw [hinfo] at hres
    obtain ⟨_, _, blkBytes, cb, ms, _, _, _, hh, ha', hex, _, hms, _, _, hld',
      _, _, _, _, _, _, blkPtr, b', hb_eq, hb', rfl, _⟩ := hres
    have hv := ok_inj (hld'.symm.trans hld)
    injection hv with _ _ hl
    injection hl with _ hl
    injection hl with _ hl
    injection hl with hblk _
    subst hblk
    have e : b' = b := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb' hb
    subst e
    exact Core.HashedBlockAt.of_good hg hh hex hms (ha'.trans hb_eq.symm)

/-- `KernelModeled::proj_ctor` hashes the block it is called on. -/
theorem hashedBlockAt_of_proj_ctor {c : Core.Ctx} {cs : List (Call F)} (hg : Core.Good c cs)
    {b : Bytes.Address} {bp ip ptr : SourceValue F} {i : F} {h h' : Heap F}
    (ev : ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs)
    (hb : Bytes.RepAddressRef Core.addrTy h b bp) (hip : ip = .field i) :
    Core.HashedBlockAt c.E (Core.ixAddr b) := by
  subst hip
  obtain ⟨v, mid, cs_assert, cs_load, ev_assert, _, ev_load, hcalls⟩ :=
    Obs.«KernelModeled::proj_ctor».obs ev
  exact hashedBlockAt_of_get_ci_cprj (hg.sub fun cl hcl => by simp [hcalls, hcl])
    (Bytes.repAddressRef_heapMono₂ Core.addrTy ev_assert.heap_extends hb) ev_load

end IxVM.Refinement.Ingress
