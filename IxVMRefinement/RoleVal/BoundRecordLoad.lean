import IxVMRefinement.RoleVal.AxiomRecordLim
import IxVMRefinement.Claim.TopProj

/-! # The bound record a role's validation loads

Every arm of `KernelRoles::validate_role` starts with `Ingress::get_ci` on the role's bound
address. So the validation of any role hashed bytes at its bound address that decode exactly to
a record, and for a projection record the block it names was loaded as well.

* `projBlockOf? c`: the block a projection record names (none for every other record).
* `validate_role_bound_loaded`, `ValidateRoleIn.bound_loaded`: the record at the role's bound
  address is decoded from bytes the validation hashed, and the block of a projection record is a
  block record decoded from bytes the validation hashed.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false

/-- **The block a projection record names.** -/
def projBlockOf? (c : Ixon.Constant) : Option _root_.Address :=
  match c.info with
  | .dPrj p => some p.block
  | .iPrj p => some p.block
  | .cPrj p => some p.block
  | .rPrj p => some p.block
  | _ => none

/-- The load at the head of every arm of the validation. -/
private theorem bound_loaded_of_get_ci {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {ro : Ix.Kernel.Role} {x_tbl v1 p39 : SourceValue F} {h m2 m32 : Heap F}
    {cs12 cs45 calls : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev14 : ObsFn W "KernelRoles::role_bound_addr" [x_tbl, .field (roleNum ro)] h v1 m2 cs12)
    (ev47 : ObsFn W "Ingress::get_ci" [v1] m2 p39 m32 cs45)
    (hsub : ∀ cl ∈ cs45, cl ∈ calls) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstantExact rawBytes = .ok c ∧
      ∀ blk, projBlockOf? c = some blk → ∃ cb ms, Claim.BlockLoad calls blk cb ms := by
  obtain ⟨-, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
  obtain ⟨ab, hab, rfl⟩ := ha_m2
  obtain ⟨rawBytes, c, hsz, hh, hblk, hx, -, hd⟩ := Claim.get_ci_head hab ev47
  refine ⟨_, rawBytes, c, had, hsz, Claim.hashed_mono hsub hh, hblk, hx, fun blk hp => ?_⟩
  unfold projBlockOf? at hp
  cases hi : c.info with
  | dPrj p =>
    rw [hi] at hp
    cases hp
    obtain ⟨cb, ms, d, hbl, -⟩ := hd.dPrj p.idx p.block hi
    exact ⟨cb, ms, hbl.mono hsub⟩
  | iPrj p =>
    rw [hi] at hp
    cases hp
    obtain ⟨cb, ms, ind, hbl, -⟩ := hd.iPrj p.idx p.block hi
    exact ⟨cb, ms, hbl.mono hsub⟩
  | cPrj p =>
    rw [hi] at hp
    cases hp
    obtain ⟨cb, ms, ind, hbl, -⟩ := hd.cPrj p.idx p.cidx p.block hi
    exact ⟨cb, ms, hbl.mono hsub⟩
  | rPrj p =>
    rw [hi] at hp
    cases hp
    obtain ⟨cb, ms, rc, hbl, -⟩ := hd.rPrj p.idx p.block hi
    exact ⟨cb, ms, hbl.mono hsub⟩
  | defn _ => rw [hi] at hp; cases hp
  | axio _ => rw [hi] at hp; cases hp
  | quot _ => rw [hi] at hp; cases hp
  | recr _ => rw [hi] at hp; cases hp
  | muts _ => rw [hi] at hp; cases hp

/-- **The bound record a role's validation loads**: the record at the role's bound address is
decoded from bytes the validation hashed, and the block a projection record names is a block
record decoded from bytes it hashed. -/
theorem validate_role_bound_loaded {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {ro : Ix.Kernel.Role} {x_rc x_tbl r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstantExact rawBytes = .ok c ∧
      ∀ blk, projBlockOf? c = some blk → ∃ cb ms, Claim.BlockLoad calls blk cb ms := by
  match Obs.«KernelRoles::validate_role».obs ev with
  | .n0 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc183 := hc) .. =>
    exact bound_loaded_of_get_ci htbl ev14 ev47 (fun cl hm => by rw [hc]; simp [hm])
  | .n1 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc227 := hc) .. =>
    exact bound_loaded_of_get_ci htbl ev14 ev47 (fun cl hm => by rw [hc]; simp [hm])
  | .n2 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc279 := hc) .. =>
    exact bound_loaded_of_get_ci htbl ev14 ev47 (fun cl hm => by rw [hc]; simp [hm])
  | .n3 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc323 := hc) .. =>
    exact bound_loaded_of_get_ci htbl ev14 ev47 (fun cl hm => by rw [hc]; simp [hm])
  | .n4 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc367 := hc) .. =>
    exact bound_loaded_of_get_ci htbl ev14 ev47 (fun cl hm => by rw [hc]; simp [hm])
  | .n5 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc419 := hc) .. =>
    exact bound_loaded_of_get_ci htbl ev14 ev47 (fun cl hm => by rw [hc]; simp [hm])

/-- **The same from the observed validation of the role.** -/
theorem ValidateRoleIn.bound_loaded {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstantExact rawBytes = .ok c ∧
      ∀ blk, projBlockOf? c = some blk → ∃ cb ms, Claim.BlockLoad calls blk cb ms := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, rawBytes, c, had, hsz, hh, hblk, hx, hproj⟩ := validate_role_bound_loaded htbl ev
  refine ⟨a, rawBytes, c, had, hsz, Claim.hashed_mono hsub hh, hblk, hx, fun blk hp => ?_⟩
  obtain ⟨cb, ms, hbl⟩ := hproj blk hp
  exact ⟨cb, ms, hbl.mono hsub⟩

end IxVM.Refinement.RoleVal
