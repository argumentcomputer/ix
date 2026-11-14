import Ix.IxVM.Consistency.L0
import IxVMRefinement.Levels.Spec
import IxVMRefinement.Subst.Steps
import IxVMRefinement.Core.AllSteps
import IxVMRefinement.Core.RomBound
import IxVMRefinement.L1.Records
import IxVMRefinement.Claim.Phase

/-! # Seams assembly for obligations `L0`, `L1`, `L2`, `L3`, `L4`, and `L6`

Combines the verified circuit-to-source (`L0`), record-loading (`L1`), universe-level (`L2`),
term-substitution (`L3`), core-typing (`L4`), and claim/role-walk (`L6`) obligations over any
declaration-check seam `Checked`:

* `mkSeams Checked`: equips `Core.S₀` with `L1.LoadedL1`, `Claim.WalkedL6`, and `Checked`,
  sharing `addr`, `Ghost`, `term`, and `ctx` definitionally with `Core.S₀` so `L1`, `L3`, `L4`,
  and `L6` transfer with zero re-elaboration;
* `defaultTableBytesUnfolds` and `defaultAdmits`: unconditional admission of the committed default
  role table via `Ix.Kernel.Reader.defaultTableBytesOf`;
* `consistent_of_decls_l7`: reduces `IxVM.Consistency.CircuitConsistent` to `Decls (mkSeams Checked)`
  and `L7 (mkSeams Checked)`;
* `mutsMemberCheckedAtFull_to_checkedAtFull` and `checkedAtFull_loadedL1`: bridges block-member
  and standalone `CheckedAtFull` witnesses from `L6` with `L1.projection_addr_spec` and
  `L1.get_ci_loadedL1_spec` under `Bounded calls`. -/

universe u

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- Seams bundle equipping `Core.S₀` with `L1.LoadedL1`, `Claim.WalkedL6`, and a chosen
declaration-check seam `Checked`. -/
def mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Seams :=
  { Core.S₀ with
    loaded := L1.LoadedL1
    Walked := Claim.WalkedL6
    Checked := Checked }

/-! ## Unconditional default role-table admission -/

/-- `Ix.Kernel.Reader.defaultTableBytes` unfolds via `Ix.Kernel.Reader.defaultTableBytesOf` to
`Claim.defaultTableBytesOf RoleData.table` without reducing `bytesOfHex RoleData.table`. -/
theorem defaultTableBytesUnfolds : Claim.DefaultTableBytesUnfolds :=
  Claim.defaultTableBytesUnfolds_of_fn Ix.Kernel.Reader.defaultTableBytesOf (fun _ => rfl) rfl

/-- The committed default role table admits under `Address.admissionHash`. -/
theorem defaultAdmits : Ix.Cert.RoleClosure.DefaultAdmits :=
  Claim.defaultAdmits_of_unfolds defaultTableBytesUnfolds

/-! ## Layer obligations `L1`, `L2`, `L3`, `L4`, and `L6` at `mkSeams Checked` -/

/-- `Records` at `mkSeams Checked`. -/
theorem records_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Records (mkSeams Checked) :=
  L1.records_L1

/-- Obligation `L1` at `mkSeams Checked`. -/
theorem l1_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.L1 (mkSeams Checked) :=
  L1.records_L1

/-- `Terms` at `mkSeams Checked`. -/
theorem terms_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Terms (mkSeams Checked) :=
  Core.terms_S₀

/-- Obligation `L3` at `mkSeams Checked`. -/
theorem l3_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.L3 (mkSeams Checked) :=
  fun _ => Core.terms_S₀

/-- `Core` at `mkSeams Checked`. -/
theorem core_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Core (mkSeams Checked) :=
  Core.core_S₀

/-- Obligation `L4` at `mkSeams Checked`. -/
theorem l4_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.L4 (mkSeams Checked) :=
  fun _ _ _ => Core.core_S₀

/-- `ClaimPhase` at `mkSeams Checked`. -/
theorem claimPhase_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.ClaimPhase (mkSeams Checked) :=
  Claim.claimPhase_L6 defaultAdmits

/-- Obligation `L6` at `mkSeams Checked`. -/
theorem l6_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.L6 (mkSeams Checked) :=
  fun _ => claimPhase_mkSeams Checked

/-- **`IxVM.consistent` reduced to `Decls` (`L5`) and `L7`** over `mkSeams Checked`. -/
theorem consistent_of_decls_l7
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop)
    (decls : IxVM.Consistency.Decls.{u} (mkSeams Checked))
    (h7 : IxVM.Consistency.L7.{u} (mkSeams Checked)) :
    IxVM.Consistency.CircuitConsistent.{u} :=
  IxVM.consistent (mkSeams Checked)
    IxVM.Consistency.l0
    (l1_mkSeams Checked)
    Levels.l2
    (l3_mkSeams Checked)
    (l4_mkSeams Checked)
    (fun _ _ _ _ => decls)
    (l6_mkSeams Checked)
    h7

/-! ## Bridging `L6` check witnesses with `L1` under `Bounded` -/

/-- Under `Bounded calls`, a block-member check witness `MutsMemberCheckedAtFull` at index `k` of
`ms` (`ms[k]? = some mc`) yields a standalone `CheckedAtFull` witness at the member's projection
record address `Core.projAddr (Core.Specs.Callees.memberProjInfo addr k mc)`. -/
theorem mutsMemberCheckedAtFull_to_checkedAtFull
    {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {addr : _root_.Address}
    {ms : Array Ixon.MutConst} {k : Nat} {mc : Ixon.MutConst}
    (hbound : IxVM.Consistency.Bounded calls)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t addr ms k)
    (hk : ms[k]? = some mc) :
    Claim.CheckedAtFull calls bAddr t
      (Core.projAddr (Core.Specs.Callees.memberProjInfo addr k mc)) := by
  refine hm.toCheckedAtFull ?_
  intro h_pa h_pre x_members x_block ap cs_pa hmem hblk ev_pa hcl_pa _hsub_pa
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem
  have hk_lt : k < ms.toList.length := by
    have hk_sz : k < ms.size := (Array.getElem?_eq_some_iff.mp hk).1
    simpa using hk_sz
  have hk_val : ((k : F)).val = k :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨_, _, _, mc', a', hget', ha', hproj⟩ := L1.projection_addr_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  exact ⟨a', ha', hproj⟩

/-- Under `Bounded calls`, a `CheckedAtFull` witness at address `a` pairs its `Ingress::get_ci`
sub-derivation with `L1.get_ci_loadedL1_spec` to produce `LoadedL1` alongside the
`KernelCheck::check_const` call on the loaded heap value. -/
theorem checkedAtFull_loadedL1
    {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (hbound : IxVM.Consistency.Bounded calls)
    (hc : Claim.CheckedAtFull calls bAddr t a) :
    ∃ (lim : Nat) (h_pre m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
      (cs_load cs_chk : List (Call F)) (bytes : ByteArray) (E_ld : Ixon.Env),
      Claim.RCFullRep t bAddr lim h_pre rc ∧
      Claim.RCFullRep t bAddr lim m_chk rc ∧
      Core.S0.addr h_pre ap a ∧
      Core.S0.addr m_chk ap a ∧
      Hashed cs_load bytes ∧
      Address.blake3Pure bytes = a ∧
      IxVM.Consistency.LoadedBy cs_load E_ld ∧
      L1.LoadedL1 E_ld m_chk ptr bytes ∧
      (∀ cl ∈ cs_load, cl ∈ calls) ∧
      loadValue m_chk ptr = .ok v ∧
      ObsFn Core.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
      (⟨"KernelCheck::check_const", [rc, v, ap], m_chk⟩ : Call F) ∈ calls ∧
      (∀ cl ∈ cs_chk, cl ∈ calls) := by
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, _hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hc
  obtain ⟨a', ha'_ref, rfl⟩ := ha_pre
  have hbound_ld : IxVM.Consistency.Bounded cs_load := RomBound.bounded_mono hbound hsub_ld
  obtain ⟨_ext, bytes, E_ld, hhash, hblake, hloaded, hL1⟩ :=
    L1.get_ci_loadedL1_spec hbound_ld ha'_ref ev_ld
  exact ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, bytes, E_ld,
    hrc_pre, hrc_m, ⟨a', ha'_ref, rfl⟩, ha_m,
    hhash, hblake, hloaded, hL1, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩

end IxVM.Refinement.Assembly
