import Ix.IxVM.Consistency.CircuitToSource
import IxVMRefinement.Levels.Spec
import IxVMRefinement.Subst.Steps
import IxVMRefinement.Core.AllSteps
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Ingress.Records
import IxVMRefinement.Claim.ClaimSeam

/-! # Seams assembly for circuit-to-source, ingress, levels, terms, core, and claim obligations

Combines the verified circuit-to-source (`CircuitToSource`), record-ingress (`RecordIngress`),
universe-level (`LevelsObligation`), term-substitution (`TermsObligation`), core-typing
(`CoreObligation`), and claim/role-walk (`ClaimObligation`) obligations over any declaration-check
seam `Checked`:

* `mkSeams Checked`: equips `Core.baseSeams` with `Ingress.LoadedRecords`, `Claim.WalkedClaim`, and `Checked`,
  sharing `addr`, `Ghost`, `term`, and `ctx` definitionally with `Core.baseSeams` so `RecordIngress`,
  `TermsObligation`, `CoreObligation`, and `ClaimObligation` transfer with zero re-elaboration;
* `defaultTableBytesUnfolds` and `defaultAdmits`: unconditional admission of the committed default
  role table via `Ix.Kernel.Reader.defaultTableBytesOf`;
* `consistent_of_decls_assembly`: reduces `IxVM.Consistency.CircuitConsistent` to `Decls (mkSeams Checked)`
  and `AssemblyObligation (mkSeams Checked)`;
* `mutsMemberCheckedAtFull_to_checkedAtFull` and `checkedAtFull_loadedRecords`: bridges block-member
  and standalone `CheckedAtFull` witnesses from the claim phase with `Ingress.projection_addr_spec` and
  `Ingress.get_ci_loadedRecords_spec` under `Bounded calls`. -/

universe u

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- Seams bundle equipping `Core.baseSeams` with `Ingress.LoadedRecords`, `Claim.WalkedClaim`, and a chosen
declaration-check seam `Checked`. -/
def mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Seams :=
  { Core.baseSeams with
    loaded := Ingress.LoadedRecords
    Walked := Claim.WalkedClaim
    Checked := Checked }

/-! ## Unconditional default role-table admission -/

/-- `Ix.Kernel.Reader.defaultTableBytes` unfolds via `Ix.Kernel.Reader.defaultTableBytesOf` to
`Claim.defaultTableBytesOf RoleData.table` without reducing `bytesOfHex RoleData.table`. -/
theorem defaultTableBytesUnfolds : Claim.DefaultTableBytesUnfolds :=
  Claim.defaultTableBytesUnfolds_of_fn Ix.Kernel.Reader.defaultTableBytesOf (fun _ => rfl) rfl

/-- The committed default role table admits under `Address.admissionHash`. -/
theorem defaultAdmits : Ix.Cert.RoleClosure.DefaultAdmits :=
  Claim.defaultAdmits_of_unfolds defaultTableBytesUnfolds

/-! ## Layer obligations at `mkSeams Checked` -/

/-- `Records` at `mkSeams Checked`. -/
theorem records_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Records (mkSeams Checked) :=
  Ingress.records_ingress

/-- `RecordIngress` at `mkSeams Checked`. -/
theorem recordIngress_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.RecordIngress (mkSeams Checked) :=
  Ingress.records_ingress

/-- `Terms` at `mkSeams Checked`. -/
theorem terms_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Terms (mkSeams Checked) :=
  Core.terms_baseSeams

/-- `TermsObligation` at `mkSeams Checked`. -/
theorem termsObligation_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.TermsObligation (mkSeams Checked) :=
  fun _ => Core.terms_baseSeams

/-- `Core` at `mkSeams Checked`. -/
theorem core_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.Core (mkSeams Checked) :=
  Core.core_baseSeams

/-- `CoreObligation` at `mkSeams Checked`. -/
theorem coreObligation_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.CoreObligation (mkSeams Checked) :=
  fun _ _ _ => Core.core_baseSeams

/-- `ClaimPhase` at `mkSeams Checked`. -/
theorem claimPhase_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.ClaimPhase (mkSeams Checked) :=
  Claim.claimPhase_claimSeams defaultAdmits

/-- `ClaimObligation` at `mkSeams Checked`. -/
theorem claimObligation_mkSeams
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) :
    IxVM.Consistency.ClaimObligation (mkSeams Checked) :=
  fun _ => claimPhase_mkSeams Checked

/-- **`IxVM.consistent` reduced to `Decls` and `AssemblyObligation`** over `mkSeams Checked`. -/
theorem consistent_of_decls_assembly
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop)
    (decls : IxVM.Consistency.Decls.{u} (mkSeams Checked))
    (hAssembly : IxVM.Consistency.AssemblyObligation.{u} (mkSeams Checked)) :
    IxVM.Consistency.CircuitConsistent.{u} :=
  IxVM.consistent (mkSeams Checked)
    IxVM.Consistency.circuitToSource
    (recordIngress_mkSeams Checked)
    Levels.levelsObligation
    (termsObligation_mkSeams Checked)
    (coreObligation_mkSeams Checked)
    (fun _ _ _ _ => decls)
    (claimObligation_mkSeams Checked)
    hAssembly

/-! ## Bridging claim-phase check witnesses with record ingress under `Bounded` -/

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
  obtain ⟨_, _, _, mc', a', hget', ha', hproj⟩ := Ingress.projection_addr_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  exact ⟨a', ha', hproj⟩

/-- Under `Bounded calls`, a `CheckedAtFull` witness at address `a` pairs its `Ingress::get_ci`
sub-derivation with `Ingress.get_ci_loadedRecords_spec` to produce `LoadedRecords` alongside the
`KernelCheck::check_const` call on the loaded heap value. -/
theorem checkedAtFull_loadedRecords
    {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (hbound : IxVM.Consistency.Bounded calls)
    (hc : Claim.CheckedAtFull calls bAddr t a) :
    ∃ (lim : Nat) (h_pre m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
      (cs_load cs_chk : List (Call F)) (bytes : ByteArray) (E_ld : Ixon.Env),
      Claim.RCFullRep t bAddr lim h_pre rc ∧
      Claim.RCFullRep t bAddr lim m_chk rc ∧
      Core.BaseSeams.addr h_pre ap a ∧
      Core.BaseSeams.addr m_chk ap a ∧
      Hashed cs_load bytes ∧
      Address.blake3Pure bytes = a ∧
      IxVM.Consistency.LoadedBy cs_load E_ld ∧
      Ingress.LoadedRecords E_ld m_chk ptr bytes ∧
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
    Ingress.get_ci_loadedRecords_spec hbound_ld ha'_ref ev_ld
  exact ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, bytes, E_ld,
    hrc_pre, hrc_m, ⟨a', ha'_ref, rfl⟩, ha_m,
    hhash, hblake, hloaded, hL1, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩

end IxVM.Refinement.Assembly
