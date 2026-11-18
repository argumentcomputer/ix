import IxVMRefinement.Assembly.NativeBlockUnitStep
import IxVMRefinement.Assembly.NativeAliasWalked
import IxVMRefinement.Endpoint.WalkedUnit

/-! # The walked unit of a block whose former is declared at its telescope

The composed statement takes, for each kind of top-walked unit, the unit's step for the fold's
clause from the facts the walk hands every unit (`Endpoint.WalkedUnitStep`). This module proves
that obligation for a one-type native block whose former is declared at its telescope, the
ordinary inductive type, from two premises about the projection guard:

* `Core.ProjGuardRunReading`: the reading of a projection guard's run;
* `InstalledTableCertified`: where such a block has one constructor, no index and a sort that
  tests zero, the projection table its install stores has its certificate over the step's
  store. It is asked of every output of the install read off the walk's member check, with
  every fact the walk hands the unit and the kind's three facts.

`nativeBlockTelescope_walked` is the obligation of the composed statement for this kind of
unit, for any link that satisfies the link laws, at the walk's limit under either validator.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (NativeFam)

/-- **The projection table a structure-like proposition's install stores is certified**
(module docstring). For a run, a role table, the run's store, a store a step runs against, and
a one-type native block whose former is declared at its telescope, with the member's check
under the role context at `lim`: at one constructor and no index, every output of the install
whose family's sort tests zero has the certificate of its new projection table over the step's
store. The limit index of the output is any. -/
def InstalledTableCertified : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (lim : Option Nat) (B : _root_.Address) (cb : Ixon.Constant)
    (ind : Ixon.Inductive),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepStore calls t E₀ E →
    L1.CanonicalHashCoverage E calls → BlockUnitRecord E₀ B cb ind →
    Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim →
    NativeRouteAt calls B → FormerAtTele t E₀ B cb ind →
    ind.ctors.size = 1 → ind.indices.toNat = 0 →
    ∀ (n : Nat) (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
      (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
      (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
      Ix.Kernel.Level.isEquiv p.resSort .zero = some true →
      BlockCert t E ⟨new ++ env.consts⟩ B

/-- **The step of every top-walked one-type native block whose former is declared at its
telescope keeps the fold's clause**, at the walk's limit under either validator, for any link
that satisfies the link laws, from the two premises about the projection guard (module
docstring). A block record is never checked as a record, so the walk checked the member. -/
theorem nativeBlockTelescope_walked {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hread : Core.ProjGuardRunReading) (hcert : InstalledTableCertified) :
    Endpoint.WalkedUnitStep.{u} (FoldExtra.{u} L) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx B cb hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ind, hrec, hnat, htele⟩ := hkind
  have hmem : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    memberChecked_of_walked_block hS hc hrec.muts hchk 0 (by simp)
  exact unitStep_nativeBlockTele hL ht hS hst hrec hmem hnat htele hkeys hinert hcover hcanon
    hread (fun h1 h0 n env new blk p₀ p ty' ctorsA caps hO hz =>
      hcert calls bAddr t E₀ E lim B cb ind ht hS hst hcanon hrec hmem hnat htele h1 h0 n env new
        blk p₀ p ty' ctorsA caps hO hz)

end IxVM.Refinement.Typing
