import IxVMRefinement.Assembly.NativeBlockTableOf
import IxVMRefinement.Guard.ProjGuardFires

/-! # The firing of a native block's new projection table, from its certificate

`BlockFire` (`NativeBlockTableOf.lean`) is what the load contract after a native block's install
asks of the family's new projection table: where the family's sort passes the zero test, the
table fires at every context over the role table and the store.

* `BlockCert t E env₂ B`: the certificate of the new table, over the step's store: where the
  environment after the install stores the family's table and its sort passes the zero test, it
  stores the family's first constructor, the store reads that constructor's raw telescope, the
  table's level parameters are positions, and the table has its certificate
  (`Ix.Kernel.ProjGuardCert`) over the store's raw dictionary. It is the premise `hcert` of
  `foldExtra_nativeNoRec` at the block's one member.
* `blockFire_of_cert`: the certificate and the reading of a `proj_guard` run
  (`Core.ProjGuardRunReading`) give `BlockFire`. The member's projection record is the one the
  install read (`BlockInstall.formerRec`); the store decodes its records.
-/

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option linter.unusedVariables false

/-- **The certificate of the family's new projection table**, over the step's store (module
docstring). No limit occurs. -/
def BlockCert (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env₂ : Ix.Kernel.Env .anon)
    (B : _root_.Address) : Prop :=
  ∀ tbl : Ix.Kernel.ProjTable .anon,
    env₂.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) =
      some (.projInfo tbl) →
    Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
    ∃ (cvC : ConstantVal .anon) (nP nF : Nat) (raw : Ix.Kernel.Expr .anon),
      env₂.find? (Core.keyOf t (Core.cprjAddr B 0 0)) = some (.ctorInfo cvC nP nF) ∧
      Guard.ctorRaw E B 0 0 = some raw ∧
      tbl.levelParams = List.range tbl.levelParams.length ∧
      Ix.Kernel.ProjGuardCert (GuardRaw.ofStore E) raw cvC.type tbl

/-- **The new table fires, from its certificate and the reading of a run** (module
docstring). -/
theorem blockFire_of_cert (hread : Core.ProjGuardRunReading) {c : Core.Ctx}
    {new : List (ConstantInfo .anon)} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {caps : IndCaps .anon}
    (hI : BlockInstall c new B cb ind caps)
    (hcert : BlockCert c.t c.E (appCtx c new).env B) : BlockFire c new B := by
  intro tbl htbl hprop
  obtain ⟨cvC, nP, nF, raw, hctor, hraw, hpos, cert⟩ := hcert tbl htbl hprop
  exact ⟨cvC, nP, nF, hctor,
    Guard.projTableFires_of_cert_at hread hI.decoded ⟨_, hI.formerRec, rfl, by decide⟩ hraw hpos cert⟩

end IxVM.Refinement.Typing
