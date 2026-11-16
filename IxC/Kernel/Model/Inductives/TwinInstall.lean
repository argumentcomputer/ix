module

public import IxC.Kernel.Verify.Inductives.TwinRun
public import IxC.Kernel.Model.Inductives.DeclRecTwin

public section

/-! # Model preservation for executable stored-recursor twin checks -/

namespace Ix.Kernel.Model

universe u

variable {V : Type u} [SetTheory V]

/-- The actual pure twin checker extends the model using its checked headers, provisioned
rule environment, and common canonical-rule renaming. -/
theorem checkTwin_model {mode : CheckMode} {fuel : Nat} {env output : Env md}
    {block : List (ConstantInfo md)} (hmode : mode.verifiedChecks = true)
    (model : EnvModelM V mode env)
    (checked : NativeTwin.check (fueledOps mode fuel) env block = .ok output) :
    ∃ result : EnvModelM V mode output, ModelExt model result :=
  declRecTwinJ (fun _ => judgeFrames_runJ fuel) (fun m => judgeSound_runJ hmode m fuel)
    model (NativeTwin.check_semantic checked)

end Ix.Kernel.Model
