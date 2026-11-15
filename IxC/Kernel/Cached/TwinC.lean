module

public import IxC.Kernel.Inductives.TwinInstall
public import IxC.Kernel.Cached.CheckerC

@[expose] public section

/-! # Cached phases for stored recursor twins

Header checks use the original index. Rule annotations use a fresh index of the entire
provisioned group. The final cache is cleared after checked rules replace provisional ones.
-/

namespace Ix.Kernel.Cached

def checkTwinS (mode : CheckMode) (fe : FEnv md) (block : List (ConstantInfo md)) :
    CheckCM md (FEnv md) := do
  flushC
  let parts ← NativeTwin.prepare (sharedOpsC mode fe) fe.env block
  let envSelf := NativeTwin.selfEnv fe.env parts
  let feSelf := mkFEnv envSelf
  flushC
  let checked ← NativeTwin.checkPartsRules (sharedOpsC mode feSelf) fe.env envSelf parts
  let envOut ← NativeTwin.finish fe.env checked
  flushC
  pure (mkFEnv envOut)

end Ix.Kernel.Cached
