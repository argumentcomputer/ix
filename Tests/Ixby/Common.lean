module
public import LSpec

/-! Shared LSpec reporting for IxBy checks. Test construction is an IO action,
so importing a suite does not evaluate its fixtures before suite selection. -/

public section

namespace Tests.Ixby

abbrev Check := String × Bool

def succeeds (label : String) (result : Except String α) : Check :=
  match result with
  | .ok _ => (label, true)
  | .error error => (s!"{label}: {error}", false)

def checkSeq (checks : List Check) : LSpec.TestSeq :=
  checks.foldl (fun seq (label, ok) => seq ++ LSpec.test label ok) .done

def runChecks (name : String) (checks : IO (List Check)) : IO UInt32 := do
  let checks ← checks
  LSpec.lspecIO (.ofList [(name, [checkSeq checks])]) []

end Tests.Ixby
