import Ix.Resource.Validate

namespace Tests.ResourceTransportFixtures
open Ix Ix.Resource

def cases : Array (String × String × Option String) := #[
  ("bridge-bad", "3a3b136bebf70228abeb5e8b6c40ce127d9f204807333b2eaaae5c4a4070497c", some "Ix.Resource.Error.sharedToUnique"),
  ("bridge-good", "3a3b136bebf70228abeb5e8b6c40ce127d9f204807333b2eaaae5c4a4070497c", none),
  ("recursion-zero", "cbd928242de3d2ddc78e84caf86152cf22ca15e77b5bb679029f35ebb862c5e0", none),
  ("recursion-succ", "5cd663ef2216856ff1ba728c924675056dfa9219b655694711c54f6812a26b35", none)]

def runCases (directory : System.FilePath)
    (cases : Array (String × String × Option String)) : IO Unit := do
  for (name, expectedProfile, expectedError) in cases do
    let env ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv
      (← IO.FS.readBinFile (directory / (name ++ ".ixe"))))
    let profile ← IO.ofExcept (Profile.ofBytes
      (← IO.FS.readBinFile (directory / (name ++ ".profile"))))
    unless toString (← IO.ofExcept profile.address) == expectedProfile do
      throw (IO.userError s!"transport fixture {name}: profile address changed")
    let result := Ix.Resource.validate env profile
    let passes := match result, expectedError with
      | .ok _, none => true
      | .error message, some expected => message.endsWith expected
      | _, _ => false
    unless passes do
      let detail := match result with | .error e => e | .ok _ => "accepted"
      throw (IO.userError s!"transport fixture {name}: expected {repr expectedError}, got {detail}")
    IO.println s!"Transport full gate: {name} passed"

def run (directory : System.FilePath := "Tests/Fixtures/ixon-v4/transport") : IO Unit :=
  runCases directory cases

end Tests.ResourceTransportFixtures
