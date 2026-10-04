import Tests.Ix.ResourceTransportFixtures

namespace Tests.ResourceTransportBetaFixtures

def cases : Array (String × String × Option String) := Id.run do
  let profile := "3a3b136bebf70228abeb5e8b6c40ce127d9f204807333b2eaaae5c4a4070497c"
  let witness := some "Ix.Resource.Error.sharedToUnique"
  let typing := some "Ix.Resource.Error.typeMismatch"
  return #[
    ("hiddenBad", profile, witness), ("hiddenGood", profile, none),
    ("deadBad", profile, none),
    ("changedInput", profile, typing), ("changedResult", profile, typing),
    ("matchingResult", profile, none), ("dependentGood", profile, none),
    ("aliasGood", profile, none), ("proofLetBad", profile, witness),
    ("directProofBad", profile, witness), ("directProofGood", profile, none),
    ("computationalBad", profile, witness), ("computationalGood", profile, none)]

def run (directory : System.FilePath := "Tests/Fixtures/ixon-v4/transport/beta") : IO Unit :=
  Tests.ResourceTransportFixtures.runCases directory cases

end Tests.ResourceTransportBetaFixtures
