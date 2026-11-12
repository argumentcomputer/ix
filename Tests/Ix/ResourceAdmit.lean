module

public import Ix.Resource.Admit

public section

namespace Tests.Resource

open Ixon Ix.Resource

/-- Budget exhaustion is an error, including cycles through open sharing. -/
def checkSharingBudget : IO Unit := do
  let cyclic : Program := { declarations := #[{ type := .sort 0 }], sharing := #[.share 0] }
  let action := analyze 20 { program := cyclic } (.share 0) none 0 .linear
  match action.run {} with
  | .error .budget _ => pure ()
  | _ => throw <| IO.userError "cyclic sharing did not exhaust the bound"

/-- Relevance walks a shared DAG as a DAG, and refuses cyclic sharing. -/
def runAdmission : IO Unit := do
  let mut sharing : Array Ixon.Expr := #[.sort 0]
  for i in [:40] do
    sharing := sharing.push (.app (.share i.toUInt64) (.share i.toUInt64))
  let dag : Program := { declarations := #[{ type := .sort 0, body := some (.share 40) }], sharing }
  unless (relevance dag { depth := 1, steps := 200 }).toOption == some #[false] do
    throw <| IO.userError "relevance expanded a shared DAG as a tree"
  let cyclic := { dag with sharing := #[.share 0], declarations := #[{ type := .sort 0, body := some (.share 0) }] }
  unless (relevance cyclic).toOption.isNone do throw <| IO.userError "cyclic sharing was admitted"
  checkSharingBudget
  IO.println "Resource admission: 3 DAG, cycle and budget checks passed"

end Tests.Resource

end
