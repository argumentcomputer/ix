module

/-!
Circuit-grouping data for the recursive-verifier toplevel, applied wherever
it is compiled for proving or verifying (see
`CompiledToplevel.groupFunctions`). Empty = no grouping: every constrained
function keeps its singleton circuit. Fill from measured workload
statistics; a stale grouping stays sound (grouping never affects
semantics), only less efficient.
-/

public section

namespace MultiStark

def verifierColdGroups : Array (String × Array String) := #[]

end MultiStark

end
