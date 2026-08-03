module

/-!
Circuit-grouping data for the IxVM kernel toplevel, applied wherever the
kernel is compiled for proving or verifying (see
`CompiledToplevel.groupFunctions`). Empty = no grouping: every constrained
function keeps its singleton circuit. Fill from measured workload
statistics; a stale grouping stays sound (grouping never affects
semantics), only less efficient.
-/

public section

namespace IxVM

def coldGroups : Array (String × Array String) := #[]

end IxVM

end
