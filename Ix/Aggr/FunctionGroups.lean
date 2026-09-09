module

/-!
Function-grouping data for the production aggregation toplevel
(`Aggr.ixAggr`), applied wherever it is compiled for proving or verifying
(see `CompiledToplevel.groupFunctions`). Empty = no grouping: every
constrained function keeps its singleton circuit. Fill from measured
workload statistics; a stale grouping stays sound (grouping never affects
semantics), only less efficient.
-/

public section

namespace Aggr

def functionGroups : Array (String × Array String) := #[]

end Aggr

end
