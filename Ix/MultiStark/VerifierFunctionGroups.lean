module

/-!
Function-grouping data for the standalone Multi-STARK verifier toplevel
(`MultiStark.multiStark`), applied wherever it is compiled for proving or
verifying (see `CompiledToplevel.groupFunctions`). Empty = no grouping:
every constrained function keeps its singleton circuit. Fill from measured
workload statistics; a stale grouping stays sound (grouping never affects
semantics), only less efficient.
-/

public section

namespace MultiStark

def verifierFunctionGroups : Array (String × Array String) := #[]

end MultiStark

end
