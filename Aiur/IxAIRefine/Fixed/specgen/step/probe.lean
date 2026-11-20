import IxAIRefine.Program
open IxAIStep.Fixed
#eval functionNames
#eval maps.map (·.name)
#eval program.tables.map (fun t => (t.name, t.rows.length))
#eval consts.length
#eval program.functions.map (fun f => (f.name, f.typeParams, f.params.map (·.1)))
