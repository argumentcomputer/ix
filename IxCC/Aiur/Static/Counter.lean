import Ix.Aiur.Compiler.UnitCounter

namespace IxCC.Aiur.Static

open _root_.Aiur (G)
open _root_.Aiur.Bytecode

def counterObservation (candidate : UnitCounter.Certificate) (inputs outputs : List G) : Option G :=
  match candidate.mode with
  | .input => inputs[candidate.column]?
  | .output => outputs[candidate.column]?

def normalizeCounter (candidate : UnitCounter.Certificate) (value : G) : G :=
  let negate := match candidate.mode with
    | .input => candidate.step != 1
    | .output => candidate.step == 1
  if negate then 0 - value else value

/-- Total observation used to assign facts. Provider binding separately
requires the selected column to exist for every active nonzero counter row. -/
def normalizedCounter (candidate : UnitCounter.Certificate) (inputs outputs : List G) : G :=
  normalizeCounter candidate ((counterObservation candidate inputs outputs).getD 0)

def CounterStep (candidate : UnitCounter.Certificate) (parent child : G) : Prop :=
  match candidate.mode with
  | .input => child = parent + candidate.step
  | .output => parent = child + candidate.step

end IxCC.Aiur.Static
