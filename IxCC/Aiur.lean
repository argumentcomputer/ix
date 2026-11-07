import Ix.Aiur.Stages.Bytecode
import IxCC.Aiur.Certificate
import IxCC.Aiur.Wire
import IxCC.Aiur.OracleEval
import IxCC.Aiur.BytecodeSound
import IxCC.Aiur.Static
import IxCC.Aiur.AIR.Memory
import IxCC.Aiur.AIR.Rank

/-! Pinned Aiur definitions, addressed bytecode ingress, and checked local
rows and static assignments yielding witness-heap executions.
Source/DSL lowering and extraction from the keyed AIR remain subsequent stages. -/
