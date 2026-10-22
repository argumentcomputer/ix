import Aiur.Circuit.Basic
import Aiur.Scalar.Circuit.Degree

namespace Aiur.Circuit

namespace ArithExpr
abbrev degree (expr : ArithExpr F) : Nat := Scalar.Circuit.ArithExpr.degree expr

/-- Zero for an empty list of expressions. -/
def maxDegree (expressions : List (ArithExpr F)) : Nat :=
  expressions.foldl (fun largest expr => max largest expr.degree) 0
end ArithExpr

/-- Includes arguments, result columns, and the enable expression. This is the
largest expression degree, not the degree of a future lookup protocol gadget. -/
def Send.maxDegree (send : Send F) : Nat :=
  max (ArithExpr.maxDegree (send.enable :: send.args.flatMap WireValue.words))
    (if send.result.words.isEmpty then 0 else 1)

/-- Includes the address, payload words, and enable expression. -/
def MemoryLookup.maxDegree (lookup : MemoryLookup F) : Nat :=
  ArithExpr.maxDegree (lookup.enable :: lookup.address :: lookup.value.words)

/-- Static costs of one chip row, independent of any assignment or trace. -/
structure ChipStats where
  name : String
  /-- All allocated field columns; provided expressions need no dedicated columns. -/
  columns : Nat
  maxConstraintDegree : Nat
  /-- Function and map sends, counted with repetitions and inactive slots. -/
  callLookups : Nat
  /-- Store/load requirements, counted with repetitions and inactive slots. -/
  romLookups : Nat
  /-- Includes the provided input/output expressions as well as required lookups. -/
  maxLookupDegree : Nat
  deriving Repr, BEq, DecidableEq

/-- Required lookup slots; the chip's own provided conclusion is not a lookup. -/
def ChipStats.lookups (stats : ChipStats) : Nat := stats.callLookups + stats.romLookups

def Chip.stats (chip : Chip F) : ChipStats := {
  name := chip.name
  columns := chip.numVars
  maxConstraintDegree := ArithExpr.maxDegree chip.constraints
  callLookups := chip.sends.length
  romLookups := chip.memory.length
  maxLookupDegree := max
    (max (ArithExpr.maxDegree chip.output.words)
      (if (chip.inputs.flatMap WireValue.words).isEmpty then 0 else 1))
    (max ((chip.sends.map Send.maxDegree).foldl max 0)
      ((chip.memory.map MemoryLookup.maxDegree).foldl max 0))
}

/-- Guards remain affine even when mutually exclusive payloads are combined. -/
def Chip.maxLookupGuardDegree (chip : Chip F) : Nat :=
  ArithExpr.maxDegree (chip.sends.map Send.enable ++ chip.memory.map MemoryLookup.enable)

/-- One record per chip, preserving circuit order. Static maps have no chip. -/
def System.stats (system : System F) : List ChipStats := system.chips.map Chip.stats

def ChipStats.format (stats : ChipStats) : String :=
  s!"{stats.name}: columns={stats.columns}, max constraint degree={stats.maxConstraintDegree}, " ++
  s!"lookups={stats.lookups} (calls={stats.callLookups}, ROM={stats.romLookups}), " ++
  s!"max lookup degree={stats.maxLookupDegree}"

def System.formatStats (system : System F) : String :=
  if system.chips.isEmpty then "No chips."
  else String.intercalate "\n" (system.stats.map ChipStats.format)

/-- Print the per-chip report; no field operations or witness rows are needed. -/
def System.printStats (system : System F) : IO Unit := IO.println system.formatStats

end Aiur.Circuit
