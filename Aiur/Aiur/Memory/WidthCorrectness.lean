import Aiur.Memory.Partition
import Aiur.Optimized.Equivalence

namespace Aiur.WidthROM

variable {F : Type} [Field F] [DecidableEq F]
  {program : Program F} {entries : List String} {config : Optimized.Config}
  {artifact : Optimized.Artifact F}

/-- The optimized compiler's entry soundness applies to untyped width-local
memory through static typed views. In particular, result canonicality follows
from the existing store-provenance induction without a tag in the ROM trace.
As with the compiler theorem, this assumes a finite derivation; the STARK
lookup argument itself is outside the Lean model. -/
theorem compiler_entry_sound
    (compiled : Optimized.compile program entries config = .ok artifact)
    {rom : WidthROM F} (valid : rom.Valid) (types : List Ty)
    {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (free : root.PublicArguments program.enums)
    (derived : Circuit.Derives artifact.system (rom.toWireROM program.enums types) root) :
    root.Evaluates program (rom.toWireROM program.enums types) :=
  Optimized.compiler_entry_sound compiled entry (rom.toWireROM_valid valid program.enums types) free derived

/-- Erasing the physical ROM's types preserves the equivalence between the
reference compiler and all optimized layout passes, for finite entry proofs. -/
theorem reference_derives_iff
    {reference : Circuit.System F} (original : Circuit.compile program = .ok reference)
    (compiled : Optimized.compile program entries config = .ok artifact)
    {rom : WidthROM F} (valid : rom.Valid) (types : List Ty)
    {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (free : root.PublicArguments program.enums) :
    Circuit.Derives reference (rom.toWireROM program.enums types) root ↔
      Circuit.Derives artifact.system (rom.toWireROM program.enums types) root :=
  Optimized.reference_derives_iff original compiled entry
    (rom.toWireROM_valid valid program.enums types) free

end Aiur.WidthROM
