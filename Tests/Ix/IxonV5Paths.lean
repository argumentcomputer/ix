module

public section

namespace Tests.IxonV5

/-- Environment variable naming the scratch directory of the Ixon v5 test
executables. `ixon-v5-primitives` writes the primitive closure there and
`ixon-v5-tests --primitives` reads it back; `--export-fixtures` and
`--export-handoff` write under it. Unset, it is `/tmp`; checkouts that run
these executables at the same time should each set their own directory. -/
def scratchDirVar : String := "IX_IXON_V5_DIR"

/-- The scratch directory: `$IX_IXON_V5_DIR`, or `/tmp`. -/
def scratchDir : IO System.FilePath :=
  return System.FilePath.mk ((← IO.getEnv scratchDirVar).getD "/tmp")

/-- The primitive address table written by `ixon-v5-primitives`. -/
def primitivesTsv (dir : System.FilePath) : System.FilePath :=
  dir / "ixon-v5-primitives.tsv"

/-- The primitive closure written by `ixon-v5-primitives` and validated by
`ixon-v5-tests --primitives`. -/
def primitivesIxe (dir : System.FilePath) : System.FilePath :=
  dir / "ixon-v5-primitives.ixe"

/-- Where `ixon-v5-tests --export-fixtures` writes the generated text fixtures. -/
def fixtureExportDir (dir : System.FilePath) : System.FilePath :=
  dir / "ixon-v5-fixtures"

/-- Where `ixon-v5-tests --export-handoff` writes the handoff artifacts. -/
def handoffExportDir (dir : System.FilePath) : System.FilePath :=
  dir / "ixon-v5-handoff"

/-- The scratch-directory paragraph of both executables' usage text. -/
def scratchUsage : String :=
  s!"Scratch files live in ${scratchDirVar} (default /tmp): ixon-v5-primitives.tsv
and ixon-v5-primitives.ixe from ixon-v5-primitives, read back by
ixon-v5-tests --primitives; ixon-v5-fixtures/ and ixon-v5-handoff/ from the
export flags. Set {scratchDirVar} when two checkouts run these at the same time."

end Tests.IxonV5

end
