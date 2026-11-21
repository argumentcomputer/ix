module

public section

namespace Tests.IxonPaths

/-- Environment variable naming the scratch directory of the Ixon test
executables. `ixon-primitives` writes the primitive closure there and
`ixon-tests --primitives` reads it back; `--export-fixtures` writes
under it. Unset, it is `/tmp`; checkouts that run
these executables at the same time should each set their own directory. -/
def scratchDirVar : String := "IX_IXON_TEST_DIR"

/-- The scratch directory: `$IX_IXON_TEST_DIR`, or `/tmp`. -/
def scratchDir : IO System.FilePath :=
  return System.FilePath.mk ((← IO.getEnv scratchDirVar).getD "/tmp")

/-- The primitive address table written by `ixon-primitives`. -/
def primitivesTsv (dir : System.FilePath) : System.FilePath :=
  dir / "ixon-primitives.tsv"

/-- The primitive closure written by `ixon-primitives` and validated by
`ixon-tests --primitives`. -/
def primitivesIxe (dir : System.FilePath) : System.FilePath :=
  dir / "ixon-primitives.ixe"

/-- Where `ixon-tests --export-fixtures` writes the generated text fixtures. -/
def fixtureExportDir (dir : System.FilePath) : System.FilePath :=
  dir / "ixon-fixtures"

/-- The scratch-directory paragraph of both executables' usage text. -/
def scratchUsage : String :=
  s!"Scratch files live in ${scratchDirVar} (default /tmp): ixon-primitives.tsv
and ixon-primitives.ixe from ixon-primitives, read back by
ixon-tests --primitives; ixon-fixtures/ from --export-fixtures. Set {scratchDirVar} when two checkouts run these at the same time."

end Tests.IxonPaths

end
