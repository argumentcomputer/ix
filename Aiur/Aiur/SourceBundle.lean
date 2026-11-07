module
public import Init.System.IO

public section

/-! Filesystem composition for applications. Imports are deliberately outside
the Aiur AST: the existing frontend receives ordinary module declarations.
The same contents are used by compilation and the application's cache key. -/
namespace Aiur.SourceBundle

/-- Read an ordered `.sources` manifest. Paths are relative to the manifest;
blank lines and `#` comments are ignored. -/
def read (manifest : System.FilePath) : IO String := do
  let directory := manifest.parent.getD "."
  let mut result := ""
  let mut seen : List String := []
  for raw in (← IO.FS.readFile manifest).splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    if seen.contains line then
      throw (IO.userError s!"duplicate source '{line}' in {manifest}")
    seen := line :: seen
    result := result ++ s!"// Source: {line}\n" ++ (← IO.FS.readFile (directory / line)) ++ "\n"
  if seen.isEmpty then throw (IO.userError s!"empty source bundle {manifest}")
  return result

end Aiur.SourceBundle
