module

public import Ix.IxVM.RoleSpecGen

/-! The rendered circuit specification and the specification digest cannot
drift apart. `IxVM/IxVM/Source/KernelRoleSpec.lean` is rebuilt from the bytes
the digest hashes (`IxVM.RoleSpecGen.checkRendering`): the checked-in file
must pass, and each mutation below, of the bytes or of the file, must be
refused. `ix codegen --check` runs the same rebuild on every PR
(`tools/ixvm/check-formal.sh`); this suite also shows that it can fail. -/

public section

namespace Tests.Ix.SpecDigestRendering

open Ix.Kernel

def renderedPath : System.FilePath := "IxVM/IxVM/Source/KernelRoleSpec.lean"

/-- `xs` with its first two entries swapped. -/
def swapFirstTwo {α : Type} : List α → List α
  | a :: b :: rest => b :: a :: rest
  | xs => xs

/-- `s` with `old` replaced once, or an error when `old` does not occur. -/
def replaceOnce (s old new : String) : Except String String := do
  match s.splitOn old with
  | [pre, post] => pure (pre ++ new ++ post)
  | parts => throw s!"the mutation's text occurs {parts.length - 1} times, not once"

/-- The mutations: each a name and the bytes and file to check. -/
def mutations (bytes : ByteArray) (file : String) :
    Except String (List (String × ByteArray × String)) := do
  let current ← Ix.SpecDigest.Committed.current
  let natAdd := Role.all.idxOf .natAdd
  let renumbered := current.rows.mapIdx fun i w =>
    if i == natAdd then { w with native := (1, 5) } else w
  let swapped := { current.schedule with groups := swapFirstTwo current.schedule.groups }
  let lastByte := bytes.size - 1
  let edited ← replaceOnce file "first_equation_group() -> Field {\n      46\n"
    "first_equation_group() -> Field {\n      45\n"
  let renumberedBytes ← Ix.SpecDigest.encode { current with rows := renumbered }
  let swappedBytes ← Ix.SpecDigest.encode { current with schedule := swapped }
  return [
    ("bytes: Nat.add's native rule renumbered to Nat.mul's", renumberedBytes, file),
    ("bytes: the first two validation groups swapped", swappedBytes, file),
    ("bytes: the last byte (the first equation group) decremented",
      bytes.set! lastByte (bytes.get! lastByte - 1), file),
    ("bytes: one byte appended", bytes.push 0, file),
    ("file: first_equation_group edited to 45", bytes, edited)]

/-- The rendering without its `spec_digest` literal, the one line holding byte
constants, so that a comparison sees the tables alone. -/
def tables (rendering : String) : String :=
  let kept := (rendering.splitOn "\n").filter fun line =>
    (line.splitOn "UInt8::BYTE_").length == 1
  "\n".intercalate kept

def run : IO UInt32 := do
  let file ← IO.FS.readFile renderedPath
  let bytes ← IO.ofExcept Ix.SpecDigest.specBytes
  let mut failures := 0
  match IxVM.RoleSpecGen.checkRendering bytes file with
  | .ok () =>
    IO.println s!"[spec-digest-rendering] accepted: {renderedPath} is the rendering of the \
      specification bytes (digest {Address.blake3Pure bytes})"
  | .error e =>
    IO.eprintln s!"[spec-digest-rendering] FAIL: the checked-in file was refused: {e}"
    failures := failures + 1
  match mutations bytes file with
  | .error e =>
    IO.eprintln s!"[spec-digest-rendering] FAIL: could not build the mutations: {e}"
    failures := failures + 1
  | .ok cases =>
    for (name, b, f) in cases do
      match IxVM.RoleSpecGen.checkRendering b f with
      | .ok () =>
        IO.eprintln s!"[spec-digest-rendering] FAIL: {name}: accepted"
        failures := failures + 1
      | .error e =>
        IO.println s!"[spec-digest-rendering] refused, {name}: {e}"
        -- Mutated bytes must change the tables too, not only the digest literal.
        if f == file then
          match IxVM.RoleSpecGen.renderFromBytes b with
          | .error _ => pure ()
          | .ok rendered =>
            if tables rendered == tables file then
              IO.eprintln s!"[spec-digest-rendering] FAIL: {name}: only the digest literal changed"
              failures := failures + 1
            else
              IO.println s!"[spec-digest-rendering]   tables differ too, \
                {IxVM.RoleSpecGen.firstDifference (tables rendered) (tables file)}"
  return if failures == 0 then 0 else 1

end Tests.Ix.SpecDigestRendering
