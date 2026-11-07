module

public import Tests.Ix.IxVM.Harness

/-!
# Scanning an Aiur program's source text

The guards over the IxVM and multi-stark programs' text (`Tests.Ix.Kernel.
PrimAddrs`, `Tests.IOIngress`) read it through `Tests.Ix.IxVM.programSources`
and split it here: into functions, the hint channels each reads, and the byte
literal lists each holds. The scanner knows only the surface it needs:
`module M {`, `fn f(` (with `pub`/`inline`), `hint::<…>("channel"` and
bracketed lists of literals.
-/

public section

namespace Tests.Ix.IxVM.Sources

/-- One function of a program: its qualified name (`Module::f`), the file it
is in, and its text up to the next function. -/
structure Function where
  name : String
  file : System.FilePath
  body : String

/-- The identifier at the start of `s`. -/
private def ident (s : String) : String :=
  String.ofList (s.toList.takeWhile fun c => c.isAlphanum || c == '_')

/-- The name a line declares after `keyword ` (`fn`, `module`), if it does. -/
private def declared (keyword line : String) : Option String :=
  let words := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  let words := words.dropWhile fun w => w == "pub" || w == "inline"
  match words with
  | k :: rest :: _ => if k == keyword then
      let name := ident rest
      if name.isEmpty then none else some name
    else none
  | _ => none

/-- The functions of the program `sources`, in order. -/
def functions (sources : Array (System.FilePath × String)) : Array Function := Id.run do
  let mut out := #[]
  for (file, text) in sources do
    let mut module := ""
    let mut current : Option (String × Array String) := none
    for line in text.splitOn "\n" do
      if let some m := declared "module" line then
        module := m
      if let some f := declared "fn" line then
        if let some (name, lines) := current then
          out := out.push { name, file, body := "\n".intercalate lines.toList }
        current := some (s!"{module}::{f}", #[line])
      else if let some (name, lines) := current then
        current := some (name, lines.push line)
    if let some (name, lines) := current then
      out := out.push { name, file, body := "\n".intercalate lines.toList }
  return out

/-- The hint channels `body` reads, in order (`hint::<T>("channel", key)`). -/
def hintChannels (body : String) : List String :=
  ((body.splitOn "hint::<").drop 1).filterMap fun chunk =>
    match chunk.splitOn "(\"" with
    | _ :: rest :: _ => some ((rest.splitOn "\"").headD "")
    | _ => none

/-- The value of a literal list item: `UInt8::BYTE_n`, a decimal or a `0x`
hexadecimal literal. -/
def literal? (item : String) : Option Nat :=
  let item := item.trimAscii.toString
  let item := if item.startsWith "UInt8::BYTE_" then (item.drop 12).toString else item
  if item.startsWith "0x" then
    (item.drop 2).toString.toList.foldlM (init := 0) fun n c =>
      if c.isDigit then some (16 * n + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (16 * n + (c.toNat - 'A'.toNat + 10))
      else none
  else if !item.isEmpty && item.all Char.isDigit then item.toNat?
  else none

/-- The bracketed lists in `body` whose items are all literals, innermost
brackets only (`[a, b, …]`; a repetition `[x; n]` is not a list of items). -/
def literalLists (body : String) : Array (Array Nat) := Id.run do
  let mut out := #[]
  for chunk in (body.splitOn "[").drop 1 do
    match chunk.splitOn "]" with
    | inner :: _ :: _ =>
      if inner.contains ';' || inner.contains '[' then continue
      let items := inner.splitOn ","
      let values := items.filterMap literal?
      if values.length == items.length then out := out.push values.toArray
    | _ => pure ()
  return out

end Tests.Ix.IxVM.Sources

end
