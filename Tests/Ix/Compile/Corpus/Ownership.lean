import Tests.Ix.Compile.Corpus.Generate
import Ix.Meta
import Ix.Ixon

namespace Tests.Ix.Compile.Corpus

open Lean

/-- A displayed name is not an identity: numeric and string components can
print alike, and private module components must survive serialization. -/
inductive NamePart where
  | str (value : String)
  | num (value : Nat)
  deriving FromJson, ToJson, BEq

def nameParts : Name → Array NamePart
  | .anonymous => #[]
  | .str parent text => (nameParts parent).push (.str text)
  | .num parent index => (nameParts parent).push (.num index)

def nameOfParts (parts : Array NamePart) : Name :=
  parts.foldl (fun parent part => match part with
    | .str text => parent.str text
    | .num index => parent.num index) .anonymous

def leanName : Ix.Name → Name
  | .anonymous _ => .anonymous
  | .str parent text _ => .str (leanName parent) text
  | .num parent index _ => .num (leanName parent) index

structure Ownership where
  names : Array (Array NamePart)
  deriving FromJson, ToJson

def Ownership.originalNames (owned : Ownership) : Array Name := owned.names.map nameOfParts

def Ownership.sourceSet (owned : Ownership) : Std.HashSet Ix.Name :=
  owned.originalNames.foldl (fun acc n => acc.insert (Ix.Name.fromLeanName n)) {}

/-- Private-to-user conversion classifies namespace membership only. The stored
identity is always the complete original source name, including private/numeric
components. Imported declarations in the same namespace are not source-owned. -/
def sourceOwnership (env : Environment) (ns : Name) : Ownership :=
  { names := (env.constants.toList.filterMap fun (n, _) =>
      if (env.getModuleIdxFor? n).isNone && ns.isPrefixOf ((privateToUserName? n).getD n)
      then some (nameParts n) else none).toArray }

def prepareOwnership (src : System.FilePath) (ns : String) : IO Ownership := do
  let owned := sourceOwnership (← getFileEnv src) ns.toName
  if owned.names.isEmpty then throw <| IO.userError s!"no source-owned declarations in {src} namespace {ns}"
  return owned

/-- Canonical auxiliary indices and representatives may differ from the source
auxiliary spelling. Ownership comes from the exact source owner before the
reserved component, preserving all private/numeric prefix components. Source
declarations using the reserved component are rejected by the compiler. -/
def imageOwner? (n : Name) : Option Name := do
  let parts := nameParts n
  let index ← parts.findIdx? (· == .str "_ix")
  unless 0 < index && index + 1 < parts.size do none
  return nameOfParts (parts.extract 0 index)

def ownedOutput (source : Std.HashSet Ix.Name) (n : Ix.Name) : Bool :=
  source.contains n || (imageOwner? (leanName n)).any fun owner =>
    source.contains (Ix.Name.fromLeanName owner)

/-- Legacy CLI selectors use displayed names. Refuse ambiguous spellings instead
of allowing a string/numeric collision to select a different original identity. -/
def checkSelectorIdentities (all selected : Array Ix.Name) : Except String Unit := do
  let wanted : Std.HashSet String := selected.foldl (fun acc n => acc.insert n.pretty) {}
  let mut seen : Std.HashMap String Ix.Name := {}
  for n in all do
    unless wanted.contains n.pretty do continue
    if let some previous := seen[n.pretty]? then
      if previous != n then throw s!"ambiguous displayed selector {n.pretty}: distinct original identities"
    seen := seen.insert n.pretty n
  for n in selected do
    unless seen[n.pretty]? == some n do throw s!"selected identity is absent: {n.pretty}"

def ownershipManifest (owned : Ownership) (names : Array (Ix.Name × Ixon.Named)) : Json :=
  let originals := owned.sourceSet
  let privateCount := owned.originalNames.filter (privateToUserName? · |>.isSome) |>.size
  Json.mkObj [
    ("sourcePublic", toJson (owned.names.size - privateCount)),
    ("sourcePrivate", toJson privateCount),
    ("generatedImages", toJson (names.filter (!originals.contains ·.1)).size),
    ("outputNames", toJson names.size),
    ("records", toJson (names.map fun (n, nd) => Json.mkObj [
      ("identity", toJson (nameParts (leanName n))), ("display", toJson n.pretty),
      ("address", toJson (toString nd.addr)),
      ("sourceOwned", toJson (originals.contains n)),
      ("private", toJson (privateToUserName? (leanName n)).isSome)]))]

end Tests.Ix.Compile.Corpus
