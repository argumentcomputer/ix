import Tests.Ix.CompileCert.Groups
import Ix.CompileCert.Indexed

/-! The indexed W check (`Ix.CompileCert.checkIndexed`, behind the certifier)
against the list-based `checkCompiled` on the direct and group fixtures: every
accepted input is accepted by both, every refused input is refused by both,
with the refusal class. Position hints cover every position and are found by
search (they are untrusted), plus controls with wrong hints, which may only
refuse. -/

namespace Tests.Ix.CompileCert.Indexed

open _root_.Ix.CompileCert
open Tests.Ix.CompileCert.Direct
open Tests.Ix.Kernel.IxonFixtures (address)

/-- Hints for a small input: every source and map position, stream and record
positions found by search. -/
def fullHints (input : Input) (artifact : AdmittedArtifact input.toArtifactInput) : Hints :=
  let sh := Shared.ofArtifact input artifact
  { sourceAt := fun _ => List.range input.source.declarations.length
    mapAt := fun _ => List.range input.map.length
    entryAt := fun n => match input.source.find n with
      | some ci => match directExport sh.cx ci with
        | .ok e => (sh.entries.toList.findIdx? (· == e.withoutHint)).getD 0
        | .error _ => 0
      | none => 0
    recordAt := fun n => match input.map.find? (·.source == n) with
      | some e => (sh.constants.toList.findIdx? (·.1 == e.record)).getD 0
      | none => 0 }

/-- Hints that point nowhere useful. -/
def emptyHints : Hints :=
  { sourceAt := fun _ => [], mapAt := fun _ => [], entryAt := fun _ => 0, recordAt := fun _ => 0 }

def indexed (input : Input) (hints : (a : AdmittedArtifact input.toArtifactInput) → Hints) :
    Option (Except Decline Unit) :=
  match prepareArtifact input.toArtifactInput with
  | .error _ => none
  | .ok a => some ((checkIndexed input a (hints a)).map fun _ => ())

def sameClass : Except Decline Unit → Except Decline Unit → Bool
  | .ok _, .ok _ => true
  | .error .sourceDomain, .error .sourceDomain => true
  | .error .mapMismatch, .error .mapMismatch => true
  | .error .correspondence, .error .correspondence => true
  | .error .blockCorrespondence, .error .blockCorrespondence => true
  | .error .definitionGroupCorrespondence, .error .definitionGroupCorrespondence => true
  | _, _ => false

/-- Both checks agree, and the expected verdict holds. -/
def agrees (input : Input) (expected : Bool) : Bool :=
  match indexed input (fullHints input) with
  | none => false
  | some r =>
    let listed := (checkCompiled input).map fun _ => ()
    -- `checkAssociation` declines unsupported sources before deciding; the
    -- indexed check decides the propositions themselves, so it refuses them
    -- as correspondence failures.
    let listed := match listed with
      | .error (.unsupported ..) => .error .correspondence
      | other => other
    sameClass r listed && r.isOk == expected

def metadataValue : Input :=
  { choiceInput with
    source := ⟨[sourceDef `first (.mdata Lean.KVMap.empty (sourceValue true))]⟩ }

def metadataWrong : Input :=
  { choiceInput with
    source := ⟨[sourceDef `first (.mdata Lean.KVMap.empty (sourceValue false))]⟩ }

def controls : List (String × (Unit → Bool)) := [
  ("single definition: accepted by both", fun _ => agrees choiceInput true),
  ("legitimate alias fiber: accepted by both", fun _ => agrees aliases true),
  ("wrong alias body: refused by both", fun _ => agrees wrongAlias false),
  ("dependency through the map: accepted by both", fun _ => agrees dependent true),
  ("changed dependency: refused by both", fun _ =>
    agrees { dependent with source := ⟨[sourceDef `first (sourceValue false),
      sourceDef `root (.const `first [.param `u])]⟩ } false),
  ("missing map entry: refused by both", fun _ =>
    agrees { choiceInput with map := [] } false),
  ("map record that resolves elsewhere: refused by both", fun _ =>
    agrees { choiceInput with map := [⟨`first, address 99, .member (address 71) 0⟩] } false),
  ("missing root: refused by both", fun _ => agrees { choiceInput with roots := [`missing] } false),
  ("metadata erased: accepted by both", fun _ => agrees metadataValue true),
  ("metadata hides nothing: refused by both", fun _ => agrees metadataWrong false),
  ("group permutation and alias: accepted by both", fun _ => agrees Groups.grouped true),
  ("unmapped touched wire member: refused by both", fun _ =>
    agrees { Groups.grouped with
      source := ⟨[sourceDef `first (sourceValue true)]⟩, roots := [`first]
      map := [⟨`first, address 81, .member (address 80) 1⟩] } false),
  ("wrong group member body: refused by both", fun _ =>
    agrees { Groups.grouped with source := ⟨[Groups.groupedSource `first (sourceValue true),
      Groups.groupedSource `root (sourceValue false),
      Groups.groupedSource `alias (sourceValue true)]⟩ } false),
  ("hints that point nowhere refuse a valid input (hints are not trusted)", fun _ =>
    match indexed choiceInput (fun _ => emptyHints) with
    | some (.error _) => true
    | _ => false),
  ("wrong stream and record positions refuse a valid input", fun _ =>
    match indexed dependent (fun a =>
        { fullHints dependent a with entryAt := fun _ => 1000, recordAt := fun _ => 1000 }) with
    | some (.error .correspondence) => true
    | _ => false),
  ("a wrong stream position alone is covered by the raw record reading", fun _ =>
    match indexed dependent (fun a => { fullHints dependent a with entryAt := fun _ => 1000 }) with
    | some (.ok _) => true
    | _ => false)]

def run : IO Unit := do
  let mut failed := 0
  for (label, control) in controls do
    let ok := control ()
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  if failed != 0 then throw (IO.userError s!"{failed}/{controls.length} indexed controls failed")
  IO.println s!"indexed: {controls.length}/{controls.length} controls agree with checkCompiled"

end Tests.Ix.CompileCert.Indexed
