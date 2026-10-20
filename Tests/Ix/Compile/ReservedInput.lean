/-
  reserved-input: the reserved names of Pass 3 (`Ix.Compile.Pass.Names`).
  A name with a component that is `_ix` or starts with it is reserved, a
  neighbour (`_i`, `ix`) is not; the display names of a changed block's Ix
  auxiliaries (`ixAuxName`), including a nested auxiliary at its canonical
  position; name prefixes compared by components, never by a stored hash.
  The drivers' refusals name the least message by its text
  (`Ix.CompileM.reservedInputRefusal?`, `reservedMetadataRefusal?`), as the
  Rust compiler does (`pass3::names::reserved_input_in`), not the first in
  the blocks' iteration order: two synthetic condensations of forty reserved
  names each, and a neighbour with none. The Rust twins are `pass3::names`'
  unit tests. The drivers' cases are `compile-reserved-mdata`'s (both
  compilers end to end): a reserved name, a reserved metadata key, and
  three reserved names of which both name exactly the least.
-/
import LSpec
import Ix.Compile.Pass.Names
import Ix.CompileDriver

namespace Tests.Ix.Compile.ReservedInput

open LSpec
open _root_.Ix (Name)
open _root_.Ix.Compile.Pass

/-- A dotted name with string components. -/
def nm (parts : List String) : Name := parts.foldl Name.mkStr Name.mkAnon

def nameControls : List (String × Bool) :=
  [("A._ix.rec is reserved", (reservedInput? (nm ["A", "_ix", "rec"])).isSome),
   ("A._ixfoo is reserved", (reservedInput? (nm ["A", "_ixfoo"])).isSome),
   ("A.ix.rec is not reserved", (reservedInput? (nm ["A", "ix", "rec"])).isNone),
   ("A._i is not reserved", (reservedInput? (nm ["A", "_i"])).isNone),
   ("_ix.inline is reserved", hasReserved inlineKey),
   ("_ix.inline_meta is reserved", hasReserved inlineMetaKey),
   ("A ↦ A._ix (ixFormName)", comps (ixFormName (nm ["A"])) == comps (nm ["A", "_ix"]))]

def auxNameControls : List (String × Bool) :=
  let a := nm ["A"]
  let b := nm ["B"]
  let members := #[a, b]
  [("A.rec ↦ A._ix.rec",
      (ixAuxName members b #[] (nm ["A", "rec"])).map comps
        == some (comps (nm ["A", "_ix", "rec"]))),
   ("A.rec_1 at canonical position 1 ↦ B._ix.rec_2",
      (ixAuxName members b #[some 1, some 0] (nm ["A", "rec_1"])).map comps
        == some (comps (nm ["B", "_ix", "rec_2"]))),
   ("A.rec_1 out of the component keeps its name ↦ A._ix.rec_1",
      (ixAuxName members b #[none] (nm ["A", "rec_1"])).map comps
        == some (comps (nm ["A", "_ix", "rec_1"]))),
   ("C.rec hangs off no member", (ixAuxName members b #[] (nm ["C", "rec"])).isNone)]

/-- Two different names that carry one stored hash: a prefix is decided by
the components, so neither is a prefix of the other. -/
def hashControls : List (String × Bool) :=
  let h : Address := ⟨⟨Array.replicate 32 7⟩⟩
  let x : Name := .str (.anonymous h) "A" h
  let y : Name := .str (.anonymous h) "B" h
  let yc : Name := .str y "rec" h
  [("A is not a prefix of B.rec although the hashes agree", (stripPrefix? x yc).isNone),
   ("B is a prefix of B.rec", (stripPrefix? y yc).map (·.length) == some 1)]

/-! ## The drivers' refusals -/

/-- One singleton block per name. -/
def blocksOf (names : List Name) : _root_.Ix.CondensedBlocks :=
  { lowLinks := names.foldl (fun m n => m.insert n n) {}
    blocks := names.foldl (fun m n => m.insert n (({} : _root_.Ix.Set Name).insert n)) {}
    blockRefs := names.foldl (fun m n => m.insert n {}) {} }

/-- `R.N<i>._ix.v` for `lo ≤ i < lo + 40`; the least is `R.N<lo>._ix.v`. -/
def reservedFrom (lo : Nat) : List Name :=
  (List.range 40).map fun i => nm ["R", s!"N{lo + i}", "_ix", "v"]

def ordinary : List Name := [nm ["R", "a"], nm ["R", "b"], nm ["S", "c"]]

/-- The first reserved name in the blocks' iteration order. -/
def firstInOrder (b : _root_.Ix.CondensedBlocks) : Option Name := Id.run do
  for (_, all) in b.blocks do
    for n in all do
      if hasReserved n then return some n
  return none

def driverControls : List (String × Bool) :=
  -- two fixtures, so that the least is not first in iteration order in at
  -- least one of them
  let fixtures := [10, 50].map fun lo =>
    (blocksOf (ordinary ++ reservedFrom lo), nm ["R", s!"N{lo}", "_ix", "v"])
  [("the refusal names the least reserved name",
      fixtures.all fun (b, least) =>
        _root_.Ix.CompileM.reservedInputRefusal? b == reservedInput? least),
   ("in a fixture the least reserved name is not the first in iteration order",
      fixtures.any fun (b, least) => (firstInOrder b).map comps != some (comps least)),
   ("no reserved name, no refusal",
      (_root_.Ix.CompileM.reservedInputRefusal? (blocksOf ordinary)).isNone),
   ("the metadata refusal names the least constant",
      _root_.Ix.CompileM.reservedMetadataRefusal? #[nm ["M", "b"], nm ["M", "a"]]
        == some (reservedMetadataInput (nm ["M", "a"]))),
   ("no reserved metadata, no refusal", (_root_.Ix.CompileM.reservedMetadataRefusal? #[]).isNone)]

def suite : List TestSeq :=
  (nameControls ++ auxNameControls ++ hashControls ++ driverControls).map fun (label, ok) =>
    test label ok

end Tests.Ix.Compile.ReservedInput
