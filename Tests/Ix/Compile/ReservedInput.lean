/-
  reserved-input: the reserved names of Pass 3 (D14, `Ix.Compile.Pass.Names`).
  A name with a component that is `_ix` or starts with it is reserved, a
  neighbour (`_i`, `ix`) is not; the display names of a changed block's Ix
  auxiliaries (`ixAuxName`), including a nested auxiliary at its canonical
  position; name prefixes compared by components, never by a stored hash.
  The Rust twins are `pass3::names`' unit tests.
-/
import LSpec
import Ix.Compile.Pass.Names

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

def suite : List TestSeq :=
  (nameControls ++ auxNameControls ++ hashControls).map fun (label, ok) => test label ok

end Tests.Ix.Compile.ReservedInput
