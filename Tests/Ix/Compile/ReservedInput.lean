/-
  D14's refusal names the least reserved input name by pretty form
  (`Ix.CompileDriver.pass3ReservedInput?`), as the Rust compiler does
  (`pass3::driver::reserved_input_in`), not the first in the blocks' iteration
  order (design document §11.6 item 3). Synthetic condensations: forty
  reserved names (the least is not the first in iteration order, checked),
  and a neighbour with none. The `pass3` suite's `ReservedIx` unit compares
  the two compilers' messages on a compiled fixture.
-/
module
public import LSpec
public import Ix.CompileDriver

public section

open LSpec

namespace Tests.Ix.Compile.ReservedInput

def nm (parts : List String) : Ix.Name := parts.foldl Ix.Name.mkStr Ix.Name.mkAnon

/-- One singleton block per name. -/
def blocksOf (names : List Ix.Name) : Ix.CondensedBlocks :=
  { lowLinks := names.foldl (fun m n => m.insert n n) {}
    blocks := names.foldl (fun m n => m.insert n (({} : Ix.Set Ix.Name).insert n)) {}
    blockRefs := names.foldl (fun m n => m.insert n {}) {} }

/-- `R.N<i>._ix.v` for `i < 40`, and some ordinary names. -/
def reserved : List Ix.Name :=
  (List.range 40).map fun i => nm ["R", s!"N{i + 10}", "_ix", "v"]

def ordinary : List Ix.Name := [nm ["R", "a"], nm ["R", "b"], nm ["S", "c"]]

def least : Ix.Name := nm ["R", "N10", "_ix", "v"]

/-- The first reserved name in the blocks' iteration order (what the
refusal named before). -/
def firstInOrder (b : Ix.CondensedBlocks) : Option Ix.Name := Id.run do
  for (_, all) in b.blocks do
    for n in all do
      if Ix.Compile.Pass.hasReserved n then return some n
  return none

def suite : List TestSeq :=
  let b := blocksOf (ordinary ++ reserved)
  [test "D14: the refusal names the least reserved name by pretty form"
     (Ix.CompileM.pass3ReservedInput? b == Ix.Compile.Pass.reservedInput? least),
   test "D14: the fixture's least reserved name is not the first in iteration order"
     (firstInOrder b != some least),
   test "D14 neighbour: no reserved name, no refusal"
     (Ix.CompileM.pass3ReservedInput? (blocksOf ordinary)).isNone]

end Tests.Ix.Compile.ReservedInput

end
