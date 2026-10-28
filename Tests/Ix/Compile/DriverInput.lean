import LSpec
import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Tests.Ix.Compile.ScheduleReference

/-! The compile drivers' input checks and keys: a condensation with a block
that has no reference set is refused by both drivers
(`Ix.CompileM.missingBlockRefs?`) instead of being scheduled as if it had no
dependencies; a block is named by its least member and an address by its
least alias (`canonicalKey`, `insertCanonicalAlias`), whatever the order. -/

namespace Tests.Ix.Compile.DriverInput

open LSpec
open _root_.Ix (Name)

private def missing : Name := Name.fromLeanName `DriverInput.missing
private def present : Name := Name.fromLeanName `DriverInput.present

/-- Two singleton blocks; only `present` has a reference set. -/
private def blocks : _root_.Ix.CondensedBlocks :=
  { lowLinks := ({} : _root_.Ix.Map Name Name).insert missing missing |>.insert present present
    blocks := ({} : _root_.Ix.Map Name (_root_.Ix.Set Name))
      |>.insert missing (({} : _root_.Ix.Set Name).insert missing)
      |>.insert present (({} : _root_.Ix.Set Name).insert present)
    blockRefs := ({} : _root_.Ix.Map Name (_root_.Ix.Set Name)).insert present {} }

private def expected : String := "block DriverInput.missing has no condensation reference set"

/-- Three aliases at one address, in every insertion order. -/
private def aliases : List Name :=
  [`DriverInput.a, `DriverInput.b, `DriverInput.c].map Name.fromLeanName

private def permutations : List (List Name) := match aliases with
  | [a, b, c] => [[a, b, c], [a, c, b], [b, a, c], [b, c, a], [c, a, b], [c, b, a]]
  | _ => []

private def least : Name := aliases.foldl (init := aliases.head!) fun k n =>
  if _root_.Ix.nameCompare n k == .lt then n else k

def suite : List TestSeq := [
  test "the reverse index keeps the least alias whatever the insertion order"
    (permutations.all fun order =>
      (order.foldl (init := ({} : Std.HashMap Address Name)) fun m n =>
        _root_.Ix.CompileM.insertCanonicalAlias m default n).get? default == some least),
  test "a block is keyed by its least member whatever the iteration order"
    (permutations.all fun order =>
      _root_.Ix.CompileM.canonicalKey Name.mkAnon order.toArray == least),
  test "missingBlockRefs? names the block without references"
    (_root_.Ix.CompileM.missingBlockRefs? blocks == some expected),
  test "missingBlockRefs? accepts a complete condensation"
    (_root_.Ix.CompileM.missingBlockRefs?
      { blocks with blockRefs := blocks.blockRefs.insert missing {} } == none),
  test "the driver refuses a block without references"
    (show Bool from match _root_.Ix.CompileM.compileEnvFold { consts := {} } blocks with
      | .error why => why == expected
      | .ok _ => false),
  test "the driver refuses a block without references at every width"
    ([1, 2, 256].all fun width =>
      match _root_.Ix.CompileM.compileEnvFold { consts := {} } blocks (width := width) with
      | .error why => why == expected
      | .ok _ => false)]

end Tests.Ix.Compile.DriverInput
