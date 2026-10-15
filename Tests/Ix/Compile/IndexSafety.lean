import LSpec
import Ix.CompileM

/-! The compiler's total array accesses (`Ix.CompileM.arrIdx`): an in-range
index reads the value, an out-of-range one is the named error
(`internalIndexError`, naming the block and the site) instead of `PANIC` and
a default value; `byteArrayCmp` reads its bytes by proof; a standalone
payload is read by its shape. -/

namespace Tests.Ix.Compile.IndexSafety

open LSpec
open _root_.Ix (Name)

private def rootName : Name := Name.fromLeanName `D8.missing

private def checkedRead (values : Array Nat) (index : Nat) : Except String Nat := do
  let cenv := _root_.Ix.CompileM.CompileEnv.new { consts := {} }
  let blockEnv : _root_.Ix.CompileM.BlockEnv :=
    { all := {}, current := rootName, mutCtx := default, univCtx := [] }
  let (out, _) ← (_root_.Ix.CompileM.CompileM.run cenv blockEnv {}
    (_root_.Ix.CompileM.arrIdx values index "index-safety read")).mapError toString
  return out

private def readError (values : Array Nat) (index : Nat) : Option String :=
  match checkedRead values index with
  | .error message => some message
  | .ok _ => none

def suite : List TestSeq := [
  test "checked reads return the in-range value and name the block and site otherwise"
    (((checkedRead #[3, 5] 1).toOption == some 5
      && readError #[3] 1 == some
        "invalidMutualBlock: internal error in block 'D8.missing': index-safety read: index 1 out of range (size 1)"
      && readError #[] 0 == some
        "invalidMutualBlock: internal error in block 'D8.missing': index-safety read: index 0 out of range (size 0)" : Bool)),
  test "byteArrayCmp is lexicographic, then by length"
    (_root_.Ix.CompileM.byteArrayCmp ⟨#[1, 2]⟩ ⟨#[1, 3]⟩ == .lt
      && _root_.Ix.CompileM.byteArrayCmp ⟨#[2]⟩ ⟨#[1, 9]⟩ == .gt
      && _root_.Ix.CompileM.byteArrayCmp ⟨#[1]⟩ ⟨#[1, 0]⟩ == .lt
      && _root_.Ix.CompileM.byteArrayCmp ⟨#[1, 0]⟩ ⟨#[1, 0]⟩ == .eq),
  test "a standalone payload is a single definition or recursor"
    ((_root_.Ix.CompileM.standaloneMutConstInfo? #[]).isNone)]

end Tests.Ix.Compile.IndexSafety
