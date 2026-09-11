import Ix.Compiler.Coverage.Sources

/-! Runtime scalar sources for physical CFG selection. The recursors have
no recursive calls or higher-order arguments. Their ordinary compilation
exposes Nat peeling, direct calls, and scalar ownership operations. -/
namespace Ix.Compiler.X86.PhysicalScalar.Examples
open Ix.Compiler.Ixon (Address Constant)

def source (name : String) (captured : Option Nat := none) : Except String Coverage.Source := do
  let nat : Ixon.Expr := .recur 0 #[]
  let tag : Ixon.Recursor := {
    k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0, motives := 0, minors := 0
    typ := .all .many .shared nat nat
    rules := #[{ fields := 0, rhs := .nat 0 },
      { fields := 1, rhs := .lam .many nat (.nat 1) }] }
  let pred : Ixon.Recursor := { tag with rules := #[{ fields := 0, rhs := .nat 2 },
    { fields := 1, rhs := .lam .many nat (.var 0) }] }
  let choose : Ixon.Recursor := {
    k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0, motives := 0, minors := 1
    typ := .all .many .shared nat (.all .many .shared nat nat)
    rules := #[{ fields := 0, rhs := .lam .many nat (.var 0) },
      { fields := 1, rhs := .lam .many nat (.lam .many nat (.var 0)) }] }
  let binary : Ixon.Expr := .all .many .shared nat (.all .many .shared nat nat)
  let body : Ixon.Expr := match name with
    | "project" => .var 1
    | "tag" => .app (.recur 1 #[]) (.var 1)
    | "pred" => .app (.recur 2 #[]) (.var 1)
    | "unary-pred" => .app (.recur 2 #[]) (.var 0)
    | "choose" => .app (.app (.recur 3 #[]) (.var 0)) (.var 1)
    | "capture-project" => .var 1
    | "capture-choice" => .app (.app (.recur 3 #[]) (.var 1)) (.var 0)
    | "capture-nested" => .letE true nat (.app (.recur 2 #[]) (.var 0))
        (.app (.app (.recur 3 #[]) (.var 2)) (.app (.recur 2 #[]) (.var 0)))
    | "nested" => .letE true nat (.app (.recur 2 #[]) (.var 1))
        (.app (.app (.recur 3 #[]) (.var 1)) (.app (.recur 2 #[]) (.var 0)))
    | _ => .app (.recur 1 #[]) (.app (.recur 2 #[]) (.var 1))
  let block ← Coverage.addressed {
    info := .muts (#[.indc {
      isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
      ctors := #[
        { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := nat },
        { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1, typ := .all .many .shared nat nat }] },
      .recr tag, .recr pred, .recr choose,
      .defn {
        kind := .defn, safety := .safe, lvls := 0
        typ := if captured.isSome then .recur 5 #[]
          else if name == "unary-pred" then .all .many .shared nat nat else binary
        value := if captured.isSome then .letE true nat
          (.app (.lam .erased (.sort 0) (.nat 3)) (.sort 0)) (.lam .many nat body)
          else if name == "unary-pred" then .lam .many nat body else .lam .many nat (.lam .many nat body) }] ++
      if captured.isSome then #[.defn {
        kind := .defn, safety := .safe, lvls := 0, typ := .sort 0
        value := .all .many .shared nat nat }] else #[])
    sharing := #[], refs := #[ValidatedScalar.literalAddress 11, ValidatedScalar.literalAddress 22,
      ValidatedScalar.literalAddress 0] ++ captured.toArray.map ValidatedScalar.literalAddress, univs := #[.zero] }
  let entry ← Coverage.addressed {
    info := .dPrj { idx := 4, block := block.1 }, sharing := #[], refs := #[], univs := #[] }
  return {
    name
    constants := [block, entry]
    root := entry.1
    literals := [0, 11, 22] ++ captured.toList
    natBlock := some block.1
    expected := .scalar 0 false }

end Ix.Compiler.X86.PhysicalScalar.Examples
