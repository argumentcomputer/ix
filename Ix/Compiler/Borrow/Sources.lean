import Ix.Compiler.Coverage.Sources

/-! Canonical synthetic Ixon inputs for borrowed direct calls. A shared Nat
constructor is inspected twice through named functions in one source group.
The group permits known calls to the recursor, whose tag read returns 11 or
22. No intermediate IR is provided. -/

namespace Ix.Compiler.Borrow.Examples

open Ix.Compiler.Ixon

private def definition (value typ : Expr) (refs : Array Address) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }
    sharing := #[], refs, univs := #[.zero] }

private def projection (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def ghost (value : Expr) : Expr :=
  .app (.lam .erased (.sort 0) value) (.sort 0)

private def natInductive : Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0
        typ := .recur 0 #[] },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[]) }] }

/-- `depth` forwarding functions precede a caller that reads the same value
 twice. Zero and successor cases both perform a constructor dispatch. -/
def source (depth : Nat) (successorCase : Bool) : Except String Coverage.Source := do
  if depth > 8 then throw "borrow fixture exceeds eight forwarding functions"
  let natT := Expr.recur 0 #[]
  let typ := Expr.all .many .shared natT natT
  let reader : Recursor :=
    { k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0
      motives := 0, minors := 0, typ
      rules := #[
        { fields := 0, rhs := .nat 0 },
        { fields := 1, rhs := .lam .many natT (.nat 1) }] }
  let mut members : Array MutConst := #[.indc natInductive, .recr reader]
  for index in [:depth] do
    members := members.push (.defn
      { kind := .defn, safety := .safe, lvls := 0, typ
        value := .lam .many natT (.app (.recur (index + 1).toUInt64 #[]) (.var 0)) })
  let call := fun value => Expr.app (.recur (depth + 1).toUInt64 #[]) value
  members := members.push (.defn
    { kind := .defn, safety := .safe, lvls := 0, typ
      value := .lam .many natT
        (.letE false natT (call (.var 0)) (call (.var 1))) })
  let block ← Coverage.addressed
    { info := .muts members, sharing := #[], univs := #[.zero]
      refs := #[X86.ValidatedScalar.literalAddress 11, X86.ValidatedScalar.literalAddress 22] }
  let natType ← Coverage.addressed (projection (.iPrj { idx := 0, block := block.1 }))
  let worker ← Coverage.addressed
    (projection (.dPrj { idx := (depth + 2).toUInt64, block := block.1 }))
  let zero ← Coverage.addressed (projection (.cPrj { idx := 0, cidx := 0, block := block.1 }))
  let successor ← Coverage.addressed
    (projection (.cPrj { idx := 0, cidx := 1, block := block.1 }))
  let major := if successorCase then .app (.ref 2 #[]) (ghost (.nat 4))
    else ghost (.ref 1 #[])
  let entry ← Coverage.addressed (definition (.app (.ref 0 #[]) major)
    (.ref 3 #[]) #[worker.1, zero.1, successor.1, natType.1,
      X86.ValidatedScalar.literalAddress 42])
  return {
    name := s!"read-tag-{depth}-{if successorCase then "succ" else "zero"}"
    constants := [block, natType, worker, zero, successor, entry]
    root := entry.1, literals := [11, 22, 42]
    expected := .scalar (if successorCase then 22 else 11) false }

end Ix.Compiler.Borrow.Examples
