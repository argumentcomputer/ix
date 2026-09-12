import Compilatrix.Coverage.Sources

/-! Synthetic Ixon inputs enter through the ordinary addressed source
compiler. No physical instruction or native plan is supplied by these cases. -/
namespace Compilatrix.X86.PhysicalHeap.Examples
open Ixon

private def projection (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def definition (typ value : Expr) (refs : Array Address) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }, sharing := #[], refs, univs := #[.zero] }

def source (name : String) : Except String Coverage.Source := do
  let nat : Expr := .recur 0 #[]
  let box : Expr := .recur 1 #[]
  let pair := name == "shared-pair"
  let boxConstructor : Expr := if pair then .all .many .shared nat (.all .many .shared nat box)
    else .all .linear .unique nat box
  let data ← Coverage.addressed {
    info := .muts #[.indc {
      isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
      ctors := #[
        { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := nat },
        { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1, typ := .all .many .shared nat nat }] },
      .indc {
        isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
        ctors := #[{
          isUnsafe := false, lvls := 0, cidx := 0, params := 0
          fields := if pair then 2 else 1, typ := boxConstructor }] }]
    sharing := #[], refs := #[], univs := #[.zero] }
  let natType ← Coverage.addressed (projection (.iPrj { idx := 0, block := data.1 }))
  let boxType ← Coverage.addressed (projection (.iPrj { idx := 1, block := data.1 }))
  let ctor ← Coverage.addressed (projection (.cPrj { idx := 1, cidx := 0, block := data.1 }))
  if pair then
    let entry ← Coverage.addressed (definition
      (.all .many .shared (.ref 0 #[]) (.all .many .shared (.ref 0 #[]) (.ref 0 #[])))
      (.lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
        (.prj 1 1 (.app (.app (.ref 2 #[]) (.var 1)) (.var 0)))))
      #[natType.1, boxType.1, ctor.1])
    return {
      name, constants := [data, natType, boxType, ctor, entry], root := entry.1
      literals := [], expected := .scalar 0 false }
  let builder ← Coverage.addressed (definition
    (.all .erased .unique (.sort 0) (.ref 1 #[]))
    (.lam .erased (.sort 0) (.app (.ref 2 #[]) (.nat 3)))
    #[natType.1, boxType.1, ctor.1, ValidatedScalar.literalAddress 19])
  let consumer ← Coverage.addressed (definition
    (.all .affine .shared (.ref 1 #[]) (.all .many .shared (.ref 0 #[]) (.ref 0 #[])))
    (.lam .affine (.ref 1 #[]) (.lam .many (.ref 0 #[]) (.var 0))) #[natType.1, boxType.1])
  let build : Expr := .app (.ref 2 #[]) (.sort 0)
  let consume := fun value => Expr.app (.app (.ref 3 #[]) build) value
  if name == "branch-call" || name == "caller-live" then
    let nat : Expr := .ref 0 #[]
    let branch := name == "branch-call"
    let typ := if branch then .all .many .shared nat (.all .many .shared nat nat) else .all .many .shared nat nat
    let step : Recursor := {
      k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0, motives := 0, minors := if branch then 1 else 0
      typ
      rules := #[{ fields := 0, rhs := if branch then .lam .many nat (consume (.var 0)) else .nat 4 },
        { fields := 1, rhs := .lam .many nat (if branch then .lam .many nat (consume (.var 0)) else .var 0) }] }
    let block ← Coverage.addressed {
      info := .muts #[.recr step, .defn {
        kind := .defn, safety := .safe, lvls := 0, typ
        value := .lam .many nat (if branch then .lam .many nat (.app (.app (.recur 0 #[]) (.var 0)) (.var 1))
          else consume (.app (.recur 0 #[]) (.var 0))) }]
      sharing := #[], refs := #[natType.1, boxType.1, builder.1, consumer.1, ValidatedScalar.literalAddress 0], univs := #[.zero] }
    let entry ← Coverage.addressed (projection (.dPrj { idx := 1, block := block.1 }))
    return {
      name, constants := [data, natType, boxType, ctor, builder, consumer, block, entry], root := entry.1
      literals := [0, 19], natBlock := some block.1, expected := .scalar 0 false }
  let body := if name == "nested-alloc" then consume (consume (.var 0)) else consume (.var 0)
  let entry ← Coverage.addressed (definition (.all .many .shared (.ref 0 #[]) (.ref 0 #[]))
    (.lam .many (.ref 0 #[]) body) #[natType.1, boxType.1, builder.1, consumer.1])
  return {
    name, constants := [data, natType, boxType, ctor, builder, consumer, entry], root := entry.1
    literals := [19], expected := .scalar 0 false }

def sourceNames : List String := ["leaf-call", "branch-call", "caller-live", "nested-alloc", "shared-pair"]

def expected (name : String) (a b : Nat) : Nat :=
  if name == "shared-pair" then b
  else if name == "branch-call" then if a == 0 then b else a - 1
  else if name == "caller-live" then a - 1
  else a

end Compilatrix.X86.PhysicalHeap.Examples
