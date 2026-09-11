import Ix.Compiler.Coverage.Sources
import Ix.Compiler.Ixon.RecursorUsage
import Ix.Compiler.PipelineErasure

/-! Canonical Ixon inputs with unique list fields and a unique-major
accumulator recursor. The entry is an explicit erased-argument application,
whose unique result is checked before ownership lowering. -/

namespace Ix.Compiler.UniqueReuse.Examples

open Ix.Compiler.Ixon

private def definition (value typ : Expr) (refs : Array Address) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }
    sharing := #[], refs, univs := #[.zero] }

private def projection (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def app2 (f x y : Expr) : Expr := .app (.app f x) y
private def app3 (f x y z : Expr) : Expr := .app (app2 f x y) z

structure Source where
  constants : List (Address × Constant)
  root : Address
  values : List Nat
  dataBlock : Address
  nil : Address
  cons : Address
  recursor : Address
  builder : Address

def Source.config (source : Source) : Pipeline.Config :=
  { blobs := fun address => (source.values.find? fun value =>
      X86.ValidatedScalar.literalAddress value == address).map .natB }

def Source.mainFrame (source : Source) : Ixon.Eval.Frame :=
  { refs := #[source.root], univs := #[.zero] }

def Source.main : Expr := .app (.ref 0 #[]) (.sort 0)

def Source.entry (source : Source) : Pipeline.ClosedEntry :=
  { refs := #[source.root], univs := #[.zero], source := Source.main }

def source (values : List Nat) (maxElements : Nat := 64) : Except String Source := do
  if values.length > maxElements then throw s!"unique fixture exceeds {maxElements} list elements"
  let natT := Expr.recur 0 #[]
  let listT := Expr.recur 1 #[]
  let builderT := .all .linear .unique natT (.all .linear .unique listT listT)
  let recursor : Recursor :=
    { k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0
      motives := 0, minors := 2
      typ := .all .many .shared builderT
        (.all .linear .unique listT (.all .linear .unique listT listT))
      rules := #[
        { fields := 0
          rhs := .lam .many builderT (.lam .linear listT (.var 0)) },
        { fields := 2
          rhs := .lam .many builderT (.lam .linear listT
            (.lam .linear natT (.lam .linear listT
              (.app (app2 (.recur 2 #[]) (.var 3)
                (app2 (.var 3) (.var 1) (.var 2))) (.var 0))))) }] }
  let dataBlock ← Coverage.addressed
    { info := .muts #[
        .indc {
          isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
          ctors := #[
            { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := natT },
            { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
              typ := .all .many .shared natT natT }] },
        .indc {
          isUnsafe := false, lvls := 0, params := 0, indices := 0
          typ := .sort 0
          ctors := #[
            { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0
              typ := listT },
            { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 2
              typ := .all .linear .unique natT (.all .linear .unique listT listT) }] },
        .recr recursor]
      sharing := #[], refs := #[], univs := #[.zero] }
  let nil ← Coverage.addressed (projection (.cPrj { idx := 1, cidx := 0, block := dataBlock.1 }))
  let cons ← Coverage.addressed (projection (.cPrj { idx := 1, cidx := 1, block := dataBlock.1 }))
  let natType ← Coverage.addressed (projection (.iPrj { idx := 0, block := dataBlock.1 }))
  let listType ← Coverage.addressed (projection (.iPrj { idx := 1, block := dataBlock.1 }))
  let recursorPrj ← Coverage.addressed (projection (.rPrj { idx := 2, block := dataBlock.1 }))
  let listT := Expr.ref 2 #[]
  let builder ← Coverage.addressed (definition
    (.lam .linear (.ref 1 #[]) (.lam .linear listT
      (app2 (.ref 0 #[]) (.var 1) (.var 0))))
    (.all .linear .unique (.ref 1 #[]) (.all .linear .unique listT listT))
    #[cons.1, natType.1, listType.1])
  let input := (values.mapIdx fun index _ => Expr.nat (index + 5).toUInt64).foldr
    (fun head tail => app2 (.ref 2 #[]) head tail) (.ref 1 #[])
  let body := app3 (.ref 0 #[]) (.ref 3 #[]) (.ref 1 #[]) input
  let entry ← Coverage.addressed (definition
    (.lam .erased (.sort 0) body)
    (.all .erased .unique (.sort 0) (.ref 4 #[]))
    (#[recursorPrj.1, nil.1, cons.1, builder.1, listType.1] ++
      (values.map X86.ValidatedScalar.literalAddress).toArray))
  return {
    constants := [dataBlock, nil, cons, natType, listType, recursorPrj, builder, entry]
    root := entry.1, values, dataBlock := dataBlock.1, nil := nil.1, cons := cons.1
    recursor := recursorPrj.1, builder := builder.1 }

end Ix.Compiler.UniqueReuse.Examples
