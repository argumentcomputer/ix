import Ix.Compiler.Coverage.Sources

/-!
# Ixon inputs for source recursion recovery

These canonical synthetic constants describe an eager tail-below fold and a
closed list-reversal entry. They supply no intermediate IR. The explicit
erased-argument applications are accepted by the existing shared-result gate.
The constants are not an upstream Lean export or a claim about Std coverage.
-/

namespace Ix.Compiler.Recursion.Examples

open Ix.Compiler.Ixon

private def definition (value typ : Expr) (refs : Array Address) : Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }
    sharing := #[], refs, univs := #[.zero] }

private def projection (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def ghost (value : Expr) : Expr :=
  .app (.lam .erased (.sort 0) value) (.sort 0)

private def app2 (f x y : Expr) : Expr := .app (.app f x) y

private def inductiveType (types : Array (Nat × Expr)) : Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0
    ctors := types.mapIdx fun i row =>
      { isUnsafe := false, lvls := 0, cidx := i.toUInt64, params := 0
        fields := row.1.toUInt64, typ := row.2 } }

structure Source where
  constants : List (Address × Constant)
  root : Address
  values : List Nat
  aliased : Bool
  nil : Address
  cons : Address
  pair : Address
  dataBlock : Address

def Source.config (source : Source) : Pipeline.Config :=
  { blobs := fun a => (source.values.find? fun n =>
      X86.ValidatedScalar.literalAddress n == a).map .natB
    limits :=
      { maxConstants := 32, maxExpressionUnits := 4096, maxExpandedExpressionUnits := 4096
        maxLayer1NodeVisits := 262144, maxErasedDeclarations := 128
        maxErasureAppendCells := 8192, maxCertificateCandidates := 64
        maxCertificateValidationAttempts := 4160, maxCertificateSourceNodeWork := 1048576
        maxUsageFuel := 1000, maxErasureFuel := 1000
        maxValidationFuel := 1000, maxLoweringFuel := 1000 } }

/-- One declaration group holds four types without introducing mutual list
recursion: Nat, List Nat, the below tuple, and the returned pair. Separate
type-only blocks would erase to duplicate block identities at today's gate.
-/
def source (values : List Nat) (aliased : Bool) : Except String Source := do
  if values.length > 64 then throw "recursion fixture exceeds 64 list elements"
  let natT := Expr.recur 0 #[]
  let listT := Expr.recur 1 #[]
  let tupleT := Expr.recur 2 #[]
  let stepT := .all .many .shared natT
    (.all .many .shared listT (.all .many .shared tupleT tupleT))
  let recursor : Recursor :=
    { k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0
      motives := 0, minors := 2
      typ := .all .many .shared tupleT
        (.all .many .shared stepT (.all .many .shared listT tupleT))
      rules := #[
        { fields := 0
          rhs := .lam .many tupleT (.lam .many stepT (.var 1)) },
        { fields := 2
          rhs := .lam .many tupleT (.lam .many stepT
            (.lam .many natT (.lam .many listT
              (.app (app2 (.var 2) (.var 1) (.var 0))
                (.app (app2 (.recur 4 #[]) (.var 3) (.var 2)) (.var 0)))))) }] }
  let dataBlock ← Coverage.addressed
    { info := .muts #[
        .indc (inductiveType #[(0, .recur 0 #[]),
          (1, .all .many .shared (.recur 0 #[]) (.recur 0 #[]))]),
        .indc (inductiveType #[(0, .recur 1 #[]),
          (2, .all .many .shared (.recur 0 #[])
            (.all .many .shared (.recur 1 #[]) (.recur 1 #[])))]),
        .indc (inductiveType #[(2, .all .many .shared
          (.all .many .shared (.recur 1 #[]) (.recur 1 #[]))
          (.all .many .shared (.recur 2 #[]) (.recur 2 #[]))), (0, .recur 2 #[])]),
        .indc (inductiveType #[(2, .all .many .shared (.recur 1 #[])
          (.all .many .shared (.recur 1 #[]) (.recur 3 #[])))]),
        .recr recursor]
      sharing := #[], refs := #[], univs := #[.zero] }
  let unit ← Coverage.addressed (projection (.cPrj { idx := 2, cidx := 1, block := dataBlock.1 }))
  let pack ← Coverage.addressed (projection (.cPrj { idx := 2, cidx := 0, block := dataBlock.1 }))
  let nil ← Coverage.addressed (projection (.cPrj { idx := 1, cidx := 0, block := dataBlock.1 }))
  let cons ← Coverage.addressed (projection (.cPrj { idx := 1, cidx := 1, block := dataBlock.1 }))
  let pair ← Coverage.addressed (projection (.cPrj { idx := 3, cidx := 0, block := dataBlock.1 }))
  let natType ← Coverage.addressed (projection (.iPrj { idx := 0, block := dataBlock.1 }))
  let listType ← Coverage.addressed (projection (.iPrj { idx := 1, block := dataBlock.1 }))
  let tupleType ← Coverage.addressed (projection (.iPrj { idx := 2, block := dataBlock.1 }))
  let pairType ← Coverage.addressed (projection (.iPrj { idx := 3, block := dataBlock.1 }))
  let listT := Expr.ref 3 #[]
  let tupleT := Expr.ref 4 #[]
  let consE := fun h t => app2 (.ref 1 #[]) h t
  let packE := fun f b => app2 (.ref 0 #[]) f b
  let base ← Coverage.addressed (definition
    (packE (ghost (.lam .many (.ref 2 #[]) (.var 0))) (ghost (.ref 1 #[])))
    (.ref 3 #[]) #[pack.1, unit.1, listType.1, tupleType.1])
  -- Inside the accumulator lambda: acc, erased argument, below, tail, head.
  let stepBody := .lam .many (.ref 2 #[]) (.lam .many listT
    (.lam .many tupleT
      (packE (ghost (.lam .many listT
        (.app (.prj 4 0 (.var 2)) (consE (.var 4) (.var 0))))) (.var 0))))
  let step ← Coverage.addressed (definition stepBody
    (.all .many .shared (.ref 2 #[])
      (.all .many .shared listT (.all .many .shared tupleT tupleT)))
    #[pack.1, cons.1, natType.1, listType.1, tupleType.1])
  let recursorPrj ← Coverage.addressed (projection (.rPrj { idx := 4, block := dataBlock.1 }))
  let heads := values.mapIdx fun i _ => ghost (.nat (i + 9).toUInt64)
  let xs := heads.foldr (fun head tail => app2 (.ref 2 #[]) head tail)
    (ghost (.ref 1 #[]))
  let call := fun xs => .app
    (.prj 5 0 (.app (app2 (.ref 0 #[]) (.ref 7 #[]) (.ref 8 #[])) xs))
    (ghost (.ref 1 #[]))
  let main := if aliased then
    .letE false (.ref 3 #[]) xs (app2 (.ref 4 #[]) (call (.var 0)) (.var 0))
    else call xs
  let entry ← Coverage.addressed (definition main (if aliased then .ref 6 #[] else .ref 3 #[])
    (#[recursorPrj.1, nil.1, cons.1, listType.1, pair.1, tupleType.1, pairType.1,
      base.1, step.1] ++
      (values.map X86.ValidatedScalar.literalAddress).toArray))
  return {
    constants := [dataBlock, unit, pack, nil, cons, pair, natType, listType,
      tupleType, pairType, recursorPrj, base, step, entry]
    root := entry.1, values, aliased, nil := nil.1, cons := cons.1, pair := pair.1
    dataBlock := dataBlock.1 }

end Ix.Compiler.Recursion.Examples
