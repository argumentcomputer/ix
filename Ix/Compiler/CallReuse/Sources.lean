import Ix.Compiler.Coverage.Sources
import Ix.Compiler.CallReuse.MapPipeline

/-!
# Ixon map inputs for suspended-credit reuse

These synthetic sources map a constant-valued direct function over a list.
The constructor wraps a non-tail recursive call. Inputs contain only canonical
Ixon constants; the ordinary validated compiler produces both intermediate IRs.
-/

namespace Ix.Compiler.CallReuse.Examples

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
  replacement : Nat
  aliased : Bool
  uniquePrefix : Nat
  dataBlock : Address
  nil : Address
  cons : Address
  pair : Address

def Source.config (source : Source) : Pipeline.Config :=
  { blobs := fun address => ((source.replacement :: source.values).find? fun value =>
      X86.ValidatedScalar.literalAddress value == address).map .natB
    limits :=
      { maxConstants := 32, maxExpressionUnits := 4096, maxExpandedExpressionUnits := 4096
        maxLayer1NodeVisits := 262144, maxErasedDeclarations := 128
        maxErasureAppendCells := 8192, maxCertificateCandidates := 64
        maxCertificateValidationAttempts := 4160, maxCertificateSourceNodeWork := 1048576
        maxUsageFuel := 1000, maxErasureFuel := 1000
        maxValidationFuel := 1000, maxLoweringFuel := 1000 } }

abbrev Source.Compilation (source : Source) :=
  CallReuse.MapCompilation source.constants source.root source.config 1000 1000

def Source.compile (source : Source) : Except Pipeline.Error source.Compilation :=
  CallReuse.compileMap source.constants source.root source.config
    1000 1000 1000 1000 1000

def source (values : List Nat) (replacement : Nat) (aliased : Bool) (uniquePrefix : Nat := 0) :
    Except String Source := do
  if values.length > 64 then throw "map fixture exceeds 64 list elements"
  if uniquePrefix > values.length || (!aliased && uniquePrefix != 0) then
    throw "map alias prefix is outside the input"
  let natT := Expr.recur 0 #[]
  let listT := Expr.recur 1 #[]
  let stepT := .all .many .shared natT
    (.all .many .shared listT (.all .many .shared listT listT))
  let recursor : Recursor :=
    { k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0
      motives := 0, minors := 2
      typ := .all .many .shared listT
        (.all .many .shared stepT (.all .many .shared listT listT))
      rules := #[
        { fields := 0, rhs := .lam .many listT (.lam .many stepT (.var 1)) },
        { fields := 2
          rhs := .lam .many listT (.lam .many stepT (.lam .many natT (.lam .many listT
            (.app (app2 (.var 2) (.var 1) (.var 0))
              (.app (app2 (.recur 3 #[]) (.var 3) (.var 2)) (.var 0)))))) }] }
  let dataBlock ← Coverage.addressed
    { info := .muts #[
        .indc (inductiveType #[(0, .recur 0 #[]),
          (1, .all .many .shared (.recur 0 #[]) (.recur 0 #[]))]),
        .indc (inductiveType #[(0, .recur 1 #[]),
          (2, .all .many .shared (.recur 0 #[])
            (.all .many .shared (.recur 1 #[]) (.recur 1 #[])))]),
        .indc (inductiveType #[(2, .all .many .shared (.recur 1 #[])
          (.all .many .shared (.recur 1 #[]) (.recur 2 #[])))]),
        .recr recursor]
      sharing := #[], refs := #[], univs := #[.zero] }
  let nil ← Coverage.addressed (projection (.cPrj { idx := 1, cidx := 0, block := dataBlock.1 }))
  let cons ← Coverage.addressed (projection (.cPrj { idx := 1, cidx := 1, block := dataBlock.1 }))
  let pair ← Coverage.addressed (projection (.cPrj { idx := 2, cidx := 0, block := dataBlock.1 }))
  let natType ← Coverage.addressed (projection (.iPrj { idx := 0, block := dataBlock.1 }))
  let listType ← Coverage.addressed (projection (.iPrj { idx := 1, block := dataBlock.1 }))
  let pairType ← Coverage.addressed (projection (.iPrj { idx := 2, block := dataBlock.1 }))
  let worker ← Coverage.addressed (definition
    (.lam .many (.ref 0 #[]) (ghost (.nat 1)))
    (.all .many .shared (.ref 0 #[]) (.ref 0 #[]))
    #[natType.1, X86.ValidatedScalar.literalAddress replacement])
  let base ← Coverage.addressed (definition (ghost (.ref 0 #[])) (.ref 1 #[]) #[nil.1, listType.1])
  let step ← Coverage.addressed (definition
    (.lam .many (.ref 2 #[]) (.lam .many (.ref 3 #[]) (.lam .many (.ref 3 #[])
      (app2 (.ref 0 #[]) (.app (.ref 1 #[]) (.var 2)) (.var 0)))))
    (.all .many .shared (.ref 2 #[])
      (.all .many .shared (.ref 3 #[]) (.all .many .shared (.ref 3 #[]) (.ref 3 #[]))))
    #[cons.1, worker.1, natType.1, listType.1])
  let map ← Coverage.addressed (projection (.rPrj { idx := 3, block := dataBlock.1 }))
  let call := fun major => .app (app2 (.ref 0 #[]) (.ref 6 #[]) (.ref 7 #[])) major
  let heads := values.mapIdx fun index _ => ghost (.nat (index + 8).toUInt64)
  let input := heads.foldr (fun head tail => app2 (.ref 2 #[]) head tail)
    (ghost (.ref 1 #[]))
  let body := if aliased then
    let suffix := (heads.drop uniquePrefix).foldr (fun head tail => app2 (.ref 2 #[]) head tail)
      (ghost (.ref 1 #[]))
    let withPrefix := (heads.take uniquePrefix).foldr (fun head tail => app2 (.ref 2 #[]) head tail)
      (.var 0)
    .letE false (.ref 3 #[]) suffix
      (app2 (.ref 4 #[]) (call withPrefix) (.var 0))
    else call input
  let entry ← Coverage.addressed (definition body
    (if aliased then .ref 5 #[] else .ref 3 #[])
    (#[map.1, nil.1, cons.1, listType.1, pair.1, pairType.1, base.1, step.1] ++
      (values.map X86.ValidatedScalar.literalAddress).toArray))
  return {
    constants := [dataBlock, nil, cons, pair, natType, listType, pairType,
      worker, map, base, step, entry]
    root := entry.1, values, replacement, aliased, uniquePrefix
    dataBlock := dataBlock.1, nil := nil.1, cons := cons.1, pair := pair.1 }

end Ix.Compiler.CallReuse.Examples
