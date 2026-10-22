import Ix.Sharing.FamilyPrototypeFast

/-! Standalone experimental component traces from canonical constant bytes.
Link natively using the workspace's existing executable objects/FFI linkage;
the evaluator uses proved closure-local rows, not the production area path. -/

open Ix.Sharing.Exact Ix.Sharing.FamilyPrototype

def main (args : List String) : IO UInt32 := do
  let path :: kText :: rest := args
    | throw (IO.userError "usage: sharing-family-prototype <constant.ixn> <experimentK> [label [width [component]]]")
  let some k := kText.toNat? | throw (IO.userError "experimentK must be a natural number")
  unless rest.length ≤ 3 do throw (IO.userError "too many arguments")
  let label := rest.headD path
  let widthFilter ← rest[1]?.mapM fun s => match s.toNat? with
    | some n => if n ∈ [1, 2, 3] then pure n else throw (IO.userError "width must be 1, 2 or 3")
    | none => throw (IO.userError "width must be a natural number")
  let componentFilter ← rest[2]?.mapM fun s => match s.toNat? with
    | some n => pure n | none => throw (IO.userError "component must be a natural number")
  let bytes ← IO.FS.readBinFile path
  let constant ← IO.ofExcept (Ixon.deConstant bytes)
  -- This is the existing budgeted ingestion API. Its refusal is explicit;
  -- the prototype makes no totality claim about that input route.
  let expanded ← IO.ofExcept ((expand {} constant.sharing (constantInfoRoots constant.info) true).mapError toString)
  IO.println s!"header\tversion=1\tK={k}\ttie=set_prec\tevaluator=lean-phiEL2-closure-local\tnumeric=Nat/Int\tstatus=experimental"
  for width in [1, 2, 3] do
    if widthFilter.any (· != width) then continue
    let stage := uniformStage width expanded (Prep.ofDag expanded.dag)
    if componentFilter.any (· ≥ stage.comps.size) then throw (IO.userError "component index out of range")
    for (members, index) in stage.comps.zipIdx do
      if componentFilter.any (· != index) then continue
      let start ← IO.monoNanosNow
      let trace ← IO.lazyPure fun _ => component ⟨k⟩ expanded stage width index members
      let elapsed := (← IO.monoNanosNow) - start
      IO.println (trace.tsv label)
      IO.println s!"time\t{label}\t{width}\t{index}\t{elapsed}\tns\treference-only"
      (← IO.getStdout).flush
  return 0
