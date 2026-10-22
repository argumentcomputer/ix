import Ix.Sharing.FamilyNormalize

/-! Offline whole-constant experiment; output is not a production canonical
artifact. Reuse identical outputs but preserve/refuse differing existing data. -/

def main (args : List String) : IO UInt32 := do
  let input :: kText :: output :: rest := args
    | throw (IO.userError "usage: sharing-family-normalize INPUT.ixn K OUTPUT.experimental.ixn [sharing-limits]")
  let some k := kText.toNat? | throw (IO.userError "K must be a natural number")
  unless k ≤ 24 do throw (IO.userError "unsupported experimental K > 24")
  unless rest.length ≤ 1 do throw (IO.userError "too many arguments")
  let limits ← match rest with
    | [] => pure ({} : Ix.Sharing.Exact.Limits)
    | [text] => IO.ofExcept (({} : Ix.Sharing.Exact.Limits).withOverrides text)
    | _ => throw (IO.userError "too many arguments")
  let bytes ← IO.FS.readBinFile input
  let constant ← IO.ofExcept (Ixon.deConstant bytes)
  IO.println s!"BEGIN\tK={k}\tinput_bytes={bytes.size}\tstatus=experimental\texact_baseline=unknown"
  (← IO.getStdout).flush
  let start ← IO.monoNanosNow
  let outcome ← IO.lazyPure fun _ =>
    Ix.Sharing.FamilyPrototype.normalizeFamily ⟨k⟩ .tagN constant limits
  let (candidate, result) ← IO.ofExcept (outcome.mapError toString)
  let elapsed := (← IO.monoNanosNow) - start
  let encoded := Ixon.serConstant candidate
  if ← (System.FilePath.mk output).pathExists then
    unless (← IO.FS.readBinFile output) == encoded do
      throw (IO.userError "refusing differing existing experimental output")
  else IO.FS.writeBinFile output encoded
  IO.println s!"END\tstatus=ok-experimental\tbytes={encoded.size}\tinput_equal={encoded == bytes}\twidth={result.stats.w}\tns={elapsed}"
  IO.println s!"model\tfamily_calls={result.phase1.statesVisited}\tphi_work={result.phase1.result.stats.costEvals}\tcandidates={result.stats.candidateLengths}"
  return 0
