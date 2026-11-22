import IxCCTests.KernelFront.Run

/-- `tests-kernel-front` runs the suite on the committed role-bound closures.
`tests-kernel-front report NAME CLOSURE.ixe SIDECAR.json` runs the kernel's
acceptance, ingress and every root through the producer, Stage A and
`Recheck.run` on one closure and prints the report as one JSON line;
`tests-kernel-front single CLOSURE.ixe SIDECAR.json` runs the front
end alone (for its time and peak memory) and prints one JSON line;
`tests-kernel-front hint-case STEM ROOT MUTATION` runs one case of the hint
tests (`Hints.caseMain`) and prints one JSON line;
`tests-kernel-front accept new|logical|committed CLOSURE.ixe` runs one
acceptance alone and prints one JSON line: the kernel front end's, the
kernel's logical entry alone on the same inputs, or the kernel's tiered entry
behind its committed prelude. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => return if ← IxCCTests.KernelFront.run then 0 else 1
  | ["report", name, ixe, sidecar] =>
    let bytes ← IO.FS.readBinFile ixe
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
    let rep ← IxCCTests.KernelFront.report name bytes json
    IO.println rep.toJson.compress
    return 0
  | ["single", ixe, sidecar] =>
    let bytes ← IO.FS.readBinFile ixe
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
    IO.println (← IxCCTests.KernelFront.single bytes json).compress
    return 0
  | ["hint-case", stem, root, mutation] => IxCCTests.KernelFront.Hints.caseMain stem root mutation
  | ["accept", front, ixe] =>
    IO.println (← IxCCTests.KernelFront.acceptOnly front (← IO.FS.readBinFile ixe)).compress
    return 0
  | _ =>
    IO.eprintln "usage: tests-kernel-front [report NAME CLOSURE.ixe SIDECAR.json | single CLOSURE.ixe SIDECAR.json | hint-case STEM ROOT MUTATION | accept new|logical|committed CLOSURE.ixe]"
    return 2
