import IxCCTests.KernelFront.Run

/-- `tests-kernel-front` runs the suite on the committed role-bound closures.
`tests-kernel-front diff NAME CLOSURE.ixe SIDECAR.json` compares ingress and the
kernel annotator with the earlier reading and annotator on one closure and
prints the report as one JSON line;
`tests-kernel-front single CLOSURE.ixe SIDECAR.json` runs the front
end alone (for its time and peak memory) and prints one JSON line;
`tests-kernel-front accept old|new|logical|committed CLOSURE.ixe` runs one
acceptance alone and prints one JSON line: the erased checker's, the kernel
front end's, the kernel's logical entry alone on the same inputs, or the
kernel's tiered entry behind its committed prelude. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => return if ← IxCCTests.KernelFront.run then 0 else 1
  | ["diff", name, ixe, sidecar] =>
    let bytes ← IO.FS.readBinFile ixe
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
    let rep ← IxCCTests.KernelFront.diff name bytes json
    IO.println rep.toJson.compress
    return 0
  | ["single", ixe, sidecar] =>
    let bytes ← IO.FS.readBinFile ixe
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
    IO.println (← IxCCTests.KernelFront.single bytes json).compress
    return 0
  | ["accept", front, ixe] =>
    IO.println (← IxCCTests.KernelFront.acceptOnly front (← IO.FS.readBinFile ixe)).compress
    return 0
  | _ =>
    IO.eprintln "usage: tests-kernel-front [diff NAME CLOSURE.ixe SIDECAR.json | single CLOSURE.ixe SIDECAR.json | accept old|new|logical|committed CLOSURE.ixe]"
    return 2
