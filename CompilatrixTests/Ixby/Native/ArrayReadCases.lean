import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Native

open Ix.Ixby Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

/-- The complete pre-dispatch body from 1eaa245, retained as a regression oracle.
It is test data, never an accepted current-runtime certificate. -/
private def previousArrayGet : Function := {
  arity := 4
  blocks := #[
    ⟨4, .letOp (.call 58 [.erased, .local 1]) 1⟩,
    ⟨5, .letOp (.primitive .natLt [.local 2, .local 4]) 2⟩,
    ⟨6, .branch (.local 5) 3 4⟩,
    ⟨6, .caseCtor (.local 1) [⟨0, 5⟩, ⟨1, 6⟩, ⟨2, 7⟩]⟩,
    ⟨6, .caseCtor (.erased) []⟩,
    ⟨8, .letOp (.primitive .natToWord32 [.local 2]) 8⟩,
    ⟨7, .letOp (.primitive .arrayGet [.local 6, .local 2]) 10⟩,
    ⟨7, .letOp (.primitive .byteBuilderFreeze [.local 6]) 11⟩,
    ⟨9, .letOp (.primitive .bytesGet [.local 6, .local 8]) 9⟩,
    ⟨10, .ret (.local 9)⟩,
    ⟨8, .ret (.local 7)⟩,
    ⟨8, .letOp (.primitive .byteBuilderLength [.local 6]) 12⟩,
    ⟨9, .letOp (.primitive .natToWord32 [.local 2]) 13⟩,
    ⟨10, .letOp (.primitive .bytesGet [.local 7, .local 9]) 14⟩,
    ⟨11, .ret (.local 10)⟩] }

/-- Compare values and semantic errors at ample fuel, locals and stack capacity.
The cost reductions have separate exact-boundary checks in Fuel and Resources. -/
def arrayReadCases (image : Image) : IO Unit := do
  let arrayId ← checked (image.ctorId `Ixby.Runtime.Array)
  let bytesId ← checked (image.ctorId `Ixby.Runtime.Bytes)
  let writerId ← checked (image.ctorId `Ixby.Runtime.WriterBuffer)
  let previous := { image.program with functions := image.program.functions.set! 62 previousArrayGet }
  need (match Compilatrix.Ixby.Runtime.Native.certify previous with | .error _ => true | .ok _ => false)
    "previous array-read body must not satisfy the current certificate"
  let run (program : Program) (limits : Limits) (args : Array Value) (fast : Bool) := do
    let frame ← enter limits program 62 args
    if fast then
      (Compilatrix.Ixby.Runtime.Chunked.run limits program 100
        (Compilatrix.Ixby.Runtime.Chunked.State.ofReference ⟨.eval frame, #[]⟩)).map
          Compilatrix.Ixby.Runtime.Chunked.Value.toReference
    else Ix.Ixby.run limits program 100 ⟨.eval frame, #[]⟩
  let mut count := 0
  for n in #[0, 1, 2, 3, 7, 8, 33] do
    let bytes := (List.range n).toArray.map (fun i => (i * 17 + 9).toUInt8)
    let elements := bytes.map (fun b => natural b.toNat)
    let mut inputs : Array Value := #[.ctor arrayId #[.array elements],
      .ctor writerId #[.byteBuilder bytes], .ctor arrayId #[word 0],
      .ctor writerId #[.scalar (.bytes bytes)], .erased, natural 0]
    for cached in #[0, n, n + 1, 2 ^ 32 + 2] do
      inputs := inputs.push (.ctor bytesId #[.scalar (.bytes bytes), natural cached])
      inputs := inputs.push (.ctor bytesId #[.erased, natural cached])
    inputs := inputs.push (.ctor bytesId #[.scalar (.bytes bytes), word n.toUInt32])
    for natBits in #[0, 1, 2, 8, 256, 257] do
      for byteArrayBytes in #[0, 1, n, n + 1] do
        let limits : Limits := { natBits, byteArrayBytes, locals := 64, continuations := 1 }
        for input in inputs do
          for index in #[natural 0, natural (n - 1), natural n, natural (n + 1),
              natural (2 ^ 32), natural (2 ^ 32 + 1), natural (2 ^ 256), word 0, .erased] do
            let args := #[word 37, input, index, word 42]
            let expected := run previous limits args false
            for (program, fast) in #[(previous, true), (image.program, false), (image.program, true)] do
              let actual := run program limits args fast
              need (same actual expected)
                s!"array read {count}: limits={reprStr limits}, input={reprStr input}, index={reprStr index}; expected {reprStr expected}, got {reprStr actual}"
            count := count + 1
  IO.println s!"array read: {count} previous-body comparisons across reference/chunked evaluators"

end CompilatrixTests.Ixby.Native
