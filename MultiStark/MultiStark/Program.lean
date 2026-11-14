import Aiur.Modules.Frontend
import Aiur.Library.Blake3.Goldilocks
import Aiur.Library.Option
import Aiur.Library.Field.Goldilocks
import Blake3.Rust
import MultiStark.Modules.ProofDeserialize
import MultiStark.Modules.SystemDeserialize
import MultiStark.Modules.Pcs
import MultiStark.Modules.Aggregation
import MultiStark.Modules.StarkIO
import MultiStark.Modules.StarkHash
import MultiStark.Modules.Mmcs
import MultiStark.Modules.StarkVerifier
import MultiStark.Modules.Transcript
import MultiStark.Modules.Recursion
import MultiStark.Modules.Aggregate

/-! Recursive multi-stark verification as an ordinary Aiur program. This package
selects Goldilocks explicitly, including its degree-two extension and Blake3
transcript. It introduces no compiler or semantic primitives.

There are two programs, which share one copy of the verifier: the recursive
verifier, with entry point `MultiStark::verify_multi_stark_proof`, and the
aggregator, which adds `Aggregation`, with entry point `MultiStark::ix_aggr`.
The modules are the Lean files under `MultiStark/MultiStark/Modules/`, written
in Formal Aiur's module language as Lean syntax (`aiur⟦ … ⟧`) and elaborated
when this package is built. They are the source of truth. -/
namespace MultiStark
open Aiur

abbrev modulus := Library.U32.Goldilocks.modulus
abbrev F := Library.U32.Goldilocks.F

/-- The recursive verifier's modules, in the order they are composed. -/
def recursionSource : Modules.Program Nat :=
  [Source.proofDeserialize, Source.systemDeserialize, Source.pcs, Source.starkIO,
    Source.starkHash, Source.mmcs, Source.starkVerifier, Source.transcript,
    Source.recursion].foldl Modules.Program.append {}

/-- The aggregator's modules, in the order they are composed. -/
def aggregateSource : Modules.Program Nat :=
  [Source.proofDeserialize, Source.systemDeserialize, Source.pcs, Source.aggregation,
    Source.starkIO, Source.starkHash, Source.mmcs, Source.starkVerifier, Source.transcript,
    Source.aggregate].foldl Modules.Program.append {}

/-- The library templates the modules use. -/
def libraries : Modules.Program Nat :=
  Library.Blake3.templates.append Library.Option.declarations
    |>.append Library.Field.Goldilocks.declarations

-- The modules check against the libraries when this file is built.
#aiur_check libraries.append recursionSource
#aiur_check libraries.append aggregateSource

/-- `source` over Goldilocks, with the shared hash, option and extension-field
libraries. -/
def withLibraries (source : Modules.Program Nat) : Modules.Program F :=
  Library.Blake3.Goldilocks.program.append (Library.Option.declarations.toField F)
    |>.append Library.Field.Goldilocks.program
    |>.append (source.toField F)

/-- The recursive verifier, with entry point `MultiStark::verify_multi_stark_proof`. -/
def recursionProgram : Modules.Program F := withLibraries recursionSource

/-- The aggregator, with entry point `MultiStark::ix_aggr`. -/
def aggregateProgram : Modules.Program F := withLibraries aggregateSource

/-- BLAKE3, in lowercase hex, of `text`. -/
def hexDigest (text : String) : String :=
  String.join ((Blake3.Rust.hash text.toUTF8).val.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits))

/-- The recursive verifier's identity: BLAKE3 of `reprStr recursionProgram`,
computed when this file is compiled. `stark-export digest` prints it, and
`ix` keys its artifact cache by it. -/
def recursionDigest : String := aiur_eval% hexDigest (reprStr recursionProgram)

/-- The aggregator's identity, as `recursionDigest` is the recursive verifier's.
`stark-export digest --aggregate` prints it. -/
def aggregateDigest : String := aiur_eval% hexDigest (reprStr aggregateProgram)

end MultiStark
