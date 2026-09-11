# Compiler trust boundary

The reviewed native/build profile is typed Lean data in
`Ix/Compiler/Tools/TrustProfile.lean`. `lake run check-compiler` validates it and
runs mutation tests for the audit's failure paths.

| Boundary | Assumption and evidence |
| --- | --- |
| `Blake3.Rust.hash` | The native implementation computes BLAKE3 over the supplied bytes. Runtime vectors and canonical artifact fixtures check compatibility. Address-identity theorems use explicit pairwise `Address.Blake3NoCollision` premises. |
| `DurableSync.file` and `DurableSync.directory` | The operating system and storage honor the synchronization requests. Cache contents still pass their independent validation; synchronization supplies no logical proof. |
| Lean and native build tools | The pinned Lean compiler/runtime, Rust toolchain, C compiler, linker, binutils, and host execute their specified operations. Their execution is outside the logical compiler simulation proofs. |
| x86 and object models | The formal instruction, byte, ABI, and object models describe the supported target behavior. Independent disassembly, object inspection, native execution, and corruption tests supply evidence for the modeled machine boundary. |
| External semantic oracles | Oracle functions are parameters of the interpreter and its theorems. An example oracle does not certify a linked native implementation. |

The complete compiler theorem axiom inventory is enforced by
`Ix/Compiler/Fence.lean`. Some address-dependent results include the existing
Blake3 dependency's native proof leaf. They must not be described as depending
only on Lean's logical axioms. Replacing this boundary requires a pure hash
specification and a refinement proof for the implementation.

The audit inventories every Lean file under the declared compiler library,
test, and benchmark roots. It rejects new project axioms, proof holes, native
decision tactics, unreviewed imports or qualified native entry points, changed
extern inventories, and changes to the reviewed compiler Lake section. It
checks both durability C exports and the source hash, all 12 Blake3 package
externs (including the unimported C module), the complete Cargo lock hash and
package identities, the Lean pin, and matching Blake3 Lake/Nix revisions.

This is a compiler-component audit. The monorepo's other dependencies, CI action
versions, and global Nix build configuration remain governed by the monorepo's
existing build and review process. The standalone Compilatrix whole-repository
Nix/CI integrity ledger is not a claim about this monorepo. The runtime and
proof gates are exposed as separate CI jobs here.

The current profile uses Lean 4.33.1, Blake3.lean
`78f5bc4b22de1172af8a5d91e7039128084fad3a`, BLAKE3 1.8.7, and lean-ffi
`93c7e52952ae94546be08313f4ff3922984c84d5`. Dependency updates require reviewing
the profile, theorem axiom fence, and compatibility fixtures together.
