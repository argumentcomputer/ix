# Ix: a zero-knowledge proof-carrying code platform

> We have just folded space from Ix. Many machines on Ix. New machines.

![Planet IX](https://upload.wikimedia.org/wikipedia/commons/5/5a/Planet_nine_artistic_plain.png)

-----------

The Ix platform enables the compilation of [Lean
4](https://github.com/leanprover/lean4) programs into zero-knowledge succinct
non-interactive arguments of knowledge (zk-SNARKs). This allows the execution
and typechecking of any Lean program to be verified by performing a
sub-100-millisecond operation against an approximately 1 kilobyte certificate,
regardless of the size of the original Lean program. In fact, the correctness of
the entire [mathlib](https://github.com/leanprover-community/mathlib4) library
of formal mathematics, containing around 2 million lines of code, may be
compiled in this way into a single kilobyte sized cryptographic certificate.

We call this technique zero-knowledge proof-carrying code or **zkPCC**, as an
extension of the well-known [proof-carrying
code](https://en.wikipedia.org/wiki/Proof-carrying_code) paradigm. Instead
of a host system verifying formal proofs carried by an application as in
proof-carrying code, in **zkPCC** the host or user verifies a cryptographic
zero-knowledge proof generated from the typechecking of that formal proof. This
greatly improves the runtime cost of this verification operation (potentially
even up to O(1) depending on the specific zk-SNARK protocol used) and minimizes
the complexity of locally dependent tooling (e.g. build systems for the formal
proof language).

Additionally, while in proof-carrying code an application must reveal the proof
artifact that demonstrates some formal property to the user, in **zkPCC** this
proof artifact may be kept private, which opens up new possibilities for economic
transactions over proofs.

> :warning: **This repository is a pre-alpha work in progress and should not be used for any purpose.**

## Use Cases

Our expectation is that Ix, and **zkPCC** in general, will allow applications to frictionlessly ship
security guarantees to their users. Some possible use cases could be:

- Software written in compiled languages like Rust can attach to their binaries
  proofs of type signatures or other formal properties verified by tools such as
  [Aeneas](https://github.com/AeneasVerif/aeneas). Given mature
  certified compilation infrastructure (e.g. a future
  [CompCert](https://en.wikipedia.org/wiki/CompCert) equivalent in Lean4),
  proofs that the compilation occurred correctly can also be attached, which
  would mitigate supply-chain attacks, such as those famously described by Ken
  Thompson in [Reflections on Trusting
  Trust](https://www.cs.cmu.edu/~rdriley/487/papers/Thompson_1984_ReflectionsonTrustingTrust.pdf).
  This would also enable secure decentralized binary caching, saving on the need
  for duplicative local recompilation or expensive continuous integration
  software.
- In operating systems, hardware based process isolation costs [25%-33% overhead
  in terms of processor
  cycles](https://research.cs.wisc.edu/areas/os/Seminar/schedules/papers/Deconstructing_Process_Isolation_final.pdf).
  This means everytime you buy a laptop, cell phone, web server, you have to pay
  for a third more computing power, because we don't know how to safely run
  applications in protection ring 0. By reducing verification overhead and
  improving portability over proof-carrying code, **zkPCC** potentially enables more
  sophisticated software-based process isolation.
- Decentralized platforms like the [Ethereum blockchain](https://ethereum.org/)
  could publish [formal specifications of their protocol](https://github.com/ConsenSys/eth2.0-dafny)
  and then require clients, layer-2s, zkVMs, etc. to publish **zkPCC** proofs
  that their current specific version satisfies such specifications. Such proofs
  could be verified on-chain, and even programmatically gate certain protocol updates
  (e.g. version X validates that version X+1 is a correct update).
- Individual smart contracts can publish on-chain proofs of their [formal
  models](https://ethereum.org/en/developers/docs/smart-contracts/formal-verification/)
  or proofs showing that their bytecode was generated from particular sources
  (currently a trusted block explorer feature).
- Cryptographic projects like the [risc0 zkVM](https://risczero.com/)
  could include a proof of the correctness of their [Lean 4 formal
  model](https://github.com/risc0/risc0-lean4) alongside (or aggregated within)
  every proof produced by their zkVM.

-----------

### Example: Embedding Fermat's Last Theorem in Fermat's Margin Note

In or around 1637, the mathematician Pierre Fermat conjectured the following:

> 1. It is impossible to separate a cube into two cubes, or a fourth power into two
> fourth powers, or in general, any power higher than the second, into two like
> powers.
> 2. I have discovered a truly marvelous proof of this
> 3. which this margin is too narrow to contain.

The first part of this statement famously evaded proof for over 350 years before
finally being demonstrated by Andrew Wiles in 1994. Mathematicians and
historians of mathematics have also long debated the second part, whether
Fermat's claim that he possessed a proof of the first part is credible, which
seems unlikely given the complexity and modern mathematical infrastructure used
by the Wiles proof of the first part. Rarely discussed, however, is the third
part, which is in fact a statement of proof theory, specifically one which
proposes an information theoretic lower bound to the size of the proof of a
particular proposition.

The specific margin in question is [page 85 in the 1621 edition of Diophantus'
Arithmetica](https://en.wikipedia.org/wiki/Fermat's_Last_Theorem#/media/File:Diophantus-II-8.jpg),
which is a folio volume with dimensions [353mm tall by 225mm wide by 40mm deep](https://www.sophiararebooks.com/pages/books/6237/diophantus-of-alexandria/arithmeticorum-libri-sex-et-de-numeris-multangulis-liber-unus-nunc-primum-graece-latine-editi). Leaving the precise dimensions of the margins as an exercise to the reader,
it is trivial to show the proposition is false regardless of margin size, or
the size of the proof (up to very large bounds) if one permits the proof to
printed in the margin using arbitrarily small text, using microfilm,
photolithography, etc. It is more interesting to assume that what Fermat meant
was that the margin is too narrow to contain a proof written in Fermat's own
handwriting.

Happily, we have an example of text we know would satisfy this constraint,
Fermat's margin note itself! In Latin, the note reads:

> Cubum autem in duos cubos, aut quadratoquadratum in duos quadratoquadratos & generaliter nullam in infinitum ultra quadratum potestatem in duos eiusdem nominis fas est dividere cuius rei demonstrationem mirabilem sane detexi. Hanc marginis exiguitas non caperet.

At 262 characters, and 8-bits per character, this is 2096 bits, or 262 bytes.
This is quite small, but fortunately not quite as small as a [Groth16 proof over
BN254](https://2π.com/23/bn254-compression/):

> A Groth16 proof has two G1 points and one G2. In the BN254 pairing curve these take 64 and 128 bytes respectively uncompressed totaling 256 bytes for a proof.

So if we can show that a Groth16 proof of *a* proof of the first part of
Fermat's Last Theorem is constructible, we will have clearly - though
non-constructively- disproven the third part.

[A Lean 4 formalization of Fermat's Last
Theorem](https://github.com/ImperialCollegeLondon/FLT) is in progress, and gives
the statement as:

```lean4
theorem PNat.pow_add_pow_ne_pow
    (x y z : ℕ+)
    (n : ℕ) (hn : n > 2) :
    x^n + y^n ≠ z^n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem FLT.Wiles_Taylor_Wiles x y z n hn
```

Currently, as the dependencies of this theorem contain `sorry` holes, we cannot
feed it through `ix` (which only works over complete program graphs). Once the
formalization is complete, however, you will be able to do

```
> ix store FLT.lean PNat.pow_add_pow_ne_pow
e53c3d4bad8538e152a89d8bf75be178a3876252744961b9a087fe3973545c20
> ix prove --check e53c3d4bad8538e152a89d8bf75be178a3876252744961b9a087fe3973545c20
b44236ba17ad7445ae3eac48a8ba86ba00f08c069237b08451e311b688146e7e
```

to generate a [multi-STARK](https://github.com/argumentcomputer/multi-stark)
proof that the theorem typechecks. With a Groth16 circuit that recursively proves
verification of such proofs, i.e. a Groth16 final SNARK, the construction is complete,
and we can embed a proof of Fermat's Last Theorem in Fermat's Margin Note.

![Fits in the Margin](docs/fitsinthemargin.png "alternatively, we could use a QR code")

-----------

## Architecture

Ix consists of the following core components:

- [The Ix compiler](https://github.com/argumentcomputer/ix/blob/main/Ix/CompileM.lean),
  which transforms Lean 4 programs into a format called `ixon`, [the ix object
  notation](https://github.com/argumentcomputer/ix/blob/main/docs/Ixon.md),
  which is an alpha-invariant content-addressable serialization or wire format.
  The compiler also includes a decompiler to convert `ixon` objects back into
  Lean programs (by preserving the alpha-relevant metadata in a separate ixon
  object and re-merging the computationally relevant and irrelevant parts).
  See [the Rust compiler guide](docs/compiler-rust.md) for its data flow, FFI,
  scheduling, parity checks and trust boundary.
- The [Aiur zkDSL](https://github.com/argumentcomputer/ix/tree/main/Ix/Aiur)
  which is a first-order functional programming language that generates
  multi-STARK circuits.
- The IxVM (not yet released), which implements reduction and typechecking
  of `ixon` (including ingress and egress from and to binary data).
- Integration with the [iroh p2p network](https://www.iroh.computer/) so that
  different ix users can easily share `ixon` data between themselves.

### Certified Ixon checker

`IxC/Kernel` is a type checker for `ixon` whose acceptance is proved to imply
consistency. It is Ix's own kernel, derived from the verified checker of
[con-leche](https://github.com/leanprover/con-leche). Its entry,
`Ix.Kernel.Admission.checkBytes`, takes canonical `ixon` bytes, and for every
environment it accepts the theorems give a set-theoretic model and no proof of
`False`, on the standard axioms only. It does not certify the compiler, the
Rust kernel, `Ix.Tc` or IxVM. [docs/kernel.md](docs/kernel.md) states what is
proved, what is trusted and what the gate checks; `--with-model` also builds
the Mathlib-based model package `Models/SetTheory`:

```sh
lake run check-kernel --with-model
```

## Benchmarks

Benchmarks (compiler, kernel, and zk-prover backends) are tracked at
https://bencher.dev/console/projects/ix/plots. `ix bench` runs the same
cells locally, and `!benchmark` runs them on a PR — see
[docs/benchmarking.md](docs/benchmarking.md).

### CUDA-accelerated Aiur proving

Aiur can use multi-stark's first-party CUDA backend. CUDA is opt-in: ordinary
Cargo and Lake builds remain CPU-only and do not require a CUDA toolkit or
runtime. First generate the benchmark environment, then set `IX_CUDA=1` (also
accepts `true` or `yes`) for the proving command:

```sh
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out InitStd.ixe
IX_CUDA=1 lake exe bench-typecheck --ixe InitStd.ixe \
  --consts Vector.extract_append --recursive
```

Rust consumers can instead enable the `cuda` feature on `aiur` or `ix-ffi`.
The backend requires an NVIDIA GPU and a CUDA toolkit with `nvcc`; build and
architecture controls are documented in the multi-stark repository. It keeps
the Goldilocks/BLAKE3 protocol and proof format unchanged, and GPU proofs remain
verifiable by the CPU implementation. Proving a whole environment across
several GPUs (`ix prove --lanes`), generating traces on the device, and
benchmarking such runs are covered in
[docs/aiur-gpu-proving.md](docs/aiur-gpu-proving.md). Dated hardware
measurements belong in [BENCHMARKS.md](BENCHMARKS.md) and
[docs/benchmarking.md](docs/benchmarking.md), not this stable overview.

## Usage

### Prerequisites

- Install Clang to enable Bindgen, then set `LIBCLANG_PATH` per https://rust-lang.github.io/rust-bindgen/requirements.html

### Build

- Build and test the Ix library with `lake build` and `lake test`
- Install the `ix` binary with `lake run install`, or run with `lake exe ix`

### Testing

**Lean tests:** `lake test`

For compiler and certification suite coverage, CI placement, exact records, byte
references and landing commands, see [Compiler and certification gates](docs/compiler-gates.md).

- `lake test -- <suite>` runs one or multiple primary test suites. Primary suites include: `ffi`, `meta-env`, `catalog`, `import-ixe`, `truthmines-spec`, `ixon`, `ixon-syntax`, `claim`, `merkle`, `assumption-tree`, `commit`, `canon`, `keccak`, `exact-sharing`, `exact-sharing-ffi`, `source-contract`, `graph-unit`, `condense-unit`, `bench-measures`, `aux-gen-unit`, `ground-unit`, `aiur-cross`, `aiur-cost`, `prim-addrs`, `kernel-reader-roundtrip`, `kernel-read-cache`, `primitive-address-parity`, `decompile-unit`, `tc-unit`
    - `exact-sharing` tests the canonical sharing construction of Ixon v4; `exact-sharing-ffi` checks that Lean and Rust produce identical bytes
    - `kernel-reader-roundtrip` checks the certified checker's Ixon reader against a direct translation of the compiled Lean constants; `kernel-read-cache` checks the environment check's persistent read cache
    - Primary runners also run with the primary suites and can be selected by name in the same way; examples are: `aiur-rust-syntax`, `ixvm-tagn`, `aiur-prove`, `aiur-hashes`, `rbtree-map`, `multi-stark`, `recursive-verifier`, `ix-aggr`, `ixes-manifest`; `ixvm-tagn` holds the IxVM circuit's TagN codec to the Lean codec
- `lake exe ixon-v4-tests` runs the Ixon v4 format suite (golden bytes, FFI, VM, text grammar, resource admission, claims, and the fixtures in `Tests/Fixtures/ixon-v4/`); `lake exe ixon-v4-primitives` regenerates the primitive closure and checks `primitives.tsv` against it; both keep their scratch files in `$IX_IXON_V4_DIR` (default `/tmp`)
- `lake build --wfail IxSharingVerify` builds the proofs of the canonical sharing construction (`IxSharingVerify`) and their audits; `lake lint` builds it too. The Ixon codec proofs, including TagN's, build with `lake -d IxC build --wfail`
- `lake test -- --ignored` runs all expensive test suites and runners
    - Most tests require at least 32 GB RAM
    - The `compile` and `decompile` tests require 128 GB RAM
    - `ixvm` generates ZK proofs and uses significant CPU
- `lake test -- --ignored <name>` runs one or more expensive suites or runners by name
- `--exclude=<name,...>` excludes ignored suites or runners from a full ignored-test run
- `lake test -- --include-ignored` runs both primary and expensive test suites
- `lake test -- --include-ignored <name>` runs all primary suites plus selected expensive suites or runners
- `lake test -- cli` runs CLI integration tests
- `lake test -- rust-compile` runs the Rust cross-compilation diagnostic

**Rust tests:** `cargo test` or `cargo nextest run`

### Nix

#### Prerequisites

- Install [Nix](https://nixos.org/download/)

- Enable [Flakes](https://zero-to-nix.com/concepts/flakes/)
  - Add `experimental-features = nix-command flakes` to `~/.config/nix/nix.conf`
    or `/etc/nix/nix.conf`
  - Add `trusted-users = root MYUSER` to `/etc/nix/nix.conf`
  - Then restart the Nix daemon with `sudo pkill nix-daemon`

#### Build

Build and run the Ix CLI with `nix build` and `nix run`.

This will prompt you to optionally enable the Cachix binary cache, which can also be done by passing `--accept-flake-config` to the Nix command. Then when building, you should see `copying path '/nix/store/<...>' from https://argumentcomputer.cachix.org`

To build and run the test suite, run `nix build .#test` and `nix run .#test`.
