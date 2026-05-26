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
- The [Aiur zkDSL](https://github.com/argumentcomputer/ix/tree/main/Ix/Aiur)
  which is a first-order functional programming language that generates
  multi-STARK circuits.
- The IxVM (not yet released), which implements reduction and typechecking
  of `ixon` (including ingress and egress from and to binary data).
- Integration with the [iroh p2p network](https://www.iroh.computer/) so that
  different ix users can easily share `ixon` data between themselves.

## Benchmarks

Compiler performance benchmarks are tracked at https://bencher.dev/console/projects/ix/plots

## Usage

### Prerequisites

- Install Clang to enable Bindgen, then set `LIBCLANG_PATH` per https://rust-lang.github.io/rust-bindgen/requirements.html

### Build

- Build and test the Ix library with `lake build` and `lake test`
- Install the `ix` binary with `lake run install`, or run with `lake exe ix`

### Testing

**Lean tests:** `lake test`

- `lake test -- <suite>` runs one or multiple primary test suites. Primary suites: `ffi`, `byte-array`, `ixon`, `claim`, `commit`, `canon`, `keccak`, `sharing`, `graph-unit`, `condense-unit`
- `lake test -- --ignored` runs only the expensive test suites: `shard-map`, `rust-canon-roundtrip`, `serial-canon-roundtrip`, `parallel-canon-roundtrip`, `graph-cross`, `condense-cross`, `compile`, `decompile`, `rust-serialize`, `rust-decompile`, `commit-io`, `aiur`, `aiur-hashes`, `ixvm`
    - Most tests require at least 32 GB RAM
    - The `compile` and `decompile` tests require 128 GB RAM
    - `aiur` and `aiur-hashes` generate ZK proofs and use significant CPU
- `lake test -- --ignored <ignored-suite>` runs one or multiple expensive suites by name
- `lake test -- --include-ignored` runs both primary and expensive test suites
- `lake test -- --include-ignored <ignored-suite>` runs all primary suites plus one or multiple expensive suites
- `lake test -- cli` runs CLI integration tests
- `lake test -- rust-compile` runs the Rust cross-compilation diagnostic

**Rust tests:** `cargo test` or `cargo nextest run`

### Proving under SP1

The Ix kernel typechecker has an SP1 guest at `sp1/guest/` driven by a host at
`sp1/host/`. The workflow is two steps: first compile a Lean program to a `.ixe`
serialized `Ixon.Env`, then feed that file to the SP1 host to either execute or
prove the typecheck.

**Nix users only:** enter the SP1 dev shell first to pick up `cargo-prove` and
the succinct Rust toolchain:

```
nix develop .#sp1
```

Non-Nix users: install the SP1 toolchain manually per the
[SP1 docs](https://docs.succinct.xyz/docs/sp1/getting-started/install).

1. **Compile a `.ixe` from a Lean file.** Pass `--path` to the Lean source,
   `--root` to slice the environment to the transitive closure of one constant,
   and `--out` for the output path. For example, to compile
   `Nat.add_comm` from the benchmark file:

   ```
   lake exe ix compile --path Benchmarks/CheckNatAddComm.lean \
                       --root Nat.add_comm \
                       --out nataddcomm.ixe
   ```

   Omitting `--root` emits the entire environment; omitting `--out` defaults to
   the lowercased input stem plus `.ixe` (e.g. `checknataddcomm.ixe`).

2. **Execute or prove under SP1.** From `sp1/host/`, run the host with `--ixe`
   pointing at the file produced above:

   ```
   cd sp1/host
   # Execute the kernel typecheck in the SP1 VM (no proof), prints failures + cycles
   RUST_LOG=info cargo run --release -- --execute --ixe ../../nataddcomm.ixe
   # Generate and verify a compressed SP1 proof of the same typecheck (CPU)
   RUST_LOG=info cargo run --release -- --ixe ../../nataddcomm.ixe
   ```

   With no `--ixe`, the host runs against an empty `Ixon.Env`.

   **Kernel modes.** The default is Anon mode (metadata-erased kernel with
   lazy on-demand ingress — matches Aiur's `kernel_check_test` semantics).
   Pass `--meta` to run Meta mode (preserves names + dup-level-param check;
   eager full-env ingress). Both prove the same structural typecheck; Meta
   is strictly more constrained but slightly more expensive in cycles.

   **GPU proving.** Build with the `cuda` feature and set `SP1_PROVER=cuda`
   at runtime:

   ```
   SP1_PROVER=cuda RUST_LOG=info cargo run --release --features cuda -- \
     --ixe ../../nataddcomm.ixe
   ```

   See the [SP1 CUDA docs](https://docs.succinct.xyz/docs/sp1/generating-proofs/hardware-acceleration/cuda)
   for prerequisites (Docker + an NVIDIA GPU with CUDA 12+).

### Proving under Zisk

The Ix kernel typechecker also has a Zisk guest at `zisk/guest/` driven by a
host at `zisk/host/`. The workflow mirrors the SP1 one — first compile a Lean
program to a `.ixe`, then feed it to the Zisk host to either execute or prove
the typecheck.

**Nix users only:** enter the Zisk dev shell first to pick up `cargo-zisk`,
`ziskemu`, and the RISC-V toolchain needed to build the guest:

```
nix develop .#zisk
```

Non-Nix users: install Zisk manually per the
[Zisk install docs](https://0xpolygonhermez.github.io/zisk/getting_started/installation.html).

1. **Compile a `.ixe` from a Lean file.** Same as for SP1:

   ```
   lake exe ix compile --path Benchmarks/CheckNatAddComm.lean \
                       --root Nat.add_comm \
                       --out nataddcomm.ixe
   ```

2. **Execute or prove under Zisk.** From `zisk/`, run the host with `--ixe`:

   ```
   cd zisk
   # Execute the kernel typecheck in the Zisk VM (no proof), prints cycles
   RUST_LOG=info cargo run --release -- --execute --ixe ../nataddcomm.ixe
   # Run the constraint checker without generating a proof
   RUST_LOG=info cargo run --release -- --verify-constraints --ixe ../nataddcomm.ixe
   # Generate and verify a VadcopFinal proof of the same typecheck (CPU)
   RUST_LOG=info cargo run --release -- --ixe ../nataddcomm.ixe
   ```

   With no `--ixe`, the host runs against an empty `Ixon.Env`. The host's
   `build.rs` invokes `zisk_sdk::build_program("../guest")`, so `cargo run`
   transparently rebuilds the guest ELF whenever its sources change.

   **Kernel modes.** Same `--meta` flag as the SP1 host (default is Anon
   with lazy on-demand ingress; `--meta` switches to Meta with eager
   full-env ingress).

   **GPU proving.** Pass `--gpu` at runtime — Zisk's prover backend ships
   with CUDA support by default (the `cpu-only` Cargo feature is opt-out
   and is not set here):

   ```
   RUST_LOG=info cargo run --release -- --gpu --ixe ../nataddcomm.ixe
   ```

   Requires a CUDA-capable GPU and the matching CUDA runtime libraries
   visible to the linker (`LD_LIBRARY_PATH`). The Nix `.#zisk` shell wires
   these up automatically; for non-Nix setups follow the
   [Zisk install docs](https://0xpolygonhermez.github.io/zisk/getting_started/installation.html).

   **Memlock limit.** Zisk's assembly emulator `mmap`s ROM with `MAP_LOCKED`
   and needs a memlock limit well above typical distro defaults (often 8 MB).
   Symptom: `mmap(rom) errno=11=Resource temporarily unavailable` followed by
   `Shmem creation … failed with exit status: 255` during
   `STARTING_ASM_MICROSERVICES`. Raise it for the current shell (needs sudo
   to lift the hard cap):

   ```
   sudo prlimit --memlock=unlimited:unlimited --pid $$
   ulimit -l   # confirm: prints 'unlimited'
   ```

   For a persistent fix, raise `memlock` system-wide via your distro's PAM
   limits and re-login.

   **Heap cap.** The Zisk zkVM has a hard 512 MB RAM cap
   ([`RAM_SIZE`](https://github.com/0xPolygonHermez/zisk/blob/v0.17.0/core/src/mem.rs#L111)),
   of which ~510 MB is usable heap, and isn't configurable without
   rebuilding the proving setup. Envs whose deserialized in-memory
   representation exceeds that won't fit (full `TutorialDefs.lean` pulls in
   Lean stdlib + Batteries + LSpec, around 1 GB resident). For bigger envs,
   prefer the SP1 backend (default 24 GB runtime cap
   [`DEFAULT_MEMORY_LIMIT`](https://github.com/succinctlabs/sp1/blob/v6.2.0/crates/core/executor/src/opts.rs#L25),
   configurable via `MEMORY_LIMIT` env var up to a ~1 TB JIT ceiling
   [`MAX_JIT_LOG_ADDR`](https://github.com/succinctlabs/sp1/blob/v6.2.0/crates/primitives/src/consts.rs#L11)),
   or shrink the env via `--root <const>` to take the transitive closure of
   a single constant.

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

This will prompt you to optionally enable the Garnix cache, which can also be done by passing `--accept-flake-config` to the Nix command. Then when building, you should see `copying path '/nix/store/<...>' from https://cache.garnix.io`

To build and run the test suite, run `nix build .#test` and `nix run .#test`.
