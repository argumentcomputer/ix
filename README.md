# ix: a zero-knowledge proof carrying code (zkPCC) platform for Lean 4

> We have just folded space from Ix...Many machines on Ix. New machines.

![Planet IX](https://upload.wikimedia.org/wikipedia/commons/5/5a/Planet_nine_artistic_plain.png)

------

The ix platform enables the compilation of [Lean
4](https://github.com/leanprover/lean4) programs into zero-knowledge succinct
non-interactive arguments of knowledge (zk-SNARKs). This allows the execution
and typechecking of any Lean program to be verified by performing a
sub-100-millisecond operation against an approximately 1 kilobyte certificate,
regardless of the size of the original Lean program. In fact, the correctness of
the entire [mathlib](https://github.com/leanprover-community/mathlib4) library
of formal mathematics, containing around 2 million lines of code, may be
compiled in this way into a single kilobyte sized cryptographic certificate.
We call this technique zero-knowledge proof-carrying code or *zkPCC*, as an
extension of the well-known [proof-carrying
code](https://en.wikipedia.org/wiki/Proof-carrying_code) paradigm. Instead
of a host system verifying formal proofs carried by an application as in *PCC*,
in *zkPCC* the host or user verifies a cryptographic zero-knowledge proof
generated from the typechecking of that formal proof. This greatly improves the
runtime cost of this verification operation (potentially even up to O(1)
depending on the specific zkSNARK protocol used) and minimizes the complexity of
local dependencies tooling (e.g. build systems for the formal proof language).
Additionally, while in *PCC* an application must reveal the proof artifact that
demonstrates some formal property to the user, in *zkPCC* this proof artifact
may be kept private, which opens up new possiblities for economic transactions
over proofs.

Our expectation is that *zkPCC* will allow applications frictionlessly ship
security guarantees to their users. Some possible use cases could be:

- Software written in compiled languages like Rust can attach to their binaries
  proofs of type signatures or other formal properties verified by tools
  [Aeneas](https://github.com/AeneasVerif/aeneas). Given mature
  certified compilation infrastructure (e.g. a future
  [CompCert](https://en.wikipedia.org/wiki/CompCert) equivalent in Lean4),
  proofs that the compilation occurred correctly can also be attached, which
  would mitigate supply-chain attacks, such as that famously by Ken
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
  improving portability over *PCC*, *zkPCC* potentially enables more
  sophisticated software-based process isolation.
- Decentralized platforms like [Ethereum blockchain](https://ethereum.org/)
  could publish [formal specifications of their protocol](https://github.com/ConsenSys/eth2.0-dafny)
  and then require clients, layer-2s, zkVMs, etc to publish *zkPCC* proofs
  that their current specific version satisfies such specifications. Such proofs
  could be verified on-chain, and even programmatically gate certain protocol updates
  (e.g. version X validates that version X+1 is a correct update).
- Individual smart contracts can publish on-chain proofs of ther [formal
  models](https://ethereum.org/en/developers/docs/smart-contracts/formal-verification/)
  or proofs showing that their bytecode was generated from particular sources
  (currently a trusted block explorer feature)
- Cryptographic projects [risc0 zkVM](https://risczero.com/)
  could include a proof of the correctness of their [Lean 4 formal
  model](https://github.com/risc0/risc0-lean4) alongside (or aggregated within)
  every proof produced by their zkVM.




## Build & Install

- Build and test the Ix library with `lake build` and `lake test`

- Run the Ix CLI with `lake exe ix`. Install the binary with `lake run install`
    - `ix store <lean-file>` will compile a lean program into the ix store as
      ixon data
    - `ix store get <address>` will print the value of ixon data at the given
      address

### Nix

#### Prerequisites

- Install [Nix](https://nixos.org/download/)

- Enable [Flakes](https://zero-to-nix.com/concepts/flakes/)
  - Add `experimental-features = nix-command flakes` to `~/.config/nix/nix.conf`
    or `/etc/nix/nix.conf`
  - Add `trusted-users = root MYUSER` to `/etc/nix/nix.conf`
  - Then restart the Nix daemon with `sudo pkill nix-daemon`

- *Recommended*: Install [Cachix](https://docs.cachix.org/installation). This
  will use our cached nix flake artifacts, saving you from recompiling Lean and
  other dependencies from scratch, which can take a substantial amount of time.
  - Run `nix profile install --accept-flake-config nixpkgs#cachix`
  - Enable the cache with `cachix use argumentcomputer`
  - When building, you should see `querying <...> on
    https://argumentcomputer.cachix.org`

#### Build

Build and run the Ix CLI with `nix build` and `nix run`

To build and run the test suite, run `nix build .#test` and `nix run .#test`

#### Cache Troubleshooting

If the Nix build hangs with a message like `building lean-stage0`, it's not
finding the cached packages and will likely take >15 minutes to build the Lean
compiler from source. Ctrl+C and check the following:

- Note that caching is only provided for `x86_64-linux` and `aarch64-darwin` at
  the moment
- Make sure `substituters` and `trusted-public-keys` have been added to
  `~/.config/nix/nix.conf`
- Try restarting the Nix daemon again
- Check the given derivation is present in the cache, see the [Cachix FAQ](https://docs.cachix.org/faq#why-is-nix-not-picking-up-on-any-of-the-pre-built-artifacts)
- Check the Lean version is supported at
  https://github.com/argumentcomputer/lean4-nix/tree/dev/manifests
