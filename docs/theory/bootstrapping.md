# Bootstrapping Ix: From Kernel Circuit to Universal Verifier

This document describes how Ix bootstraps a certified ZK verification key
from its own kernel typechecker. With a formally verified Aiur circuit for
the Ix kernel, we can generate a verification key `vk_ix` by running the Lean
kernel once (natively, out of circuit), and then use `vk_ix` to certify
arbitrary Aiur circuits — including future versions of the kernel itself.

Prerequisites: [kernel.md](kernel.md) (kernel formalization),
[compiler.md](compiler.md) (compilation pipeline),
[zk.md](zk.md) (ZK layer and IxVM).

**Current state**: The kernel circuit does not yet exist. This document
describes the design and trust argument for when it is built.


## Overview

The core idea in three sentences:

1. The Ix kernel typechecker is written as an Aiur circuit, producing a
   verification key `vk_ix` that can verify ZK proofs of the form "this
   Ixon constant is well-typed."

2. A one-time native execution of the Lean kernel certifies that the circuit
   is correct — the formal proofs of soundness (in `Ix/Theory/`) typecheck,
   bridging the specification to the circuit implementation.

3. Since Aiur circuits are defined as Lean programs, and Lean programs can
   carry formal proofs of their properties, `vk_ix` can verify ZK proofs
   that *any* Aiur circuit is correct — including proofs about circuits
   that have nothing to do with type theory.

This is the bootstrapping loop: the kernel verifies itself, and then
verifies everything else.

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│   Lean Kernel (native, one-time)                                │
│   Checks: Ix/Theory/ proofs + kernel circuit correctness proof  │
│                          │                                      │
│                          ▼                                      │
│              ┌──────────────────────┐                           │
│              │  vk_ix               │                           │
│              │  (verification key   │                           │
│              │   for kernel circuit)│                           │
│              └──────────┬───────────┘                           │
│                         │                                       │
│           ┌─────────────┼─────────────┐                         │
│           ▼             ▼             ▼                          │
│     CheckClaim    CheckClaim    CheckClaim                      │
│     (user thm)   (circuit C)  (circuit D)                       │
│                                                                 │
│   Any Lean constant    Any Aiur circuit                         │
│   can be verified      can be certified                         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```


## Part I: The Kernel Circuit

### What It Computes

The kernel circuit is an Aiur program that implements the Ix typechecker:

```
kernel_circuit(env_data, const_data) → accept / reject
```

Given serialized Ixon data representing a typing environment and a constant,
the circuit checks whether the constant is well-typed in the environment.
This is the same computation that `Ix/Kernel2/` performs natively, but
expressed as an arithmetic circuit over the Goldilocks field.

Concretely, the circuit performs:
1. **Deserialize** the Ixon input (unconstrained witness)
2. **Re-serialize and hash** (constrained) to verify the witness matches the
   claimed content addresses
3. **Run the typechecker** on the deserialized constant: eval, infer,
   isDefEq — all the operations from the Kernel2 mutual block
4. **Output** accept (the constant is well-typed) or reject (type error)

### Circuit Structure

The kernel circuit is composed from the existing IxVM building blocks
plus new components for the typechecker:

| Component | Status | Description |
|-----------|--------|-------------|
| Blake3 | Exists (`Ix/IxVM/Blake3.lean`) | Hash computation in-circuit |
| Ixon serde | Exists (`Ix/IxVM/IxonSerialize.lean`) | Serialization/deserialization |
| NbE eval | To build | Krivine machine evaluation |
| NbE quote | To build | Read-back from values to expressions |
| isDefEq | To build | Definitional equality checking |
| Infer/Check | To build | Type inference and checking |
| WHNF | To build | Weak head normal form reduction |
| Iota/Delta/Proj | To build | Reduction strategies |

The eval/quote/isDefEq components are the largest part. They correspond to
the 42-function mutual block in `Ix/Kernel2/Infer.lean`, re-expressed in
the Aiur DSL.

### Bounded Computation

ZK circuits must have bounded execution. The kernel circuit uses fuel
parameters (matching the existing `DEFAULT_FUEL = 10_000_000` and
`MAX_REC_DEPTH = 2_000` bounds in Kernel2) to ensure termination. If the
fuel is exhausted, the circuit rejects — this is sound because rejecting a
well-typed constant is conservative (never a false accept).


## Part II: Generating vk_ix

### The Verification Key

When an Aiur program is compiled to a circuit, the compilation produces a
**verification key** — a compact cryptographic object that encodes the
circuit's constraint structure. Anyone with `vk_ix` can verify a STARK proof
that the kernel circuit accepted a particular input, without re-running the
circuit.

```
compile(kernel_circuit) → (proving_key, vk_ix)
```

The verification key is deterministic: the same circuit definition always
produces the same `vk_ix`. This is crucial — it means `vk_ix` is a
*function of the source code*, not of any particular execution.

### Why vk_ix Is Trustworthy

The verification key is trustworthy because the circuit it encodes is
provably correct. The argument has three layers:

**Layer 1: Specification (Ix/Theory/)**

The pure specification defines `eval_s`, `quote_s`, `isDefEq_s` on
mathematical objects (`SExpr`, `SVal`), and proves:
- NbE stability and idempotence (0 sorries)
- DefEq soundness (same normal form)
- Fuel monotonicity
- Eval preserves well-formedness

These proofs are Lean theorems — they are checked by the Lean kernel.

**Layer 2: Typing judgment and NbE soundness (Ix/Theory/, future)**

The `IsDefEq` typing judgment defines what "well-typed" means. The NbE
soundness theorems (see [kernel.md](kernel.md) Part V) connect the
computational specification to the logical judgment:

```
nbe_type_preservation:
    HasType env Γ e A → eval(e) = v → quote(v) = e' →
    IsDefEq env Γ e e' A
```

**Layer 3: Circuit equivalence**

The kernel circuit (Aiur) computes the same function as the specification
(`eval_s`, `quote_s`, `isDefEq_s`). This can be expressed as a Lean theorem:

```
theorem kernel_circuit_sound :
    kernel_circuit(env_data, const_data) = accept →
    well_typed(deserialize(const_data))
```

This theorem, once proven in Lean, is itself a Lean constant that can be
typechecked.

### The One-Time Native Check

Generating a *certified* `vk_ix` requires one trusted computation:

1. **Write** the kernel circuit in Aiur (a Lean program)
2. **Write** the formal proof that the circuit correctly implements the
   kernel specification (a Lean proof term)
3. **Run the Lean kernel natively** to typecheck the proof
4. **Compile** the circuit to produce `vk_ix`

Step 3 is the trust anchor. The Lean kernel runs on ordinary hardware,
without ZK, and verifies that the proof term inhabits the correct type.
This is a standard Lean `lake build` — if it succeeds, the proof is valid.

After this one-time check, `vk_ix` is certified forever. No further native
kernel execution is needed to verify ZK proofs against it.

### What Must Be Trusted

The trusted computing base for `vk_ix` is:

| Component | Nature | Size |
|-----------|--------|------|
| Lean kernel | Software (Lean4 kernel in C++) | ~10K LOC |
| STARK proof system | Cryptographic assumption | Goldilocks + FRI |
| Blake3 | Cryptographic assumption | 256-bit security |
| Aiur compiler | Software (Lean + Rust) | ~5K LOC |
| Hardware | Physical | One-time execution |

The formal proofs in `Ix/Theory/` do *not* need to be trusted — they are
*checked* by the Lean kernel, which is in the trusted base.


## Part III: Using vk_ix to Verify Constants

### CheckClaim Proofs

With `vk_ix` in hand, anyone can verify a `CheckClaim` without running the
kernel:

```
1. Prover has: a constant c with address addr = blake3(serialize(c))
2. Prover runs: kernel_circuit(env, c) → accept
3. Prover generates: STARK proof π that the circuit accepted
4. Prover publishes: CheckClaim(addr) + π

5. Verifier has: vk_ix + CheckClaim(addr) + π
6. Verifier runs: verify(vk_ix, claim, π) → accept/reject
```

If verification succeeds, the verifier knows that `c` is well-typed in
`env`, without seeing `c` or running the kernel. The ZK property means `c`
can remain hidden behind a commitment.


## Part IV: Using vk_ix to Certify Other Circuits

This is the key insight that makes bootstrapping powerful. An Aiur circuit
is just a Lean program. A *correct* Aiur circuit is a Lean program with a
proof of its properties. The kernel can check that proof.

### The General Pattern

Suppose we have an Aiur circuit `C` that claims to compute some function
`f`. To certify `C`:

1. **Define** `C` as a Lean program (in the Aiur DSL)
2. **Prove** in Lean that `C` computes `f`:
   ```lean
   theorem C_correct : ∀ x, execute(C, x) = f(x)
   ```
3. **Compile** the definition of `C` plus `C_correct` to an Ixon constant
4. **Prove** (in ZK, using the kernel circuit) that this Ixon constant
   typechecks:
   ```
   CheckClaim(addr_of_C_correct)
   ```
5. **Verify** the ZK proof against `vk_ix`

If verification passes, we know:
- The Lean kernel accepted `C_correct`
- Therefore `C` computes `f`
- Therefore the verification key `vk_C = compile(C)` is a correct
  verification key for `f`

### What This Gives Us

For any function `f` with a proven-correct Aiur implementation `C`:

```
vk_ix  ──proves──▶  "C correctly implements f"
                            │
                            ▼
                        vk_C = compile(C)
                            │
                            ▼
                    ZK proofs about f
```

The chain of trust:
- `vk_ix` is certified by the one-time native Lean kernel check
- `vk_C` is certified by a ZK proof verified against `vk_ix`
- Proofs about `f` are verified against `vk_C`

Each link in the chain is either a cryptographic verification (fast, no
trust in the prover) or the one-time native check (trusted hardware).

### Example: Certifying a New Hash Function

Suppose someone writes an Aiur circuit for SHA-256 and proves it correct:

```lean
-- In Lean/Aiur:
def sha256_circuit : Aiur.Toplevel := aiur { ... }

-- The correctness proof:
theorem sha256_correct :
    ∀ input, execute(sha256_circuit, input) = SHA256.spec(input) := by
  ...
```

To certify `sha256_circuit`:

1. Compile `sha256_correct` to Ixon → `addr_sha256`
2. Generate ZK proof that `addr_sha256` typechecks (using kernel circuit)
3. Verify proof against `vk_ix` → now `sha256_circuit` is certified
4. Compile `sha256_circuit` → `vk_sha256`
5. Anyone can now use `vk_sha256` to verify SHA-256 computations


## Part V: Worked Example — Certifying vk_C

This section traces the full lifecycle of certifying a third-party circuit's
verification key, from circuit definition through ZK-verified certification.

### Setup

Alice writes a circuit `C` that computes Poseidon hashing over the
Goldilocks field. She wants Bob to trust `vk_C` — the verification key for
her circuit — without Bob having to audit the circuit source code or run the
Lean kernel himself.

### Step 1: Alice Defines the Circuit in Aiur

Alice writes the Poseidon circuit as a Lean program using the Aiur DSL:

```lean
namespace Poseidon

-- The Aiur circuit definition
def circuit : Aiur.Toplevel := aiur {
  fn poseidon(input: [G; 8]) -> [G; 4] {
    -- full-round: add round constants, apply S-box, MDS mix
    let mut state: [G; 12] = pad(input);
    fold(0..4, state, |st, @r| full_round(st, round_constants(@r)));
    fold(0..22, state, |st, @r| partial_round(st, round_constants(@r + 4)));
    fold(0..4, state, |st, @r| full_round(st, round_constants(@r + 26)));
    return squeeze(state)
  }
}

end Poseidon
```

### Step 2: Alice Writes a Reference Specification

The specification is a pure Lean function — no circuit DSL, just math:

```lean
namespace Poseidon.Spec

def sbox (x : G) : G := x ^ 7

def mds_mix (state : Vector G 12) : Vector G 12 :=
  Vector.ofFn fun i => (Vector.ofFn fun j => MDS_MATRIX[i][j] * state[j]).sum

def full_round (state : Vector G 12) (rc : Vector G 12) : Vector G 12 :=
  mds_mix (state.zipWith rc (· + ·) |>.map sbox)

def poseidon (input : Vector G 8) : Vector G 4 :=
  let state := pad input
  let state := (List.range 4).foldl (fun s r => full_round s (RC r)) state
  let state := (List.range 22).foldl (fun s r => partial_round s (RC (r+4))) state
  let state := (List.range 4).foldl (fun s r => full_round s (RC (r+26))) state
  squeeze state

end Poseidon.Spec
```

### Step 3: Alice Proves Circuit Correctness

Alice proves that executing the Aiur circuit produces the same result as
the specification. This proof has two parts:

**Part A: The circuit's constraints are sound.** If the constraints hold,
the output satisfies the spec.

```lean
theorem Poseidon.soundness :
    ∀ input : Vector G 8,
      Aiur.constraintsHold circuit "poseidon" input output →
      output = Poseidon.Spec.poseidon input := by
  intro input h_constraints
  -- Unfold the circuit step by step
  simp [circuit, Poseidon.Spec.poseidon]
  -- Each full_round in the circuit maps to full_round in the spec
  -- The S-box constraint (x^7) is enforced by intermediate witnesses
  -- The MDS mix is a linear combination — holds by field arithmetic
  ...
```

**Part B: The circuit's constraints are complete.** For every valid input,
there exist witnesses satisfying the constraints.

```lean
theorem Poseidon.completeness :
    ∀ input : Vector G 8,
      ∃ witnesses, Aiur.constraintsHold circuit "poseidon" input
        (Poseidon.Spec.poseidon input) := by
  intro input
  -- The witnesses are the intermediate round states
  exact ⟨compute_witnesses input, by simp [compute_witnesses, ...]⟩
```

Together these establish:

```lean
theorem Poseidon.correct :
    ∀ input output,
      Aiur.execute circuit "poseidon" input = output ↔
      output = Poseidon.Spec.poseidon input := by
  exact ⟨soundness, completeness⟩
```

### Step 4: Compile to Ixon

Alice compiles her Lean development (circuit definition + specification +
proofs) through the Ix pipeline:

```
Lean constants:
  Poseidon.circuit        : Aiur.Toplevel
  Poseidon.Spec.poseidon  : Vector G 8 → Vector G 4
  Poseidon.correct        : ∀ input output, ...
        │
        ▼  (CanonM → CondenseM → CompileM → Serialize)
  addr_circuit   = blake3(serialize(compile(Poseidon.circuit)))
  addr_spec      = blake3(serialize(compile(Poseidon.Spec.poseidon)))
  addr_correct   = blake3(serialize(compile(Poseidon.correct)))
```

The address `addr_correct` is the content hash of the compiled proof. It
depends (via its Ixon `refs` table) on `addr_circuit` and `addr_spec`.

### Step 5: Generate ZK Proof of Type-Correctness

Alice runs the kernel circuit (prover side) to produce a STARK proof that
`Poseidon.correct` typechecks:

```
Prover inputs:
  env_data   = serialized Ixon environment (all dependencies)
  const_data = serialized Poseidon.correct

Kernel circuit execution:
  1. Deserialize env_data and const_data (unconstrained)
  2. Re-serialize and blake3-hash (constrained) — verify addr_correct
  3. Infer the type of Poseidon.correct:
       ∀ (input : Vector G 8) (output : Vector G 4),
         Aiur.execute circuit "poseidon" input = output ↔
         output = Poseidon.Spec.poseidon input
  4. Check this type is inhabited (it's a Prop in Sort 0)
  5. Output: accept

STARK proof generation:
  π_cert = prove(kernel_circuit, env_data, const_data)
```

### Step 6: Bob Verifies

Bob receives from Alice:
- `addr_correct` — the content address of the correctness proof
- `π_cert` — the STARK proof
- `vk_C = compile(Poseidon.circuit)` — the verification key for Poseidon

Bob runs:

```
verify(vk_ix, CheckClaim(addr_correct), π_cert) → accept
```

This takes milliseconds and requires no trust in Alice. Bob now knows:

1. There exists a Lean constant at `addr_correct` that typechecks
2. That constant's type asserts `Poseidon.circuit` correctly implements
   `Poseidon.Spec.poseidon`
3. Therefore `vk_C` is a verification key for a circuit that correctly
   computes Poseidon hashing

Bob can now use `vk_C` to verify Poseidon hash proofs from anyone.

### The Trust Chain (Summarized)

```
Lean kernel (native, one-time)
    certifies
vk_ix (verification key for the kernel circuit)
    verifies π_cert, which proves
"Poseidon.correct typechecks" (the circuit is sound)
    certifies
vk_C (verification key for Poseidon circuit)
    verifies
ZK proofs of Poseidon hash computations
```

Each arrow is either a cryptographic verification or the one-time native
check. No step requires trusting Alice's code — only the Lean kernel, the
STARK proof system, and Blake3.


## Part VI: What Circuit Correctness Proofs Look Like

The worked example above glosses over the hardest part: actually proving
that a circuit is correct. Two existing Lean projects provide concrete
proof methodologies at complementary levels:

**Protocol level** — [ArkLib](https://github.com/Verified-zkEVM/ArkLib)
formalizes Interactive Oracle Reductions (IORs): the cryptographic protocol
layer underlying STARKs. Each protocol step is an `OracleReduction` with
proven completeness and soundness. Security properties compose via sequential
composition with additive error bounds.

**Circuit level** — [Clean](https://github.com/Verified-zkEVM/clean)
formalizes individual circuit gadgets. Each gadget is a `FormalCircuit`
bundling the computation, a specification, and proofs of soundness
(constraints imply spec) and completeness (valid inputs have satisfying
witnesses). Gadgets compose via subcircuit abstraction — a proven gadget
becomes a trusted building block for larger circuits.

For detailed descriptions of these frameworks and how to adapt them to Aiur's
bytecode IR, selector-guarded constraints, and channel-based lookups, see
[aiur.md](aiur.md).

### Proof Structure for the Kernel Circuit

The full correctness argument for `vk_ix` combines three levels:

```
ArkLib level (protocol soundness):
  multi-stark proof system is knowledge-sound
  FRI commitment scheme is binding
  ────────────────────────────────────────────
Clean level (circuit soundness):
  blake3 gadget is correct
  Ixon serde gadget is correct
  NbE eval gadget is correct
  isDefEq gadget is correct
  ...
  ────────────────────────────────────────────
Ix/Theory level (specification soundness):
  NbE is sound w.r.t. typing judgment
  typing judgment is consistent
  ────────────────────────────────────────────
Conclusion:
  vk_ix verifies well-typedness correctly
```

Each level is proven independently and composed. Together, they give
end-to-end soundness: a proof verified against `vk_ix` implies genuine
well-typedness.


## Part VII: Self-Certification (The Bootstrap)

The bootstrapping loop closes when the kernel circuit certifies itself.

### The Argument

1. Let `K` be the kernel circuit (an Aiur program)
2. Let `K_correct` be the proof that `K` correctly implements the Lean type
   theory's typing judgment
3. Compile `K` to produce `vk_ix = compile(K)`
4. The native Lean kernel checks `K_correct` — this is the one-time trust
   anchor
5. Now, `K` can *also* check `K_correct` inside ZK:
   - Compile `K_correct` to Ixon → `addr_K_correct`
   - Run `K` on `addr_K_correct` → accept
   - Generate STARK proof π
   - Verify π against `vk_ix` → the kernel has certified itself

After step 5, anyone with `vk_ix` and π can verify that the kernel circuit
is correct, without trusting the original native execution. The native check
bootstrapped the system; the ZK proof makes it transferable.

### Why This Isn't Circular

The potential circularity: "the kernel proves itself correct." But the
argument is not circular because:

1. **The proof `K_correct` exists independently** — it's a mathematical
   object (a Lean proof term) that can be checked by any implementation of
   the Lean kernel, not just by `K` itself.

2. **The native check grounds the trust** — the first verification of
   `K_correct` happens natively on the Lean kernel (C++ implementation),
   which is an independent trusted base.

3. **The ZK self-check is a transferability step** — it doesn't establish
   correctness (the native check already did that); it makes the
   correctness *verifiable without re-running the native kernel*.

The situation is analogous to a compiler that compiles itself: the first
compilation uses a trusted bootstrap compiler, and subsequent
self-compilations only add convenience (reproducibility), not additional
trust.


## Part VIII: Incremental Verification

### Environment Accumulation

Real Lean developments have thousands of constants built incrementally.
The kernel circuit supports this:

```
1. Start with base environment E₀ (e.g., Lean's prelude)
2. For each new constant cᵢ:
   a. Prove: CheckClaim(addr(cᵢ)) in environment E_{i-1}
   b. Verify against vk_ix
   c. Extend: E_i = E_{i-1} ∪ {cᵢ}
```

Each `CheckClaim` proof is independent and can be generated in parallel
(for constants without dependencies on each other).

### Proof Composition

ZK proofs can be composed. A proof that "constants c₁, ..., cₙ are all
well-typed" can be compressed into a single proof using recursive
verification:

```
1. For each cᵢ: generate proof πᵢ that CheckClaim(addr(cᵢ)) holds
2. Generate a recursive proof π* that "πᵢ verifies against vk_ix for all i"
3. Publish π* (one proof, constant size regardless of n)
```

This requires a recursive STARK verifier circuit — verifying a STARK proof
inside another STARK. The Aiur framework supports this because the STARK
verifier is itself a computation that can be expressed as a circuit.


## Part IX: Circuit Certification for Third-Party Code

### The General Certification Protocol

For a third party who wants their Aiur circuit `C` certified:

```
Third party provides:
  1. C : Aiur.Toplevel               -- the circuit
  2. spec : α → β → Prop             -- the specification
  3. C_correct : ∀ x, spec x (execute C x)  -- the proof

Certification:
  4. Compile (C, spec, C_correct) to Ixon constants
  5. Generate CheckClaim proof using kernel circuit
  6. Verify against vk_ix

Output:
  7. vk_C = compile(C)               -- the certified verification key
  8. π_cert                           -- proof that C is correct
```

Anyone can verify `π_cert` against `vk_ix` and be convinced that `vk_C`
correctly verifies computations of `spec`.

### What Counts as a Correctness Proof

The proof `C_correct` can establish various properties:

- **Functional correctness**: `execute(C, x) = f(x)` for a reference
  implementation `f`
- **Input/output relation**: `∀ x y, execute(C, x) = y → R(x, y)` for a
  relation `R`
- **Type safety**: the circuit's Lean definition is well-typed (automatic
  from Lean's type system)
- **Equivalence**: `execute(C₁, x) = execute(C₂, x)` (two circuits compute
  the same function)

The kernel doesn't care what the theorem says — it only checks that the
proof term has the claimed type. The *meaning* of the theorem is between
the prover and the verifier.


## Part X: The Full Trust Model

### What You Trust

| Component | Trust basis | Eliminable? |
|-----------|-------------|-------------|
| Lean kernel (C++) | Audited software | No (trust anchor) |
| Hardware (one-time) | Physical | No (runs the native check) |
| STARK soundness | Cryptographic | No (hardness assumption) |
| Blake3 | Cryptographic | No (collision resistance) |
| Aiur compiler | Software | Partially (can be verified by `vk_ix`) |
| `Ix/Theory/` proofs | Checked by Lean kernel | Yes (verified, not trusted) |
| Kernel circuit | Checked by Lean kernel | Yes (verified, not trusted) |
| Any Aiur circuit | Checked via `vk_ix` | Yes (verified, not trusted) |

### What You Don't Trust

- The prover's hardware or software (ZK soundness protects against cheating)
- The correctness of any particular proof (verified cryptographically)
- The formal proofs themselves (checked by the kernel, not believed on faith)
- Third-party circuit implementations (certified via `vk_ix`)

### The Aiur Compiler Question

One subtlety: the Aiur compiler translates Lean programs to circuits. If the
compiler has a bug, `vk_ix` might not actually encode the kernel. This can
be addressed by:

1. **Compiler verification**: prove the Aiur compiler correct in Lean, and
   check that proof natively (adds the compiler to the one-time native check)
2. **Translation validation**: for each compiled circuit, generate a proof
   that the circuit's constraints match the source program (checked per-use)
3. **Multiple implementations**: compile with independent compilers and check
   that the verification keys agree

Option 1 is the cleanest and fits naturally into the bootstrapping framework.


## Part XI: Comparison with Other Approaches

### vs. Trusted Setup (Groth16, PLONK)

Traditional ZK systems require a trusted setup ceremony for each circuit.
Ix's bootstrapping eliminates per-circuit trusted setups: the one-time native
kernel check certifies `vk_ix`, and `vk_ix` certifies all other circuits
via formal proofs.

### vs. Unverified Circuits

Most ZK applications today use circuits that are correct "by construction"
(the developer is careful). Ix provides machine-checked proofs of
correctness, reducing the trusted base from "the circuit developer" to "the
Lean kernel + cryptographic assumptions."

### vs. Verified Compilers (CompCert, CakeML)

Verified compilers prove that compilation preserves semantics. Ix goes
further: the compilation target (a ZK circuit) can *itself prove* that
future compilations are correct, creating a self-sustaining verification
ecosystem.


## Part XII: Roadmap

### Phase 1: Kernel Circuit Implementation

Write the Ix kernel as an Aiur program. This requires expressing the
42-function mutual block from `Ix/Kernel2/Infer.lean` in the Aiur DSL,
including:
- Krivine machine evaluation with thunks
- NbE quote (read-back)
- Definitional equality with all reduction strategies
- Type inference and checking
- Inductive type validation

### Phase 2: Circuit Correctness Proofs

Prove that the kernel circuit computes the same function as the Lean
implementation. The existing `Ix/Theory/` proofs provide the specification;
the new work is bridging the Aiur implementation to this specification
(analogous to the Verify layer in [kernel.md](kernel.md) Part XII).

### Phase 3: vk_ix Generation

Compile the verified kernel circuit. Run the Lean kernel natively to check
all proofs. Publish `vk_ix` with the self-certification proof.

### Phase 4: Ecosystem

Build tooling for third-party circuit certification:
- Proof automation for common circuit patterns
- Incremental verification for large Lean developments
- Recursive proof composition for environment-scale checking


## Key References

### Ix
- [kernel.md](kernel.md) — Kernel formalization (NbE soundness, typing
  judgment, verification bridge)
- [compiler.md](compiler.md) — Compilation pipeline (content addressing,
  alpha-invariance, serialization)
- [zk.md](zk.md) — ZK layer (commitments, claims, IxVM circuits)
- `Ix/Theory/` — Formal specification and proofs (0 sorries)
- `Ix/Kernel2/` — Kernel implementation (Lean)
- `Ix/IxVM/` — Existing ZK circuits (blake3, Ixon serde)
- `Ix/Aiur/` — Aiur DSL definition and compilation
- `src/aiur/` — Aiur circuit synthesis and STARK proof generation

### Circuit Verification
- [ArkLib](https://github.com/Verified-zkEVM/ArkLib) (`~/ArkLib`) —
  Protocol-level verification: IOR framework, Sum-Check, FRI, STARK soundness
- [Clean](https://github.com/Verified-zkEVM/clean) (`~/clean`) —
  Circuit-level verification: `FormalCircuit` pattern, gadget soundness/completeness
