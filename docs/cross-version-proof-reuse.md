# Proof reuse across Lean versions

Status: design. Phase 1 is proposed for implementation; phases 2 and 3 are
gated on the measurements in phase 2.

This refines [primitive bindings](primitive-bindings.md) and the compatibility
policy in the [2026-10-08 handoff](lean-proof-reuse-handoff.md). The goal is
that a new Lean release, including each release candidate, invalidates only
the proofs whose statements actually changed, without hardcoding per-version
tables in ix and without slowing the proving path.

## What invalidates proofs today

Three separate mechanisms scope a retained proof, and each needs its own fix.

1. **The catalog profile pins the `ix` executable hash**
   ([`make_profile`](../crates/kernel/src/catalog_prove/mod.rs)). Any rebuild,
   including one that only bumps the Lean toolchain for the exporter,
   rejects every retained proof.
2. **The IxVM program embeds primitive addresses.** About 89 address
   constants such as `nat_addr` and `str_addr`
   ([Infer.lean](../Ix/IxVM/Kernel/Infer.lean)) and the Quot pins in
   `check_quot` ([Check.lean](../Ix/IxVM/Kernel/Check.lean)) are compiled into
   the circuit. A primitive-profile change therefore changes the IxVM
   verifying key.
3. **Claims carry no semantic context.** `Claim::Check { const_addr,
   assumptions }` ([proof.rs](../crates/ixon/src/proof.rs)) is meaningful only
   relative to the verifying key that checked it, including whatever
   primitive table that key embeds.

Content addressing already gives the right reuse unit: a proof is about the
Ixon object at an address. A constant whose address is unchanged across Lean
versions needs no new proof unless one of the mechanisms above discards it.

## Principles

### Proof identity is the verification identity

A retained proof's meaning is fixed by the circuits that verify it. The
aggregation protocol already defines that identity
([Protocol.lean](../Ix/Aggr/Protocol.lean)):

```text
blake3(ixvm vk) ‖ verify_claim index (u64 LE) ‖ blake3(ix_aggr vk) ‖ ix_aggr index (u64 LE)
```

The verifying keys commit to the circuits and to the commitment and FRI
parameters. The entrypoint indices are included because the circuit cannot
materialize its own function index. Every aggregation node pins this blob
transitively. Its digest, not a single key digest and not the executable
hash, is the replacement for `executable` in the catalog profile.

The identity must still be compared, not inferred. Identical primitive
profiles across two Lean versions are evidence that the generated circuits
match, but only equal identity digests establish it.

### The Lean→Ixon compiler is provenance, not proof identity

Deserialization, address hashing, typing, and primitive behavior all run
inside the circuit. The compiler only decides which object a Lean declaration
becomes:

- If it emits different bytes, the address changes and the declaration is
  proved again. Reuse is lost; soundness is not affected.
- If it emits identical bytes, reuse is correct, because the proven statement
  is about those bytes. Names live in metadata outside the address, so
  name-only changes fall here.

The compiler is trusted for faithfulness: the catalog's final statement is
that a snapshot's declarations type-check, and the snapshot's name→address
map comes from the compiler and exporter of that run. A miscompilation to a
different well-typed object is not detected by any proof, and was not
detected by pinning the executable hash either. Its defenses are the
decompile and recompile fidelity checks
([Ixon v3 verification](ixon-v3-verification.md)) and recording the compiler
and exporter identity in each snapshot record.

Reducibility hints are stored outside the address (`Env::anon_hints`), so a
compiler change can alter them without re-addressing. They are expected to
affect proving cost only; that the IxVM treats them purely as guidance must
be confirmed before relying on it.

### Literal interpretation belongs to each object

A string or natural literal is stored as a payload reference. Its type and
expansion come from ambient primitive addresses. Interpretation therefore
cannot be fixed per snapshot or per claim:

- Suppose constant `X` has a type containing `"a"` and was proved under String
  binding `S₁`. A newer constant `Y` that uses `X` reads `X`'s type. If `Y`'s
  leaf types that literal under `S₂`, `X`'s statement means different things
  in `X`'s proof and in `Y`'s proof.
- Requiring a single interpretation per snapshot avoids that inconsistency
  only by discarding every retained subtree with literals under the old
  binding, including its unrelated declarations.

Each literal should therefore reference its binding through the constant's
existing `refs` table. The binding address then participates in object
hashing, the [shard walk](../crates/ixon/src/shard_claim.rs), witness
construction, and assumption discharge like any other dependency. Objects
under old and new bindings coexist in one corpus. This also closes the
existing gap where the shard walk treats literals as blob references and
omits the literal-support declarations they depend on.

### Bindings are tagged facts with their own discharge rule

An assumption leaf today means "this constant is well-typed", and aggregate
verification expects no residual assumptions. "Address `a` may use the
native `Nat.add` rule" is a different proposition. Carrying such facts
through the assumption tree requires:

- a domain-separated, content-addressed binding object
  `Binding { role, addrs }`, where `addrs` includes support declarations the
  rule constructs (for example the `Bool` constructors returned by
  `Nat.beq`);
- a leaf rule: an address receives special treatment only when its binding
  is in the leaf's assumptions, and otherwise reduces as an ordinary
  constant;
- a specified discharge rule in aggregation, either a retained validation
  proof `Validate { binding }` proven once per binding, or an explicitly
  permitted residual fact in a revised verification contract.

Native admission checks performed by the verifier would be checking outside
the STARK. If used, the verification contract must say so.

For accelerations, binding facts cost no reuse in practice: if an
operation's definition changes, its address changes, and so does every
constant that references it.

## Role classification

| Category | Roles | Treatment |
| --- | --- | --- |
| Intrinsic kernel support | Quot type, ctor, lift, ind; Eq | `Quot(kind)` is supplied by the checked object and cannot authorize itself. Replacing the address pins requires checking each quotient's complete type and Eq support in the circuit. These addresses depend only on Eq and rarely change, so this is low priority. |
| Literal interpretation | Nat, zero, succ; String and its construction support, Char, `Char.ofNat`, List | Per-object literal bindings. |
| Accelerations | Nat and Int operations, Decidable shortcuts, BitVec, String operations | Binding facts validated by contract, with ordinary reduction when absent. |
| Trust extensions | `reduceBool`, `reduceNat`, `System.Platform.numBits` | Axiom policy, not the binding table. |

Ordinary reduction is a fallback only for accelerations of supported
definitions. Literal and intrinsic support have no fallback.

## Phases

### Phase 1: verification identity

1. Expose the aggregation identity digest.
2. Add a catalog-profile schema that uses it instead of the executable hash.
   Keep `objectFormat`, `structuralAbove`, and the axiom policy explicit.
3. Namespace leaf-cache and proof-store lookups by that identity. The store
   is currently keyed by proof hash and searched by claim
   ([run.rs](../crates/kernel/src/catalog_prove/run.rs)); a proof under
   another key fails verification and is re-proved, which is safe but
   wasteful.
4. Accept records under the existing profile schema only through explicit
   verification under their own identity, never by relabeling them.
5. Record compiler and exporter identity in each snapshot record.

Acceptance:

- A host rebuild with unchanged verifying keys and entrypoints reuses every
  retained proof.
- A changed verifying key or entrypoint index rejects retained evidence.
- Legacy records are either verified under their original identity or
  rejected; none are silently adopted.

This phase changes no circuit and needs no proving run to test.

### Phase 2: measure

For the CSLib exports under 4.34.1, 4.35.0-rc1, and 4.35.0-rc2, compare:

- the verification identity digests of the corresponding ix builds;
- the overlap of constant address sets;
- the exact chunk claims reusable from the previous catalog.

These separate avoidable executable-based invalidation from real declaration
churn. Upstream churn is expected to be the ceiling: Ixon addresses commit to
dependencies' values, so a changed proof of an `Init` lemma re-addresses
every downstream constant regardless of the kernel. Whether phase 1 alone
captures most of the rc→rc cost is a hypothesis this phase tests.

### Phase 3: format and circuit migration

Only if phase 2 shows enough reusable content behind changed primitive
bindings. The native checker, IxVM, object format, shard walk, witness
construction, claims, and aggregation change together:

1. Per-object literal bindings through `refs`. This is a one-time format
   change that re-addresses every constant containing a literal and adds a
   binding ref per such constant.
2. Binding objects, the leaf rule, and the discharge rule above. The IxVM
   reads bindings from its witness instead of embedded constants, so its
   verifying key no longer depends on the Lean version.
3. Validation proofs for accelerations, retained as long-lived content.
4. Full quotient type checking, if removing the Quot pins becomes worthwhile.

This phase changes the verifying keys once, so all retained proofs are
re-proved once. Afterwards a new Lean version needs validation for its new
bindings and new leaves only for re-addressed constants.

Acceptance, in addition to those in
[primitive bindings](primitive-bindings.md):

- Two String representations coexist in one retained corpus, and a newer
  constant using an older one types the older literals under the older
  binding.
- A leaf cannot apply a native rule to an address without the matching
  binding fact in its assumptions.
- Aggregation rejects undischarged binding facts unless the verification
  contract explicitly permits them.
- Replacing hardcoded comparisons with binding lookups, membership checks,
  and extra dependencies is measured for execution records, proof size, and
  proving time. Keeping the same shortcuts does not establish unchanged
  cost.

## Open questions

- The wire encoding of literal bindings and the bootstrap order between
  literal support and operations that themselves contain literals.
- Whether binding facts are discharged by in-circuit validation, by a
  verifier-side composite check, or by policy during a transition.
- Whether reducibility hints can affect acceptance, not only cost, in the
  IxVM.
