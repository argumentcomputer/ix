# Primitive bindings across Lean versions

Status: Rust checker admission implemented; the object, witness, and proof
compatibility migration below remains a proposal.

The [2026-10-08 handoff](lean-proof-reuse-handoff.md) records the newer
direction toward a complete, immutable compatibility profile with predictable
reuse boundaries. The finer-grained reuse and dynamic fallback proposals below
remain research context; they are not the settled production policy.

The Rust checker accepts new bindings by declaration contracts rather than a
Lean-version allowlist. Nat literals require the inductive and constructor
shapes. String literals require a typechecked expansion through `String.ofList`,
`List.nil`/`List.cons`, and `Char.ofNat`; their types may be definitionally equal
to the required interfaces. The representation need not match a built-in
String layout. A changed interpretation does not establish compatibility with
historical proofs or with another kernel's literal interpretation.

New `Nat.pred`, `add`, `sub`, `mul`, `pow`, `beq`, and `ble` bindings can enable
accelerated reductions after checking their definition types and symbolic
recurrence equations. Validation uses an isolated checker with optional
shortcuts disabled. Literal-contract recursion is rejected. The results are
cached within a worker and invalidated when its declarations are replaced.
These checks are conditional on the referenced declarations, just like ordinary
per-declaration checking; certifying an environment still requires checking its
complete dependency closure.

Established native capabilities remain available when their own bindings match.
An unrelated String binding change, for example, preserves native Nat arithmetic.
Other new operations use ordinary reduction when their acceleration is not
validated. This includes unfamiliar well-founded Nat operations, String
operations, Decidable/BitVec shortcuts, and platform-specific shortcuts.
Quotient reductions require the canonical declaration types and Eq support.
There is no claim that fallback has the same proving cost as acceleration.

Primitive profile schema 1 records each role as present or absent. Absent roles
do not inherit old addresses. The loader and `prims info` require a complete
canonical object with the expected schema and role count; earlier experimental
profile files must be regenerated. The `.ixe` object format is unchanged.
Resource literal identities follow the selected primitive bindings.

Focused tests cover forged and conflicting operation bindings, circular
admission, invalid literal interfaces, new addresses, alternate String
representations, cache invalidation, and ordinary-reduction fallback. The
exported Init/Std environments for 4.35.0-rc1 and 4.35.0-rc2 pass the literal
contracts and all seven structural Nat recurrence checks. Both produce profile
`7bac5b5c18248ee46124550858a7dc13ac7e394fd81e4aef2f7f0b0eff63916c`.
The exported-environment regression can be rerun with:

```sh
IX_TEST_PRIMITIVE_ENV=/path/to/initstd.ixe cargo test --release -p ix-kernel \
  --lib exported_lean_profile_admission -- --ignored --nocapture
```

This admission path is native Rust checking. It does not change the IxVM
program, literal wire references, shard dependencies, aggregate claims, or
catalog compatibility identity. In particular, loading a profile is not yet
authorization to reuse GPU proofs under that profile. Binding-dependent proof
reuse requires the migration described below.

Primitive content addresses should be validated input data to ix. A Lean
release that changes those addresses should ordinarily require new binding
data and compatibility evidence. A new ix checker release should be needed
when the supported typing, literal interpretation, or reduction rules change.

The goal is to preserve proof reuse for unchanged statements while allowing
multiple Lean versions in one retained corpus. This does not make different
definitions share an address or make an old proof establish a new statement.
CSLib and other library source code need no changes for this design.

Ixon currently stores a string or natural literal as a reference to a payload
blob, without an explicit literal-type binding. The Rust checker obtains the
type from `PrimAddrs`; the IxVM checker embeds corresponding addresses in its
program. A new `String` address can therefore require rebuilding ix even if
the typing rule is unchanged. The address can change because a transitive
dependency changes, without an edit to the declaration named `String`.
See [Ixon expressions](../crates/ixon/src/expr.rs),
[primitive addresses](../crates/common/src/prim_addrs.rs),
[Rust inference](../crates/kernel/src/infer.rs), and
[IxVM inference](../Ix/IxVM/Kernel/Infer.lean).

There is a separate compatibility restriction: the catalog proving profile
commits to the entire ix executable. A rebuild can therefore prevent catalog
reuse even when the checking program is semantically unchanged. Primitive
binding changes and executable identity need separate treatment.
See [catalog profiles](../crates/kernel/src/catalog_prove/mod.rs).

The proposed design has five parts.

1. **Separate primitive roles from concrete addresses.**

   The exporter supplies content-addressed bindings between supported roles
   and the actual declarations in its output. Lean version names remain
   provenance; identical binding data should have identical identity across
   toolchains.

   The checker validates the declarations and the conditions required by
   each special rule. An address table, a declaration name, or a matching
   function type is insufficient evidence. A function of type
   `Nat → Nat → Nat` is not necessarily addition, and an arbitrary type
   cannot acquire inhabitants merely by being assigned the `String` role.

   Bindings must preserve exact declaration identities. Recognizing two
   representations as supported does not establish definitional equality
   between their types.

2. **Make literal interpretation an explicit dependency.**

   A literal should identify both its payload and the binding that determines
   its type and interpretation. A schematic representation is:

   ```text
   Str { payload: blob_address, binding: binding_address }
   Nat { payload: blob_address, binding: binding_address }
   ```

   This is a logical representation, not an assigned wire encoding. The
   existing reference table could avoid repeating full addresses at each
   occurrence.

   A string binding identifies the type and the support needed to construct
   and reduce that literal, such as the relevant `String.ofList`, `List`,
   `Char`, and natural-literal bindings. A type address alone may leave the
   interpretation dependent on an uncommitted helper or ambient table.

   Keep literal construction bindings separate from optional operations such
   as string append. Including every operation would create unnecessary
   dependencies and could introduce cycles when operations contain literals.
   The encoding must establish an acyclic bootstrap or explicitly represent
   any required mutual dependencies.

   Bindings and their semantic dependencies participate in object hashes,
   dependency walking, witness construction, and claim coverage. Old and new
   literal bindings can then coexist: an old object keeps its original
   interpretation when a new toolchain is added to the corpus.

3. **Validate support before enabling specialized rules.**

   Literal typing and expansion must agree. A binding can justify an ordinary
   term expansion whose type is checked, or satisfy a supported representation
   contract that justifies equivalent compact processing. For strings, an
   expansion through `String.ofList` and character construction provides a
   useful starting point. Lean's kernel already relates string literals to
   constructor expansion; see the
   [Lean kernel implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/kernel/type_checker.cpp).

   Accelerated operations require stronger conditions than type correctness.
   Their reductions must preserve the conversion behavior the checker claims
   to implement. Suitable checks can include declaration shapes, definitional
   recurrence checks, or certificates verified by a fixed supported
   validator. An arbitrary propositional equality or type isomorphism is not
   permission to add a Lean definitional-equality rule.

   Validation must not use the very shortcut it is trying to justify. Check
   the defining data or certificate before enabling that operation's fast
   path. Bind any validation evidence to the exact declarations, validator,
   and permitted assumptions.

   A binding's identity commits to its semantic data and validation
   requirements. Replaceable proof bytes should remain separate evidence for
   a fixed validation claim, so a different proof of that claim does not
   rename every literal using the binding.

4. **Retain ordinary reduction as a fallback where it applies.**

   Separate required kernel support from optional accelerations. An unfamiliar
   address for an ordinary definition should be checked and reduced normally
   when that is supported. Missing an optimization may increase work without
   requiring a checker release.

   This does not provide a universal fallback. Quotient primitives, opaque
   native operations, and unsupported literal representations may require
   validated special support or a change to the checker. The checker should
   report an unsupported capability rather than invent a binding or silently
   use another version's semantics.

   Extending an optimization registry should not change the meaning of
   existing objects. Each applicable optimization must be justified for its
   exact target and representation, and preserve the established meaning.
   See the existing [reduction implementation](../crates/kernel/src/whnf.rs)
   and [quotient checks](../crates/kernel/src/check.rs).

5. **Scope proof compatibility to committed semantics.**

   Compatibility must bind the actual checking program, verification keys and
   proof parameters, object interpretation, and axiom policy. Replacing the
   whole-executable hash with a manually assigned version string would not
   establish compatibility.

   Bind primitive dependencies through the objects and claims that need
   them. Do not put the hash of an entire toolchain-wide primitive registry
   into every claim. An unrelated registry entry should not change a claim
   whose complete semantic dependencies remain identical.

   The dependency set must include implicit support used during typing and
   reduction, including support reached through dependencies. It must be
   enforced by the checker, rather than accepted as a prover-supplied list of
   lookups that happened on one execution path. The current
   [shard walk](../crates/ixon/src/shard_claim.rs) treats literal references as
   blob references; explicit binding dependencies require corresponding
   changes in both the native and in-circuit walks.

   Aggregation must enforce these identities and validate binding evidence
   while discharging dependencies. Every binding must be justified by checked
   evidence or remain an explicit permitted assumption. Sharing a proof store
   alone does not establish compatibility between different checking
   programs or semantic contexts.

Under this design, reuse follows the actual dependencies:

| Change | Expected reuse |
| --- | --- |
| New Lean RC with identical objects and bindings | Reuse unchanged claims under a compatible checker identity. |
| `String` binding changes, but a claim has no dependency on it | Reuse that claim. |
| A claim depends on the changed binding or changed declarations | Reprove the affected claim and the necessary aggregate path. |
| Historical objects still use the old `String` binding | Keep their objects and proofs under the original binding. |
| A host executable rebuild leaves the committed checker and verification identities unchanged | Permit reuse once the narrower compatibility mechanism is implemented. |
| The checking program or proof parameters change | Require explicit compatibility support or new proofs. |

Pinning toolchain provenance does not itself prevent content deduplication.
Unnecessary invalidation arises when every proof is scoped to a monolithic
toolchain profile. Conversely, a changed low-level declaration can affect a
large dependency closure even with precise bindings. Existing shard proofs
make the shard, rather than each individual declaration, the unit of reuse.

The certified kernel provides a relevant precedent. Its
[`checkBytesWith`](../IxC/Kernel/Admission.lean) entry accepts explicit pin
tables, a prelude, and Nat-operation pin variants. Its
[`checkBytesWith_has_model`](../IxC/Kernel/Admission/Theorems.lean) theorem
applies to arbitrary such inputs that pass the checked admission path.
The [reader](../IxC/Kernel/Ixon/Reader.lean) also accounts for literal support
as dependencies, and the [checker](../IxC/Kernel/Checker.lean) checks conditions
behind specialized Nat reductions. These are useful components and design
precedents. The model-existence result does not by itself establish the
soundness of an altered GPU checker, authenticate content addresses, or prove
complete compatibility with another Lean release.

Implementation should proceed as a deliberate format and checker migration:

1. Classify the current primitive entries into literal support, genuine kernel
   rules, optional accelerations, and native or platform-specific behavior.
   Specify the validation and fallback conditions for each category.
2. Define canonical binding records and explicit literal references, including
   bootstrap rules. Update serialization, native and IxVM checking, witness
   construction, dependency walking, and resource validation together.
3. Implement binding validation and reusable evidence. Make both backends agree
   on accepted bindings, reductions, and unsupported cases.
4. Extend claims, aggregation, and catalog compatibility to authenticate all
   semantic inputs. Retain the conservative executable restriction until its
   replacement is justified.
5. Preserve existing proof records under their original interpretation. New
   literal encodings change affected addresses; old proofs cannot simply be
   relabeled. Reuse across the migration requires an explicit verified bridge
   or support for the old checker and format.
6. Generate and compare bindings for each supported Lean release. Unchanged
   entries reuse existing evidence; changed entries are validated under the
   same rules when possible. Unsupported semantic changes require a checker
   update. Exporter compatibility with Lean remains a separate concern.

Acceptance checks should cover both soundness and reuse:

- Load two different `String` representations into one retained corpus and
  check that each literal retains its own type and expansion.
- Add or change an unused primitive binding and demonstrate unchanged claim
  identities, verified cache hits, and zero new leaf proofs for unaffected
  claims.
- Reject forged type bindings, operations with the correct type but wrong
  behavior, invalid or circular certificates, and missing binding dependencies.
- Confirm that alternate valid evidence for the same validation claim does not
  unnecessarily change literal or declaration addresses.
- Reject incompatible literal, constructor, and operation combinations across
  representations. Exercise literals appearing inside types and proofs as
  well as ordinary values.
- Compare native and in-circuit acceptance and reduction results. Require final
  aggregate verification with complete dependency coverage and the declared
  axiom policy.
- Measure binding validation, fallback execution, proof size, and incremental
  proving cost separately. Do not assume that accepting more versions has no
  performance cost.

The exact wire encoding, the initial supported representation contracts, the
placement of reusable validation evidence, and the mechanism for authenticating
checker identity remain design decisions. The required invariant is that an
object's meaning and a proof's statement cannot change when a different Lean
toolchain or primitive registry is available.
