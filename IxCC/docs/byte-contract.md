# The byte contract: what a compile claim is about

Written 2026-11-10. **Status:** IxCC reads both envelopes below, takes its
pinned identities from the role table of a role-bound one, computes every
address with pure BLAKE3, and its compile claim names the role table beside
the root (all implemented). Every committed fixture is role-bound, written by
this repository's `ix` ([corpus](corpus.md)); only the erased checker's typing
bundles and the catalogs over them are frozen unbound data.

A statement of the [end-to-end plan](end-to-end.md) has two premises about
content addresses: that the kernel's reading of the closure of the *seeds* (the
target and the theorems the unfolding table names) has a model with the
kernel's laws, and that IxCC's checked source program is faithful to that
reading, with typing derivations for what it runs. A consumer that proves
claims about the same seeds discharges them, or a native kernel run does.
Neither means anything unless IxCC compiles from the records those proofs are
about. This page says exactly which bytes IxCC reads and how they are
identified, so that a compile claim can be compared term for term with a
kernel claim about the same constants. (Until 2026-11-11 the first premise was
stated as acceptance of the artifact with root `H` under its table `ρ`; the
[certification design](certification-design.md#the-restatement-of-2026-11-11)
says why that was the wrong shape.)

## The artifact

An `.ixe` environment, as `ix compile` writes it (`Ixon.Env.putEnv`,
`Ix/Ixon.lean`). All integers marked N0 are TagN integers with a 0-bit flag
(ix's codec, `IxCK/Ixon/Codec.lean`); every address is 32 bytes.

| Part | Bytes | Role-bound (`0xE5`) | Unbound (`0xE4`) |
| --- | --- | --- | --- |
| header | TagN(4): flag `0xE`, value 5 or 4 | `E5` | `E4` |
| root | 32 | the constant root `H` | the same |
| `main` | `00`, or `01` and an address | present | present |
| assumptions | N0 count, then strictly ascending addresses | present | present |
| **binding** | address `ρ`, N0 length, that many bytes | **present** | absent |
| §1 blobs | N0 count; per blob address, N0 length, bytes; ascending | present | present |
| §2 constants (records) | N0 count; per record address, N0 length, bytes; ascending | present | present |
| §3 hints | N0 count; per hint an N0 index delta and an N0 hint | present | present |
| §4–§6 metadata | names, named entries, commitments | present | present |

The role-bound envelope is the unbound one with the binding inserted after
the assumptions; nothing else differs. `ix compile` writes it by default;
`ix compile --unbound` writes the unbound one, which no committed fixture
uses any more (a bridge, to be removed).

### What identifies it

- **The root `H`** is the canonical Merkle root of the §2 addresses: sorted,
  deduplicated, leaves `BLAKE3(00 ‖ a)`, nodes `BLAKE3(01 ‖ l ‖ r)`, an odd
  node paired with 32 zero bytes, the empty set's root 32 zero bytes
  (`IxCC/IxCC/Ixon/Merkle.lean`). The root covers the records only. It does
  not cover the binding, the hints or the metadata.
- **The role table's address `ρ`** is `BLAKE3` of the binding section's
  bytes. It is the *binding hash* that ix's typing claims name
  (`ClaimContext.binding`, `Ix/Claim.lean`) and the `bindingHash` of a host
  admission statement (`Ix/HostAdmission/Codec.lean`).
- **A constant** is named by its record's address; a member of a `muts` block
  by the address of its projection record (`dPrj`, `iPrj`, `rPrj`, `cPrj`
  with that block and index, and empty tables), whether or not the file holds
  that record. The kernel's reader keys members the same way
  (`IxCK/Kernel/Ixon/Reader.lean`, "Keys").

So an artifact is named by the pair `(H, ρ)`; an unbound one by `H` alone.
Two artifacts with the same records and different role tables have the same
`H`.

### The hash

BLAKE3, unkeyed, 32-byte output, everywhere: records, blobs, the root's
leaves and nodes, the binding section, the projection keys of block members.
Every address IxCC computes uses the pure Lean implementation
(`Blake3.Pure.hash`; `Address.blake3` is `Address.blake3Pure`), so no address on
the verifier path comes from foreign code and every byte-level theorem rests on
the three standard axioms. (The erased checker keeps the Rust hasher for its
internal hash-consing keys, which are not addresses anything names.) The kernel's admission takes the
hash as a parameter (`IxCK/Kernel/Admission.lean`), and every theorem holds at
every hash; ix instantiates it with `Address.admissionHash`, which is pure
BLAKE3 by definition and is executed by the Rust implementation on a recorded
assumption that the two agree (`Ix/Address/Admission.lean`).

### Canonical bytes

Every record must be a canonical Ixon v4 constant: ix's bounded decoder
`Ixon.Canonical.deConstant` accepts it, and it re-encodes to exactly its
bytes. IxCC and the kernel's admission decode records with that same function
(`IxCC/IxCC/Ixon/V3/Wire.lean`, `IxCK/Kernel/Admission/Bytes.lean`).
*Canonical sharing* ([Ixon v4](../../docs/Ixon-v4.md)) is a requirement on
the producer, not something either reader checks: a record's sharing table is
the output of the one canonical construction, so its address is a function of
the declaration's expanded expressions. A statement about an address is about
whatever bytes hash to it, so neither premise depends on it; what depends on
it is that two producers compiling the same declaration name it by the same
address.

## Which records are the closure

Every §2 record is part of the closure the root covers, and IxCC reads every
one. For a role-bound artifact they are, by provenance:

1. **The requested closure**: the requested constants and the closure ix's
   compiler selects for them (dependencies, recursors, whole logical units and
   checker support).
2. **Role support**: the constants bound to roles, closed under the roles'
   blocks and dependencies, and their own closures, compiled from the same
   source.
3. **Certificates**: the theorems the role table names as evidence for the
   equations of the bound operations, and their closures.

`ix compile` binds every role whose constant is among these records, wherever
the constant came from: when the artifact keeps the certificates' closure (a
bound definition is specified by equations, as `String.utf8ByteSize` is), a
role constant that only that closure contains (for `String.utf8ByteSize`,
`Classical.choice` and `Nat.lor`) is bound too
(`Ix.RoleBinding.Compile.finalize`). A record that is a role's constant but is
not bound to it would be read as an ordinary declaration, and an unbound
`Classical.choice` as an axiom the kernel's strict check does not admit.

The three are not marked in the file and need not be: they are ordinary
records under one root, and the kernel admits them together. IxCC accounts
for each record kind it meets:

| Kind | What IxCC does |
| --- | --- |
| `defn`, `recr`, `axio`, `quot` | a Src constant (`Src.Ingress.readConsts`) |
| `muts` (a block) | one Src constant per member and per constructor, keyed by its projection address |
| `dPrj`, `iPrj`, `rPrj`, `cPrj` (projection records) | an alias of the member it names; a projection record that names no member of a block in the closure is refused (`src ingress: projection record … names no member of a block in the closure`) |
| §1 blobs | authenticated; read through the constants that reference them (`nat` and `str` literals) |
| assumptions | read; a reference to a constant the file does not hold is refused at ingress, so IxCC compiles only closed closures |
| §3 hints | read and range-checked, kept as advice for the erased checker; not covered by `H` |
| §4–§6 metadata | not part of the closure: kept as opaque bytes, never interpreted |
| the binding | authenticated, decoded, kept with the environment (`V3.Env.binding`) and read for the pins |

Which records the compiled program *reaches* is decided by the target, as
before; the rest are read and ignored. Support and certificate records cost
ingestion and erased typing, not compilation.

## The role binding

The binding section's grammar is the kernel's (`IxCK/Kernel/Ixon/RoleTable.lean`):
`E8 03`, a specification version byte, the bound roles (a role's index and
its address, indices strictly increasing), then the evidence entries (a
role's index, a count and that many pieces of evidence, each `00` or `01` and
a theorem's address). A role's index is its position in the kernel's
`Ix.Kernel.Role.all` (`IxCK/Kernel/Key.lean`). IxCC reads it with its own
decoder of the same grammar (`IxCC/IxCC/Ixon/V3/Binding.lean`), against the
kernel's role vocabulary imported from that module, so a change to the
vocabulary changes IxCC's reading in the same build. It refuses:

- a section whose bytes do not hash to its address;
- a section that is not exactly one canonical binding section (the kernel's
  `RoleTable.ofBytes` refuses the same inputs);
- a table that binds one address to two roles.

It does not check the table against the specifications (the version, closure
under blocks and dependencies, the evidence): that is the kernel's admission
(`admitBinding`), which premise (i) covers. The specification version is read
and reported, never compared with a value IxCC holds.

### Pinned identities

For a role-bound artifact, every identity IxCC treats specially is the
constant the table binds to the identity's role (`Src.Pinned.ofRoles`). An
identity whose role the table does not bind has no pin and is absent, as an
identity whose constant is missing from the closure is. For an unbound
artifact the fixed table stays (`Pins.fixed`, `IxCC/IxCC/Src/Syntax.lean`).

| IxCC identity | Kernel role |
| --- | --- |
| `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec` | `nat`, `natZero`, `natSucc`, `natRec` |
| `Bool`, `Bool.true`, `Bool.false` | `bool`, `boolTrue`, `boolFalse` |
| `Eq` | `eq` |
| `Decidable.isFalse`, `Decidable.isTrue` | `decidableIsFalse`, `decidableIsTrue` |
| the primitives `add`, `sub`, `mul`, `div`, `mod`, `pow`, `gcd`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `pred` | `natAdd`, `natSub`, `natMul`, `natDiv`, `natMod`, `natPow`, `natGcd`, `natBeq`, `natBle`, `natLand`, `natLor`, `natXor`, `natShiftLeft`, `natShiftRight`, `natPred` |
| the standard axioms `propext`, `Quot.sound`, `Classical.choice` | `propext`, `quotSound`, `choice` |
| the D12 allowlist (`Lean.opaqueId`) | none: keeps its fixed address |

The pins travel with the program (`Known.pins`), and every check of a pinned
identity on the recheck path compares with them: `Pinned.knownOk`, the `prim`
entries' address check (`Table.checkPrim`), the standard-axiom closure of
`eqn` and `csimp` theorems (`Table.isStandardAxiom`) and the allowlist
(`Table.validateOpaque`). `Src.Ingress.ofEnv_pins` states that ingress gives
the program the pins of the environment it read (`Pinned.pinsOf`).

Not identities, and so not taken from the table: the `lazy` rows
(`Pinned.lazyRows`), which are the producer's proposals (the table check
accepts a `lazy` entry for any definition of the right shape), and the
primitive table (`V3.PrimAddrs.canonical`, `Ixon/V3/PrimAddrs.lean`), which the
erased checker uses only to speed up its reduction of literals, and the
resource profile reads for its literal pins (`V3.checkLiteralProfile`) and its
`Eq` (`Resource.Addressed`).

## A compile claim and a kernel claim, term for term

The kernel typing claims of the certified IxVM work (pull request #678; not in
this repository) are `check` (one seed, a constant's address) and `checkEnv`
(the seeds are the leaves of a tree whose root the claim names, hashed as the
root `H` above is: leaves `BLAKE3(00 ‖ a)`, nodes `BLAKE3(01 ‖ l ‖ r)`). Their
consistency statement covers a claim in the default context: the binding the
kernel's default role table (every role bound), validated, no user axioms, no
assumed leaves. It concludes that the kernel's reading of the closure of the
seeds, under that table, has a model; it says nothing about an artifact or its
root, and it refuses a seed that is `unsafe` or `partial`.

| Term | Compile claim (`CompileClaim`, `Ix.Claim.compile`) | IxVM typing claim (`checkEnv`, default context) | Host admission statement |
| --- | --- | --- | --- |
| records | `env` = `H`, the artifact IxCC read | none: records are found by address | `contentRoot` = `H` |
| seeds | `target`, and the theorems the image `D` names (planned field) | `root`: the root of a tree whose leaves are the seeds | `main` |
| role table | `roleTable` = `ρ`, the artifact's; absent for an unbound artifact | `ctx.binding` = the default table's address | `bindingHash` = `ρ` |
| specifications | not named | `ctx.spec`, the specification digest | `hostSpecDigest` |
| axioms beyond the standard three | not named: the producer's admission refuses relevant axioms, and the table admits only the standard three in the closure of an `eqn` or `csimp` theorem | `ctx.axioms` = none | the policy |
| hash | BLAKE3 | BLAKE3 | BLAKE3 |

A consumer pairs a compile claim with an IxVM claim by the seeds and the
table, not by `(H, ρ)`: the IxVM claim's leaves include the target and every
theorem the image's table names (one claim: two claims give two unrelated
models), and the compile claim's `ρ` is a restriction of the default table
(each role `ρ` binds, bound to the same address and evidence there), with the
closure of the seeds holding no constant of a role `ρ` leaves unbound, which
`ix compile`'s role selection ensures. The second condition is decidable from
the two tables' bytes and the records; the lemma that it makes the two
readings the same is planned beside the kernel's reader. A `checkEnv` claim
whose root is `H` itself is refused by IxVM, since every `ix compile`
artifact holds `partial` records.

The compile claim is the header `E8 05 04 07` (validator 7), then `env`
(32 bytes), the role table (`00` for none, or `01` and its 32-byte address),
`target` (32), the policy (one byte), the ABI arity (N0) and `elfHash` (32):
103 bytes in all for an unbound artifact and 135 for a role-bound one when the
arity takes one byte, on both sides
(`IxCC/IxCC/CompileClaim.lean`, `Ix/Claim.lean`, `crates/ixon/src/proof.rs`).
The former payload without the role table (validator 6) is refused.
`CompileClaim.verifyBytes` and `Ring0Sip.verifyBytes` accept a claim only when
the environment's root and role-table address are the claim's, and their
soundness theorems state both (`verifyBytes_immortal_sound`,
`verifyBytes_zeroRc_sound`, `verifyBytes_plainRc_sound`,
`verifyBytesRing0Sip_sound`).

## What is not yet so

- **The image is not named, so the seeds are not determined.** An image digest
  is to join the claim when the image exists ([roadmap](roadmap.md), DO-11);
  with it, the claim's target and `D` fix the seeds a paired IxVM claim must
  cover. Until then the table's theorems are fixed only by the certificate,
  which the claim does not bind.
- **The table restriction is neither checked nor proved.** By reading, an
  artifact's table binds each of its roles where the default table does
  (both come from compiling the same toolchain's library); no check compares
  them and no lemma says the readings then agree.
- **The premise's environment is not the one IxCC's kernel front end
  accepts.** That front end runs the kernel's tiered entry on the whole
  artifact under its own table and prelude; premise (i) is about the closure
  of the seeds under the IxVM claim's table and the committed prelude
  ([kernel front end](kernel-front-end-design.md#acceptance)).
- **The unbound bridge.** `ix compile --unbound` stays until it is removed
  (it has no IxCC user since the role-bound refreeze; the typing bundles and
  catalogs are frozen data, not regenerated). IxCC still reads the unbound
  envelope, with the fixed pins; its tests write it from a role-bound closure
  (`IxCCTests/Support/Envelope.lean`).
- **Two readings.** IxCC's decoder and the kernel's reader each read the
  bytes; they share the record decoder and, for the binding, the role
  vocabulary, not the framing or the reading into declarations. The plan
  replaces a proof that they agree by the faithfulness premise. The front end
  over the kernel ([kernel front end](kernel-front-end-design.md), the
  native-discharge milestone SP-N in the [roadmap](roadmap.md)) checks IxCC's
  reading against the kernel's at every key, declaration header, evaluated term
  and read type, and asks the kernel about its own reading; it is implemented
  beside the default front end.
