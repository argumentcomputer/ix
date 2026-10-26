# Host artifact admission statements

`ix check-lean complete.ixe` derives an `Ix.HostAdmission.Statement` for each
successful bound whole-artifact admission and reports its content address.
The statement commits to the actual admitted binding, current host
specification, complete record set, optional main, and admission kind.
Selected, capped and legacy unbound checks issue no host statement.

To persist and replay a statement:

```sh
ix check-lean complete.ixe --host-out result.ixhc
ix verify-host <reported-address> complete.ixe --statement-file result.ixhc
```

`--host-store` instead writes the checked statement to the ordinary content
store. Without `--statement-file`, `verify-host` reads that store. Both read
paths rehash the bytes at the requested address, decode exactly one canonical
statement, admit the complete supplied artifact again, and require exact
statement equality. Persisted bytes contain no trusted success marker.

The logical kind supplies the existing standard-three logical model. The
tiered kind additionally supplies typing over the opaque tier scope; permitted
unsafe tier axioms have no logical model. External artifact assumptions are
unsupported in both kinds. An unresolved thin bundle is refused rather than
completed from a store or assigned a closed statement.

The content root covers every actual prepared record address. The tiered
roots cover the two partitions of that same input, including projections.
Roots use the existing canonical Merkle grammar: byte-lexical sort and dedup,
BLAKE3 leaf domain `00`, node domain `01`, and 32 zero bytes for odd padding.
The host implementation is total, with a proved decreasing level reducer.
An empty partition is `none`; a zero-valued root remains a present address.
The complete bound input must have a content root.

The statement commits to `artifact.main` exactly. A present main must be an
actual input record. Version 1 claims whole-artifact admission, not that main
has a specified value or theorem type. Names and display metadata are outside
this identity. Referenced blob identities are committed by their record
bytes, and admission authenticates all provided blobs.

The separate host envelope is `IXHC`, version 1. It does not change shared
Claim/Proof format 4, the `.ixe` envelope, or IxVM public inputs.

| Field | Encoding |
| --- | --- |
| Magic, version, checked object format | ASCII `IXHC`, byte `01`, byte `04` |
| Kind | `00` logical; `01` tiered |
| Policy | `00` no external artifact assumptions |
| Host specification, binding, content root | Three fixed 32-byte addresses |
| Main | `00` absent; `01` followed by a 32-byte address |
| Logical and tier roots | Tiered kind only; two options in the same encoding |

Unknown tags, versions, object formats, truncations and trailing bytes refuse.
The statement address is BLAKE3 of all canonical envelope bytes. Verification
derives the current `Ix.SpecDigest.specDigest`; a stale proposed digest cannot
change the checker's specification. Its existing 8696-byte/version-2 frozen
guards live in `Ix.SpecDigest.Audit`, imported by both certificate and host
audits. The spec encoder and frozen values are unchanged.

The Rust module mirrors only the host codec and checks independent shared
vectors. Rust decoding alone provides no semantic admission. These target
receipts also provide no Source-value or `CompileCorrect` claim: that requires
the complete source/target relation and coherent Source value model for the
whole accounted-for closure. No such constructor is enabled by this envelope.
