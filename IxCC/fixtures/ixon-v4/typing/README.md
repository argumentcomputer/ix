# Erased typing fixtures

These four anonymous Ixon v4 bundles (Nat, Nat.add, String, Quot.lift: 4,
18, 307 and 5 constants) were extracted with ix's `ix pack --anon` from the
producer's compilation of the primitive closure: `ix compile --consts` of
every [`primitives.tsv`](../primitives.tsv) name the toolchain has
(`String.Legacy.back` is not in Lean 4.34.1), after which `ix addr-of`
reproduces every other row of ix's committed table. No consumer encoder
generated their bytes. ix's Rust kernel (`ix check-rs --anon`) accepts all
four: 3, 15, 278 and 4 declaration targets.

**Frozen.** They are data, not regenerated: they are unbound (version-4)
environments, which the ix of this repository no longer writes (its `ix pack
--anon` of the role-bound primitive closure writes the whole role-bound
environment), and they are the pieces of the [catalogs](../catalog/README.md),
which are frozen too. They go when the switch to the certified kernel retires
the erased checker's typing tests. They were made by an earlier ix, whose
revision is not in this repository's history, with `ix compile --consts` of the
primitive names and `ix pack --anon` of each bundle; an `ix compile --unbound`
of this repository reproduced the four byte for byte while it had that flag.
[`provenance.json`](provenance.json) records the bundles' hashes, constant
counts and `main`, and the reference check of that time (the Rust kernel's
per-bundle target counts).

The required suite checks complete byte admission for each bundle, then
adds positive Nat/String literals, a proof of `20 + 22 = 42`, and rejection
cases for incorrect literal typing, UTF-8, primitive profiles and arithmetic.
Upstream MIT/Apache licenses are retained in the parent directory.
