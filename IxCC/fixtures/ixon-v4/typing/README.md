# Erased typing fixtures

These four anonymous Ixon v4 bundles (Nat, Nat.add, String, Quot.lift: 4,
18, 307 and 5 constants) were extracted with ix's `ix pack --anon` from the
producer's compilation of the primitive closure: `ix compile --consts` of
every [`primitives.tsv`](../primitives.tsv) name the toolchain has
(`String.Legacy.back` is not in Lean 4.34.1), after which `ix addr-of`
reproduces every other row of ix's committed table. No consumer encoder
generated their bytes. ix's Rust kernel (`ix check-rs --anon`) accepts all
four: 3, 15, 278 and 4 declaration targets.

`lake exe refreeze-ixon typing --ix IX --revision REV` makes them and writes
[`provenance.json`](provenance.json): the producer revision, binary digest and
version, the commands, the primitive environment's digest, and per bundle its
hash, constant count and `main`. With the ix of this repository it compiles
the closure with `--unbound` and records `ix check-lean` on the whole closure
as the reference check (every bundle constant must be one it passed); the
committed record, from the producer below, has the Rust kernel's per-bundle
target counts instead. The ix of this repository reproduces the four bundles
byte for byte. The producer is the
corpus manifests' (ix `be45a159`: the certified line `f829b760` plus the
local `--equations` export); this is not a Nix build. (The v3 bundles came
from ix's `Tests/IxonV3Primitives` program; its v4 successor,
`ixon-v4-primitives`, is a test executable of the full ix workspace, which
the CLI compilation replaces.)

The required suite checks complete byte admission for each bundle, then
adds positive Nat/String literals, a proof of `20 + 22 = 42`, and rejection
cases for incorrect literal typing, UTF-8, primitive profiles and arithmetic.
Upstream MIT/Apache licenses are retained in the parent directory.
