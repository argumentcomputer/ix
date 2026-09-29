# Catalog-v2 reference files

Both catalogs commit the same three original anonymous environments, ordered
`Nat`, `Nat.add`, `Quot.lift`, with 4, 18 and 5 constants respectively. Nat.add
includes Nat's four constants; the union has 23. The source bytes are the
existing [`typing/` bundles](../typing/README.md).

`fat.ixc/` was assembled on 2026-09-29 by the upstream `ix` binary (version
`4.34.0|0.0.1`), built with Lake from an unmodified `jcb/ix-compilatrix`
workspace at `0a31c8dbc63755924c645bf1afedc563e395e88a`. Its SHA-256 is recorded
in `provenance.json`. This is not a Nix build. Its command was:

```sh
ix catalog assemble --labels Nat,Nat.add,Quot.lift --toolchains 4.34.0 \
  --pins 0a31c8dbc63755924c645bf1afedc563e395e88a --deps '1:0' \
  fat.ixc ../typing/Nat.ixe ../typing/Nat.add.ixe ../typing/Quot.lift.ixe
ix catalog verify --deep fat.ixc
```

`chunked.ixc/` is a separately constructed consumer fixture, not producer
chunk assembly. `CatalogFixtures.envBytes`, `chunked` and `manifestBytes`
framed a first-owner partition of the producer's original addressed bytes:
4, 14 and 5 constants. Each chunk retains its original blobs and anonymous
presentation sections, drops hints/main for omitted constants, and lists
omitted original constants as assumptions. No constant or blob preimage was
regenerated. The producer Rust `ix catalog verify --deep chunked.ixc` accepts
all files and the same 23-constant union. This check does not establish full
original member coverage or erased typing; the consumer tests establish those
additional executed checks. Its member toolchain and pin fields match
`fat.ixc/`; the chunk files and `members.json` are unchanged since their
2026-09-16 construction.

`members.json` is a consumer witness containing the full 4/18/5 original
address sets, not the 4/14/5 owner slices. Tests authenticate every list against
its committed root/count and check first ownership, disjoint chunks and full
coverage. The witness format is not an upstream manifest extension.

Both profiles have members root
`beeaa41ba33be861b8c7c25a80e2f93293961b2cb95000a3471c3f782c0cfc5b`
and content root
`1a40750cd8a9de7506ded7fdcfb3141e8a2453eab2a02159b50dfd506e081f76`.
The required compiled suite validates the retained bytes and these fixed
identities; it does not regenerate expected files during the test.
