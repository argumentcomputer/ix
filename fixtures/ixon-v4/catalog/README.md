# Catalog-v2 reference files

Both catalogs commit the same three original anonymous environments, ordered
`Nat`, `Nat.add`, `Quot.lift`, with 4, 18 and 5 constants respectively. Nat.add
includes Nat's four constants; the union has 23. The source bytes are the
existing [`typing/` bundles](../typing/README.md).

`fat.ixc/` was assembled by the producer `ix` (the corpus manifests' binary,
version `4.34.1|0.0.1`, revision `be45a159`), with `lake exe refreeze-ixon
catalog`, which runs, from the typing bundles:

```sh
ix catalog assemble --labels Nat,Nat.add,Quot.lift --toolchains 4.34.1 \
  --pins be45a159f1bb3629d109f742b950786ae8fc11f4 --deps '1:0' \
  fat.ixc Nat.ixe Nat.add.ixe Quot.lift.ixe
ix catalog verify --deep fat.ixc
```

`chunked.ixc/` is a separately constructed consumer fixture, not producer
chunk assembly. The same command writes it with
`CatalogFixtures.writeChunked` (also `lake exe tests-ixon-v3
write-chunked-catalog FAT OUT`), which frames (`envBytes`, `chunked`,
`manifestBytes`) a first-owner partition of the producer's original addressed bytes:
4, 14 and 5 constants. Each chunk retains its original blobs and anonymous
presentation sections, drops hints/main for omitted constants, and lists
omitted original constants as assumptions. No constant or blob preimage was
regenerated. The producer Rust `ix catalog verify --deep chunked.ixc` accepts
all files and the same 23-constant union. This check does not establish full
original member coverage or erased typing; the consumer tests establish those
additional executed checks. Its member toolchain and pin fields match
`fat.ixc/`.

`members.json` is a consumer witness containing the full 4/18/5 original
address sets, not the 4/14/5 owner slices. Tests authenticate every list against
its committed root/count and check first ownership, disjoint chunks and full
coverage. The witness format is not an upstream manifest extension.

Both profiles have members root
`93f5cb9a9b8215c4be11cffd6635f90974fac93141a998e9ac1646d8c59dad63`
and content root
`fd480b2813819f8babf38f86c533536b21b0d5c16b346dd9fae834990b09a7e4`.
The required compiled suite validates the retained bytes and these fixed
identities (ix's `ix catalog assemble` printed both roots, and `ix catalog
verify --deep` accepts both catalogs); it does not regenerate expected files
during the test.
