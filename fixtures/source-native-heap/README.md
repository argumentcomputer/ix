# Allocating CFG native evidence

`expected.json` pins the reviewed `physical-leaf-cfg/1` report for five
source-produced and four direct physical CFGs. `native_harness.c` is an
independent arithmetic, resource, and ABI oracle. Generated JSON, canonical
IxIR₂ snapshots, and ELF objects are temporary gate outputs.

```sh
lake build source-native-heap heap-snapshot-object check-source-native-heap
.lake/build/bin/check-source-native-heap \
  --fixture .lake/build/bin/source-native-heap \
  --consumer .lake/build/bin/heap-snapshot-object \
  --cc cc --harness fixtures/source-native-heap/native_harness.c
```

The checker runs two fresh producers, independently decodes every complete
snapshot, checks fixed formulas and corruption rejection, and compiles each
persisted snapshot in a separate process. On x86-64 Linux it also links and
runs every object with guarded finite memory. See the
[contract and evidence](../../docs/source-native-heap.md) for the admitted
fragment, source/physical fixture distinction, exact workspace ABI,
successful-run theorem premises, limits, and counts. Update the reviewed
report only after inspecting intentional identity or code changes.
