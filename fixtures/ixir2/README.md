# IxIR₂ snapshot fixtures

`expected.json` freezes the complete report for `ixir2-snapshot/1`: 12 snapshot
roots and sizes, 51 identity mutations, 56 boundary cases, 18,802 proper-prefix
rejections, and eight file-size checks. The normative byte grammar and proof
scope are in [the wire contract](../../docs/ixir2-wire.md).

The producer emits complete `.ixir2` binaries, full JSON inspection views,
boundary inputs, and the report into a new directory. Ten snapshots come from
actual checked Ixon maps or borrowed calls and preserve complete physical
execution and reclamation across decoding. `all-syntax` covers every sum tag
and cyclic declaration references; it is a codec fixture with intentionally
invalid ownership flow. `finite-context` and all source snapshots pass ingress.

```sh
lake build ixir2-fixture check-ixir2
./.lake/build/bin/check-ixir2 --fixture .lake/build/bin/ixir2-fixture
./.lake/build/bin/ixir2-fixture /tmp/new-ixir2-artifacts
```

The gate compares two fresh complete artifact sets, independently decodes
their binaries and checks the full JSON/source observations, probes the real
ingress APIs, and rejects 15 checker corruptions. The expected report is also
integrity-pinned in `docs/trusted-externs.json`. Review byte/root changes before
updating that report or its pin.
