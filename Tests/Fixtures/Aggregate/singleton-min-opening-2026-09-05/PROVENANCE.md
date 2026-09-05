# Experimental minimum-opening-width singleton aggregate

This is a genuine `ix_aggr` shape-0 wrap using the explicit
`min-opening-width-v1` lookup-packing profile. Its IxVM child proof,
environment, subject tree, CheckEnv claim and IxVM key are byte-identical to
the [default-profile fixture](../singleton-2026-09-05/PROVENANCE.md). The
environment contains one well-formed axiom declaration: the certificate
checks its well-formedness, not a proof of the postulated proposition. The
canonical subject tree has no assumptions.

Only the aggregate system uses the new profile. It chooses circuit-local
lookup groups minimizing accumulator plus quotient opening width, subject to
the existing blowup/degree bound. User constraints, lookup order, main-trace layouts,
preprocessed commitments and the 175 active circuit heights are unchanged.
Both proofs still use blowup log 2, cap height 0, 100 binary-FRI queries,
20-bit query grinding, no commitment grinding and a constant final polynomial.
The aggregate key, allowed-key digest, outer claim and root are different.
Default system construction and the production CLI have **not** adopted them.

Generated on 2026-09-05 by `Benchmarks/FlockRootFixture.lean` in the
uncommitted Stage 3 worktree based on
`40cf786ac78990108701ac2f1ec5e3b5867f4410`, using Lean 4.33.1, multi-stark
`6ad074c1f2983ecdd7a56984d333441d6b38186a` and Plonky3
`3152b14a89067c83775a8076cc262ffc48a1fd7c`. No personal store/cache or
formalization workspace was used. This is one minimal fixture, not a
representative corpus or an independently audited profile.

## Identities

- Subject: `f7a3722c3ab8ad9d45a8cecf412c1d1cae92e2e453a8e923b7f466bfecd345a8`
- Subject-tree root: `71cbf135649af05f7cce8ba201a48e46556de51483f690cc6ec500a65530059c`
- Bundled claim: `CheckEnv(71cbf135649af05f7cce8ba201a48e46556de51483f690cc6ec500a65530059c, none)`
- Root wrapper BLAKE3: `635c8f79af8cf1a913cb9291fbd1aa1a3f2c4ff221e6ec1339795989c649910f`
- Root wrapper SHA-256: `4cab2c294c1ba5ed80f3481c8fe2854cf7842b9ef95be64bcbbc9edf3c44fb95`
- Aggregate key BLAKE3: `3c740f5b7645b1f7cdf361b7de3e20628c18ea3bf9cfafd1bd8aac4aca2bf7ba`
- Outer claim BLAKE3: `72e37e5dda38c176b1caaa377ea779ca285d8e614ca268aeb9130812fdc2216d`
- Child wrapper BLAKE3: `9381b528d31fdb23e8af24c6131bb3a3dd898f446848d295e4f8b0da24c7a618`
- Child wrapper SHA-256: `0795bff320f62034e76bb37e1ebf2e6da7968302a828242cc8e0041ba1236001`

`fixture.json` records every input/key/claim/proof file's length and BLAKE3
digest, circuit heights, native timings and memory measurements.
`execution.json` is the checkpoint from before aggregate proving. A directory
is complete only when `fixture.json` exists and explicit-profile verification
passes. Fixture metadata alone never selects a trusted key.

## Reproduction and verification

From the repository root, generate into a **new** directory:

```sh
IX_FLOCK=1 lake build ix bench-flock-root-fixture
flock_fixture_parent=$(mktemp -d /tmp/ix-flock-min-opening.XXXXXX)
(
  ulimit -v 67108864
  RAYON_NUM_THREADS=8 .lake/build/bin/bench-flock-root-fixture \
    --min-opening-width --output "$flock_fixture_parent/root" --prove
)
.lake/build/bin/bench-flock-root-fixture --min-opening-width \
  --verify "$flock_fixture_parent/root"
```

Without `--prove`, the harness proves/verifies the IxVM child and executes
the aggregate without proving it. Generation requires a Linux address-space
limit of at most 64 GiB and refuses existing destinations before writes. The
cap is an OS allocation guard, not an RSS prediction; allocation failure can
terminate the subprocess and leave an incomplete directory.

Verify these saved files without proving or writing anything:

```sh
.lake/build/bin/bench-flock-root-fixture --min-opening-width \
  --verify Tests/Fixtures/Aggregate/singleton-min-opening-2026-09-05
```

Verification checks bounded, digest-checked bytes, the exact singleton and
subject tree, both explicitly rebuilt keys, the expected outer claim and
both native proofs. Omitting the profile flag is an error. The normal
`ix flock-root` path rejects this experimental root with `InvalidProofShape`
under its unchanged production key. CI checks these boundaries and verifies
both fixtures in fresh processes; it does not regenerate native proofs.

## Measured costs

AMD Ryzen 9 7950X3D, 128 GiB-class RAM (`MemTotal=134128111616` bytes),
8 Rayon workers, 64 GiB address-space cap, 10 ms process-tree RSS sampling:

| Measurement | Default profile | This profile |
| --- | ---: | ---: |
| Active committed column widths, summed | 9,025 | 8,367 |
| Root wrapper bytes | 8,565,030 | 8,002,662 |
| Aggregate proof time, including execution | 75.813 s | 75.386 s |
| Aggregate proof sampled peak RSS | 25.26 GiB | 22.61 GiB |
| Native aggregate verification | 0.121 s | 0.228 s |
| Stage 3 canonicality rows, packed-check compiler | 3,162,519 | 3,056,107 |
| Stage 3 padded z/a/b, packed-check compiler | 192 GiB | 192 GiB |

These are single local runs. RSS includes retained system/runtime state,
not only incremental prover allocations. Widths are not height-weighted.
The native RSS model now uses the field's true extension degree instead of
inferring it from grouped lookup width; its historical calibration remains
approximate. The changed child prediction did not change its key/proof bytes.
Smaller native proof bytes and sampled proving RSS do not imply faster
verification or proportionally smaller Stage 3 memory.

Count this root safely without allocating its Flock witness:

```sh
(
  ulimit -v 16777216
  IX_FLOCK_TIMING=1 RAYON_NUM_THREADS=8 .lake/build/bin/bench-flock-root-fixture \
    --min-opening-width --count Tests/Fixtures/Aggregate/singleton-min-opening-2026-09-05
)
```

Count mode first verifies the fixture, then sets the table limit to `2^32`
and the padded-witness limit to **one byte**. It exits zero only after the
expected witness-admission rejection, emitting `ix.flock-stage3.fixture-count`
JSON on stdout and the exact shape count on stderr. No wiring is compiled and
no prover is started; `compiled: false` is intentional. Production admission
defaults remain unchanged. This count took 0.149 s with a 347 MiB process
high-water RSS, excluding native validation from the reported count time.

The initial Stage 2 packing experiment shrank Stage 3's largest table only
1.65%, leaving 768 GiB padded z/a/b. The query-point/denominator-sharing
compiler then reduced both profiles to `nu=23`, 8,388,608 rows and
**412,316,860,416 bytes (384 GiB)** of padded z/a/b alone. Packed canonicality
checks subsequently reduce both profiles to `nu=22`, 4,194,304 rows and
**206,158,430,208 bytes (192 GiB)**. This profile now has 3,056,107 packed
canonicality rows, versus 3,162,519 under the default Stage 2 key. All native
fixture bytes and other Stage 3 table row counts are unchanged.
No Flock proof or evaluated relation was produced for this real aggregate.
See the [paired measurement](../../../../flock-stage3/measurements/stage2-lookup-packing-2026-09-05.json)
for the original paired counts and circuit-width changes, and the
[query-sharing measurement](../../../../flock-stage3/measurements/pcs-query-sharing-2026-09-05.json)
for the preceding compiler and the
[canonicality-packing measurement](../../../../flock-stage3/measurements/packed-canonicality-2026-09-05.json)
for current per-gate counts on the same unchanged native fixtures. Deployment
adoption requires explicit key/relation pins, further corpus measurements and
independent review; this fixture is not automatic authorization to adopt it.
