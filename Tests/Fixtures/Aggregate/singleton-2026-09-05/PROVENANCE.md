# Current-protocol singleton aggregate

This is a genuine `ix_aggr` shape-0 wrap of an IxVM `CheckEnv` proof, not a
toy verifier circuit. Its environment contains one well-formed axiom
declaration. The certificate checks that declaration's well-formedness; it
does not prove the proposition postulated by the axiom. Both native proofs
use the production defaults: blowup log 2, cap height 0, 100 binary-FRI
queries, 20-bit query grinding, no commitment grinding, constant final
polynomial. The canonical subject tree has no assumptions.

The fixture was generated on 2026-09-05 by
`Benchmarks/FlockRootFixture.lean`, in the uncommitted Stage 3 worktree based
on `40cf786ac78990108701ac2f1ec5e3b5867f4410`. It uses Lean 4.33.1,
multi-stark `6ad074c1f2983ecdd7a56984d333441d6b38186a`, and Plonky3
`3152b14a89067c83775a8076cc262ffc48a1fd7c`. No personal store/cache or
formalization workspace was used. This is a minimal current-protocol
measurement, not a representative full-environment corpus.

## Identities

- Subject: `f7a3722c3ab8ad9d45a8cecf412c1d1cae92e2e453a8e923b7f466bfecd345a8`
- Subject-tree root: `71cbf135649af05f7cce8ba201a48e46556de51483f690cc6ec500a65530059c`
- Bundled claim: `CheckEnv(71cbf135649af05f7cce8ba201a48e46556de51483f690cc6ec500a65530059c, none)`
- Root wrapper BLAKE3: `254dcab734b79f1714d6c9b372ccdf8fcbad69e01fb90b51b0007f8cb6841406`
- Root wrapper SHA-256: `6ea804f334bf5a4f126c7f2713acc6636740a6789f10c23b42ea860857f8fada`
- Child wrapper BLAKE3: `9381b528d31fdb23e8af24c6131bb3a3dd898f446848d295e4f8b0da24c7a618`
- Child wrapper SHA-256: `0795bff320f62034e76bb37e1ebf2e6da7968302a828242cc8e0041ba1236001`

`fixture.json` records every input/key/claim/proof file's byte length and
BLAKE3 digest, native circuit heights, timings, and memory measurements.
`execution.json` is the checkpoint written before aggregate proving. The
fixture is complete only when `fixture.json` exists and verification passes.
The 116-byte environment and its canonical subject tree are included; no
external manifest is needed for this singleton certificate.

## Reproduction and verification

From the repository root, build and generate into a **new** directory:

```sh
IX_FLOCK=1 lake build ix bench-flock-root-fixture
flock_fixture_parent=$(mktemp -d /tmp/ix-flock-fixture.XXXXXX)
(
  ulimit -v 67108864
  RAYON_NUM_THREADS=8 .lake/build/bin/bench-flock-root-fixture \
    --output "$flock_fixture_parent/root" --prove
)
.lake/build/bin/bench-flock-root-fixture --verify "$flock_fixture_parent/root"
```

Without `--prove`, the harness proves/verifies the tiny IxVM child and only
executes the aggregate. Generation requires a Linux process address-space
limit of at most 64 GiB. This is an OS allocation guard, not a prediction of
RSS; an allocation failure can terminate the subprocess and leave an
incomplete output directory. Existing destinations are refused before writes.

To verify these saved files without proving or writing anything:

```sh
.lake/build/bin/bench-flock-root-fixture \
  --verify Tests/Fixtures/Aggregate/singleton-2026-09-05
```

Verification checks bounded, digest-checked bytes, the exact singleton
environment and subject tree, both current keys, the expected outer claim,
and both native proofs. CI runs this fresh-process verification; it does not
regenerate the high-memory native aggregate proof.

## Measured costs

AMD Ryzen 9 7950X3D, 128 GiB-class RAM (`MemTotal=134128111616` bytes),
8 Rayon workers, 64 GiB address-space cap, 10 ms process-tree RSS sampling:

| Operation | Time | Sampled peak RSS |
| --- | ---: | ---: |
| IxVM child proof | 0.189 s | 0.87 GiB |
| Aggregate execution alone, in the proving run | 1.652 s | 2.68 GiB |
| Aggregate proof, including its own execution | 75.813 s | 25.26 GiB |
| Aggregate native verification | 0.121 s | Not separately sampled |

RSS includes retained system/runtime state, not just incremental prover
allocation. The aggregate has 175 active circuits. The root wrapper is
8,565,030 bytes and the child wrapper 4,485,008 bytes.

The initial Stage 3 count required `nu=26`, 67,108,864 rows of uniform capacity,
and **3,298,534,883,328 bytes (3 TiB) of padded z/a/b alone**. The subsequent
shared-PCS/weighted-quotient compiler reduces the same unchanged root to
`nu=24`, 16,777,216 rows and **824,633,720,832 bytes (768 GiB)**. Query-point
and denominator sharing subsequently reduces it to `nu=23`, 8,388,608 rows
and **412,316,860,416 bytes (384 GiB)**, with 6,283,484 canonicality rows.
Packing two canonicality requests into the same 512-column row reduces it
again to `nu=22`, 4,194,304 rows and **206,158,430,208 bytes (192 GiB)**,
with 3,162,519 packed canonicality rows. The other table row counts and all
native fixture bytes are unchanged. The latest count took 0.155 s with a
350 MiB process peak under a 16 GiB address-space cap. Native
validation and counting pass, but production admission still correctly refuses
the root before wiring compilation. No Flock proof or evaluated relation
was produced for this fixture. See the retained
[baseline](../../../../flock-stage3/measurements/persisted-singleton-2026-09-05.json)
[PCS follow-up](../../../../flock-stage3/measurements/persisted-singleton-pcs-2026-09-05.json)
[query-sharing measurement](../../../../flock-stage3/measurements/pcs-query-sharing-2026-09-05.json)
and [canonicality-packing measurement](../../../../flock-stage3/measurements/packed-canonicality-2026-09-05.json).
