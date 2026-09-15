# CSLib Stage 2 guest target

On 2026-09-15, recompiling the existing Stage 2 verifier with CSLib's native
keys and entrypoints produced an IXBF guest that accepts the retained CSLib
proof and returns its exact public claim. The source verifier and compiled
guest also reject a changed claim and trailing proof bytes. This is the
preferred full Stage 3 workload; the separately pinned
[Init guest](IxbyStage2GuestConfig.md) remains a fallback.

These are source and reference-execution checks. **No full-workload Stage 3
proof has been generated.** The [scaling plan](IxbyStage3ScalePlan.md) records
the remaining execution, memory and segment-composition work.

## Fixed configuration

The retained proof was generated from Ix revision
`a860e9197ba0c9c9240196095dc0f97d57e9cddb`. Its default native keys differ
from the older Init target. A fresh native process exported the keys,
checked the proof's content address and exact closed claim, and successfully
verified the aggregate with those keys.

| Configuration field | CSLib value |
| --- | --- |
| `ixvmKey` | 751,155 raw bytes |
| `verifyClaimEntry` | `766` |
| `aggregateKey` | 188,866 raw bytes |
| `aggregateEntry` | `243` |

BLAKE3 pins:

- IxVM key: `437565b17b2cff6838bd60f2b5c0dcbbe67dfd99fe594c96e017358893e22cda`.
- Aggregate key: `0fc0ebeb3f279c8673eae19c4b964adc0d2d6ec0dc50ad2061ff4cea9c6e4993`.
- Allowed identity: `cbb22937484f988ac555f63b35f9e8af5f44470cbb75b422acd414acb6e769c7`.

The 80-byte allowed-identity preimage is exactly
`BLAKE3(ixvm.vk) || u64le(766) || BLAKE3(aggr.vk) || u64le(243)`.
The keys retain the default native security configuration: 100 queries,
log blowup 2, cap height 0, binary FRI, constant final polynomial, no commit
grinding and 20 query-grinding bits. Function grouping remains enabled.

The guest still takes only canonical `CheckEnv(root, none)` bytes and a raw
native multiproof. Both keys and entrypoints are frozen into the image.
All source parser/verifier limits, the 16 MiB proof bound, the 16-billion-step
reference budget, primitive meanings and success/rejection ABI are unchanged.
This is a separately identified guest; it does not replace the Init pins or
change an existing Flock setup.

## Compilation checks

Compilation used Compilatrix checkout
`9e12065c4987c70ab321d7566f5d777aee48c4aa` and its existing Lean 4.33.0
libraries and compiler objects. First, the cached original adapter reproduced
the old 1,002,355-byte Init image exactly. The CSLib adapter changed only the
two key size/digest guards and the frozen verify-claim entry from 755 to 766.
The lowering implementation and pure source verifier were reused unchanged.

Two fresh compiler invocations produced identical 1,016,587-byte CSLib
images. The independent Compilatrix binary reader checked the image against
its inspection sidecar. Comparing the complete decoded old/new images found
only eight changed leaves in wrapper function 680: two key byte strings,
four corresponding length words and two copies of the verify-claim entry.
All other decoded fields and reference limits were equal.

The new image retains 681 functions, 6,763 blocks, 146 constructors and a
maximum frame size of 73 locals. These checks establish the observed change
and execution agreement; they do not supply an all-input compiler-refinement
or native-constraint certificate.

## Artifact pins

All hashes in this table are SHA-256; the key pins above use BLAKE3.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| Compiled CSLib image | 1,016,587 | `1c864b7a10614549f1bba23e465b9e70a9dabeff5615c5885aa0e55517ce3f09` |
| Unchanged `ixby-exec` | 119,481,384 | `d17f50b7d7b343ffa7e5c0c6b23c6e433987e971acb7e94539ee4d7503e76cfa` |
| Original `Ixon.Proof` envelope | 4,813,220 | `2b7825cf6e75c8442a0f4b339a441e2e263d5f02733be80853a9322f752e0395` |
| Raw native multiproof | 4,813,182 | `5a4a9142de2962345f73ae3cfbe6bca194366b6239cff1e307389b7e55efa99c` |
| Canonical public claim | 34 | `a8e13e51a1ef480f9385211a2cf3d939820ca7254f7fd564a473638502d0ecc3` |
| IXFI input | 4,813,238 | `8b03e43e9ec59ee9d82af519de11c2ca7930e09942ee5e0f85263e851ea0ffcc` |
| Exact successful IXFO output | 49 | `c810a2a4d205ae4ff03a0bb910f03c8f7824f572228a480d9c1c2eea2f2c7198` |

The Ixon proof address is
`b3c021c2e357cb89301026f014dd9385cc9fda8499fdc81e7be5539865ade418`.
The claim root is
`34477692f706b3e0fdd637cc60abd17c97025fd19b444661ed450a334799ebad`.
Its exact public serialization is `e5 || root[32] || 00`.

The source input is the raw multiproof, after checking and removing the
38-byte Ixon envelope. No expanded prover advice or proof-format translation
was supplied to the guest.

## Measured verification

Each source check ran in a fresh process using the unchanged pure Lean
verifier and this fixed configuration. Valid proof, changed claim and trailing
proof cases passed their expected acceptance/rejection checks in 4.32, 0.41
and 0.19 seconds respectively.

The compiled guest then ran on `john@3.21.127.50` with a 32 GiB per-process
virtual-address limit and a 7,200-second timeout. The positive run used one
CPU; the two rejection cases ran in separate processes concurrently.

| Compiled case | Exact result | Reference transitions | Wall seconds | Peak RSS, KiB |
| --- | --- | ---: | ---: | ---: |
| Original CSLib proof and claim | 49-byte success containing the public claim | 2,268,502,805 | 300.89 | 548,096 |
| Changed claim | 13-byte erased/rejection output | 928,153,535 | 112.42 | 564,684 |
| Trailing proof byte | 13-byte erased/rejection output | 323,262,983 | 40.20 | 346,660 |

All three interpreter processes exited successfully; rejection is an explicit
guest result. The downloaded inputs and outputs were checked against their
recorded hashes and exact expected encodings. The unchanged older Init guest
had rejected this CSLib proof; the recompiled guest accepts it without source
verifier or proof-format changes. This demonstrates compatibility for this
target, rather than a general compatibility claim across native versions.

These timings and memory figures measure reference execution, not Flock
witness generation or proving. In particular, reference transitions are not
a measured count of Flock rows.

## Retained reproduction files

The server archive is
`/home/john/work/ix-cslib-stage2-20260914.bR0RIt`; the successful guest run is
`/tmp/ixby-stage2-cslib.Y0FwwN`. The latter contains `stage2.ixby`, the
unchanged `ixby-exec`, `input.py`, `run.sh`, `negative.py`, exact inputs and
outputs, receipts, logs and timing files. The original archived proof and
store were preserved.

Local compilation files are in `/tmp/ixby-cslib-compile.FEWLTI`, including
`Stage2Ixby.lean`, both keys, `build.py`, `stage2-cslib-compile`,
`cslib.ixby`, its repeat and inspection, `compare-images.py`,
`decoded-changes.json`, and the source-check harness/results. Runtime copies
and receipts are in its `results.r7j8qX` subdirectory. The native key-export
harness is in `/tmp/ixby-stage2-cslib.nMlfwF`; its `results.tLBXAu` directory
contains the exported keys and native verification log.

For another server run, create a fresh `/tmp/ixby-stage2-cslib.*` directory
and copy only the program, interpreter and three scripts into it. Invoke
`bash run.sh <fresh-directory>` there, followed by
`python3 negative.py <fresh-directory>` under the same 32 GiB virtual-address
limit. The scripts check their pinned inputs and refuse to replace existing
results. Local image regeneration uses
`./stage2-cslib-compile "$PWD" compile cslib-replay.ixby` from the compilation
directory, with `LEAN_SYSROOT` and `LEAN_PATH` set as in `build.py`.
Scratch paths are run locations, not permanent artifact storage; use the
byte pins above when copying them to a later proving run.
