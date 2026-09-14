# Constrained original-byte source reads

`flock-stage3/host/src/ixby/ixbf_decode/source/` supplies fixed-shape byte
windows authenticated to the standard, unkeyed BLAKE3 digest of the original
file. It connects the existing compression gate to exact chunk/tree controls,
a constrained byte selector, and the existing header decoder. It does not
itself implement whole-file dispatch, registry admission or execution. The
later [generic dispatcher](IxbyFunctionalDispatch.md) supplies state-selected
decoding and a small-file proof that reuses one authenticated buffer.

These raw file digests are not the domain-separated Exec commitment chain.
No old profile, key, factory, buffer limit, Flock pin or proof decoder changes.
The source conformance envelope has its own identity and no Exec fallback.

## Read contract

`SourceCapacity::new(depth, window_bytes)` admits tree depths 0–54 and physical
windows 0–1,024 bytes. A depth `d` admits at most `2^d` chunks of 1,024 bytes.
Depth 54 handles every u64 file length; this component admission does not
enlarge any existing execution profile. The conformance setups use depth 14
(16 MiB) and seven-bit row domains. Empty files have one empty chunk.

`SourceReadSlots::read` receives:

- The exact cursor word `(offset, file_length)` and a narrow u64 `take`.
- Two words containing the externally expected raw BLAKE3 digest.
- Private first, next and final chunk proofs, in that order. Each contains
  64 byte words and two sibling-CV words per setup-owned tree level.

The offset must be at most the file length, the length must fit the chosen
tree depth, and `take` must not exceed the physical window. Chunk bytes beyond
their exact length are zero. The window contains exactly the requested source
bytes, zero after `take`, zero after EOF, and zero in partial-word padding.
The reader returns the constrained narrow file length and the window words.

The last chunk index is `saturating_sub(file_length, 1) / 1024`. The first index
is `min(offset / 1024, last)`; the next is `min(first + 1, last)`. The selector
uses the low ten offset bits over those two chunks. This also handles empty
files and aligned EOF reads without inventing an extra chunk.

All chunk data used by selection is the same wire data used by compression.
The indices and file length used by compression are the selector's actual
derived outputs, not host hints. Every chunk's final result is connected to
the same expected root. Validity residuals and all block/level positions are
fixed in the emitted circuit. Counting does not inspect witness data.

The caller must bind the root to the approved original artifact and the cursor
and `take` to the actual parser/payload operation. In particular:

- Header and record lookahead require their full fixed lookahead sizes.
- Direct whole-payload Nat decoding requires an exact-length window. The
  generic dispatcher instead reads fixed lookahead and constrains its
  first-terminator prefix mask before passing bytes to that decoder.
- UTF-8 needs an authenticated active window at its carried cursor; disabled
  or empty windows use a constrained zero take as required by that consumer.

An unconstrained private root, cursor or take is not a source-authentication
claim. The standalone proof publishes the externally expected root/query;
the header verifier additionally requires offset zero and take 272. The
[generic dispatcher](IxbyFunctionalDispatch.md) now makes these connections
for every record/payload in its explicit small-file proof class.

## Hash and length binding

The controls follow the original BLAKE3 tree, not the generic Merkle example's
hash-of-two-digests construction. Chunk compression uses its absolute chunk
counter, exact block length, and derived CHUNK_START/CHUNK_END flags. The
single-chunk root gets ROOT on its final active block. Parent compression uses
IV, counter zero, length 64 and PARENT, with ROOT at the length-derived final
parent. Missing right subtrees are promoted; inactive siblings must be zero.
Conditional CV selection is itself constrained, including its Boolean flag.

The definitions follow the [official BLAKE3 reference implementation](https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/reference_impl.rs).
Independent test advice uses the already pinned `blake3` 1.8.7 subtree API;
the cryptographic relation uses the existing Flock compression table. Neither
the native hasher nor the original source file is available to verification.

A path for an early chunk alone does not authenticate a claimed file length.
For example, an eight-full-chunk file's first path still matches the real root
when the claimant declares five full chunks: an opaque right sibling hides
the suffix. Therefore the reader separately authenticates the claimed final
chunk to the same root. Tests exercise this exact attack with valid first
and next paths, canonical padding, and locally valid recomputed final-path
rows. The final root equality must reject it.

## Geometry and scope

The three new Boolean gates have explicit input/output schemas:

| Gate | Inputs | Outputs | Depth-14 geometry |
| --- | ---: | ---: | --- |
| Block controls | 7 | 3 | `k_log=13`, 3,650 used columns |
| Path controls | 7 | 7 | `k_log=14`, 5,228 used columns |
| Window, 32 bytes | 130 | 7 | `k_log=16`, 41,745 used columns |
| Window, 96 bytes | 130 | 11 | `k_log=16`, 53,901 used columns |
| Window, 272 bytes | 130 | 22 | `k_log=17`, 88,057 used columns |
| Window, 592 bytes | 130 | 42 | `k_log=18`, 149,047 used columns |
| Window, 1,024 bytes | 130 | 69 | `k_log=18`, 227,239 used columns |

The window selector is a shrinking Boolean barrel selector, not a scan of
the entire file. Prefix masks share small equality/suffix computations rather
than performing a full-width subtraction for each output byte.

One depth-14 read emits one window, 48 block-control rows, 42 path-control rows,
90 compression rows and 90 two-word selectors. The header proof adds one
existing header-decoder row. This simple component authenticates three paths
on every read, even when they repeat. A scalable whole-file parser must share
chunk authentication across records and authenticate the final chunk once per
file, while retaining exact byte/cursor/root connections. The current cost
must not be multiplied over all Init records and advertised as a scalable
parser design or a full-guest proof estimate.

## Verification evidence

Seven ordinary tests pass. They cover all chunk offsets, every take/EOF pair
for the 32-byte window, full u64 controls, partial blocks and every padding
position, every output bit of the block/path/32-byte tables, unused columns,
recycled witness buffers,
lazy count/emit parity, and image-independent reader/header layouts. Native
tree differentials reconstruct every leaf of 229 source lengths, up to 34
chunks: 1,846 honest paths. Those are native/constraint component checks, not
1,846 cryptographic proofs.

Real source proofs use private envelope `IXFSRC00`, component tags 0/1 and
distinct `ix:ixby:ixbf-source-{read32,header}:d14:v0` transcript domains. Their
strict little-endian fixed-integer encoding rejects unknown kind/revision,
noncanonical encodings, trailing bytes and proofs over 8 MiB. Fast128 admission,
the pinned PCS geometry and the legacy compression backend are unchanged.

The verifier process has a cleared environment, runs outside the worktree and
receives only the component selector, externally expected values and proof.
It constructs its own fixed public template. It receives no source chunks,
path advice, artifact filenames or host-parser acceptance result.

| Component | Externally expected words | Fixed public words | Complete proof bytes |
| --- | ---: | ---: | ---: |
| 32-byte source read | 6 | 34 | 205,932 |
| Original-file header | 18 | 35 | 218,612 |

Expected values are root/query/window for reads, and root/query/14 decoded
fields for headers. The table excludes those expected values from proof byte
counts. Both setups have dense PCS geometry `m=22`. Original Init tests compare
header fields against the separate typed native parser before proving, and
authenticate the program, input and output against their original raw digests.
Header membership proves the header belongs to the committed original file;
it does not prove the rest of that file parses or executes correctly.

All fifteen combined codec opt-in tests pass: 58 honest proofs and 45
recomputed malicious proofs rejected with `Wiring(Gkr(ProductMismatch))`.
Twelve honest proofs and eight recomputed negatives are new source cases.
Negative cases include byte replacement outside the published window,
unchanged-output block-length replacement, sibling replacement, skipped
compression, altered compression counter/ROOT, header-body replacement that
preserves every decoded field, and the false-length attack described above.
Changed expected roots, query fields, output metadata and envelope bytes also
reject. All original corpus/Init record, grammar and scalar censuses pass
unchanged.

Full release workspace regressions pass 216 Stage 3 tests (36 opt-in) and
266 Stage 4 tests (39 opt-in), with zero failures. Both workspaces pass strict
release Clippy and formatting. The first combined codec run took 194.93 seconds
in the test body, 205.65 seconds wall including build contention/rebuild, and
reported 3,180,520 KiB maximum RSS. Workspace runs overlapped that run; these
are not isolated proof timings or aggregate concurrent memory measurements.
The final repeat, without a rebuild or overlapping workspace/lint jobs, also
passes all fifteen tests, 58 honest proofs and 45 recomputed rejections. It
took 170.61 seconds in the body, 170.82 seconds wall and reported 3,201,984 KiB
maximum RSS. This measures the combined suite and verifier children, not an
individual proof or an exclusive-host benchmark. Evidence is kept locally in
`/tmp/ixby-source-auth.mrjiz1/`. Earlier scalar milestone timings remain
historical, not measurements of source authentication. All jobs completed.

Use the ordinary and opt-in commands and four retained-fixture variables in
[the record document](IxbyFunctionalRecords.md). The full codec opt-in filter
also includes the two new source tests. No cloud machine is needed.

## Remaining work

The later [state-selected dispatcher](IxbyFunctionalDispatch.md) proves
complete small-file grammars using one shared authenticated buffer. Remaining
work includes authenticated typed record/payload materialization and scalable
shared chunk use for larger files;
authenticated registry ownership, coverage and forward references; complete
duplicate-alternative checks; and the explicit raw-file/Exec commitment bridge.
Execution still needs streaming witnesses, scalable code/memory access,
complete state segments with VM-derived global fuel, sound composition and
the full pinned Init proof. Native/source refinement remains separate.
The work stays local and uncommitted; EC2 has not been restarted.
