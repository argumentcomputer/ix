# Certified MMCS row hashing

The Stage2 compiler binds the pinned `MultiStark.Verify.Mmcs.hashRow` to a
certified runtime body. Each canonical field's eight little-endian bytes are
written into one immutable builder, which is frozen once per row before the
hash primitive. The generic width-eight encoding, the per-field byte appends,
and the source fold helper are no longer executed or compiled.

| Workload | Previous transitions | Row-hash transitions | Saved |
| --- | ---: | ---: | ---: |
| Stage2–CSLib | 254,245,163 | 227,780,761 | 26,464,402 (10.41%) |
| Stage2–singleton fixture | 500,247,577 | 458,512,092 | 41,735,485 (8.34%) |

Both runs preserve their exact outputs. The seven invalid singleton cases
retain their previous transition counts; they reject before any row is hashed.
These are logical reference-machine transition counts; native proving and
wall-time improvements are unmeasured. The singleton fixture is a smoke proof,
not a full Init verification claim. The baseline is revision
`b2ba553284aa49c8f8672f9c925e9cf0d52b8691`, including FRI fusion, ordinary
leaf-call inlining and single-dispatch array reads. Artifact identities and
execution evidence are in [row-hash.json](../fixtures/ixby-stage2/row-hash.json).
The earlier CSLib profile counted 447,726 hashed fields, so the saving is about
59 logical transitions per field.

## Helper bodies and certificates

The [emitter](../Compilatrix/Ixby/Runtime/Wire.lean) installs two functions
after the existing wire helpers. `Ixby.Runtime.rowBytesLoop` (function 108)
compares the index with the row size, reads the native element, converts the
erased Nat to a field, appends the field's eight canonical bytes to the
builder, and tail-calls itself; it freezes once after the last field.
`MultiStark.Verify.Mmcs.hashRow` (function 109) dispatches on the array view,
starts an empty builder, calls the loop, hashes the frozen bytes, and returns
a packed 32-byte digest. Erased `Fin` fields are Nat scalars in a native array,
so the packed and writer byte views cannot represent a field row; those
branches trap like an unreachable case. The vendored verifier and its
provenance pins remain unchanged.

The [complete body templates](../Compilatrix/Ixby/Runtime/Native/Code/Wire.lean)
are checked against every emitted and decoded Stage2 image, and the
[kernel proofs](../Compilatrix/Ixby/Runtime/Native/RowHash.lean) establish:

- `hashRow_bytes`: the source digest is the BLAKE3 hash of `rowBytes`, the
  concatenation of untagged eight-byte little-endian words, by definition.
- `rowBytesLoop_returns`: from any index, any existing builder prefix and any
  caller continuation, the loop returns the prefix followed by exactly the
  remaining suffix's words. Its premises are ten locals, 64 Nat bits, eight
  bytes of capacity, a row size below `2^32`, and builder capacity for the
  remaining fields.
- `hashRow_returns`: a native field row returns the packed source digest
  `(hashRow fields).bytes`, using one continuation slot, 32 bytes of digest
  capacity, and `8 * size` bytes of row capacity.
- `hashRow_packed_traps` and `hashRow_writer_traps`: byte views fail with
  `notConstructor` at the second transition, for any remaining fuel.

The loop costs eight transitions per field and `8*n + 5` from entry through
halt; the complete helper costs `8*n + 13`. The loop needs ten locals and the
helper one continuation slot. Ten new exact [axiom fences](../CompilatrixTests/Fences/IxbyRowHash.lean)
use only `propext`, `Classical.choice`, and `Quot.sound`, preserving all 2,771
prior assertions. All 107 earlier runtime/wire body certificates, their public
theorem premises, and the inliner's separate complete-image certificate are
unchanged; the inliner now protects the 110-function prefix. No upstream
source, reference primitive, runtime ABI, native interface, toolchain, or new
axiom is introduced.

This is a helper-body certificate at the same boundary as the wire helpers:
the installed body is proved against the reference machine and the pinned
source definition, and the frontend's differential source oracle compares the
installed and source-compiled images. It is not a kernel source-equality
replacement, and general typed LCNF source-to-Ixby refinement remains open.
Resource exhaustion need not occur at the same point in the shorter execution.

## Artifacts and validation

Both images shrink by 71 bytes and four blocks with an unchanged function
count: the source row hash and its fold helper are replaced by the two
certified bodies. The singleton image is 990,915 bytes; the CSLib image is
1,005,147 bytes. Each has 669 functions, 5,807 blocks, and 140 constructor
layouts. Maximum frame size remains 66 locals. The inliner selects 951
ordinary call sites. The 97 runtime helpers, the ten earlier wire helpers, and
the source reader body are unchanged up to the two-slot renumbering.

`check-ixby-lean` now runs 40,947 source-oracle helper executions, 109 caller
cases, 100 resource cases, and 525 exact transition formulas, and rejects
2,325 certificate mutations (1,460 structurally admitted). The row-hash cases
cover widths from zero to 64, boundary field values including `p - 1`,
arbitrary builder prefixes, suffix ranges, both byte-view rejections, local,
continuation, Nat-bit and byte-capacity limits, and one-less-fuel rejections.
The typed source suite adds eight `rowHash` comparisons through both the
source-compiled and installed paths, for 4,593 differential executions. The
existing inliner, FRI, binary, and eight serialized Stage2 execution gates
remain required. Fresh repeated compilation and an independent binary reader
check the frozen artifact.

```sh
lake exe check-ixby-lean
lake build CompilatrixTests.Proofs
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
lake exe stage2-ixby fixtures/ixby-stage2 valid /tmp/stage2.ixby
nix build .#checks.x86_64-linux.ixby-lean
```

`compile-no-fri` and `compile-baseline` retain the new runtime prefix while
disabling the optional source fusion and inlining; their pinned hashes are
updated accordingly. Historical inlining, array-read and FRI measurement
records remain unchanged.
