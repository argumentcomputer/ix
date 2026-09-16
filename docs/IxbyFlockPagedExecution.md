# Paged execution consumers

These components are part of the full functional Stage 3 implementation in
progress. They do not yet provide an original-CSLib execution proof. The
existing fixed-capacity Exec profiles, statements, and setup keys are unchanged.

## Frames and continuations

[`paged_frame`](../flock-stage3/host/src/ixby/paged_frame/mod.rs) connects frame
transitions to the actual addresses, write flags, and values consumed by the
authenticated memory log. A frame has at most 128 locals, indexed by its
continuation depth, and the physical stack supports 1,024 continuations.
Function and block positions admit 1,024 functions and 256 blocks per function.
The original program's local and continuation limits are checked separately
against full 64-bit limits.

A call saves the caller's function, target, and local count. The caller's
locals remain in its own memory bank. Return pops the authenticated header
and writes the result at the caller's next local position. Over-application
uses a distinct continuation containing the remaining immutable argument
vector. Tail calls retain the current depth.

Entering a function or appending constructor fields copies a previously
resolved vector one cell at a time. The carried state includes its source,
count, position, and destination base. The next instruction cannot start
before the exact copy completes. Copy steps preserve fuel; each logical
Eval, Apply, or Return transition consumes one unit, including terminal
return. Halted padding preserves both state and fuel.

Every batch must bind all five frame words, the remaining/consumed fuel word,
and both memory-root words. Instruction consumers must produce the actual
action wires, and the caller must feed every returned access to the same
ordered memory-log check. The component's standalone proof test publishes its
action sequence explicitly; it does not establish that a program produced it.

## Code and values

[`paged_code`](../flock-stage3/host/src/ixby/paged_code/mod.rs) derives code,
operand, declaration, alternative, and local addresses from the constrained
frame and indices. It rejects high-bit aliases, wrong frame sizes, invalid
opcode/operand combinations, and reads outside the live local prefix. All
accesses are read-only. Unused accesses read the canonical zero cell.

Packed code records preserve functional instruction and primitive tags.
[`paged_value`](../flock-stage3/host/src/ixby/paged_value.rs) checks the new
32-byte physical values: Nat has an immediate 128-bit magnitude; constructor
and PAP values contain an admitted declaration index and a heap field range;
bytes and strings contain a range in an actual byte bank. Scalar field values
are canonical Goldilocks elements. Literals cannot forge constructor/PAP
values. Allocation and source-range authentication remain separate obligations.

| Memory bank | Cell address base | Contents |
| --- | ---: | --- |
| Functions | `1 << 36` | Arity, entry, block count |
| Blocks | `2 << 36` | Headers, operands, alternatives |
| Constructors | `3 << 36` | Full ID, member/tag magnitudes, field count |
| Locals | `4 << 36` | 128 cells per continuation depth |
| Continuations | `5 << 36` | Resume or remaining-arguments record |
| Scratch | `6 << 36` | Resolved operands |
| Heap | `7 << 36` | Immutable field vectors |
| Program bytes | `8 << 36` | Original source bytes |
| Input bytes | `9 << 36` | Original input bytes |
| Dynamic bytes | `10 << 36` | Runtime byte data |

Each cell is 32 bytes. Byte pointers include the five-bit offset within a
cell. All cell addresses fit the approved 40-bit memory depth. Physical
capacities are independent of the semantic limits in the original program.

`PackedProgram::from_artifact` is an untrusted advice generator. Its full
original CSLib census contains 56,592 cells, including the unchanged
1,016,587 source bytes, 681 functions, 6,763 blocks and 15,298 operands. Every
packed block and operand passes the corresponding constrained consumer's row
check. This does not prove source-to-code admission: the streaming parser
still needs to constrain the writes and complete semantic reference checks.

## Local evidence

The numeric dispatcher binds the functional primitive tag and exact arity to
the existing Word32 and Goldilocks consumers, or to a new immediate Nat128
consumer. Nat128 addition and multiplication reject physical overflow;
subtraction saturates at zero. Division and remainder constrain the full
256-bit quotient/product identity and a remainder below the divisor, with
explicit zero-divisor semantics. Equality and ordering produce canonical Bool
values. Byte primitives produce requests for the separate byte consumer;
they cannot be accepted as completed numeric operations. String operations
remain outside this execution profile.

- Three Nat128 tests compare boundary values with exact native arithmetic,
  constrain every quotient/remainder advice bit, reject low-half-only product
  identities, and check the complete matrices and recycled-buffer padding.
- Two primitive tests check all functional tags and arities, unused operands,
  type rejection, and combined numeric wiring against independent results.
  A genuine combined instruction proof is still required.

- Five ordinary frame tests cover calls, tail calls, over-application, copy
  completion, semantic/physical bounds, all state padding, native/Boolean
  differential checks, and the combined frame/fuel/memory wiring.
- Two genuine 309,235-byte frame/fuel/memory proofs verify in fresh processes.
  Each checks six physical steps, four logical transitions, 18 memory accesses,
  eight touched cells, and a 16-billion-step budget. The fixture exercises
  function 680, block 184, 74 locals, and continuation depth 648.
- All 48 changed expected public words reject. Five locally valid, recomputed
  attacks changing a target, depth, copied value, saved caller, or fuel row
  reject at Flock's wiring check. Truncated and extended envelopes reject.
- The complete proof test, including both honest proofs, malicious proofs and
  fresh receivers, took 23.98 seconds with four Rayon threads. GNU time reported
  maximum RSS of 2,163,944 KiB; this is a per-process maximum, not a simultaneous
  parent/child sum.
- Three ordinary code-consumer tests cover all functional instruction kinds,
  exact address derivation, literal and local values, immediate Nat128 values,
  pointer boundaries, and full-width declaration/alternative indices.

The memory advice generator uses a native overlay during a batch and computes
Merkle paths once per touched cell at commit. The circuit still checks every
ordered access through the exact permutation and authenticated boundaries.

## Remaining integration

Connect original source admission and input initialization; operand gathering
and instruction dispatch; immutable allocation and primitive consumers;
complete execution boundaries and output serialization; and execution-proof
aggregation. Then prove representative original-CSLib segments and measure
the full run. None of the component results above substitutes for that run.

```sh
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml paged_frame:: \
  -- --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml paged_code:: \
  -- --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  frame_memory_proof_verifies_fresh_and_rejects_recomputed_steps \
  -- --ignored --nocapture --test-threads=1
```
