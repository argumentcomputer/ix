# Source admission for paged execution

The paged execution memory now has constrained original-byte loading and
source-bound code capture. Complete program reference validation, typed input
initialization, output binding and full execution aggregation remain required.
These components do not yet establish a full CSLib execution proof.

## Original byte banks

[`source_bytes`](../flock-stage3/host/src/ixby/ixbf_decode/paged/source_bytes/mod.rs)
has separate fixed Program and Input setups. Each batch authenticates two
adjacent 1 KiB chunks and the exact final chunk to the same standard unkeyed
BLAKE3 digest. The final chunk binds the claimed length, including empty files.
The setup supports original files through 16 MiB.

The copy gate derives all 64 memory addresses from the chunk cursor and the
setup-owned bank. Its new cell values are the authenticated source words;
every old cell is constrained to zero. A missing second chunk and the bytes
after EOF produce zero cells. The shared memory-tree proof authenticates these
actual old/new cells to both memory roots. There is no host-selected address
list or native acceptance flag in this relation.

The nine public words contain one source identity `[length, digest2]` and two
`[chunk cursor, memory root2]` boundaries. A complete chain starts at cursor
zero and ends after the exact final chunk. Program loading starts at the
fixed empty memory root; Input loading starts at the Program's final root.
The full execution composition must constrain those stage links.

Four real **393,532-byte proofs** verify in fresh processes receiving only
their expected statements and proof bytes. Both Program and Input setups
cover an initial and final batch. Every changed public word and malformed
envelope rejects. Eight locally valid recomputed control, address, live-chunk
and byte substitutions reject at Flock's wiring check. Ordinary tests cover
empty files, exact chunk boundaries, odd chunk counts, EOF padding, full-width
metadata, poisoned row padding and complete native-memory root equality.

The fixed class has 64 leaves, at most 127 internal memory-tree nodes,
`nu=10`, `M=24` and 126,908 dense field words. Source authentication and memory
authentication share their compression table. The four-proof test took
20.30 seconds wall time, with 3,556,596 KiB peak process RSS and four Rayon
threads. This includes setup, fresh verifier processes and adversarial proofs.

## Source-bound packed code

[`code_capture`](../flock-stage3/host/src/ixby/ixbf_decode/paged/code_capture/mod.rs)
consumes the actual constrained Program dispatcher fields. It writes function
declarations, full constructor identities and field counts, block headers,
operands and case alternatives into the execution layout. Function/block
ownership and all write positions derive from the grammar's counters.

Seven capture words carry the current function/block, open flag, partial
header, operand count, pending scalar kind and a 256-bit case-constructor
bitmap. The bitmap rejects duplicate alternatives. A completed header passes
the same physical code checker used by instruction fetch, including primitive
arity and exact operand count. Local operands must reference the block's live
locals. The fixed profile captures Nat128 magnitudes, original String/Bytes
source offsets, canonical fixed scalars and Erased. UTF-8 partial steps and
batch padding preserve pending state without creating extra writes.

The batch authenticates source chunks, runs up to 32 actual parser/capture
steps and proves all generated accesses through the ordered memory log and
shared tree. It carries **all 30 parser words, seven capture words and two
memory-root words** at both boundaries, plus the three source identity words:
81 public words total. Its fixed class has 32 memory leaves, up to 255 parent
nodes, `nu=10`, `M=26` and 495,216 dense field words. Advice stops before any
source-page, step, cell or parent-node quota is exceeded.

Three real **452,899-byte joint proofs** verify in fresh processes. They cover
declarations, wide natural literals and byte payload references. All 81 public
word substitutions and malformed envelopes reject. Four locally valid
recomputed constructor-ID, write-position, Nat-magnitude and payload-range
substitutions reject at Flock's wiring check. Setup took 3.161 seconds; witness
evaluation plus proving took 0.399–0.728 seconds per honest proof with four
Rayon threads. These small batches are not full-execution throughput estimates.

The complete original 1,016,587-byte CSLib program passes **1,227 joint circuit
evaluations**, covering 37,878 parser events. Every intermediate boundary is
equal, the parser reaches EOF/Done, capture state closes, and the final memory
root equals the native packed program including its original bytes. Evaluation
took 51.961 seconds after setup and raw memory loading. Independently, every
captured typed cell equals the native packer's 24,823 typed cells. These are
circuit/differential checks; the complete 1,227-batch chain has not yet been
proved or aggregated.

`CompiledSourceBytes` and `CompiledCodeCapture` expose fixed compilation,
proving, verification and verified child-replay inputs. Setup is compiled
before examining any source, statement, advice or proof. Replay objects are
native witness material; recursive composition must constrain the complete
child verifier and its inherited claims.

## Remaining admission work

The code capture stage still needs a complete pass over admitted declarations
and blocks to prove constructor-ID uniqueness, entry-frame contracts,
forward/self-call and constructor arities, and successor-frame contracts.
All unreachable blocks must receive these checks. The older dense reference
checker does not provide scalable admission for this memory layout.

Input grammar events must materialize actual heap values and entry locals,
using the admitted program context. Initialization must derive the execution
parameters, fuel and entry frame. Final output bytes must be tied to the
halted value. The final relation must bind all source identities, memory/state
boundaries and the original Exec commitment format.

## Reproduction

```sh
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  ixby::ixbf_decode::paged:: -- --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  source_bytes_prove_fresh_and_reject_recomputed_copies \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  code_capture_proves_fresh_and_rejects_recomputed_events \
  -- --ignored --nocapture --test-threads=1
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_program_all_code_batches_match_native_packing \
  -- --ignored --nocapture --test-threads=1
```
