# Constrained functional records and reference checks

The `ixby::ixbf_decode` record components extend the
[original-wire codecs](IxbyFunctionalCodec.md) toward IXBF/IXFI/IXFO body and
value admission. They decode local records and check relations between their
fields. They do **not** yet implement the complete circuit parser, authenticate
source/registry lookups, admit IXBF to the native Exec factory, or prove Init.
The later [grammar-control component](IxbyFunctionalGrammar.md) now supplies
the record-selection, complete-state traversal and EOF relation, with explicit
remaining whole-file dispatch/authentication obligations.

## Original-wire records

`RecordDecodeGate` has a setup-owned `RecordKind`, eleven input words and eight
output words. Inputs are a `(byte offset, file length)` u64 pair, a canonical
Boolean enable word, three exact u128 bounds and 96 original lookahead bytes.
Outputs are six normalized fields, the next cursor/file-length pair and a
validity residual. Every unused field and padding bit is zero.

| Kind | Parsed record and local checks |
| --- | --- |
| `Metadata` | One minimal u128 LEB128 natural |
| `Count` | Natural count bounded by its declared limit and remaining file bytes |
| `Index` | Natural index strictly below the supplied record count |
| `Constructor` | Original 32-byte block identity, u128 member/tag/field count; operand limit |
| `Function` | Arity, entry block and block count; operand/local/block limits, valid entry index, remaining bytes |
| `Block` | Local-frame size and one of the eight instruction tags |
| `Alternative` | Constructor and successor indices, each checked against its supplied count |
| `Input` | IXFI format 1/semantics 0 at offset zero; root count, entry arity, operand/node limits |
| `Output` | IXFO format 1/semantics 0 at offset zero; one implicit root and sufficient node/byte budget |
| `Value` | Scalar/constructor/PAP/erased prefix; full constructor identity or function index, child count and supplied budgets |
| `Operand` | Local/literal/erased prefix; exact local reference when present |
| `Scalar` | Scalar tag, canonical Bool/u32/Goldilocks/extension payload when fixed-size |
| `Operation` | Operation prefix, original primitive tag/arity or leading constructor/function index and argument count |

The metadata class explicitly rejects encodings wider than 128 bits. This is
not a change to the functional format or the host reader, which still preserves
arbitrary-precision metadata. A constructor identity contains the full 256-bit
block plus its 128-bit member and tag in this class: 512 bits are compared, not
just a small tag or truncated digest.

Record width and table geometry do not grow with file length. All source bytes
after EOF must be zero; following records are not padding. Cursor addition and
file bounds retain every u64 carry. Disabled records preserve the cursor,
require zero lookahead and produce zero fields. Unused bound words are zero;
used bounds can remain wired from the surrounding context on disabled rows.

These are deliberately **prefix** relations where a body follows. A scalar
value prefix leaves its scalar unparsed. Literal operands leave the scalar at
the next cursor. Nat, String and ByteArray scalar prefixes leave their variable
payloads to dedicated decoding. Operation operands, post-operand projection
fields and successor indices are not silently treated as consumed. The caller
must constrain the grammar state that selects each kind and enable wire.

## Cross-record checks

`RecordLinkGate` uses a setup-owned relation, canonical enable, and two sets of
five u128 words. Its slot pins the only output, the validity residual, to a
verifier-owned zero. Disabled link rows require all input facts to be zero.

- `ExactArity`: matching reference/record index and exact argument/field count.
- `PartialArity`: matching function index and strict undersaturation.
- `SuccessorFrame`: matching target/block index, exact u128 addition of added
  locals, no overflow, exact successor frame and its declared local limit.
- `ConstructorValue`: equality of the complete constructor identity and arity.
- `DistinctConstructors`: distinct complete identities; a changed field count
  does not make a duplicate constructor declaration unique.

The call conformance circuit connects an operation's decoded target/count and
a function's decoded arity directly to the link gate. The constructor circuit
similarly connects decoded declaration/value identities and child counts. Both
pin actual record tags and enables to verifier-owned constants. Record indices
and lookup provenance still need the complete parser and authenticated registry;
these checks are not themselves a code-memory argument.

All eighteen new record/link variants have lazy count/emit parity, fully
initialized recycled witness buffers and constrained outputs/unused columns.
No existing Exec profile, setup key, primitive meaning, Flock pin or security
parameter is changed.

## Original record milestone evidence

The following counts and timings describe the original record-only milestone.
The later [grammar evidence](IxbyFunctionalGrammar.md) extends the same external
tests with constrained control rows and separate ByteArray count events.
The subsequent [scalar evidence](IxbyFunctionalScalars.md) also adds checked
payload cursors, guest Nat limits and UTF-8 to these original-source tests.

Ten new ordinary tests cover malformed/nonminimal/truncated records, all 45
functional primitive arities, canonical fields, u128 metadata, every constructor
identity bit, carry boundaries, source padding, disabled rows, poisoned buffers,
count/emission agreement and distinct proof tags/domains/fixed public templates.

Five new opt-in tests also pass:

- All 81 independent compiler programs match original-source record constraints:
  3,256 records and 946 reference/frame checks, covering all instruction forms,
  operation forms and primitive tags.
- Every original Init block interval is traversed exactly in the differential:
  37,260 records and 21,878 link checks, including all 146 constructors,
  681 functions, 6,763 blocks, 4,463 exact arities, 67 partial arities and
  10,585 constructor-identity pairs.
- The independent structured identity transport and exact Init I/O match the
  value-prefix/arity relations. Together they contain eleven value nodes,
  including constructor/PAP cases and the three real Init ByteArrays.
- Twenty-two new honest component proofs verify in fresh environment-cleared
  processes, including disabled decoding, both cross-record circuits, and an
  original Init call at byte 5,239 to function 9, whose header starts at 5,834.
- Twenty-one new locally valid, fully recomputed substitutions fail fresh
  global wiring verification. This includes replacing a decoded callee arity
  or constructor identity inside its consumer. Changed public words, fixed
  constants, proof kind/domain, truncation and trailing bytes also reject.

At that milestone, body traversal, forest structure and EOF were only native
test assertions. The later grammar component constrains their control relation
and exact payload extents; source identity and authenticated registry selection
remain outside these differentials. The later scalar layer constrains the
guest Nat-bit limit and String UTF-8; neither is a claim of these record gates
alone. Payloads still require authenticated source-position linkage.

The expected public vectors contain the supplied source windows and metadata.
They are **not full-file commitments or Exec statement digests**. A verifier
child gets only the approved component selector, expected public words and
complete proof bytes; it never runs the host reader. The `IXFCOD00` envelope
retains the original component tags/domains and assigns distinct new ones;
there is no fallback interpretation as an `IXBYEX00` execution proof.

| Conformance class | Inner `k_log` | Complete bundle bytes |
| --- | ---: | ---: |
| Metadata/count/index/block/output/operand records | 14 | 108,044 |
| Constructor/function/alternative/input/scalar/operation records | 15 | 107,516 |
| Value prefix | 16 | 107,028 |
| Exact arity/constructor identity/distinct identities | 12 | 108,460 |
| Partial arity/successor frame | 13 | 107,892 |
| Decoded call and callee plus arity link | mixed | 108,820 |
| Decoded constructor declaration/value plus identity/arity link | mixed | 112,116 |

These sizes exclude the externally expected public words. All use the
unchanged Flock pin and admitted Fast128 PCS profiles. They measure local
component relations, not full-program or five-billion-step execution cost.
Together with the earlier codec tests, all eleven opt-in tests cover thirty-six
honest proofs and twenty-seven recomputed negative proofs.

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --workspace ixby::ixbf_decode:: \
  -- --test-threads=1
IXBY_IXBF_CORPUS=/path/to/compiler-corpus \
IXBY_IXBF_STAGE2_IMAGE=/path/to/stage2.ixby \
IXBY_IXBF_INIT_INPUT=/path/to/init.ixbi \
IXBY_IXBF_INIT_OUTPUT=/path/to/init.ixbo \
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --workspace ixby::ixbf_decode:: \
  -- --ignored --test-threads=1 --nocapture
```

The measured opt-in runs use four Rayon workers, a 32 GiB virtual-address
limit and a 600-second timeout. No cloud restart or larger resource envelope
is required for this component milestone.
On 2026-09-14, the complete warm eleven-test run took 18.53 seconds wall time
and reported 274,196 KiB maximum RSS, including original-artifact differentials,
all thirty-six honest proofs, twenty-seven forged proofs and isolated verifier
children. This is a combined test-run measurement, not a single-proof timing
or an estimate of Init proving. Full workspace regressions also passed:
197 Stage 3 tests and 266 Stage 4 tests, with strict Clippy and formatting clean.

## Remaining admission work

The [grammar layer](IxbyFunctionalGrammar.md) now constrains required record
kinds/bounds, complete ordered control traversal, cursor continuity, final EOF
and preorder-forest completion. The scalar layer adds checked payload packing,
guest Nat limits and UTF-8. The later [generic dispatcher](IxbyFunctionalDispatch.md)
derives selection and byte requests from actual state and proves complete
small-file grammars using one shared authenticated buffer. Larger files still
need scalable shared chunk authentication. Registry facts must be bound to
the original decoded records, including indices, ownership and forward
references. The native test walk is not a substitute for those links.

Remaining semantic work includes complete duplicate-alternative checks and authenticated
ownership/coverage of the full constructor and function registries. Afterwards,
the execution path still needs streaming witnesses, scalable memory/code access,
full-state segments and sound composition. Native/source refinement remains
separate. See the [scaling plan](IxbyStage3ScalePlan.md).
