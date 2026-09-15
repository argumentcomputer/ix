# Aiur bytecode fixtures

The four `.bin` files are complete canonical `aiur-bytecode/1` preimages.
`expected.json` freezes their BLAKE3 roots and top-level counts. The grammar
and exporter contract are in [aiur-wire.md](../../docs/aiur-wire.md).

Expected bytes are handwritten in
[WireFixtures.lean](../../CompilatrixTests/Aiur/WireFixtures.lean), separately
from the production encoder. The required `check-aiur` gate compares fresh
encoding and replay processes against these files, then exercises corrupted
frames, roots, and component certificates. Changing a golden requires a
review of the grammar, source AST, expected bytes, and inventory together.

`unit-counter` contains a decrementing self-call and a zero branch.
`ranked-mutual` retains ranks on two mutually calling functions. These are
component-check examples, not proofs of bytecode execution or keyed AIR
acceptance. `wire-corpus` intentionally contains invalid SSA indices and
circuit partitions to cover every representable payload; it is exclusively
a serialization fixture.

No production IxVM export or constraint dump is included yet.
