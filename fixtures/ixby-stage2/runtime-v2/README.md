# Current runtime fixture

Format 1, semantics 2. This independent 248-byte program exercises all eleven
runtime revision 2 opcodes, persistent nested arrays, unaligned immutable
builder chunks, and a slice. Its 21-byte input produces the exact 78-byte
output in 15 logical transitions. The 184-byte profile and expected statement
are independently encoded and committed.

The upstream 517,843-byte revision 2 root passes fresh local verification
against this statement. See the [integration record](../../../docs/ixby-runtime-v2.md)
and [artifact hashes/receipt](../runtime-v2-integration.json). The root is a
local upstream artifact, not embedded in this fixture directory.
