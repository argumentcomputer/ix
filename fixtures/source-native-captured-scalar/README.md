These nine synthetic Ixon sources export a lambda capturing one exact Word
Nat. Three bodies project the capture, branch between the capture and the
argument's predecessor, or compose predecessor/choice helpers. Each is
compiled separately for captures zero, seven, and the maximum Word through
the ordinary source compiler and actual physical CFG selector.

`expected.json` pins source and IR roots, selected and emitted function counts,
text hashes and sizes, finite stack bounds, and the full test inventory.
The producer emits nine ELF objects, nine full compiler snapshots, and one
report. The checker compares two complete fresh generations byte for byte.

All 171 boundary cases execute the source and intermediate applications,
physical bodies, typed native code, and complete ELF bytes. Initialization
allocates two slots and frees the temporary literal closure. Application
frees the captured export, leaving two dead slots, two frees and RC operations,
no reuse, and no live nodes. The independent artifact checker rejects 135
corruptions, including changed captures, initialization, argument order, and
reclamation counts.

The C harness uses a unary declaration, checks all three mathematical bodies,
and varies RSI on the guarded-stack bridge. It makes 1,494 native calls across
19 boundary and 64 deterministic random inputs per object, on ordinary and
guarded finite stacks. It checks saved registers, stack restoration, caller
frames, and reservation canaries.

See [the captured scalar contract](../../docs/source-native-captured-scalar.md)
for theorem premises, limits, negative cases, and reproduction commands.
