# Scalar native regression fixtures

`expected.json` pins the five synthetic functions, source and IxIR₁ roots,
complete native text digests, code sizes, and sufficient stack bounds.
The producer compiles each function once and supplies inputs later. The C
harness independently computes expected results with 128-bit arithmetic and
exercises ordinary and guarded stacks.

See [the fragment, ABI, proofs, and gate](../../docs/source-native-scalar.md).
Refresh the reviewed report only after inspecting identities, complete text,
arithmetic/fallback observations, and stack changes. The independent checker
never refreshes it automatically.
