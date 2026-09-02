The reviewed `expected.json` matrix records 11 synthetic Ixon cases and two
production Ixon rejection cases. Its roots, HPT identities, stage boundaries,
semantic observations, and memory counters are frozen expectations.

Generate complete snapshots with `lake exe source-coverage /tmp/new-coverage`.
Run `lake exe check-source-coverage --fixture .lake/build/bin/source-coverage`
to compare two fresh compiler processes against this matrix and each other.
Add `--cc cc --harness fixtures/x86/native_harness.c` on x86-64 Linux to link
and run the three source-driven objects.

The full snapshots compare original Ixon bytes, raw and addressed IxIR0/IxIR1
graphs and maps, canonical HPT certificate/cache records, and structural IxIR2
diagnostics. They are temporary check outputs. IxIR2 diagnostics are not a
codec or a persistent content-address format.

Refresh this matrix only after reviewing the compiler policy or fixture
change that explains the drift. The checker never updates expectations.
