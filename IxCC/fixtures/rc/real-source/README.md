# RC real-source regression input

The accepted H0 input used by the H1 certificate and H4 native gates.
Reverse.lean calls Lean's actual List.reverse; the independent expected
list/pair formulas remain in the tests. The three roots are
IxCCTests.Own.H0.{reverseList,reverseRepeated,sharedReverse}.

The closure and sidecar are written by the ix of this repository (role-bound)
with the commands `provenance.json` records, by `lake exe refreeze-ixon
rc-real-source --ix IX --ix-path FAKE` ([`docs/corpus.md`](../../docs/corpus.md),
"Refreezing"), which also rewrites `manifest.sha256`. Test promotion does not
silently regenerate input.
