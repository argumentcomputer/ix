# RC real-source regression input

The accepted H0 input used by the H1 certificate and H4 native gates.
Reverse.lean calls Lean's actual List.reverse; the independent expected
list/pair formulas remain in the tests. The three roots are
IxCCTests.Own.H0.{reverseList,reverseRepeated,sharedReverse}.

The input was refrozen on 2026-11-07, when the roots were renamed from the
project's former namespace, with the producer of the original H0 export
(ix `be45a159`, rebuilt) and the H0 commands that `provenance.json` records;
the rename changed only the names in the closure and sidecar. The producer
identity is baseline evidence, not a claim that G2 final producer
selection/refreeze has completed. A future intentional refreeze must update
this manifest after reviewing source/producer identities; test promotion does
not silently regenerate input.
