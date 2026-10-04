# Canonical equality type beta controls

Thirteen independently selected theorem roots from `Source.lean`, exported
with frozen producer `cb68d94c`, Lean4.34.1, strict-anonymous IXON v4, baseline
`lean-core.profile`, and no generated equations. Each corresponding profile
is the original100k-step profile, address
`3a3b136bebf70228abeb5e8b6c40ce127d9f204807333b2eaaae5c4a4070497c`.
Both languages consume these exact bytes through their full combined gate.

Expected refusals are precise: `hiddenBad`, `proofLetBad`, `directProofBad`,
and `computationalBad` must report SharedToUnique; `changedInput` and
`changedResult` must report TypeMismatch. Budget or unrelated errors do not
satisfy these controls. The other seven roots must accept.

The `deadBad` positive is intentional: a computational value used only as a
discarded equality-type endpoint need not fulfill a runtime promise. A
Nonempty witness containing that same dishonest function remains forbidden.
Direct proof-returning and ordinary computational lambda applications do not
qualify for the equality-type beta rule. Dependent binders, aliases, and full
input/result contract matching are checked separately.

The old producer can emit the negative cases because these files test the
strengthened validator on committed inputs. Re-exporting negatives with the
current producer is expected to fail. Root selection is `BetaControls.NAME`;
the `.ixe` stem gives NAME. `sha256.txt` records exact bytes/source identity.
