#!/usr/bin/env python3
"""gen_deployed.py CERTIFIED.lean OUT.lean

Writes the module `IxAICombined.Deployed`: the trained model, its card and its gate decisions,
taken from a certified bundle file (`ix/bundle/Certified_<config>.lean`), in the combined
certificate's environment. The kernel-route training chain of the bundle file is left out: in the
combined certificate the model's provenance is the Aiur run, not `trainingCertified`.

Copied as they stand: `config`, the final model (`w<N>`, renamed `trainedOutput`), `cardOutput`,
and every theorem after `cardOutput`.
"""
import re
import sys

source, out = sys.argv[1], sys.argv[2]
lines = open(source).read().split("\n")


def definition(name):
    """The lines of `def name ...`, up to the next blank line."""
    start = next(i for i, line in enumerate(lines) if line.startswith(f"def {name} "))
    end = next(i for i in range(start, len(lines)) if lines[i] == "")
    return lines[start:end]


trained = next(line for line in lines if line.startswith("def trainedOutput "))
final = re.fullmatch(r"def trainedOutput : Model := (w\d+)", trained).group(1)
model = definition(final)
model[0] = model[0].replace(f"def {final} ", "def trainedOutput ", 1)
card_at = next(i for i, line in enumerate(lines) if line.startswith("def cardOutput "))
end_at = next(i for i, line in enumerate(lines) if line.startswith("end IxAICertified."))
tail = lines[card_at:end_at]

text = "\n".join([
    "import IxAICombined",
    "open IxAICore Triage",
    "",
    "/-! # The deployed model in the combined certificate's environment",
    "",
    "The trained model as a literal, its card and its gate decisions. A combined certificate over",
    "this environment covers them together with the binding of the Aiur run that produced the",
    "model, so one claim ties the run, the card and the decisions to the same constant. -/",
    "",
    "set_option maxRecDepth 1000000",
    "set_option maxHeartbeats 0",
    "",
    "namespace IxAICombined.Deployed",
    "",
    *definition("config"),
    "",
    *model,
    "",
    "/-- The configuration the card is computed under is the one the training run certifies. -/",
    "theorem config_eq : config = IxAIAiur.fullConfig := rfl",
    "",
    "/-- The deployed model is in the range in which a model is determined by its field encoding",
    "(`IxAICombined.eq_of_encModel_eq`), so a run that ends at this model's encoding ends at this",
    "model. -/",
    "theorem trainedOutput_ok : IxAIStep.Fixed.TrainSpec.modelOkB trainedOutput = true := by",
    "  decide +kernel",
    "",
    *tail,
    "end IxAICombined.Deployed",
    "",
])
open(out, "w").write(text)
print(f"{out}: model {final}, {sum(1 for line in tail if line.startswith('theorem '))} theorems")
