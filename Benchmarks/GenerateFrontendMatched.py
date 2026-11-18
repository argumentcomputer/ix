"""Generate literal benchmark data from GenerateFrontendMatched.lean exports.

Run both generators from the repository root. The prelude comes from an empty
module; expected user declarations are only consumed by the output comparator.
Keep output deterministic so regeneration can be checked byte for byte.
"""

import json
from pathlib import Path


def generate():
    directory = Path(".lake/frontend-benchmark")
    prelude = json.loads((directory / "matched-prelude.json").read_text())
    expected = json.loads((directory / "matched-expected.json").read_text())
    digest = json.loads((directory / "matched-digest.json").read_text())
    strings = {}

    def string(value):
        if value not in strings:
            strings[value] = len(strings)
        return f"w_string_{strings[value]}()"

    def cons(values):
        result = "store(ListNode.Nil)"
        for value in reversed(values):
            result = f"store(ListNode.Cons({value}, {result}))"
        return result

    def aiur(wire):
        if wire[0] == 0:
            return f"w_num({wire[1]})"
        if wire[0] == 1:
            return f"w_text({string(wire[1])})"
        return f"w_node({wire[1]}, {cons([aiur(child) for child in wire[2]])})"

    def lean(wire):
        if wire[0] == 0:
            return f"(.num {wire[1]})"
        if wire[0] == 1:
            return "(.text " + json.dumps(wire[1], ensure_ascii=False) + ")"
        return f"(.node {wire[1]} [" + ", ".join(map(lean, wire[2])) + "])"

    functions = []
    for i, wire in enumerate(prelude[2]):
        functions.append(f"  fn w_seed_{i}() -> W {{\n    {aiur(wire)}\n  }}")
    seeds = cons([f"w_seed_{i}()" for i in range(len(prelude[2]))])
    functions.append("  fn w_seed() -> List‹W› { " + seeds + " }")

    expected_entries = []
    for i, wire in enumerate(expected[2]):
        functions.append(f"  fn w_expected_{i}() -> W {{\n    {aiur(wire)}\n  }}")
        expected_entries.append(f"w_expected_{i}()")
    functions.append("  fn w_expected() -> W { w_node(0, " + cons(expected_entries) + ") }")

    for name, value in [
        ("ix", "ix"), ("contract", "contract"), ("kind", "kind"),
        ("code", "code"), ("u_motive", "u_motive"), ("rec", "rec"),
        ("recon", "recOn"), ("caseson", "casesOn"), ("nat", "Nat"),
        ("ctoridx", "_ctorIdx"), ("refl", "refl"),
    ]:
        functions.append(f"  fn w_word_{name}() -> ByteStream {{ {string(value)} }}")
    for value, i in strings.items():
        data = cons([f"{byte}u8" for byte in value.encode("utf-8")])
        functions.append(f"  fn w_string_{i}() -> ByteStream {{ {data} }}")
    for i in range(12):
        args = ", ".join(f"x{j}: W" for j in range(i))
        if args:
            args = ", " + args
        children = cons([f"x{j}" for j in range(i)])
        functions.append(f"  fn w{i}(tag: G{args}) -> W {{ w_node(tag, {children}) }}")

    text = """import Benchmarks.FrontendWire
import Ix.Aiur.Meta
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Generated immutable prelude and expected output data. Seed data comes from
elaborating the EMPTY module, never from the benchmark's user declarations.
Expected user declarations are used only by the output comparator.
Regenerate with Benchmarks/GenerateFrontendMatched.lean and the data generator.
-/
namespace FrontendMatchedData
open FrontendWire
"""
    # Split expected data by constant to avoid elaborating one enormous term.
    for i, wire in enumerate(expected[2]):
        text += f"private def expected_{i} : Wire := {lean(wire)}\n"
    text += "def sourceDigest : Address := ⟨⟨#[" + ", ".join(map(str, digest)) + "]⟩⟩\n"
    entries = ", ".join(f"expected_{i}" for i in range(len(expected[2])))
    text += "def expected : Wire := .node 0 [" + entries + "]\n"
    text += "def aiurData := ⟦\n" + "\n".join(functions) + "\n⟧\nend FrontendMatchedData\n"
    Path("Benchmarks/FrontendMatchedData.lean").write_text(text, encoding="utf-8")
    print(
        "Generated", len(prelude[2]), "prelude constants and", len(expected[2]),
        "expected constants;", len(text.encode("utf-8")), "bytes",
    )


if __name__ == "__main__":
    generate()
