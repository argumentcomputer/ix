#!/usr/bin/env python3
"""Static seed-size inventory under the typed schema.

Reads one `ix codegen --trace-report` document and prints, per program, how
the typed seed compares with the canonical seed and with the main row, plus
the functions with the largest static byte savings. Static sites only: row
weights are not in the report, so nothing here is weighted by real rows.
"""
import json
import sys
from collections import Counter


def ratio(a, b):
    return a / b if b else float("inf")


def summarize(program):
    functions = program["functions"]
    rows = []
    for f in functions:
        canonical = f["canonical_seed_bytes"]
        typed = f["typed_seed_bytes"]
        row_bytes = f["singleton_main_bytes_per_real_row"]
        bits = Counter(f["typed_seed_word_bits"])
        rows.append({
            "index": f["index"],
            "name": (f["names"] or [f"function_{f['index']}"])[0],
            "words": f["canonical_seed_words"],
            "canonical": canonical,
            "typed": typed,
            "row": row_bytes,
            "u8": bits.get(8, 0), "u16": bits.get(16, 0),
            "u32": bits.get(32, 0), "full": bits.get(64, 0),
        })
    n = len(rows)
    total_canonical = sum(r["canonical"] for r in rows)
    total_typed = sum(r["typed"] for r in rows)
    total_row = sum(r["row"] for r in rows)
    print(f"## {program['program']}: {n} constrained functions")
    print()
    print("| Measure | Value |")
    print("| --- | ---: |")
    print(f"| Canonical seed bytes, summed over static functions | {total_canonical:,} |")
    print(f"| Typed seed bytes, summed | {total_typed:,} |")
    print(f"| Typed / canonical, summed | {ratio(total_typed, total_canonical):.3f} |")
    print(f"| Main row bytes, summed | {total_row:,} |")
    print(f"| Typed seed / main row, summed | {ratio(total_typed, total_row):.3f} |")
    for bound in (0.5, 0.25, 0.125):
        count = sum(1 for r in rows if r["typed"] <= bound * r["canonical"])
        print(f"| Functions with typed <= {bound:g} x canonical | {count} |")
    unchanged = sum(1 for r in rows if r["typed"] == r["canonical"])
    print(f"| Functions with no narrowing at all | {unchanged} |")
    within = sum(1 for r in rows if r["typed"] * 2 > r["row"])
    print(f"| Functions whose typed seed still exceeds half the row | {within} |")
    words = Counter()
    for r in rows:
        for k in ("u8", "u16", "u32", "full"):
            words[k] += r[k]
    total_words = sum(words.values())
    print(f"| Seed words: u8 / u16 / u32 / full | "
          f"{words['u8']:,} / {words['u16']:,} / {words['u32']:,} / {words['full']:,} "
          f"of {total_words:,} |")
    print()
    print("Largest static savings, canonical minus typed bytes per row:")
    print()
    print("| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |")
    print("| --- | ---: | ---: | ---: | ---: | --- |")
    for r in sorted(rows, key=lambda r: r["typed"] - r["canonical"])[:15]:
        print(f"| {r['index']} `{r['name']}` | {r['words']} | {r['canonical']} | {r['typed']} | "
              f"{r['row']} | {r['u8']}/{r['u16']}/{r['u32']}/{r['full']} |")
    print()
    print("Widest typed seeds relative to the row (least to gain from generation):")
    print()
    print("| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |")
    print("| --- | ---: | ---: | ---: | ---: | --- |")
    for r in sorted(rows, key=lambda r: -ratio(r["typed"], r["row"]))[:10]:
        print(f"| {r['index']} `{r['name']}` | {r['words']} | {r['canonical']} | {r['typed']} | "
              f"{r['row']} | {r['u8']}/{r['u16']}/{r['u32']}/{r['full']} |")
    print()
    return rows


def main():
    document = json.load(open(sys.argv[1]))
    assert document["compact_encoding"] == "typed_schema_guarded", document["compact_encoding"]
    all_rows = []
    for program in document["programs"]:
        all_rows.extend(summarize(program))
    if len(sys.argv) > 2:
        with open(sys.argv[2], "w") as out:
            json.dump(all_rows, out, indent=1)


if __name__ == "__main__":
    main()
