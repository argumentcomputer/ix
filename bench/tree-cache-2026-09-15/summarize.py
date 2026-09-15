#!/usr/bin/env python3
"""Summarize completed, verified Init trials without mixing in the pilot."""

import argparse
import json
from pathlib import Path
import statistics


CASES = ("old-regenerate", "fixed-regenerate", "fixed-trees")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--include", type=Path, action="append", default=[])
    parser.add_argument("--allow-incomplete", action="store_true",
                        help="exclude unfinished trials and list them in the report")
    args = parser.parse_args()
    results = []
    excluded = []
    reference = None
    for directory in [args.directory, *args.include]:
        metadata = json.loads((directory / "metadata.json").read_text())
        if metadata["diagnostic_pilot"]:
            raise SystemExit("the diagnostic pilot is excluded from comparisons")
        identity = (metadata["fixtures"], metadata["binaries"], metadata["environment"],
                    metadata["cpu_affinity"], metadata["gpus"])
        if reference is not None and identity != reference:
            raise SystemExit("fixture, binary, environment or hardware differs between runs")
        reference = identity
        expected = {(block, case) for block, order in enumerate(metadata["orders"], 1) for case in order}
        for block, case in sorted(expected):
            trial = directory / f"{block:02}-{case}"
            path = trial / "result.json"
            result = json.loads(path.read_text()) if path.exists() else None
            if result is None or not result["valid"]:
                if not args.allow_incomplete:
                    raise SystemExit(f"unfinished or invalid trial: {path}")
                excluded.append(str(trial))
                continue
            command = json.loads((trial / "command.json").read_text())
            budget = int(command["environment"]["AIUR_TREE_CACHE_BYTES"])
            result["tree_budget_bytes"] = budget
            result["group"] = f"{case}-{budget // 2**20}MiB" if case == "fixed-trees" else case
            result["run"] = str(directory)
            results.append(result)
    if not results:
        raise SystemExit("no completed trials")
    if len({r["root"] for r in results}) != 1:
        raise SystemExit("trials have different roots")
    if len({(r["generated_sources"], r["generated_rows"], r["seed_preparation_bytes"]) for r in results}) != 1:
        raise SystemExit("trials generated different workloads")
    summary = {}
    for case in dict.fromkeys(r["group"] for r in results):
        rows = [r for r in results if r["group"] == case]
        times = [r["wall_seconds"] for r in rows]
        summary[case] = {
            "trials": len(rows),
            "wall_seconds": times,
            "median_seconds": statistics.median(times),
            "range_seconds": [min(times), max(times)],
            "median_cpu_seconds": statistics.median(r["cpu_seconds"] for r in rows),
            "max_rss_gib": max(r["max_rss_kib"] for r in rows) / 2**20,
            "sampled_peak_gpu_gib": max(max(r["sampled_peak_gpu_mib"].values()) for r in rows) / 1024,
            "cache_outcomes": [r.get("cache") for r in rows],
            "tree_budget_bytes": rows[0]["tree_budget_bytes"],
        }
        metrics = {"Init-resident-four-gpu": {
            "status": "ok", "wall-seconds": summary[case]["median_seconds"],
            "cpu-seconds": summary[case]["median_cpu_seconds"],
            "peak-rss": summary[case]["max_rss_gib"] * 2**30,
        }}
        (args.directory / f"{case}.rows.json").write_text(json.dumps(metrics, indent=2) + "\n")
    paired = []
    for run, block in sorted({(r["run"], r["block"]) for r in results}):
        rows = {r["case"]: r for r in results if r["block"] == block and r["run"] == run}
        if any(case not in rows for case in CASES):
            continue
        a, b, c = (rows[case]["wall_seconds"] for case in CASES)
        paired.append({
            "block": block,
            "run": run,
            "fix_without_retention_seconds": b - a,
            "fix_without_retention_percent": (b / a - 1) * 100,
            "enable_retention_seconds": c - b,
            "enable_retention_percent": (c / b - 1) * 100,
        })
    report = {"cases": summary, "paired": paired, "root": results[0]["root"],
              "excluded_unfinished_trials": excluded, "trials": results}
    (args.directory / "analysis.json").write_text(json.dumps(report, indent=2) + "\n")
    lines = [
        "# Init performance results", "",
        "| Case | Trials (seconds) | Median | Range | Max RSS (GiB) | Sampled max VRAM/GPU (GiB) |",
        "| --- | --- | ---: | --- | ---: | ---: |",
    ]
    for case, row in summary.items():
        trials = ", ".join(f"{value:.2f}" for value in row["wall_seconds"])
        lo, hi = row["range_seconds"]
        lines.append(f"| {case} | {trials} | {row['median_seconds']:.2f} | {lo:.2f}–{hi:.2f} | {row['max_rss_gib']:.2f} | {row['sampled_peak_gpu_gib']:.2f} |")
    lines += [
        "", "| Case | Reused per trial | Budget refusals per trial | Workspace evictions per trial | LDE spills per trial |",
        "| --- | --- | --- | --- | --- |",
    ]
    for case, row in summary.items():
        outcomes = row["cache_outcomes"]
        cells = [", ".join(str(c[key]) if c is not None else "unavailable" for c in outcomes)
                 for key in ("reused", "rejected_budget", "evicted_workspace", "lde_spills")]
        lines.append(f"| {case} | " + " | ".join(cells) + " |")
    lines += [
        "", "Negative changes below mean less time; each comparison uses the same repetition block.", "",
        "| Block | Fixes without retention | Enable retention |",
        "| --- | ---: | ---: |",
    ]
    for row in paired:
        lines.append(f"| {row['block']} | {row['fix_without_retention_seconds']:+.2f} s ({row['fix_without_retention_percent']:+.2f}%) | {row['enable_retention_seconds']:+.2f} s ({row['enable_retention_percent']:+.2f}%) |")
    lines += ["", f"All completed trials verified root `{report['root']}`.",
              "One-off budget measurements are exploratory; small differences within the repeated-run range do not establish a speedup.", ""]
    if excluded:
        lines += ["Excluded unfinished trials:", "", *(f"- `{trial}`" for trial in excluded), ""]
    (args.directory / "analysis.md").write_text("\n".join(lines))
    print("\n".join(lines))


if __name__ == "__main__":
    main()
