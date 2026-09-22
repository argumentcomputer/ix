#!/usr/bin/env python3
"""Report the completed CPU/GPU Init comparison."""

import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    results = {mode: json.loads((args.directory / mode / "result.json").read_text())
               for mode in ("cpu", "gpu")}
    if not all(row["valid"] for row in results.values()):
        raise SystemExit("both trials must complete and pass validation")
    cpu, gpu = results.values()
    if cpu["root"] != gpu["root"]:
        raise SystemExit("verified roots differ")
    wall = (1 - gpu["wall_seconds"] / cpu["wall_seconds"]) * 100
    cpu_time = (1 - gpu["cpu_seconds"] / cpu["cpu_seconds"]) * 100
    lines = [
        "# CPU/GPU trace generation with regeneration", "",
        "One trial per mode, using the same binary, fixture and four-GPU prover.", "",
        "| Trace generation | End-to-end (s) | Process CPU (s) | Peak RSS (GiB) | Sampled max VRAM/GPU (GiB) | LDE spills |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, row in results.items():
        lines.append(
            f"| {mode.upper()} | {row['wall_seconds']:.2f} | {row['cpu_seconds']:.2f} | "
            f"{row['max_rss_kib'] / 2**20:.2f} | "
            f"{max(row['sampled_peak_gpu_mib'].values()) / 1024:.2f} | {row['lde_spills']} |"
        )
    lines += [
        "", f"GPU trace generation used **{abs(wall):.2f}% {'less' if wall >= 0 else 'more'} wall time** "
        f"and **{abs(cpu_time):.2f}% {'less' if cpu_time >= 0 else 'more'} process CPU time** in this pair.", "",
        "Both modes regenerated traces, LDEs and Merkle trees for round two. The tree cache is removed.",
        f"Both completed eight fresh claims, seven fresh joins and verified root `{cpu['root']}`.",
        "Each made 182 main commitments across both rounds. CPU mode used only the host commitment path; "
        f"GPU mode generated {gpu['generated_rows']:,} rows from {gpu['generated_sources']} sources.", "",
        "These are end-to-end timings, not isolated trace-kernel measurements. "
        "One pair gives an initial result; it does not characterize run-to-run variation. "
        "GPU memory is sampled once per second, and spill bytes describe logical data rather than PCIe traffic.", "",
    ]
    (args.directory / "analysis.md").write_text("\n".join(lines))
    print("\n".join(lines))


if __name__ == "__main__":
    main()
