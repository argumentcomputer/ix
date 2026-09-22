"""Check replay equivalence and summarize the seed transport measurements."""

import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("analyze", HERE.parent / "prover-profile-2026-09-15/analyze.py")
analyze = importlib.util.module_from_spec(spec)
spec.loader.exec_module(analyze)


def main():
    labels = ["baseline-profile", "packed-profile", "packed-pageable-profile",
              "baseline-control", "packed-control", "packed-pageable-control"]
    rows = {}
    reference_plan = None
    reference_settings = None
    reference_shapes = None
    proof = "12beead9b79adc380e89315c871294470a76d7e9d574cce5e76b791e887697e2"
    for label in labels:
        directory = HERE / label
        metadata = json.loads((directory / "meta.json").read_text())
        assert metadata["exit_code"] == 0
        assert "aborted_for_contention" not in metadata and "watcher_error" not in metadata
        stderr = (directory / "stderr").read_text()
        assert f"proof {proof} (not persisted)" in stderr
        assert "record 14003112192 B" in stderr
        plan = [line for line in stderr.splitlines() if line.startswith("[trace-shards] shard ")]
        assert len(plan) == 7
        settings = {key: value for key, value in metadata["environment"].items()
                    if key not in ("AIUR_PROFILE", "AIUR_CUDA_PROFILE", "CUDA_INJECTION64_PATH")}
        settings["cpu_affinity"] = metadata["cpu_affinity"]
        spans = analyze.read_spans(directory / "spans.jsonl")
        shapes = sorted([span["fields"] for span in spans if span["name"] == "aiur/blake3_seeds"],
                        key=lambda value: json.dumps(value, sort_keys=True))
        if reference_plan is None:
            reference_plan, reference_settings, reference_shapes = plan, settings, shapes
        assert plan == reference_plan and settings == reference_settings and shapes == reference_shapes, label
        phases = {name: analyze.seconds((s["start"], s["end"]) for s in spans if s["name"] == name)
                  for name in ("aiur/prove_planned", "aiur/replay", "aiur/prepare_slot",
                               "aiur/blake3_seeds", "aiur/blake3_device_rows")}
        rss = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", stderr)[1]) / 2**20
        with (directory / "gpu.csv").open() as stream:
            gpu_peak = max(float(row[2]) for row in csv.reader(stream)) / 1024
        row = {"phases_s": phases, "peak_rss_gib": rss, "sampled_gpu_peak_gib": gpu_peak}
        if (directory / "analysis.json").exists():
            data = json.loads((directory / "analysis.json").read_text())
            assert data["activity_summary"]["dropped"] == data["activity_summary"]["invalid"] == 0
            row.update(seed_transfers=data["blake3_seed_transfers"],
                       transfers=data["transfers"], device_memory=data["device_memory"],
                       kernel_s=data["kernel_s"],
                       stage1_s=data["phases"]["stark/stage1_commit"]["union_s"],
                       lookup_s=data["phases"]["stark/lookup_construction"]["union_s"])
        rows[label] = row
    baseline_bytes = rows["baseline-profile"]["seed_transfers"]["bytes"]
    for label in ["packed-profile", "packed-pageable-profile"]:
        assert rows[label]["seed_transfers"]["bytes"] * 1296 == baseline_bytes * 176
        assert rows[label]["seed_transfers"]["count"] == 334
    output = {"proof": proof, "trace_plan_sha256": hashlib.sha256("\n".join(reference_plan).encode()).hexdigest(),
              "pieces": 7, "record_bytes": 14003112192, "runs": rows}
    (HERE / "comparison.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
