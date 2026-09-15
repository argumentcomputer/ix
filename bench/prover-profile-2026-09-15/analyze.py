"""Correlate span intervals with GPU activity without double-counting overlap."""

import argparse
from collections import defaultdict
import json
from pathlib import Path


def union(intervals):
    result = []
    for start, end in sorted(intervals):
        if end <= start:
            continue
        if result and start <= result[-1][1]:
            result[-1] = (result[-1][0], max(end, result[-1][1]))
        else:
            result.append((start, end))
    return result


def intersect(left, right):
    left, right = union(left), union(right)
    result = []
    i = j = 0
    while i < len(left) and j < len(right):
        lo, hi = max(left[i][0], right[j][0]), min(left[i][1], right[j][1])
        if hi > lo:
            result.append((lo, hi))
        if left[i][1] < right[j][1]:
            i += 1
        else:
            j += 1
    return result


def subtract(left, right):
    right = union(right)
    result = []
    for start, end in union(left):
        for lo, hi in right:
            if hi <= start:
                continue
            if lo >= end:
                break
            if start < lo:
                result.append((start, lo))
            start = max(start, hi)
            if start >= end:
                break
        if start < end:
            result.append((start, end))
    return result


def seconds(intervals):
    return sum(end - start for start, end in union(intervals)) / 1e9


def json_lines(path):
    with path.open() as stream:
        for line in stream:
            yield json.loads(line)


def read_spans(path):
    definitions, entered, spans = {}, defaultdict(list), []
    for event in json_lines(path):
        ident = event["id"]
        key = (ident, event["tid"])
        kind = event["event"]
        if kind == "new":
            definitions[ident] = event
        elif kind == "record":
            definitions[ident]["fields"].update(event["fields"])
        elif kind == "enter":
            entered[key].append(event["ts_ns"])
        elif kind == "exit":
            assert entered[key], f"Unmatched exit: {event}"
            start = entered[key].pop()
            assert event["ts_ns"] >= start, f"Clock moved backwards: {event}"
            spans.append(dict(definitions[ident], start=start, end=event["ts_ns"], tid=event["tid"]))
    assert not any(entered.values()), "Unclosed span entries"
    return spans


def memory_usage(activities):
    live, current, peak, unmatched = {}, 0, 0, 0
    series = []
    for record in sorted((a for a in activities if a["kind"] == "memory" and a["memory_kind"] == 3),
                         key=lambda a: a["timestamp"]):
        key = (record["device"], record["address"])
        if record["operation"] == 1:
            assert key not in live, f"Duplicate live device allocation: {record}"
            live[key] = record["bytes"]
            current += record["bytes"]
        elif record["operation"] == 2:
            size = live.pop(key, None)
            if size is None:
                unmatched += 1
            else:
                current -= size
        peak = max(peak, current)
        series.append((record["timestamp"], current))
    return {"peak_live_bytes": peak, "final_live_bytes": current, "unmatched_frees": unmatched}, series


def analyze(directory):
    spans = read_spans(directory / "spans.jsonl")
    activities = list(json_lines(directory / "cuda.jsonl"))
    summary = [a for a in activities if a["kind"] == "summary"]
    assert len(summary) == 1 and summary[0]["dropped"] == 0 and summary[0]["invalid"] == 0, summary
    gpu = [a for a in activities if a["kind"] in ("kernel", "memcpy", "memset")]
    kernels = union((a["start"], a["end"]) for a in gpu if a["kind"] == "kernel")
    transfers = union((a["start"], a["end"]) for a in gpu if a["kind"] == "memcpy")
    by_name = defaultdict(list)
    for span in spans:
        by_name[span["name"]].append((span["start"], span["end"]))
    windows = union(by_name["aiur/prove_planned"])
    assert windows, "No planned proof was captured"
    busy = intersect(kernels, windows)
    no_kernel = subtract(windows, kernels)
    report = {"proof_s": seconds(windows), "kernel_s": seconds(busy),
              "kernel_busy_fraction": seconds(busy) / seconds(windows),
              "transfer_only_s": seconds(intersect(no_kernel, transfers)), "phases": {},
              "activity_summary": summary[0]}
    memory, memory_series = memory_usage(activities)
    report["device_memory"] = memory if memory_series else None
    report["transfers"] = []
    for kind in [1, 2, 8]:
        records = [a for a in gpu if a["kind"] == "memcpy" and a["copy_kind"] == kind]
        report["transfers"].append({"copy_kind": kind, "bytes": sum(a["bytes"] for a in records),
            "count": len(records), "union_s": seconds((a["start"], a["end"]) for a in records)})
    for name, intervals in sorted(by_name.items()):
        clipped = intersect(intervals, windows)
        report["phases"][name] = {
            "count": len({s["id"] for s in spans if s["name"] == name}),
            "entries": len(intervals), "union_s": seconds(intervals),
            "inside_proof_s": seconds(clipped),
            "no_kernel_s": seconds(intersect(clipped, no_kernel)),
            "kernel_s": seconds(intersect(clipped, kernels)),
        }
    stages = ["stark/stage1_commit", "stark/lookup_construction", "stark/quotient", "stark/fri_open"]
    outside = subtract(windows, [interval for name in stages for interval in by_name[name]])
    report["outside_stages_s"] = seconds(outside)
    report["outside_stages_no_kernel_s"] = seconds(intersect(outside, no_kernel))
    report["outside_stages_witness_s"] = seconds(intersect(outside, by_name["aiur/witness"]))
    seed_intervals = by_name["aiur/blake3_device_rows"]
    seed_copies = [r for r in gpu if r["kind"] == "memcpy" and r["copy_kind"] == 1
                   and any(lo <= r["start"] < hi for lo, hi in seed_intervals)]
    report["blake3_seed_transfers"] = {"bytes": sum(r["bytes"] for r in seed_copies),
        "count": len(seed_copies), "union_s": seconds((r["start"], r["end"]) for r in seed_copies)}
    report["top_kernels"] = []
    names = defaultdict(list)
    for record in gpu:
        if record["kind"] == "kernel":
            names[record["name"]].append((record["start"], record["end"]))
    for name, intervals in sorted(names.items(), key=lambda pair: -seconds(intersect(pair[1], windows)))[:20]:
        report["top_kernels"].append({"name": name, "count": len(intervals),
                                     "union_s": seconds(intersect(intervals, windows))})
    report["top_apis"] = []
    names = defaultdict(list)
    for record in activities:
        if record["kind"] in ("driver", "runtime"):
            names[(record["kind"], record["name"])].append((record["start"], record["end"]))
    for (kind, name), intervals in sorted(names.items(), key=lambda pair: -seconds(intersect(pair[1], no_kernel)))[:20]:
        report["top_apis"].append({"kind": kind, "name": name, "count": len(intervals),
            "union_s": seconds(intersect(intervals, windows)),
            "no_kernel_s": seconds(intersect(intervals, no_kernel))})
    cpu = defaultdict(list)
    for span in spans:
        if span["name"] == "aiur/cpu_witness":
            cpu[span["fields"]["circuit"]].append((span["start"], span["end"]))
    report["cpu_circuits"] = [{"circuit": circuit, "count": len(intervals),
        "union_s": seconds(intervals), "no_kernel_s": seconds(intersect(intervals, no_kernel))}
        for circuit, intervals in sorted(cpu.items(), key=lambda pair: -seconds(pair[1]))[:20]]
    report["longest_gaps"] = []
    for start, end in sorted(no_kernel, key=lambda interval: interval[0] - interval[1])[:20]:
        active = {name: seconds(intersect(intervals, [(start, end)])) for name, intervals in by_name.items()}
        report["longest_gaps"].append({"start_s": (start - windows[0][0]) / 1e9,
            "duration_s": (end - start) / 1e9, "phases": {k: v for k, v in active.items() if v > .001}})
    (directory / "analysis.json").write_text(json.dumps(report, indent=2) + "\n")
    # Complete events keep the file readable by Chrome/Perfetto without assuming
    # stack discipline across the producer and consumer's shared parent spans.
    origin = min([s["start"] for s in spans] + [r["start"] for r in activities if "start" in r])
    trace = [{"ph": "M", "name": "process_name", "pid": 1, "args": {"name": "CPU"}},
             {"ph": "M", "name": "process_name", "pid": 2, "args": {"name": "CUDA GPU 0"}}]
    for record in spans:
        trace.append({"ph": "X", "cat": "span", "name": record["name"], "pid": 1,
            "tid": int(record["tid"]), "ts": (record["start"] - origin) / 1000,
            "dur": (record["end"] - record["start"]) / 1000, "args": record["fields"]})
    for record in gpu:
        trace.append({"ph": "X", "cat": record["kind"], "name": record["name"], "pid": 2 + record["device"],
            "tid": record["stream"], "ts": (record["start"] - origin) / 1000,
            "dur": (record["end"] - record["start"]) / 1000,
            "args": {k: record[k] for k in ("bytes", "copy_kind", "correlation")}})
    for record in activities:
        if record["kind"] in ("runtime", "driver"):
            trace.append({"ph": "X", "cat": record["kind"], "name": record["name"], "pid": 1,
                "tid": record["tid"], "ts": (record["start"] - origin) / 1000,
                "dur": (record["end"] - record["start"]) / 1000,
                "args": {"correlation": record["correlation"]}})
    for timestamp, live in memory_series:
        trace.append({"ph": "C", "name": "Live device allocations", "pid": 2, "tid": 0,
                      "ts": (timestamp - origin) / 1000, "args": {"GiB": live / 2**30}})
    (directory / "timeline.json").write_text(json.dumps({"traceEvents": trace}) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("top_kernels", "longest_gaps", "cpu_circuits")}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    analyze(parser.parse_args().directory)
