"""CLI: render the benchmark cost-model graphs.

    python -m benchstats all                  # every graph
    python -m benchstats aiur-predictor        # profiled features  -> FFT
    python -m benchstats aiur-runtime          # FFT -> exec/prove time, throughput, RAM
    python -m benchstats zisk-predictor        # profiled features  -> cycles (single + multi shard)
    python -m benchstats zisk-runtime          # cycles -> prove time/throughput/RAM (shard.rs model)
    python -m benchstats zisk-prove-validate   # shard.rs model vs real GPU proves (with R²)

Figures are written to `figures/` (gitignored — view with `kitten icat`).
"""
import argparse

from . import load, plot
from .plot import ENV_COLOR


def _project(rows, keep):
    """Keep only `keep` columns (drop incidental ones like shard/blocks)."""
    return [{k: r[k] for k in keep if k in r} for r in rows]


def aiur_predictor(a):
    rows = load.load("aiur/features.csv")
    pts = _project(rows, ["name", "env", "hb", "subst", "defeq", "bytes", "fft"])
    plot.feature_panels(pts, "fft", "Aiur FFT cost", "aiur_features_vs_fft.png",
                        "Aiur — profiled features vs FFT cost", a.svg)


def aiur_runtime(a):
    rows = load.load("aiur/cost.csv")
    fft, exec_us, prove_ms, rss_kb, kept = load.numeric(
        rows, "fft_cost", "exec_us", "prove_ms", "peak_rss_kb")
    colors = [ENV_COLOR.get(r.get("env", ""), "#1f77b4") for r in kept]
    exec_ms = [v / 1e3 for v in exec_us]
    exec_tput = [f / (e / 1e6) for f, e in zip(fft, exec_us)]   # FFT-units / s
    prove_tput = [f / (p / 1e3) for f, p in zip(fft, prove_ms)]  # FFT-units / s
    ram_gb = [v / 1024 / 1024 for v in rss_kb]
    plot.cost_vs_runtime(fft, "Aiur FFT cost", [
        dict(label="exec time", y=exec_ms, ylabel="exec time (ms)", yscale="log", fit="loglog"),
        dict(label="exec throughput", y=exec_tput, ylabel="exec throughput\n(FFT-units/s)", yscale="linear"),
        dict(label="peak RAM", y=ram_gb, ylabel="peak RAM (GB)", yscale="log", fit="loglog",
             note="process peak RSS (execute+prove; peak is in prove for completers)"),
    ], "aiur_exec_vs_fft.png", "Aiur — FFT cost vs execution", colors, a.svg)
    plot.cost_vs_runtime(fft, "Aiur FFT cost", [
        dict(label="prove time", y=prove_ms, ylabel="prove time (ms)", yscale="log", fit="loglog"),
        dict(label="prove throughput", y=prove_tput, ylabel="prove throughput\n(FFT-units/s)", yscale="linear"),
        dict(label="peak RAM", y=ram_gb, ylabel="peak RAM (GB)", yscale="log", fit="loglog"),
    ], "aiur_prove_vs_fft.png", "Aiur — FFT cost vs proving", colors, a.svg)


def zisk_predictor(a):
    single = _project(load.load("zisk/single_shard.csv"),
                      ["name", "hb", "bytes", "subst", "cycles"])
    plot.feature_panels(single, "cycles", "Zisk cycles (steps)",
                        "zisk_single_features_vs_cycles.png",
                        "Zisk single-shard (full-closure) — features vs cycles", a.svg)
    multi = _project(load.load("zisk/multi_shard.csv"),
                     ["shard", "hb", "bytes", "subst", "cycles"])
    plot.feature_panels(multi, "cycles", "Zisk cycles (steps)",
                        "zisk_multi_features_vs_cycles.png",
                        "Zisk multi-shard (per shard) — features vs cycles", a.svg)


def zisk_runtime(a):
    # Project the actual shard.rs prove model (constants read from the code) over
    # a cycle range. x = steps; B = steps in billions. See zisk-prove-validate for
    # the same model checked against real GPU proves.
    from . import shard_model
    k = shard_model.read_constants(a.shard_rs)
    B = lambda s: s / 1e9
    plot.model_lines((2.7e8, 5.0e9), [
        dict(label=f"{k['RAM_BASE_GIB']:.0f} + {k['RAM_GIB_PER_BCYCLE']:.0f}·B",
             fn=lambda s: k["RAM_BASE_GIB"] + k["RAM_GIB_PER_BCYCLE"] * B(s),
             ylabel="peak host RAM (GiB)", yscale="linear"),
        dict(label=f"{k['PROVE_SETUP_SECS']:.0f} + {k['PROVE_SECS_PER_BCYCLE']:.0f}·B",
             fn=lambda s: k["PROVE_SETUP_SECS"] + k["PROVE_SECS_PER_BCYCLE"] * B(s),
             ylabel="GPU prove time (s)", yscale="linear"),
        dict(label="steps/s",
             fn=lambda s: (s / 1e6) / (k["PROVE_SETUP_SECS"] + k["PROVE_SECS_PER_BCYCLE"] * B(s)),
             ylabel="prove throughput\n(M steps/s)", yscale="linear"),
    ], "zisk_prove_vs_cycles.png",
        "Zisk — cycles vs proving (shard.rs model projection)", a.svg)


def zisk_prove_validate(a):
    """Real GPU proves (zisk-host, RTX PRO 6000) vs the actual shard.rs model."""
    from . import shard_model
    k = shard_model.read_constants(a.shard_rs)
    steps, ram, leaf, wall, kept = load.numeric(
        load.load("zisk/prove_real.csv"), "steps", "peak_ram_gib", "leaf_secs", "wall_secs")
    kinds = [f"{r.get('kind','single')} w{r.get('witness','5')}" for r in kept]
    ram_model = lambda s: k["RAM_BASE_GIB"] + k["RAM_GIB_PER_BCYCLE"] * s / 1e9
    time_model = lambda s: k["PROVE_SETUP_SECS"] + k["PROVE_SECS_PER_BCYCLE"] * s / 1e9
    plot.model_vs_data([
        dict(x=steps, y=ram, model=ram_model, ylabel="peak host RAM (GiB)", groups=kinds,
             formula=f"{k['RAM_BASE_GIB']:.0f} + {k['RAM_GIB_PER_BCYCLE']:.0f}·Bsteps"),
        dict(x=steps, y=leaf, model=time_model, ylabel="prove time (s)", groups=kinds,
             y2=wall, y2label="measured (wall, incl. setup)",
             formula=f"{k['PROVE_SETUP_SECS']:.0f} + {k['PROVE_SECS_PER_BCYCLE']:.0f}·Bsteps"),
    ], "zisk_prove_validation.png",
        "Zisk shard.rs cost model vs real GPU proves (RTX PRO 6000 Blackwell)", a.svg)


CMDS = {"aiur-predictor": aiur_predictor, "aiur-runtime": aiur_runtime,
        "zisk-predictor": zisk_predictor, "zisk-runtime": zisk_runtime,
        "zisk-prove-validate": zisk_prove_validate}


def main():
    ap = argparse.ArgumentParser(prog="benchstats", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("graph", choices=["all"] + list(CMDS), help="which graph(s) to render")
    ap.add_argument("--svg", action="store_true", help="also write .svg")
    ap.add_argument("--shard-rs", default=None,
                    help="path to the ix repo's crates/kernel/src/shard.rs "
                         "(model constants source; default ~/ix/...)")
    a = ap.parse_args()
    todo = CMDS.values() if a.graph == "all" else [CMDS[a.graph]]
    for fn in todo:
        fn(a)


if __name__ == "__main__":
    main()
