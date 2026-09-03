"""Reusable matplotlib builders for the benchmark cost-model graphs."""
import math
import os

import matplotlib
matplotlib.use("Agg")  # headless: render to file
import matplotlib.pyplot as plt

from . import fit
from .load import FIGURES

# stable per-library colours (Aiur env column); falls back to grey
ENV_COLOR = {
    "Init": "#1f77b4", "Std": "#2ca02c", "Lean": "#9467bd",
    "Mathlib": "#d62728", "IxVM": "#7f7f7f",
}


def _save(figpath, svg):
    os.makedirs(FIGURES, exist_ok=True)
    out = os.path.join(FIGURES, figpath)
    plt.gcf().savefig(out, dpi=140, bbox_inches="tight")
    if svg:
        s = out.rsplit(".", 1)[0] + ".svg"
        plt.gcf().savefig(s)
    plt.close()
    print(f"wrote {out}")


def feature_panels(points, target_name, target_label, out, title, svg=False):
    """Small-multiples: one log-log panel per profiled feature vs the target cost,
    each with a power-law fit (y = a*x^b) overlaid. `points` is a list of dicts;
    feature columns are every key except name/env/the target."""
    feats = [k for k in points[0] if k not in ("name", "env", target_name)]
    ncol = 2
    nrow = (len(feats) + ncol - 1) // ncol
    fig, axes = plt.subplots(nrow, ncol, figsize=(11, 3.2 * nrow), squeeze=False)
    for idx, feat in enumerate(feats):
        ax = axes[idx // ncol][idx % ncol]
        xs, ys, cols = [], [], []
        for p in points:
            try:
                x = float(p[feat]); y = float(p[target_name])
            except (ValueError, KeyError):
                continue
            if x > 0 and y > 0:
                xs.append(x); ys.append(y); cols.append(ENV_COLOR.get(p.get("env", ""), "#1f77b4"))
        ax.scatter(xs, ys, s=14, c=cols, alpha=0.7, edgecolors="none")
        if len(xs) >= 3:
            a, b, r2 = fit.loglog(xs, ys)
            gx = [min(xs), max(xs)]
            ax.plot(gx, [a * v ** b for v in gx], "k-", lw=1)
            ax.set_title(f"{feat}:  y≈{a:.2g}·{feat}^{b:.2f}   R²(log)={r2:.3f}", fontsize=9)
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_xlabel(feat); ax.set_ylabel(target_label, fontsize=8)
        ax.grid(True, which="both", ls=":", lw=0.4, alpha=0.5)
    for j in range(len(feats), nrow * ncol):
        axes[j // ncol][j % ncol].axis("off")
    fig.suptitle(title, fontsize=12)
    fig.tight_layout(rect=[0, 0, 1, 0.97])
    _save(out, svg)


def cost_vs_runtime(x, xlabel, panels, out, title, colors=None, svg=False):
    """Stacked shared-x panels (one figure = "one graph"): cost on x, each panel a
    runtime measure (time / throughput / RAM). `panels` = list of
    dict(label, y, ylabel, yscale, fit). `fit` in {None,'loglog','affine'}."""
    fig, axes = plt.subplots(len(panels), 1, figsize=(9, 2.6 * len(panels)),
                             sharex=True, squeeze=False)
    for i, pan in enumerate(panels):
        ax = axes[i][0]
        xs = [x[k] for k in range(len(x)) if x[k] is not None and pan["y"][k] is not None and pan["y"][k] > 0]
        ys = [pan["y"][k] for k in range(len(x)) if x[k] is not None and pan["y"][k] is not None and pan["y"][k] > 0]
        cs = ([colors[k] for k in range(len(x)) if x[k] is not None and pan["y"][k] is not None and pan["y"][k] > 0]
              if colors else "#1f77b4")
        ax.scatter(xs, ys, s=16, c=cs, alpha=0.75, edgecolors="none")
        if pan.get("fit") == "loglog" and len(xs) >= 3:
            a, b, r2 = fit.loglog(xs, ys)
            gx = sorted(xs)
            ax.plot(gx, [a * v ** b for v in gx], "k-", lw=1,
                    label=f"y≈{a:.2g}·x^{b:.2f} (R²log {r2:.3f})")
            ax.legend(fontsize=7, loc="upper left")
        elif pan.get("fit") == "affine" and len(xs) >= 3:
            r = fit.wls([xs], ys, relative=False)
            b, a = r["coef"]
            gx = sorted(xs)
            ax.plot(gx, [a + b * v for v in gx], "k-", lw=1,
                    label=f"y≈{a:.3g}+{b:.3g}·x (R² {r['r2']:.3f})")
            ax.legend(fontsize=7, loc="upper left")
        ax.set_xscale("log")
        ax.set_yscale(pan.get("yscale", "log"))
        ax.set_ylabel(pan["ylabel"], fontsize=9)
        ax.grid(True, which="both", ls=":", lw=0.4, alpha=0.5)
        if pan.get("note"):
            ax.text(0.99, 0.05, pan["note"], transform=ax.transAxes, fontsize=7,
                    ha="right", va="bottom", color="#888")
    axes[-1][0].set_xlabel(xlabel)
    fig.suptitle(title, fontsize=12)
    fig.tight_layout(rect=[0, 0, 1, 0.97])
    _save(out, svg)


def model_vs_data(panels, out, title, svg=False):
    """Overlay a *fixed* model line (no fitted params) on measured points and
    annotate the model's R² and MAPE against the data. `panels` = list of
    dict(x, y, model, ylabel, formula[, y2, y2label]). `model` is a callable
    x->ŷ (e.g. read from shard.rs); R² = 1 − Σ(y−ŷ)²/Σ(y−ȳ)²."""
    fig, axes = plt.subplots(len(panels), 1, figsize=(8.5, 4.0 * len(panels)),
                             squeeze=False)
    for i, pan in enumerate(panels):
        ax = axes[i][0]
        x, y, model = pan["x"], pan["y"], pan["model"]
        groups = pan.get("groups")
        if groups:
            styles = {"single w5": ("o", "#1f77b4"), "sharded w5": ("^", "#2ca02c"),
                      "sharded w10": ("s", "#ff7f0e"), "single w10": ("D", "#9467bd")}
            for g in dict.fromkeys(groups):
                xs_g = [x[i] for i in range(len(x)) if groups[i] == g]
                ys_g = [y[i] for i in range(len(x)) if groups[i] == g]
                mk, col = styles.get(g, ("o", "#1f77b4"))
                ax.scatter(xs_g, ys_g, s=38, c=col, marker=mk, zorder=3,
                           label=f"measured ({g} leaf)")
        else:
            ax.scatter(x, y, s=34, c="#1f77b4", zorder=3, label="measured (leaf)")
        if pan.get("y2") is not None:
            ax.scatter(x, pan["y2"], s=20, c="#7f7f7f", marker="x", zorder=3,
                       label=pan.get("y2label", "measured (2)"))
        gx = [min(x) * (max(x) / min(x)) ** (k / 100) for k in range(101)]
        ax.plot(gx, [model(v) for v in gx], "-", lw=1.8, color="#d62728", zorder=2,
                label=f"shard.rs model: {pan['formula']}")
        yhat = [model(v) for v in x]
        ybar = sum(y) / len(y)
        ss_res = sum((a - b) ** 2 for a, b in zip(y, yhat))
        ss_tot = sum((a - ybar) ** 2 for a in y)
        r2 = 1 - ss_res / ss_tot if ss_tot else float("nan")
        mape = sum(abs(a - b) / a for a, b in zip(y, yhat)) / len(y) * 100
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_xlabel("guest STEPS (cycles)"); ax.set_ylabel(pan["ylabel"])
        ax.set_title(f"{pan['ylabel']}   —   model R²={r2:.3f}, MAPE={mape:.0f}%", fontsize=10)
        ax.grid(True, which="both", ls=":", lw=0.4, alpha=0.5)
        ax.legend(fontsize=8, loc="upper left")
    fig.suptitle(title, fontsize=12)
    fig.tight_layout(rect=[0, 0, 1, 0.97])
    _save(out, svg)


def model_lines(xrange, panels, out, title, svg=False):
    """Draw documented model lines over a cost range when no raw points exist
    (Zisk prove model). `panels` = list of dict(label, fn, ylabel, yscale)."""
    xs = [xrange[0] * (xrange[1] / xrange[0]) ** (k / 60) for k in range(61)]
    fig, axes = plt.subplots(len(panels), 1, figsize=(9, 2.6 * len(panels)),
                             sharex=True, squeeze=False)
    for i, pan in enumerate(panels):
        ax = axes[i][0]
        ax.plot(xs, [pan["fn"](v) for v in xs], "-", lw=1.6, color="#d62728",
                label=pan.get("label", ""))
        ax.set_xscale("log"); ax.set_yscale(pan.get("yscale", "linear"))
        ax.set_ylabel(pan["ylabel"], fontsize=9)
        ax.grid(True, which="both", ls=":", lw=0.4, alpha=0.5)
        if pan.get("label"):
            ax.legend(fontsize=7, loc="upper left")
    axes[-1][0].set_xlabel("cycles (steps)")
    fig.suptitle(title, fontsize=12)
    fig.tight_layout(rect=[0, 0, 1, 0.97])
    _save(out, svg)
