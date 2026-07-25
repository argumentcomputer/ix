"""CSV loading for the benchmark datasets under `data/`."""
import csv
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "data")
FIGURES = os.path.join(ROOT, "figures")


def load(rel_path):
    """Load `data/<rel_path>` as a list of dict rows."""
    with open(os.path.join(DATA, rel_path)) as f:
        return list(csv.DictReader(f))


def numeric(rows, *names, require=True):
    """Return parallel float columns for `names`, dropping any row where a
    requested field is missing / non-numeric (e.g. DNF). Returns (cols..., kept_rows)."""
    cols = [[] for _ in names]
    kept = []
    for r in rows:
        vals = []
        ok = True
        for nm in names:
            v = r.get(nm, "")
            try:
                vals.append(float(v))
            except (TypeError, ValueError):
                ok = False
                break
        if ok:
            for i, v in enumerate(vals):
                cols[i].append(v)
            kept.append(r)
    return (*cols, kept)
