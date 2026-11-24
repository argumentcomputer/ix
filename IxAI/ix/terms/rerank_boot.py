"""Bootstrap confidence intervals for the difference of two rankers on the same theorems.

    rerank_boot.py BASE.npz NEW.npz [NEW2.npz ...] [--feats DIR --split test]

Each npz holds the per-theorem arrays `rerank_gpu.evaluate` returns. Theorems
are resampled with replacement (10000 draws); with `--feats`, whole modules
are resampled as well. Reports the gain in R@10, MRR and rare-premise R@10
with 95% percentile intervals.
"""
import argparse
import numpy as np

def stats(o, idx):
    return np.array([100 * o['h10'][idx].sum() / o['n'][idx].sum(), o['rr'][idx].mean(),
                     100 * o['rare_h'][idx].sum() / max(o['rare_n'][idx].sum(), 1),
                     100 * o['own_h'][idx].sum() / max(o['own_n'][idx].sum(), 1)])

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('base'); ap.add_argument('new', nargs='+')
    ap.add_argument('--feats', default=''); ap.add_argument('--split', default='test'); ap.add_argument('--draws', type=int, default=10000)
    args = ap.parse_args()
    B = dict(np.load(args.base)); n = len(B['n']); rng = np.random.default_rng(0)
    groups = None
    if args.feats:
        from encoder_gpu import load_meta
        M = load_meta(); items = np.load('%s/%s_items.npy' % (args.feats, args.split))
        mods = M['lib_mod'][M['item_row'][items]]; groups = [np.nonzero(mods == m)[0] for m in np.unique(mods)]
    for path in args.new:
        N = dict(np.load(path)); d0 = stats(N, np.arange(n)) - stats(B, np.arange(n))
        for label in (['theorems'] + (['modules'] if groups else [])):
            ds = []
            for _ in range(args.draws):
                if label == 'theorems': idx = rng.integers(0, n, n)
                else: idx = np.concatenate([groups[j] for j in rng.integers(0, len(groups), len(groups))])
                ds.append(stats(N, idx) - stats(B, idx))
            lo, hi = np.percentile(np.array(ds), [2.5, 97.5], axis=0)
            print('%-60s %-8s dR@10 %+.2f [%+.2f, %+.2f]  dMRR %+.4f [%+.4f, %+.4f]  dRare %+.2f [%+.2f, %+.2f]  dOwn %+.2f [%+.2f, %+.2f]' % (
                path.split('/')[-1], label, d0[0], lo[0], hi[0], d0[1], lo[1], hi[1], d0[2], lo[2], hi[2], d0[3], lo[3], hi[3]))

if __name__ == '__main__':
    main()
