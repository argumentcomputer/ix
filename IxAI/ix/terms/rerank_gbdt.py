"""Gradient-boosted ranking over the candidate pools of `rerank_feats.py`, as
an upper bound for what the pooled features support.

    rerank_gbdt.py FEATS_DIR [--fit val|dom] [--test]

The pool (without gold that was added only for being gold) serves as the
candidate set; a candidate outside it is ranked last. Validation numbers are
5-fold cross-validated by module. `--fit dom` adds the training sample with
a training-query indicator feature, set to 0 when scoring held-out queries.
"""
import argparse
import numpy as np, lightgbm as lgb
from encoder_gpu import load_meta
from rerank_feats import NAMES

def load(d, split):
    p = lambda k: np.load('%s/%s_pool_%s.npy' % (d, split, k))
    return dict(ptr=p('ptr'), row=p('row'), gold=p('gold'), forced=p('forced'), X=p('X').astype(np.float32),
                items=np.load('%s/%s_items.npy' % (d, split)))

def pool_eval(P, scores, qs, M, use, first):
    lib_cid, lib_mod, item_row, gptr, gold = M['lib_cid'], M['lib_mod'], M['item_row'], M['gold_ptr'], M['gold']
    h = np.zeros(3); n = 0; rr = 0.0; sl = np.zeros(3); st = np.zeros(3)
    for q in qs:
        a, b = P['ptr'][q], P['ptr'][q + 1]; ok = ~P['forced'][a:b]; s = scores[a:b][ok]; rows = P['row'][a:b][ok]; g = P['gold'][a:b][ok]
        order = np.argsort(-s, kind='stable'); topc = [int(lib_cid[x]) for x in rows[order[:10]]]
        i = P['items'][q]; gs = gold[gptr[i]:gptr[i + 1]]; gset = set(int(c) for c in gs); n += len(gs)
        for x, k in enumerate((1, 5, 10)): h[x] += len(gset & set(topc[:k]))
        for c in gs:
            gr = first[int(c)]; cl = 0 if lib_mod[gr] == lib_mod[item_row[i]] else (1 if use[gr] > 0 else 2)
            st[cl] += 1; sl[cl] += int(c) in set(topc)
        if g.any(): rr += 1.0 / (int((s > s[g].max()).sum()) + 1)
    return '%5.1f %5.1f %5.1f %6.3f | %5.1f %5.1f %5.1f' % (*(100 * h / n), rr / len(qs), *(100 * sl / np.maximum(st, 1)))

def matrix(P, qs, dom, max_neg=None, seed=0):
    rng = np.random.default_rng(seed); X = []; y = []; grp = []
    for q in qs:
        a, b = P['ptr'][q], P['ptr'][q + 1]; g = P['gold'][a:b]
        if not g.any(): continue
        idx = np.arange(b - a)
        if max_neg and (~g).sum() > max_neg:
            idx = np.concatenate([np.nonzero(g)[0], rng.choice(np.nonzero(~g)[0], max_neg, replace=False)])
        x = P['X'][a:b][idx]
        X.append(np.concatenate([x, np.full((len(idx), 1), dom, np.float32)], 1)); y.append(g[idx].astype(int)); grp.append(len(idx))
    return np.concatenate(X), np.concatenate(y), grp

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('feats'); ap.add_argument('--fit', default='val'); ap.add_argument('--test', action='store_true')
    ap.add_argument('--rounds', type=int, default=400)
    args = ap.parse_args()
    M = load_meta(); lib_cid, lib_mod = M['lib_cid'], M['lib_mod']
    first = {}
    for r, c in enumerate(lib_cid): first.setdefault(int(c), r)
    gptr, gold = M['gold_ptr'], M['gold']
    use = np.zeros(len(lib_cid))
    for i in np.nonzero((M['item_split'] == 0) & ~(lib_mod[M['item_row']] % 50 == 7))[0]:
        for c in gold[gptr[i]:gptr[i + 1]]: use[first[int(c)]] += 1
    V = load(args.feats, 'val'); T = load(args.feats, 'train') if args.fit == 'dom' else None
    params = dict(objective='lambdarank', learning_rate=0.05, num_leaves=31, min_data_in_leaf=50, feature_fraction=0.8,
                  lambdarank_truncation_level=30, eval_at=[10], verbose=-1, num_threads=0)
    def train(qs):
        X, y, g = matrix(V, qs, 0.0)
        if T is not None:
            Xt, yt, gt = matrix(T, range(len(T['items'])), 1.0, max_neg=600); X = np.concatenate([X, Xt]); y = np.concatenate([y, yt]); g = g + gt
        return lgb.train(params, lgb.Dataset(X, y, group=g), num_boost_round=args.rounds)
    def score(P, bst):
        return bst.predict(np.concatenate([P['X'], np.zeros((len(P['X']), 1), np.float32)], 1))
    vmod = lib_mod[M['item_row'][V['items']]]; fold_of = {m: k % 5 for k, m in enumerate(np.unique(vmod))}
    folds = np.array([fold_of[m] for m in vmod]); sc = np.zeros(len(V['X']))
    for f in range(5):
        bst = train(np.nonzero(folds != f)[0]); s = score(V, bst)
        for q in np.nonzero(folds == f)[0]: sc[V['ptr'][q]:V['ptr'][q + 1]] = s[V['ptr'][q]:V['ptr'][q + 1]]
    print('gbdt fit %s  val  %s' % (args.fit, pool_eval(V, sc, range(len(V['items'])), M, use, first)), flush=True)
    zi = NAMES.index('z_dense')
    print('dense on pool   val  %s' % pool_eval(V, V['X'][:, zi], range(len(V['items'])), M, use, first), flush=True)
    if args.test:
        bst = train(np.arange(len(V['items']))); Te = load(args.feats, 'test')
        print('gbdt fit %s  test %s' % (args.fit, pool_eval(Te, score(Te, bst), range(len(Te['items'])), M, use, first)), flush=True)

if __name__ == '__main__':
    main()
