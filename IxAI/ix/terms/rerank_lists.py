"""Write top-ten premise lists of fitted scorers by name.

    rerank_lists.py FEATS_DIR SPLIT OUT.tsv [--sample N] NAME=MODEL.json ...

Lines are `THEOREM<TAB>MODULE<TAB>RANKER<TAB>p1,...,p10`, with a `gold` line
per theorem holding its gold premises. `SPLIT` is val or test; `--sample N`
keeps the N theorems `np.random.default_rng(0).permutation` puts first, in
dataset order. `head6=` with no file is the six-weight head of
`fusion_gpu.py` at its printed weights.
"""
import argparse, json
import numpy as np, torch
from encoder_gpu import DATA, DEV, log
from rerank_gpu import Data, Scorer, BASE6, HEAD6, evaluate

def load_model(path):
    if not path:
        m = Scorer(BASE6, 'linear'); m.w.data = torch.tensor(HEAD6, device=DEV); return m
    j = json.load(open(path)); m = Scorer(j['cols'], j['kind'], hidden=len(j['state'].get('l1.bias', [0] * 32)))
    m.load_state_dict({k: torch.tensor(v, device=DEV) for k, v in j['state'].items()}); return m

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('feats'); ap.add_argument('split'); ap.add_argument('out')
    ap.add_argument('--sample', type=int, default=0); ap.add_argument('models', nargs='+')
    args = ap.parse_args()
    D = Data(args.feats); F = D.full(args.split); M = D.M
    qs = np.arange(len(F['items']))
    if args.sample: qs = np.sort(np.random.default_rng(0).permutation(len(qs))[:args.sample])
    mod_name = []; row_name = []
    for line in open(DATA + '/mathlib-full/decls.tsv'):
        f = line.rstrip('\n').split('\t')
        if f[0] == 'mod': mod_name.append(f[2])
        elif f[0] == 'lib': row_name.append(f[1])
    tops = {}
    for spec in args.models:
        name, path = spec.split('=', 1); t = []
        evaluate(D, F, load_model(path), qs, tops=t); tops[name] = t; log('ranked', name)
    item_row, lib_mod, gptr, gold = M['item_row'], M['lib_mod'], M['gold_ptr'], M['gold']
    with open(args.out, 'w') as out:
        for k, q in enumerate(qs):
            i = F['items'][q]; thm = row_name[item_row[i]]; mod = mod_name[lib_mod[item_row[i]]]
            out.write('%s\t%s\tgold\t%s\n' % (thm, mod, ','.join(row_name[D.first[int(c)]] for c in gold[gptr[i]:gptr[i + 1]])))
            for name, t in tops.items():
                out.write('%s\t%s\t%s\t%s\n' % (thm, mod, name, ','.join(row_name[int(j)] for j in t[k])))
    log('wrote', args.out, len(qs), 'theorems')

if __name__ == '__main__':
    main()
