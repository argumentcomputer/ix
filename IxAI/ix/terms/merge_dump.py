"""Pool a library's term dump with the Mathlib dump into one dump with one
constant id space, so `graph_export` can build a single graph over both.

    merge_dump.py MATHLIB-DUMP LIBRARY-DUMP OUT-DIR

The ids are those of `cross.py`: every Mathlib constant keeps its id, and a
library constant whose address is not in Mathlib gets the next free id, in
the library's order. Library constants that Mathlib also has are dropped (the
same address is the same declaration). The library's nodes are copied with
every constant reference (tags 2, 3 and 4, field `a`) renumbered; in
`consts.tsv` only `id` and `node_start` are rewritten, so `owner`, `member`
and `ctor` of a library row still hold library ids. Only
`consts.tsv` and `nodes.bin` are written; `pids.npy` maps each library id to
its pooled id.
"""
import sys, os, shutil
import numpy as np

def main():
    mdir, ldir, out = sys.argv[1:4]
    os.makedirs(out, exist_ok=True)
    maddr = {}; nm = 0; mnodes = 0
    for line in open(mdir + '/consts.tsv'):
        f = line.split('\t', 2); maddr[f[1]] = int(f[0]); nm += 1
    mnodes = os.path.getsize(mdir + '/nodes.bin') // 16
    lrows = [line.rstrip('\n').split('\t') for line in open(ldir + '/consts.tsv')]
    pid = np.empty(len(lrows), dtype=np.int64); new = []
    for i, f in enumerate(lrows):
        assert int(f[0]) == i
        j = maddr.get(f[1])
        if j is None: j = nm + len(new); new.append(i)
        pid[i] = j
    ln = np.fromfile(ldir + '/nodes.bin', dtype='<u4').reshape(-1, 4)
    shutil.copyfile(mdir + '/consts.tsv', out + '/consts.tsv')
    shutil.copyfile(mdir + '/nodes.bin', out + '/nodes.bin')
    start = mnodes
    with open(out + '/consts.tsv', 'a') as ct, open(out + '/nodes.bin', 'ab') as nb:
        for k, i in enumerate(new):
            f = list(lrows[i]); s, c = int(f[8]), int(f[9])
            seg = ln[s:s + c].copy()
            ref = np.isin(seg[:, 0], (2, 3, 4))
            seg[ref, 1] = pid[seg[ref, 1]].astype(np.uint32)
            nb.write(seg.astype('<u4').tobytes())
            f[0] = str(nm + k); f[8] = str(start); start += c
            ct.write('\t'.join(f) + '\n')
    np.save(out + '/pids.npy', pid)
    print('mathlib constants %d  library constants %d  new %d  pooled %d' % (nm, len(lrows), len(new), nm + len(new)))

if __name__ == '__main__':
    main()
