import sys, importlib.util
spec = importlib.util.spec_from_file_location("spans", sys.argv[1]); spans = importlib.util.module_from_spec(spec); spec.loader.exec_module(spans)
for d in sys.argv[2:]:
    S = spans.load(f"{d}/spans.jsonl")
    look = sorted(iv for s in S if s['name']=='stark/lookup_construction' for iv in s['intervals'])
    commit = sorted(iv for s in S if s['name']=='stark/stage1_commit' for iv in s['intervals'])
    def inside(t, ivs):
        import bisect
        i = bisect.bisect_right(ivs, (t, float('inf'))) - 1
        return i >= 0 and ivs[i][0] <= t <= ivs[i][1]
    cb = [iv for s in S if s['name']=='aiur/codegen_device_rows' for iv in s['intervals']]
    inl = [iv for iv in cb if inside(iv[0], look)]; inc = [iv for iv in cb if inside(iv[0], commit)]
    other = len(cb) - len(inl) - len(inc)
    print(f"{d.split('/')[-1]:24s} callbacks: lookup {spans.union(inl)/1e9:6.2f}s n={len(inl)}  commit {spans.union(inc)/1e9:6.2f}s n={len(inc)}  other n={other}  lookup_construction {spans.union(look)/1e9:6.2f}s  sum of callback durations in lookup {sum(b-a for a,b in inl)/1e9:6.2f}s")
