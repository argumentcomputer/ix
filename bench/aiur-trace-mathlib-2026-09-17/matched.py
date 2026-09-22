import json, re, sys
sys.path.insert(0, 'bench/aiur-trace-init-2026-09-16')
from spans import load, union
def phases(run):
    spans = load(f'{run}/spans.jsonl')
    proofs = sorted(iv for s in spans if s['name'] == 'aiur/prove_planned' for iv in s['intervals'])
    log = open(f'{run}/stderr.log').read().splitlines()
    pe = re.compile(r"worker \d+: (claim \d+|join \d+|root) (?:proven|published) at \+(\d+)s")
    units = [m[1] for l in log for m in [pe.search(l)] if m]
    assert len(units) == len(proofs), (len(units), len(proofs))
    out = {}
    for name in ('stark/stage1_commit', 'stark/lookup_construction', 'stark/quotient', 'stark/fri_open', 'aiur/witness', 'aiur/codegen_seeds', 'aiur/codegen_device_rows'):
        ivs = [iv for s in spans if s['name'] == name for iv in s['intervals']]
        for u, (a, b) in zip(units, proofs):
            clipped = [(max(a, x), min(b, y)) for x, y in ivs if y > a and x < b]
            out.setdefault(u, {})[name] = union(clipped) / 1e9
    for u, (a, b) in zip(units, proofs): out[u]['proof'] = (b - a) / 1e9
    return out
R = sys.argv[1]
cpu, gen = phases(f'{R}/q78-ix-new6-cpu'), phases(f'{R}/q78-ix-new6-generated')
claims = [f'claim {i}' for i in range(11)]
print(f"{'phase, same 11 claims':28} {'cpu':>8} {'gen':>8} {'delta':>8}")
for name in ('proof', 'stark/stage1_commit', 'stark/lookup_construction', 'stark/quotient', 'stark/fri_open', 'aiur/witness', 'aiur/codegen_seeds', 'aiur/codegen_device_rows'):
    c = sum(cpu[u][name] for u in claims); g = sum(gen[u][name] for u in claims)
    print(f"{name:28} {c:8.1f} {g:8.1f} {g-c:+8.1f}")
joins = [u for u in cpu if u.startswith('join') and u in gen]
print(f"same joins: {joins}")
for name in ('proof', 'stark/stage1_commit', 'stark/lookup_construction', 'aiur/witness'):
    c = sum(cpu[u][name] for u in joins); g = sum(gen[u][name] for u in joins)
    print(f"{name:28} {c:8.1f} {g:8.1f} {g-c:+8.1f}")
