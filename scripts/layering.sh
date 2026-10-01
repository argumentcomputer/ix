#!/usr/bin/env bash
# scripts/layering.sh — the layering fence for the vendored con-leche tree
# under `Ix/Kernel/**` (`scripts/vendor-conleche.py list`).
#
# PORTED from con-leche at ae0c0c4e4ce6a0081648aff03fe9c39d002c4526,
# `tests/layering.sh` (Apache-2.0; the con-leche checkout for review is
# `plans/refs/con-leche`).  Upstream's long header records the gate's
# history; what it fences is summarised here.  Adaptations for this
# repository (plans/ix-kernel-con-leche-port-v4.md, L0; the move under
# `Ix/Kernel`, 2026-10-01):
#   * the module graph is the vendored tree only: every module under
#     `Ix/Kernel/` except Ix's boundary (`Ref`, `Search`, `Audit`, `Ingress`,
#     `Egress`, `Ixon`), as `scripts/vendor-conleche.py` lists it.  Upstream's
#     umbrella `ConLeche.lean` and `Main.lean` are not vendored, and the Ix
#     side is fenced by the Lean audits in `Ix/Kernel/Audit/*`;
#   * modules are classified BY THEIR UPSTREAM PATH
#     (`scripts/vendor-conleche.py upstream`): the vendoring flattens
#     `ConLeche/Kernel/X` to `Ix/Kernel/X`, so "the implementation" is what
#     sits upstream under `ConLeche/{Kernel,Cached,Frontend}/`;
#   * THE DEAD CLAUSE IS REPAIRED.  Upstream's base→model clause compared
#     `LANE[b] == 'P'`, a lane `lane()` never returns, so it could never
#     fire.  It now compares with `'model'`, and the capstone assembly is
#     classified BY PATH, as upstream's own comment states
#     (`ConLeche/Verify/Cached{,/*}` and `ConLeche/MainTheorem.lean`),
#     instead of the three-module list that contradicted it.  At ae0c0c4e
#     the repaired clause finds no edge; with upstream's list it would
#     report `Verify/Cached/{InstalledC,StreamConsts}` → `Model/Fold`,
#     which are capstone modules by layout;
#   * a fifth clause, THE BOUNDARY: a vendored module imports only vendored
#     modules, `Init`, `Std` and `Lean` (the last at elaboration time; the
#     Lean import audit checks that part).  Ix's boundary imports the
#     vendored tree, never the other way round;
#   * an absent tree passes vacuously, and the rules-closure clause waits
#     until a rules module exists.
#
# THE CLAUSES.
#   1. IMPLEMENTATION→THEORY: upstream's `ConLeche/{Kernel,Cached,Frontend}/*`
#      (now `Ix/Kernel/{*.lean,Basis,Inductives,Cached,Frontend}`) never
#      import `Ix.Kernel.{Verify,SetTheory,Model,SetModel,Semantics,Term}.*`.
#   2. BASE→MODEL: no base module (everything outside the model lane
#      `Ix/Kernel/Model{,/*}` and the capstone assembly) imports the model
#      lane.
#   3. THE RULES FENCE: `Ix/Kernel/Rules/*` and `Ix/Kernel/Model/Rules/*`
#      (except `Model.Rules.Recompose`) do not directly import
#      `Ix.Kernel.{Core,TypeChecker,CoreIO,DeclCheck,Checker*}` or `Cached*`.
#   4. THE RULES CLOSURE: the elaboration closure of those modules (direct
#      imports, then `public import`s) reaches exactly the five recorded
#      doors.  A new door is a regression; a door no longer reached is
#      progress to record by deleting it here.  Both fail.
#   5. THE BOUNDARY (above).
#
# Every import kind is an edge: `public`, `private`, `meta`, `import all`.
# Lake gives no import barrier between `lean_lib`s of one package, so this
# script, not the library split, is the fence.
#
# Usage: scripts/layering.sh [--list]   (--list prints the base→model
# edges, every rules module's elaboration closure with its doors marked
# `!`, and one witnessing chain per door).
set -u
cd "$(dirname "$0")/.."
exec python3 - "$@" <<'PYEOF'
import os, re, sys

import importlib.util
sys.dont_write_bytecode = True   # no __pycache__ in the tree
_spec = importlib.util.spec_from_file_location('vendor', 'scripts/vendor-conleche.py')
vendor = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(vendor)
TREE = vendor.vendored_tree()
if not TREE:
    print('layering: no vendored tree under Ix/Kernel/; nothing to check')
    sys.exit(0)

IMP = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)

# --------------------------------------------------------------- the
# module graph.
mods = {rel[:-5].replace('/', '.'): rel for rel in TREE}
UP = {name: vendor.upstream_path(rel) for name, rel in mods.items()}

def source(rel):
    return re.sub(r'/-.*?-/', '', open(rel, encoding='utf-8').read(), flags=re.S)   # strip block comments

imports = {name: IMP.findall(source(rel)) for name, rel in mods.items()}
edges = {name: [m for m in imports[name] if m in mods] for name in mods}

# --------------------------------------------------------------- the
# classification, BY UPSTREAM PATH: `ConLeche/Model{,/*}` is the lane,
# `ConLeche/Verify/Cached{,/*}` and `ConLeche/MainTheorem.lean` are the
# capstone assembly, upstream's umbrella `ConLeche.lean` (not vendored) the
# umbrella, everything else is base.
IMPL_DIRS   = ('ConLeche/Kernel/', 'ConLeche/Cached/', 'ConLeche/Frontend/')
THEORY_PFX  = ('Ix.Kernel.Verify.', 'Ix.Kernel.SetTheory.',
               'Ix.Kernel.Model.', 'Ix.Kernel.SetModel.', 'Ix.Kernel.Semantics.',
               'Ix.Kernel.Term.')

def lane(m):
    up = UP[m]
    if (up in ('ConLeche/Verify/Cached.lean', 'ConLeche/MainTheorem.lean')
            or up.startswith('ConLeche/Verify/Cached/')):
        return 'caps'
    if up == 'ConLeche.lean': return 'umbrella'
    if up == 'ConLeche/Model.lean' or up.startswith('ConLeche/Model/'): return 'model'
    return 'base'

LANE = {m: lane(m) for m in mods}

basev = sorted((a, b) for a in mods for b in edges[a]
               if LANE[a] == 'base' and LANE[b] == 'model')
implv = sorted((a, b) for a in mods for b in edges[a]
               if UP[a].startswith(IMPL_DIRS) and b.startswith(THEORY_PFX))

# THE BOUNDARY: the vendored tree imports only itself and the toolchain.
BOUNDARY = ('Init', 'Std', 'Lean')
boundv = sorted((a, b) for a in mods for b in imports[a]
                if b not in mods and b.split('.')[0] not in BOUNDARY)

# THE RULES FENCE (upstream task #305).
RULES_DIRS  = ('ConLeche/Rules/', 'ConLeche/Model/Rules/')
RULES_EXEMPT = {'Ix.Kernel.Model.Rules.Recompose'}
def impl_mod(b):
    return (b in ('Ix.Kernel.Core', 'Ix.Kernel.TypeChecker',
                  'Ix.Kernel.CoreIO', 'Ix.Kernel.DeclCheck',
                  'Ix.Kernel.Cached')
            or b.startswith('Ix.Kernel.Checker')
            or b.startswith('Ix.Kernel.Cached.'))
rulesv = sorted((a, b) for a in mods for b in edges[a]
                if UP[a].startswith(RULES_DIRS) and a not in RULES_EXEMPT
                and impl_mod(b))

# THE RULES FENCE, CLOSURE FORM.  A module elaborates in its direct
# imports plus, transitively, their `public import`s (`import all` is a
# direct edge; a `meta import` is elaboration-time only and invisible to a
# proof), so that closure bounds what its proofs can reach.
PUBIMP = re.compile(r'^\s*(?:public\s+)+import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
DIRIMP = re.compile(r'^\s*(?:public\s+|private\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
pubedges, diredges = {}, {}
for name, rel in mods.items():
    src = source(rel)
    pubedges[name] = [m for m in PUBIMP.findall(src) if m in mods]
    diredges[name] = [m for m in DIRIMP.findall(src) if m in mods]

def closure_with_parents(m):
    """the elaboration environment of `m`, and for each member the edge it
    entered through (first hop: any non-meta import; later hops: public
    imports only)"""
    parent, todo = {}, []
    for x in diredges[m]:
        if x not in parent: parent[x] = m; todo.append(x)
    while todo:
        x = todo.pop()
        for y in pubedges[x]:
            if y not in parent: parent[y] = x; todo.append(y)
    return parent

def chain_to(parent, m, t):
    ch = [t]
    while ch[-1] != m: ch.append(parent[ch[-1]])
    return ' <- '.join(ch)

RULES_CLOSURE_DOORS = {
    'Ix.Kernel.Core',
    'Ix.Kernel.TypeChecker',
    'Ix.Kernel.CoreIO',
    'Ix.Kernel.Checker',
    'Ix.Kernel.CheckerBase',
}
rules_mods = sorted(m for m in mods if UP[m].startswith(RULES_DIRS)
                    and m not in RULES_EXEMPT)
rules_closure = {m: closure_with_parents(m) for m in rules_mods}
doors_seen = {}
for m in rules_mods:
    for t in rules_closure[m]:
        if impl_mod(t):
            doors_seen.setdefault(t, (m, chain_to(rules_closure[m], m, t)))
new_doors  = sorted(t for t in doors_seen if t not in RULES_CLOSURE_DOORS)
# The closure clause waits for the rules tier: while the subtree is
# imported step by step there may be no rules module yet.
gone_doors = sorted(t for t in RULES_CLOSURE_DOORS if t not in doors_seen) if rules_mods else []

if '--list' in sys.argv[1:]:
    for a, b in basev:
        print(f'{a} -> {b}')
    for m in rules_mods:
        par = rules_closure[m]
        marks = ' '.join(('!' if impl_mod(x) else '') + x for x in sorted(par))
        print(f'closure {m} ({len(par)}): {marks}')
    for t, (m, ch) in sorted(doors_seen.items()):
        print(f'door {t}: {ch}')
    sys.exit(0)

fail = 0
def report(title, items, hint):
    global fail
    if items:
        fail = 1
        print(f'LAYERING FAIL — {title} ({len(items)}):')
        for a, b in items:
            print(f'    {a} -> {b}')
        print(f'    {hint}')

report('base module importing the model lane', basev,
       'upstream ConLeche/{Kernel,Verify,SetTheory,Term,SetModel,Semantics}/* stand '
       'BELOW the lane; nothing there may import Ix/Kernel/Model/*.')
report('implementation importing theory', implv,
       'upstream ConLeche/{Kernel,Cached,Frontend}/* must never import '
       'Ix/Kernel/{SetTheory,SetModel,Semantics,Model,Verify,Term}/*.')
report('rules tier importing the pure implementation', rulesv,
       'Ix/Kernel/Rules/* and Ix/Kernel/Model/Rules/* are stated over '
       'Ix/Kernel/CoreDefs and may not import Ix/Kernel/{Core,TypeChecker,'
       'CoreIO,Checker*,DeclCheck} or Cached/*.')
report('rules tier CLOSURE reaching an unlisted implementation module',
       [(doors_seen[t][0], t) for t in new_doors] +
       [('  via', doors_seen[t][1]) for t in new_doors],
       'a new public re-export carries the impl into the rules tier\'s '
       'elaboration environment; repoint it (see --list).')
report('rules tier CLOSURE door no longer reached (record the progress)',
       [('RULES_CLOSURE_DOORS', t) for t in gone_doors],
       'delete the door from RULES_CLOSURE_DOORS in this script and say so '
       'in the evidence note.')
report('vendored tree importing outside itself and the toolchain', boundv,
       'the vendored tree imports only itself, Init, Std and Lean; Ix\'s '
       'boundary imports the vendored tree, never the reverse.')

n = {l: sum(1 for m in LANE if LANE[m] == l)
     for l in ("base", "model", "caps", "umbrella")}
if not fail:
    print(f'layering: base {n["base"]} / model {n["model"]} / caps {n["caps"]} / '
          f'umbrella {n["umbrella"]} modules; '
          f'{len(basev)} base->model edges, {len(implv)} impl->theory, '
          f'{len(rulesv)} rules->impl, {len(boundv)} outside the boundary; '
          f'rules closure: {len(rules_mods)} modules, '
          f'{len(doors_seen)} doors{" as listed" if rules_mods else " (no rules module yet)"}')
sys.exit(fail)
PYEOF
