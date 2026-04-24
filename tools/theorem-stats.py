#!/usr/bin/env python3
"""Theorem dependency analysis for Aiur verified-compiler proofs.

Walks Ix/Aiur/Proofs/*.lean, parses theorems + bodies, builds a DAG.
Reports numerical metrics: sorry hot-spots, critical paths, per-file
breakdown, bottleneck ranking. Output: tools/theorem-stats.md.
"""
from __future__ import annotations
import re
from collections import deque, Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROOFS_DIR = ROOT / "Ix" / "Aiur" / "Proofs"
OUT_MD = ROOT / "tools" / "theorem-stats.md"
ROOT_THM = "Aiur.Toplevel.compile_correct"

DENY = {
    "Nat","Int","Bool","True","False","Prop","Type","Sort","String","List",
    "Option","Some","None","Except","Ok","Error","Unit","Eq","Ne","And","Or",
    "Not","Iff","Forall","Exists","Sigma","Char","UInt8","UInt16","UInt32",
    "UInt64","Array","Vector","HashMap","Std","Lean","Name","Function","Set",
    "Map","Pair","Mem","Subtype","Decidable","DecidableEq","Inhabited","BEq",
    "Hashable","Ord","Repr","ToString","Coe","Monad","Pure","Bind","Functor",
    "Applicative","Id","IO","Empty","PUnit","PSum","PSigma","PProd","Prod",
    "Sum","Quot","Quotient","HEq","Cast","ULevel","ReaderT","StateT","ExceptT",
}
THM_HEAD = re.compile(
    r"^(?:private\s+|@\[[^\]]*\]\s+)*theorem\s+([A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*)",
    re.MULTILINE)
BOUNDARY = re.compile(
    r"^(?:private\s+|@\[[^\]]*\]\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom|namespace|end)\b",
    re.MULTILINE)
NS_OPEN = re.compile(r"^namespace\s+([A-Za-z_][\w.]*)", re.MULTILINE)
NS_CLOSE = re.compile(r"^end(?:\s+([A-Za-z_][\w.]*))?\s*$", re.MULTILINE)
CITE_UPPER = re.compile(r"\b[A-Z][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\b")
CITE_LOWER = re.compile(r"\b[a-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\b")
LINE_C = re.compile(r"--[^\n]*")
BLOCK_C = re.compile(r"/-.*?-/", re.DOTALL)


def strip_comments(s):
    return LINE_C.sub("", BLOCK_C.sub(" ", s))


def ns_map(src):
    ev = [(m.start(), "o", m.group(1)) for m in NS_OPEN.finditer(src)]
    ev += [(m.start(), "c", m.group(1) or "") for m in NS_CLOSE.finditer(src)]
    ev.sort()
    out, stack, last = [(0, "")], [], 0
    for off, kind, n in ev:
        out.append((last, ".".join(stack)))
        if kind == "o":
            stack.append(n)
        elif stack and (not n or stack[-1].endswith(n)):
            stack.pop()
        last = off
    out.append((last, ".".join(stack)))
    return out


def ns_at(nm, off):
    cur = ""
    for o, n in nm:
        if o <= off:
            cur = n
        else:
            break
    return cur


def parse_file(path):
    src = strip_comments(path.read_text())
    nm = ns_map(src)
    bounds = [m.start() for m in BOUNDARY.finditer(src)] + [len(src)]
    for i, start in enumerate(bounds[:-1]):
        chunk = src[start:bounds[i + 1]]
        m = THM_HEAD.match(chunk)
        if not m:
            continue
        ns = ns_at(nm, start)
        fqn = f"{ns}.{m.group(1)}" if ns else m.group(1)
        sc = len(re.findall(r"\bsorry\b", chunk))
        loc = chunk.count("\n")
        yield fqn, chunk, sc, loc


def short(fqn):
    return fqn[5:] if fqn.startswith("Aiur.") else fqn


def reachable(start, edges):
    """BFS from start through edges; return set of reached nodes."""
    seen = {start}
    q = deque([start])
    while q:
        n = q.popleft()
        for d in edges.get(n, ()):
            if d not in seen:
                seen.add(d)
                q.append(d)
    return seen


def main():
    nodes = {}
    sym = defaultdict(set)
    for path in sorted(PROOFS_DIR.glob("*.lean")):
        for fqn, body, sc, loc in parse_file(path):
            nodes[fqn] = {"file": path.name, "body": body, "sorry": sc, "loc": loc, "deps": set()}
            parts = fqn.split(".")
            for k in range(len(parts)):
                sym[".".join(parts[k:])].add(fqn)

    for fqn, info in nodes.items():
        cites = set()
        for r in (CITE_UPPER, CITE_LOWER):
            for tok in r.findall(info["body"]):
                if tok in DENY:
                    continue
                for tgt in sym.get(tok, ()):
                    if tgt != fqn:
                        cites.add(tgt)
        info["deps"] = cites

    forward = {f: i["deps"] for f, i in nodes.items()}
    own_sorry = {f for f, i in nodes.items() if i["sorry"] > 0}
    rev = defaultdict(set)
    for s, ds in forward.items():
        for d in ds:
            if d in nodes:
                rev[d].add(s)
    rev = dict(rev)

    # Tainted: yellow = depends on a sorry transitively (BFS over reverse from each red).
    tainted = set()
    q = deque(own_sorry)
    while q:
        n = q.popleft()
        for p in rev.get(n, ()):
            if p not in tainted and p not in own_sorry:
                tainted.add(p)
                q.append(p)

    # Distance from compile_correct (forward).
    dist = {}
    if ROOT_THM in nodes:
        dist[ROOT_THM] = 0
        q = deque([ROOT_THM])
        while q:
            n = q.popleft()
            for d in forward.get(n, ()):
                if d not in dist:
                    dist[d] = dist[n] + 1
                    q.append(d)

    # Per-file breakdown.
    file_stats = defaultdict(lambda: {"thms": 0, "red": 0, "yel": 0, "sorries": 0, "loc": 0})
    for fqn, info in nodes.items():
        f = file_stats[info["file"]]
        f["thms"] += 1
        f["sorries"] += info["sorry"]
        f["loc"] += info["loc"]
        if fqn in own_sorry:
            f["red"] += 1
        elif fqn in tainted:
            f["yel"] += 1

    # Sorry impact: for each red, count ancestors that depend on it (taint-reach upward).
    sorry_impact = {}
    for r in own_sorry:
        anc = reachable(r, rev)
        sorry_impact[r] = {
            "ancestors": len(anc) - 1,
            "ancestors_red": len([a for a in anc if a != r and a in own_sorry]),
            "reaches_compile_correct": ROOT_THM in anc,
        }

    # Sorry depth: for each red, count descendants (forward reach).
    sorry_depth = {}
    for r in own_sorry:
        desc = reachable(r, forward)
        sorry_depth[r] = {
            "descendants": len(desc) - 1,
            "descendants_red": len([d for d in desc if d != r and d in own_sorry]),
        }

    # Critical reach: count of red+yellow nodes reachable forward from each red.
    # (BFS, cycle-safe — replaces recursive longest-path which hit cycles.)
    crit_chain = {}
    for r in own_sorry:
        seen = {r}
        q = deque([r])
        ry_count = 0
        while q:
            n = q.popleft()
            for d in forward.get(n, ()):
                if d in seen:
                    continue
                seen.add(d)
                if d in own_sorry or d in tainted:
                    ry_count += 1
                    q.append(d)
        crit_chain[r] = ry_count

    # In-degree (citation count) per red.
    in_deg = {r: len(rev.get(r, ())) for r in own_sorry}

    # Hot-spot ranking: closing a red theorem unblocks its (cite-graph) ancestors.
    # Score = ancestors-reachable. Top ones = closure-leverage.
    by_leverage = sorted(own_sorry, key=lambda r: -sorry_impact[r]["ancestors"])

    # Cycle detection via Tarjan SCC.
    def sccs():
        idx = {}
        low = {}
        stack = []
        on = set()
        cnt = [0]
        out = []

        def strong(v):
            idx[v] = low[v] = cnt[0]
            cnt[0] += 1
            stack.append(v)
            on.add(v)
            for w in forward.get(v, ()):
                if w not in idx:
                    strong(w)
                    low[v] = min(low[v], low[w])
                elif w in on:
                    low[v] = min(low[v], idx[w])
            if low[v] == idx[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                out.append(comp)
        import sys
        sys.setrecursionlimit(10000)
        for v in nodes:
            if v not in idx:
                strong(v)
        return out

    nontrivial_sccs = [c for c in sccs() if len(c) > 1]

    # File-level critical files (most red/yellow load).
    by_file_red_yel = sorted(
        file_stats.items(), key=lambda kv: -(kv[1]["red"] + kv[1]["yel"]))

    # Build report.
    L = []
    P = L.append
    P("# Theorem dependency analysis")
    P("")
    P(f"Generated from `Ix/Aiur/Proofs/*.lean`. Root: `{short(ROOT_THM)}`.")
    P("")
    P("## Summary")
    P("")
    red, yel = len(own_sorry), len(tainted)
    grn = len(nodes) - red - yel
    P(f"- **{len(nodes)} theorems** across {len(file_stats)} files.")
    P(f"- **{red} red** (own sorry), **{yel} yellow** (transitive sorry), **{grn} green** (clean).")
    P(f"- **{len(dist)} reachable** from `compile_correct` ({len(nodes) - len(dist)} unreached).")
    P(f"- **Total sorry occurrences**: {sum(i['sorry'] for i in nodes.values())}.")
    P("")
    P("## Distance from `compile_correct` (forward edges)")
    P("")
    P("| d | count | red | yellow | green |")
    P("|---|---|---|---|---|")
    bucket = defaultdict(lambda: [0, 0, 0, 0])
    for f, d in dist.items():
        b = bucket[d]
        b[0] += 1
        if f in own_sorry: b[1] += 1
        elif f in tainted: b[2] += 1
        else: b[3] += 1
    for d in sorted(bucket):
        b = bucket[d]
        P(f"| {d} | {b[0]} | {b[1]} | {b[2]} | {b[3]} |")
    P("")
    P("## Sorry hot-spots (by leverage = transitive ancestors that depend on closure)")
    P("")
    P("Closing a high-leverage red unblocks the largest sub-tree of dependents.")
    P("")
    P("| Rank | Theorem | File | LoC | Sorries | Ancestors | d | Reaches root |")
    P("|---|---|---|---|---|---|---|---|")
    for i, r in enumerate(by_leverage, 1):
        info = nodes[r]
        imp = sorry_impact[r]
        d = dist.get(r, "—")
        reaches = "✓" if imp["reaches_compile_correct"] else " "
        P(f"| {i} | `{short(r)}` | `{info['file']}` | {info['loc']} | {info['sorry']} | {imp['ancestors']} | {d} | {reaches} |")
    P("")
    P("## Sorry depth (forward reach — how much further the proof obligation extends)")
    P("")
    P("| Theorem | Descendants | Red descendants |")
    P("|---|---|---|")
    by_depth = sorted(own_sorry, key=lambda r: -sorry_depth[r]["descendants"])
    for r in by_depth:
        d = sorry_depth[r]
        P(f"| `{short(r)}` | {d['descendants']} | {d['descendants_red']} |")
    P("")
    P("## Critical reach — red/yellow nodes reachable forward from each red")
    P("")
    P("| Theorem | Reachable red+yellow |")
    P("|---|---|")
    for r in sorted(own_sorry, key=lambda r: -crit_chain[r]):
        P(f"| `{short(r)}` | {crit_chain[r]} |")
    P("")
    P("## Per-file breakdown")
    P("")
    P("| File | Theorems | Red | Yellow | Sorries | LoC |")
    P("|---|---|---|---|---|---|")
    for fname, fs in by_file_red_yel:
        if fs["red"] or fs["yel"]:
            P(f"| `{fname}` | {fs['thms']} | {fs['red']} | {fs['yel']} | {fs['sorries']} | {fs['loc']} |")
    P("")
    if nontrivial_sccs:
        P("## Cycles (non-trivial SCCs)")
        P("")
        for comp in nontrivial_sccs:
            P(f"- {len(comp)}-cycle: " + ", ".join(f"`{short(c)}`" for c in comp))
        P("")
    else:
        P("## Cycles")
        P("")
        P("None (DAG-shaped).")
        P("")
    P("## Red list (compact)")
    P("")
    for r in sorted(own_sorry):
        info = nodes[r]
        d = dist.get(r, "—")
        P(f"- `{short(r)}` ({info['file']}, {info['sorry']}× sorry, d={d})")
    P("")
    P("## Yellow list (compact)")
    P("")
    for r in sorted(tainted):
        info = nodes[r]
        d = dist.get(r, "—")
        P(f"- `{short(r)}` ({info['file']}, d={d})")
    P("")

    OUT_MD.parent.mkdir(parents=True, exist_ok=True)
    OUT_MD.write_text("\n".join(L))
    print(f"Total theorems:    {len(nodes)}")
    print(f"  Red (own sorry): {red}")
    print(f"  Yellow (taint):  {yel}")
    print(f"  Green (clean):   {grn}")
    print(f"  Reachable from {short(ROOT_THM)}: {len(dist)}")
    print(f"Top 5 leverage reds:")
    for r in by_leverage[:5]:
        imp = sorry_impact[r]
        print(f"  {imp['ancestors']:>4} anc | d={dist.get(r, '—')} | {short(r)}")
    print(f"Stats written: {OUT_MD}")


if __name__ == "__main__":
    main()
