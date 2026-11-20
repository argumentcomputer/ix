#!/usr/bin/env python3
"""Rewrite generated `.obs` path-lemma proofs so their terms grow linearly with the function.

  obs_rewrite.py [--chunk K] FILE.lean...   rewrite each file in place
  obs_rewrite.py --fuse FILE.lean...        rewrite in continuation form (see `fuse_proof`)
  obs_rewrite.py --check FILE.lean...       report what would change, write nothing

The generated proofs are straight-line inversion scripts. Three habits make their terms grow
quadratically, because each substitution rebuilds every type that mentions the substituted
variable:

  * `calls = c₁ ++ c₂` and `values = v :: vs` are substituted as soon as they appear, into a
    goal whose call list and value lists keep growing;
  * the body of a `let` runs under `bindings ++ locals`, re-flattened at every variable lookup;
  * hypotheses whose inversion has been taken stay in the context, so every later heap or
    value substitution rebuilds their types, each with its own copy of the environment.

The rewrite keeps the `calls` equations as hypotheses and substitutes them at the end, innermost
first; substitutes an argument list's `values` equations in reverse at its `nil_inv`; flattens the
environment once when a `let` body is first used; and clears each hypothesis after its inversion.

With `--fuse` the proof is instead rewritten in continuation form (`fuse_proof`), for the cost of
checking it in IxVM, whose kernel pays for every subterm that mentions a bound variable once per
enclosing binder: one lemma application per inverted construct instead of a chain of
`Exists.casesOn`/`And.casesOn`, each carrying the rest of the statement, and lookups proved by
evaluation instead of a `simp` rewrite of the lookup equation and its substitution.

With `--chunk K` the proof is also cut every K tactic lines into nested `as_aux_lemma` blocks. Ix's
certified compile chooses a sharing order per constant at a cost that grows much faster than the
constant, so many constants of a few hundred thousand nodes compile in minutes where one of two
million does not finish in an hour.
"""
import re
import sys

LAST_CALLS = {"letValue_inv", "matchValue_inv", "binary_inv", "call_inv"}
FUSED_IMPORT = "import IxAIRefine.Core.Fused"
# The largest flat tuple/array pattern `IxAIRefine.Core.Fused` has a `let` lemma for.
FUSED_MAX = 20
THIRD_CALLS = {"var_inv", "literal_inv", "global_literal_inv"}
METHOD = re.compile(r"^(\s+)obtain ⟨(.*)⟩ := (\w+)\.(\w+)$")
FUNCTION = re.compile(r"^(\s+)obtain .* := [A-Za-z_.]+_inv (\w+)$")
FLATTEN = "List.cons_append, List.nil_append, List.append_nil, List.append_assoc"


def rewrite_proof(lines):
    """`lines`: the tactic lines of one proof, up to but excluding its closing `exact`."""
    fresh = 0
    calls, chains, rests, out = [], {}, set(), []

    def name():
        nonlocal fresh
        fresh += 1
        return f"hq{fresh}"

    for line in lines:
        m = METHOD.match(line)
        if not m:
            out.append(line)
            f = FUNCTION.match(line)
            if f:
                out.append(f"{f.group(1)}try clear {f.group(2)}")
            continue
        indent, comps, hyp, lemma = m.group(1), m.group(2).split(", "), m.group(3), m.group(4)
        after = []
        if hyp in rests:
            rests.discard(hyp)
            out.append(f"{indent}try simp only [{FLATTEN}] at {hyp}")
        if lemma == "letValue_inv":
            rests.add(comps[7])
        if lemma in LAST_CALLS:
            if comps[-1] != "rfl":
                raise ValueError(line)
            comps[-1] = name()
            calls.append(comps[-1])
        elif lemma in THIRD_CALLS:
            if len(comps) != 3 or comps[2] != "rfl":
                raise ValueError(line)
            comps[2] = name()
            calls.append(comps[2])
        elif lemma == "cons_inv":
            if len(comps) != 9 or comps[5] != "rfl" or comps[8] != "rfl":
                raise ValueError(line)
            comps[8] = name()
            calls.append(comps[8])
            comps[5] = name()
            chain = chains.pop(hyp, [])
            chain.append(comps[5])
            chains[comps[7]] = chain
        elif lemma == "nil_inv":
            if len(comps) != 3 or comps[0] != "rfl" or comps[2] != "rfl":
                raise ValueError(line)
            comps[2] = name()
            calls.append(comps[2])
            comps[0] = name()
            chain = chains.pop(hyp, [])
            chain.append(comps[0])
            after = [f"{indent}subst {h}" for h in reversed(chain)]
        out.append(f"{indent}obtain ⟨{', '.join(comps)}⟩ := {hyp}.{lemma}")
        out.append(f"{indent}try clear {hyp}")
        out.extend(after)
    if chains:
        raise ValueError(f"unfinished argument lists: {sorted(chains)}")
    out.extend(f"  subst {h}" for h in reversed(calls))
    return out


LET = re.compile(r"^  obtain ⟨(\w+), (\w+), (\w+), (\w+), (\w+), (\w+), (\w+), (\w+), rfl⟩ := (\w+)\.letValue_inv$")
CALL = re.compile(r"^  obtain ⟨(\w+), (\w+), (\w+), (\w+), (\w+), (\w+), rfl⟩ := (\w+)\.call_inv$")
CONS = re.compile(r"^  obtain ⟨(\w+), (\w+), (\w+), (\w+), (\w+), rfl, (\w+), (\w+), rfl⟩ := (\w+)\.cons_inv$")
VAR = re.compile(r"^  obtain ⟨(\w+), rfl, rfl⟩ := (\w+)\.var_inv$")
NIL = re.compile(r"^  obtain ⟨rfl, rfl, rfl⟩ := (\w+)\.nil_inv$")
INDEX = re.compile(r"^  obtain ⟨(\w+), (\w+), (\w+)⟩ := (\w+)\.index_inv$")
COLL = re.compile(r"^  obtain ⟨(\w+), (\w+), rfl⟩ := (\w+)\.(array|tuple)_inv$")
MBIND = re.compile(r"^  obtain rfl := matchPattern_bind_inv (\w+)$")
MTUP = re.compile(r"^  obtain ⟨(\w+), (\w+), -, (\w+)⟩ := matchPattern_(tuple|array)_inv (\w+)$")
MLCONS = re.compile(r"^  obtain ⟨(\w+), (\w+), (\w+), (\w+), rfl, (\w+), (\w+), rfl⟩ := matchListWith_cons_inv (\w+)$")
MLNIL = re.compile(r"^  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv (\w+)$")
GENERIC = re.compile(r"^  obtain ⟨(.*)⟩ := (\w+)\.(\w+)_inv$")
REFINE = re.compile(r"^refine (?:Fused\.\w+ (\w+)|(\w+)\.\w+_elim) ")
CONSUMES = re.compile(r":= (?:\w+_inv )?(\w+)(?:\.\w+_inv)?$")

CALL_SPLITS = {"letValue", "matchValue", "binary", "call"}
ELIMS = {"letValue", "call", "binary", "literal", "index", "project", "tuple", "array", "builtin",
         "hint", "nil", "cons", "var"}


class Fuser:
    """The continuation-form rewrite of one proof (`fuse_proof`)."""
    def __init__(self, lines):
        self.lines = lines
        self.consumer = {}
        for i, l in enumerate(lines):
            m = CONSUMES.search(l)
            if m and l.lstrip().startswith("obtain"):
                self.consumer.setdefault(m.group(1), i)
        self.skip = set()
        self.out = []
        self.deferred = []
        self.fresh = 0
        # derivations whose value is a fused tuple, with the name of the pattern's equation
        self.tuple_valued = {}
        # pending value-list equations of an argument list, keyed by its remaining derivation
        self.chains = {}

    def name(self, p):
        self.fresh += 1
        return f"{p}{self.fresh}"

    def at(self, h):
        i = self.consumer.get(h)
        return (i, self.lines[i]) if i is not None else (None, "")

    def emit(self, s):
        self.out.append("  " + s)
        m = REFINE.match(s)
        if m:
            self.out.append(f"  try clear {m.group(1) or m.group(2)}")

    def var_chain(self, i):
        """Lines i.. invert a variable: `obtain ⟨l, rfl, rfl⟩ := d.var_inv`, `simp at l`,
        `subst l`. Their indices, or None."""
        m = VAR.match(self.lines[i])
        if not m or self.lines[i + 1] != f"  simp at {m.group(1)}" or self.lines[i + 2] != f"  subst {m.group(1)}":
            return None
        return [i, i + 1, i + 2]

    def run(self):
        for i, line in enumerate(self.lines):
            if i in self.skip:
                continue
            self.step(i, line)
        self.out += [f"  subst {h}" for h in reversed(self.deferred)]
        return self.out

    def step(self, i, line):
        m = LET.match(line)
        if m:
            return self.let(m)
        m = CALL.match(line)
        if m:
            return self.call(i, m)
        m = COLL.match(line)
        if m:
            return self.coll(m)
        m = VAR.match(line)
        if m and self.var_chain(i):
            l, d = m.groups()
            self.skip.update(self.var_chain(i)[1:])
            hq, hm = self.name("zq"), self.name("zm")
            if d in self.tuple_valued:
                hv = self.tuple_valued.pop(d)
                self.emit(f"refine Fused.var_is {d} rfl fun {hv} {hm} {hq} => ?_")
            else:
                self.emit(f"refine Fused.var_is {d} rfl fun {l} {hm} {hq} => ?_")
                self.emit(f"subst {l}")
            self.emit(f"subst {hm}")
            self.deferred.append(hq)
            return
        m = CONS.match(line)
        if m:
            v, vs, mid, c1, c2, d, a2, a = m.groups()
            j, l2 = self.at(d)
            vc = self.var_chain(j) if j is not None else None
            if vc:
                hv = self.name("zv")
                self.skip.update(vc)
                self.emit(f"refine Fused.args_var_cons {a} rfl fun {vs} {hv} {a2} => ?_")
                self.chains[a2] = self.chains.pop(a, []) + [hv]
                return
            mi = INDEX.match(l2) if j is not None else None
            if mi:
                k, _ = self.at(mi.group(2))
                vc = self.var_chain(k) if k is not None else None
                if vc:
                    hv = self.name("zv")
                    self.skip.update([j] + vc)
                    self.emit(f"refine Fused.args_index_var_cons {a} rfl fun {v} {vs} {mi.group(3)} {hv} {a2} => ?_")
                    self.chains[a2] = self.chains.pop(a, []) + [hv]
                    return
            hv, hq = self.name("zv"), self.name("zq")
            self.emit(f"refine {a}.cons_elim fun {v} {vs} {mid} {c1} {c2} {hv} {d} {a2} {hq} => ?_")
            self.chains[a2] = self.chains.pop(a, []) + [hv]
            self.deferred.append(hq)
            return
        m = NIL.match(line)
        if m:
            hv, hm, hq = self.name("zv"), self.name("zm"), self.name("zq")
            self.emit(f"refine {m.group(1)}.nil_elim fun {hv} {hm} {hq} => ?_")
            for h in reversed(self.chains.pop(m.group(1), []) + [hv]):
                self.emit(f"subst {h}")
            self.emit(f"subst {hm}")
            self.deferred.append(hq)
            return
        m = INDEX.match(line)
        if m:
            p, e, pr, d = m.groups()
            self.emit(f"refine {d}.index_elim fun {p} {e} {pr} => ?_")
            return
        m = GENERIC.match(line)
        if m and m.group(3) in ELIMS:
            comps = m.group(1).split(", ")
            lemma = m.group(3)
            calls_at = len(comps) - 1 if lemma in LAST_CALLS else (2 if lemma == "literal" else None)
            names = []
            for c in comps:
                if c == "rfl":
                    h = self.name("ze")
                    names.append(h)
                else:
                    names.append("_" if c == "-" else c)
            self.emit(f"refine {m.group(2)}.{lemma}_elim fun {' '.join(names)} => ?_")
            for k, (c, n) in enumerate(zip(comps, names)):
                if c == "rfl":
                    if k == calls_at:
                        self.deferred.append(n)
                    else:
                        self.emit(f"subst {n}")
            return
        self.out.append(line)

    def let(self, m):
        v, mid, bs, c1, c2, de, mt, dr, d = m.groups()
        hq = self.name("zq")
        j, l = self.at(mt)
        if MBIND.match(l):
            self.skip.add(j)
            self.emit(f"refine Fused.let_bind {d} fun {v} {mid} {c1} {c2} {de} {dr} {hq} => ?_")
            self.deferred.append(hq)
            return
        mm = MTUP.match(l)
        if mm:
            vs, hv, ml, kind, _ = mm.groups()
            idx, xs = [j], []
            substituted = self.lines[j + 1] == f"  subst {hv}"
            if substituted:
                idx.append(j + 1)
            while True:
                k, lk = self.at(ml)
                if k is None:
                    break
                if MLNIL.match(lk):
                    idx.append(k)
                    break
                mc = MLCONS.match(lk)
                if not mc:
                    break
                b, _ = self.at(mc.group(5))
                if b is None or not MBIND.match(self.lines[b]):
                    break
                xs.append(mc.group(1))
                idx += [k, b]
                ml = mc.group(6)
            if MLNIL.match(self.lines[idx[-1]]) and 2 <= len(xs) <= FUSED_MAX:
                self.skip.update(idx)
                self.emit(f"refine Fused.let_{kind}_{len(xs)} {d} fun {' '.join(xs)} {mid} {c1} {c2} {de} {dr} {hq} => ?_")
                self.deferred.append(hq)
                if not substituted:
                    self.tuple_valued[de] = hv
                return
        self.emit(f"refine {d}.letValue_elim fun {v} {mid} {bs} {c1} {c2} {de} {mt} {dr} {hq} => ?_")
        self.deferred.append(hq)

    def call(self, i, m):
        vs, mid, c, cs, a, ev, d = m.groups()
        rw = f"  rw [instanceName_plain_some] at {ev}"
        hq = self.name("zq")
        if self.lines[i + 1] == rw:
            self.skip.add(i + 1)
            self.emit(f"refine Fused.call_plain {d} fun {vs} {mid} {c} {cs} {a} {ev} {hq} => ?_")
        else:
            self.emit(f"refine {d}.call_elim fun {vs} {mid} {c} {cs} {a} {ev} {hq} => ?_")
        self.deferred.append(hq)

    def coll(self, m):
        vs, a, d, kind = m.groups()
        hr = self.name("zr")
        self.emit(f"refine {d}.{kind}_elim fun {vs} {a} {hr} => ?_")
        self.emit(f"subst {hr}")


def fuse_proof(lines):
    """`lines`: the generator's tactic lines of one proof, up to but excluding its closing
    `exact`. Each inversion becomes one application of a continuation-form lemma
    (`IxAIRefine.Core.Fused`), so the proof term is a telescope of binders without the
    `Exists.casesOn`/`And.casesOn` layers of `obtain`; a call argument that is a variable or a
    projection of one, a `let` binding a name or a flat tuple/array of names, and a call of a
    plain function are inverted whole, with variable lookups proved by `rfl`. Value and heap
    equations are substituted where they appear, a list's in reverse at its end; call-list
    equations at the end of the proof, innermost first. Each consumed hypothesis is cleared, so
    that `--chunk` cuts abstract only over what is still live."""
    return Fuser(lines).run()


def chunk(lines, k):
    """Cut a tactic sequence into nested `as_aux_lemma` blocks of about `k` lines, so that each
    block becomes its own small constant. `lines` are tactic lines at two-space indent, with
    deeper continuation lines; a cut is made only before a line at exactly two spaces."""
    out, level, since = [], 0, 0
    for line in lines:
        top = line.startswith("  ") and not line.startswith("   ")
        if top and since >= k and not line.startswith("  exact "):
            out.append(" " * (2 + level) + "as_aux_lemma =>")
            level += 1
            since = 0
        out.append(" " * level + line)
        since += 1
    return out


def rewrite_file(path, check, chunk_lines, fused=False):
    text = open(path).read().split("\n")
    out, i, done = [], 0, 0
    while i < len(text):
        line = text[i]
        if not (line.startswith("theorem ") and ".obs " in line):
            out.append(line)
            i += 1
            continue
        end = next(j for j in range(i, len(text)) if text[j].startswith("  exact "))
        if any("subst hq" in l or "refine " in l for l in text[i:end]):
            raise ValueError(f"{path}: {line.split()[1]} is already rewritten")
        start = next(j for j in range(i, end) if text[j].lstrip().startswith("obtain "))
        out.extend(text[i:start])
        proof = (fuse_proof if fused else rewrite_proof)(text[start:end]) + [text[end]]
        out.extend(chunk(proof, chunk_lines) if chunk_lines else proof)
        i = end + 1
        done += 1
    if fused and done and FUSED_IMPORT not in out:
        last = max(k for k, l in enumerate(out) if l.startswith("import "))
        out.insert(last + 1, FUSED_IMPORT)
    print(f"{path}: {done} proofs, {len(text)} -> {len(out)} lines")
    if not check:
        open(path, "w").write("\n".join(out))


if __name__ == "__main__":
    args = sys.argv[1:]
    check = "--check" in args
    fused = "--fuse" in args
    chunk_lines = int(args[args.index("--chunk") + 1]) if "--chunk" in args else 0
    files = [a for i, a in enumerate(args)
             if a not in ("--check", "--chunk", "--fuse") and (i == 0 or args[i - 1] != "--chunk")]
    for p in files:
        rewrite_file(p, check, chunk_lines, fused)
