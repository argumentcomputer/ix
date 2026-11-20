#!/usr/bin/env python3
"""Rewrite generated `.obs` path-lemma proofs so their terms grow linearly with the function.

  obs_rewrite.py [--chunk K] FILE.lean...   rewrite each file in place
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

With `--chunk K` the proof is also cut every K tactic lines into nested `as_aux_lemma` blocks. Ix's
certified compile chooses a sharing order per constant at a cost that grows much faster than the
constant, so many constants of a few hundred thousand nodes compile in minutes where one of two
million does not finish in an hour.
"""
import re
import sys

LAST_CALLS = {"letValue_inv", "matchValue_inv", "binary_inv", "call_inv"}
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


def rewrite_file(path, check, chunk_lines):
    text = open(path).read().split("\n")
    out, i, done = [], 0, 0
    while i < len(text):
        line = text[i]
        if not (line.startswith("theorem ") and ".obs " in line):
            out.append(line)
            i += 1
            continue
        end = next(j for j in range(i, len(text)) if text[j].startswith("  exact "))
        if any("subst hq" in l for l in text[i:end]):
            raise ValueError(f"{path}: {line.split()[1]} is already rewritten")
        start = next(j for j in range(i, end) if text[j].lstrip().startswith("obtain "))
        out.extend(text[i:start])
        proof = rewrite_proof(text[start:end]) + [text[end]]
        out.extend(chunk(proof, chunk_lines) if chunk_lines else proof)
        i = end + 1
        done += 1
    print(f"{path}: {done} proofs, {len(text)} -> {len(out)} lines")
    if not check:
        open(path, "w").write("\n".join(out))


if __name__ == "__main__":
    args = sys.argv[1:]
    check = "--check" in args
    chunk_lines = int(args[args.index("--chunk") + 1]) if "--chunk" in args else 0
    files = [a for i, a in enumerate(args)
             if a not in ("--check", "--chunk") and (i == 0 or args[i - 1] != "--chunk")]
    for p in files:
        rewrite_file(p, check, chunk_lines)
