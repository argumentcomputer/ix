#!/usr/bin/env bash
# scripts/trust-surface.sh — the trust-surface fence for the vendored
# con-leche tree under `Ix/Kernel/**` (`scripts/vendor-conleche.py list`).
#
# PORTED from con-leche at ae0c0c4e4ce6a0081648aff03fe9c39d002c4526,
# `tests/trust-surface.sh` (Apache-2.0; the checkout for review is
# `plans/refs/con-leche`), with its lexer fixture copied verbatim to
# `scripts/trust-surface/lexer.lean`.  Adaptations for this repository
# (plans/ix-kernel-con-leche-port-v4.md, L0; the move under `Ix/Kernel`,
# 2026-10-01):
#   * the scan covers the vendored tree: every `Ix/Kernel/**/*.lean` except
#     Ix's boundary (`Ref`, `Search`, `Audit`, `Ingress`, `Egress`, `Ixon`)
#     and Ix's umbrella `Ix/Kernel.lean`.  Ix's own sources are fenced by the
#     Lean audits in `Ix/Kernel/Audit/*` (which see compiled code, not
#     tokens), and Ix's tests deliberately hold the audits' negative
#     controls;
#   * the allowlist drops `Main.lean` (con-leche's driver and its
#     `markPersistent` calls are not ported) and `ConLeche/Challenge.lean`
#     (the Comparator pair is not ported; inventory section 3.7, row 2);
#   * the allowlist names files by their vendored paths
#     (`ConLeche/Kernel/X` is `Ix/Kernel/X`);
#   * an absent tree scans nothing and passes once the lexer self-test
#     passes.
#   * ruled entries are recorded once more in the Lean runtime audit
#     (`Ix.Kernel.Audit.runtimeRulings`), which checks the compiled closure.
#
# WHY THIS EXISTS (upstream).  The layering fence keeps the implementation
# from importing the theory; this gate keeps compiler escapes out of every
# file that is not knowingly part of the trusted computing base.  The
# escapes are invisible to `#print axioms`: a theorem can stand at exactly
# `[propext, Classical.choice, Quot.sound]` and still be about a function
# whose compiled behaviour was swapped by `@[implemented_by]`, read off a
# `@[computed_field]` word, or decided by `native_decide`.  An escape is a
# TCB entry, admissible only where someone has written down why.
#
# THE BLANKING IS A LEXER, NOT A REGEX (upstream task #224).  `code_only`
# is a one-pass state machine covering line comments, nested block
# comments, string literals with every escape including the string gap
# (`\` NEWLINE), single-line `{…}` interpolations (left as code), raw
# strings, and character literals.  An unterminated literal is a hard
# error.  `scripts/trust-surface/lexer.lean` exercises every form and
# names, in trailing `EXPECT:` markers, exactly the lines the gate must
# report; `--selftest` runs that check alone, and every run does it first.
#
# THE ALLOWLIST, and the justification for every entry (file → the tokens
# tolerated there).  A token in an allowlisted file that is not on its own
# list fails just as loudly as one in a bare file.
#
#   Ix/Kernel/Expr.lean          computed_field
#       The packed `@[computed_field] data` and `Level.hashData`: the
#       user's ruling R-meta ("we trust the compiler"), the same escape
#       class `Lean.Expr` lives on.  Expression equality is not an escape:
#       it goes through `@[csimp]` + `withPtrEq`/`withPtrAddr` with the
#       memoised descent proved equal to `decide (a = b)`.
#
#   Ix/Kernel/Name.lean          computed_field
#       A cached hash only (`Name.hashData`), as `Lean.Name`'s.  Pointer
#       equality goes through `@[csimp]` + `withPtrEq` with the redundancy
#       proved (`Name.beqPtr_eq`).
#
#   Ix/Kernel/Exclusive.lean     unsafe, implemented_by
#       `withExclusive`: defined as `k false` and `@[implemented_by]` the
#       compiled `k (isExclusiveUnsafe a)`, the reference-count read the
#       substitution memo keys on.  The obligation `h : k true = k false`
#       licenses the substitution; every use goes through `withExcl`,
#       whose continuation returns a `Subsingleton`, so `h` is
#       `Subsingleton.elim`.  The file's docstring is the justification.
#
#   Ix/Kernel/BasisGen.lean      unsafe, implemented_by
#       ELABORATION ONLY.  `#annotate_basis` / `#annotate_pins` run the
#       annotation pass at elaboration time through `unsafe evalTerm`
#       (a `meta section`) and splice the resulting literals.  Nothing here
#       is in the binary; the literals are ordinary data the proofs consume.
#
# Not policed, as upstream: `partial`, `@[csimp]`, `withPtrEq`/`withPtrAddr`,
# `opaque`, `noncomputable`.  The Lean runtime audit polices the compiled
# form of the first two (`partial` only in `Ix/Kernel/Frontend/InModel*`,
# `csimp` only with a theorem on the standard axioms).
#
# Usage: scripts/trust-surface.sh [--list|--selftest]
#   --list      print every scanned occurrence, allowlisted or not.
#   --selftest  run only the lexer self-test.
set -u
cd "$(dirname "$0")/.."
exec python3 - "$@" <<'PYEOF'
import os, re, sys

# --------------------------------------------------------------- the
# tokens.  Each is a compiler escape that `#print axioms` cannot see.
TOKENS = {
    'unsafe':         re.compile(r'\bunsafe\b'),
    'unsafeCast':     re.compile(r'\bunsafeCast\b'),
    'ptrAddrUnsafe':  re.compile(r'\bptrAddrUnsafe\b'),
    'implemented_by': re.compile(r'\bimplemented_by\b'),
    'computed_field': re.compile(r'\bcomputed_field\b'),
    'native_decide':  re.compile(r'\bnative_decide\b'),
    # bare `ofReduceBool`/`ofReduceNat`: the meta-logic's compiler-trust
    # axioms.  The checker's own name constants (`ofReduceBoolName`,
    # `ofReduceBoolA`) are longer identifiers and do not match.
    'ofReduceBool':   re.compile(r'\bofReduce(?:Bool|Nat)\b'),
    'sorry':          re.compile(r'\bsorry\b'),
    'lcProof':        re.compile(r'\blcProof\b'),
    'extern':         re.compile(r'@\[[^\]]*\bextern\b'),
    'axiom':          re.compile(r'^\s*axiom\s', re.M),
}

ALLOW = {
    'Ix/Kernel/Expr.lean':     {'computed_field'},
    'Ix/Kernel/Name.lean':     {'computed_field'},
    'Ix/Kernel/BasisGen.lean': {'unsafe', 'implemented_by'},
    'Ix/Kernel/Exclusive.lean': {'unsafe', 'implemented_by'},
}

# NOT SCANNED: the lexer's own fixture lives outside the scanned tree.
SKIP_DIRS = ()

LEXER_FIXTURE = 'scripts/trust-surface/lexer.lean'

def sources():
    import importlib.util
    sys.dont_write_bytecode = True   # no __pycache__ in the tree
    spec = importlib.util.spec_from_file_location('vendor', 'scripts/vendor-conleche.py')
    vendor = importlib.util.module_from_spec(spec); spec.loader.exec_module(vendor)
    return sorted(rel for rel in vendor.vendored_tree()
                  if not SKIP_DIRS or not rel.startswith(SKIP_DIRS))

# ------------------------------------------------------- the LEXER.
# `code_only` blanks every comment and every string literal, in one
# pass, keeping line AND column structure so reported line numbers and
# the echoed text stay true.  See the header for the forms covered and
# for why the regex it replaced was unsound.

class LexError(Exception):
    pass

# a character that may CONTINUE a Lean identifier — used to tell a
# raw-string prefix `r"` from the `r` that ends `myr`, and a character
# literal `'x'` from the prime in `foo'`.
_IDENT_TAIL = re.compile(r"[0-9A-Za-z_'!?À-￿]")
# `'x'`, `'\n'`, `'\''`, `'"'`, `'\x41'`, `'e'`
_CHARLIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'")
# `r"`, `r#"`, `r##"` ...
_RAWSTR = re.compile(r'r(#*)"')

def code_only(src, path='<input>'):
    out = list(src)
    n = len(src)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '

    def die(pos, msg):
        raise LexError(f'{path}:{src.count(chr(10), 0, pos) + 1}: {msg}')

    def ident_before(i):
        return i > 0 and _IDENT_TAIL.match(src[i - 1]) is not None

    def scan_block_comment(i, limit):
        """i is at `/-`.  Returns the index after the matching `-/`."""
        start, depth = i, 0
        while i < limit:
            if src.startswith('/-', i):
                depth += 1
                blank(i, i + 2); i += 2
            elif src.startswith('-/', i):
                depth -= 1
                blank(i, i + 2); i += 2
                if depth == 0:
                    return i
            else:
                blank(i, i + 1); i += 1
        die(start, 'unterminated block comment')

    def scan_raw_string(m, limit):
        """m matched `_RAWSTR`.  A raw string has no escapes at all; it
        ends at the quote followed by as many `#` as opened it."""
        close = '"' + m.group(1)
        j = src.find(close, m.end(), limit)
        if j < 0:
            die(m.start(), 'unterminated raw string literal')
        end = j + len(close)
        blank(m.start(), end)
        return end

    def scan_string(i, limit):
        """i is just after the opening `"`.  Returns the index after the
        closing `"`.  Blanks the literal text; a `{...}` interpolation
        segment is left as code."""
        start = i
        while i < limit:
            c = src[i]
            if c == '\\':
                if i + 1 >= limit:
                    die(i, 'backslash at end of input inside a string literal')
                if src[i + 1] == '\n':
                    # THE STRING GAP: `\` NEWLINE, then the continuation
                    # line's leading blanks, are not part of the value.
                    j = i + 2
                    while j < limit and src[j] in ' \t':
                        j += 1
                    blank(i, j); i = j
                else:
                    blank(i, i + 2); i += 2
                continue
            if c == '"':
                blank(i, i + 1)
                return i + 1
            if c == '{':
                # An interpolation `{...}`, but only if it closes on this
                # line (see the header); the attempt is speculative.
                eol = src.find('\n', i)
                stop = limit if eol < 0 else min(limit, eol)
                saved = out[i:]
                try:
                    j = scan_code(i + 1, stop, stop_brace=True)
                except LexError:
                    j = stop
                if j < stop and src[j] == '}':
                    blank(i, i + 1); blank(j, j + 1)
                    i = j + 1
                    continue
                out[i:] = saved          # not an interpolation after all
            blank(i, i + 1); i += 1
        die(start, 'unterminated string literal')

    def scan_code(i, limit, stop_brace=False):
        """Scan Lean source, blanking comments and string literals.
        With `stop_brace`, stop at the first unmatched `}` and return
        its index (the code inside a `{...}` interpolation)."""
        depth = 0
        while i < limit:
            c = src[i]
            if c == '/' and src.startswith('/-', i):
                i = scan_block_comment(i, limit)
                continue
            if c == '-' and src.startswith('--', i):
                j = src.find('\n', i)
                if j < 0 or j > limit:
                    j = limit
                blank(i, j); i = j
                continue
            if c == '"':
                blank(i, i + 1)
                i = scan_string(i + 1, limit)
                continue
            if c == 'r' and not ident_before(i):
                m = _RAWSTR.match(src, i, limit)
                if m:
                    i = scan_raw_string(m, limit)
                    continue
            if c == "'" and not ident_before(i):
                m = _CHARLIT.match(src, i, limit)
                if m:
                    blank(i, m.end()); i = m.end()
                    continue
            if stop_brace:
                if c == '{':
                    depth += 1
                elif c == '}':
                    if depth == 0:
                        return i
                    depth -= 1
            i += 1
        return i

    scan_code(0, n)
    return ''.join(out)

def scan_file(rel):
    """The (line, token, text) occurrences the gate sees in one file."""
    with open(rel, encoding='utf-8') as fh:
        raw = fh.read()
    hits = []
    for i, line in enumerate(code_only(raw, rel).split('\n'), 1):
        for tok, rx in TOKENS.items():
            if rx.search(line):
                hits.append((i, tok, line.strip()))
    return hits

# ---------------------------------------------------- the SELF-TEST.
# The fixture names, in trailing `EXPECT:` line-comment markers, exactly
# the lines the gate must report; every other line must stay silent.
_MARKER = re.compile(r'--\s*EXPECT:((?:\s+[A-Za-z_]+)+)\s*$')

def selftest():
    if not os.path.exists(LEXER_FIXTURE):
        print(f'TRUST-SURFACE SELF-TEST FAIL - {LEXER_FIXTURE} is missing')
        return 1
    with open(LEXER_FIXTURE, encoding='utf-8') as fh:
        raw = fh.read()
    want = set()
    for i, line in enumerate(raw.split('\n'), 1):
        m = _MARKER.search(line)
        if m:
            for tok in m.group(1).split():
                want.add((i, tok))
    try:
        got = {(i, tok) for i, tok, _ in scan_file(LEXER_FIXTURE)}
    except LexError as e:
        print(f'TRUST-SURFACE SELF-TEST FAIL - the lexer choked: {e}')
        return 1
    missed = sorted(want - got)
    spurious = sorted(got - want)
    if missed or spurious:
        print('TRUST-SURFACE SELF-TEST FAIL - the lexer does not agree with '
              f'{LEXER_FIXTURE}:')
        for i, tok in missed:
            print(f'    HIDDEN    {LEXER_FIXTURE}:{i} [{tok}] '
                  f'is real code and was not reported')
        for i, tok in spurious:
            print(f'    PHANTOM   {LEXER_FIXTURE}:{i} [{tok}] '
                  f'is comment/string content and was reported')
        return 1
    print(f'self-test: {len(want)} expected occurrences over '
          f'{len(raw.splitlines())} fixture lines, none hidden, none '
          f'phantom ({LEXER_FIXTURE})')
    return 0

if '--selftest' in sys.argv[1:]:
    sys.exit(selftest())
if selftest() != 0:
    sys.exit(1)

occurrences = []          # (file, line, token, text)
try:
    for rel in sources():
        for i, tok, text in scan_file(rel):
            occurrences.append((rel, i, tok, text))
except LexError as e:
    print(f'TRUST-SURFACE FAIL - the source lexer could not finish: {e}')
    print('    An unterminated string or comment means the blanking has')
    print('    desynchronised, so the scan below it would be meaningless.')
    sys.exit(1)

if '--list' in sys.argv[1:]:
    for rel, i, tok, text in occurrences:
        ok = 'ok ' if tok in ALLOW.get(rel, ()) else 'NEW'
        print(f'{ok} {rel}:{i} [{tok}] {text}')
    sys.exit(0)

bad = [o for o in occurrences if o[2] not in ALLOW.get(o[0], ())]

if bad:
    print(f'TRUST-SURFACE FAIL - compiler escapes outside the allowlist '
          f'({len(bad)}):')
    for rel, i, tok, text in bad:
        print(f'    {rel}:{i} [{tok}] {text}')
    print('    Each of these is a TCB entry invisible to `#print axioms`.')
    print('    Remove it, or add it to the allowlist in this script WITH')
    print('    the justification -- the header is the trusted-surface')
    print('    census a reviewer reads.')
    sys.exit(1)

used = {(rel, tok) for rel, _, tok, _ in occurrences}
# Entries for files not ported yet are not stale.
stale = sorted((f, t) for f, ts in ALLOW.items() for t in ts
               if (f, t) not in used and os.path.exists(f))
for f, t in stale:
    print(f'note: allowlist entry {f} [{t}] has no occurrence left '
          f'(it may be dropped)')

files = len({o[0] for o in occurrences})
print(f'trust surface: {len(occurrences)} escapes in {files} allowlisted '
      f'files ({len(sources())} scanned); 0 outside the allowlist')
PYEOF
