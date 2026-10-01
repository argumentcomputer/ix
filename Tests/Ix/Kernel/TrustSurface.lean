import Tests.Ix.Kernel.KernelLayout

/-! # The kernel's trust-surface fence (`kernel-trust-surface`)

Derived from con-leche's `tests/trust-surface.sh` (Apache-2.0), modified; see
`Ix/Kernel/NOTICE`. Its lexer fixture, upstream's
`tests/trust-surface/lexer.lean`, is kept unchanged as
`Tests/Fixtures/trust-surface/lexer.lean` (its text still names upstream's
script). Until 2026-10-01 this was `scripts/trust-surface.sh`, a Python
program in a shell wrapper, as upstream's is.

It scans the checker and the theory under `Ix/Kernel/`
(`Tests.Ix.Kernel.KernelLayout`, whose table `topLevel` must classify every
file under `Ix/Kernel/`) for compiler escapes. Ix's boundary (`Ixon`,
`Audit`, `Ingress`, `Egress`, `Ref`, `Search`) is fenced by Ix's Lean audits
in `Ix/Kernel/Audit/*`, which see compiled code, not tokens; ruled entries
are recorded once more in the Lean runtime audit
(`Ix.Kernel.Audit.runtimeRulings`), which checks the compiled closure.

WHY THIS EXISTS (upstream). The layering fence keeps the implementation
from importing the theory; this gate keeps compiler escapes out of every
file that is not knowingly part of the trusted computing base. The
escapes are invisible to `#print axioms`: a theorem can stand at exactly
`[propext, Classical.choice, Quot.sound]` and still be about a function
whose compiled behaviour was swapped by `@[implemented_by]`, read off a
`@[computed_field]` word, or decided by `native_decide`. An escape is a
TCB entry, admissible only where someone has written down why.

THE BLANKING IS A LEXER, NOT A REGEX (upstream task #224). `codeOnly`
is a one-pass state machine covering line comments, nested block
comments, string literals with every escape including the string gap
(`\` NEWLINE), single-line `{…}` interpolations (left as code), raw
strings, and character literals. An unterminated literal is a hard
error. The fixture exercises every form and names, in trailing `EXPECT:`
markers, exactly the lines the gate must report; `--selftest` runs that
check alone, and every run does it first.

THE ALLOWLIST, and the justification for every entry (file → the tokens
tolerated there). A token in an allowlisted file that is not on its own
list fails just as loudly as one in a bare file.

  Ix/Kernel/Expr.lean          computed_field
      The packed `@[computed_field] data` and `Level.hashData`: the
      user's ruling R-meta ("we trust the compiler"), the same escape
      class `Lean.Expr` lives on. Expression equality is not an escape:
      it goes through `@[csimp]` + `withPtrEq`/`withPtrAddr` with the
      memoised descent proved equal to `decide (a = b)`.

  Ix/Kernel/Name.lean          computed_field
      A cached hash only (`Name.hashData`), as `Lean.Name`'s. Pointer
      equality goes through `@[csimp]` + `withPtrEq` with the redundancy
      proved (`Name.beqPtr_eq`).

  Ix/Kernel/Exclusive.lean     unsafe, implemented_by
      `withExclusive`: defined as `k false` and `@[implemented_by]` the
      compiled `k (isExclusiveUnsafe a)`, the reference-count read the
      substitution memo keys on. The obligation `h : k true = k false`
      licenses the substitution; every use goes through `withExcl`,
      whose continuation returns a `Subsingleton`, so `h` is
      `Subsingleton.elim`. The file's docstring is the justification.

  Ix/Kernel/BasisGen.lean      unsafe, implemented_by
      ELABORATION ONLY. `#annotate_basis` / `#annotate_pins` run the
      annotation pass at elaboration time through `unsafe evalTerm`
      (a `meta section`) and splice the resulting literals. Nothing here
      is in the binary; the literals are ordinary data the proofs consume.

Not policed, as upstream: `partial`, `@[csimp]`, `withPtrEq`/`withPtrAddr`,
`opaque`, `noncomputable`. The Lean runtime audit polices the compiled
form of the first two (`partial` only in `Ix/Kernel/Frontend/InModel*`,
`csimp` only with a theorem on the standard axioms).

Changes from upstream: the scanned files come from the repository's own
layout, and a file under `Ix/Kernel/` that the layout does not classify
fails; the allowlist drops upstream's `Main.lean` and
`ConLeche/Challenge.lean` (not part of this kernel) and names files by
their paths here; an empty `Ix/Kernel/` scans nothing and passes once the
lexer self-test passes; and three patterns are wider than upstream's
regular expressions, so this fence reports everything they do and more: a
token's word boundary is ASCII (a non-ASCII letter next to a token is a
boundary, where Python's Unicode `\b` is not); `extern` counts after any
`[` on its line (`attribute [extern …]` as well as `@[extern …]`); and an
`axiom` declaration counts after declaration modifiers and same-line
attributes and at the end of a line, as well as before a blank at the
start of one.

Usage: `lake exe kernel-trust-surface [--list|--selftest]`, from the
repository root.
  --list      print every scanned occurrence, allowlisted or not.
  --selftest  run only the lexer self-test.
Exit code 0 on success, 1 on a finding or a lexer failure.
-/

namespace Tests.Ix.Kernel.TrustSurface

open Tests.Ix.Kernel.KernelLayout

/-! ## The tokens: each a compiler escape that `#print axioms` cannot see -/

def tokens : List String :=
  ["unsafe", "unsafeCast", "ptrAddrUnsafe", "implemented_by", "computed_field", "native_decide",
   "ofReduceBool", "sorry", "lcProof", "extern", "axiom"]

def allow : List (String × List String) := [
  ("Ix/Kernel/Expr.lean", ["computed_field"]),
  ("Ix/Kernel/Name.lean", ["computed_field"]),
  ("Ix/Kernel/BasisGen.lean", ["unsafe", "implemented_by"]),
  ("Ix/Kernel/Exclusive.lean", ["unsafe", "implemented_by"])]

def allowed (file tok : String) : Bool :=
  ((allow.lookup file).getD []).contains tok

/-- The lexer's own fixture, outside the scanned tree. -/
def lexerFixture : String := "Tests/Fixtures/trust-surface/lexer.lean"

/-! ## The lexer

`codeOnly` blanks every comment and every string literal in one pass,
keeping line and column structure so reported line numbers and the echoed
text stay true. -/

abbrev LexM := StateT (Array Char) (Except String)

structure Lexer where
  src : Array Char
  path : String

namespace Lexer

def size (L : Lexer) : Nat := L.src.size

def at? (L : Lexer) (i : Nat) : Option Char := L.src[i]?

/-- `src[i] = a` and `src[i + 1] = b` (Python's `src.startswith(ab, i)`,
not bounded by a scan limit). -/
def startsAt (L : Lexer) (i : Nat) (a b : Char) : Bool :=
  L.at? i == some a && L.at? (i + 1) == some b

/-- Python's `src.find(c, start)`. -/
def findChar (L : Lexer) (c : Char) (start : Nat) : Option Nat := Id.run do
  let mut j := start
  while j < L.size do
    if L.src[j]! == c then return some j
    j := j + 1
  return none

/-- Python's `src.find(s, start, stop)`: `s` wholly inside `[start, stop)`. -/
def find (L : Lexer) (s : Array Char) (start stop : Nat) : Option Nat := Id.run do
  let mut j := start
  while j + s.size ≤ stop do
    let mut ok := true
    for k in [0:s.size] do
      if ok && L.src[j + k]! != s[k]! then ok := false
    if ok then return some j
    j := j + 1
  return none

def blank (a b : Nat) : LexM Unit :=
  modify fun out => Id.run do
    let mut o := out
    for k in [a:b] do
      if o[k]! != '\n' then o := o.set! k ' '
    return o

def die {α : Type} (L : Lexer) (pos : Nat) (msg : String) : LexM α :=
  let line := ((L.src.extract 0 pos).filter (· == '\n')).size + 1
  throw s!"{L.path}:{line}: {msg}"

/-- A character that may continue a Lean identifier (`[0-9A-Za-z_'!?À-￿]`):
tells a raw-string prefix `r"` from the `r` that ends `myr`, and a
character literal `'x'` from the prime in `foo'`. -/
def identTail (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' ||
  (0xC0 ≤ c.toNat && c.toNat ≤ 0xFFFF)

def identBefore (L : Lexer) (i : Nat) : Bool :=
  i > 0 && identTail L.src[i - 1]!

def isHex (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- `'x'`, `'\n'`, `'\''`, `'"'`, `'\x41'`, `'é'` at `i` (Python's
`'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'` with `endpos`
`limit`): the index after it. -/
def charLit (L : Lexer) (i limit : Nat) : Option Nat :=
  let c (k : Nat) : Option Char := if k < limit then L.at? k else none
  let quoteAt (k : Nat) : Bool := c k == some '\''
  let hexes (k n : Nat) : Bool := (List.range n).all fun d => (c (k + d)).any isHex
  if c i != some '\'' then none
  else match c (i + 1) with
    | some '\\' =>
      if c (i + 2) == some 'x' && hexes (i + 3) 2 && quoteAt (i + 5) then some (i + 6)
      else if c (i + 2) == some 'u' && hexes (i + 3) 4 && quoteAt (i + 7) then some (i + 8)
      else if (c (i + 2)).any (· != '\n') && quoteAt (i + 3) then some (i + 4)
      else none
    | some ch =>
      if ch != '\'' && ch != '\\' && ch != '\n' && quoteAt (i + 2) then some (i + 3) else none
    | none => none

/-- `r"`, `r#"`, `r##"` … at `i`, within `limit`: the closing delimiter and
the index after the opening one. -/
def rawOpen (L : Lexer) (i limit : Nat) : Option (String × Nat) := Id.run do
  if !(i < limit && L.at? i == some 'r') then return none
  let mut k := i + 1
  while k < limit && L.at? k == some '#' do k := k + 1
  if k < limit && L.at? k == some '"' then
    return some ("\"" ++ String.ofList (List.replicate (k - i - 1) '#'), k + 1)
  return none

def blockComment (L : Lexer) (i limit : Nat) : LexM Nat := do
  let start := i
  let mut i := i
  let mut depth := 0
  while i < limit do
    if L.startsAt i '/' '-' then
      depth := depth + 1
      blank i (i + 2); i := i + 2
    else if L.startsAt i '-' '/' then
      depth := depth - 1
      blank i (i + 2); i := i + 2
      if depth == 0 then return i
    else
      blank i (i + 1); i := i + 1
  L.die start "unterminated block comment"

/-- A raw string has no escapes at all; it ends at the quote followed by as
many `#` as opened it. -/
def rawString (L : Lexer) (start : Nat) (close : String) (body limit : Nat) : LexM Nat := do
  let some j := L.find close.toList.toArray body limit | L.die start "unterminated raw string literal"
  let stop := j + close.length
  blank start stop
  return stop

mutual

/-- `i` is just after the opening `"`. Returns the index after the closing
`"`. Blanks the literal text; a `{...}` interpolation segment that closes on
its line is left as code (the attempt is speculative). -/
partial def string (L : Lexer) (i limit : Nat) : LexM Nat := do
  let start := i
  let mut i := i
  while i < limit do
    let c := L.src[i]!
    if c == '\\' then
      if i + 1 ≥ limit then
        L.die i "backslash at end of input inside a string literal"
      if L.src[i + 1]! == '\n' then
        -- THE STRING GAP: `\` NEWLINE, then the continuation line's leading
        -- blanks, are not part of the value.
        let mut j := i + 2
        while j < limit && (L.src[j]! == ' ' || L.src[j]! == '\t') do j := j + 1
        blank i j; i := j
      else
        blank i (i + 2); i := i + 2
      continue
    if c == '"' then
      blank i (i + 1)
      return i + 1
    if c == '{' then
      let eol := L.findChar '\n' i
      let stop := match eol with | some e => min limit e | none => limit
      let saved ← get
      let j ← tryCatch (code L (i + 1) stop true) (fun _ => pure stop)
      if j < stop && L.src[j]! == '}' then
        blank i (i + 1); blank j (j + 1)
        i := j + 1
        continue
      set saved          -- not an interpolation after all
    blank i (i + 1); i := i + 1
  L.die start "unterminated string literal"

/-- Scan Lean source, blanking comments and string literals. With
`stopBrace`, stop at the first unmatched `}` and return its index (the code
inside a `{...}` interpolation). -/
partial def code (L : Lexer) (i limit : Nat) (stopBrace : Bool) : LexM Nat := do
  let mut i := i
  let mut depth := 0
  while i < limit do
    let c := L.src[i]!
    if c == '/' && L.startsAt i '/' '-' then
      i ← blockComment L i limit
      continue
    if c == '-' && L.startsAt i '-' '-' then
      let j := match L.findChar '\n' i with
        | some j => if j > limit then limit else j
        | none => limit
      blank i j; i := j
      continue
    if c == '"' then
      blank i (i + 1)
      i ← string L (i + 1) limit
      continue
    if c == 'r' && !L.identBefore i then
      if let some (close, body) := L.rawOpen i limit then
        i ← rawString L i close body limit
        continue
    if c == '\'' && !L.identBefore i then
      if let some e := L.charLit i limit then
        blank i e; i := e
        continue
    if stopBrace then
      if c == '{' then depth := depth + 1
      else if c == '}' then
        if depth == 0 then return i
        depth := depth - 1
    i := i + 1
  return i

end

end Lexer

/-- The source with every comment and string literal blanked. -/
def codeOnly (src : String) (path : String) : Except String (Array Char) := do
  let chars := src.toList.toArray
  let L : Lexer := { src := chars, path }
  let (_, out) ← (Lexer.code L 0 chars.size false).run chars
  return out

/-! ## The patterns -/

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def wordAt (line : Array Char) (q : Nat) (w : String) : Bool := Id.run do
  let mut k := q
  for c in w.toList do
    if line[k]? != some c then return false
    k := k + 1
  return true

/-- The positions of `w` with an (ASCII) word boundary on both sides. -/
def wordHits (line : Array Char) (w : String) : List Nat := Id.run do
  let len := w.length
  let first := w.front
  let mut hits := []
  for q in [0:line.size] do
    if line[q]! == first && wordAt line q w &&
        (q == 0 || !isWordChar line[q - 1]!) &&
        (q + len == line.size || !(line[q + len]?.any isWordChar)) then
      hits := q :: hits
  return hits.reverse

def hasWord (line : Array Char) (w : String) : Bool := !(wordHits line w).isEmpty

/-- `extern` inside a bracket on its line: after a `[` with no `]` between
(upstream: after `@[`). -/
def externHit (line : Array Char) : Bool :=
  (wordHits line "extern").any fun q =>
    (List.range q).any fun p => line[p]! == '[' && !((line.extract (p + 1) q).contains ']')

/-- An `axiom` declaration: at the start of the line after blanks,
declaration modifiers and `@[…]` attributes, followed by a blank or the end
of the line (upstream: `^\s*axiom\s`). -/
def axiomHit (line : Array Char) : Bool := Id.run do
  let n := line.size
  let mut i := 0
  let skip (i : Nat) : Nat := Id.run do
    let mut j := i
    while j < n && isPySpace line[j]! do j := j + 1
    return j
  i := skip i
  let mut more := true
  while more do
    more := false
    if line[i]? == some '@' && line[i + 1]? == some '[' then
      let mut j := i + 2
      while j < n && line[j]! != ']' do j := j + 1
      if j < n then
        i := skip (j + 1); more := true
    else
      for m in ["private", "protected", "noncomputable", "unsafe", "partial"] do
        if !more && wordAt line i m && (line[i + m.length]?.any isPySpace) then
          i := skip (i + m.length); more := true
  return wordAt line i "axiom" && (i + 5 == n || (line[i + 5]?.any isPySpace))

def tokenHit (line : Array Char) : String → Bool
  | "ofReduceBool" => hasWord line "ofReduceBool" || hasWord line "ofReduceNat"
  | "extern" => externHit line
  | "axiom" => axiomHit line
  | tok => hasWord line tok

/-- The (line, token, text) occurrences the gate sees in one file. -/
def scanFile (rel : String) : IO (Except String (Array (Nat × String × String))) := do
  let raw ← readText rel
  match codeOnly raw rel with
  | .error e => return .error e
  | .ok out =>
    let mut hits := #[]
    let mut lineNo := 1
    for line in (String.ofList out.toList).splitOn "\n" do
      let chars := line.toList.toArray
      for tok in tokens do
        if tokenHit chars tok then
          hits := hits.push (lineNo, tok, pyStrip line.toList)
      lineNo := lineNo + 1
    return .ok hits

/-! ## The self-test

The fixture names, in trailing `EXPECT:` line-comment markers, exactly the
lines the gate must report; every other line must stay silent. -/

/-- The tokens of a marker `--\s*EXPECT:((?:\s+[A-Za-z_]+)+)\s*$` on `line`. -/
def marker (line : List Char) : Option (List String) :=
  let isTok (c : Char) := c.isAlpha || c == '_'
  let rec go : List Char → Option (List String)
    | [] => none
    | '-' :: '-' :: rest =>
      let after := rest.dropWhile isPySpace
      let attempt : Option (List String) :=
        if after.take 7 == "EXPECT:".toList then
          let tail := after.drop 7
          let words := (String.ofList tail).split isPySpace |>.toList.map (·.toString)
            |>.filter (!·.isEmpty)
          if (tail.head?.any isPySpace) && !words.isEmpty &&
              tail.all (fun c => isPySpace c || isTok c) then some words else none
        else none
      match attempt with
      | some ws => some ws
      | none => go ('-' :: rest)
    | _ :: rest => go rest
  go line

/-- Python's `len(text.splitlines())`. -/
def pyLineCount (text : String) : Nat :=
  let seps := ['\n', '\r', '\x0b', '\x0c', '\x1c', '\x1d', '\x1e', '\x85', ' ', ' ']
  let chars := text.toList
  let n := (chars.filter seps.contains).length
  if chars.isEmpty then 0 else if seps.contains chars.getLast! then n else n + 1

def pairLt (a b : Nat × String) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def selftest : IO UInt32 := do
  unless ← System.FilePath.pathExists lexerFixture do
    IO.println s!"TRUST-SURFACE SELF-TEST FAIL - {lexerFixture} is missing"
    return 1
  let raw ← readText lexerFixture
  let mut want : Array (Nat × String) := #[]
  let mut lineNo := 1
  for line in raw.splitOn "\n" do
    if let some toks := marker line.toList then
      for tok in toks do
        unless want.contains (lineNo, tok) do want := want.push (lineNo, tok)
    lineNo := lineNo + 1
  let got ← match ← scanFile lexerFixture with
    | .ok hits => pure (hits.map fun (i, tok, _) => (i, tok))
    | .error e =>
      IO.println s!"TRUST-SURFACE SELF-TEST FAIL - the lexer choked: {e}"
      return 1
  let missed := (want.filter (!got.contains ·)).qsort pairLt
  let spurious := ((got.filter (!want.contains ·)).toList.eraseDups.toArray).qsort pairLt
  if !missed.isEmpty || !spurious.isEmpty then
    IO.println s!"TRUST-SURFACE SELF-TEST FAIL - the lexer does not agree with {lexerFixture}:"
    for (i, tok) in missed do
      IO.println s!"    HIDDEN    {lexerFixture}:{i} [{tok}] is real code and was not reported"
    for (i, tok) in spurious do
      IO.println s!"    PHANTOM   {lexerFixture}:{i} [{tok}] is comment/string content and was reported"
    return 1
  IO.println s!"self-test: {want.size} expected occurrences over {pyLineCount raw} fixture lines, \
    none hidden, none phantom ({lexerFixture})"
  return 0

def run (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  if (← selftest) != 0 then return 1
  let (sources, unclassified) ← covered
  if ← reportUnclassified "TRUST-SURFACE" unclassified then return 1
  let mut occurrences : Array (String × Nat × String × String) := #[]
  for rel in sources do
    match ← scanFile rel with
    | .ok hits => occurrences := occurrences ++ hits.map fun (i, tok, text) => (rel, i, tok, text)
    | .error e =>
      IO.println s!"TRUST-SURFACE FAIL - the source lexer could not finish: {e}"
      IO.println "    An unterminated string or comment means the blanking has"
      IO.println "    desynchronised, so the scan below it would be meaningless."
      return 1
  if args.contains "--list" then
    for (rel, i, tok, text) in occurrences do
      IO.println s!"{if allowed rel tok then "ok " else "NEW"} {rel}:{i} [{tok}] {text}"
    return 0
  let bad := occurrences.filter fun (rel, _, tok, _) => !allowed rel tok
  if !bad.isEmpty then
    IO.println s!"TRUST-SURFACE FAIL - compiler escapes outside the allowlist ({bad.size}):"
    for (rel, i, tok, text) in bad do
      IO.println s!"    {rel}:{i} [{tok}] {text}"
    IO.println "    Each of these is a TCB entry invisible to `#print axioms`."
    IO.println "    Remove it, or add it to the allowlist in Tests/Ix/Kernel/TrustSurface.lean WITH"
    IO.println "    the justification -- the header is the trusted-surface"
    IO.println "    census a reviewer reads."
    return 1
  -- entries for files not ported yet are not stale
  let mut stale : Array (String × String) := #[]
  for (file, toks) in allow do
    for tok in toks do
      if !occurrences.any (fun (rel, _, t, _) => rel == file && t == tok) &&
          (← System.FilePath.pathExists file) then
        stale := stale.push (file, tok)
  for (file, tok) in stale.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) do
    IO.println s!"note: allowlist entry {file} [{tok}] has no occurrence left (it may be dropped)"
  let files := (occurrences.map (·.1)).toList.eraseDups.length
  IO.println s!"trust surface: {occurrences.size} escapes in {files} allowlisted files \
    ({sources.size} scanned); 0 outside the allowlist"
  return 0

end Tests.Ix.Kernel.TrustSurface

def main (args : List String) : IO UInt32 := Tests.Ix.Kernel.TrustSurface.run args
