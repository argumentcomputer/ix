import Tests.Ix.Kernel.KernelLayout

/-! # The kernel's trust-surface fence (`kernel-trust-surface`)

Derived from con-leche's `tests/trust-surface.sh` (Apache-2.0), modified; see
`IxCK/Kernel/NOTICE`. Its lexer fixture, upstream's
`tests/trust-surface/lexer.lean`, is kept unchanged as
`Tests/Fixtures/trust-surface/lexer.lean` (its text still names upstream's
script). Upstream's is a Python program in a shell wrapper.

It scans the checker and the theory under `IxCK/Kernel/`
(`Tests.Ix.Kernel.KernelLayout`, whose table `topLevel` must classify every
file under `IxCK/Kernel/`) for compiler escapes, and the root library's files
that substitute code in the certified entries' execution (`rootSources`),
and its display modules (`displaySources`: the one display-only
read).
Ix's boundary (`Ixon`,
`Audit`, `Ingress`, `Egress`, `Ref`, `Search`) is fenced by Ix's Lean audits
in `IxCK/Kernel/Audit/*`, which see compiled code, not tokens; ruled entries
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

THE BLANKING IS A LEXER, NOT A REGEX. `codeOnly`
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

  IxCK/Kernel/Expr.lean         computed_field
      The packed `@[computed_field] data`, `Expr.hashW`, `Level.hashData` and
      `Level.hasParamData`: the
      user's ruling R-meta ("we trust the compiler"), the same escape
      class `Lean.Expr` lives on. Expression equality is not an escape:
      it goes through `@[csimp]` + `withPtrEq`/`withPtrAddr` with the
      memoised descent proved equal to `decide (a = b)`.

  IxCK/Kernel/Name.lean         computed_field
      A cached hash only (`Name.hashData`), as `Lean.Name`'s. Pointer
      equality goes through `@[csimp]` + `withPtrEq` with the redundancy
      proved (`Name.beqPtr_eq`).

  IxCK/Kernel/Key.lean          computed_field, ofReduceBool, sorryAx, trustCompiler
      A cached hash only (`Key.hashData`), as `Name`'s: the constant keys
      (input, role and derived) hash in O(1). Pointer equality goes
      through `@[csimp]` + `withPtrEq` with the redundancy proved
      (`Key.beqPtr_eq`).
      NAMES ONLY: `ofReduceBool`, `ofReduceNat`, `sorryAx`, and
      `trustCompiler` are constructors of `Role`, the roles of Lean's
      non-standard/compiler-trust axioms, with their Lean names
      (`Role.leanName`). A binding names them so that it can bind them as
      inert axioms (`Role.inert`): the kernel declines their declarations
      (non-standard axioms), IxVM refuses each as a claim's seed and
      refuses every use, and nothing here evaluates natively.

  IxCK/Kernel/Roles.lean        ofReduceBool, sorryAx, trustCompiler
      NAMES ONLY, the same `Role` constructors: their specification
      (`Role.spec`, an axiom of the stated type), the roles their types
      mention (`Role.deps`), `installAnchors`, and `Role.inert`, which
      marks them inert.

  IxCK/Kernel/Basis/Names.lean  sorryAx
      NAME ONLY: `sorryAxName := roleKey .sorryAx` names the `Role.sorryAx`
      key.

  IxCK/Kernel/Cached/ParsedC.lean trustCompiler
      NAME ONLY: checks `cv.name = roleKey .trustCompiler` in the inert
      compiler-trust axiom declaration branch (`checkDeclC`), installing
      nothing so any use declines.

  IxCK/Kernel/Cached/Policy.lean sorryAx, trustCompiler
      NAME ONLY: looks up `Role.sorryAx` in the user-axiom policy filter and
      checks `cv.name = roleKey .trustCompiler` in the inert compiler-trust
      axiom declaration branch (`checkStdAxiomDeclC`), installing nothing.

  IxCK/Kernel/Checker.lean      trustCompiler
      NAME ONLY: checks `cv.name = roleKey .trustCompiler` in the inert
      compiler-trust axiom declaration branch (`checkDecl`), installing
      nothing so any use declines.

  IxCK/Kernel/Semantics/Bridge/DeclRun.lean trustCompiler
      NAME ONLY: case-splits on `cv.name = roleKey .trustCompiler` in the
      soundness proof of `checkDecl`'s inert compiler-trust branch.

  IxCK/Kernel/Verify/BridgeDecl.lean trustCompiler
      NAME ONLY: case-splits on `cv.name = roleKey .trustCompiler` in the
      fuel-bridge proof for `checkDecl`'s inert compiler-trust branch.

  IxCK/Kernel/Verify/Cached/BridgeC.lean trustCompiler
      NAME ONLY: case-splits on `cv.name = roleKey .trustCompiler` in the
      simulation proof of `checkDeclC`'s inert compiler-trust branch.

  IxCK/Kernel/Admission.lean    sorryAx
      NAME ONLY: lists `Role.sorryAx` in `userAxiomRoles`.

  IxCK/Kernel/Exclusive.lean    unsafe, implemented_by
      `withExclusive`: defined as `k false` and `@[implemented_by]` the
      compiled `k (isExclusiveUnsafe a)`, the reference-count read the
      substitution memo keys on. The obligation `h : k true = k false`
      licenses the substitution; every use goes through `withExcl`,
      whose continuation returns a `Subsingleton`, so `h` is
      `Subsingleton.elim`. The file's docstring is the justification.

  IxCK/Kernel/BasisGen.lean     unsafe, implemented_by, addDecl
      ELABORATION ONLY. `#annotate_basis` / `#annotate_pins` run the
      annotation pass at elaboration time through `unsafe evalTerm`
      (a `meta section`) and splice the resulting literals. Nothing here
      is in the binary; the literals are ordinary data the proofs consume.
      The generated declarations are installed by `Lean.addDecl`, which
      runs Lean's kernel on them (unless `debug.skipKernelTC` is set, which
      the kernel-bypass scan forbids in every certified library).

  IxCK/Kernel/Audit/Axioms.lean sorryAx
      NAME ONLY: checks whether a declaration's dependency graph contains
      Lean's `sorryAx` constant in the axiom audit engine.

  IxCK/Kernel/Audit/ClosureManifest.lean unsafe
      NAME ONLY: matches `Lean.DefinitionSafety.unsafe` when hashing a
      definition's safety tag into the SHA-256 closure manifest.

  IxCK/Kernel/Audit/Roots.lean  ptrAddrUnsafe
      NAME ONLY: enumerates Lean's audited runtime primitives
      (`withPtrAddrUnsafe`, `ptrEq`, `ptrAddrUnsafe`, `isExclusiveUnsafe`) in
      `runtimeRulings`.

  IxCK/Kernel/Audit/Runtime.lean unsafe, implemented_by, computed_field, extern, csimp
      AUDIT ENGINE & NEGATIVE CONTROLS: `Finding.unsafe` constructor and
      elaboration-time `RuntimeControls` negative-control fixtures verifying
      `checkRuntimeWith` rejects unruled escapes (their csimps included).

  csimp in IxCK/Kernel/{Expr,Name,Key,Cached/CoreC,Cached/StateC,Canon,Core,
  CoreDefs,DeclCheck,ExprOps,FEnv,Inductives/NativeInstall,Inductives/Scope,
  Inductives/StructParts,Level,StdAxioms,Units}.lean, IxCK/Ixon/Codec.lean and
  Ix/Cert/Compile.lean
      PROVED REPLACEMENTS: each `@[csimp] theorem f_eq : @f = @g` runs a
      faster `g` for the checker's (or the certified compile's) `f`, with
      the equation proved. The runtime audit admits a project csimp only
      from the ruled modules (`csimpModules`: `IxCK.Kernel` and
      `IxCK.Ixon.Codec` for the checker, `Ix` for `Ix.Cert.compile`,
      `Ix/Cert/RuntimeAudit.lean`) and only on the standard axioms, a test a
      theorem that never reached the kernel also passes; the full-closure
      kernel replay re-checks every one of these theorems.

  Ix/Cert/Compile.lean          ofReduceBool, sorryAx, trustCompiler, csimp
      NAME ONLY: matches `Ix.Kernel.Role.ofReduceBool` / `.ofReduceNat` /
      `.sorryAx` / `.trustCompiler` when classifying axiom roles in
      `roleRecordKind`.

  Ix/Cert/LayoutExtra.lean      sorryAx
      NAME ONLY: proof referencing the `Role.sorryAx` entry in a table of
      role kinds.

  Ix/Address/Admission.lean     implemented_by
      The admission hash: `Address.admissionHash` is defined as pure
      BLAKE3 (`Address.blake3Pure`), which every theorem about the
      authenticated entries (`Ixon.Authenticated`) is stated at, and
      `@[implemented_by]` the Rust BLAKE3 `Address.blake3`. Unlike the
      entries above, no obligation proves the substitution: the owner
      approved it (2026-10-13) on the explicit assumption that the two
      agree on every input, which `Tests.Ix.Kernel.AddressPure` checks on
      fixture inputs. It is the one such assumption; the runtime audit
      admits it by name only for the authenticated entries
      (`Ix.Kernel.Audit.assumedSubstitutions`). The file's docstring is
      the justification.

  Ix/KernelDisplay/Peek.lean    unsafe, unsafeCast
      DISPLAY ONLY; OUTSIDE THE CERTIFIED CLOSURE; `.meta` NEVER DECIDES.
      A binder's or a let's Lean name, and a
      failure's terms and binders, are display annotations held in a
      `Squash`, a subsingleton, so no statement, equation or decision of the
      checker sees them; the same property hides their value from safe code.
      `peekSquash` reads one (`unsafeCast`, a `Squash` is its value at run
      time) to print it, and `peekAll` hands it to the safe renderer
      (`Ix.KernelDisplay.Render`). No certified root's compiled closure
      reaches it (`IxCK/Kernel/Audit/Roots.lean`, `Ix/Cert/RuntimeAudit.lean`),
      and the `.meta` and `.source` verdicts are `.anon`'s (the erasure test).
      The file is scanned with the display modules (`displaySources`), which
      hold no other escape.

Not policed, as upstream: `partial`, `withPtrEq`/`withPtrAddr`, `opaque`,
`noncomputable`. The Lean runtime audit polices the compiled form of
`partial` (no `partial` definition at all) and of `@[csimp]` (only with a
theorem on the standard axioms).

Added here (not upstream):
- `csimp` in attribute position (inside `[…]`, as `extern`). The runtime
  audit's test is also passed by a csimp theorem that never reached the
  kernel, and an unchecked `@f = @g` swaps the executed code while every
  proof about `f` still stands. The full-closure kernel replay (`lake run
  check-kernel-replay`, `Scripts/KernelReplay.lean`) re-checks every such
  theorem; each file that declares one is allowlisted for `csimp` above, so
  a new one in another file is seen.
- `addDecl`, `addDeclCore`, `addDeclWithoutChecking`, `setEnv`, `modifyEnv`
  and `skipKernelTC`: the ways a metaprogram installs a declaration, checked
  or not.
- The kernel-bypass scan (`bypassTokens`): `skipKernelTC` and
  `addDeclWithoutChecking` anywhere in the text of every certified library
  (`bypassDirs`, `bypassRootFiles`) and lakefile, comments included, with no
  allowlist.

Changes from upstream: the scanned files come from the repository's own
layout, and a file under `IxCK/Kernel/` that the layout does not classify
fails; the allowlist drops upstream's `Main.lean` and
`ConLeche/Challenge.lean` (not part of this kernel) and names files by
their paths here; an empty `IxCK/Kernel/` scans nothing and passes once the
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
   "bv_decide", "ofReduceBool", "sorry", "sorryAx", "trustCompiler", "lcProof", "extern", "axiom",
   "skipKernelTC", "addDecl", "addDeclCore", "addDeclWithoutChecking", "setEnv", "modifyEnv",
   "csimp"]

/-- The kernel-bypass tokens: each names a way to put a declaration into an
environment without the kernel checking it (`debug.skipKernelTC`, which
`Lean.addDecl` obeys, and `addDeclWithoutChecking`). Searched for, as words in
the raw text, with no allowlist, in every certified library (`bypassDirs`,
`bypassRootFiles`) and the lakefiles (`bypassLakefiles`, where `leanOptions`
or `moreLeanArgs` could set the option for a whole package). The test fixtures that need ill-typed
declarations (`Tests/`, `Benchmarks/`) are not scanned. The full-closure kernel
replay (`Scripts/KernelReplay.lean`) is what detects such a declaration in an
`.olean`; this scan names the source line. -/
def bypassTokens : List String := ["skipKernelTC", "addDeclWithoutChecking"]

/-- The certified libraries the kernel-bypass scan covers. -/
def bypassDirs : Array System.FilePath :=
  #["IxCK", "Ix", "IxVMRefinement", "IxSharingVerify", "Aiur/Aiur", "IxVM/IxVM",
    "MultiStark/MultiStark", "Models/SetTheory/IxSetTheoryModel"]

/-- Library root files the kernel-bypass scan covers besides `bypassDirs`. -/
def bypassRootFiles : Array String :=
  #["Ix.lean", "IxSharingVerify.lean", "FormalAiurKeys.lean", "FormalCodegen.lean",
    "Aiur/Aiur.lean", "IxVM/IxVM.lean", "MultiStark/MultiStark.lean",
    "Models/SetTheory/IxSetTheoryModel.lean"]

/-- Every workspace's lakefile: an option set there applies to a whole package.
These are searched as plain text (a TOML file is not Lean). -/
def bypassLakefiles : Array String :=
  #["lakefile.lean", "IxCK/lakefile.lean", "Aiur/lakefile.lean", "IxVM/lakefile.lean",
    "MultiStark/lakefile.lean", "Models/SetTheory/lakefile.toml"]

def allow : List (String × List String) := [
  ("IxCK/Kernel/Expr.lean", ["computed_field", "csimp"]),
  ("IxCK/Kernel/Name.lean", ["computed_field", "csimp"]),
  ("IxCK/Kernel/Key.lean", ["computed_field", "ofReduceBool", "sorryAx", "trustCompiler", "csimp"]),
  ("IxCK/Kernel/Cached/CoreC.lean", ["csimp"]),
  ("IxCK/Kernel/Cached/StateC.lean", ["csimp"]),
  ("IxCK/Kernel/Canon.lean", ["csimp"]),
  ("IxCK/Kernel/Core.lean", ["csimp"]),
  ("IxCK/Kernel/CoreDefs.lean", ["csimp"]),
  ("IxCK/Kernel/DeclCheck.lean", ["csimp"]),
  ("IxCK/Kernel/ExprOps.lean", ["csimp"]),
  ("IxCK/Kernel/FEnv.lean", ["csimp"]),
  ("IxCK/Kernel/Inductives/NativeInstall.lean", ["csimp"]),
  ("IxCK/Kernel/Inductives/Scope.lean", ["csimp"]),
  ("IxCK/Kernel/Inductives/StructParts.lean", ["csimp"]),
  ("IxCK/Kernel/Level.lean", ["csimp"]),
  ("IxCK/Kernel/StdAxioms.lean", ["csimp"]),
  ("IxCK/Kernel/Units.lean", ["csimp"]),
  ("IxCK/Ixon/Codec.lean", ["csimp"]),
  ("IxCK/Kernel/Roles.lean", ["ofReduceBool", "sorryAx", "trustCompiler"]),
  ("IxCK/Kernel/Basis/Names.lean", ["sorryAx"]),
  ("IxCK/Kernel/Cached/ParsedC.lean", ["trustCompiler"]),
  ("IxCK/Kernel/Cached/Policy.lean", ["sorryAx", "trustCompiler"]),
  ("IxCK/Kernel/Checker.lean", ["trustCompiler"]),
  ("IxCK/Kernel/Semantics/Bridge/DeclRun.lean", ["trustCompiler"]),
  ("IxCK/Kernel/Verify/BridgeDecl.lean", ["trustCompiler"]),
  ("IxCK/Kernel/Verify/Cached/BridgeC.lean", ["trustCompiler"]),
  ("IxCK/Kernel/Admission.lean", ["sorryAx"]),
  ("IxCK/Kernel/BasisGen.lean", ["unsafe", "implemented_by", "addDecl"]),
  ("IxCK/Kernel/Exclusive.lean", ["unsafe", "implemented_by"]),
  ("IxCK/Kernel/Audit/Axioms.lean", ["sorryAx"]),
  ("IxCK/Kernel/Audit/ClosureManifest.lean", ["unsafe"]),
  ("IxCK/Kernel/Audit/Roots.lean", ["ptrAddrUnsafe"]),
  ("IxCK/Kernel/Audit/Runtime.lean", ["unsafe", "implemented_by", "computed_field", "extern", "csimp"]),
  ("Ix/Cert/Compile.lean", ["ofReduceBool", "sorryAx", "trustCompiler", "csimp"]),
  ("Ix/Cert/LayoutExtra.lean", ["sorryAx"]),
  ("Ix/Address/Admission.lean", ["implemented_by"]),
  ("Ix/KernelDisplay/Peek.lean", ["unsafe", "unsafeCast"])]

/-- Additional certified-boundary directories scanned for lexical compiler
escapes so inlined `@[implemented_by]` or `bv_decide` cannot hide outside the
core checker/theory fence. -/
def boundaryDirs : Array System.FilePath :=
  #["IxCK/Ixon", "Ix/Ixon/Authenticated", "Ix/HostAdmission", "Ix/Cert"]

/-- Root-library files in the certified entries' execution that substitute
code: the admission hash, which the authenticated entries run. -/
def rootSources : Array String := #["Ix/Address/Admission.lean"]

/-- The root library's display modules: the renderer, the `.meta`
name pass, the Source names and the one display-only read. -/
def displaySources : Array String :=
  #["Ix/KernelDisplay/MetaNames.lean", "Ix/KernelDisplay/Peek.lean",
    "Ix/KernelDisplay/Render.lean", "Ix/LeanIngress/Names.lean"]

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

/-- Whether the opening `"` at `pos` is immediately preceded (ignoring whitespace
and already-blanked comments) by `'!'`, as in `s!"..."`, `s! "..."`, `m!"..."`,
or `f!"..."`. -/
def precededByBang (out : Array Char) (pos : Nat) : Bool := Id.run do
  let mut k := pos
  while k > 0 do
    k := k - 1
    let ch := out[k]!
    if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' then
      continue
    return ch == '!'
  return false

mutual

/-- `i` is just after the opening `"`. Returns the index after the closing
`"`. Blanks the literal text; in an interpolated string (`isInterp = true`,
e.g. `s!"..."` or `s! "..."`), `{...}` interpolations may span multiple lines
and are left as code; in a plain string, single-line `{...}` is still checked
speculatively so unmatched braces never desynchronise across lines. -/
partial def string (L : Lexer) (i limit : Nat) (isInterp : Bool) : LexM Nat := do
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
      let stop := if isInterp then limit else
        match L.findChar '\n' i with | some e => min limit e | none => limit
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
      let isInterp := precededByBang (← get) i
      blank i (i + 1)
      i ← string L (i + 1) limit isInterp
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

/-- Line numbers where word-bounded `w` occurs inside `[...]` brackets
across the full comment/string-blanked source (covering single-line and
multi-line `@[\n extern "sym"\n]` and `attribute [\n extern "sym"\n]`):
the attribute position of `extern` and `csimp`. -/
def bracketHitLines (out : Array Char) (w : String) : Array Nat := Id.run do
  let n := out.size
  let mut lineNo := 1
  let mut bracketDepth : Nat := 0
  let mut lines : Array Nat := #[]
  for q in [0:n] do
    let c := out[q]!
    if c == '\n' then
      lineNo := lineNo + 1
    else if c == '[' then
      bracketDepth := bracketDepth + 1
    else if c == ']' then
      if bracketDepth > 0 then bracketDepth := bracketDepth - 1
    else if bracketDepth > 0 && c == w.front && wordAt out q w &&
        (q == 0 || !isWordChar out[q - 1]!) &&
        (q + w.length == n || !(out[q + w.length]?.any isWordChar)) then
      unless lines.contains lineNo do
        lines := lines.push lineNo
  return lines

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
      for m in ["public", "private", "protected", "noncomputable", "unsafe", "partial", "meta", "scoped", "local"] do
        if !more && wordAt line i m && (line[i + m.length]?.any isPySpace) then
          i := skip (i + m.length); more := true
  return wordAt line i "axiom" && (i + 5 == n || (line[i + 5]?.any isPySpace))

def externHitLines (out : Array Char) : Array Nat := bracketHitLines out "extern"

def tokenHit (externLines csimpLines : Array Nat) (lineNo : Nat) (line : Array Char) :
    String → Bool
  | "ofReduceBool" => hasWord line "ofReduceBool" || hasWord line "ofReduceNat"
  | "extern" => externLines.contains lineNo
  | "csimp" => csimpLines.contains lineNo
  | "axiom" => axiomHit line
  | tok => hasWord line tok

/-- Scan raw Lean source text for compiler-escape occurrences. -/
def scanSource (raw : String) (path : String) : Except String (Array (Nat × String × String)) := do
  let out ← codeOnly raw path
  let externLines := externHitLines out
  let csimpLines := bracketHitLines out "csimp"
  let mut hits := #[]
  let mut lineNo := 1
  for line in (String.ofList out.toList).splitOn "\n" do
    let chars := line.toList.toArray
    for tok in tokens do
      if tokenHit externLines csimpLines lineNo chars tok then
        hits := hits.push (lineNo, tok, pyStrip line.toList)
    lineNo := lineNo + 1
  return hits

/-- The (line, token, text) occurrences the gate sees in one file. -/
def scanFile (rel : String) : IO (Except String (Array (Nat × String × String))) := do
  let raw ← readText rel
  return scanSource raw rel

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

/-- Inline regression self-tests covering modifier-prefixed `axiom`, multi-line
`@[extern]`, multi-line `s!"{...}"` interpolation, and `sorryAx`/`trustCompiler`. -/
def extraSelftests : Except String Unit := do
  let cases : List (String × String × Array (Nat × String)) := [
    ("public axiom", "public axiom pwn : False\n", #[(1, "axiom")]),
    ("meta axiom", "meta axiom pwn : False\n", #[(1, "axiom")]),
    ("scoped axiom", "scoped axiom pwn : False\n", #[(1, "axiom")]),
    ("local axiom", "local axiom pwn : False\n", #[(1, "axiom")]),
    ("multiline extern", "@[\n  extern \"sym\"\n]\nopaque f : Nat\n", #[(2, "extern")]),
    ("benign extern ident", "def extern : Nat := 0\n", #[]),
    ("multiline s! interp", "def f := s!\"{\n  unsafeCast 0\n}\"\n", #[(2, "unsafeCast")]),
    ("multiline s! spaced interp", "def f := s! \"{\n  unsafeCast 0\n}\"\n", #[(2, "unsafeCast")]),
    ("sorryAx token", "def f := sorryAx\n", #[(1, "sorryAx")]),
    ("trustCompiler token", "def f := Lean.trustCompiler\n", #[(1, "trustCompiler")]),
    ("csimp attribute", "@[csimp] theorem f_eq : @f = @g := rfl\n", #[(1, "csimp")]),
    ("csimp attribute command", "attribute [inline, csimp] f_eq\n", #[(1, "csimp")]),
    ("multiline csimp", "@[\n  csimp\n]\ntheorem f_eq : @f = @g := rfl\n", #[(2, "csimp")]),
    ("benign csimp ident", "def csimp : Nat := 0\n", #[]),
    ("skipKernelTC option", "set_option debug.skipKernelTC true in\n", #[(1, "skipKernelTC")]),
    ("skipKernelTC withOptions",
      "run_meta withOptions (debug.skipKernelTC.set · true) (addDecl d)\n",
      #[(1, "skipKernelTC"), (1, "addDecl")]),
    ("addDeclWithoutChecking", "def f := env.addDeclWithoutChecking d\n",
      #[(1, "addDeclWithoutChecking")]),
    ("addDeclCore", "def f := env.addDeclCore 0 d none\n", #[(1, "addDeclCore")]),
    ("setEnv and modifyEnv", "def f := do setEnv e; modifyEnv id\n",
      #[(1, "setEnv"), (1, "modifyEnv")]),
    ("bypass in comment", "-- debug.skipKernelTC addDeclWithoutChecking\n", #[])
  ]
  for (label, src, want) in cases do
    let hits ← scanSource src s!"<selftest:{label}>"
    let got := (hits.map fun (l, tok, _) => (l, tok)).qsort pairLt
    let wantSorted := want.qsort pairLt
    if got != wantSorted then
      throw s!"{label}: expected {wantSorted.toList}, got {got.toList}"

/-! ## The kernel-bypass scan -/

/-- Every `.lean` file under `dir`, recursively, skipping `.lake` directories,
sorted by code point. -/
def leanFilesOutsideLake (dir : System.FilePath) : IO (Array String) := do
  unless ← dir.isDir do return #[]
  let mut files := #[]
  for path in ← dir.walkDir (fun d => return d.fileName != some ".lake") do
    if (path.fileName.getD "").endsWith ".lean" && !(← path.isDir) then
      files := files.push path.toString
  return files.qsort (· < ·)

/-- The lines of `text` holding a `bypassTokens` word, as (line, token, text). -/
def bypassHits (text : String) : Array (Nat × String × String) := Id.run do
  let mut hits := #[]
  let mut lineNo := 1
  for line in text.splitOn "\n" do
    let chars := line.toList.toArray
    for tok in bypassTokens do
      if hasWord chars tok then hits := hits.push (lineNo, tok, pyStrip line.toList)
    lineNo := lineNo + 1
  return hits

/-- The kernel-bypass occurrences in the certified libraries and the lakefiles,
as (file, line, token, text), and the number of files read. The text is searched
as it is, comments and strings included: the lexer is not run over the ~100 MB
of the libraries, and a mention in a comment fails too (rephrase it). -/
def bypassScan : IO (Array (String × Nat × String × String) × Nat) := do
  let mut files : Array String := #[]
  for d in bypassDirs do files := files ++ (← leanFilesOutsideLake d)
  for f in bypassRootFiles ++ bypassLakefiles do
    if ← System.FilePath.pathExists f then files := files.push f
  let mut hits := #[]
  for rel in files do
    let src ← IO.FS.readFile rel
    unless bypassTokens.any (fun tok => (src.splitOn tok).length > 1) do continue
    hits := hits ++ (bypassHits (← readText rel)).map fun (i, t, x) => (rel, i, t, x)
  return (hits, files.size)

def selftest : IO UInt32 := do
  if let .error e := extraSelftests then
    IO.println s!"TRUST-SURFACE SELF-TEST FAIL - regression case failed: {e}"
    return 1
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
  let (kernelCore, unclassified) ← covered
  if ← reportUnclassified "TRUST-SURFACE" unclassified then return 1
  let allKernel ← leanFilesUnder "IxCK/Kernel"
  let kernelIx := allKernel.filter (fun f => part? f == some .ix)
  let mut boundarySources : Array String := #[]
  for dir in boundaryDirs do
    boundarySources := boundarySources ++ (← leanFilesUnder dir)
  for rel in rootSources ++ displaySources do
    unless ← System.FilePath.pathExists rel do
      IO.println s!"TRUST-SURFACE FAIL - a root source is missing: {rel}"
      return 1
  let sources := kernelCore ++ kernelIx ++ boundarySources ++ rootSources ++ displaySources
  let mut occurrences : Array (String × Nat × String × String) := #[]
  for rel in sources do
    match ← scanFile rel with
    | .ok hits => occurrences := occurrences ++ hits.map fun (i, tok, text) => (rel, i, tok, text)
    | .error e =>
      IO.println s!"TRUST-SURFACE FAIL - the source lexer could not finish: {e}"
      IO.println "    An unterminated string or comment means the blanking has"
      IO.println "    desynchronised, so the scan below it would be meaningless."
      return 1
  let (bypass, bypassFiles) ← bypassScan
  if args.contains "--list" then
    for (rel, i, tok, text) in occurrences do
      IO.println s!"{if allowed rel tok then "ok " else "NEW"} {rel}:{i} [{tok}] {text}"
    for (rel, i, tok, text) in bypass do
      IO.println s!"BYPASS {rel}:{i} [{tok}] {text}"
    return 0
  if !bypass.isEmpty then
    IO.println s!"TRUST-SURFACE FAIL - kernel-bypass tokens in the certified libraries \
      ({bypass.size}):"
    for (rel, i, tok, text) in bypass do
      IO.println s!"    {rel}:{i} [{tok}] {text}"
    IO.println "    Each of these can add a declaration the kernel never checked. They have no"
    IO.println "    allowlist: fixtures that need ill-typed declarations belong under Tests/,"
    IO.println "    and a comment that names one must be rephrased (the text is searched as is)."
    return 1
  let bad := occurrences.filter fun (rel, _, tok, _) => !allowed rel tok
  if !bad.isEmpty then
    IO.println s!"TRUST-SURFACE FAIL - compiler escapes outside the allowlist ({bad.size}):"
    for (rel, i, tok, text) in bad do
      IO.println s!"    {rel}:{i} [{tok}] {text}"
    IO.println "    Each of these is a TCB entry invisible to `#print axioms`."
    IO.println "    Remove it, or add it to the allowlist in Tests/Ix/Kernel/TrustSurface.lean WITH"
    IO.println "    the justification -- the header is the trusted-surface"
    IO.println "    audit census."
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
  IO.println s!"kernel bypass: {bypassFiles} files of the certified libraries and lakefiles \
    scanned for {bypassTokens}; none found"
  return 0

end Tests.Ix.Kernel.TrustSurface

def main (args : List String) : IO UInt32 := Tests.Ix.Kernel.TrustSurface.run args
