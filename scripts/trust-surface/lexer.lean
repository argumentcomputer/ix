/-!
# `tests/trust-surface.sh`'s LEXER FIXTURE (task #224)

This file is **not** part of the build (nothing imports it, no
`lean_lib` root reaches it) and it is **not** part of the gate's own
scan: `tests/trust-surface.sh` lists `tests/trust-surface/` in
`SKIP_DIRS`, exactly as it does the e2e fixture sources.  It exists so
that `tests/trust-surface.sh --selftest` can run the scanner over a
file that exercises every Lean literal form and check the answer.

THE BUG IT PINS (found at task #213).  The gate used to strip string
literals with the regex `"(?:\\.|[^"\\])*"`, whose escape class `\\.`
does not match a backslash followed by a NEWLINE — Lean's *string gap*.
A single gap-carrying literal therefore failed to match, quote parity
flipped for the rest of the file, and from there on string CONTENT was
scanned as code (the #213 lane saw its own error message's word
`axiom` reported as a bare `axiom` declaration) while real code was
scanned as string — which is the direction that matters, because an
escape could hide there unseen.

THE CONTRACT.  Every line below that the gate MUST report carries a
trailing line-comment marker `EXPECT:` followed by the token names;
every line without such a marker MUST NOT be reported.  The self-test
asserts equality of the two sets, so this file is its own expected
output.
-/

namespace TrustSurfaceFixture

/- ------------------------------------------------------------------ -/
/- 1. THE STRING GAP.                                                  -/

-- Gap, then the tokens inside string CONTENT: not code, never reported.
def gapContent : String :=
  "this literal mentions implemented_by, unsafe, native_decide and \
   sorry after a gap; it is all string content"

-- A REAL escape sitting after the gap-carrying literal above.  Before
-- the fix the scanner was one quote out of phase here and read the
-- attribute as string content.
@[implemented_by gapContent]                     -- EXPECT: implemented_by
opaque gapThenRealEscape : String

-- A gap in an INTERPOLATED string, with interpolation on both sides.
def interpGap (n : Nat) : String :=
  s!"count {n} — the word unsafe here is content, and so is {n} \
     lcProof after the gap"

@[implemented_by gapContent]                     -- EXPECT: implemented_by
opaque interpThenRealEscape : String

-- A gap whose continuation line begins with the token.
def gapAtLineStart : String :=
  "the next line starts with \
computed_field, still content"

/- ------------------------------------------------------------------ -/
/- 2. ORDINARY ESCAPES, so the gap fix does not break them.            -/

def quoteEscape : String := "a \" that does not end the string: unsafe"
def backslashEscape : String := "trailing backslash \\"
def afterBackslash : String := "extern is content here too"
def hexEscape : String := "\x41é ptrAddrUnsafe is content"

/- ------------------------------------------------------------------ -/
/- 3. INTERPOLATION IS CODE.  A `{…}` segment of a string is Lean       -/
/-    source, so an escape hiding in one must still be reported.        -/

unsafe def hidden (s : String) : String := s        -- EXPECT: unsafe

unsafe def inInterpolation : String :=              -- EXPECT: unsafe
  s!"result: {hidden (unsafeCast ())}"              -- EXPECT: unsafeCast

-- Balanced braces in a PLAIN string are scanned as interpolation too
-- (the form is not lexically distinguishable); harmless, because the
-- scanner only ever reports what it finds.
def plainBraces : String := "a {b} c"

-- An UNBALANCED brace in a plain string must not desynchronise: the
-- scanner falls back to reading it as literal content.
def strayOpenBrace : String := "an unmatched { brace, then unsafe"
def strayCloseBrace : String := "an unmatched } brace, then extern"

/- ------------------------------------------------------------------ -/
/- 4. RAW STRINGS: no escapes at all inside.                           -/

def raw0 : String := r"no escapes: \ and implemented_by are content"
def raw1 : String := r#"a " inside, and unsafe, and \n literal"#
def raw2 : String := r##"a "# inside, and native_decide"##

-- `r` that is only the tail of an identifier is not a raw-string prefix.
def myr : String := "not a raw string: sorry is content"

/- ------------------------------------------------------------------ -/
/- 5. CHARACTER LITERALS.                                              -/

def quoteChar : Char := '"'    -- does not open a string; unsafe is comment
def escChar : Char := '\''
def nlChar : Char := '\n'
def primed' : Char := 'x'
def afterChars : String := "extern is content"

/- ------------------------------------------------------------------ -/
/- 6. COMMENTS, INCLUDING NESTED BLOCK COMMENTS.                       -/

-- A line comment naming implemented_by, unsafe and sorry: not reported.

/- A block comment naming native_decide.
   /- nested, naming lcProof and ofReduceBool -/
   still the outer comment, naming extern. -/

/-- A doc comment naming unsafe and computed_field. -/
def documented : Nat := 0

-- A `--` inside a string is not a comment: the tokens after it on the
-- same line are still string content.
def dashesInString : String := "-- unsafe implemented_by, all content"

-- A `/-` inside a string does not open a block comment either.
def blockOpenInString : String := "/- unsafe, still content"

/- ------------------------------------------------------------------ -/
/- 7. THE REMAINING TOKENS, as real code, after everything above.      -/

axiom fixtureAxiom : Nat                         -- EXPECT: axiom
@[extern "c_symbol"] opaque externalised : Nat   -- EXPECT: extern
example : Nat := by exact 0    -- no native_decide here

def usesSorry : Nat := sorry                     -- EXPECT: sorry

end TrustSurfaceFixture
