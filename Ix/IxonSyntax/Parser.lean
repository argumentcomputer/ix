/-
  Recursive-descent parser for the Ixon text format.

  Behavioral mirror of `crates/ixon/src/syntax/parse.rs`: same grammar,
  same reserved words, same error kinds/messages/positions, same
  metering semantics. Structure differs (handwritten descent here, nom
  there) — parity is enforced by the shared corpus, not structurally.

  Representation: the source is decoded once into a char array with a
  parallel cumulative byte-offset table. Parsing walks char indices;
  all emitted spans and error positions are byte offsets, matching the
  Rust implementation exactly.

  Whitespace is exactly `{' ', '\t', '\r', '\n'}` — an explicit set,
  not a Unicode class (Unicode whitespace drifts by version; both
  implementations use this list).
-/
module

public import Ix.IxonSyntax.AST
public import Ix.IxonSyntax.Error

public section

namespace Ixon.Syntax
namespace Parser

/-- Reserved words: rejected as bare name components everywhere
    (escape as `«def»`). Every declaration-STARTING word must be
    reserved — otherwise a preceding declaration's final term absorbs
    it as an application argument in multi-decl files. Mirrors Rust
    `RESERVED`. -/
def RESERVED : List String :=
  [ "import", "def", "theorem", "opaque", "axiom", "quot", "inductive",
    "recursor", "mutual", "end", "unsafe", "partial", "fun", "let",
    "have", "where", "proj", "Prop", "Type", "Sort", "dprj", "iprj",
    "cprj", "rprj" ]

def isReserved (s : String) : Bool := RESERVED.contains s

/-- Lean's `isLetterLike` ranges (self-contained; parity-locked with
    the Rust port, cross-checked against core in M4). -/
def isLetterLike (c : Char) : Bool :=
  let v := c.val
  (0x3b1 ≤ v && v ≤ 0x3c9 && v != 0x3bb)                    -- greek lower (no λ)
  || (0x391 ≤ v && v ≤ 0x3a9 && v != 0x3a0 && v != 0x3a3)   -- greek upper (no Π Σ)
  || (0x3ca ≤ v && v ≤ 0x3fb)                               -- accented greek
  || (0x1f00 ≤ v && v ≤ 0x1ffe)                             -- polytonic greek
  || (0x2100 ≤ v && v ≤ 0x214f)                             -- letterlike symbols
  || (0x1d49c ≤ v && v ≤ 0x1d59f)                           -- script/fraktur/etc.

def isSubScript (c : Char) : Bool :=
  let v := c.val
  (0x2080 ≤ v && v ≤ 0x209c) || (0x1d62 ≤ v && v ≤ 0x1d6a) || v == 0x2c7c

def isIdFirst (c : Char) : Bool :=
  c.isAlpha || c == '_' || isLetterLike c

def isIdRest (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'
  || isSubScript c || isLetterLike c

/-- The whitespace set (explicit; see module docstring). -/
def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- Parser context: decoded chars plus cumulative byte offsets
    (`byteOff[i]` = byte offset of `chars[i]`; `byteOff[chars.size]` =
    total byte size). -/
structure Ctx where
  chars : Array Char
  byteOff : Array Nat
  limits : Limits

def Ctx.ofString (src : String) (limits : Limits) : Ctx := Id.run do
  let chars := src.toList.toArray
  let mut byteOff := Array.mkEmpty (chars.size + 1)
  let mut o := 0
  for c in chars do
    byteOff := byteOff.push o
    o := o + c.utf8Size
  byteOff := byteOff.push o
  return { chars, byteOff, limits }

/-- Internal parse error. `pos` is a CHAR index (converted to bytes at
    the boundary); `special` carries structured kinds with byte spans;
    `fatal` mirrors Rust's committed `Failure`. -/
structure PErr where
  pos : Nat := 0
  expected : String := ""
  special : Option (ErrorKind × Span) := none
  fatal : Bool := false
  deriving Inhabited

structure St where
  idx : Nat := 0
  depth : Nat := 0
  deriving Inhabited

abbrev M := ReaderT Ctx (EStateM PErr St)

instance : Inhabited (M α) := ⟨fun _ s => .error default s⟩

/-- Byte offset of char index `i`. -/
def off (i : Nat) : M Nat := do
  let ctx ← read
  return ctx.byteOff[min i (ctx.byteOff.size - 1)]!

def sp (fromIdx toIdx : Nat) : M Span := do
  return ⟨← off fromIdx, ← off toIdx⟩

def curIdx : M Nat := do return (← get).idx

def setIdx (i : Nat) : M Unit := modify fun s => { s with idx := i }

def peekAt (i : Nat) : M (Option Char) := do
  return (← read).chars[i]?

def peek : M (Option Char) := do peekAt (← get).idx

/-- Backtrackable expectation failure at char index `i`. -/
def failExp (i : Nat) (what : String) : M α :=
  throw { pos := i, expected := what }

/-- Committed structured failure. -/
def failFatal (kind : ErrorKind) (span : Span) : M α :=
  throw { pos := 0, special := some (kind, span), fatal := true }

/-- Convert backtrackable errors into committed ones (Rust `cut`). -/
def cut (p : M α) : M α :=
  tryCatch p fun e => throw { e with fatal := true }

/-- Run `p`; on a backtrackable error restore state and return `none`
    (fatal errors propagate). The workhorse mirroring Rust's
    `Err(Error) => fallback`. -/
def attempt? (p : M α) : M (Option α) := do
  let st ← get
  tryCatch (some <$> p) fun e => do
    if e.fatal then throw e
    set st
    return none

/-- Depth guard . -/
def withDepth (p : M α) : M α := do
  let ctx ← read
  let st ← get
  if st.depth ≥ ctx.limits.maxDepth then
    let o ← off st.idx
    failFatal (.capExceeded .depth ctx.limits.maxDepth) ⟨o, o⟩
  else
    modify fun s => { s with depth := s.depth + 1 }
    tryCatch
      (do
        let a ← p
        modify fun s => { s with depth := s.depth - 1 }
        return a)
      (fun e => do
        modify fun s => { s with depth := s.depth - 1 }
        throw e)

/-- Does `lit` occur at char index `i`? Returns the index after it. -/
def litAt (ctx : Ctx) (i : Nat) (lit : List Char) : Option Nat :=
  match lit with
  | [] => some i
  | c :: cs =>
    match ctx.chars[i]? with
    | some c' => if c == c' then litAt ctx (i + 1) cs else none
    | none => none

/-- Skip whitespace, `--` line comments, nested `/- -/` block
    comments. -/
partial def ws : M Unit := do
  let ctx ← read
  let s ← get
  let mut i := s.idx
  let mut go := true
  while go do
    match ctx.chars[i]? with
    | some c =>
      if isWs c then
        i := i + 1
      else if (litAt ctx i ['-', '-']).isSome then
        i := i + 2
        while ctx.chars[i]?.isSome && ctx.chars[i]! != '\n' do
          i := i + 1
        if ctx.chars[i]?.isSome then i := i + 1
      else if (litAt ctx i ['/', '-']).isSome then
        let openIdx := i
        let mut depth := 1
        i := i + 2
        while depth > 0 do
          if (litAt ctx i ['/', '-']).isSome then
            depth := depth + 1
            i := i + 2
          else if (litAt ctx i ['-', '/']).isSome then
            depth := depth - 1
            i := i + 2
          else
            match ctx.chars[i]? with
            | some _ => i := i + 1
            | none =>
              let o ← off openIdx
              setIdx i
              failFatal .unterminatedComment ⟨o, o + 2⟩
      else
        go := false
    | none => go := false
  setIdx i

/-- Lex one identifier component at `i` (no whitespace skip). -/
def identRaw (ctx : Ctx) (i : Nat) : Option (String × Nat) := Id.run do
  match ctx.chars[i]? with
  | some c0 =>
    if !isIdFirst c0 then return none
    let mut j := i + 1
    while ctx.chars[j]?.any isIdRest do
      j := j + 1
    let s := (ctx.chars.extract i j).foldl (·.push ·) ""
    return some (s, j)
  | none => return none

/-- Lex one ascii-digit run at `i`. -/
def digitsRaw (ctx : Ctx) (i : Nat) : Option (String × Nat) := Id.run do
  let mut j := i
  while ctx.chars[j]?.any Char.isDigit do
    j := j + 1
  if j == i then return none
  return some ((ctx.chars.extract i j).foldl (·.push ·) "", j)

/-- `«…»` quoted component starting at `i` (expects `«` there). -/
def quotedComponent (i : Nat) : M (String × Nat) := do
  let ctx ← read
  if ctx.chars[i]? != some '«' then failExp i "name"
  else Id.run do
    let mut j := i + 1
    while ctx.chars[j]?.isSome && ctx.chars[j]! != '»' do
      j := j + 1
    return do
      match ctx.chars[j]? with
      | none =>
        let o ← off i
        failFatal .unterminatedQuotedName ⟨o, o + 2⟩
      | some _ =>
        if j == i + 1 then failExp i "nonempty «…» component"
        else
          let s := (ctx.chars.extract (i + 1) j).foldl (·.push ·) ""
          return (s, j + 1)

/-- Keyword or contextual word: a full identifier component equal to
    `w`. Consumes leading whitespace. -/
def kw (w : String) : M Span := do
  ws
  let ctx ← read
  let i ← curIdx
  match identRaw ctx i with
  | some (c, j) =>
    if c == w then do
      let span ← sp i j
      setIdx j
      return span
    else failExp i w
  | none => failExp i w

/-- Peek the next identifier word (after ws) without consuming. -/
def peekWord : M (Option String) := do
  ws
  let ctx ← read
  return (identRaw ctx (← curIdx)).map (·.1)

/-- Punctuation token; `":"` refuses to match the prefix of `":="`,
    and `"|"` the prefix of `"|-"` (the ASCII main-expression
    turnstile) — so ctor/rule bars never absorb it. -/
def sym (s : String) : M Span := do
  ws
  let ctx ← read
  let i ← curIdx
  if s == ":" && (litAt ctx i [':', '=']).isSome then failExp i ":"
  else if s == "|" && (litAt ctx i ['|', '-']).isSome then failExp i "|"
  else
    match litAt ctx i s.toList with
    | some j => do
      let span ← sp i j
      setIdx j
      return span
    | none => failExp i s

/-- `⊢` or `|-` — the main-expression marker. -/
def turnstileTok : M Span := do
  ws
  let ctx ← read
  let i ← curIdx
  if ctx.chars[i]? == some '⊢' then do
    let span ← sp i (i + 1)
    setIdx (i + 1)
    return span
  else
    match litAt ctx i ['|', '-'] with
    | some j => do
      let span ← sp i j
      setIdx j
      return span
    | none => failExp i "⊢"

/-- `→` or `->`. -/
def arrowTok : M Span := do
  ws
  let ctx ← read
  let i ← curIdx
  match ctx.chars[i]? with
  | some '→' => do
    let span ← sp i (i + 1)
    setIdx (i + 1)
    return span
  | _ =>
    match litAt ctx i ['-', '>'] with
    | some j => do
      let span ← sp i j
      setIdx j
      return span
    | none => failExp i "→"

/-- Dotted surface name. Leading component: identifier or `«…»`;
    continuations may also be bare digit runs (numeric components).
    Stops before `.{` and before a reserved continuation. -/
partial def nameP : M SName := do
  ws
  let ctx ← read
  let start ← curIdx
  let (first, afterFirst) ←
    match identRaw ctx start with
    | some (c, j) =>
      if isReserved c then failExp start "name"
      else pure (NameComponent.str c, j)
    | none =>
      if ctx.chars[start]? == some '«' then do
        let (s, j) ← quotedComponent start
        pure (NameComponent.str s, j)
      else failExp start "name"
  let mut parts := #[first]
  let mut i := afterFirst
  let mut go := true
  while go do
    if ctx.chars[i]? == some '.' && ctx.chars[i+1]? != some '{' then
      let r := i + 1
      match identRaw ctx r with
      | some (c, j) =>
        if isReserved c then go := false -- leave `.def` unconsumed
        else
          parts := parts.push (.str c)
          i := j
      | none =>
        if ctx.chars[r]? == some '«' then
          let (s, j) ← quotedComponent r
          parts := parts.push (.str s)
          i := j
        else
          match digitsRaw ctx r with
          | some (d, j) =>
            parts := parts.push (.num d.toNat!)
            i := j
          | none => go := false -- trailing `.` stays unconsumed
    else
      go := false
  setIdx i
  return { parts, span := ← sp start i }

def isHexAny (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- `#hex` reference at the CURRENT index, no leading-whitespace skip
    (callers control adjacency). 4–64 lowercase hex digits. -/
def hashRaw : M HashRef := do
  let ctx ← read
  let start ← curIdx
  if ctx.chars[start]? != some '#' then failExp start "#hash"
  else Id.run do
    let mut j := start + 1
    while ctx.chars[j]?.any isHexAny do
      j := j + 1
    let run := (ctx.chars.extract (start + 1) j).foldl (·.push ·) ""
    return do
      let span ← sp start j
      match run.toList.find? Char.isUpper with
      | some bad =>
        failFatal
          (.invalidHash s!"uppercase digit '{bad}' (addresses are lowercase)")
          span
      | none =>
        if ctx.chars[j]?.any isIdRest then
          failFatal (.invalidHash "invalid character in hash") span
        else if run.length < 4 then
          failFatal
            (.invalidHash s!"too short ({run.length} digits, minimum 4)")
            span
        else if run.length > 64 then
          failFatal
            (.invalidHash s!"too long ({run.length} digits, maximum 64)")
            span
        else do
          setIdx j
          return { hex := run, span }

def digitInRadix (radix : Nat) (c : Char) : Bool :=
  if radix == 16 then isHexAny c
  else if radix == 10 then c.isDigit
  else if radix == 8 then '0' ≤ c && c ≤ '7'
  else c == '0' || c == '1'

def digitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Nat literal: decimal, `0x`, `0b`, `0o`. Arbitrary precision. -/
def natlit : M (Nat × Span) := do
  ws
  let ctx ← read
  let start ← curIdx
  let (radix, digitsStart) :=
    match litAt ctx start ['0', 'x'] with
    | some j => (16, j)
    | none =>
      match litAt ctx start ['0', 'b'] with
      | some j => (2, j)
      | none =>
        match litAt ctx start ['0', 'o'] with
        | some j => (8, j)
        | none => (10, start)
  Id.run do
    let mut j := digitsStart
    while ctx.chars[j]?.any (digitInRadix radix) do
      j := j + 1
    if j == digitsStart then return failExp start "number"
    let n := (ctx.chars.extract digitsStart j).foldl
      (fun acc c => acc * radix + digitVal c) 0
    return do
      let span ← sp start j
      setIdx j
      return (n, span)

/-- Nat literal bounded to `u64` (mirrors Rust's `nat_u64`). -/
def natU64 : M (Nat × Span) := do
  let (n, span) ← natlit
  if n < 2 ^ 64 then return (n, span)
  else failFatal .natOutOfRange span

def hexEscape (n : Nat) (escStartOff : Nat) : M Char := do
  let ctx ← read
  let i ← curIdx
  Id.run do
    let mut ok := true
    let mut v := 0
    for k in [0:n] do
      match ctx.chars[i + k]? with
      | some c => if isHexAny c then v := v * 16 + digitVal c else ok := false
      | none => ok := false
    let val := v
    let good := ok
    return do
      if !good then
        failFatal .invalidEscape ⟨escStartOff, ← off i⟩
      else if !val.isValidChar then
        failFatal .invalidEscape ⟨escStartOff, (← off i) + n⟩
      else do
        setIdx (i + n)
        return Char.ofNat val

/-- String literal with Lean escapes. -/
partial def strlit : M (String × Span) := do
  ws
  let ctx ← read
  let start ← curIdx
  if ctx.chars[start]? != some '"' then failExp start "string literal"
  else do
    setIdx (start + 1)
    let mut out := ""
    let mut go := true
    while go do
      let i ← curIdx
      match ctx.chars[i]? with
      | none =>
        let o ← off start
        failFatal .unterminatedString ⟨o, ctx.byteOff[ctx.byteOff.size - 1]!⟩
      | some '"' =>
        setIdx (i + 1)
        go := false
      | some '\\' =>
        let escStart ← off i
        match ctx.chars[i+1]? with
        | none => failFatal .invalidEscape ⟨escStart, escStart + 1⟩
        | some e =>
          setIdx (i + 2)
          match e with
          | 'n' => out := out.push '\n'
          | 't' => out := out.push '\t'
          | 'r' => out := out.push '\r'
          | '\\' => out := out.push '\\'
          | '"' => out := out.push '"'
          | '\'' => out := out.push '\''
          | 'x' => out := out.push (← hexEscape 2 escStart)
          | 'u' => out := out.push (← hexEscape 4 escStart)
          | _ => failFatal .invalidEscape ⟨escStart, ← off (i + 2)⟩
      | some c =>
        setIdx (i + 1)
        out := out.push c
    let stop ← curIdx
    return (out, ← sp start stop)

mutual

/-- Universe expression: `uatom ("+" nat)?`. -/
partial def univ : M UnivExpr := do
  let a ← uatom
  ws
  let ctx ← read
  let i ← curIdx
  if ctx.chars[i]? == some '+' then do
    setIdx (i + 1)
    let (n, nsp) ← cut natU64
    return .add a n (a.span.to nsp)
  else
    return a

/-- Universe atom: literal, var, parens, contextual `max`/`imax`. -/
partial def uatom : M UnivExpr := withDepth do
  ws
  let ctx ← read
  let start ← curIdx
  match ctx.chars[start]? with
  | some c =>
    if c.isDigit then do
      let (n, span) ← natU64
      return .nat n span
    else if c == '(' then do
      setIdx (start + 1)
      let u ← cut univ
      let _ ← cut (sym ")")
      return u
    else if c == '«' then do
      let (s, j) ← quotedComponent start
      setIdx j
      return .var (.str s) (← sp start j)
    else
      match identRaw ctx start with
      | some ("max", j) => do
        setIdx j
        let a ← cut uatom
        let b ← cut uatom
        return .max a b ⟨← off start, b.span.stop⟩
      | some ("imax", j) => do
        setIdx j
        let a ← cut uatom
        let b ← cut uatom
        return .imax a b ⟨← off start, b.span.stop⟩
      | some (c', j) =>
        if isReserved c' then failExp start "universe"
        else do
          setIdx j
          return .var (.str c') (← sp start j)
      | none => failExp start "universe"
  | none => failExp start "universe"

end

/-- Adjacent `.{u, v}` level list (no whitespace before `.{`). -/
partial def levelsAdj : M (Option (Array UnivExpr)) := do
  let ctx ← read
  let openIdx ← curIdx
  if (litAt ctx openIdx ['.', '{']).isNone then return none
  else do
    setIdx (openIdx + 2)
    ws
    let j ← curIdx
    if ctx.chars[j]? == some '}' then
      failFatal .emptyLevels (← sp openIdx (j + 1))
    else do
      setIdx (openIdx + 2)
      let first ← cut univ
      let mut levels := #[first]
      let mut go := true
      while go do
        ws
        let i ← curIdx
        match ctx.chars[i]? with
        | some ',' =>
          setIdx (i + 1)
          levels := levels.push (← cut univ)
        | some '}' =>
          setIdx (i + 1)
          go := false
        | _ => cut (failExp i "`,` or `}`")
      return some levels

/-- Constant reference: `Name`, `#hash`, `Name#hash`, with optional
    adjacent `.{levels}`. -/
partial def cref : M ConstRef := do
  ws
  let ctx ← read
  let start ← curIdx
  if ctx.chars[start]? == some '#' then do
    let h ← hashRaw
    let levels ← levelsAdj
    return { hash := some h, levels, span := ← sp start (← curIdx) }
  else do
    let n ← nameP
    let hash ←
      if ctx.chars[(← curIdx)]? == some '#' then some <$> hashRaw
      else pure none
    let levels ← levelsAdj
    return { name := some n, hash, levels, span := ← sp start (← curIdx) }

/-- Greedy optional universe argument for `Type`/`Sort`: a numeral, a
    simple identifier or `«…»` component (not dotted/hashed), or a
    parenthesized universe. -/
partial def uargOpt : M (Option UnivExpr) := do
  let saved ← get
  ws
  let ctx ← read
  let j ← curIdx
  match ctx.chars[j]? with
  | some c =>
    if c.isDigit then do
      let (n, span) ← natU64
      return some (.nat n span)
    else if c == '(' then do
      match ← attempt? (do
          setIdx (j + 1)
          let u ← univ
          let _ ← sym ")"
          pure u) with
      | some u => return some u
      | none =>
        set saved
        return none
    else if c == '«' then do
      let (s, k) ← quotedComponent j
      if ctx.chars[k]? == some '#' || ctx.chars[k]? == some '.' then do
        set saved
        return none
      else do
        setIdx k
        return some (.var (.str s) (← sp j k))
    else
      match identRaw ctx j with
      | some (w, k) =>
        let simple := !isReserved w && w != "max" && w != "imax"
          && w != "_" && ctx.chars[k]? != some '#'
          && ctx.chars[k]? != some '.'
        if simple then do
          setIdx k
          return some (.var (.str w) (← sp j k))
        else do
          set saved
          return none
      | none =>
        set saved
        return none
  | none =>
    set saved
    return none

/-- Binder name: identifier component or `_`. -/
def binderNameP : M BinderName := do
  ws
  let ctx ← read
  let i ← curIdx
  match identRaw ctx i with
  | some (c, j) => do
    let span ← sp i j
    if c == "_" then do
      setIdx j
      return .anon span
    else if isReserved c then failExp i "binder name"
    else do
      setIdx j
      return .ident (.str c) span
  | none =>
    if ctx.chars[i]? == some '«' then do
      let (s, j) ← quotedComponent i
      setIdx j
      return .ident (.str s) (← sp i j)
    else failExp i "binder name"

mutual

/-- Application atom. -/
partial def atom : M Term := withDepth do
  ws
  let ctx ← read
  let start ← curIdx
  match ctx.chars[start]? with
  | none => failExp start "term"
  | some c =>
    if c == '(' then do
      setIdx (start + 1)
      let t ← cut term
      let _ ← cut (sym ")")
      return t
    else if c == '"' then do
      let (s, span) ← strlit
      return .strLit s span
    else if c == '#' || c == '«' then do
      return .ref (← cref)
    else if c.isDigit then do
      let (n, span) ← natlit
      return .natLit n span
    else if isIdFirst c then do
      let some (word, _) := identRaw ctx start | failExp start "term"
      match word with
      | "_" => failFatal .placeholder (← sp start (start + 1))
      | "Prop" => do
        let span ← kw "Prop"
        return .sort .prop span
      | "Type" => do
        let ksp ← kw "Type"
        let u ← uargOpt
        let span := match u with
          | some x => ksp.to x.span
          | none => ksp
        return .sort (.type u) span
      | "Sort" => do
        let ksp ← kw "Sort"
        match ← uargOpt with
        | some u => return .sort (.sort u) (ksp.to u.span)
        | none => cut (failExp (← curIdx) "universe")
      | "proj" => do
        let ksp ← kw "proj"
        let typeRef ← cut cref
        let (idx, _) ← cut natU64
        let v ← cut atom
        return .proj typeRef idx v (ksp.to v.span)
      | w =>
        if isReserved w then failExp start "term"
        else return .ref (← cref)
    else failExp start "term"

/-- Application spine: `atom+`, flat. -/
partial def appP : M Term := do
  let head ← atom
  let mut args := #[]
  let mut go := true
  while go do
    match ← attempt? atom with
    | some t => args := args.push t
    | none => go := false
  if args.isEmpty then return head
  else return .app head args (head.span.to args.back!.span)

/-- One bracketed binder group. `(…)` is tentative (backtrackable
    before the `:`); `{…}`, `[…]`, `⦃…⦄` commit. -/
partial def binderGroup : M BinderGroup := do
  ws
  let ctx ← read
  let start ← curIdx
  let bracket : Option (Char × String × Lean.BinderInfo) :=
    match ctx.chars[start]? with
    | some '(' => some ('(', ")", .default)
    | some '{' => some ('{', "}", .implicit)
    | some '[' => some ('[', "]", .instImplicit)
    | some '⦃' => some ('⦃', "⦄", .strictImplicit)
    | _ => none
  match bracket with
  | none => failExp start "binder"
  | some (openC, closeS, info) => do
    setIdx (start + 1)
    if openC == '[' then do
      match ← attempt? binderNamesColon with
      | some names => do
        let ty ← cut term
        let _ ← cut (sym closeS)
        return .mk info names ty (← sp start (← curIdx))
      | none => do
        let ty ← cut term
        let _ ← cut (sym closeS)
        return .mk info #[] ty (← sp start (← curIdx))
    else do
      let names ←
        if openC == '(' then binderNamesColon
        else cut binderNamesColon
      let ty ← cut term
      let _ ← cut (sym closeS)
      return .mk info names ty (← sp start (← curIdx))

/-- `ident+ :` — the committing prefix of a named binder group. -/
partial def binderNamesColon : M (Array BinderName) := do
  let first ← binderNameP
  let mut names := #[first]
  let mut go := true
  while go do
    match ← attempt? binderNameP with
    | some n => names := names.push n
    | none => go := false
  let _ ← sym ":"
  return names

partial def binderGroups1 : M (Array BinderGroup) := do
  let first ← binderGroup
  let mut groups := #[first]
  let mut go := true
  while go do
    match ← attempt? binderGroup with
    | some g => groups := groups.push g
    | none => go := false
  return groups

/-- `fun binder+ => term`. -/
partial def lamTerm : M Term := do
  let ksp ← kw "fun"
  let groups ← cut binderGroups1
  let _ ← cut (sym "=>")
  let body ← cut term
  return .lam groups body (ksp.to body.span)

/-- `let x : T := v; b` / `have x : T := v; b`. -/
partial def letTerm (nonDep : Bool) : M Term := do
  let ksp ← kw (if nonDep then "have" else "let")
  let name ← cut binderNameP
  let _ ← cut (sym ":")
  let ty ← cut term
  let _ ← cut (sym ":=")
  let val ← cut term
  let _ ← cut (sym ";")
  let body ← cut term
  return .letE nonDep name ty val body (ksp.to body.span)

/-- Dependent domain: `binder+ → term` (committed once the first
    group parses). -/
partial def piTerm : M Term := do
  ws
  let start ← curIdx
  let groups ← binderGroups1
  let _ ← cut arrowTok
  let body ← cut term
  return .pi groups body ⟨← off start, body.span.stop⟩

/-- Arrow layer: dependent domain, or application with optional `→`. -/
partial def piOrArrow : M Term := do
  ws
  let ctx ← read
  let j ← curIdx
  let starter := ctx.chars[j]?
  if starter == some '(' || starter == some '{' || starter == some '['
      || starter == some '⦃' then
    match ← attempt? piTerm with
    | some t => return t
    | none => appArrow
  else
    appArrow

partial def appArrow : M Term := do
  let lhs ← appP
  match ← attempt? arrowTok with
  | some _ => do
    let cod ← cut term
    return .arrow lhs cod (lhs.span.to cod.span)
  | none => return lhs

/-- Term entry point. -/
partial def term : M Term := withDepth do
  match ← peekWord with
  | some "fun" => lamTerm
  | some "let" => letTerm false
  | some "have" => letTerm true
  | _ => piOrArrow

end

/-- `.{u, v}` universe-parameter binders on a declaration. -/
partial def uparams : M (Array UParam) := do
  let ctx ← read
  if (litAt ctx (← curIdx) ['.', '{']).isNone then return #[]
  else do
    setIdx ((← curIdx) + 2)
    let mut out := #[]
    let mut go := true
    while go do
      ws
      let start ← curIdx
      let comp ←
        match identRaw ctx start with
        | some (c, j) =>
          if isReserved c || c == "_" then
            cut (failExp start "universe parameter")
          else do
            setIdx j
            pure (NameComponent.str c)
        | none =>
          if ctx.chars[start]? == some '«' then do
            let (s, j) ← quotedComponent start
            setIdx j
            pure (NameComponent.str s)
          else cut (failExp start "universe parameter")
      out := out.push { name := comp, span := ← sp start (← curIdx) }
      ws
      let i ← curIdx
      match ctx.chars[i]? with
      | some ',' => setIdx (i + 1)
      | some '}' =>
        setIdx (i + 1)
        go := false
      | _ => cut (failExp i "`,` or `}`")
    return out

/-- Optional declaration name + optional universe parameters. -/
partial def declName : M (Option SName × Array UParam) := do
  ws
  let ctx ← read
  let j ← curIdx
  if (litAt ctx j ['.', '{']).isSome then do
    return (none, ← uparams)
  else if ctx.chars[j]? == some '«'
      || (identRaw ctx j).any (fun (c, _) => !isReserved c) then do
    let n ← nameP
    let ups ← uparams
    return (some n, ups)
  else
    return (none, #[])

/-- `(<key> := <nat>)` count annotation. -/
partial def annot (key : String) (label : String) : M Nat := do
  ws
  let ctx ← read
  let i ← curIdx
  if ctx.chars[i]? != some '(' then failExp i label
  else do
    setIdx (i + 1)
    match ← attempt? (kw key) with
    | none => do
      setIdx i
      failExp i label
    | some _ => do
      let _ ← cut (sym ":=")
      let (v, _) ← cut natU64
      let _ ← cut (sym ")")
      return v

/-- Optional `(k := true|false)` on a recursor. -/
partial def kAnnot : M Bool := do
  let saved ← get
  ws
  let ctx ← read
  let j ← curIdx
  if ctx.chars[j]? != some '(' then do
    set saved
    return false
  else do
    setIdx (j + 1)
    match ← attempt? (kw "k") with
    | none => do
      set saved
      return false
    | some _ => do
      let _ ← cut (sym ":=")
      let v ← match ← peekWord with
        | some "true" => do let _ ← kw "true"; pure true
        | some "false" => do let _ ← kw "false"; pure false
        | _ => cut (failExp (← curIdx) "true or false")
      let _ ← cut (sym ")")
      return v

def defDecl (kwKind : DefKw) (kwWord : String) (mods : Modifiers)
    (startIdx : Nat) : M Decl := do
  let _ ← kw kwWord
  if mods.isPartial && kwKind != .defn then
    cut (failExp startIdx "def after partial")
  else do
    let (name, ups) ← cut declName
    let _ ← cut (sym ":")
    let ty ← cut term
    let _ ← cut (sym ":=")
    let value ← cut term
    return .defn
      { kw := kwKind, mods, name, uparams := ups, ty, value
        span := ← sp startIdx (← curIdx) }

def axiomDecl (mods : Modifiers) (startIdx : Nat) : M Decl := do
  let _ ← kw "axiom"
  if mods.isPartial then cut (failExp startIdx "def after partial")
  else do
    let (name, ups) ← cut declName
    let _ ← cut (sym ":")
    let ty ← cut term
    return .axio
      { isUnsafe := mods.isUnsafe, name, uparams := ups, ty
        span := ← sp startIdx (← curIdx) }

def quotDecl (startIdx : Nat) : M Decl := do
  let _ ← kw "quot"
  let kind ← match ← peekWord with
    | some "type" => do let _ ← kw "type"; pure QuotKindKw.type
    | some "ctor" => do let _ ← kw "ctor"; pure QuotKindKw.ctor
    | some "lift" => do let _ ← kw "lift"; pure QuotKindKw.lift
    | some "ind" => do let _ ← kw "ind"; pure QuotKindKw.ind
    | _ => cut (failExp (← curIdx) "quotient kind (type|ctor|lift|ind)")
  let (name, ups) ← cut declName
  let _ ← cut (sym ":")
  let ty ← cut term
  return .quot
    { kind, name, uparams := ups, ty, span := ← sp startIdx (← curIdx) }

partial def ctorBlock : M (Array CtorDecl) := do
  if (← peekWord) != some "where" then return #[]
  else do
    let _ ← kw "where"
    let mut ctors := #[]
    let mut go := true
    while go do
      match ← attempt? (sym "|") with
      | some barSp => do
        let (name, ups) ← cut declName
        if let some up := ups[0]? then
          failFatal
            (.unexpectedToken "(params := _)"
              "universe parameters (constructors inherit the inductive's)")
            up.span
        else do
          let params ← cut (annot "params" "(params := _)")
          let fields ← cut (annot "fields" "(fields := _)")
          let _ ← cut (sym ":")
          let ty ← cut term
          ctors := ctors.push
            { name, params, fields, ty
              span := barSp.to ⟨← off (← curIdx), ← off (← curIdx)⟩ }
      | none => go := false
    if ctors.isEmpty then cut (failExp (← curIdx) "|")
    else return ctors

def indDecl (mods : Modifiers) (startIdx : Nat) : M Decl := do
  let _ ← kw "inductive"
  if mods.isPartial then cut (failExp startIdx "def after partial")
  else do
    let (name, ups) ← cut declName
    let params ← cut (annot "params" "(params := _)")
    let indices ← cut (annot "indices" "(indices := _)")
    let _ ← cut (sym ":")
    let ty ← cut term
    let ctors ← ctorBlock
    return .indc
      { isUnsafe := mods.isUnsafe, name, uparams := ups, params, indices
        ty, ctors, span := ← sp startIdx (← curIdx) }

partial def ruleBlock : M (Array RuleDecl) := do
  if (← peekWord) != some "where" then return #[]
  else do
    let _ ← kw "where"
    let mut rules := #[]
    let mut go := true
    while go do
      match ← attempt? (sym "|") with
      | some barSp => do
        let _ ← cut (kw "rule")
        let fields ← cut (annot "fields" "(fields := _)")
        let _ ← cut (sym ":=")
        let rhs ← cut term
        rules := rules.push
          { fields, rhs
            span := barSp.to ⟨← off (← curIdx), ← off (← curIdx)⟩ }
      | none => go := false
    if rules.isEmpty then cut (failExp (← curIdx) "|")
    else return rules

def recrDecl (mods : Modifiers) (startIdx : Nat) : M Decl := do
  let _ ← kw "recursor"
  if mods.isPartial then cut (failExp startIdx "def after partial")
  else do
    let (name, ups) ← cut declName
    let params ← cut (annot "params" "(params := _)")
    let indices ← cut (annot "indices" "(indices := _)")
    let motives ← cut (annot "motives" "(motives := _)")
    let minors ← cut (annot "minors" "(minors := _)")
    let k ← kAnnot
    let _ ← cut (sym ":")
    let ty ← cut term
    let rules ← ruleBlock
    return .recr
      { isUnsafe := mods.isUnsafe, name, uparams := ups, params, indices
        motives, minors, k, ty, rules, span := ← sp startIdx (← curIdx) }

def prjDecl (kind : PrjKind) (word : String) (startIdx : Nat) : M Decl := do
  let _ ← kw word
  let (name, ups) ← cut declName
  if let some up := ups[0]? then
    failFatal (.unexpectedToken ":=" "universe parameters") up.span
  else do
    let _ ← cut (sym ":=")
    ws
    let block ← cut hashRaw
    let (idx, _) ← cut natU64
    let cidx ←
      if kind == .cprj then some <$> Prod.fst <$> cut natU64
      else pure none
    return .prj
      { kind, name, block, idx, cidx, span := ← sp startIdx (← curIdx) }

mutual

/-- One declaration. -/
partial def decl : M Decl := do
  ws
  let startIdx ← curIdx
  let mut mods : Modifiers := {}
  let mut going := true
  while going do
    match ← peekWord with
    | some "unsafe" =>
      if mods.isUnsafe then going := false
      else do
        let _ ← kw "unsafe"
        mods := { mods with isUnsafe := true }
    | some "partial" =>
      if mods.isPartial then going := false
      else do
        let _ ← kw "partial"
        mods := { mods with isPartial := true }
    | _ => going := false
  if mods.isUnsafe && mods.isPartial then
    cut (failExp startIdx "either unsafe or partial (not both)")
  else do
    let hasMods := mods.isUnsafe || mods.isPartial
    match ← peekWord with
    | some "def" => defDecl .defn "def" mods startIdx
    | some "theorem" => defDecl .thm "theorem" mods startIdx
    | some "opaque" => defDecl .opaq "opaque" mods startIdx
    | some "axiom" => axiomDecl mods startIdx
    | some "inductive" => indDecl mods startIdx
    | some "recursor" => recrDecl mods startIdx
    | some "quot" =>
      if hasMods then failExp (← curIdx) "declaration"
      else quotDecl startIdx
    | some "mutual" =>
      if hasMods then failExp (← curIdx) "declaration"
      else mutualDecl startIdx
    | some "dprj" =>
      if hasMods then failExp (← curIdx) "declaration"
      else prjDecl .dprj "dprj" startIdx
    | some "iprj" =>
      if hasMods then failExp (← curIdx) "declaration"
      else prjDecl .iprj "iprj" startIdx
    | some "cprj" =>
      if hasMods then failExp (← curIdx) "declaration"
      else prjDecl .cprj "cprj" startIdx
    | some "rprj" =>
      if hasMods then failExp (← curIdx) "declaration"
      else prjDecl .rprj "rprj" startIdx
    | _ => failExp (← curIdx) "declaration"

partial def mutualDecl (startIdx : Nat) : M Decl := do
  let _ ← kw "mutual"
  let mut members := #[]
  let mut go := true
  while go do
    if (← peekWord) == some "end" then
      if members.isEmpty then cut (failExp (← curIdx) "declaration")
      else do
        let _ ← kw "end"
        go := false
    else do
      let d ← cut decl
      match d with
      | .defn _ | .indc _ | .recr _ => members := members.push d
      | other => failFatal .badMutualMember other.span
  return .muts members (← sp startIdx (← curIdx))

end

/-- `import Foo.Bar#hash` / `import #hash`. -/
partial def importDecl : M ImportDecl := do
  ws
  let startIdx ← curIdx
  let _ ← kw "import"
  ws
  let ctx ← read
  let (prefixName, hash) ←
    if ctx.chars[(← curIdx)]? == some '#' then do
      let h ← cut hashRaw
      pure (none, h)
    else do
      let n ← cut nameP
      if ctx.chars[(← curIdx)]? != some '#' then
        cut (failExp (← curIdx) "#hash")
      else do
        let h ← cut hashRaw
        pure (some n, h)
  if hash.hex.length != 64 then
    failFatal (.importHashLength hash.hex.length) hash.span
  else
    return { prefixName, hash, span := ← sp startIdx (← curIdx) }

/-- The `value : type` interior — deterministic on its own: no term
    production consumes a bare `:`, so the value spine stops at the
    annotation. Only the decl→main *boundary* needs the turnstile. -/
partial def mainExprTail (startIdx : Nat) : M MainExpr := do
  let value ← cut term
  let _ ← cut (sym ":")
  let ty ← cut term
  let stopIdx ← curIdx
  ws
  let ctx ← read
  if (ctx.chars[(← curIdx)]?).isSome then
    let o ← off (← curIdx)
    failFatal .mainExprNotLast ⟨o, o⟩
  else
    return { value, ty, span := ← sp startIdx stopIdx }

/-- The trailing `⊢ value : type` main expression. The turnstile stops
    a preceding declaration's application spine (found by property
    testing); it is required after declarations and optional only when
    the main expression is the file's sole item. -/
partial def mainExprP : M MainExpr := do
  ws
  let startIdx ← curIdx
  let _ ← turnstileTok
  mainExprTail startIdx

/-- Whole file: `ixon <version>` header, imports, declarations,
    optional main expression, EOF. -/
partial def file : M File := do
  ws
  let startIdx ← curIdx
  -- Optional version header: absent means version 1, forever
  -- (grammar versions ≥ 2 must declare themselves). A leading `ixon`
  -- followed by a numeral is always the header (a constant literally
  -- named `ixon` applied to a literal at file start needs parens);
  -- followed by anything else it is content.
  let version ←
    if (← peekWord) == some "ixon" then do
      let saved ← get
      let _ ← kw "ixon"
      ws
      let ctx ← read
      if (ctx.chars[(← curIdx)]?).any Char.isDigit then do
        let (version, vsp) ← natU64
        if version != VERSION then
          failFatal (.unknownVersion version VERSION) vsp
        else pure version
      else do
        set saved
        pure VERSION
    else pure VERSION
  do
    let mut imports := #[]
    let mut go := true
    while go do
      if (← peekWord) == some "import" then
        imports := imports.push (← importDecl)
      else go := false
    let mut decls := #[]
    let mut mainE : Option MainExpr := none
    go := true
    while go do
      ws
      let ctx ← read
      let i ← curIdx
      if ctx.chars[i]?.isNone then go := false
      else if ctx.chars[i]? == some '⊢'
          || (litAt ctx i ['|', '-']).isSome then do
        mainE := some (← mainExprP)
        go := false
      else
        -- Bare `value : type` (no turnstile) is accepted only as the
        -- file's SOLE item: with no preceding declaration term there
        -- is no boundary to absorb into, and the interior is
        -- deterministic. After declarations the turnstile is required
        -- (the bare form errors on the orphaned `:` — never a silent
        -- re-split).
        let keywordItem := match identRaw ctx i with
          | some (w, _) =>
            ["def", "theorem", "opaque", "axiom", "inductive",
             "recursor", "quot", "mutual", "unsafe", "partial", "dprj",
             "iprj", "cprj", "rprj", "import"].contains w
          | none => false
        if !keywordItem && decls.isEmpty then do
          mainE := some (← mainExprTail i)
          go := false
        else decls := decls.push (← decl)
    return { version, imports, decls, main := mainE
             span := ← sp startIdx (← curIdx) }

/-- Short description of what sits at char index `pos`. -/
def foundSnippet (ctx : Ctx) (pos : Nat) : String := Id.run do
  match ctx.chars[pos]? with
  | none => return "end of input"
  | some c0 =>
    if isIdFirst c0 || c0.isDigit then
      let mut j := pos
      while ctx.chars[j]?.any (fun c => isIdRest c || c.isDigit) do
        j := j + 1
      let word := (ctx.chars.extract pos (min j (pos + 24))).foldl
        (·.push ·) ""
      return s!"`{word}`"
    else
      return s!"`{c0}`"

def convert (src : String) (ctx : Ctx) (e : PErr) : SyntaxError :=
  match e.special with
  | some (kind, span) => SyntaxError.new kind span src
  | none =>
    let bytePos := ctx.byteOff[min e.pos (ctx.byteOff.size - 1)]!
    let expected := if e.expected.isEmpty then "valid syntax" else e.expected
    SyntaxError.new
      (.unexpectedToken expected (foundSnippet ctx e.pos))
      ⟨bytePos, bytePos⟩ src

end Parser

open Parser in
/-- Parse a whole `.ixon` file. -/
def parseFile (src : String) (limits : Limits := {})
    : Except SyntaxError File :=
  if src.utf8ByteSize > limits.maxBytes then
    .error <| SyntaxError.new
      (.capExceeded .bytes limits.maxBytes) ⟨0, 0⟩ src
  else
    let ctx := Ctx.ofString src limits
    match (Parser.file.run ctx).run {} with
    | .ok f _ =>
      if countFileNodes f > limits.maxNodes then
        .error <| SyntaxError.new
          (.capExceeded .nodes limits.maxNodes) ⟨0, 0⟩ src
      else .ok f
    | .error e _ => .error (convert src ctx e)

open Parser in
/-- Parse a standalone term (whole input). -/
def parseTerm (src : String) (limits : Limits := {})
    : Except SyntaxError Term :=
  if src.utf8ByteSize > limits.maxBytes then
    .error <| SyntaxError.new
      (.capExceeded .bytes limits.maxBytes) ⟨0, 0⟩ src
  else
    let ctx := Ctx.ofString src limits
    let p : M Term := do
      let t ← term
      ws
      let ctx' ← read
      if ctx'.chars[(← curIdx)]?.isSome then
        failExp (← curIdx) "end of input"
      else return t
    match (p.run ctx).run {} with
    | .ok t _ =>
      if countTermNodes t > limits.maxNodes then
        .error <| SyntaxError.new
          (.capExceeded .nodes limits.maxNodes) ⟨0, 0⟩ src
      else .ok t
    | .error e _ => .error (convert src ctx e)

end Ixon.Syntax
