import IxCC.Tools.Check

/-! A conservative lexer for the trust ledger's source inventory. It handles
nested Lean comments and quoted literals, retains line locations, and rejects
unterminated input. Inventory consumers reject syntax they cannot account for;
this scanner is a tripwire, not a replacement for Lean's parser or axiom fence. -/

namespace IxCC.Tools.SourceScan

inductive Kind where
  | name | literal | punctuation | quotedName
  deriving BEq, Repr, Inhabited

structure Token where
  text : String
  line : Nat
  kind : Kind
  deriving BEq, Repr, Inhabited

private def nameStart (char : Char) : Bool :=
  Lean.isIdFirst char

private def namePart (char : Char) : Bool :=
  Lean.isIdRest char || char == '.'

/-- Check whether `chars` starting at `index` begins a Lean raw string literal
`r#*"..."#*`, returning `(numHashes, bodyStart)` if so. -/
private def rawStringOpen? (chars : Array Char) (index : Nat) : Option (Nat × Nat) := Id.run do
  if chars[index]? != some 'r' then return none
  let mut k := index + 1
  while k < chars.size && chars[k]! == '#' do k := k + 1
  if chars[k]? == some '"' then
    return some (k - (index + 1), k + 1)
  return none

/-- Whether `chars[index..]` starts with `"` followed by `hashes` consecutive `#`s. -/
private def matchesRawClose (chars : Array Char) (index hashes : Nat) : Bool := Id.run do
  if chars[index]? != some '"' then return false
  for h in [:hashes] do
    if chars[index + 1 + h]? != some '#' then return false
  return true

/-- Core lexer loop supporting Lean raw strings (`r#*"..."#*`) and interpolated
string expressions (`s!"...{...}..."`). When `stopBrace` is true, stops at the
first unmatched `}` (returning its index without consuming it). -/
private partial def scanCore (chars : Array Char) (cSource stopBrace : Bool)
    (initIndex initLine : Nat) : Except String (Array Token × Nat × Nat) := do
  let mut tokens := #[]
  let mut index := initIndex
  let mut line := initLine
  let mut braceDepth : Nat := 0
  while index < chars.size do
    let char := chars[index]!
    let next := chars[index + 1]?.getD '\x00'
    if char.isWhitespace then
      if char == '\n' then line := line + 1
      index := index + 1
    else if (cSource && char == '/' && next == '/') ||
        (!cSource && char == '-' && next == '-') then
      while index < chars.size && chars[index]! != '\n' do index := index + 1
    else if char == '/' && next == (if cSource then '*' else '-') then
      let mut depth := 1
      index := index + 2
      while index < chars.size && depth > 0 do
        let first := chars[index]!
        let second := chars[index + 1]?.getD '\x00'
        if !cSource && first == '/' && second == '-' then
          depth := depth + 1
          index := index + 2
        else if first == (if cSource then '*' else '-') && second == '/' then
          depth := depth - 1
          index := index + 2
        else
          if first == '\n' then line := line + 1
          index := index + 1
      if depth != 0 then throw s!"line {line}: unterminated block comment"
    else if !cSource && char == 'r' && (rawStringOpen? chars index).isSome then
      let some (hashes, bodyStart) := rawStringOpen? chars index | unreachable!
      let startLine := line
      let mut value := ""
      let mut ended := false
      index := bodyStart
      while index < chars.size && !ended do
        if matchesRawClose chars index hashes then
          ended := true
          index := index + 1 + hashes
        else
          let current := chars[index]!
          if current == '\n' then line := line + 1
          value := value.push current
          index := index + 1
      if !ended then throw s!"line {startLine}: unterminated raw string literal"
      tokens := tokens.push ⟨value, startLine, .literal⟩
    else if char == '"' || (char == '\'' &&
        (cSource || next == '\\' || chars[index + 2]? == some '\'')) then
      let startLine := line
      let delimiter := char
      let isInterp := !cSource && delimiter == '"' &&
        (tokens.back?.map fun t =>
          (t.kind == .punctuation && t.text == "!") ||
          (t.kind == .name && t.text.endsWith "!")).getD false
      let mut value := ""
      let mut interpTokens : Array Token := #[]
      let mut ended := false
      index := index + 1
      while index < chars.size && !ended do
        let current := chars[index]!
        if current == delimiter then
          ended := true
          index := index + 1
        else if current == '\\' then
          if index + 1 ≥ chars.size then throw s!"line {startLine}: dangling literal escape"
          let esc := chars[index + 1]!
          if esc == '\n' then line := line + 1
          value := (value.push current).push esc
          index := index + 2
        else if isInterp && current == '{' then
          match scanCore chars false true (index + 1) line with
          | .ok (inner, endIdx, endLine) =>
            if endIdx < chars.size && chars[endIdx]! == '}' then
              for k in [index : endIdx + 1] do
                value := value.push chars[k]!
              interpTokens := interpTokens.push ⟨"{", line, .punctuation⟩
              interpTokens := interpTokens ++ inner
              interpTokens := interpTokens.push ⟨"}", endLine, .punctuation⟩
              index := endIdx + 1
              line := endLine
            else
              value := value.push current
              index := index + 1
          | .error _ =>
            value := value.push current
            index := index + 1
        else
          if current == '\n' then line := line + 1
          value := value.push current
          index := index + 1
      if !ended then throw s!"line {startLine}: unterminated literal"
      tokens := tokens.push ⟨value, startLine, .literal⟩
      tokens := tokens ++ interpTokens
    else if char == '«' then
      let startLine := line
      index := index + 1
      let mut value := ""
      while index < chars.size && chars[index]! != '»' do
        if chars[index]! == '\n' then line := line + 1
        value := value.push chars[index]!
        index := index + 1
      if index == chars.size then throw s!"line {startLine}: unterminated quoted name"
      index := index + 1
      tokens := tokens.push ⟨value, startLine, .quotedName⟩
    else if nameStart char || char.isDigit || (char == '.' && nameStart next) then
      let start := index
      index := index + 1
      while index < chars.size && namePart chars[index]! && chars[index]! != '«' do
        index := index + 1
      tokens := tokens.push ⟨String.ofList (chars.extract start index).toList, line, .name⟩
    else if stopBrace && char == '{' then
      braceDepth := braceDepth + 1
      tokens := tokens.push ⟨"{", line, .punctuation⟩
      index := index + 1
    else if stopBrace && char == '}' then
      if braceDepth == 0 then
        return (tokens, index, line)
      braceDepth := braceDepth - 1
      tokens := tokens.push ⟨"}", line, .punctuation⟩
      index := index + 1
    else
      tokens := tokens.push ⟨String.singleton char, line, .punctuation⟩
      index := index + 1
  return (tokens, index, line)

def scan (input : String) (cSource : Bool := false) : Except String (Array Token) := do
  let (tokens, _, _) ← scanCore input.toList.toArray cSource false 0 1
  return tokens

/-- Read a Lean identifier (possibly dotted and/or containing guillemet-quoted
components such as `Lean.«ofReduceBool»`, `«Blake3».«Rust»`, `«sorryAx»`)
starting at `tokens[start]`, returning `(normalizedName, nextIndex, hasQuoted)`. -/
def identAt (tokens : Array Token) (start : Nat) : Option (String × Nat × Bool) := Id.run do
  let some first := tokens[start]? | return none
  unless first.kind == .name || first.kind == .quotedName do return none
  let mut text := first.text
  let mut hasQuoted := first.kind == .quotedName
  let mut index := start + 1
  for _ in [start + 1:tokens.size] do
    let some next := tokens[index]? | break
    let continues := next.line == first.line &&
      ((text.endsWith "." && (next.kind == .name || next.kind == .quotedName)) ||
        (next.kind == .name && next.text.startsWith ".") ||
        (next.kind == .punctuation && next.text == "." &&
          (tokens[index + 1]?.map fun t => t.line == first.line &&
            (t.kind == .name || t.kind == .quotedName)).getD false))
    unless continues do break
    text := text ++ next.text
    if next.kind == .quotedName then hasQuoted := true
    index := index + 1
  return some (text, index, hasQuoted)

/-- The module name written from `tokens[start]` on, with the index after it: a
name, or a name with guillemet-quoted components (`«Blake3».Rust`,
`Blake3.«Rust»`, `«Blake3».«Rust»`), read whole and unquoted as Lean reads it. -/
private def moduleAt (tokens : Array Token) (start : Nat) : Option (String × Nat) :=
  (identAt tokens start).map fun (text, finish, _) => (text, finish)

/-- The import commands of `tokens`: for each, the index of its module name's
first token, the index after the name, and the module. An import command is the
keyword `import`, whatever modifiers come before it (`public import M`,
`meta import M`, `public meta import M` are read alike: the keyword is what is
matched), with `all` after it read through (`import all M`). A keyword `import`
followed by no module name yields `<unreadable import at line N>`, which names
no module, so every check that compares imports fails on it. -/
private def importCommands (tokens : Array Token) : List (Nat × Nat × String) := Id.run do
  let mut result := []
  for index in [:tokens.size] do
    let token := tokens[index]!
    unless token.kind == .name && token.text == "import" do continue
    let start := if (tokens[index + 1]?.map fun t => t.kind == .name && t.text == "all").getD false
      then index + 2 else index + 1
    match moduleAt tokens start with
    | some (mod, finish) => result := (start, finish, mod) :: result
    | none => result := (start, start, s!"<unreadable import at line {token.line}>") :: result
  return result.reverse

/-- The modules `tokens` imports, in order (`importCommands`). -/
def imports (tokens : Array Token) : List String :=
  (importCommands tokens).map (·.2.2)

/-- The names under the module root `root` that `tokens` spell outside their
import commands: each name token that is `root` or starts with `root.` (so
`open root` and `open root.M` count, as do qualified uses), and `root` for a
guillemet-quoted `«root»` (as in `«Blake3».Rust.x`). A name reached without
spelling `root` (after an `open` of it elsewhere, by generalized field
notation, through an instance) is not seen: this is a reading of the text. -/
def namesUnder (tokens : Array Token) (root : String) : List String := Id.run do
  let mut inImport := (List.replicate tokens.size false).toArray
  for (start, finish, _) in importCommands tokens do
    for index in [start:finish] do inImport := inImport.set! index true
  let mut result := []
  for index in [:tokens.size] do
    let token := tokens[index]!
    if inImport[index]! then continue
    if token.kind == .name && (token.text == root || token.text.startsWith (root ++ ".")) then
      result := token.text :: result
    else if token.kind == .quotedName && token.text == root then
      result := root :: result
  return result.reverse

/-- Strip a leading `_root_.` qualifier when present. -/
private def stripRootPrefix (name : String) : String :=
  if name.startsWith "_root_." then (name.drop 7).toString else name

/-- Names that declare an axiom, leave a proof hole, evaluate natively, or
bypass Lean's kernel: `axiom`, `sorry`, `sorryAx`, `native_decide`, `bv_decide`,
the axioms native evaluation rests on (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
`Lean.trustCompiler`), the qualified markers they reduce (`Lean.reduceBool`,
`Lean.reduceNat`), and kernel-bypass primitives (`skipKernelTC`,
`addDeclWithoutChecking`, `addDeclCore`). The bare `reduceBool`/`reduceNat` are
not refused: IxCC uses them as field names. -/
def forbiddenNames : List String :=
  ["axiom", "sorry", "sorryAx", "native_decide", "bv_decide",
   "ofReduceBool", "Lean.ofReduceBool", "ofReduceNat", "Lean.ofReduceNat",
   "trustCompiler", "Lean.trustCompiler", "Lean.reduceBool", "Lean.reduceNat",
   "skipKernelTC", "addDeclWithoutChecking", "addDeclCore"]

/-- Kernel-bypass identifiers forbidden even when qualified as a dotted suffix
(e.g. `debug.skipKernelTC`, `env.addDeclWithoutChecking`,
`Lean.Environment.addDeclCore`). -/
def forbiddenComponents : List String :=
  ["skipKernelTC", "addDeclWithoutChecking", "addDeclCore"]

private def isNameLike (token : Token) : Bool :=
  token.kind == .name || token.kind == .quotedName

/-- Whether `tokens[index]` is the flag `native` of a `decide` configuration,
`decide +native` (after any other `+flag`/`-flag`s, as in
`decide +kernel +native`), rather than an addition such as `x + native`. -/
private def decideNativeFlag (tokens : Array Token) (index : Nat) : Bool := Id.run do
  let text (i : Nat) : String := (tokens[i]?.map (·.text)).getD ""
  if index == 0 || text (index - 1) != "+" then return false
  -- walk back over the preceding `±flag` pairs to the tactic name
  let mut at_ := index - 1
  while at_ ≥ 2 && ["+", "-"].contains (text (at_ - 2)) &&
      (tokens[at_ - 1]?.map isNameLike).getD false do
    at_ := at_ - 2
  return at_ ≥ 1 && (tokens[at_ - 1]?.map isNameLike).getD false && text (at_ - 1) == "decide"

/-- Whether `tokens` starting at `rhsIdx` (immediately after `native :=`) is a
truthy boolean expression such as `true`, `(true)`, `Bool.true`, `!false`, or
`not false`. -/
private def isTruthyNativeRhs (tokens : Array Token) (rhsStart : Nat) : Bool := Id.run do
  let mut rhsIdx := rhsStart
  while (tokens[rhsIdx]?.map fun t => t.kind == .punctuation && t.text == "(").getD false do
    rhsIdx := rhsIdx + 1
  match identAt tokens rhsIdx with
  | some (rhs, _, _) =>
    let r := stripRootPrefix rhs
    r == "true" || r == "Bool.true" || r == "not"
  | none => (tokens[rhsIdx]?.map fun t => t.kind == .punctuation && t.text == "!").getD false

/-- If `tokens` starting at `afterDecide` has a `( ... )` configuration block
containing `native := <expr>` where `<expr>` is not literally `false`, return
the corresponding error detail. -/
private def decideConfigNativeError? (tokens : Array Token) (afterDecide : Nat) : Option String := Id.run do
  let text (i : Nat) : String := (tokens[i]?.map (·.text)).getD ""
  let mut i := afterDecide
  -- skip any preceding `+flag` / `-flag` pairs (e.g. `decide +kernel (config := ...)`)
  while i + 1 < tokens.size && ["+", "-"].contains (text i) &&
      (tokens[i + 1]?.map isNameLike).getD false do
    i := i + 2
  if text i != "(" then return none
  let mut depth : Nat := 1
  let mut j := i + 1
  while j < tokens.size && depth > 0 do
    let t := tokens[j]!
    if t.kind == .punctuation && t.text == "(" then
      depth := depth + 1; j := j + 1
    else if t.kind == .punctuation && t.text == ")" then
      depth := depth - 1; j := j + 1
    else if let some (nm, nextJ, _) := identAt tokens j then
      if stripRootPrefix nm == "native" && text nextJ == ":" && text (nextJ + 1) == "=" then
        let rhsIdx := nextJ + 2
        let isLiteralFalse :=
          match identAt tokens rhsIdx with
          | some (rhs, afterRhs, _) =>
            let r := stripRootPrefix rhs
            (r == "false" || r == "Bool.false") &&
              [",", "}", ")"].contains (text afterRhs)
          | none => false
        if !isLiteralFalse then
          if isTruthyNativeRhs tokens rhsIdx then
            return some "native := true is not allowed in checked sources"
          return some "decide config with native := is not allowed in checked sources"
      j := nextJ
    else
      j := j + 1
  return none

/-- Whether `tokens[index]` is a bare nullary inductive constructor declaration
`| sorryAx` on its own constructor branch (such as `PolicyDecline.sorryAx`). -/
private def isNullarySorryAxCtor (tokens : Array Token) (index nextIdx : Nat)
    (name : String) (hasQuoted : Bool) : Bool :=
  !hasQuoted && name == "sorryAx" && index > 0 &&
    tokens[index - 1]!.kind == .punctuation &&
    tokens[index - 1]!.text == "|" &&
    tokens[index - 1]!.line == tokens[index]!.line &&
    !(index ≥ 2 && tokens[index - 2]!.text == "|" &&
      tokens[index - 2]!.line == tokens[index]!.line) &&
    (tokens[nextIdx]?.map fun t => t.line != tokens[index]!.line || t.text == "|").getD true

/-- Refuse `axiom`, `sorry`, `sorryAx`, `bv_decide`, kernel-bypass primitives,
and every spelling of native evaluation the lexer can see (including
guillemet-quoted and `_root_.`-qualified forms): the names in `forbiddenNames`,
`forbiddenComponents`, `decide +native`, `decide (config := { native := ... })`,
and any `native := true` / `(true)` / `Bool.true` / `!false` / `not false`.
Comments and non-interpolated literals are not scanned. -/
def hygiene (tokens : Array Token) : Except String Unit := do
  let mut index := 0
  while index < tokens.size do
    let token := tokens[index]!
    if let some (name, nextIdx, hasQuoted) := identAt tokens index then
      let stripped := stripRootPrefix name
      if forbiddenNames.contains stripped then
        unless isNullarySorryAxCtor tokens index nextIdx name hasQuoted do
          throw s!"line {token.line}: {name} is not allowed in checked sources"
      if (stripped.splitOn ".").any forbiddenComponents.contains then
        throw s!"line {token.line}: {name} is not allowed in checked sources"
      if stripped == "native" then
        if decideNativeFlag tokens index then
          throw s!"line {token.line}: decide +native is not allowed in checked sources"
        if (tokens[nextIdx]?.map (·.text)) == some ":" &&
            (tokens[nextIdx + 1]?.map (·.text)) == some "=" &&
            isTruthyNativeRhs tokens (nextIdx + 2) then
          throw s!"line {token.line}: native := true is not allowed in checked sources"
      if stripped == "decide" then
        if let some msg := decideConfigNativeError? tokens nextIdx then
          throw s!"line {token.line}: {msg}"
      index := nextIdx
    else
      index := index + 1

/-- `hygiene` for a pure Lean dependency's closure file: the same, except that
an unquoted name right after `|` or `.` on the **same line** matching `axiom`,
`sorryAx`, or the specVersion 4 compiler-trust role constructors
(`trustCompiler`, `ofReduceBool`, `ofReduceNat`) is a data-type constructor
(such as `Ix.Kernel.Role.trustCompiler`), not an axiom declaration or a use of
Lean's compiler-trust axioms; every `axiom` declaration and every bare,
guillemet-quoted, `_root_.`-qualified, or `Lean.*`-qualified compiler-trust
name remains refused. -/
def hygieneDependency (tokens : Array Token) : Except String Unit :=
  let keep := (List.range tokens.size).filter fun index =>
    !(tokens[index]!.kind == .name &&
      ["axiom", "sorryAx", "trustCompiler", "ofReduceBool", "ofReduceNat"].contains tokens[index]!.text &&
      index > 0 &&
      tokens[index - 1]!.line == tokens[index]!.line &&
      ["|", "."].contains tokens[index - 1]!.text &&
      !(index ≥ 2 && tokens[index - 1]!.text == "|" &&
        tokens[index - 2]!.text == "|" && tokens[index - 2]!.line == tokens[index]!.line))
  hygiene (keep.toArray.map (tokens[·]!))

/-- Keywords after which a declaration's name follows. -/
private def declarationKeywords : List String :=
  ["def", "theorem", "lemma", "abbrev", "instance", "structure", "class", "inductive",
   "opaque", "axiom", "example"]

/-- Commands that can only stand between declarations: a `native_decide` after
one belongs to no declaration. -/
private def commandKeywords : List String :=
  ["variable", "universe", "deriving", "initialize", "builtin_initialize", "macro", "syntax",
   "elab", "notation", "macro_rules", "elab_rules"]

/-- Modifiers allowed between `@[...]` and the declaration keyword. -/
private def modifier (name : String) : Bool :=
  ["public", "protected", "private", "unsafe", "partial", "noncomputable", "meta"].contains name

/-- Lean top-level command/modifier starters that terminate a multi-line
`attribute [...] target₁ target₂ ...` target list. -/
private def commandStarters : List String :=
  declarationKeywords ++ commandKeywords ++
  ["public", "protected", "private", "unsafe", "partial", "noncomputable", "meta",
   "scoped", "local", "namespace", "section", "end", "mutual", "open", "export",
   "import", "module", "attribute", "set_option", "variables", "universes",
   "coinductive", "class_inductive", "infix", "infixl", "infixr", "prefix", "postfix",
   "declare_syntax_cat", "register_simp_attr", "run_cmd", "run_meta", "run_elab",
   "add_decl_doc", "unseal", "seal", "init_quot", "builtin_simproc", "simproc",
   "dsimproc", "gen_injective_theorems", "recommended_spelling"]

/-- Each `native_decide` tactic of `tokens` with the declaration whose text holds
it (in its signature, as a default argument's proof, or in its body) and its
line. The declaration is the one the nearest preceding declaration keyword
names, qualified by the open namespaces (`namespace A.B` … `end A.B`;
`section` and `mutual` open scopes that add none; `_root_.` names are not
qualified). Guillemet-quoted identifiers are normalized. A `native_decide` that
no named declaration holds (in an `example`, an anonymous `instance`, after a
command such as `variable`), and an `end` that closes no scope, are refused. -/
def nativeDecideSites (tokens : Array Token) : Except String (List (String × Nat)) := do
  let mut scopes : List (Option String) := []
  let mut current : Option String := none
  let mut result := []
  let mut index := 0
  while index < tokens.size do
    let token := tokens[index]!
    let some (text, nextIdx, hasQuoted) := identAt tokens index
      | do index := index + 1; continue
    let stripped := stripRootPrefix text
    let nextIdent := identAt tokens nextIdx
    let sameLine := (tokens[nextIdx]?.map fun t => t.line == token.line && isNameLike t).getD false
    if !hasQuoted && text == "namespace" then
      let some (name, afterName, _) := nextIdent | throw s!"line {token.line}: namespace without a name"
      scopes := (name.splitOn ".").reverse.map some ++ scopes
      current := none
      index := afterName
    else if !hasQuoted && (text == "section" || text == "mutual") then
      scopes := none :: scopes
      current := none
      index := nextIdx
    else if !hasQuoted && text == "end" then
      let (count, afterEnd) := if sameLine then
        match nextIdent with
        | some (name, afterName, _) => ((name.splitOn ".").length, afterName)
        | none => (1, nextIdx)
      else (1, nextIdx)
      if scopes.length < count then throw s!"line {token.line}: end closes no open scope"
      scopes := scopes.drop count
      current := none
      index := afterEnd
    else if stripped == "native_decide" then
      let some name := current
        | throw s!"line {token.line}: native_decide outside a named declaration"
      result := (name, token.line) :: result
      index := nextIdx
    else if !hasQuoted && commandKeywords.contains text then
      current := none
      index := nextIdx
    else if !hasQuoted && declarationKeywords.contains text then
      match nextIdent with
      | some (name, afterName, _) =>
        if !name.startsWith "." then
          if name.startsWith "_root_." then
            current := some (name.drop 7).toString
          else
            current := some (".".intercalate ((scopes.filterMap id).reverse ++ [name]))
          index := afterName
        else
          current := none
          index := nextIdx
      | none =>
        current := none
        index := nextIdx
    else
      index := nextIdx
  return result.reverse

/-- The hygiene of a pure Lean dependency's closure file, with each
`native_decide` it holds as `(declaration, line)` (`nativeDecideSites`), for the
dependency's reviewed inventory (`native_decide_sites`) to account for. Every
other name and spelling `hygieneDependency` refuses is still refused here,
`decide +native` and `Lean.ofReduceBool` among them. -/
def dependencyHygiene (tokens : Array Token) : Except String (List (String × Nat)) := do
  let isTactic (token : Token) : Bool :=
    isNameLike token && stripRootPrefix token.text == "native_decide"
  hygieneDependency (tokens.filter (!isTactic ·))
  if tokens.any isTactic then nativeDecideSites tokens else return []

/-- Find the index of the `]` matching the `[` at `openIdx`, tracking nested
`[`/`]` pairs (so e.g. `@[simp [foo], extern "sym"]` does not terminate early). -/
private def findMatchingBracket (tokens : Array Token) (openIdx : Nat) : Option Nat := Id.run do
  let mut depth : Nat := 1
  let mut i := openIdx + 1
  while i < tokens.size do
    let t := tokens[i]!
    if t.kind == .punctuation && t.text == "[" then
      depth := depth + 1
    else if t.kind == .punctuation && t.text == "]" then
      depth := depth - 1
      if depth == 0 then return some i
    i := i + 1
  return none

/-- Count normalized identifier occurrences equal to `target` anywhere inside
`[...]` (bracket depth > 0). -/
private def bracketedNameCount (tokens : Array Token) (target : String) : Nat := Id.run do
  let mut depth : Nat := 0
  let mut count : Nat := 0
  let mut i := 0
  while i < tokens.size do
    let t := tokens[i]!
    if t.kind == .punctuation && t.text == "[" then
      depth := depth + 1; i := i + 1
    else if t.kind == .punctuation && t.text == "]" then
      if depth > 0 then depth := depth - 1
      i := i + 1
    else if let some (nm, nextI, _) := identAt tokens i then
      if depth > 0 && stripRootPrefix nm == target then
        count := count + 1
      i := nextI
    else
      i := i + 1
  return count

/-- Count all normalized identifier occurrences equal to `target` in `tokens`. -/
private def allNameCount (tokens : Array Token) (target : String) : Nat := Id.run do
  let mut count : Nat := 0
  let mut i := 0
  while i < tokens.size do
    if let some (nm, nextI, _) := identAt tokens i then
      if stripRootPrefix nm == target then count := count + 1
      i := nextI
    else
      i := i + 1
  return count

/-- Collect positions (starting index and next index) inside `attributes` whose
normalized identifier equals `target`. -/
private def attrNamePositions (attributes : Array Token) (target : String) : List (Nat × Nat) := Id.run do
  let mut pos : List (Nat × Nat) := []
  let mut i := 0
  while i < attributes.size do
    if let some (nm, nextI, _) := identAt attributes i then
      if stripRootPrefix nm == target then pos := (i, nextI) :: pos
      i := nextI
    else
      i := i + 1
  return pos.reverse

/-- Read one target identifier of an `attribute [...] target₁ target₂ ...`
command (possibly across multiple lines, normalizing `.quotedName`), stopping
before any unquoted top-level command starter keyword. -/
private def attributeTargetAt (tokens : Array Token) (idx : Nat) : Option (String × Nat) :=
  match identAt tokens idx with
  | some (name, nextIdx, hasQuoted) =>
    if (!hasQuoted && commandStarters.contains name) || name.startsWith "." then none
    else some (name, nextIdx)
  | none => none

def externs (tokens : Array Token) : Except String (List (String × String)) := do
  let mut declarations := []
  let mut seen := 0
  for index in [:tokens.size] do
    let token := tokens[index]!
    if token.kind == .literal then continue
    let isAttrStart :=
      ((token.kind == .punctuation && token.text == "@") ||
        (isNameLike token && token.text == "attribute")) &&
      (tokens[index + 1]?.map fun t => t.kind == .punctuation && t.text == "[").getD false
    unless isAttrStart do continue
    let some finish := findMatchingBracket tokens (index + 1)
      | throw s!"line {token.line}: unterminated attribute"
    let attributes := tokens.extract (index + 2) finish
    let positions := attrNamePositions attributes "extern"
    if positions.isEmpty then continue
    if positions.length != 1 then throw s!"line {token.line}: ambiguous extern attributes"
    let mut symbolAt := positions.head!.2
    if (attributes[symbolAt]?.map fun t => t.kind == .name && t.text.toList.all Char.isDigit).getD false then
      symbolAt := symbolAt + 1
    let some symbol := attributes[symbolAt]?
      | throw s!"line {token.line}: extern has no explicit symbol"
    if symbol.kind != .literal || symbol.text.isEmpty || symbol.text.contains '\\' then
      throw s!"line {token.line}: extern needs an auditable explicit symbol string"
    let mut after := finish + 1
    if token.text == "@" then
      while after < tokens.size && tokens[after]!.kind == .name && modifier tokens[after]!.text do
        after := after + 1
      if !["opaque", "def"].contains (tokens[after]?.map (·.text) |>.getD "") then
        throw s!"line {token.line}: unrecognized extern declaration form"
      let some (name, _) := identAt tokens (after + 1)
        | throw s!"line {token.line}: missing extern declaration"
      if name.startsWith "." then throw s!"line {token.line}: unsupported extern name"
      declarations := (symbol.text, name) :: declarations
      seen := seen + 1
    else
      let mut count := 0
      while after < tokens.size do
        match attributeTargetAt tokens after with
        | some (name, nextIdx) =>
          declarations := (symbol.text, name) :: declarations
          count := count + 1
          after := nextIdx
        | none => break
      if after < tokens.size && tokens[after]!.line == tokens[finish]!.line then
        let isCmd := tokens[after]!.kind == .name && commandStarters.contains tokens[after]!.text
        if !isCmd || count == 0 then
          throw s!"line {token.line}: unsupported attribute-command target"
      if count == 0 then throw s!"line {token.line}: missing attribute-command names"
      seen := seen + 1
  let spelled := bracketedNameCount tokens "extern"
  unless spelled == seen do
    throw s!"{spelled - seen} extern outside an attribute the inventory reads"
  return declarations.reverse

/-- Every `implemented_by` substitution a source declares, as
`(declaration, implementation)`: compiled code runs `implementation` where it
would run `declaration`. Both the `@[… implemented_by impl …]` attribute on a
`def` or `opaque` and the `attribute [implemented_by impl] decl ...` command
(including multi-line target lists and guillemet-quoted names) are read; any
other spelling of `implemented_by` outside comments and literals is refused, so
no substitution escapes the inventory. -/
def implementedBys (tokens : Array Token) : Except String (List (String × String)) := do
  let mut result : List (String × String) := []
  let mut seen := 0
  for index in [:tokens.size] do
    let token := tokens[index]!
    if token.kind == .literal then continue
    let isAttrStart :=
      ((token.kind == .punctuation && token.text == "@") ||
        (isNameLike token && token.text == "attribute")) &&
      (tokens[index + 1]?.map fun t => t.kind == .punctuation && t.text == "[").getD false
    unless isAttrStart do continue
    let some finish := findMatchingBracket tokens (index + 1)
      | throw s!"line {token.line}: unterminated attribute"
    let attributes := tokens.extract (index + 2) finish
    let positions := attrNamePositions attributes "implemented_by"
    if positions.isEmpty then continue
    if positions.length != 1 then throw s!"line {token.line}: ambiguous implemented_by attributes"
    let targetAt := positions.head!.2
    let some (target, _) := identAt attributes targetAt
      | throw s!"line {token.line}: implemented_by names no implementation"
    if target.startsWith "." then throw s!"line {token.line}: unsupported implemented_by target"
    if token.text == "@" then
      let mut after := finish + 1
      while after < tokens.size && tokens[after]!.kind == .name && modifier tokens[after]!.text do
        after := after + 1
      unless ["def", "opaque"].contains ((tokens[after]?.map (·.text)).getD "") do
        throw s!"line {token.line}: implemented_by not on a def or an opaque"
      let some (name, _) := identAt tokens (after + 1)
        | throw s!"line {token.line}: missing declaration"
      if name.startsWith "." then throw s!"line {token.line}: unsupported declaration name"
      result := (name, target) :: result
      seen := seen + 1
    else
      let mut after := finish + 1
      let mut count := 0
      while after < tokens.size do
        match attributeTargetAt tokens after with
        | some (name, nextIdx) =>
          result := (name, target) :: result
          count := count + 1
          after := nextIdx
        | none => break
      if after < tokens.size && tokens[after]!.line == tokens[finish]!.line then
        let isCmd := tokens[after]!.kind == .name && commandStarters.contains tokens[after]!.text
        if !isCmd || count == 0 then
          throw s!"line {token.line}: unsupported attribute-command target"
      if count == 0 then throw s!"line {token.line}: missing attribute-command names"
      seen := seen + 1
  let spelled := allNameCount tokens "implemented_by"
  unless spelled == seen do
    throw s!"{spelled - seen} implemented_by outside an attribute the inventory reads"
  return result.reverse

/-- A `@[csimp]` theorem as its source states it: compiled code calls
`replacement` wherever it would call `replaces`. -/
structure CSimp where
  name : String
  replaces : String
  replacement : String
  deriving BEq, Repr

/-- The replacement stated by the theorem whose name starts at `index`:
the statement must be `: @f = @g :=` (no binders; each `@` optional;
guillemet-quoted identifiers normalized). -/
private def csimpStatement (tokens : Array Token) (index : Nat) : Except String (String × String) :=
  let text (i : Nat) : String := (tokens[i]?.map (·.text)).getD ""
  let skipAt (i : Nat) : Nat := if text i == "@" then i + 1 else i
  let line := (tokens[index]?.map (·.line)).getD 0
  match identAt tokens index with
  | none => .error s!"line {line}: missing csimp theorem name"
  | some (thmName, afterName, _) =>
    if text afterName != ":" then
      .error s!"line {line}: csimp theorem {thmName} is not stated as `: @f = @g :=`"
    else
      match identAt tokens (skipAt (afterName + 1)) with
      | some (lhs, afterLhs, _) =>
        if text afterLhs != "=" then
          .error s!"line {line}: csimp theorem {thmName} is not stated as `: @f = @g :=`"
        else
          match identAt tokens (skipAt (afterLhs + 1)) with
          | some (rhs, afterRhs, _) =>
            if text afterRhs == ":" && text (afterRhs + 1) == "=" then
              .ok (lhs, rhs)
            else
              .error s!"line {line}: csimp theorem {thmName} is not stated as `: @f = @g :=`"
          | none => .error s!"line {line}: csimp theorem {thmName} is not stated as `: @f = @g :=`"
      | none => .error s!"line {line}: csimp theorem {thmName} is not stated as `: @f = @g :=`"

/-- Every `@[csimp]` theorem and `attribute [csimp]` command, with the
replacement each states. A csimp attribute that is not on a theorem of this
source stated as `: @f = @g :=`, or any `csimp` inside `[...]` that escapes the
inventory, is refused. -/
def csimps (tokens : Array Token) : Except String (List CSimp) := do
  let mut result : List CSimp := []
  let mut seen := 0
  for index in [:tokens.size] do
    let token := tokens[index]!
    if token.kind == .literal then continue
    let isAttrStart :=
      ((token.kind == .punctuation && token.text == "@") ||
        (isNameLike token && token.text == "attribute")) &&
      (tokens[index + 1]?.map fun t => t.kind == .punctuation && t.text == "[").getD false
    unless isAttrStart do continue
    let some finish := findMatchingBracket tokens (index + 1)
      | throw s!"line {token.line}: unterminated attribute"
    let attributes := tokens.extract (index + 2) finish
    let positions := attrNamePositions attributes "csimp"
    if positions.isEmpty then continue
    if positions.length != 1 then throw s!"line {token.line}: ambiguous csimp attributes"
    if token.text == "@" then
      let mut after := finish + 1
      while after < tokens.size && tokens[after]!.kind == .name && modifier tokens[after]!.text do
        after := after + 1
      unless (tokens[after]?.map (·.text)) == some "theorem" do
        throw s!"line {token.line}: csimp attribute not on a theorem"
      let some (thmName, _, _) := identAt tokens (after + 1)
        | throw s!"line {token.line}: missing csimp theorem name"
      let (replaces, replacement) ← csimpStatement tokens (after + 1)
      result := ⟨thmName, replaces, replacement⟩ :: result
      seen := seen + 1
    else
      let mut after := finish + 1
      let mut count := 0
      while after < tokens.size do
        match attributeTargetAt tokens after with
        | some (name, nextIdx) =>
          let declared := (List.range tokens.size).find? fun i =>
            tokens[i]!.kind == .name && tokens[i]!.text == "theorem" &&
              ((identAt tokens (i + 1)).map (·.1) == some name)
          let some declared := declared
            | throw s!"line {token.line}: csimp attribute on {name}, which is not a theorem of this source"
          let (replaces, replacement) ← csimpStatement tokens (declared + 1)
          result := ⟨name, replaces, replacement⟩ :: result
          count := count + 1
          after := nextIdx
        | none => break
      if after < tokens.size && tokens[after]!.line == tokens[finish]!.line then
        let isCmd := tokens[after]!.kind == .name && commandStarters.contains tokens[after]!.text
        if !isCmd || count == 0 then
          throw s!"line {token.line}: unsupported csimp attribute target"
      if count == 0 then throw s!"line {token.line}: missing csimp attribute names"
      seen := seen + 1
  let spelled := bracketedNameCount tokens "csimp"
  unless spelled == seen do
    throw s!"{spelled - seen} csimp outside an attribute the inventory reads"
  return result.reverse

/-! ## Nix attribute names

The trust ledger compares the checks `nix/checks.nix` defines with its
recorded list. This lexer reads only what that needs: the attribute names
bound directly in the attribute sets of the file's body. -/

/-- A context of the Nix lexer: code (inside an antiquotation, with its own
brace depth), a `"…"` string or an `''…''` string. -/
private inductive NixFrame where
  | code (depth : Nat)
  | quoted
  | indented
  deriving Inhabited

/-- A token of the Nix file outside every string and antiquotation, with the
brace depth of its context (a `{` carries the depth outside it, a `}` the
depth after it). Strings and antiquotations appear as the tokens `"`, `''` and
`${`, so a binding cannot hide in one. -/
structure NixToken where
  text : String
  depth : Nat
  line : Nat
  deriving Repr, Inhabited

private def nixIdStart (char : Char) : Bool := char.isAlpha || char == '_'
private def nixIdPart (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '\'' || char == '-'

def nixTokens (input : String) : Except String (Array NixToken) := do
  let chars := input.toList.toArray
  let at_ (i : Nat) : Char := chars[i]?.getD '\x00'
  let mut tokens : Array NixToken := #[]
  let mut stack : List NixFrame := []
  let mut depth := 0
  let mut index := 0
  let mut line := 1
  while index < chars.size do
    let char := at_ index
    let next := at_ (index + 1)
    if char == '\n' then line := line + 1
    match stack with
    | .quoted :: rest =>
      if char == '\\' then index := index + 2
      else if char == '$' && next == '$' then index := index + 2
      else if char == '$' && next == '{' then
        stack := .code 0 :: stack
        index := index + 2
      else if char == '"' then
        stack := rest
        index := index + 1
      else index := index + 1
    | .indented :: rest =>
      if char == '\'' && next == '\'' then
        let third := at_ (index + 2)
        if third == '\'' || third == '$' then index := index + 3
        else if third == '\\' then index := index + 4
        else
          stack := rest
          index := index + 2
      else if char == '$' && next == '$' then index := index + 2
      else if char == '$' && next == '{' then
        stack := .code 0 :: stack
        index := index + 2
      else index := index + 1
    | frame =>
      let top := frame.isEmpty
      if char.isWhitespace then index := index + 1
      else if char == '#' then
        while index < chars.size && at_ index != '\n' do index := index + 1
      else if char == '/' && next == '*' then
        index := index + 2
        while index < chars.size && !(at_ index == '*' && at_ (index + 1) == '/') do
          if at_ index == '\n' then line := line + 1
          index := index + 1
        if index ≥ chars.size then throw s!"line {line}: unterminated comment"
        index := index + 2
      else if char == '"' then
        if top then tokens := tokens.push ⟨"\"", depth, line⟩
        stack := .quoted :: stack
        index := index + 1
      else if char == '\'' && next == '\'' then
        if top then tokens := tokens.push ⟨"''", depth, line⟩
        stack := .indented :: stack
        index := index + 2
      else if char == '$' && next == '{' then
        if top then tokens := tokens.push ⟨"${", depth, line⟩
        stack := .code 0 :: stack
        index := index + 2
      else if char == '{' then
        match frame with
        | .code d :: rest => stack := .code (d + 1) :: rest
        | _ =>
          tokens := tokens.push ⟨"{", depth, line⟩
          depth := depth + 1
        index := index + 1
      else if char == '}' then
        match frame with
        | .code 0 :: rest => stack := rest
        | .code (d + 1) :: rest => stack := .code d :: rest
        | _ =>
          if depth == 0 then throw s!"line {line}: unbalanced closing brace"
          depth := depth - 1
          tokens := tokens.push ⟨"}", depth, line⟩
        index := index + 1
      else if nixIdStart char then
        let start := index
        while index < chars.size && nixIdPart (at_ index) do index := index + 1
        if top then tokens := tokens.push ⟨String.ofList (chars.extract start index).toList, depth, line⟩
      else if ["==", "!=", "<=", ">=", "//", "++", "->", "&&", "||"].contains
          (String.ofList [char, next]) then
        if top then tokens := tokens.push ⟨String.ofList [char, next], depth, line⟩
        index := index + 2
      else
        if top then tokens := tokens.push ⟨String.singleton char, depth, line⟩
        index := index + 1
  unless stack.isEmpty do throw "unterminated string or antiquotation"
  unless depth == 0 do throw "unbalanced braces"
  return tokens

/-- The attribute names bound directly in the attribute sets of the body of a
Nix file of the form `{ args }: let … in { … } // … { … }`: the body follows
the `in` that closes the first top-level `let`, and each `{` opened at depth 0
there starts a set whose bindings are `name = …;` or `inherit [(…)] names;`.
Anything else in a binding position (a string or antiquoted name, an
attribute path) is refused, so no binding escapes the inventory. -/
def nixBodyAttributes (input : String) : Except String (List String) := do
  let tokens ← nixTokens input
  let text (i : Nat) : String := (tokens[i]?.map (·.text)).getD ""
  let mut lets := 0
  let mut start := none
  for i in [:tokens.size] do
    if tokens[i]!.depth == 0 && text i == "let" then lets := lets + 1
    if tokens[i]!.depth == 0 && text i == "in" && lets > 0 then
      lets := lets - 1
      if lets == 0 then
        start := some (i + 1)
        break
  let some first := start | throw "no top-level `let … in` before the attribute sets"
  let mut names : List String := []
  let mut binding := false
  let mut i := first
  while i < tokens.size do
    let token := tokens[i]!
    if token.depth == 0 then
      -- `{` opens a set; its `}` (depth 0 after it) closes it
      binding := token.text == "{"
      i := i + 1
    else if token.depth == 1 && binding then
      if token.text == "}" then
        binding := false
        i := i + 1
      else if token.text == "inherit" then
        i := i + 1
        while i < tokens.size && text i != ";" do
          if text i == "(" then
            let mut parens := 0
            while i < tokens.size && !(text i == ")" && parens == 1) do
              if text i == "(" then parens := parens + 1
              if text i == ")" then parens := parens - 1
              i := i + 1
            i := i + 1
          else if (text i).toList.headD ' ' |> nixIdStart then
            names := names ++ [text i]
            i := i + 1
          else throw s!"line {tokens[i]!.line}: unsupported inherit"
        i := i + 1
      else if nixIdStart ((token.text.toList.headD ' ')) && text (i + 1) == "=" then
        names := names ++ [token.text]
        binding := false
        i := i + 2
      else throw s!"line {token.line}: unsupported binding `{token.text}` in an attribute set"
    else
      if token.depth == 1 && token.text == ";" then binding := true
      i := i + 1
  return names

def cExports (tokens : Array Token) : Except String (List String) := do
  let mut result := []
  for index in [:tokens.size] do
    if tokens[index]!.kind != .name || tokens[index]!.text != "LEAN_EXPORT" then continue
    let mut after := index + 1
    while after < tokens.size && !["(", ";", "{", "}"].contains tokens[after]!.text do
      after := after + 1
    if after == tokens.size || tokens[after]!.text != "(" || after == index + 1 ||
        tokens[after - 1]!.kind != .name then
      throw s!"line {tokens[index]!.line}: unsupported C export"
    result := tokens[after - 1]!.text :: result
  return result.reverse

end IxCC.Tools.SourceScan
