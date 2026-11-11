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

def scan (input : String) (cSource : Bool := false) : Except String (Array Token) := do
  let chars := input.toList.toArray
  let mut tokens := #[]
  let mut index := 0
  let mut line := 1
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
    else if char == '"' || (char == '\'' &&
        (cSource || next == '\\' || chars[index + 2]? == some '\'')) then
      let startLine := line
      let delimiter := char
      let mut value := ""
      let mut ended := false
      index := index + 1
      while index < chars.size && !ended do
        let current := chars[index]!
        if current == delimiter then
          ended := true
          index := index + 1
        else if current == '\\' then
          if index + 1 ≥ chars.size then throw s!"line {startLine}: dangling literal escape"
          value := (value.push current).push chars[index + 1]!
          index := index + 2
        else
          if current == '\n' then line := line + 1
          value := value.push current
          index := index + 1
      if !ended then throw s!"line {startLine}: unterminated literal"
      tokens := tokens.push ⟨value, startLine, .literal⟩
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
    else
      tokens := tokens.push ⟨String.singleton char, line, .punctuation⟩
      index := index + 1
  return tokens

def imports (tokens : Array Token) : List String := Id.run do
  let mut result := []
  for index in [:tokens.size] do
    if tokens[index]!.text == "import" && tokens[index]!.kind == .name then
      -- `import all M` (module system) names M
      let skip := if tokens[index + 1]?.map (·.text) == some "all" then 2 else 1
      if let some next := tokens[index + skip]? then
        if next.kind == .name then result := next.text :: result
  return result.reverse

/-- Names that declare an axiom, leave a proof hole, or evaluate natively: the
`native_decide` tactic and the axioms native evaluation rests on
(`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`) and the
qualified markers they reduce (`Lean.reduceBool`, `Lean.reduceNat`). The bare
`reduceBool`/`reduceNat` are not refused: IxCC uses them as field names. -/
def forbiddenNames : List String :=
  ["axiom", "sorry", "native_decide",
   "ofReduceBool", "Lean.ofReduceBool", "ofReduceNat", "Lean.ofReduceNat",
   "trustCompiler", "Lean.trustCompiler", "Lean.reduceBool", "Lean.reduceNat"]

/-- Whether `tokens[index]` is the flag `native` of a `decide` configuration,
`decide +native` (after any other `+flag`/`-flag`s, as in
`decide +kernel +native`), rather than an addition such as `x + native`. -/
private def decideNativeFlag (tokens : Array Token) (index : Nat) : Bool := Id.run do
  let text (i : Nat) : String := (tokens[i]?.map (·.text)).getD ""
  if index == 0 || text (index - 1) != "+" then return false
  -- walk back over the preceding `±flag` pairs to the tactic name
  let mut at_ := index - 1
  while at_ ≥ 2 && ["+", "-"].contains (text (at_ - 2)) &&
      (tokens[at_ - 1]?.map (·.kind == .name)).getD false do
    at_ := at_ - 2
  return at_ ≥ 1 && text (at_ - 1) == "decide"

/-- Refuse `axiom`, `sorry` and every spelling of native evaluation the lexer
can see: the names in `forbiddenNames`, `decide +native` and a configuration
field `native := true` (`decide (config := { native := true })`). Comments and
literals are not scanned. -/
def hygiene (tokens : Array Token) : Except String Unit := do
  for index in [:tokens.size] do
    let token := tokens[index]!
    if token.kind != .name then continue
    if forbiddenNames.contains token.text then
      throw s!"line {token.line}: {token.text} is not allowed in checked sources"
    if token.text == "native" then
      if decideNativeFlag tokens index then
        throw s!"line {token.line}: decide +native is not allowed in checked sources"
      if (tokens[index + 1]?.map (·.text)) == some ":" &&
          (tokens[index + 2]?.map (·.text)) == some "=" &&
          (tokens[index + 3]?.map (·.text)) == some "true" then
        throw s!"line {token.line}: native := true is not allowed in checked sources"

/-- `hygiene` for a pure Lean dependency's closure file: the same, except that the
name `axiom` right after `|` or `.` is a constructor named `axiom` (declared, or
referred to with a leading dot), as a dependency's data types may have one; an
`axiom` declaration, with or without modifiers and attributes, never follows
either, so it is still refused. -/
def hygieneDependency (tokens : Array Token) : Except String Unit :=
  let keep := (List.range tokens.size).filter fun index =>
    !(tokens[index]!.kind == .name && tokens[index]!.text == "axiom" &&
      index > 0 && ["|", "."].contains tokens[index - 1]!.text)
  hygiene (keep.toArray.map (tokens[·]!))

private def modifier (name : String) : Bool :=
  ["public", "protected", "private", "unsafe", "partial", "noncomputable", "meta"].contains name

def externs (tokens : Array Token) : Except String (List (String × String)) := do
  let mut declarations := []
  for index in [:tokens.size] do
    let token := tokens[index]!
    if token.kind == .literal then continue
    if (token.text == "@" || token.text == "attribute") &&
        (tokens[index + 1]?.map (·.text)) == some "[" then
      let mut finish := index + 2
      while finish < tokens.size && tokens[finish]!.text != "]" do finish := finish + 1
      if finish == tokens.size then throw s!"line {token.line}: unterminated attribute"
      let attributes := tokens.extract (index + 2) finish
      let positions := (List.range attributes.size).filter fun pos =>
        attributes[pos]!.kind == .name && attributes[pos]!.text == "extern"
      if positions.isEmpty then continue
      if positions.length != 1 then throw s!"line {token.line}: ambiguous extern attributes"
      let mut symbolAt := positions.head! + 1
      if (attributes[symbolAt]?.map (fun t => t.text.toList.all Char.isDigit)).getD false then
        symbolAt := symbolAt + 1
      let some symbol := attributes[symbolAt]?
        | throw s!"line {token.line}: extern has no explicit symbol"
      if symbol.kind != .literal || symbol.text.isEmpty || symbol.text.contains '\\' then
        throw s!"line {token.line}: extern needs an auditable explicit symbol string"
      let mut after := finish + 1
      if token.text == "@" then
        while after < tokens.size && modifier tokens[after]!.text do after := after + 1
        if !["opaque", "def"].contains (tokens[after]?.map (·.text) |>.getD "") then
          throw s!"line {token.line}: unrecognized extern declaration form"
        let some name := tokens[after + 1]? | throw s!"line {token.line}: missing extern declaration"
        if name.kind != .name then throw s!"line {token.line}: unsupported extern name"
        declarations := (symbol.text, name.text) :: declarations
      else
        let mut count := 0
        while after < tokens.size && tokens[after]!.line == tokens[finish]!.line &&
            tokens[after]!.kind == .name do
          declarations := (symbol.text, tokens[after]!.text) :: declarations
          count := count + 1
          after := after + 1
        if after < tokens.size && tokens[after]!.line == tokens[finish]!.line then
          throw s!"line {token.line}: unsupported attribute-command target"
        if count == 0 then throw s!"line {token.line}: missing attribute-command names"
  return declarations.reverse

/-- Every `implemented_by` substitution a source declares, as
`(declaration, implementation)`: compiled code runs `implementation` where it
would run `declaration`. Both the `@[… implemented_by impl …]` attribute on a
`def` or `opaque` and the `attribute [implemented_by impl] decl` command are
read; any other spelling of `implemented_by` outside comments and literals is
refused, so no substitution escapes the inventory. -/
def implementedBys (tokens : Array Token) : Except String (List (String × String)) := do
  let mut result : List (String × String) := []
  let mut seen := 0
  for index in [:tokens.size] do
    let token := tokens[index]!
    if token.kind == .literal then continue
    unless (token.text == "@" || token.text == "attribute") &&
        (tokens[index + 1]?.map (·.text)) == some "[" do continue
    let mut finish := index + 2
    while finish < tokens.size && tokens[finish]!.text != "]" do finish := finish + 1
    if finish == tokens.size then throw s!"line {token.line}: unterminated attribute"
    let attributes := tokens.extract (index + 2) finish
    let positions := (List.range attributes.size).filter fun pos =>
      attributes[pos]!.kind == .name && attributes[pos]!.text == "implemented_by"
    if positions.isEmpty then continue
    if positions.length != 1 then throw s!"line {token.line}: ambiguous implemented_by attributes"
    let some target := attributes[positions.head! + 1]?
      | throw s!"line {token.line}: implemented_by names no implementation"
    if target.kind != .name then throw s!"line {token.line}: unsupported implemented_by target"
    if token.text == "@" then
      let mut after := finish + 1
      while after < tokens.size && modifier tokens[after]!.text do after := after + 1
      unless ["def", "opaque"].contains ((tokens[after]?.map (·.text)).getD "") do
        throw s!"line {token.line}: implemented_by not on a def or an opaque"
      let some name := tokens[after + 1]? | throw s!"line {token.line}: missing declaration"
      if name.kind != .name then throw s!"line {token.line}: unsupported declaration name"
      result := (name.text, target.text) :: result
      seen := seen + 1
    else
      let mut after := finish + 1
      let mut count := 0
      while after < tokens.size && tokens[after]!.line == tokens[finish]!.line &&
          tokens[after]!.kind == .name do
        result := (tokens[after]!.text, target.text) :: result
        count := count + 1
        after := after + 1
      if count == 0 then throw s!"line {token.line}: missing attribute-command names"
      seen := seen + 1
  let spelled := tokens.toList.countP fun t => t.kind == .name && t.text == "implemented_by"
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

/-- The replacement stated by the theorem whose name is the token at `index`:
the statement must be `: @f = @g :=` (no binders; each `@` optional). -/
private def csimpStatement (tokens : Array Token) (index : Nat) : Except String (String × String) :=
  let text (i : Nat) : String := (tokens[i]?.map (·.text)).getD ""
  let isName (i : Nat) : Bool := (tokens[i]?.map (fun token => token.kind == Kind.name)).getD false
  let skipAt (i : Nat) : Nat := if text i == "@" then i + 1 else i
  let lhs := skipAt (index + 2)
  let rhs := skipAt (lhs + 2)
  if text (index + 1) == ":" && isName lhs && text (lhs + 1) == "=" && isName rhs &&
      text (rhs + 1) == ":" && text (rhs + 2) == "=" then
    .ok (text lhs, text rhs)
  else
    .error s!"line {(tokens[index]?.map (·.line)).getD 0}: csimp theorem {text index} is not stated as `: @f = @g :=`"

/-- Every `@[csimp]` theorem and `attribute [csimp]` command, with the
replacement each states. A csimp attribute that is not on a theorem of this
source stated as `: @f = @g :=` is refused. -/
def csimps (tokens : Array Token) : Except String (List CSimp) := do
  let mut result : List CSimp := []
  for index in [:tokens.size] do
    let token := tokens[index]!
    if token.kind == .literal then continue
    unless (token.text == "@" || token.text == "attribute") &&
        (tokens[index + 1]?.map (·.text)) == some "[" do continue
    let mut finish := index + 2
    while finish < tokens.size && tokens[finish]!.text != "]" do finish := finish + 1
    if finish == tokens.size then throw s!"line {token.line}: unterminated attribute"
    let attributes := tokens.extract (index + 2) finish
    unless attributes.any (fun a => a.kind == .name && a.text == "csimp") do continue
    if token.text == "@" then
      let mut after := finish + 1
      while after < tokens.size && modifier tokens[after]!.text do after := after + 1
      unless (tokens[after]?.map (·.text)) == some "theorem" do
        throw s!"line {token.line}: csimp attribute not on a theorem"
      let (replaces, replacement) ← csimpStatement tokens (after + 1)
      result := ⟨(tokens[after + 1]?.map (·.text)).getD "", replaces, replacement⟩ :: result
    else
      let mut after := finish + 1
      let mut count := 0
      while after < tokens.size && tokens[after]!.line == tokens[finish]!.line &&
          tokens[after]!.kind == .name do
        let name := tokens[after]!.text
        let declared := (List.range tokens.size).find? fun i =>
          tokens[i]!.kind == .name && tokens[i]!.text == "theorem" &&
            (tokens[i + 1]?.map (·.text)) == some name
        let some declared := declared
          | throw s!"line {token.line}: csimp attribute on {name}, which is not a theorem of this source"
        let (replaces, replacement) ← csimpStatement tokens (declared + 1)
        result := ⟨name, replaces, replacement⟩ :: result
        count := count + 1
        after := after + 1
      if after < tokens.size && tokens[after]!.line == tokens[finish]!.line then
        throw s!"line {token.line}: unsupported csimp attribute target"
      if count == 0 then throw s!"line {token.line}: missing csimp attribute names"
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
