import Ix.Compiler.Tools.Check

/-! A conservative lexer for the trust ledger's source inventory. It handles
nested Lean comments and quoted literals, retains line locations, and rejects
unterminated input. Inventory consumers reject syntax they cannot account for;
this scanner is a tripwire, not a replacement for Lean's parser or axiom fence. -/

namespace Ix.Compiler.Tools.SourceScan

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
      if let some next := tokens[index + 1]? then
        if next.kind == .name then result := next.text :: result
  return result.reverse

def hygiene (tokens : Array Token) : Except String Unit := do
  for token in tokens do
    if token.kind == .name && ["axiom", "sorry", "native_decide"].contains token.text then
      throw s!"line {token.line}: {token.text} is not allowed in checked sources"

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
        if count == 0 then throw s!"line {token.line}: missing attribute-command names"
  return declarations.reverse

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

end Ix.Compiler.Tools.SourceScan
