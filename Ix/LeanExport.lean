/-
  `Ix.LeanExport`: read the NDJSON export of a Lean environment written by
  `lean4export` (format 3.1.0), and stand its declarations up as a
  `Lean.Environment` that the compiler and the role binding read.

  This is how ix compiles libraries elaborated by another Lean toolchain
  without being built on it: that toolchain's `lean4export` writes the
  declarations, and ix, on its own toolchain, reads them here. Nothing read
  here is trusted. The compiled environment is checked downstream like any
  other.

  **Why unchecked insertion is acceptable.** `environment` puts the
  declarations into a `Lean.Environment` without Lean's kernel checking
  them (this module alone imports `Lean.Environment`'s private scope for
  that). The compiler only translates its input: an address is the content
  of the declarations it was given, whether they type-check or not. Typing
  is established downstream, by the claims about the compiled environment,
  which IxVM checks against the role binding's specifications. A declaration
  that does not type-check makes those claims fail; it can never make one
  hold.

  **The reader is strict.** It refuses:
  - a format version other than `formatVersion`, or an exporter other than
    `lean4export`;
  - a `meta` record that is missing, repeated or not first;
  - an index out of sequence, or one that refers to a record not yet read;
  - a record with missing or extra fields;
  - a declaration name declared twice;
  - any value it cannot read back exactly.

  **What an export cannot carry, and so what this reader cannot give back.**
  `lean4export` writes a syntax-valued `mdata` entry with `repr`, which keeps
  a source span's text but not the string it is a span of; this reader drops
  such entries and counts them (`Imported.droppedSyntaxMData`). An `mdata`
  map is written as a JSON object, so its entries come back in key order.
  Upstream `lean4export` also hash-conses expressions under Lean's
  `BEq Expr`, which is α-equivalence and ignores binder annotations, so every
  α-equivalent subterm is written with the binder names and binder info of
  its first occurrence; the fixture recipe patches that
  (`Tests/Fixtures/toolchains/Regenerate.lean`). All of these are metadata: an
  environment compiled from an export matches the native compile of the same
  declarations in content (every constant, address and the role binding), not
  in metadata.
-/
module

public import Lean.Data.Json
public import Lean.Environment
public import Std.Data.HashSet
import all Lean.Environment

public section

namespace Ix.LeanExport

open Lean (Json Name Level Expr ConstantInfo)

/-- The export format this reader accepts. -/
def formatVersion : String := "3.1.0"

/-- The exporter this reader accepts. -/
def exporterName : String := "lean4export"

/-- An export's `meta` record: the exporter and the Lean that wrote it. -/
structure ExportMeta where
  exporterVersion : String
  formatVersion : String
  leanVersion : String
  leanGithash : String
  deriving Repr, Inhabited, BEq

/-- An imported export. -/
structure Imported where
  exportMeta : ExportMeta
  /-- The declarations, in the order the export lists them. -/
  constants : Array (Name × ConstantInfo)
  /-- The syntax-valued `mdata` entries dropped (see the module header). -/
  droppedSyntaxMData : Nat
  deriving Inhabited

/-- What has been read so far. Index 0 of the names is the anonymous name and
index 0 of the levels is `zero`, as in the export. -/
structure State where
  exportMeta : Option ExportMeta := none
  names : Array Name := #[.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  constants : Array (Name × ConstantInfo) := #[]
  declared : Std.HashSet Name := {}
  droppedSyntaxMData : Nat := 0
  deriving Inhabited

/-! ## Fields -/

/-- The fields of an object, which must be exactly `keys`, in that order. -/
def fields (what : String) (j : Json) (keys : Array String) : Except String (Array Json) := do
  let .obj kvs := j | throw s!"{what}: object expected"
  let present := kvs.toList.map (·.1)
  unless kvs.size == keys.size do
    throw s!"{what}: expected the fields {keys.toList}, found {present}"
  keys.mapM fun k => match kvs.get? k with
    | some v => pure v
    | none => throw s!"{what}: expected the fields {keys.toList}, found {present}"

/-- The single field of a one-field object, with its key. -/
def soleField (what : String) (j : Json) : Except String (String × Json) := do
  let .obj kvs := j | throw s!"{what}: object expected"
  match kvs.toList with
  | [kv] => pure kv
  | kvs => throw s!"{what}: expected one field, found {kvs.map (·.1)}"

def natOf (what : String) (j : Json) : Except String Nat :=
  j.getNat?.mapError fun e => s!"{what}: {e}"

def strOf (what : String) (j : Json) : Except String String :=
  j.getStr?.mapError fun e => s!"{what}: {e}"

def boolOf (what : String) (j : Json) : Except String Bool :=
  j.getBool?.mapError fun e => s!"{what}: {e}"

def arrOf (what : String) (j : Json) : Except String (Array Json) :=
  j.getArr?.mapError fun e => s!"{what}: {e}"

/-! ## Indices -/

def State.name (s : State) (what : String) (j : Json) : Except String Name := do
  let i ← natOf what j
  match s.names[i]? with
  | some n => pure n
  | none => throw s!"{what}: name {i} is not defined yet"

def State.level (s : State) (what : String) (j : Json) : Except String Level := do
  let i ← natOf what j
  match s.levels[i]? with
  | some l => pure l
  | none => throw s!"{what}: level {i} is not defined yet"

def State.expr (s : State) (what : String) (j : Json) : Except String Expr := do
  let i ← natOf what j
  match s.exprs[i]? with
  | some e => pure e
  | none => throw s!"{what}: expression {i} is not defined yet"

def State.nameList (s : State) (what : String) (j : Json) : Except String (List Name) := do
  return (← (← arrOf what j).mapM (s.name what)).toList

def State.levelList (s : State) (what : String) (j : Json) : Except String (List Level) := do
  return (← (← arrOf what j).mapM (s.level what)).toList

/-- A new record's index must be the next one: the export numbers each kind
densely, in order. -/
def nextIndex (what : String) (j : Json) (expected : Nat) : Except String Unit := do
  let i ← natOf what j
  unless i == expected do throw s!"{what}: index {i} out of sequence, expected {expected}"

/-! ## Metadata values -/

def skipSpace : List Char → List Char
  | c :: cs => if c.isWhitespace then skipSpace cs else c :: cs
  | [] => []

/-- The token up to whitespace or a closing parenthesis outside `«»`. -/
def nameToken (cs : List Char) : String × List Char :=
  go cs false []
where
  go : List Char → Bool → List Char → String × List Char
    | c :: rest, quoted, acc =>
      if !quoted && (c.isWhitespace || c == ')') then (String.ofList acc.reverse, c :: rest)
      else go rest (if c == '«' then true else if c == '»' then false else quoted) (c :: acc)
    | [], _, acc => (String.ofList acc.reverse, [])

/-- A string literal's source text, escapes kept. -/
def stringToken : List Char → Option (String × List Char)
  | '"' :: cs => go cs ['"']
  | _ => none
where
  go : List Char → List Char → Option (String × List Char)
    | '\\' :: c :: rest, acc => go rest (c :: '\\' :: acc)
    | '"' :: rest, acc => some (String.ofList ('"' :: acc).reverse, rest)
    | c :: rest, acc => go rest (c :: acc)
    | [], _ => none

/-- A `Name` as `Repr Name` writes it: a quoted name literal, or, for a name a
literal cannot spell (numeric components, macro scopes), the constructor form
`Lean.Name.mkStr p "s"` or `Lean.Name.mkNum p n`, with `p` parenthesized when
it is itself an application. `fuel` bounds the nesting. -/
def nameRepr : Nat → List Char → Option (Name × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match skipSpace cs with
    | '(' :: rest => do
      let (n, rest) ← nameRepr fuel rest
      match skipSpace rest with
      | ')' :: rest => some (n, rest)
      | _ => none
    | cs@('`' :: _) =>
      let (tok, rest) := nameToken cs
      (Lean.Syntax.decodeNameLit tok).map (·, rest)
    | cs =>
      let (head, rest) := nameToken cs
      if head == "Lean.Name.anonymous" then some (.anonymous, rest)
      else if head == "Lean.Name.mkStr" then do
        let (p, rest) ← nameRepr fuel rest
        let (lit, rest) ← stringToken (skipSpace rest)
        some (.str p (← Lean.Syntax.decodeStrLit lit), rest)
      else if head == "Lean.Name.mkNum" then do
        let (p, rest) ← nameRepr fuel rest
        let (tok, rest) := nameToken (skipSpace rest)
        some (.num p (← tok.toNat?), rest)
      else none

/-- A `DataValue` as `lean4export` writes it, with `reprStr`. `none` for a
syntax value, which `repr` does not preserve. Any other value must read back
exactly: `reprStr` of the result is the input, so the layout `repr` gives a
long value (a line break after the constructor) is accepted only as written. -/
def dataValue (s : String) : Except String (Option Lean.DataValue) := do
  if s.startsWith "Lean.DataValue.ofSyntax" then return none
  let rest (pre : String) : Option String :=
    if s.startsWith (pre ++ " ") || s.startsWith (pre ++ "\n") then
      some (String.ofList (skipSpace (s.drop pre.length).toString.toList))
    else none
  let candidate : Option Lean.DataValue :=
    if let some r := rest "Lean.DataValue.ofBool" then
      if r == "true" then some (.ofBool true) else if r == "false" then some (.ofBool false) else none
    else if let some r := rest "Lean.DataValue.ofNat" then
      r.toNat?.map .ofNat
    else if let some r := rest "Lean.DataValue.ofInt" then
      let r := if r.startsWith "(" && r.endsWith ")" then ((r.drop 1).dropEnd 1).toString else r
      r.toInt?.map .ofInt
    else if let some r := rest "Lean.DataValue.ofString" then
      (Lean.Syntax.decodeStrLit r).map .ofString
    else if let some r := rest "Lean.DataValue.ofName" then
      match nameRepr r.length r.toList with
      | some (n, tail) => if (skipSpace tail).isEmpty then some (.ofName n) else none
      | none => none
    else none
  match candidate with
  | some v =>
    unless reprStr v == s do throw s!"metadata value does not read back: {s.take 120}"
    return some v
  | none => throw s!"unreadable metadata value: {s.take 120}"

/-- An `mdata` object: keys are names as `Name.toString` writes them, values
`DataValue`s. Syntax values are dropped and counted. -/
def kvMap (j : Json) : Except String (Lean.KVMap × Nat) := do
  let .obj kvs := j | throw "mdata data: object expected"
  let mut entries : Array (Name × Lean.DataValue) := #[]
  let mut dropped := 0
  for (k, v) in kvs.toList do
    let key := k.toName
    unless key.toString == k && !key.isAnonymous do
      throw s!"mdata key does not read back: {k}"
    match ← dataValue (← strOf "mdata value" v) with
    | some dv => entries := entries.push (key, dv)
    | none => dropped := dropped + 1
  return ({ entries := entries.toList }, dropped)

/-! ## Records -/

def binderInfo (j : Json) : Except String Lean.BinderInfo := do
  match ← strOf "binderInfo" j with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | other => throw s!"binderInfo: unknown value {other}"

/-- A natural number literal, written in decimal. -/
def natLiteral (s : String) : Except String Nat := do
  let some n := s.toNat? | throw s!"natVal: not a decimal numeral: {s.take 40}"
  unless toString n == s do throw s!"natVal: not a canonical decimal numeral: {s.take 40}"
  return n

/-- An indexed record: its index field `idx`, which must be the next index,
and its one other field. -/
def indexed (what : String) (j : Json) (idx : String) (expected : Nat) :
    Except String (String × Json) := do
  let .obj kvs := j | throw s!"{what}: object expected"
  let some i := kvs.get? idx | throw s!"{what}: no {idx} field"
  nextIndex what i expected
  soleField what (.obj (kvs.erase idx))

def nameRecord (s : State) (j : Json) : Except String State := do
  let (tag, body) ← indexed "name" j "in" s.names.size
  let n ← match tag with
    | "str" =>
      let fs ← fields "name.str" body #["pre", "str"]
      pure (Name.str (← s.name "name.str" fs[0]!) (← strOf "name.str" fs[1]!))
    | "num" =>
      let fs ← fields "name.num" body #["pre", "i"]
      pure (Name.num (← s.name "name.num" fs[0]!) (← natOf "name.num" fs[1]!))
    | other => throw s!"name: unknown kind {other}"
  return { s with names := s.names.push n }

def levelRecord (s : State) (j : Json) : Except String State := do
  let (tag, body) ← indexed "level" j "il" s.levels.size
  let pair (what : String) : Except String (Level × Level) := do
    let a ← arrOf what body
    unless a.size == 2 do throw s!"{what}: expected two levels"
    return (← s.level what a[0]!, ← s.level what a[1]!)
  let l ← match tag with
    | "succ" => pure (Level.succ (← s.level "level.succ" body))
    | "max" => let (a, b) ← pair "level.max"; pure (Level.max a b)
    | "imax" => let (a, b) ← pair "level.imax"; pure (Level.imax a b)
    | "param" => pure (Level.param (← s.name "level.param" body))
    | other => throw s!"level: unknown kind {other}"
  return { s with levels := s.levels.push l }

def exprRecord (s : State) (j : Json) : Except String State := do
  let (tag, body) ← indexed "expression" j "ie" s.exprs.size
  let mut dropped := 0
  let e ← match tag with
    | "bvar" => pure (Expr.bvar (← natOf "bvar" body))
    | "sort" => pure (Expr.sort (← s.level "sort" body))
    | "const" =>
      let fs ← fields "const" body #["name", "us"]
      pure (Expr.const (← s.name "const" fs[0]!) (← s.levelList "const" fs[1]!))
    | "app" =>
      let fs ← fields "app" body #["fn", "arg"]
      pure (Expr.app (← s.expr "app" fs[0]!) (← s.expr "app" fs[1]!))
    | "lam" =>
      let fs ← fields "lam" body #["name", "type", "body", "binderInfo"]
      pure (Expr.lam (← s.name "lam" fs[0]!) (← s.expr "lam" fs[1]!) (← s.expr "lam" fs[2]!)
        (← binderInfo fs[3]!))
    | "forallE" =>
      let fs ← fields "forallE" body #["name", "type", "body", "binderInfo"]
      pure (Expr.forallE (← s.name "forallE" fs[0]!) (← s.expr "forallE" fs[1]!)
        (← s.expr "forallE" fs[2]!) (← binderInfo fs[3]!))
    | "letE" =>
      let fs ← fields "letE" body #["name", "type", "value", "body", "nondep"]
      pure (Expr.letE (← s.name "letE" fs[0]!) (← s.expr "letE" fs[1]!) (← s.expr "letE" fs[2]!)
        (← s.expr "letE" fs[3]!) (← boolOf "letE" fs[4]!))
    | "proj" =>
      let fs ← fields "proj" body #["typeName", "idx", "struct"]
      pure (Expr.proj (← s.name "proj" fs[0]!) (← natOf "proj" fs[1]!) (← s.expr "proj" fs[2]!))
    | "natVal" => pure (Expr.lit (.natVal (← natLiteral (← strOf "natVal" body))))
    | "strVal" => pure (Expr.lit (.strVal (← strOf "strVal" body)))
    | "mdata" =>
      let fs ← fields "mdata" body #["data", "expr"]
      let (kv, n) ← kvMap fs[0]!
      dropped := n
      pure (Expr.mdata kv (← s.expr "mdata" fs[1]!))
    | other => throw s!"expression: unknown kind {other}"
  return { s with exprs := s.exprs.push e, droppedSyntaxMData := s.droppedSyntaxMData + dropped }

/-- Record a declaration, refusing a name declared twice. -/
def State.declare (s : State) (ci : ConstantInfo) : Except String State := do
  if s.declared.contains ci.name then throw s!"{ci.name} is declared twice"
  return { s with declared := s.declared.insert ci.name, constants := s.constants.push (ci.name, ci) }

def hints (j : Json) : Except String Lean.ReducibilityHints := do
  match j with
  | .str "opaque" => pure .opaque
  | .str "abbrev" => pure .abbrev
  | j =>
    let fs ← fields "hints" j #["regular"]
    let n ← natOf "hints.regular" fs[0]!
    unless n < UInt32.size do throw s!"hints.regular: {n} is out of range"
    pure (.regular n.toUInt32)

def safety (j : Json) : Except String Lean.DefinitionSafety := do
  match ← strOf "safety" j with
  | "safe" => pure .safe
  | "unsafe" => pure .unsafe
  | "partial" => pure .partial
  | other => throw s!"safety: unknown value {other}"

def quotKind (j : Json) : Except String Lean.QuotKind := do
  match ← strOf "quot.kind" j with
  | "type" => pure .type
  | "ctor" => pure .ctor
  | "lift" => pure .lift
  | "ind" => pure .ind
  | other => throw s!"quot.kind: unknown value {other}"

def inductiveRecord (s : State) (body : Json) : Except String State := do
  let fs ← fields "inductive" body #["types", "ctors", "recs"]
  let mut s := s
  for t in ← arrOf "inductive.types" fs[0]! do
    let f ← fields "inductive type" t #["name", "levelParams", "type", "numParams",
      "numIndices", "all", "ctors", "numNested", "isRec", "isReflexive", "isUnsafe"]
    let w := "inductive type"
    s ← s.declare (.inductInfo {
      name := ← s.name w f[0]!, levelParams := ← s.nameList w f[1]!, type := ← s.expr w f[2]!,
      numParams := ← natOf w f[3]!, numIndices := ← natOf w f[4]!, all := ← s.nameList w f[5]!,
      ctors := ← s.nameList w f[6]!, numNested := ← natOf w f[7]!, isRec := ← boolOf w f[8]!,
      isReflexive := ← boolOf w f[9]!, isUnsafe := ← boolOf w f[10]! })
  for c in ← arrOf "inductive.ctors" fs[1]! do
    let f ← fields "constructor" c #["name", "levelParams", "type", "induct", "cidx",
      "numParams", "numFields", "isUnsafe"]
    let w := "constructor"
    s ← s.declare (.ctorInfo {
      name := ← s.name w f[0]!, levelParams := ← s.nameList w f[1]!, type := ← s.expr w f[2]!,
      induct := ← s.name w f[3]!, cidx := ← natOf w f[4]!, numParams := ← natOf w f[5]!,
      numFields := ← natOf w f[6]!, isUnsafe := ← boolOf w f[7]! })
  for r in ← arrOf "inductive.recs" fs[2]! do
    let f ← fields "recursor" r #["name", "levelParams", "type", "all", "numParams",
      "numIndices", "numMotives", "numMinors", "rules", "k", "isUnsafe"]
    let w := "recursor"
    let rules ← (← arrOf "recursor.rules" f[8]!).mapM fun rule => do
      let g ← fields "recursor rule" rule #["ctor", "nfields", "rhs"]
      pure ({
        ctor := ← s.name "recursor rule" g[0]!, nfields := ← natOf "recursor rule" g[1]!,
        rhs := ← s.expr "recursor rule" g[2]! } : Lean.RecursorRule)
    s ← s.declare (.recInfo {
      name := ← s.name w f[0]!, levelParams := ← s.nameList w f[1]!, type := ← s.expr w f[2]!,
      all := ← s.nameList w f[3]!, numParams := ← natOf w f[4]!, numIndices := ← natOf w f[5]!,
      numMotives := ← natOf w f[6]!, numMinors := ← natOf w f[7]!, rules := rules.toList,
      k := ← boolOf w f[9]!, isUnsafe := ← boolOf w f[10]! })
  return s

def declarationRecord (s : State) (tag : String) (body : Json) : Except String State := do
  match tag with
  | "axiom" =>
    let f ← fields tag body #["name", "levelParams", "type", "isUnsafe"]
    s.declare (.axiomInfo {
      name := ← s.name tag f[0]!, levelParams := ← s.nameList tag f[1]!,
      type := ← s.expr tag f[2]!, isUnsafe := ← boolOf tag f[3]! })
  | "def" =>
    let f ← fields tag body #["name", "levelParams", "type", "value", "hints", "safety", "all"]
    s.declare (.defnInfo {
      name := ← s.name tag f[0]!, levelParams := ← s.nameList tag f[1]!,
      type := ← s.expr tag f[2]!, value := ← s.expr tag f[3]!, hints := ← hints f[4]!,
      safety := ← safety f[5]!, all := ← s.nameList tag f[6]! })
  | "thm" =>
    let f ← fields tag body #["name", "levelParams", "type", "value", "all"]
    s.declare (.thmInfo {
      name := ← s.name tag f[0]!, levelParams := ← s.nameList tag f[1]!,
      type := ← s.expr tag f[2]!, value := ← s.expr tag f[3]!, all := ← s.nameList tag f[4]! })
  | "opaque" =>
    let f ← fields tag body #["name", "levelParams", "type", "value", "all", "isUnsafe"]
    s.declare (.opaqueInfo {
      name := ← s.name tag f[0]!, levelParams := ← s.nameList tag f[1]!,
      type := ← s.expr tag f[2]!, value := ← s.expr tag f[3]!, all := ← s.nameList tag f[4]!,
      isUnsafe := ← boolOf tag f[5]! })
  | "quot" =>
    let f ← fields tag body #["name", "levelParams", "type", "kind"]
    s.declare (.quotInfo {
      name := ← s.name tag f[0]!, levelParams := ← s.nameList tag f[1]!,
      type := ← s.expr tag f[2]!, kind := ← quotKind f[3]! })
  | "inductive" => inductiveRecord s body
  | "meta" => throw "a meta record must be the first line, and appear once"
  | other => throw s!"unknown record {other}"

/-- The `meta` record. -/
def metaRecord (body : Json) : Except String ExportMeta := do
  let f ← fields "meta" body #["exporter", "format", "lean"]
  let e ← fields "meta.exporter" f[0]! #["name", "version"]
  let fmt ← fields "meta.format" f[1]! #["version"]
  let l ← fields "meta.lean" f[2]! #["githash", "version"]
  let name ← strOf "meta.exporter.name" e[0]!
  unless name == exporterName do throw s!"exporter {name}, expected {exporterName}"
  let version ← strOf "meta.format.version" fmt[0]!
  unless version == formatVersion do
    throw s!"export format {version}, expected {formatVersion}"
  return {
    exporterVersion := ← strOf "meta.exporter.version" e[1]!, formatVersion := version,
    leanGithash := ← strOf "meta.lean.githash" l[0]!,
    leanVersion := ← strOf "meta.lean.version" l[1]! }

/-- Read one line. -/
def step (s : State) (line : String) : Except String State := do
  let j ← Json.parse line
  let .obj kvs := j | throw "a record must be an object"
  if s.exportMeta.isNone then
    let (tag, body) ← soleField "first record" j
    unless tag == "meta" do throw "the first record must be meta"
    return { s with exportMeta := some (← metaRecord body) }
  if kvs.contains "in" then nameRecord s j
  else if kvs.contains "il" then levelRecord s j
  else if kvs.contains "ie" then exprRecord s j
  else
    let (tag, body) ← soleField "declaration" j
    declarationRecord s tag body

def State.finish (s : State) : Except String Imported := do
  let some m := s.exportMeta | throw "empty export"
  return { exportMeta := m, constants := s.constants, droppedSyntaxMData := s.droppedSyntaxMData }

/-- Read an export held in memory. -/
def importString (text : String) : Except String Imported := do
  let mut s : State := {}
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    s ← (step s line).mapError fun e => s!"line {n}: {e}"
  s.finish

/-- Read an export file line by line. -/
def importFile (path : System.FilePath) : IO Imported := do
  let h ← IO.FS.Handle.mk path .read
  let mut s : State := {}
  let mut n := 0
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    n := n + 1
    let line := if line.endsWith "\n" then (line.dropEnd 1).toString else line
    if line.isEmpty then continue
    s ← IO.ofExcept ((step s line).mapError fun e => s!"{path}:{n}: {e}")
  IO.ofExcept (s.finish.mapError fun e => s!"{path}: {e}")

/-- An elaborator environment holding exactly `constants`, inserted without
checking. It carries no imports, modules or extension entries: what the
compiler reads of an environment are its constants. -/
def environment (constants : Array (Name × ConstantInfo)) : IO Lean.Environment := do
  let env ← Lean.mkEmptyEnvironment
  -- The first stage of the map, which `Environment.find?` reads.
  let map : Lean.ConstMap := constants.foldl (fun m (n, ci) => m.insert n ci) {}
  return Lean.Environment.ofKernelEnv { env.toKernelEnv with constants := map.switch }

end Ix.LeanExport

end
