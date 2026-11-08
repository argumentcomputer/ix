import IxVM.Program

/-! # Rendering the checked IxVM source as Lean

`IxVM.Checked.source` (`IxVM/IxVM/Checked.lean`) is the program the backend
headline's source semantics runs for the entry `IxVM::verify_claim`: what
`Aiur.Modules.prepare IxVM.program ["IxVM::verify_claim"]` computes, linked,
renamed and elaborated, written out as a Lean literal. This module renders
that literal from the native preparation:

* `IxVM/IxVM/Checked/<fragment>.lean`: one file per linked module instance,
  one definition per function (`IxVM.Checked.Fn.«M::f»`); subterms deeper
  than `threshold` become their own definitions (`….part<k>`), so no
  elaborated term is deep;
* `IxVM/IxVM/Checked/Declarations.lean`: enums, structs, aliases, consts and
  maps;
* `IxVM/IxVM/Checked/Program.lean`: the program, over those definitions and
  the table generator's tables (`IxVM.Checked.genericTables`).

`lake exe ixvm/ixvm-checked` writes the files; `--check` compares them and
checks that the literal is the native preparation
(`IxVM.CheckedCheck`). The test suite runs the same checks. -/

namespace IxVM.CheckedGen
open Aiur.Generic
open Aiur (Assertion BinOp Constant)

abbrev F := IxVM.F

def entry : String := "IxVM::verify_claim"

/-- Subterms at least this high get their own definition. -/
def threshold : Nat := 40

def q (s : String) : String := s.quote

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def opt (r : α → String) : Option α → String
  | some x => s!"(some {r x})"
  | none => "none"

def bool (b : Bool) : String := if b then "true" else "false"

def field (x : F) : String := toString x.val

partial def ty : Ty → String
  | .field => ".field"
  | .tuple ts => s!"(.tuple {list (ts.map ty)})"
  | .array t n => s!"(.array {ty t} {n})"
  | .ptr t => s!"(.ptr {ty t})"
  | .param n => s!"(.param {q n})"
  | .named n args => s!"(.named {q n} {list (args.map ty)})"

def recordHead (h : RecordHead) : String :=
  s!"\{ type := {ty h.type}, fields := {list (h.fields.map q)}, rest := {bool h.rest}, " ++
    s!"params := {list (h.params.map q)}, slots := {opt (fun s => list (s.map (opt toString))) h.slots} }"

def fieldRef (f : FieldRef) : String :=
  s!"\{ name := {q f.name}, owner := {opt ty f.owner}, index := {f.index}, arity := {f.arity} }"

def updateStep : UpdateStep → String
  | .member f => s!"(.member {fieldRef f})"
  | .project i n => s!"(.project {i} {n})"
  | .index i n => s!"(.index {i} {n})"

def assertion (a : Assertion) : String :=
  s!"\{ message := {opt q a.message}, runtimeCheck := {bool a.runtimeCheck} }"

def builtin : Builtin → String
  | .ascribe t => s!"(.ascribe {ty t})"
  | .debug m => s!"(.debug {q m})"
  | .assertEq a => s!"(.assertEq {assertion a})"

def control : Control → String
  | .block l => s!"(.block {q l})"
  | .exit .function => "(.exit .function)"
  | .exit (.block l) => s!"(.exit (.block {q l}))"

def binOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div"

partial def pattern : Pattern F → String
  | .literal x => s!"(.literal {field x})"
  | .wildcard => ".wildcard"
  | .bind n => s!"(.bind {q n})"
  | .global n t => s!"(.global {q n} {opt ty t})"
  | .load p => s!"(.load {pattern p})"
  | .orElse l r b =>
      s!"(.orElse {pattern l} {pattern r} \{ names := {list (b.names.map q)}, " ++
        s!"rightOrder := {list (b.rightOrder.map toString)} })"
  | .tuple ps => s!"(.tuple {list (ps.map pattern)})"
  | .array ps => s!"(.array {list (ps.map pattern)})"
  | .repeat p n => s!"(.repeat {pattern p} {n})"
  | .record h ps => s!"(.record {recordHead h} {list (ps.map pattern)})"
  | .construct t c ps => s!"(.construct {ty t} {q c} {list (ps.map pattern)})"
  | .constructAs ps' t c ps =>
      s!"(.constructAs {list (ps'.map q)} {ty t} {q c} {list (ps.map pattern)})"

partial def height : Expr F → Nat
  | .literal _ | .var _ | .global _ _ => 1
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs | .record _ xs
  | .update _ xs | .builtin _ xs | .call _ _ xs => 1 + (xs.map height).foldl max 0
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _ | .store x
  | .load x | .hint _ x _ | .neg x | .control _ x => 1 + height x
  | .letValue _ x b | .binary _ x b => 1 + max (height x) (height b)
  | .matchValue x arms => 1 + max (height x) ((arms.map (fun a => height a.2)).foldl max 0)

structure St where
  parts : Array String := #[]
  next : Nat := 0

abbrev R := StateM St

mutual
  /-- An expression; a subterm at least `threshold` high (other than the
  root) becomes the definition `base.part<k>`. -/
  partial def expr (base : String) (root : Bool) (e : Expr F) : R String := do
    if !root && height e ≥ threshold then
      let body ← expr base true e
      let st ← get
      let name := s!"{base}.part{st.next}"
      let part := s!"def {name} : Expr F :=\n  {body}\n"
      set { st with next := st.next + 1, parts := st.parts.push part }
      return name
    match e with
    | .literal x => return s!"(.literal {field x})"
    | .var n => return s!"(.var {q n})"
    | .global n t => return s!"(.global {q n} {opt ty t})"
    | .tuple xs => return s!"(.tuple {← exprs base xs})"
    | .array xs => return s!"(.array {← exprs base xs})"
    | .repeat x n => return s!"(.repeat {← expr base false x} {n})"
    | .index x i => return s!"(.index {← expr base false x} {i})"
    | .slice x a b => return s!"(.slice {← expr base false x} {a} {opt toString b})"
    | .construct n ts c xs =>
        return s!"(.construct {q n} {opt (fun ts => list (ts.map ty)) ts} {q c} {← exprs base xs})"
    | .constructAs ps t c xs =>
        return s!"(.constructAs {list (ps.map q)} {ty t} {q c} {← exprs base xs})"
    | .record h xs => return s!"(.record {recordHead h} {← exprs base xs})"
    | .member x f => return s!"(.member {← expr base false x} {fieldRef f})"
    | .update ps xs =>
        return s!"(.update {list (ps.map fun p => list (p.map updateStep))} {← exprs base xs})"
    | .builtin op xs => return s!"(.builtin {builtin op} {← exprs base xs})"
    | .project x i => return s!"(.project {← expr base false x} {i})"
    | .letValue p x b =>
        return s!"(.letValue {pattern p} {← expr base false x}\n    {← expr base false b})"
    | .store x => return s!"(.store {← expr base false x})"
    | .load x => return s!"(.load {← expr base false x})"
    | .hint t x c => return s!"(.hint {ty t} {← expr base false x} {q c})"
    | .neg x => return s!"(.neg {← expr base false x})"
    | .binary op l r => return s!"(.binary {binOp op} {← expr base false l} {← expr base false r})"
    | .call n ts xs =>
        return s!"(.call {q n} {opt (fun ts => list (ts.map ty)) ts} {← exprs base xs})"
    | .matchValue x arms => do
        let x ← expr base false x
        let arms ← arms.mapM fun (p, b) => do return s!"({pattern p},\n    {← expr base false b})"
        return s!"(.matchValue {x} {list arms})"
    | .control k x => return s!"(.control {control k} {← expr base false x})"

  partial def exprs (base : String) (xs : List (Expr F)) : R String := do
    return list (← xs.mapM (expr base false))
end

/-- A function's definitions: its parts, then itself. -/
def renderFunction (func : Function F) : String :=
  let base := s!"Fn.«{func.name}»"
  let (body, st) := (expr base true func.body).run {}
  let params := list (func.params.map fun (n, t) => s!"({q n}, {ty t})")
  let parts := String.join st.parts.toList
  parts ++ s!"def {base} : Function F where\n  name := {q func.name}\n  typeParams := " ++
    s!"{list (func.typeParams.map q)}\n  params := {params}\n  result := {ty func.result}\n  " ++
    s!"body := {body}\n  isInline := {bool func.isInline}\n"

def enumDecl (d : EnumDecl) : String :=
  s!"\{ name := {q d.name}, typeParams := {list (d.typeParams.map q)}, constructors := " ++
    s!"{list (d.constructors.map fun c => s!"\{ name := {q c.name}, fields := {list (c.fields.map ty)} }")} }"

def structDecl (d : StructDecl) : String :=
  s!"\{ name := {q d.name}, typeParams := {list (d.typeParams.map q)}, fields := " ++
    s!"{list (d.fields.map fun (n, t) => s!"({q n}, {ty t})")} }"

def aliasDecl (d : AliasDecl) : String :=
  s!"\{ name := {q d.name}, typeParams := {list (d.typeParams.map q)}, target := {ty d.target} }"

def constDecl (d : ConstDecl F) : String := s!"\{ name := {q d.name}, value := {pattern d.value} }"

def mapDecl (m : MapDecl) : String :=
  s!"\{ name := {q m.name}, params := {list (m.params.map fun (n, t) => s!"({q n}, {ty t})")}, " ++
    s!"result := {ty m.result}, input := {q m.input}, output := {q m.output} }"

def listLines (xs : List String) : String :=
  if xs.isEmpty then "[]" else "[\n    " ++ ",\n    ".intercalate xs ++ "]"

/-- A module name from a fragment's symbol. -/
def moduleName (symbol : String) : String :=
  String.ofList (symbol.toList.map fun c => if c.isAlphanum then c else '_')

def header (imports : List String) (doc : String) : String :=
  "\n".intercalate (imports.map ("import " ++ ·)) ++ "\n\n" ++
    s!"/-! {doc}\n\nGenerated by `lake exe ixvm/ixvm-checked` from the native preparation of\n" ++
    "`IxVM.program` for `IxVM::verify_claim`; do not edit. `--check` (and the\n" ++
    "test suite `ixvm-checked-source`) compares it and the preparation. -/\n\n" ++
    "set_option maxRecDepth 100000\n\nnamespace IxVM.Checked\nopen Aiur.Generic\n\n"

def footer : String := "end IxVM.Checked\n"

/-- The rendered files, as paths relative to the repository root, and their
contents. -/
def render (prepared : Aiur.Modules.Prepared IxVM.program) : List (System.FilePath × String) := Id.run do
  let prog : Program F := prepared.environment.source.program
  let mut files : List (System.FilePath × String) := []
  let mut modules : List String := []
  let mut fnNames : List String := []
  for fr in prepared.environment.assembly.fragments.values do
    if fr.program.functions.isEmpty then continue
    let m := moduleName fr.key.symbol
    modules := modules ++ [m]
    let names := fr.program.functions.map (·.name)
    fnNames := fnNames ++ names
    let fns := prog.functions.filter (names.contains ·.name)
    let text := header ["IxVM.Checked.Base"] s!"The checked functions of the module instance `{fr.key.symbol}`." ++
      "\n".intercalate (fns.map renderFunction) ++ "\n" ++ footer
    files := files ++ [(System.FilePath.mk s!"IxVM/IxVM/Checked/Fn/{m}.lean", text)]
  let decls := header ["IxVM.Checked.Base"] "The checked program's declarations." ++
    s!"def enums : List EnumDecl := {listLines (prog.enums.map enumDecl)}\n\n" ++
    s!"def structs : List StructDecl := {listLines (prog.structs.map structDecl)}\n\n" ++
    s!"def aliases : List AliasDecl := {listLines (prog.aliases.map aliasDecl)}\n\n" ++
    s!"def consts : List (ConstDecl F) := {listLines (prog.consts.map constDecl)}\n\n" ++
    s!"def maps : List MapDecl := {listLines (prog.maps.map mapDecl)}\n\n" ++ footer
  files := files ++ [(System.FilePath.mk "IxVM/IxVM/Checked/Declarations.lean", decls)]
  let program := header (modules.map (s!"IxVM.Checked.Fn.{·}") ++
      ["IxVM.Checked.Declarations", "IxVM.Checked.Tables"])
      "The checked program: the functions, declarations and tables." ++
    s!"def functions : List (Function F) := {listLines (fnNames.map (s!"Fn.«{·}»"))}\n\n" ++
    "def program : Program F where\n  functions := functions\n  enums := enums\n" ++
    "  structs := structs\n  tables := genericTables\n  maps := maps\n  aliases := aliases\n" ++
    "  consts := consts\n\n" ++ footer
  files := files ++ [(System.FilePath.mk "IxVM/IxVM/Checked/Program.lean", program)]
  return files

end IxVM.CheckedGen
