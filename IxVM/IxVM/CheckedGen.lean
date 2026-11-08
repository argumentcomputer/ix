import IxVM.Program
import Aiur.Generic.LookupFacts

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

/-- **The lookup facts**: for every function with no type parameters (named by
its plain name), a theorem that the program resolves its name to its closure,
proved by `Program.sourceFunction?_of_mem` from the function's index and one
certificate that the names' keys are distinct (`decide +kernel` on natural
numbers, no string comparison). Generic functions get no fact here. -/
def lookup (prog : Program F) (fnNames : List String) : String := Id.run do
  let mut facts : List String := []
  let mut index := 0
  for name in fnNames do
    if let some f := prog.functions.find? (·.name == name) then
      if f.typeParams.isEmpty && name.toList.head? != some '$' then
        facts := facts ++ [s!"theorem Lookup.«{name}» : program.sourceFunction? {q name} =\n" ++
          s!"    some \{ types := [], params := Fn.«{name}».params.map fun (n, t) => (n, (t.subst []).toCore),\n" ++
          s!"           body := Fn.«{name}».body } :=\n" ++
          s!"  Program.sourceFunction?_of_mem (f := Fn.«{name}») functionNames_nodup\n" ++
          s!"    (List.getElem_mem (l := functions) (n := {index}) (by decide +kernel))\n" ++
          s!"    (head_ne_of_bytes (by decide +kernel)) rfl\n"]
    index := index + 1
  return header ["IxVM.Checked", "Aiur.Generic.LookupFacts"] "The checked program's lookup facts." ++
    "/-- The function names as numbers (`nameKey`). -/\n" ++
    s!"def functionKeys : List Nat := {listLines (fnNames.map fun n => toString (nameKey n))}\n\n" ++
    "/-- The keys are the names' keys: each name's key computed once. -/\n" ++
    "theorem functionKeys_eq : functions.map (fun f => nameKey f.name) = functionKeys := by decide +kernel\n\n" ++
    "theorem functionKeys_nodup : functionKeys.Nodup := by decide +kernel\n\n" ++
    "/-- **The function names are distinct**, certified on their keys. -/\n" ++
    "theorem functionNames_nodup : (functions.map (·.name)).Nodup :=\n" ++
    "  nodup_of_nameKeys (by simpa only [List.map_map, Function.comp_def, functionKeys_eq] using functionKeys_nodup)\n\n" ++
    "/-- **No map is named like a function.** -/\n" ++
    "theorem mapKeys_fresh : ∀ m ∈ maps, nameKey m.name ∉ functions.map (fun f => nameKey f.name) := by\n" ++
    "  rw [functionKeys_eq]; decide +kernel\n\n" ++
    "\n".intercalate facts ++ "\n" ++ footer


/-! ## Mirrors

`mirrors` renders, for a closure of functions of the checked program, a Lean
function per function (its *mirror*: the body run on values and a heap, with
fuel, `Option` for failure) and a lemma `of_eval` that every derivation of the
function is a run of its mirror. The lemma's script inverts the derivation
node by node (`Ix.IxVM.Refinement.Mirror`), applies the callees' lemmas at
calls (maps: `EvalFn.map_row`), and evaluates the mirror on what it found.
Functions the generator cannot handle (recursive ones, hints, control,
generic calls, nested patterns) get a mirror without a lemma, or nothing. -/

namespace MirrorGen

/-- What the renderer reads. -/
structure Ctx where
  prog : Program F
  src : Aiur.Generic.Source F
  /-- Functions whose lemma is not generated (recursive ones), assumed in callers. -/
  given : List String
  /-- The given functions a function reaches. -/
  needs : String → List String
  /-- Functions whose mirror definition has already been emitted. -/
  defined : List String := []
  /-- The function currently being rendered. -/
  self : String := ""

abbrev M := StateT Nat (Except String)

def fresh (base : String) : M String := do
  let n ← get
  set (n + 1)
  return s!"{base}{n}"

def var (n : String) : String := "x_" ++ n

def ind (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("  " ++ ·))

def plainCallee : String → Option (List Ty) → Option String
  | n, none => some n
  | n, some [] => some n
  | _, _ => none

def isFunction (ctx : Ctx) (n : String) : Bool := ctx.prog.functions.any (·.name == n)

def constField (ctx : Ctx) (n : String) (t : Ty) : M String :=
  match ctx.src.world.constant n (t.subst []) with
  | .ok (.literal c) => return field c
  | _ => throw s!"const {n} is not a literal"

/-- A flat pattern: binds and wildcards only. -/
def flatName : Pattern F → Option String
  | .bind n => some (var n)
  | .wildcard => some "_"
  | _ => none

def flatNames (ps : List (Pattern F)) : M (List String) :=
  ps.mapM fun p => match flatName p with
    | some n => pure n
    | none => throw "nested pattern"

mutual
  /-- An atom: lines that bind it, the value term and the heap term. -/
  partial def atom (ctx : Ctx) (e : Expr F) (h : String) : M (List String × String × String) := do
    match e with
    | .var n => return ([], var n, h)
    | .literal c => return ([], s!"(.field {field c})", h)
    | .global n (some t) => return ([], s!"(.field {← constField ctx n t})", h)
    | e =>
      let v ← fresh "v"
      let h' ← fresh "h"
      let code ← block ctx e h
      return ([s!"let ({v}, {h'}) ← {code}"], v, h')

  partial def atoms (ctx : Ctx) (es : List (Expr F)) (h : String) :
      M (List String × List String × String) := do
    let mut lines := []
    let mut vs := []
    let mut cur := h
    for e in es do
      let (ls, v, h') ← atom ctx e cur
      lines := lines ++ ls
      vs := vs ++ [v]
      cur := h'
    return (lines, vs, cur)

  /-- An `Option (SourceValue F × Heap F)` term. -/
  partial def block (ctx : Ctx) (e : Expr F) (h : String) : M String := do
    let wrap (lines : List String) (last : String) : String :=
      if lines.isEmpty then last else "(do\n" ++ ind ("\n".intercalate (lines ++ [last])) ++ ")"
    match e with
    | .var _ | .literal _ | .global _ (some _) =>
      let (_, v, h') ← atom ctx e h
      return s!"some ({v}, {h'})"
    | .tuple es | .array es =>
      let (ls, vs, h') ← atoms ctx es h
      return wrap ls s!"some (.tuple {list vs}, {h'})"
    | .repeat x n =>
      let (ls, v, h') ← atom ctx x h
      return wrap ls s!"some (.tuple (List.replicate {n} {v}), {h'})"
    | .call name targs es =>
      let some g := plainCallee name targs | throw s!"generic call {name}"
      let (ls, vs, h') ← atoms ctx es h
      if isFunction ctx g then
        if g != ctx.self && !ctx.defined.contains g then
          throw s!"missing callee mirror {g}"
        return wrap ls s!"«{g}» k {h'} {" ".intercalate vs}"
      else
        return wrap ls s!"mapCall IxVM.Checked.source.tables {q g} {list vs} {h'}"
    | .binary op l r =>
      let (ls, vs, h') ← atoms ctx [l, r] h
      return wrap ls s!"match evalBinOp {binOp op} {vs[0]!} {vs[1]!} with\n  | .ok z => some (z, {h'})\n  | .error _ => none"
    | .load x =>
      let (ls, v, h') ← atom ctx x h
      return wrap ls s!"match loadValue {h'} {v} with\n  | .ok z => some (z, {h'})\n  | .error _ => none"
    | .index x i =>
      let (ls, v, h') ← atom ctx x h
      return wrap ls s!"match projectValue {v} {i} with\n  | .ok z => some (z, {h'})\n  | .error _ => none"
    | .builtin op es =>
      let (ls, vs, h') ← atoms ctx es h
      return wrap ls s!"match Builtin.apply {builtin op} {list vs} with\n  | .ok z => some (z, {h'})\n  | .error _ => none"
    | .letValue p x b =>
      let (ls, v, h') ← atom ctx x h
      let rest ← block ctx b h'
      match p with
      | .bind n => return wrap (ls ++ [s!"let {var n} := {v}"]) rest
      | .wildcard => return wrap ls rest
      | .tuple ps | .array ps =>
        let ns ← flatNames ps
        return wrap ls s!"match {v} with\n  | .tuple {list ns} =>\n{ind (ind rest)}\n  | _ => none"
      | .construct t c ps =>
        let ns ← flatNames ps
        let n ← fresh "e"
        return wrap ls (s!"match {v} with\n  | .construct {n} {q c} {list ns} =>\n" ++
          s!"    if {n} = constructorName [] {ty t} then\n{ind (ind (ind rest))}\n    else none\n  | _ => none")
      | _ => throw "let pattern"
    | .matchValue x arms =>
      let (ls, v, h') ← atom ctx x h
      let mut chain := "none"
      for (p, b) in arms.reverse do
        let body ← block ctx b h'
        chain ← match p with
          | .literal c => pure s!"if {v} = .field {field c} then\n{ind body}\nelse\n{ind chain}"
          | .wildcard => pure body
          | _ => throw "match arm pattern"
      return wrap ls chain
    | _ => throw "expression form"
end

/-! ### Scripts -/

/-- What the final step uses: fuel names and rewrite facts. -/
structure Facts where
  fuel : List String := []
  rw : List String := []

def rcasesList (ys : List String) : String :=
  ys.foldr (fun y acc => s!"_ | ⟨{y}, {acc}⟩") "_ | ⟨_, _⟩"

mutual
  partial def proveArgs (ctx : Ctx) (es : List (Expr F)) (args : String) (fs : Facts)
      (k : Facts → M (List String)) : M (List String) := do
    match es with
    | [] => return [s!"obtain ⟨rfl, rfl⟩ := {args}.nil_inv"] ++ (← k fs)
    | e :: es =>
      let v ← fresh "v"; let vs ← fresh "vs"; let m ← fresh "m"; let d ← fresh "d"; let a ← fresh "args"
      return [s!"obtain ⟨{v}, {vs}, {m}, rfl, {d}, {a}⟩ := {args}.cons_inv"] ++
        (← prove ctx e d fs fun fs => proveArgs ctx es a fs k)

  partial def prove (ctx : Ctx) (e : Expr F) (d : String) (fs : Facts)
      (k : Facts → M (List String)) : M (List String) := do
    match e with
    | .var _ =>
      let l ← fresh "l"
      return [s!"obtain ⟨{l}, rfl⟩ := {d}.var_inv", s!"simp at {l}", s!"subst {l}"] ++ (← k fs)
    | .literal _ => return [s!"obtain ⟨rfl, rfl⟩ := {d}.literal_inv"] ++ (← k fs)
    | .global n (some t) =>
      return [s!"obtain ⟨rfl, rfl⟩ := {d}.global_literal_inv (x := ({← constField ctx n t} : F)) " ++
        "(eq_of_isLiteral (by decide +kernel))"] ++ (← k fs)
    | .tuple es | .array es =>
      let vs ← fresh "vs"; let a ← fresh "args"
      let inv := match e with | .tuple _ => "tuple_inv" | _ => "array_inv"
      return [s!"obtain ⟨{vs}, {a}, rfl⟩ := {d}.{inv}"] ++ (← proveArgs ctx es a fs k)
    | .repeat x _ =>
      let p ← fresh "v"; let dp ← fresh "d"
      return [s!"obtain ⟨{p}, {dp}, rfl⟩ := {d}.repeat_inv"] ++ (← prove ctx x dp fs k)
    | .call name targs es =>
      let some g := plainCallee name targs | throw s!"generic call {name}"
      let vs ← fresh "vs"; let m ← fresh "m"; let a ← fresh "args"; let c ← fresh "callee"
      return [s!"obtain ⟨{vs}, {m}, {a}, {c}⟩ := {d}.call_inv"] ++
        (← proveArgs ctx es a fs fun fs => do
          let pre := [match targs with
            | none => s!"rw [instanceName_plain_none] at {c}"
            | _ => s!"rw [instanceName_plain_some] at {c}"]
          if isFunction ctx g then
            let kk ← fresh "k"; let hk ← fresh "hk"
            let lem := match ctx.given.idxOf? g with
              | some i => s!"ih{i}"
              | none => s!"«{g}».of_eval" ++ String.join ((ctx.needs g).map fun n => s!" ih{ctx.given.idxOf n}")
            return pre ++ [s!"obtain ⟨{kk}, {hk}⟩ := {lem} {c}"] ++
              (← k { fs with fuel := fs.fuel ++ [kk], rw := fs.rw ++ [s!"{hk} k' (by omega)"] })
          else
            let hm ← fresh "hm"
            return pre ++ [s!"have {hm} := {c}.map_row «{g}».none"] ++
              (← k { fs with rw := fs.rw ++ [hm] }))
    | .binary _ l r =>
      let x ← fresh "x"; let y ← fresh "y"; let m ← fresh "m"; let dl ← fresh "d"; let dr ← fresh "d"
      let op ← fresh "op"
      return [s!"obtain ⟨{x}, {y}, {m}, {dl}, {dr}, {op}⟩ := {d}.binary_inv"] ++
        (← prove ctx l dl fs fun fs => prove ctx r dr { fs with rw := fs.rw ++ [op] } k)
    | .load x =>
      let p ← fresh "p"; let dp ← fresh "d"; let ld ← fresh "ld"
      return [s!"obtain ⟨{p}, {dp}, {ld}⟩ := {d}.load_inv"] ++
        (← prove ctx x dp { fs with rw := fs.rw ++ [ld] } k)
    | .index x _ =>
      let p ← fresh "p"; let dp ← fresh "d"; let pr ← fresh "pr"
      return [s!"obtain ⟨{p}, {dp}, {pr}⟩ := {d}.index_inv"] ++
        (← prove ctx x dp { fs with rw := fs.rw ++ [pr] } k)
    | .builtin _ es =>
      let vs ← fresh "vs"; let a ← fresh "args"; let ap ← fresh "ap"
      return [s!"obtain ⟨{vs}, {a}, {ap}⟩ := {d}.builtin_inv"] ++
        (← proveArgs ctx es a { fs with rw := fs.rw ++ [ap] } k)
    | .letValue p x b =>
      let v ← fresh "v"; let m ← fresh "m"; let bs ← fresh "bs"; let dx ← fresh "d"
      let mt ← fresh "mt"; let db ← fresh "d"
      return [s!"obtain ⟨{v}, {m}, {bs}, {dx}, {mt}, {db}⟩ := {d}.letValue_inv"] ++
        (← prove ctx x dx fs fun fs => do
          let steps ← bindPattern p mt
          let (ls, fs) := match steps with | (ls, some hp) => (ls, { fs with rw := fs.rw ++ [hp] }) | (ls, none) => (ls, fs)
          return ls ++ (← prove ctx b db fs k))
    | .matchValue x arms =>
      let v ← fresh "v"; let m ← fresh "m"; let bs ← fresh "bs"; let body ← fresh "body"
      let dx ← fresh "d"; let sel ← fresh "sel"; let db ← fresh "d"
      return [s!"obtain ⟨{v}, {m}, {bs}, {body}, {dx}, {sel}, {db}⟩ := {d}.matchValue_inv"] ++
        (← prove ctx x dx fs fun fs => proveArms ctx arms sel db fs k)
    | _ => throw "expression form"

  partial def bindPattern (p : Pattern F) (mt : String) : M (List String × Option String) := do
    let finish := [s!"simp only [Except.ok.injEq, Option.some.injEq] at {mt}", s!"subst {mt}"]
    match p with
    | .bind _ => return ([s!"rw [matchPattern_bind] at {mt}"] ++ finish, none)
    | .wildcard => return ([s!"rw [matchPattern_wildcard] at {mt}"] ++ finish, none)
    | .tuple ps | .array ps | .construct _ _ ps =>
      let _ ← flatNames ps
      let inv := match p with
        | .tuple _ => "matchPattern_tuple_inv" | .array _ => "matchPattern_array_inv"
        | _ => "matchPattern_construct_inv"
      let ys ← fresh "ys"; let hp ← fresh "hp"; let hl ← fresh "hl"; let ml ← fresh "ml"
      let mut names := []
      for _ in ps do names := names ++ [← fresh "y"]
      return ([s!"obtain ⟨{ys}, {hp}, {hl}, {ml}⟩ := {inv} {mt}",
        s!"rcases {ys} with {rcasesList names} <;> simp at {hl}",
        s!"simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure, Except.pure] at {ml}",
        s!"subst {ml}"], some hp)
    | _ => throw "let pattern"

  partial def proveArms (ctx : Ctx) (arms : List (Pattern F × Expr F)) (sel db : String) (fs : Facts)
      (k : Facts → M (List String)) : M (List String) := do
    match arms with
    | [] => return [s!"simp [SourceSemantics.selectArm] at {sel}"]
    | (.wildcard, b) :: _ =>
      return [s!"obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv {sel}"] ++ (← prove ctx b db fs k)
    | (.literal _, b) :: rest =>
      let hc ← fresh "hc"; let sel' ← fresh "sel"
      let first ← prove ctx b db { fs with rw := fs.rw ++ [hc] } k
      let second ← proveArms ctx rest sel' db { fs with rw := fs.rw ++ [hc] } k
      let bullet (ls : List String) : List String := match ls with
        | [] => []
        | l :: ls => ("· " ++ l) :: ls.map ("  " ++ ·)
      return [s!"rcases selectArm_literal_inv {sel} with ⟨{hc}, rfl, rfl⟩ | ⟨{hc}, {sel'}⟩"] ++
        bullet first ++ bullet second
    | _ => throw "match arm pattern"
end

def finalStep (f : String) (fs : Facts) : List String :=
  let fuel := if fs.fuel.isEmpty then "1" else " + ".intercalate fs.fuel ++ " + 1"
  [s!"refine ⟨{fuel}, fun k hk => ?_⟩",
   "obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩",
   s!"simp (config := \{ decide := true, maxSteps := 10000000 }) [«{f}»{String.join (fs.rw.map (", " ++ ·))}]"]

/-- The mirror of one function. -/
def mirrorDef (ctx : Ctx) (f : Function F) : M String := do
  let ps := f.params.map (var ·.1)
  let body ← block ctx f.body "h"
  let argTys := String.join (f.params.map fun _ => "SourceValue F → ")
  return s!"/-- The mirror of `{f.name}`. -/\ndef «{f.name}» : Nat → Heap F → {argTys}Option (SourceValue F × Heap F)\n" ++
    s!"  | 0, _{String.join (f.params.map fun _ => ", _")} => none\n" ++
    s!"  | k + 1, h{String.join (ps.map (", " ++ ·))} =>\n{ind (ind body)}\n"

/-- **What a mirror lemma says**: every derivation of the function is a run of
its mirror at every large enough fuel. -/
def completeDef (f : Function F) : String :=
  let ps := f.params.map (var ·.1)
  let binders := if ps.isEmpty then "" else s!"\{{" ".intercalate ps} : SourceValue F} "
  s!"/-- Every derivation of `{f.name}` is a run of its mirror. -/\n" ++
  s!"abbrev «{f.name}».Complete : Prop :=\n" ++
  s!"  ∀ {binders}\{h h' : Heap F} \{r : SourceValue F},\n" ++
  s!"    EvalFn W {q f.name} {list ps} h r h' → ∃ k0, ∀ k ≥ k0, «{f.name}» k h {" ".intercalate ps} = some (r, h')\n"

/-- The lemma of one function. -/
def mirrorLemma (ctx : Ctx) (f : Function F) : M String := do
  let ps := f.params.map (var ·.1)
  let script ← prove ctx f.body "body" {} fun fs => pure (finalStep f.name fs)
  let ihs := String.join ((ctx.needs f.name).map fun g => s!" (ih{ctx.given.idxOf g} : «{g}».Complete)")
  let (_, st) := (expr s!"IxVM.Checked.Fn.«{f.name}»" true f.body).run {}
  let fnDefs := ", ".intercalate (s!"IxVM.Checked.Fn.«{f.name}»" ::
    (List.range st.next).map fun i => s!"IxVM.Checked.Fn.«{f.name}».part{i}")
  return s!"theorem «{f.name}».of_eval{ihs} : «{f.name}».Complete := by\n" ++
    s!"  intro {" ".intercalate (ps ++ ["h", "h'", "r", "ev"])}\n" ++
    s!"  have body := ev.function_inv IxVM.Checked.Lookup.«{f.name}»\n" ++
    s!"    (by simp [{fnDefs}, ControlLower.hasControl])\n" ++
    s!"  simp only [{fnDefs}] at body\n" ++
    "\n".intercalate (script.map ("  " ++ ·)) ++ "\n"

/-- The calls of a body: functions and maps. -/
partial def calls : Expr F → List String
  | .call n _ es => n :: es.flatMap calls
  | .tuple es | .array es | .builtin _ es | .update _ es | .record _ es | .construct _ _ _ es
  | .constructAs _ _ _ es => es.flatMap calls
  | .letValue _ x b | .binary _ x b => calls x ++ calls b
  | .matchValue x arms => calls x ++ arms.flatMap (calls ·.2)
  | .member x _ | .repeat x _ | .index x _ | .slice x _ _ | .project x _ | .store x | .load x
  | .hint _ x _ | .neg x | .control _ x => calls x
  | _ => []

end MirrorGen

/-- **The mirrors of a closure**: the functions reachable from `roots`, callees
first, each with its mirror, and a lemma where the generator handles it. -/
def mirrors (prog : Program F) (src : Aiur.Generic.Source F) (roots : List String) (title : String) :
    String := Id.run do
  -- the closure, callees first
  let fnOf (n : String) := prog.functions.find? (·.name == n)
  let mut order : List String := []
  let mut maps : List String := []
  let mut stack : List (String × Bool) := roots.reverse.map (·, false)
  let mut seen : List String := []
  while !stack.isEmpty do
    match stack with
    | [] => break
    | (n, done) :: rest =>
      stack := rest
      if done then
        if !order.contains n then order := order ++ [n]
      else if !seen.contains n then
        seen := seen ++ [n]
        match fnOf n with
        | none => if !maps.contains n then maps := maps ++ [n]
        | some f =>
          stack := (n, true) :: stack
          for c in (MirrorGen.calls f.body).eraseDups do
            if c != n && !seen.contains c then stack := (c, false) :: stack
  let reach (n : String) : List String := Id.run do
    let mut acc : List String := []
    let mut todo := [n]
    for _ in [0:100000] do
      match todo with
      | [] => break
      | m :: rest =>
        todo := rest
        if !acc.contains m then
          acc := acc ++ [m]
          if let some f := fnOf m then todo := todo ++ (MirrorGen.calls f.body)
    return acc
  -- recursive and mutually recursive functions are not proved by the generator; callers assume them
  let recursive := order.filter fun n => match fnOf n with
    | some f => (MirrorGen.calls f.body).any fun c => (fnOf c).isSome && (reach c).contains n
    | none => false
  let needs (n : String) : List String :=
    recursive.filter fun g => g != n && (reach n).contains g
  let mut out := header ["Ix.IxVM.Refinement.Mirror", "IxVM.Checked.Lookup"] s!"Generated mirrors: {title}." ++
    "end IxVM.Checked\n\nnamespace IxVM.Refinement.Mirrors\n\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option maxHeartbeats 4000000\n\n" ++
    "open Aiur Aiur.Generic Aiur.Generic.SourceSemantics\nopen IxVM.Checked (F)\n\n" ++
    "/-- The checked source's world. -/\nabbrev W : World F := IxVM.Checked.source.world\n\n"
  let mut report : List String := []
  for m in maps do
    let idx := (prog.maps.map (·.name)).idxOf m
    out := out ++ s!"theorem «{m}».none : IxVM.Checked.source.program.sourceFunction? {q m} = none :=\n" ++
      s!"  Program.sourceFunction?_of_key\n    (IxVM.Checked.mapKeys_fresh _ (List.getElem_mem (l := IxVM.Checked.maps) (n := {idx}) (by decide)))\n" ++
      "    (head_ne_of_bytes (by decide +kernel))\n\n"
  let mut defined : List String := []
  for n in order do
    let some f := fnOf n | continue
    let ctx : MirrorGen.Ctx := { prog, src, given := recursive, needs, defined, self := n }
    match (MirrorGen.mirrorDef ctx f).run' 0 with
    | .error e => report := report ++ [s!"{n}: no mirror ({e})"]
    | .ok d =>
      defined := defined ++ [n]
      out := out ++ d ++ "\n" ++ MirrorGen.completeDef f ++ "\n"
      if recursive.contains n then
        report := report ++ [s!"{n}: mirror only (recursive)"]
      else match (MirrorGen.mirrorLemma ctx f).run' 0 with
        | .error e => report := report ++ [s!"{n}: mirror only ({e})"]
        | .ok l =>
          out := out ++ l ++ "\n"
          report := report ++ [s!"{n}: mirror and lemma"]
  let doc := "/-! Generator report:\n\n" ++ String.join (report.map (s!"* " ++ · ++ "\n")) ++ "-/\n\n"
  return out ++ doc ++ "end IxVM.Refinement.Mirrors\n"

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
  files := files ++ [(System.FilePath.mk "IxVM/IxVM/Checked/Lookup.lean", lookup prog fnNames)]
  files := files ++ [(System.FilePath.mk "Ix/IxVM/Refinement/Mirrors/TagN.lean",
    mirrors prog prepared.environment.source
      ["IxonDeserialize::get_tagn0", "IxonDeserialize::get_tagn2", "IxonDeserialize::get_tagn4"]
      "the TagN decoders and their callees")]
  return files

end IxVM.CheckedGen
