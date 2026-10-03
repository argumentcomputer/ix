import CompilatrixTests.Src.Support

/-! # K1 artifacts as kernel terms

The recheck path's input for one bench-k1 closure — the `Src.Program` that
ingress, the pinned identities and `Table.build` produce, and the relevance
annotation — printed as a Lean module, so that `decide +kernel` can evaluate
`Src.Recheck.run` and erasure on it (M1.K1, M2.8). The loader decodes bytes
natively; the printed module is its output as data, with no decoding left
for the kernel.

The printer writes every constant as its own definition, the `NatMap`s as
literal tries (no insertion left for the kernel), the addresses as byte
lists (read only by the pins) and every other value in constructor syntax.
The definitions are `noncomputable`: only the kernel reads them, so no code
is generated. `lake exe gen-src-artifacts` regenerates the committed modules
under `CompilatrixTests/Src/Artifacts/`; `--check` compares them with a
fresh load. Terms are printed as trees (ingress's sharing is not kept), so
this suits the small closures (fib, tak, gcd), not sum-loop or ackermann. -/

namespace CompilatrixTests.Src.Artifact

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance Compilatrix.Ixon

/-- Single-line `repr`, for the contract records. -/
def line {α : Type} [Repr α] (x : α) : String := (repr x).pretty 100000

def paren (s : String) : String := s!"({s})"

def listOf {α : Type} (f : α → String) (xs : List α) : String :=
  "[" ++ ", ".intercalate (xs.map f) ++ "]"

def univ : Univ → String
  | .zero => ".zero"
  | .succ u => paren s!".succ {univ u}"
  | .max a b => paren s!".max {univ a} {univ b}"
  | .imax a b => paren s!".imax {univ a} {univ b}"
  | .var i => paren s!".var {i}"

def propWhen : PropWhen → String
  | .never => ".never"
  | .allZero ps => paren s!".allZero {ps}"

def rel : Rel → String
  | .rel => ".rel"
  | .proof w => paren s!".proof {propWhen w}"
  | .type => ".type"

def mode : Mode → String
  | .strict => ".strict"
  | .byName => ".byName"

def binderContract (c : V3.BinderContract) : String :=
  if c == {} then "{}" else line c

def valueContract (c : V3.ValueContract) : String :=
  if c == {} then "{}" else line c

def binder (b : Binder) : String :=
  let fields := (if b.contract == {} then [] else [s!"contract := {binderContract b.contract}"]) ++
    (if b.rel == .rel then [] else [s!"rel := {rel b.rel}"]) ++
    (if b.propWhen == .never then [] else [s!"propWhen := {propWhen b.propWhen}"])
  if fields.isEmpty then "{}" else "{ " ++ ", ".intercalate fields ++ " }"

def term : Term → String
  | .var i => paren s!".var {i}"
  | .sort u => paren s!".sort {univ u}"
  | .const c us => paren s!".const {c} {listOf univ us}"
  | .app f a m r => paren s!".app {term f} {term a} {mode m} {rel r}"
  | .lam b d t => paren s!".lam {binder b} {term d} {term t}"
  | .pi b res d t => paren s!".pi {binder b} {valueContract res} {term d} {term t}"
  | .letE c r ty v b => paren s!".letE {line c} {rel r} {term ty} {term v} {term b}"
  | .proj s i e => paren s!".proj {s} {i} {term e}"
  | .natLit n => paren s!".natLit {n}"
  | .strLit s => paren s!".strLit {s.quote}"

def defKind : DefKind → String
  | .defn => ".defn" | .opaq => ".opaq" | .thm => ".thm"

def safety : DefinitionSafety → String
  | .unsaf => ".unsaf" | .safe => ".safe" | .part => ".part"

def quotKind : QuotKind → String
  | .type => ".type" | .ctor => ".ctor" | .lift => ".lift" | .ind => ".ind"

def rule (r : Rule) : String :=
  s!"\{ ctor := {r.ctor}, fields := {r.fields}, rhs := {term r.rhs} }"

def decl : Decl → String
  | .defn k s l ty v => paren s!".defn {defKind k} {safety s} {l}\n    {term ty}\n    {term v}"
  | .induct s l np ni ty cs => paren s!".induct {s} {l} {np} {ni}\n    {term ty} {cs}"
  | .ctor s l ind cidx np nf ty => paren s!".ctor {s} {l} {ind} {cidx} {np} {nf}\n    {term ty}"
  | .recr s k l np nmot nmin ni ind rules ty =>
    paren s!".recr {s} {k} {l} {np} {nmot} {nmin} {ni} {ind}\n    \
      {listOf rule rules}\n    {term ty}"
  | .quot k l ty => paren s!".quot {quotKind k} {l}\n    {term ty}"
  | .axio s l ty => paren s!".axio {s} {l}\n    {term ty}"

/-- A trie, literally; `f` receives each value's key (the subtrie's root
holds key `k`, its children add bit weight `w`). -/
def natMapK {α : Type} (f : Nat → α → String) : NatMap α → Nat → Nat → String
  | .leaf, _, _ => ".leaf"
  | .node v z o, k, w =>
    let v := match v with
      | some x => paren s!"some {f k x}"
      | none => "none"
    paren s!".node {v} {natMapK f z k (2 * w)} {natMapK f o (k + w) (2 * w)}"

def natMap {α : Type} (f : α → String) (m : NatMap α) : String := natMapK (fun _ x => f x) m 0 1

def primOp (op : PrimOp) : String := s!".{op.name}"

def resolve : Resolve → String
  | .prim op => paren s!".prim {primOp op}"
  | .csimp g us thm => paren s!".csimp {g} {listOf univ us} {thm}"
  | .eqn thm body => paren s!".eqn {thm}\n    {term body}"
  | .case r => paren s!".case {r}"

def fieldSrc : FieldSrc → String
  | .index i => paren s!".index {i}"
  | .proof => ".proof"

def recKind : RecKind → String
  | .ordinary => ".ordinary"
  | .subsingleton w fs => paren s!".subsingleton {propWhen w} {listOf fieldSrc fs}"
  | .empty => ".empty"

def fieldClass : FieldClass → String
  | .keep => ".keep"
  | .proof w => paren s!".proof {propWhen w}"
  | .type => ".type"

def tag : Tag → String
  | .lam r w => paren s!".lam {rel r} {propWhen w}"
  | .arg r => paren s!".arg {rel r}"
  | .letE r => paren s!".letE {rel r}"

def termKey : TermKey → String
  | .value c => paren s!".value {c}"
  | .eqn c => paren s!".eqn {c}"
  | .rule r j => paren s!".rule {r} {j}"

def optId : Option CId → String
  | some c => paren s!"some {c}"
  | none => "none"

def known (k : Known) : String :=
  s!"\n      \{ nat := {optId k.nat}, natZero := {optId k.natZero}, natSucc := {optId k.natSucc},\n        \
    natRec := {optId k.natRec}, bool := {optId k.bool}, boolTrue := {optId k.boolTrue},\n        \
    boolFalse := {optId k.boolFalse}, eq := {optId k.eq}, decIsFalse := {optId k.decIsFalse},\n        \
    decIsTrue := {optId k.decIsTrue} }"

/-- The addresses a program mentions, in first-use order. -/
def addresses (p : Program) : Array Compilatrix.Ixon.Address := Id.run do
  let mut out : Array Compilatrix.Ixon.Address := #[]
  for e in p.entries do
    let block := match e.ref with
      | .member a _ | .ctor a _ _ => a
    for a in [block, e.addr] do
      unless out.contains a do out := out.push a
  for (a, _) in p.roots do
    unless out.contains a do out := out.push a
  return out

def bytes (a : Compilatrix.Ixon.Address) : String :=
  listOf (fun (b : UInt8) => s!"{b}") a.hash.data.toList

/-- One bench-k1 artifact's module text. -/
def render (name modName : String) (p : Program) (ann : Ann) : String := Id.run do
  let addrs := addresses p
  let addrName := fun (a : Compilatrix.Ixon.Address) => s!"a{(addrs.findIdx? (· == a)).getD 0}"
  let cref : CRef → String
    | .member a i => paren s!".member {addrName a} {i}"
    | .ctor a i c => paren s!".ctor {addrName a} {i} {c}"
  let mut out := s!"import Compilatrix.Src.Relevance.Syntax

/-! The `{name}` bench-k1 closure as recheck-path input (M1.K1): its `Src.Program`
({p.size} constants, with the table `Table.build` gives) and its relevance
annotation, from `fixtures/ixon-v4/bench-k1/{name}.ixe`. Generated by
`lake exe gen-src-artifacts` (`CompilatrixTests.Src.Artifact`); do not edit. -/

namespace CompilatrixTests.Src.Artifacts.{modName}

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance

set_option maxRecDepth 100000

/-- An address from its 32 bytes (read only by the pins). -/
private def addr (bs : List UInt8) : Compilatrix.Ixon.Address :=
  (Compilatrix.Ixon.Address.ofBytes? ⟨bs.toArray⟩).getD default

"
  for (a, i) in addrs.toList.zipIdx do
    out := out ++ s!"noncomputable def a{i} : Ixon.Address := addr {bytes a}\n"
  out := out ++ "\n"
  for c in [0:p.size] do
    let some e := p.entry? c | continue
    out := out ++ s!"noncomputable def c{c} : ConstEntry :=\n  \{ ref := {cref e.ref}, addr := {addrName e.addr}\n    \
      decl := {decl e.decl} }\n\n"
  let t := p.table
  out := out ++ s!"noncomputable def table : Table :=
  \{ resolve := {natMap resolve t.resolve}
    recKind := {natMap recKind t.recKind}
    lazy := {natMap (fun (n : Nat) => s!"{n}") t.lazy}
    inline := {natMap (fun (_ : Unit) => "()") t.inline}
    opaqueByValue := {natMap (fun (_ : Unit) => "()") t.opaqueByValue} }

/-- The program: ingress, the pinned identities and the built table. -/
noncomputable def program : Program :=
  \{ consts := {natMapK (fun c (_ : ConstEntry) => s!"c{c}") p.consts 0 1}
    size := {p.size}
    table
    roots := {listOf (fun ((a, c) : Compilatrix.Ixon.Address × CId) => s!"({addrName a}, {c})") p.roots}
    known := {known p.known} }

/-- The relevance annotation (the annotator's output for the program). -/
noncomputable def ann : Ann :=
  \{ consts := {natMap (fun (r : ConstRel) =>
        s!"\{ result := {rel r.result}, params := {listOf rel r.params} }") ann.consts}
    ctors := {natMap (fun (r : CtorRel) => s!"\{ fields := {listOf fieldClass r.fields} }") ann.ctors}
    nodes := {listOf (fun ((k, ts) : TermKey × List Tag) =>
      s!"({termKey k},\n      {listOf tag ts})") ann.nodes} }

end CompilatrixTests.Src.Artifacts.{modName}
"
  return out

/-- The artifacts: fixture name and module name. -/
def artifacts : List (String × String) := [("fib", "Fib"), ("tak", "Tak"), ("gcd", "Gcd")]

def path (modName : String) : System.FilePath :=
  "CompilatrixTests/Src/Artifacts" / s!"{modName}.lean"

/-- Load a bench-k1 closure as the recheck path receives it: the prepared
program (before installation) and the annotator's annotation. -/
def load (name : String) : IO (Program × Ann) := do
  let bytes ← IO.FS.readBinFile (fixtures / "bench-k1" / s!"{name}.ixe")
  let json ← IO.ofExcept (Lean.Json.parse
    (← IO.FS.readFile (fixtures / "bench-k1" / s!"{name}.equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (Compilatrix.Ixon.V3.decodeAnonymousEnv bytes)
  let (p, _, _) ← IO.ofExcept ((prepare { typecheck := false } env hints).mapError toString)
  let ann ← IO.ofExcept (Relevance.annotate env p)
  return (p, ann)

/-- Write the modules, or with `check` compare them with the committed ones
(exit 1 on a difference). -/
def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let mut stale := 0
  for (name, modName) in artifacts do
    let (p, ann) ← load name
    let text := render name modName p ann
    let file := path modName
    if check then
      let old ← (IO.FS.readFile file).toBaseIO
      if (match old with | .ok o => o == text | .error _ => false) then
        IO.println s!"{file}: current"
      else
        IO.eprintln s!"{file}: stale (run lake exe gen-src-artifacts)"
        stale := stale + 1
    else
      IO.FS.writeFile file text
      IO.println s!"{file}: {p.size} constants, {text.length} bytes"
  return if stale == 0 then 0 else 1

end CompilatrixTests.Src.Artifact
