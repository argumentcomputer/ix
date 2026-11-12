import IxCCTests.Src.Artifact
import IxCCTests.Anf.LeanRender
import IxCCTests.Pipeline.Support
import IxCCTests.Recheck.Stages
import Std.Data.HashMap

/-! # Recheck artifacts as kernel terms

The whole recheck path's input for one bench-k1 closure — the `Src.Program`
as ingress leaves it (no table), the configuration and the certificate
`produce` makes — printed as Lean modules, so that `decide +kernel` can
evaluate `Recheck.run` on it. Beside the input, each
artifact records what the native run computes: the laid-out typed x86
program (`Recheck.runTyped`) and the object's bytes (`Recheck.run`), which
the kernel modules (`IxCCTests.Recheck.Kernel`) state as equalities.

**Sharing.** Ingress's terms are DAGs; printed as trees, sum-loop's
program had 1.68 M nodes when it was among the artifacts. The printer hash-conses every term of the program
(bottom-up: a node's key is its constructor, payload and its children's
numbers) and hoists into its own definition `t<i>` every node that is used
more than once (and is not tiny), and every node whose inline text grows
past a bound. The kernel unfolds `t<i>` where the evaluation reaches it and
never re-expands it in the term, so the artifact's size and the kernel's
input are the DAG's. Constants are `c<i>`, addresses `a<i>` (byte lists,
read only as numbers by the pins and as bytes by the provenance note).

The printer reuses `IxCCTests.Src.Artifact`'s term syntax and
`IxCCTests.Anf.LeanRender`'s middle-end certificate syntax; the
backend's certificate parts, the typed program and the root records are
printed with their derived `Repr`. `lake exe gen-recheck-artifacts`
regenerates the committed modules under `IxCCTests/Recheck/Artifacts/`;
`tests-recheck` compares them with a fresh `ingress` + `produce` + `run`. -/

namespace IxCCTests.Recheck.Artifact

open IxCC IxCC.Src IxCC.Src.Relevance IxCC.Recheck IxCC.Ixon
open IxCCTests.Src.Artifact (paren listOf line univ propWhen rel mode binder valueContract
  defKind safety quotKind natMapK natMap fieldClass tag termKey known bytes primOp)

/-! ## Hash-consing the program's terms -/

/-- One DAG node: its text is `parts[0] ++ kid₀ ++ parts[1] ++ … ++ parts[n]`,
each kid printed as its definition's name or inline. -/
structure Node where
  parts : List String
  kids : List Nat
  deriving Inhabited

structure Dag where
  ids : Std.HashMap String Nat := {}
  nodes : Array Node := #[]
  /-- Tree nodes visited (the size of the terms printed as trees). -/
  tree : Nat := 0

def Dag.intern (parts : List String) (kids : List Nat) : StateM Dag Nat := do
  let key := String.intercalate "#" (parts ++ kids.map toString) ++ s!"/{kids.length}"
  let d ← get
  match d.ids[key]? with
  | some i => pure i
  | none =>
    let i := d.nodes.size
    set { d with ids := d.ids.insert key i, nodes := d.nodes.push ⟨parts, kids⟩ }
    pure i

def tick : StateM Dag Unit := modify fun d => { d with tree := d.tree + 1 }

/-- Intern a term bottom-up (children before parents, so a node's number
exceeds its children's). -/
def internTerm : Term → StateM Dag Nat
  | .var i => do tick; Dag.intern [paren s!".var {i}"] []
  | .sort u => do tick; Dag.intern [paren s!".sort {univ u}"] []
  | .const c us => do tick; Dag.intern [paren s!".const {c} {listOf univ us}"] []
  | .app f a m r => do
    tick
    let f ← internTerm f
    let a ← internTerm a
    Dag.intern ["(.app ", " ", s!" {mode m} {rel r})"] [f, a]
  | .lam b d t => do
    tick
    let d ← internTerm d
    let t ← internTerm t
    Dag.intern [s!"(.lam {binder b} ", " ", ")"] [d, t]
  | .pi b res d t => do
    tick
    let d ← internTerm d
    let t ← internTerm t
    Dag.intern [s!"(.pi {binder b} {valueContract res} ", " ", ")"] [d, t]
  | .letE c r ty v b => do
    tick
    let ty ← internTerm ty
    let v ← internTerm v
    let b ← internTerm b
    Dag.intern [s!"(.letE {line c} {rel r} ", " ", " ", ")"] [ty, v, b]
  | .proj s i e => do
    tick
    let e ← internTerm e
    Dag.intern [s!"(.proj {s} {i} ", ")"] [e]
  | .natLit n => do tick; Dag.intern [paren s!".natLit {n}"] []
  | .strLit s => do tick; Dag.intern [paren s!".strLit {s.quote}"] []

/-- A declaration with its terms replaced by DAG numbers. -/
inductive DeclRef where
  | defn (k : DefKind) (s : DefinitionSafety) (l : Nat) (ty v : Nat)
  | induct (s : Bool) (l np ni : Nat) (ty : Nat) (cs : List CId)
  | ctor (s : Bool) (l : Nat) (ind : CId) (cidx np nf : Nat) (ty : Nat)
  | recr (s k : Bool) (l np nmot nmin ni : Nat) (ind : CId) (rules : List (CId × Nat × Nat)) (ty : Nat)
  | quot (k : QuotKind) (l : Nat) (ty : Nat)
  | axio (s : Bool) (l : Nat) (ty : Nat)

def internDecl : Decl → StateM Dag DeclRef
  | .defn k s l ty v => do pure (.defn k s l (← internTerm ty) (← internTerm v))
  | .induct s l np ni ty cs => do pure (.induct s l np ni (← internTerm ty) cs)
  | .ctor s l ind cidx np nf ty => do pure (.ctor s l ind cidx np nf (← internTerm ty))
  | .recr s k l np nmot nmin ni ind rules ty => do
    let rules ← rules.mapM fun r => do pure (r.ctor, r.fields, ← internTerm r.rhs)
    pure (.recr s k l np nmot nmin ni ind rules (← internTerm ty))
  | .quot k l ty => do pure (.quot k l (← internTerm ty))
  | .axio s l ty => do pure (.axio s l (← internTerm ty))

def DeclRef.roots : DeclRef → List Nat
  | .defn _ _ _ ty v => [ty, v]
  | .induct _ _ _ _ ty _ | .ctor _ _ _ _ _ _ ty | .quot _ _ ty | .axio _ _ ty => [ty]
  | .recr _ _ _ _ _ _ _ _ rules ty => ty :: rules.map (·.2.2)

/-- Which nodes get their own definition: used at least twice and longer
than `tiny` characters inline, or longer than `long` inline. Returns the
choice and each node's inline length. -/
def hoist (d : Dag) (roots : List Nat) (tiny long : Nat) : Array Bool × Array Nat := Id.run do
  let n := d.nodes.size
  let mut uses : Array Nat := Array.replicate n 0
  for node in d.nodes do
    for k in node.kids do uses := uses.modify k (· + 1)
  for r in roots do uses := uses.modify r (· + 1)
  let mut hoisted : Array Bool := Array.replicate n false
  let mut len : Array Nat := Array.replicate n 0
  for i in [0:n] do
    let node := d.nodes[i]!
    let own := node.parts.foldl (· + ·.length) 0
    let kidsLen := node.kids.foldl (fun s k => s + if hoisted[k]! then (toString k).length + 1 else len[k]!) 0
    let l := own + kidsLen
    len := len.set! i l
    if (uses[i]! ≥ 2 && l > tiny) || l > long then hoisted := hoisted.set! i true
  return (hoisted, len)

/-- A node's text with hoisted kids named. -/
partial def nodeText (d : Dag) (hoisted : Array Bool) (i : Nat) : String :=
  let node := d.nodes[i]!
  let kids := node.kids.map fun k => if hoisted[k]! then s!"t{k}" else nodeText d hoisted k
  let rec weave : List String → List String → String
    | p :: ps, k :: ks => p ++ k ++ weave ps ks
    | ps, [] => String.join ps
    | [], _ => ""
  weave node.parts kids

/-- A reference to node `i` where a term is expected. -/
def refText (d : Dag) (hoisted : Array Bool) (i : Nat) : String :=
  if hoisted[i]! then s!"t{i}" else nodeText d hoisted i

/-! ## Rendering -/

def declText (r : Nat → String) : DeclRef → String
  | .defn k s l ty v => paren s!".defn {defKind k} {safety s} {l}\n    {r ty}\n    {r v}"
  | .induct s l np ni ty cs => paren s!".induct {s} {l} {np} {ni}\n    {r ty} {cs}"
  | .ctor s l ind cidx np nf ty => paren s!".ctor {s} {l} {ind} {cidx} {np} {nf}\n    {r ty}"
  | .recr s k l np nmot nmin ni ind rules ty =>
    let rs := listOf (fun ((c, f, rhs) : CId × Nat × Nat) =>
      s!"\{ ctor := {c}, fields := {f}, rhs := {r rhs} }") rules
    paren s!".recr {s} {k} {l} {np} {nmot} {nmin} {ni} {ind}\n    {rs}\n    {r ty}"
  | .quot k l ty => paren s!".quot {quotKind k} {l}\n    {r ty}"
  | .axio s l ty => paren s!".axio {s} {l}\n    {r ty}"

def entryText : Table.Entry → String
  | .prim op => paren s!".prim {primOp op}"
  | .csimp g thm => paren s!".csimp {g} {thm}"
  | .eqn thm => paren s!".eqn {thm}"
  | .case => ".case"

/-! Nested values are printed on one line each: structure-instance fields
on separate lines must share a column, which a nested position cannot
promise. -/

def tableCertText (c : Table.TableCert) : String :=
  s!"\{ resolve := {listOf (fun ((f, e) : CId × Table.Entry) => s!"({f}, {entryText e})") c.resolve}, \
    recKind := {c.recKind}, lazy := {c.lazy}, inline := {c.inline}, opaqueByValue := {c.opaqueByValue} }"

def annText (ann : Ann) : String :=
  s!"\{ consts := {natMap (fun (r : ConstRel) =>
      s!"\{ result := {rel r.result}, params := {listOf rel r.params} }") ann.consts}, \
    ctors := {natMap (fun (r : CtorRel) => s!"\{ fields := {listOf fieldClass r.fields} }") ann.ctors}, \
    nodes := {listOf (fun ((k, ts) : TermKey × List Tag) => s!"({termKey k}, {listOf tag ts})") ann.nodes} }"

def midText (c : Anf.Pipeline.Cert) : String :=
  s!"\{ shrink := \{ caseOfCase := {c.shrink.caseOfCase}, smallJoin := {c.shrink.smallJoin} }, \
    steps := {listOf IxCCTests.Anf.LeanRender.step c.steps} }"

/-- A value by its derived `Repr`, on one line. -/
def reprText {α : Type} [Repr α] (x : α) : String := (repr x).pretty 1000000000

def configText (cfg : Config) : String :=
  s!"\{ names := {listOf String.quote cfg.names} }"

/-- What the native run computes, recorded beside the input. -/
structure Expected where
  /-- `runTyped`'s laid-out typed program. -/
  typed : X86.Program
  /-- The object's bytes. -/
  object : List UInt8
  /-- `Stages.upTo` at every stage, in `Stage.all` order. -/
  stages : List (Option (List Nat))
  /-- The ELF writer's input: the encoded text, block offsets and
  relocations, the entry block, the export names and the provenance. -/
  elf : X86.ELF.Input

/-- The ELF writer's input as a term (the provenance root as its bytes). -/
def elfText (i : X86.ELF.Input) : String :=
  let prov := match i.provenance with
    | .ixir1Policy root l p => s!"(.ixir1Policy (addr {bytes root}) {l} {p})"
    | .ixir2 root => s!"(.ixir2 (addr {bytes root}))"
  s!"\{ encoded := X86.Encode.Output.ofLists {i.encoded.text.data.toList} {i.encoded.blockOffsets.toList} \
    {reprText i.encoded.relocations.toList}, entryBlock := {i.entryBlock}, exportName := {i.exportName.quote}, \
    exports := {listOf (fun ((n, b) : String × X86.BlockId) => s!"({n.quote}, {b})") i.exports}, \
    provenance := {prov} }"

/-- One artifact: the input and the native results. -/
structure Input where
  name : String
  modName : String
  /-- What the module's header says the program is (the bench-k1 closure
  when `none`). -/
  origin : Option String := none
  program : Program
  cfg : Config
  cert : Cert
  expected : Expected

/-- The artifact's module text, and statistics for the log. -/
def render (a : Input) (tiny : Nat := 24) (long : Nat := 2000) : String × String := Id.run do
  let p := a.program
  let entries := p.entries.zipIdx
  let (refs, dag) := (entries.mapM fun ((e, _) : ConstEntry × Nat) => internDecl e.decl).run ({} : Dag)
  let roots := refs.flatMap DeclRef.roots
  let (hoisted, _) := hoist dag roots tiny long
  let r := refText dag hoisted
  let addrs := Src.Artifact.addresses p
  let addrName := fun (x : IxCC.Ixon.Address) => s!"a{(addrs.findIdx? (· == x)).getD 0}"
  let cref : CRef → String
    | .member x i => paren s!".member {addrName x} {i}"
    | .ctor x i c => paren s!".ctor {addrName x} {i} {c}"
  let hoistedCount := (hoisted.toList.filter id).length
  let originText := match a.origin with
    | some o => o
    | none => s!"The `{a.name}` bench-k1 closure"
  let fromText := if a.origin.isSome then "its closure" else s!"`fixtures/ixon-v4/bench-k1/{a.name}.ixe`"
  let genText := if a.origin.isSome then "`lake exe corpus kernel-artifacts`" else "`lake exe gen-recheck-artifacts`"
  let mut out := s!"import IxCC.Recheck.Run

/-! {originText} as `Recheck.run`'s input: the `Src.Program`
ingress makes from {fromText} ({p.size} constants, no table),
the configuration and `produce`'s certificate, with the laid-out typed program and the
object's bytes the native run computes. Terms are shared: {dag.tree} tree nodes, {dag.nodes.size}
DAG nodes, {hoistedCount} of them hoisted into definitions `t<i>`. Generated by
{genText} (`IxCCTests.Recheck.Artifact`); do not edit. -/

namespace IxCCTests.Recheck.Artifacts.{a.modName}

open IxCC IxCC.Src IxCC.Src.Relevance

set_option maxRecDepth 100000

/-- An address from its 32 bytes. -/
private def addr (bs : List UInt8) : IxCC.Ixon.Address :=
  (IxCC.Ixon.Address.ofBytes? ⟨bs.toArray⟩).getD default

"
  for (x, i) in addrs.toList.zipIdx do
    out := out ++ s!"noncomputable def a{i} : Ixon.Address := addr {bytes x}\n"
  out := out ++ "\n"
  for i in [0:dag.nodes.size] do
    if hoisted[i]! then
      out := out ++ s!"noncomputable def t{i} : Term := {nodeText dag hoisted i}\n"
  out := out ++ "\n"
  for ((e, c), ref) in entries.zip refs do
    out := out ++ s!"noncomputable def c{c} : ConstEntry :=\n  \{ ref := {cref e.ref}, addr := {addrName e.addr}\n    \
      decl := {declText r ref} }\n\n"
  out := out ++ s!"/-- The program as ingress leaves it: constants, roots and pinned identities. -/
noncomputable def program : Program :=
  \{ consts := {natMapK (fun c (_ : ConstEntry) => s!"c{c}") p.consts 0 1}
    size := {p.size}
    roots := {listOf (fun ((x, c) : IxCC.Ixon.Address × CId) => s!"({addrName x}, {c})") p.roots}
    known := {known p.known}
    byStatement := {Src.Artifact.natMap (fun (_ : Unit) => "()") p.byStatement} }

/-- The configuration (the roots' names). -/
def cfg : Recheck.Config := {configText a.cfg}

/-- `produce`'s certificate. -/
noncomputable def cert : Recheck.Cert :=
  \{ table := {tableCertText a.cert.table}
    relevance := {annText a.cert.relevance}
    mid := {midText a.cert.mid}
    alloc := {reprText a.cert.alloc}
    frames := {reprText a.cert.frames}
    order := {reprText a.cert.order} }

/-- The laid-out typed x86 program the native `Recheck.runTyped` computes. -/
def typed : X86.Program :=
  {reprText a.expected.typed}

/-- The object's bytes the native `Recheck.run` computes ({a.expected.object.length} bytes). -/
def object : List UInt8 :=
  {a.expected.object}

/-- `Stages.upTo` at every stage (`Stages.Stage.all`), computed natively. -/
def stages : List (Option (List Nat)) :=
  {a.expected.stages}

/-- The ELF writer's input the native run computes (for measuring the
writer and its validator alone). -/
noncomputable def elfInput : X86.ELF.Input :=
  {elfText a.expected.elf}

end IxCCTests.Recheck.Artifacts.{a.modName}
"
  let stats := s!"{a.name}: {p.size} constants, tree {dag.tree}, dag {dag.nodes.size}, hoisted {hoistedCount}, \
    {out.length} bytes"
  return (out, stats)

/-! ## The artifacts -/

/-- The artifacts: fixture name and module name. -/
def artifacts : List (String × String) :=
  [("fib", "Fib"), ("tak", "Tak"), ("gcd", "Gcd"), ("even-odd", "EvenOdd"), ("sfib", "Sfib")]

def path (modName : String) : System.FilePath :=
  "IxCCTests/Recheck/Artifacts" / s!"{modName}.lean"

/-- `produce` and the native run on an ingressed closure. -/
def loadFrom (name modName : String) (inp : Recheck.Input) (origin : Option String := none) : IO Input := do
  let cfg : Config := { names := inp.names }
  let cert ← IxCCTests.Pipeline.ofErr s!"{name}: produce" fun _ => produce cfg inp
  let t ← IxCCTests.Pipeline.ofErr s!"{name}: runTyped" fun _ => runTyped cfg inp.program cert
  let a ← IxCCTests.Pipeline.ofErr s!"{name}: run" fun _ => run cfg inp.program cert
  let b := a.backend
  let elf : X86.ELF.Input :=
    { encoded := b.encoded, entryBlock := b.program.entry, exportName := b.exportName
      exports := b.exports.filter (·.1 != b.exportName), provenance := t.provenance }
  pure { name, modName, origin, program := inp.program, cfg, cert
         expected := { typed := t.program, object := a.object.data.toList
                       stages := Stages.Stage.all.map fun s => Stages.upTo s cfg inp.program cert
                       elf } }

/-- Ingress, `produce` and the native run on a bench-k1 closure. -/
def load (name modName : String) : IO Input := do
  loadFrom name modName (← IxCCTests.Pipeline.benchInput name)

/-- Write the modules, or with `--check` compare them with the committed
ones (exit 1 on a difference). `--only NAME` restricts to one artifact. -/
def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let only := match args.dropWhile (· != "--only") with
    | _ :: n :: _ => some n
    | _ => none
  let mut stale := 0
  for (name, modName) in artifacts do
    if only.any (· != name) then continue
    let a ← load name modName
    let (text, stats) := render a
    let file := path modName
    if check then
      let old ← (IO.FS.readFile file).toBaseIO
      if (match old with | .ok o => o == text | .error _ => false) then
        IO.println s!"{file}: current"
      else
        IO.eprintln s!"{file}: stale (run lake exe gen-recheck-artifacts)"
        stale := stale + 1
    else
      IO.FS.writeFile file text
      IO.println s!"{file}: {stats}"
  return if stale == 0 then 0 else 1

end IxCCTests.Recheck.Artifact
