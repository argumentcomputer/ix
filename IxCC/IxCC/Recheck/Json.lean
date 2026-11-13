import IxCC.Recheck.Cert
import IxCC.Recheck.Err
import IxCC.Src.Hints
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Lean.Data.Json.FromToJson

/-! # The certificate as JSON

The serialisation of `Recheck.Cert` (format `ixcc/cert/1`). The file
is untrusted data like the certificate itself: `run` accepts or rejects what
it decodes, so the format carries no checksum and no identity of the program
it was made for. It is compact (positional arrays, one-letter tags), since
the relevance annotation of a large closure has many entries:

| Value | JSON |
| --- | --- |
| `PropWhen` | `"n"` (never) or the parameters that must all be zero, `[i, …]` |
| `Rel` | `"r"`, `"t"`, `["p", W]` |
| `FieldClass` | `"k"`, `"t"`, `["p", W]` |
| `TermKey` | `["v", c]` (value), `["q", c]` (eqn body), `["u", r, j]` (rule) |
| `Tag` | `["l", R, W]`, `["a", R]`, `["e", R]` |
| table entry | `["prim", op]`, `["word", name, thm]` (`name` as `UInt64.add`), `["csimp", g, thm]`, `["eqn", thm]`, `["case"]` |
| Anf step | `["P2", rounds]`, `["P3", [[caller, [callee, …]], …]]`, `["P4", inv, [[caller, callee, mask], …]]`, `["prune"]` |
| `Loc` | a register name, `["s", i]`, `["i", i]`, `["o", i]` |
| allocation | `[numSlots, [[locs, termLocs, [[i, dst, src], …], [[loc, [v, …]], …]], …]]` |
| frame layout | `[size, [slot offsets], [[register, offset], …], outArgs]` |

`ofJson (toJson c)` gives back `c` (tested by `tests-pipeline`). -/

namespace IxCC.Recheck.CertJson

open Lean (Json toJson)

abbrev Dec := Except String

def str (s : String) : Json := Json.str s
def nat (n : Nat) : Json := toJson n
def arr (xs : List Json) : Json := Json.arr xs.toArray

def getNat (j : Json) : Dec Nat := j.getNat?
def getStr (j : Json) : Dec String := j.getStr?
def getBool (j : Json) : Dec Bool := j.getBool?
def getArr (j : Json) : Dec (List Json) := (·.toList) <$> j.getArr?
def listOf {α : Type} (f : Json → Dec α) (j : Json) : Dec (List α) := do (← getArr j).mapM f
def nats (j : Json) : Dec (List Nat) := listOf getNat j
def field (j : Json) (k : String) : Dec Json := j.getObjVal? k

/-- Maximum constant/global index allowed as a `NatMap` or table key in a certificate. -/
def maxNatMapKey : Nat := 1000000

/-- Maximum middle-end steps allowed in a certificate. -/
def maxMidSteps : Nat := 64

def natKey? (j : Json) : Dec Nat := do
  let k ← getNat j
  if k ≤ maxNatMapKey then pure k
  else throw s!"certificate key {k} exceeds maximum {maxNatMapKey}"

/-- Reject hostile number tokens before `Lean.Json.parse` (see `Src.Hints.checkJsonText`). -/
def checkJsonText (text : String) : Except String Unit :=
  Src.Hints.checkJsonText text

/-- A pair `[a, b]`. -/
def pair {α β : Type} (f : Json → Dec α) (g : Json → Dec β) (j : Json) : Dec (α × β) := do
  match ← getArr j with
  | [a, b] => pure (← f a, ← g b)
  | _ => throw s!"expected a pair, got {j.compress}"

/-! ## Src -/

def propWhen : Src.PropWhen → Json
  | .never => str "n"
  | .allZero ps => arr (ps.map nat)

def propWhen? (j : Json) : Dec Src.PropWhen :=
  match j with
  | .str "n" => pure .never
  | _ => .allZero <$> nats j

def rel : Src.Rel → Json
  | .rel => str "r"
  | .type => str "t"
  | .proof w => arr [str "p", propWhen w]

def rel? (j : Json) : Dec Src.Rel :=
  match j with
  | .str "r" => pure .rel
  | .str "t" => pure .type
  | _ => do
    match ← getArr j with
    | [.str "p", w] =>
      let pw ← propWhen? w
      if pw == .never then throw "non-canonical proof .never"
      else pure (.proof pw)
    | _ => throw s!"bad Rel {j.compress}"

def fieldClass : Src.Relevance.FieldClass → Json
  | .keep => str "k"
  | .type => str "t"
  | .proof w => arr [str "p", propWhen w]

def fieldClass? (j : Json) : Dec Src.Relevance.FieldClass :=
  match j with
  | .str "k" => pure .keep
  | .str "t" => pure .type
  | _ => do
    match ← getArr j with
    | [.str "p", w] =>
      let pw ← propWhen? w
      if pw == .never then throw "non-canonical proof .never"
      else pure (.proof pw)
    | _ => throw s!"bad FieldClass {j.compress}"

def termKey : Src.TermKey → Json
  | .value c => arr [str "v", nat c]
  | .eqn c => arr [str "q", nat c]
  | .rule r j => arr [str "u", nat r, nat j]

def termKey? (j : Json) : Dec Src.TermKey := do
  match ← getArr j with
  | [.str "v", c] => .value <$> natKey? c
  | [.str "q", c] => .eqn <$> natKey? c
  | [.str "u", r, i] => return .rule (← natKey? r) (← natKey? i)
  | _ => throw s!"bad TermKey {j.compress}"

def tag : Src.Relevance.Tag → Json
  | .lam r w => arr [str "l", rel r, propWhen w]
  | .arg r => arr [str "a", rel r]
  | .letE r => arr [str "e", rel r]

def tag? (j : Json) : Dec Src.Relevance.Tag := do
  match ← getArr j with
  | [.str "l", r, w] => return .lam (← rel? r) (← propWhen? w)
  | [.str "a", r] => .arg <$> rel? r
  | [.str "e", r] => .letE <$> rel? r
  | _ => throw s!"bad Tag {j.compress}"

def ann (a : Src.Relevance.Ann) : Json :=
  Json.mkObj [
    ("consts", arr (a.consts.toList.map fun (c, r) => arr [nat c, rel r.result, arr (r.params.map rel)])),
    ("ctors", arr (a.ctors.toList.map fun (c, r) => arr [nat c, arr (r.fields.map fieldClass)])),
    ("nodes", arr (a.nodes.map fun (k, ts) => arr [termKey k, arr (ts.map tag)]))]

def ann? (j : Json) : Dec Src.Relevance.Ann := do
  let consts ← listOf (fun e => do
    match ← getArr e with
    | [c, r, ps] => return (← natKey? c, ({ result := ← rel? r, params := ← listOf rel? ps } : Src.Relevance.ConstRel))
    | _ => throw s!"bad ConstRel {e.compress}") (← field j "consts")
  let ctors ← listOf (pair natKey? fun fs => do
    return ({ fields := ← listOf fieldClass? fs } : Src.Relevance.CtorRel)) (← field j "ctors")
  let nodes ← listOf (pair termKey? (listOf tag?)) (← field j "nodes")
  return { consts := Src.NatMap.ofList consts, ctors := Src.NatMap.ofList ctors, nodes }

def primOp? (s : String) : Dec Src.PrimOp :=
  match Src.PrimOp.all.find? (·.name == s) with
  | some op => pure op
  | none => throw s!"bad primitive {s}"

/-- A word operation by its Lean name (`UInt64.add`, `UInt8.toUInt32`). -/
def wordOp? (s : String) : Dec (Src.Width × Src.WordOp) :=
  let all := Src.Width.all.flatMap fun w => (Src.WordOp.ofWidth w).map (w, ·)
  match all.find? (fun (w, op) => op.leanName w == s) with
  | some wop => pure wop
  | none => throw s!"bad word operation {s}"

def entry : Src.Table.Entry → Json
  | .prim op => arr [str "prim", str op.name]
  | .word w op thm => arr [str "word", str (op.leanName w), nat thm]
  | .csimp g thm => arr [str "csimp", nat g, nat thm]
  | .eqn thm => arr [str "eqn", nat thm]
  | .case => arr [str "case"]

def entry? (j : Json) : Dec Src.Table.Entry := do
  match ← getArr j with
  | [.str "prim", .str op] => .prim <$> primOp? op
  | [.str "word", .str name, thm] => do
    let (w, op) ← wordOp? name
    return .word w op (← natKey? thm)
  | [.str "csimp", g, thm] => return .csimp (← natKey? g) (← natKey? thm)
  | [.str "eqn", thm] => .eqn <$> natKey? thm
  | [.str "case"] => pure .case
  | _ => throw s!"bad table entry {j.compress}"

def table (t : Src.Table.TableCert) : Json :=
  Json.mkObj [
    ("resolve", arr (t.resolve.map fun (c, e) => arr [nat c, entry e])),
    ("recKind", arr (t.recKind.map nat)),
    ("lazy", arr (t.lazy.map fun (c, a) => arr [nat c, nat a])),
    ("inline", arr (t.inline.map nat)),
    ("opaqueByValue", arr (t.opaqueByValue.map nat))]

def table? (j : Json) : Dec Src.Table.TableCert := do
  return { resolve := ← listOf (pair natKey? entry?) (← field j "resolve")
           recKind := ← listOf natKey? (← field j "recKind")
           lazy := ← listOf (pair natKey? natKey?) (← field j "lazy")
           inline := ← listOf natKey? (← field j "inline")
           opaqueByValue := ← listOf natKey? (← field j "opaqueByValue") }

/-! ## The middle end -/

def step : Anf.Pipeline.Step → Json
  | .shrink rounds => arr [str "P2", arr (rounds.map nat)]
  | .inline r => arr [str "P3", arr (r.map fun (g, cs) => arr [nat g, arr (cs.map nat)])]
  | .specialize c => arr [str "P4", nat c.inv,
      arr (c.decisions.map fun d => arr [nat d.caller, nat d.callee, arr (d.mask.map Json.bool)])]
  | .prune => arr [str "prune"]

def step? (j : Json) : Dec Anf.Pipeline.Step := do
  match ← getArr j with
  | [.str "P2", rounds] =>
    let c ← nats rounds
    unless Anf.Shrink.checkCert c do
      throw "P2 shrink certificate exceeds round or global bounds"
    return .shrink c
  | [.str "P3", r] =>
    let rd ← listOf (pair natKey? (listOf natKey?)) r
    unless Anf.Inline.checkCert rd do
      throw "P3 inline certificate exceeds bounds or contains self-inlining"
    return .inline rd
  | [.str "P4", inv, ds] =>
    let decisions ← listOf (fun d => do
      match ← getArr d with
      | [a, b, m] => return ({ caller := ← natKey? a, callee := ← natKey? b, mask := ← listOf getBool m } :
          Anf.Specialize.Decision)
      | _ => throw s!"bad P4 decision {d.compress}") ds
    return .specialize { inv := ← getNat inv, decisions }
  | [.str "prune"] => pure .prune
  | _ => throw s!"bad Anf step {j.compress}"

def mid (c : Anf.Pipeline.Cert) : Json :=
  Json.mkObj [("shrink", arr [nat c.shrink.caseOfCase, nat c.shrink.smallJoin]),
    ("steps", arr (c.steps.map step))]

def mid? (j : Json) : Dec Anf.Pipeline.Cert := do
  let (caseOfCase, smallJoin) ← pair getNat getNat (← field j "shrink")
  let shrink : Anf.Shrink.Params := { caseOfCase, smallJoin }
  unless shrink.checkCert do
    throw "shrink parameters exceed maximum bounds"
  let steps ← listOf step? (← field j "steps")
  unless steps.length ≤ maxMidSteps do
    throw s!"middle-end step count {steps.length} exceeds maximum {maxMidSteps}"
  return { shrink, steps }

/-! ## The backend -/

def gprs : List (X86.GPR × String) :=
  [(.rax, "rax"), (.rcx, "rcx"), (.rdx, "rdx"), (.rbx, "rbx"), (.rsp, "rsp"), (.rbp, "rbp"),
   (.rsi, "rsi"), (.rdi, "rdi"), (.r8, "r8"), (.r9, "r9"), (.r10, "r10"), (.r11, "r11"),
   (.r12, "r12"), (.r13, "r13"), (.r14, "r14"), (.r15, "r15")]

def gpr (r : X86.GPR) : Json := str ((gprs.lookup r).getD "?")

def gpr? (j : Json) : Dec X86.GPR := do
  let s ← getStr j
  match gprs.find? (·.2 == s) with
  | some (r, _) => pure r
  | none => throw s!"bad register {s}"

def loc : Xv.Loc → Json
  | .reg r => gpr r
  | .slot i => arr [str "s", nat i]
  | .inArg i => arr [str "i", nat i]
  | .outArg i => arr [str "o", nat i]

def loc? (j : Json) : Dec Xv.Loc :=
  match j with
  | .str _ => .reg <$> gpr? j
  | _ => do
    match ← getArr j with
    | [.str "s", i] => .slot <$> getNat i
    | [.str "i", i] => .inArg <$> getNat i
    | [.str "o", i] => .outArg <$> getNat i
    | _ => throw s!"bad location {j.compress}"

def blockOut (b : Xv.Alloc.BlockOut) : Json :=
  arr [arr (b.locs.map fun ls => arr (ls.map loc)), arr (b.termLocs.map loc),
    arr (b.edits.map fun (i, .move d s) => arr [nat i, loc d, loc s]),
    arr (b.cert.map fun (l, vs) => arr [loc l, arr (vs.map nat)])]

def blockOut? (j : Json) : Dec Xv.Alloc.BlockOut := do
  match ← getArr j with
  | [locs, termLocs, edits, cert] =>
    return { locs := ← listOf (listOf loc?) locs, termLocs := ← listOf loc? termLocs
             edits := ← listOf (fun e => do
               match ← getArr e with
               | [i, d, s] => return (← getNat i, .move (← loc? d) (← loc? s))
               | _ => throw s!"bad edit {e.compress}") edits
             cert := ← listOf (pair loc? nats) cert }
  | _ => throw "bad allocation block"

def maxAllocSlots : Nat := 4096

def output (o : Xv.Alloc.Output) : Json := arr [nat o.numSlots, arr (o.blocks.map blockOut)]

def output? (j : Json) : Dec Xv.Alloc.Output := do
  let (numSlots, blocks) ← pair getNat (listOf blockOut?) j
  if numSlots > maxAllocSlots then
    throw s!"alloc numSlots {numSlots} exceeds limit {maxAllocSlots}"
  return { numSlots, blocks }

def frame (l : Xv.Stacking.FrameLayout) : Json :=
  arr [nat l.size, arr (l.slotOff.map nat), arr (l.saveOff.map fun (r, o) => arr [gpr r, nat o]), nat l.outArgs]

def frame? (j : Json) : Dec Xv.Stacking.FrameLayout := do
  match ← getArr j with
  | [size, slotOff, saveOff, outArgs] =>
    return { size := ← getNat size, slotOff := ← nats slotOff
             saveOff := ← listOf (pair gpr? getNat) saveOff, outArgs := ← getNat outArgs }
  | _ => throw s!"bad frame layout {j.compress}"

/-! ## The certificate -/

def format : String := "ixcc/cert/1"

def cert (c : Cert) : Json :=
  Json.mkObj [
    ("format", str format),
    ("table", table c.table),
    ("relevance", ann c.relevance),
    ("mid", mid c.mid),
    ("alloc", arr (c.alloc.map output)),
    ("frames", arr (c.frames.map frame)),
    ("order", arr (c.order.map fun g => arr (g.map nat)))]

def cert? (j : Json) : Dec Cert := do
  let f ← getStr (← field j "format")
  unless f == format do throw s!"unsupported certificate format {f}"
  return { table := ← table? (← field j "table")
           relevance := ← ann? (← field j "relevance")
           mid := ← mid? (← field j "mid")
           alloc := ← listOf output? (← field j "alloc")
           frames := ← listOf frame? (← field j "frames")
           order := ← listOf nats (← field j "order") }

end CertJson

/-- The certificate's text (compact JSON). -/
def Cert.toText (c : Cert) : String := (CertJson.cert c).compress

/-- Parse a certificate; a malformed one is a `cert.parse` error. -/
def Cert.ofText (text : String) : Except Err Cert :=
  match (CertJson.checkJsonText text >>= fun () => Lean.Json.parse text >>= CertJson.cert?) with
  | .ok c => .ok c
  | .error m => .error { stage := .cert, code := "cert.parse", message := m }

/-- The certificate's file: its text and a newline, the bytes `ixcc compile --emit-cert` writes. -/
def Cert.toFile (c : Cert) : String := c.toText ++ "\n"

/-- A certificate as the verifier reads it: a file text and what `Cert.ofText`, the reader of
`ixcc check-cert` and `compile --cert`, reads it as. -/
structure Cert.Read where
  text : String
  cert : Cert
  read : Cert.ofText text = .ok cert

/-- **The producer's read-back.** The certificate `c` a producer built, read back from its file
text (`toFile`) through `Cert.ofText`, with every text and decode limit the verifier applies; a
certificate past one is refused here with the limit's reason (`cert: cert.parse: …`). The
verifier then runs on the decoded certificate, and the text is what is written. -/
def Cert.readBack (c : Cert) : Except Err Cert.Read :=
  let text := c.toFile
  match h : Cert.ofText text with
  | .ok d => .ok ⟨text, d, h⟩
  | .error e => .error e

#guard (CertJson.rel? (CertJson.arr [CertJson.str "p", CertJson.str "n"])).isOk == false
#guard (CertJson.fieldClass? (CertJson.arr [CertJson.str "p", CertJson.str "n"])).isOk == false
#guard (CertJson.output? (CertJson.arr [CertJson.nat 4097, CertJson.arr []])).isOk == false
#guard (CertJson.output? (CertJson.arr [CertJson.nat 4096, CertJson.arr []])).isOk == true

end IxCC.Recheck
