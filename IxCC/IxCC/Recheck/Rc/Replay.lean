import IxCC.Own.Plain.Certificate
import IxCC.Cfg.Rc.Public
import IxCC.Cfg.Rc.Scoped
import IxCC.Recheck.Run

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open Lean (Json)

structure Cert where
  base : Recheck.Cert
  own : Json

def Cert.toText (c : Cert) : String :=
  (Json.arr #[.str "ixcc/rc-cert/2", CertJson.cert c.base, c.own]).compress

def Cert.ofText (text : String) : Except String Cert := do
  CertJson.checkJsonText text
  let json ← Json.parse text
  match (← json.getArr?).toList with
  | [.str "ixcc/rc-cert/2", base, own] => return { base := ← CertJson.cert? base, own }
  | _ => throw "rc.cert: unsupported certificate envelope"

/-- `Cert.ofText` with its refusal as the verifier reports it (`cert: cert.parse: …`): the reader
of `ixcc check-cert` and `compile --cert` for a plain-RC certificate. -/
def Cert.parse (text : String) : Except Err Cert :=
  (Cert.ofText text).mapError fun message => { stage := .cert, code := "cert.parse", message }

/-- The certificate's file: its text and a newline, the bytes `ixcc compile --emit-cert` writes. -/
def Cert.toFile (c : Cert) : String := c.toText ++ "\n"

/-- A plain-RC certificate as the verifier reads it: a file text and what `Cert.parse` reads it
as. -/
structure Cert.Read where
  text : String
  cert : Cert
  read : Cert.parse text = .ok cert

/-- **The producer's read-back** (`Recheck.Cert.readBack` for the plain-RC envelope): the
certificate's file text read back through `Cert.parse`, with every text and decode limit. -/
def Cert.readBack (c : Cert) : Except Err Cert.Read :=
  let text := c.toFile
  match h : Cert.parse text with
  | .ok d => .ok ⟨text, d, h⟩
  | .error e => .error e

structure Front where
  src : Src.Program
  checked : Src.Relevance.Checked
  lam : Lam.Program
  anf : Anf.Program
  fir : Fir.Program
  own : Own.Plain.Program
  cfg : Cfg.Rc.Program
  lowered : Rt.Lowered
  drop : Lir.FunId

def Front.reps (f : Front) : Lir.FunId → Option (List Xv.Stacking.ArgRep) :=
  (⟨f.lowered, f.drop⟩ : Cfg.Rc.Public.Lowered).reps

def Front.layout (f : Front) : Cfg.Rc.Native.Layout :=
  ⟨f.cfg.base.size, f.cfg.base.ctors.filter (fun c => c.arity > 0)⟩

def Front.env (f : Front) (base : Xv.Xl.Env) : Xv.Xl.Env :=
  f.layout.env base

/-- The inputs the end-to-end theorems about a front half made under
certificate `c` cover (`Recheck.Covered`, of `c.base`). -/
def Front.Covered (f : Front) (c : Cert) : Nat × List Nat → Prop :=
  Recheck.Covered c.base.mid f.src f.lam f.anf

def runFront (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Front := do
  let (src, checked) ← Recheck.front cfg P c.base
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let anf ← Recheck.anfOf c.base src lam
  let fir ← (Fir.lower anf).mapError Err.ofFir
  let own ← (Own.Plain.Certificate.admit fir c.own).mapError fun message =>
    { stage := .cert, code := "own.plain", message }
  let some candidate := Cfg.Rc.generate fir own.bodies |
    throw { stage := .rt, code := "rc.cfg", message := "ownership candidate lowering declined" }
  unless Cfg.Rc.checkScopedProgram fir own.bodies candidate do
    throw { stage := .rt, code := "rc.scope", message := "scoped dense-source RC gate refused" }
  Recheck.checkParams cfg candidate.base (candidate.base.exports.zipIdx.map fun (f, i) => (i, f))
  let lowered ← (Cfg.Rc.Public.lower { names := cfg.names } fir own.bodies candidate).mapError fun message =>
    { stage := .rt, code := "rc.lower", message }
  return {
    src, checked, lam, anf, fir, own, cfg := candidate
    lowered := lowered.runtime, drop := lowered.drop }

/-- Existing backend validators with the single additional raw-word export
representation. A returned pointer must never be tagged as a Nat argument. -/
def backTyped (cfg : Config) (f : Front) (root : Ixon.Address) (c : Recheck.Cert) :
    Except Err (Xv.VProgram × Xv.LProgram × Xv.Stacking.Stacked × X86.Program ×
      List (String × X86.BlockId)) := do
  let xv ← (Xv.Select.select f.lowered.program).mapError Err.ofSelect
  (Xv.Validate.program (f.env cfg.env) xv c.alloc).mapError Err.ofValidate
  let xl ← (Xv.Alloc.applyProgram xv c.alloc).mapError fun message =>
    { stage := .alloc, code := "alloc.apply", message }
  let backendCfg := { Recheck.backendConfig cfg f.lowered root c with reps := f.reps, env := f.env cfg.env }
  let (stacked, program, exports) ← (Backend.lay xl backendCfg).mapError Err.ofBackend
  return (xv, xl, stacked, program, exports)

structure Artifact where
  front : Front
  backend : Backend.Artifact
  roots : List Root

/-- Use the existing allocation, frame, ordering, typed-x86, encoding and ELF
validators directly, with every decision from the serialized certificate. -/
def run (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Artifact := do
  let f ← runFront cfg P c
  let root := (f.src.roots.head?.map (·.1)).getD default
  let provenance := cfg.provenance.getD (.ixir1Policy root 3 1)
  let cfg := { cfg with provenance := some provenance }
  let (_, xl, stacked, program, exports) ← backTyped cfg f root c.base
  Recheck.checkSymbols stacked.exports
  let backend ← (Backend.finish xl.main stacked program exports provenance).mapError Err.ofBackend
  let rows := (List.range f.src.roots.length).zip
    (f.src.roots.zip (f.cfg.base.exports.zip f.lowered.roots))
  return { front := f, backend, roots := Recheck.rootsOf cfg f.src f.cfg.base f.lowered rows }

end IxCC.Recheck.RcReplay
