import Compilatrix.Own.Plain.Certificate
import Compilatrix.Cfg.Rc.Public
import Compilatrix.Cfg.Rc.Scoped
import Compilatrix.Recheck.Run

set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay
open Lean (Json)

structure Cert where
  base : Recheck.Cert
  own : Json

def Cert.toText (c : Cert) : String :=
  (Json.arr #[.str "compilatrix/rc-cert/2", CertJson.cert c.base, c.own]).compress

def Cert.ofText (text : String) : Except String Cert := do
  let json ← Json.parse text
  match (← json.getArr?).toList with
  | [.str "compilatrix/rc-cert/2", base, own] => return { base := ← CertJson.cert? base, own }
  | _ => throw "rc.cert: unsupported certificate envelope"

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

def runFront (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Front := do
  let (src, checked) ← Recheck.front cfg P c.base
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let anf ← (Anf.Pipeline.run c.base.mid lam).mapError fun message =>
    { stage := .anf, code := "anf.replay", message }
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
  (Xv.Validate.program cfg.env xv c.alloc).mapError Err.ofValidate
  let xl ← (Xv.Alloc.applyProgram xv c.alloc).mapError fun message =>
    { stage := .alloc, code := "alloc.apply", message }
  let backendCfg := { Recheck.backendConfig cfg f.lowered root c with reps := f.reps }
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

end Compilatrix.Recheck.RcReplay
