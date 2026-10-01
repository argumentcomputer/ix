import Compilatrix.Recheck.Cert
import Compilatrix.Recheck.Err
import Compilatrix.Src.Recheck
import Compilatrix.Lam.Erase
import Compilatrix.Cfg.Lower
import Compilatrix.Rt.Backend
import Compilatrix.Rt.Readback

/-! # `Recheck.run`: the compiler's checked path

`run cfg P c` (design note 00 "Produce and recheck", D17; 06 S44) takes a
`Src.Program` as ingress left it (constants, roots and pinned identities,
no table) and a certificate, and re-runs every pass on the certificate's
decisions, validating what the producer searched for:

```text
P ─Table.ofCert (V)→ ─install + Relevance.check (V)→ ─Lazify (P)→ ─Lam.erase (P)→ Lam
  ─Anf.Pipeline.run c.mid (P: P1, then P2/P3/P4/prune on the certificate's decisions)→ Anf
  ─Fir.lower (P)→ ─Own.immortal (P)→ ─Cfg.lower (P)→ Cfg ─roots (≤ 5 parameters)→
  ─switches (check)→ ─Rt.lower (P, with edge splitting)→ Lir ─Select.select (P)→ Xv
  ─Validate.program c.alloc (V)→ ─Alloc.applyProgram→ Xl
  ─Backend.emit: FrameLayout.check c.frames (V), stacking emission, tunnelling (P),
    Order.check c.order (V), linearisation (P), Program.check, E1, E2, ELF→ object
```

No search runs here: the annotator, `Table.build`, `Admit`, the middle end's
oracles, linear scan and the layout oracles are `produce`'s. A certificate
that a validator refuses is a rejection naming its stage and code; one it
accepts gives code as correct as any other it would accept (the passes'
theorems quantify over the certificate). `Recheck.sound` (M2.8) is stated of
this function.

**Kernel style.** `runLir` is the front half, up to the lowered Lir program
(what M2.7's front theorem, `Recheck.front_refines`, is stated of);
`runTyped` is `run` up to the laid-out typed x86 program (`runLir`, then
everything before `Backend.finish`); `run` adds `Backend.finish`: the typed
program's check, E1 encoding, E2's stream check and the ELF writer with its
validator, each by its kernel-evaluable twin proved equal to the original
(`Program.checkK`, `Stream.encodeK`, `ELF.writeCheckedK`). The whole path is
written in kernel-evaluable style (persistent `NatMap`s, lists, structural
recursion or fuel), and `decide +kernel` evaluates both functions on the K1
artifacts (`CompilatrixTests.Recheck.Kernel`, M1.K1): `run`'s object bytes
equal the native run's. -/

namespace Compilatrix.Recheck

open Compilatrix.Src (CId)

/-- A root as the object exports it. -/
structure Root where
  /-- The name the configuration gave it (`root<i>` if none). -/
  name : String
  /-- The source constant and its address. -/
  const : CId
  addr : Ixon.Address
  /-- Its Lir function and exported symbol (`cx_<name>`). -/
  fn : Lir.FunId
  symbol : String
  /-- Parameters the entry wrapper passes (all tagged `Nat`s). -/
  params : Nat
  /-- The result's readback type, when Phase 1 reads it (`Nat`, `Bool`). -/
  ty : Option (Rt.Sig × Rt.FoTy)
  deriving Inhabited

/-- The driver's arguments for reading a root's results back
(`--type T --sig S`, `fixtures/x86/runtime_driver.c`). -/
def Root.driverType (r : Root) : Option (String × String) :=
  r.ty.map fun (sig, ty) => (ty.encode, sig.encode)

/-- What `run` made: every level, for tests, dumps and reports. -/
structure Artifact where
  /-- The program with its table and installed annotation. -/
  src : Src.Program
  checked : Src.Relevance.Checked
  lam : Lam.Program
  anf : Anf.Program
  fir : Fir.Program
  own : Own.Program
  cfg : Cfg.Program
  lowered : Rt.Lowered
  xv : Xv.VProgram
  xl : Xv.LProgram
  backend : Backend.Artifact
  roots : List Root

/-- The ELF object. -/
def Artifact.object (a : Artifact) : ByteArray := a.backend.object

/-- The ELF object's bytes as a list: what a kernel evaluation of `run`
states (`(run cfg P c).map Artifact.bytes = .ok bytes`, M1.K1, M2.8). -/
def Artifact.bytes (a : Artifact) : List UInt8 := a.object.data.toList

/-! ## Roots -/

/-- A root constant's result type from its Src type: `Nat` or `Bool`
(Phase 1 reads first-order results of those types; others have no
readback type yet). -/
def resultTy (p : Src.Program) (c : CId) : Option Rt.FoTy :=
  match p.decl? c with
  | some d =>
    match (Src.Term.pis d.type).2 with
    | .const r [] =>
      if some r == p.known.nat then some .nat
      else if some r == p.known.bool then some (.ind 0) else none
    | _ => none
  | none => none

/-- The readback signature of `Bool` results: inductive 0 with the
program's constructor tags for `false` and `true`. -/
def boolSig (C : Cfg.Program) : Rt.Sig :=
  let tagOf := fun (k : Option Key.CtorKey) => (k.bind (Fir.CtorInfo.ofKey C.ctors)).map (·.tag)
  let n := match tagOf C.known.boolFalse, tagOf C.known.boolTrue with
    | some f, some t => max f t + 1
    | _, _ => 2
  { inds := [List.replicate n []] }

/-- A root's parameter count at Cfg (its entry block's parameters). -/
def cfgParams (C : Cfg.Program) (f : Fir.FunId) : Nat :=
  ((C.fun? f).map (·.params.length)).getD 0

/-- A root constant's readback signature and type: `Nat`, or `Bool` with the
program's tags (`none`: Phase 1 reads it back as nothing). -/
def rootTy (p : Src.Program) (C : Cfg.Program) (c : CId) : Option (Rt.Sig × Rt.FoTy) :=
  match resultTy p c with
  | some .nat => some ({}, Rt.FoTy.nat)
  | some t => some (boolSig C, t)
  | none => none

/-- The roots: Src's roots, Cfg's exports and Rt's symbols correspond by
position (erasure keeps the Src root order, Anf and Fir keep Lam's). -/
def rootsOf (cfg : Config) (p : Src.Program) (C : Cfg.Program) (l : Rt.Lowered) :
    List (Nat × (Ixon.Address × CId) × Fir.FunId × (Lir.FunId × String)) → List Root
  | [] => []
  | (i, (addr, c), f, (fn, symbol)) :: rest =>
    { name := (cfg.names[i]?).getD s!"root{i}", const := c, addr, fn, symbol, params := cfgParams C f
      ty := rootTy p C c } ::
      rootsOf cfg p C l rest

/-- A root with more parameters than the wrapper passes (04 §6): declined
before lowering, with its own code. -/
def checkParams (cfg : Config) (C : Cfg.Program) : List (Nat × Fir.FunId) → Except Err Unit
  | [] => pure ()
  | (i, f) :: rest =>
    let n := cfgParams C f
    if n > maxParams then
      .error { stage := .rt, code := "rt.params"
               message := s!"root {(cfg.names[i]?).getD s!"root{i}"} takes {n} parameters; \
                 the entry wrapper passes at most {maxParams}" }
    else checkParams cfg C rest

/-- A symbol two exports share, if any (the first export's, in order). -/
def sharedSymbol? : List Xv.Stacking.Export → Option String
  | [] => none
  | e :: rest => if rest.any (·.symbol == e.symbol) then some e.symbol else sharedSymbol? rest

/-- Every export has its own symbol (M2.8). `Backend.finish` lists the
further exports without the entry symbol, so an export sharing the entry's
symbol would be dropped and its symbol would run `main`'s wrapper;
`Rt.symbolOf` replaces characters, so distinct root names can share a
symbol. Declined with `stacking.symbols`. -/
def checkSymbols (exports : List Xv.Stacking.Export) : Except Err Unit :=
  match sharedSymbol? exports with
  | none => pure ()
  | some s => .error { stage := .stacking, code := "stacking.symbols", message := s!"two exports share the symbol {s}" }

/-! ## The passes -/

/-- The front end on the certificate: the table, the annotation, `Lazify`. -/
def front (cfg : Config) (P : Src.Program) (c : Cert) :
    Except Err (Src.Program × Src.Relevance.Checked) := do
  let table ← (Src.Table.ofCert cfg.table P c.table).mapError fun msg =>
    { stage := .table, code := "table.entry", message := msg }
  match Src.Recheck.annotation { P with table } c.relevance with
  | .ok r => pure r
  | .error (.install msg) => throw { stage := .relevance, code := "relevance-S1", message := msg }
  | .error (.relevance errs) =>
    let p := { P with table }
    let first := errs[0]?.map (·.rule) |>.getD "S1"
    throw { stage := .relevance, code := s!"relevance-{first}"
            message := "; ".intercalate (errs.toList.take 8 |>.map (·.render p)) }
  | .error (.table msg) => throw { stage := .table, code := "table.entry", message := msg }

/-- Lam through Cfg on the certificate's middle-end decisions. -/
def middle (c : Cert) (lam : Lam.Program) : Except Err (Anf.Program × Fir.Program × Own.Program × Cfg.Program) := do
  let anf ← (Anf.Pipeline.run c.mid lam).mapError fun msg =>
    { stage := .anf, code := "anf.replay", message := msg }
  let fir ← (Fir.lower anf).mapError Err.ofFir
  let own := Own.immortal fir
  pure (anf, fir, own, Cfg.lower own)

/-- The backend configuration: `Rt.Lowered.config` with the certificate's
layouts and order. -/
def backendConfig (cfg : Config) (l : Rt.Lowered) (root : Ixon.Address) (c : Cert) : Backend.Config :=
  { l.config (cfg.provenance.getD (defaultProvenance root)) with
    layouts := some c.frames, order := some c.order, env := cfg.env }

/-- Lir to the laid-out typed program: selection, the allocation
certificate, stacking and layout with the certificate's layouts and order. -/
def backTyped (cfg : Config) (l : Rt.Lowered) (root : Ixon.Address) (c : Cert) :
    Except Err (Xv.VProgram × Xv.LProgram × Xv.Stacking.Stacked × X86.Program ×
      List (String × X86.BlockId)) := do
  let xv ← (Xv.Select.select l.program).mapError Err.ofSelect
  (Xv.Validate.program cfg.env xv c.alloc).mapError Err.ofValidate
  let xl ← (Xv.Alloc.applyProgram xv c.alloc).mapError fun msg =>
    { stage := .alloc, code := "alloc.apply", message := msg }
  let (stacked, program, exports) ← (Backend.lay xl (backendConfig cfg l root c)).mapError
    Err.ofBackend
  pure (xv, xl, stacked, program, exports)

/-- What the recheck path makes up to the laid-out typed x86 program, before
`X86.Program.check`: every level, the stacked and laid-out programs, each
export's block, the provenance the object will carry, and the roots. -/
structure Typed where
  src : Src.Program
  checked : Src.Relevance.Checked
  lam : Lam.Program
  anf : Anf.Program
  fir : Fir.Program
  own : Own.Program
  cfg : Cfg.Program
  lowered : Rt.Lowered
  xv : Xv.VProgram
  xl : Xv.LProgram
  stacked : Xv.Stacking.Stacked
  /-- The laid-out typed program. -/
  program : X86.Program
  exports : List (String × X86.BlockId)
  provenance : X86.ELF.Provenance
  roots : List Root

/-- What the recheck path makes up to the lowered Lir program (its front
half, `runLir`): every level from the checked source to Lir. -/
structure Front where
  src : Src.Program
  checked : Src.Relevance.Checked
  lam : Lam.Program
  anf : Anf.Program
  fir : Fir.Program
  own : Own.Program
  cfg : Cfg.Program
  lowered : Rt.Lowered

/-- The recheck path up to the lowered Lir program (the front half, M2.7):
the front end, erasure, the middle end, Fir, Own and Cfg, the roots'
parameter check, the switch check (`Rt.checkSwitches`, which discharges
`Rt.lower_correct`'s `SwitchOk` without types) and `Rt.lower`. -/
def runLir (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Front := do
  let (src, checked) ← front cfg P c
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let (anf, fir, own, C) ← middle c lam
  checkParams cfg C (List.zipIdx C.exports |>.map fun (f, i) => (i, f))
  (Rt.checkSwitches C).mapError Err.ofSwitch
  let lowered ← (Rt.lower { names := cfg.names } C).mapError Err.ofRt
  pure { src, checked, lam, anf, fir, own, cfg := C, lowered }

/-- The recheck path up to the laid-out typed program: `run` without its
final checks and encodings (`Program.check`, E1/E2 and the ELF writer). -/
def runTyped (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Typed := do
  let f ← runLir cfg P c
  let root := (f.src.roots.head?.map (·.1)).getD default
  let (xv, xl, stacked, program, exports) ← backTyped cfg f.lowered root c
  let rows := (List.range f.src.roots.length).zip (f.src.roots.zip (f.cfg.exports.zip f.lowered.roots))
  let roots := rootsOf cfg f.src f.cfg f.lowered rows
  pure { src := f.src, checked := f.checked, lam := f.lam, anf := f.anf, fir := f.fir, own := f.own
         cfg := f.cfg, lowered := f.lowered, xv, xl, stacked, program, exports
         provenance := cfg.provenance.getD (defaultProvenance root), roots }

/-- The recheck path (D17): the object `P` compiles to under certificate `c`,
or the stage and code that declined or rejected it: `runTyped`, then
`checkSymbols` (every export its own symbol) and `Backend.finish` (`Program.check`, E1/E2 and
the ELF writer). -/
def run (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Artifact := do
  let t ← runTyped cfg P c
  checkSymbols t.stacked.exports
  let backend ← (Backend.finish t.xl.main t.stacked t.program t.exports t.provenance).mapError
    Err.ofBackend
  pure { src := t.src, checked := t.checked, lam := t.lam, anf := t.anf, fir := t.fir
         own := t.own, cfg := t.cfg, lowered := t.lowered, xv := t.xv, xl := t.xl, backend
         roots := t.roots }

end Compilatrix.Recheck
