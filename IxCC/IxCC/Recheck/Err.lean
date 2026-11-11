import IxCC.Src.Syntax
import IxCC.Src.Relevance.Check
import IxCC.Lam.Erase.Term
import IxCC.Fir.Lower
import IxCC.Rt.Lower
import IxCC.Rt.Switches
import IxCC.Backend

/-! # Declines and rejections of the compiler

Every way the compiler stops names the stage that stopped it and a
code, rendered as `stage: code: message`. The codes are the stages' own:
Src's `Diag` codes (`decode`, `typing`, `relevance-C2`, `admit` codes, …),
erasure's `EraseError.code` (`erase-const-kind`, `erase-string`,
`erase-mode`, `erase-minor`, `erase-lazy`, `erase-proj`, `erase-ctor-layout`,
`erase-C2`, `erase-C4`, `erase-S2`, `erase-scope`, `erase-recursor`,
`erase-root`, `erase-record`, `erase-fuel`, `erase-budget`, and the forms
its proof excludes: `erase-univs`, `erase-unbox-elim`, `erase-pin`,
`erase-key`), the closures step's `anf.entry` and P8's `defun.captures`,
`defun.tags`, `defun.input` and `defun.budget`, `fir.closures` (unreachable
after the closures step), `Rt.lower`'s `rt.*`, the allocation
validator's check names and so on; the compiler adds `rt.params` (a root
with more parameters than the entry wrapper passes), `rt.dispatch` and
`rt.pins` (the switch check `Rt.checkSwitches`: a default arm, mixed or
indistinguishable keys, `Nat.zero` and `Nat.succ` on one key), `stacking.symbols`
(two exports sharing a symbol, `Recheck.checkSymbols`), `cli.*` (arguments and
files) and `cert.*` (a certificate that does not parse). A decline is a
program outside the Phase 1 fragment; a rejection is a certificate the
recheck path does not accept. Neither ever produces code. -/

namespace IxCC.Recheck

/-- Where the compiler stopped. -/
inductive Stage where
  /-- Decoding, erased typing, ingress, the sidecar (not on the recheck path),
  and the recheck path's own size and depth check of the program
  (`Recheck.checkSrc`). -/
  | ingress
  /-- The unfolding table: its certificate re-checked (`Table.ofCert`). -/
  | table
  /-- The relevance oracle, installation and check (tiers S and C). -/
  | relevance
  /-- The producer's admission of the relevant closure (`Src.Admit`). -/
  | admit
  | erase
  /-- The middle end's replay (`Anf.Pipeline.run`) and the closures step
  (`Anf.Pipeline.closures`: `anf.entry`, P8's `defun.*`). -/
  | anf
  | fir
  /-- Runtime lowering and the entry ABI. -/
  | rt
  | select
  /-- The allocation certificate's validation and application. -/
  | alloc
  | stacking
  | layout
  /-- The typed program's checks, encoding and the stream check (E1/E2). -/
  | x86
  | elf
  /-- The standalone executable: the roots it runs and its writer. -/
  | exe
  /-- The certificate's serialisation. -/
  | cert
  /-- The command line and its files. -/
  | cli
  deriving DecidableEq, Repr, Inhabited

def Stage.name : Stage → String
  | .ingress => "ingress" | .table => "table" | .relevance => "relevance" | .admit => "admit"
  | .erase => "erase" | .anf => "anf" | .fir => "fir" | .rt => "rt" | .select => "select"
  | .alloc => "alloc" | .stacking => "stacking" | .layout => "layout" | .x86 => "x86"
  | .elf => "elf" | .exe => "exe" | .cert => "cert" | .cli => "cli"

/-- A decline or rejection: its stage, code and message. -/
structure Err where
  stage : Stage
  code : String
  message : String
  deriving Inhabited, DecidableEq

def Err.render (e : Err) : String := s!"{e.stage.name}: {e.code}: {e.message}"

instance : ToString Err := ⟨Err.render⟩

/-- Split a rendered `code: message` at its first `": "`. -/
def splitCode (s : String) : String × String :=
  match s.splitOn ": " with
  | code :: rest@(_ :: _) => (code, ": ".intercalate rest)
  | _ => (s, "")

/-- A Src diagnostic (its code; the rest of its rendering as the message). -/
def Err.ofDiag (stage : Stage) (d : Src.Diag) : Err :=
  { stage, code := d.code, message := (splitCode d.render).2 }

/-- An erasure decline: its code, and its rendering after the bracketed code
(where it happened, then why). -/
def Err.ofErase (e : Lam.Erase.EraseError) : Err :=
  let rest := (e.render.drop (e.code.length + 2)).toString
  let rest := if rest.startsWith ": " then (rest.drop 2).toString else rest.trimAsciiStart.toString
  { stage := .erase, code := e.code, message := rest }

def Err.ofFir (e : Fir.Lower.Error) : Err :=
  let (code, message) := splitCode e.render
  { stage := .fir, code, message }

/-- A decline of the closures step (`Anf.Pipeline.closures`): P8's `defun.*` codes
and `anf.entry` as they are, anything else (the size check) as
`anf.closures`. -/
def Err.ofClosures (msg : String) : Err :=
  let (code, message) := splitCode msg
  if code.startsWith "defun." || code == "anf.entry" then { stage := .anf, code, message }
  else { stage := .anf, code := "anf.closures", message := msg }

def Err.ofRt (e : Rt.Error) : Err :=
  let (code, message) := splitCode e.render
  { stage := .rt, code, message }

def Err.ofSwitch (e : Rt.SwitchError) : Err :=
  let (code, message) := splitCode e.render
  { stage := .rt, code, message }

def Err.ofSelect (e : Xv.Select.Error) : Err :=
  { stage := .select, code := s!"select.{e.form}"
    message := s!"function {e.fn} block {e.block} {(e.stmt.map (s!"statement {·}")).getD "terminator"}: {e.reason}" }

def Err.ofValidate (e : Xv.Validate.Err) : Err :=
  { stage := .alloc, code := s!"alloc.{e.code.name}", message := e.text }

def stackingCode : Xv.Stacking.Error → String
  | .layouts .. => "stacking.layouts"
  | .layout _ => "stacking.layout"
  | .func .. => "stacking.func"
  | .export .. => "stacking.export"
  | .noEntry => "stacking.noEntry"
  | .tooLarge _ => "stacking.tooLarge"
  | .clobbers .. => "stacking.clobbers"
  | .malformed => "stacking.malformed"
  | .arity _ => "stacking.arity"

def Err.ofBackend : Backend.Error → Err
  | .select why => { stage := .select, code := "select", message := why }
  | .alloc why => { stage := .alloc, code := "alloc", message := why }
  | .stacking e => { stage := .stacking, code := stackingCode e, message := e.toString }
  | .layout why => { stage := .layout, code := "layout.order", message := why }
  | .check e => { stage := .x86, code := "x86.check", message := s!"{repr e}" }
  | .stream e => { stage := .x86, code := "x86.stream", message := s!"{repr e}" }
  | .elf e => { stage := .elf, code := "elf.check", message := s!"{repr e}" }
  | .symbols s => { stage := .stacking, code := "stacking.symbols", message := s!"two exports share the symbol {s}" }

end IxCC.Recheck
