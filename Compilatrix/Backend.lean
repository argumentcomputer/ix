import Compilatrix.Xv.Select.Driver
import Compilatrix.Xv.Alloc.Driver
import Compilatrix.Xv.Stacking.Run
import Compilatrix.X86.Layout.Tunnel
import Compilatrix.X86.Layout.Linearize
import Compilatrix.X86.StreamValidate
import Compilatrix.X86.ELFValidate

/-!
# The backend (05 §1, §10)

`Backend.compile` takes a Lir program to a checked ELF object:

```text
Lir ─Select.run→ Xv ─Alloc.run (linear scan, validated; all-slots fallback)→ Xl
    ─stacking (FrameLayout per function, checked)→ X86 ─tunnel→ ─order (checked)→ ─linearize→
    ─Program.check→ E1 bytes ─Stream.encode (E2 check)→ ─ELF.writeChecked→ object
```

`Backend.emit` is the part below allocation, and `compileWith` takes any
allocator. The certificate fields here are the frame layouts and the
block order (05 §1.1); when a configuration leaves them out, their
untrusted oracles supply them, and the checks run either way. (The
allocation's certificate is `Alloc.run`'s own.)

The ELF writer exports one symbol, so an object exports `main`'s wrapper;
other exports keep their wrappers in the text, unnamed (a divergence from
05 §6.1's wrapper per root in the object, until the writer grows a symbol
table of exports).
-/

namespace Compilatrix.Backend

open Compilatrix.Xv

structure Config where
  /-- One frame layout per function; `none` runs `Stacking.produce`. -/
  layouts : Option (List Stacking.FrameLayout) := none
  /-- The block order, per layout group; `none` runs `Order.produce`. -/
  order : Option X86.Layout.Order := none
  /-- How each export passes its arguments (default: every one a `Nat`). -/
  reps : Lir.FunId → Option (List Stacking.ArgRep) := fun _ => none
  provenance : X86.ELF.Provenance
  /-- The calling convention's clobber sets, which allocation assumes and
  stacking checks. -/
  env : Xl.Env := {}

inductive Error where
  | select (why : String)
  | alloc (why : String)
  | stacking (e : Stacking.Error)
  | layout (why : String)
  | check (e : X86.ValidationError)
  | stream (e : X86.Stream.Error)
  | elf (e : X86.ELF.CheckedError)
  deriving Repr, Inhabited

def Error.toString : Error → String
  | .select why => s!"selection: {why}"
  | .alloc why => s!"allocation: {why}"
  | .stacking e => e.toString
  | .layout why => why
  | .check e => s!"x86 validation: {repr e}"
  | .stream e => s!"stream: {repr e}"
  | .elf e => s!"ELF: {repr e}"

instance : ToString Error := ⟨Error.toString⟩

/-- Everything the backend produced, kept for tests and reports. -/
structure Artifact where
  stacked : Stacking.Stacked
  /-- The laid-out program. -/
  program : X86.Program
  checked : X86.Checked
  encoded : X86.Encode.Output
  object : ByteArray
  exportName : String
  /-- Each export's wrapper block after layout. -/
  exports : List (String × X86.BlockId)

/-- Stacking and layout: the typed program an object is made of. -/
def lay (p : LProgram) (cfg : Config) : Except Error (Stacking.Stacked × X86.Program × List (String × X86.BlockId)) := do
  let layouts := cfg.layouts.getD (Stacking.produce p)
  let stacked ← (Stacking.run p layouts cfg.reps cfg.env).mapError .stacking
  let tunnelled := X86.Layout.tunnel stacked.program
  let order := cfg.order.getD (X86.Layout.Order.produce tunnelled stacked.shape)
  let (program, pos) ← (X86.Layout.run tunnelled stacked.shape order).mapError .layout
  let exports := stacked.exports.map fun e => (e.symbol, UInt32.ofNat ((pos.get? e.block).getD e.block))
  pure (stacked, program, exports)

/-- Xl to a checked ELF object exporting `main`'s wrapper. -/
def emit (p : LProgram) (cfg : Config) : Except Error Artifact := do
  let (stacked, program, exports) ← lay p cfg
  let checked ← program.check.mapError .check
  let stream ← (X86.Stream.encode checked).mapError .stream
  let some main := stacked.exports.find? (·.fn == p.main) | throw (.stacking .noEntry)
  let object ← (X86.ELF.writeChecked
    { encoded := stream.output, entryBlock := program.entry, exportName := main.symbol,
      provenance := cfg.provenance }).mapError .elf
  pure { stacked, program, checked, encoded := stream.output, object := object.bytes,
         exportName := main.symbol, exports }

/-- Lir to an ELF object: selection, the given allocator, then `emit`. -/
def compileWith (alloc : VProgram → Except String LProgram) (p : Lir.Program) (cfg : Config) :
    Except Error Artifact := do
  let (xv, _) ← (Select.run p).mapError fun e => .select s!"{e.form}: {e.reason}"
  let xl ← (alloc xv).mapError .alloc
  emit xl cfg

/-- Lir to an ELF object with M1.B4's allocation: linear scan, validated,
falling back to all slots per function (`Alloc.run`). -/
def compile (p : Lir.Program) (cfg : Config) : Except Error Artifact :=
  compileWith (fun xv => (·.program) <$> Alloc.run cfg.env xv) p cfg

end Compilatrix.Backend
