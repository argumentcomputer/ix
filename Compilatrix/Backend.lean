import Compilatrix.Xv.Select.Driver
import Compilatrix.Xv.Alloc.Driver
import Compilatrix.Xv.Stacking.Run
import Compilatrix.X86.Layout.Tunnel
import Compilatrix.X86.Layout.Linearize
import Compilatrix.X86.StreamValidate
import Compilatrix.X86.ELFValidate
import Compilatrix.X86.CheckK
import Compilatrix.X86.StreamK
import Compilatrix.X86.ELFWriteK

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

The object exports a symbol per export's wrapper (05 §6.1): `main`'s is
the ELF entry symbol, and the others follow it in the symbol table
(`ELF.Input.exports`, certified by `ELF.Valid.exported`).
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
  /-- Two exports share this symbol (`sharedSymbol?`). -/
  | symbols (symbol : String)
  deriving Repr, Inhabited

def Error.toString : Error → String
  | .select why => s!"selection: {why}"
  | .alloc why => s!"allocation: {why}"
  | .stacking e => e.toString
  | .layout why => why
  | .check e => s!"x86 validation: {repr e}"
  | .stream e => s!"stream: {repr e}"
  | .elf e => s!"ELF: {repr e}"
  | .symbols s => s!"stacking: two exports share the symbol {s}"

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

/-- The laid-out typed program to a checked ELF object: `Program.check`, E1
encoding with E2's stream check, and the ELF writer with its validator.
`main` is the function whose wrapper is the entry symbol.

Each step is its kernel-evaluable twin (M1.K1): `Program.checkK`,
`Stream.encodeK` (the list encoder `Encode.encodeK` and the one-pass
`Stream.checkK`) and `ELF.writeCheckedK` (the list writer and the windowed
validator). They are proved equal to `Program.check`, `Stream.encode` and
`ELF.writeChecked` (`Program.checkK_eq`, `Stream.encodeK_eq`,
`ELF.writeCheckedK_eq`), so the object and its certificates are the
originals'. -/
def finish (main : Lir.FunId) (stacked : Stacking.Stacked) (program : X86.Program)
    (exports : List (String × X86.BlockId)) (provenance : X86.ELF.Provenance) :
    Except Error Artifact := do
  let checked ← program.checkK.mapError .check
  let stream ← (X86.Stream.encodeK checked).mapError .stream
  let some entry := stacked.exports.find? (·.fn == main) | throw (.stacking .noEntry)
  let object ← (X86.ELF.writeCheckedK
    { encoded := stream.output, entryBlock := program.entry, exportName := entry.symbol,
      exports := exports.filter (·.1 != entry.symbol), provenance }).mapError .elf
  pure { stacked, program, checked, encoded := stream.output, object := object.bytes,
         exportName := entry.symbol, exports }

/-- A symbol two exports share, if any (the first export's, in order). -/
def sharedSymbol? : List Stacking.Export → Option String
  | [] => none
  | e :: rest => if rest.any (·.symbol == e.symbol) then some e.symbol else sharedSymbol? rest

/-- Every export has its own symbol. `finish` lists the further exports
without the entry symbol, so an export sharing the entry's symbol would be
dropped and its symbol would run `main`'s wrapper; `Rt.symbolOf` replaces
characters, so distinct root names can share a symbol. The recheck path
runs the same check (`Recheck.checkSymbols`, `stacking.symbols`). -/
def checkSymbols (exports : List Stacking.Export) : Except Error Unit :=
  match sharedSymbol? exports with
  | none => pure ()
  | some s => .error (.symbols s)

/-- Xl to a checked ELF object exporting every export's wrapper, `main`'s
as the entry symbol; declined if two exports share a symbol. -/
def emit (p : LProgram) (cfg : Config) : Except Error Artifact := do
  let (stacked, program, exports) ← lay p cfg
  checkSymbols stacked.exports
  finish p.main stacked program exports cfg.provenance

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
