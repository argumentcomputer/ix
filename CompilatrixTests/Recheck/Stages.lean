import Compilatrix.Recheck.Run
import CompilatrixTests.Rt.Kernel

/-! # The recheck path by stages, for kernel measurements

`upTo s cfg P c` runs `Recheck.run`'s path up to and including stage `s`
and returns a summary of that stage's output (sizes that traverse it, so
the kernel evaluates all of it), or `none` if the path stops earlier. The
stages follow `Recheck.runTyped` and `Backend.finish` step by step; the
kernel measurements (`plans/x86-phase1/k1/`) time `decide +kernel` of each
prefix on the recheck artifacts, so a stage's cost is the difference
between consecutive prefixes. The generator records the native summaries
beside each artifact (`stages`). -/

namespace CompilatrixTests.Recheck.Stages

open Compilatrix Compilatrix.Recheck

/-- The stages of the recheck path, in order. -/
inductive Stage where
  /-- The table certificate, the annotation's installation and check, `Lazify`. -/
  | front
  | erase
  /-- The middle end (P1–P4 on the certificate). -/
  | anf
  /-- `Fir.lower`, `Own.immortal`, `Cfg.lower` and the roots' parameter check. -/
  | cfg
  | rt
  | select
  /-- The allocation validator and `Alloc.applyProgram`. -/
  | alloc
  /-- Stacking (with the frame-layout check), tunnelling, the order check and
  linearisation: `runTyped`'s program. -/
  | lay
  /-- `X86.Program.check`. -/
  | check
  /-- E1 encoding and E2's stream check. -/
  | encode
  /-- The ELF writer. -/
  | write
  /-- The ELF writer and its validator: `run`'s object. -/
  | object
  deriving DecidableEq, Repr, Inhabited

def Stage.all : List Stage :=
  [.front, .erase, .anf, .cfg, .rt, .select, .alloc, .lay, .check, .encode, .write, .object]

def Stage.name : Stage → String
  | .front => "front" | .erase => "erase" | .anf => "anf" | .cfg => "cfg" | .rt => "rt"
  | .select => "select" | .alloc => "alloc" | .lay => "lay" | .check => "check"
  | .encode => "encode" | .write => "write" | .object => "object"

def lamSize (L : Lam.Program) : List Nat :=
  [L.size, L.globalList.foldl (fun n (_, g) => n + g.body.nodes) 0]

def anfSize (A : Anf.Program) : List Nat :=
  [A.size, A.globalList.foldl (fun n (_, gd) => n + gd.body.nodes) 0]

def cfgSize (C : Cfg.Program) : List Nat := [C.size, C.blocks, C.instrs]

def xSize {ρ : Type} (p : Xv.Program ρ) : List Nat :=
  let fs := p.funcs.toList
  [fs.length, fs.foldl (fun n f => n + f.blocks.toList.length) 0,
   fs.foldl (fun n f => n + f.blocks.toList.foldl (fun m b => m + b.body.toList.length) 0) 0]

def x86Size (p : X86.Program) : List Nat :=
  [p.blocks.toList.length, p.blocks.toList.foldl (fun n b => n + b.instructions.toList.length) 0,
   p.entry.toNat]

/-- The summary at stage `s`: `.error` carries the summary where `s` stops
the prefix (an early exit), `.ok` means `s` is past the end. -/
def upToE (s : Stage) (cfg : Config) (P : Src.Program) (c : Cert) : Except (Option (List Nat)) Unit := do
  let (src, checked) ← (front cfg P c).mapError fun _ => none
  if s == .front then throw (some [src.size, checked.reached.length, checked.instances.length])
  let (lam, _) ← (Compilatrix.Lam.erase src checked).mapError fun _ => none
  if s == .erase then throw (some (lamSize lam))
  let anf ← (Compilatrix.Anf.Pipeline.run c.mid lam).mapError fun _ => none
  if s == .anf then throw (some (anfSize anf))
  let fir ← (Compilatrix.Fir.lower anf).mapError fun _ => none
  let C := Compilatrix.Cfg.lower (Compilatrix.Own.immortal fir)
  (checkParams cfg C (List.zipIdx C.exports |>.map fun (f, i) => (i, f))).mapError fun _ => none
  if s == .cfg then throw (some (cfgSize C))
  let lowered ← (Compilatrix.Rt.lower { names := cfg.names } C).mapError fun _ => none
  if s == .rt then throw (some ((fun (a, b, c, d, e) => [a, b, c, d, e]) (CompilatrixTests.Rt.Kernel.summaryOf lowered.program)))
  let (xv, _) ← (Compilatrix.Xv.Select.run lowered.program).mapError fun _ => none
  if s == .select then throw (some (xSize xv))
  (Compilatrix.Xv.Validate.program cfg.env xv c.alloc).mapError fun _ => none
  let xl ← (Compilatrix.Xv.Alloc.applyProgram xv c.alloc).mapError fun _ => none
  if s == .alloc then throw (some (xSize xl))
  let root := (src.roots.head?.map (·.1)).getD default
  let (stacked, program, exports) ← (Compilatrix.Backend.lay xl (backendConfig cfg lowered root c)).mapError fun _ => none
  if s == .lay then throw (some (x86Size program))
  let checked ← program.checkK.mapError fun _ => none
  if s == .check then throw (some (x86Size checked.program))
  let stream ← (Compilatrix.X86.Stream.encodeK checked).mapError fun _ => none
  if s == .encode then
    throw (some [stream.output.text.size, stream.output.blockOffsets.size, stream.output.relocations.size])
  let some entry := stacked.exports.find? (·.fn == xl.main) | throw none
  let input : Compilatrix.X86.ELF.Input :=
    { encoded := stream.output, entryBlock := program.entry, exportName := entry.symbol,
      exports := exports.filter (·.1 != entry.symbol), provenance := cfg.provenance.getD (defaultProvenance root) }
  let bytes ← (Compilatrix.X86.ELF.writeK input).mapError fun _ => none
  if s == .write then throw (some [bytes.length])
  let object ← (Compilatrix.X86.ELF.writeCheckedK input).mapError fun _ => none
  throw (some [object.bytes.size])

/-- The summary of the path up to and including `s`, or `none` if it stops
earlier. -/
def upTo (s : Stage) (cfg : Config) (P : Src.Program) (c : Cert) : Option (List Nat) :=
  match upToE s cfg P c with
  | .error r => r
  | .ok () => none

end CompilatrixTests.Recheck.Stages
