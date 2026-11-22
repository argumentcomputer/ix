import IxCC.Xv.Syntax
import IxCC.Lir.Print

/-!
# Xv and Xl text

A readable rendering for diagnostics and test failures; not parsed back.
Each row prints as its LLVM mnemonic, width and encoding class:

```text
fn f0 fib(v0) -> 1
  b0:
    jcc cmp.64.MI8 v0, 3 ; be -> b1(), b2()
  b2:
    v7 = lea.64.RM [v0 - 4]
    v2 = call f0(v7)
```
-/

namespace IxCC.Xv

open IxCC.Lir (VReg)

private def commaSep (xs : List String) : String := ", ".intercalate xs

class OperandText (ρ : Type) where
  text : ρ → String

instance : OperandText VReg := ⟨Lir.VReg.text⟩

def gprText (r : X86.GPR) : String :=
  match r with
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

instance : OperandText Loc where
  text
    | .reg r => gprText r
    | .slot i => s!"s{i}"
    | .inArg i => s!"in{i}"
    | .outArg i => s!"out{i}"

variable {ρ : Type} [OperandText ρ]

def wordText (w : Lir.Word) : String := Lir.Arg.text (.imm w)

def Amode.text (a : Amode ρ) : String :=
  let base := match a.base with
    | some (.r x) => [OperandText.text x]
    | some .ctx => ["ctx"]
    | none => []
  let index := match a.index with
    | some (x, s) => [s!"{OperandText.text x}*{s.word.toNat}"]
    | none => []
  let parts := " + ".intercalate (base ++ index)
  let d := a.disp.toInt
  let disp :=
    if d == 0 then (if parts.isEmpty then "0" else "")
    else if parts.isEmpty then toString d
    else if d < 0 then s!" - {-d}" else s!" + {d}"
  s!"[{parts}{disp}]"

def XArg.text : XArg ρ → String
  | .r x => OperandText.text x
  | .m a => a.text
  | .i w => wordText w

def formText : X86.OpEn → String
  | .MR => "MR" | .RM => "RM" | .MI => "MI" | .MI8 => "MI8" | .OI => "OI" | .O => "O"
  | .RMI => "RMI" | .RMI8 => "RMI8" | .D32 => "D32" | .ZO => "ZO" | .M => "M" | .MC => "MC"

def opText (o : X86.Op) : String :=
  let src := if o.src == o.w then "" else s!".{o.src.bits}"
  s!"{(X86.desc o).mnemonic}.{o.w.bits}{src}.{formText o.form}"

def defsText (xs : List ρ) : String :=
  if xs.isEmpty then "" else s!"{commaSep (xs.map OperandText.text)} = "

def Inst.text : Inst ρ → String
  | .op o defs args => s!"{defsText defs}{opText o} {commaSep (args.map XArg.text)}"
  | .fused p pargs c defs cargs =>
      s!"{defsText defs}fused {opText p} {commaSep (pargs.map XArg.text)}; {opText c} {commaSep (cargs.map XArg.text)}"
  | .move d s => s!"{OperandText.text d} = move {OperandText.text s}"
  | .zero x => s!"{OperandText.text x} = zero"
  | .call f args rets => s!"{defsText rets}call f{f}({commaSep (args.map OperandText.text)})"

def Edge.text (e : Edge ρ) : String := s!"b{e.target}({commaSep (e.args.map OperandText.text)})"

def condText (c : X86.Condition) : String := X86.Condition.suffix c

def Term.text : Term ρ → String
  | .jmp e => s!"jmp {e.text}"
  | .jcc p pargs defs c t f =>
      s!"{defsText defs}jcc {opText p} {commaSep (pargs.map XArg.text)} ; j{condText c} -> {t.text}, {f.text}"
  | .ret vs => s!"ret {commaSep (vs.map OperandText.text)}"
  | .tail f args => s!"tail f{f}({commaSep (args.map OperandText.text)})"
  | .fail r => s!"fail {repr r}"
  | .trap => "trap"

def Func.text (fi : Nat) (f : Func ρ) : String := Id.run do
  let conv := match f.conv with
    | .internal => ""
    | .sysvExport s => s!" export {s}"
  let mut out := s!"fn f{fi} {f.name}({commaSep (f.params.map OperandText.text)}) -> {f.results}{conv}\n"
  for h : b in [:f.blocks.size] do
    let blk := f.blocks[b]
    let params := if blk.params.isEmpty then "" else s!"({commaSep (blk.params.map OperandText.text)})"
    out := out ++ s!"  b{b}{params}{if blk.cold then " cold" else ""}:\n"
    for i in blk.body do out := out ++ s!"    {i.text}\n"
    out := out ++ s!"    {blk.term.text}\n"
  return out

def Program.text (p : Program ρ) : String :=
  String.join (p.funcs.toList.zipIdx.map fun (f, i) => Func.text i f)

end IxCC.Xv
