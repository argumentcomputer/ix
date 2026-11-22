import IxCC.Lir.Syntax

/-!
# Lir text

A readable rendering of Lir programs for diagnostics and test failures.
It is not parsed back.

```text
fn f0 fib(v0) -> 1
  b2:
    v1 = sub.64 v0, 2
    v2 = call f0(v1)
    brovf addc v5 = v3, v4 -> b3(), b4()
  b4 cold:
    fail natOverflow
```
-/

namespace IxCC.Lir

private def commaSep (xs : List String) : String := ", ".intercalate xs

def Width.text : Width → String
  | .w8 => "8"
  | .w16 => "16"
  | .w32 => "32"
  | .w64 => "64"

def VReg.text (x : VReg) : String := s!"v{x}"

def Arg.text : Arg → String
  | .v x => VReg.text x
  | .imm w => if w.toNat < 0x10000 then toString w.toNat else s!"0x{String.ofList (Nat.toDigits 16 w.toNat)}"

def Addr.text (m : Addr) : String :=
  let base := match m.base with
    | some (.v x) => [VReg.text x]
    | some .ctx => ["ctx"]
    | none => []
  let index := match m.index with
    | some (x, s) => [s!"{VReg.text x}*{s.word.toNat}"]
    | none => []
  let parts := " + ".intercalate (base ++ index)
  let disp :=
    if m.disp == 0 then (if parts.isEmpty then "0" else "")
    else if parts.isEmpty then toString m.disp
    else if m.disp < 0 then s!" - {-m.disp}" else s!" + {m.disp}"
  s!"[{parts}{disp}]"

def Cond.text : Cond → String
  | .eq => "eq" | .ne => "ne"
  | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"
  | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"
  | .tz => "tz" | .tnz => "tnz"

def BinOp.text : BinOp → String
  | .add => "add" | .sub => "sub" | .and => "and" | .or => "or" | .xor => "xor"
  | .mul => "mul" | .shl => "shl" | .shr => "shr" | .sar => "sar"
  | .udiv => "udiv" | .urem => "urem"

def Rhs.text : Rhs → String
  | .arg a => a.text
  | .bin o w a b => s!"{o.text}.{w.text} {a.text}, {b.text}"
  | .load w e m => s!"load.{w.text}{match e with | .zero => "" | .sign => "s"} {m.text}"
  | .addr m => s!"addr {m.text}"
  | .select c w a b t f => s!"select {c.text}.{w.text} {a.text}, {b.text} ? {t.text} : {f.text}"
  | .test c w a b => s!"test {c.text}.{w.text} {a.text}, {b.text}"

def Stmt.text : Stmt → String
  | .assign x r => s!"{VReg.text x} = {r.text}"
  | .store w m a => s!"store.{w.text} {m.text}, {a.text}"
  | .call rs f as =>
      let lhs := if rs.isEmpty then "" else s!"{commaSep (rs.map VReg.text)} = "
      s!"{lhs}call f{f}({commaSep (as.map Arg.text)})"

def Edge.text (e : Edge) : String := s!"b{e.target}({commaSep (e.args.map Arg.text)})"

def Resource.text : Sem.Resource → String
  | .heap => "heap"
  | .stack => "stack"
  | .natOverflow => "natOverflow"

def Term.text : Term → String
  | .jump e => s!"jump {e.text}"
  | .br c w a b t f => s!"br {c.text}.{w.text} {a.text}, {b.text} -> {t.text}, {f.text}"
  | .brOvf o x a b ok ovf =>
      let op := match o with | .addC => "addc" | .subB => "subb"
      s!"brovf {op} {VReg.text x} = {a.text}, {b.text} -> {ok.text}, {ovf.text}"
  | .ret as => s!"ret {commaSep (as.map Arg.text)}"
  | .tail f as => s!"tail f{f}({commaSep (as.map Arg.text)})"
  | .fail r => s!"fail {Resource.text r}"
  | .trap => "trap"

def Block.text (label : Label) (b : Block) : String :=
  let params := if b.params.isEmpty then "" else s!"({commaSep (b.params.map VReg.text)})"
  let header := s!"  b{label}{params}{if b.cold then " cold" else ""}:\n"
  header ++ String.join (b.body.toList.map fun s => s!"    {s.text}\n") ++ s!"    {b.term.text}\n"

def Func.text (id : FunId) (f : Func) : String :=
  let conv := match f.conv with
    | .internal => ""
    | .sysvExport symbol => s!" export {symbol}"
  let header := s!"fn f{id} {f.name}({commaSep (f.params.map VReg.text)}) -> {f.results}{conv}\n"
  header ++ String.join ((List.range f.blocks.size).map fun b => Block.text b f.blocks[b]!)

def Program.text (p : Program) : String :=
  s!"main f{p.main}\n" ++ String.join ((List.range p.funcs.size).map fun i => Func.text i p.funcs[i]!)

end IxCC.Lir
