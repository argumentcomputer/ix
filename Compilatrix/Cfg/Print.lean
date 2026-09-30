import Compilatrix.Cfg.Syntax
import Compilatrix.Fir.Print

/-! # Cfg printer

Blocks with their parameters, instructions and terminator, for dumps and
test failures (`^` marks a back edge). Not on the recheck path. -/

namespace Compilatrix.Cfg

open Compilatrix.Fir (renderArgs renderKey)

def renderRhs : Own.Rhs → String
  | .fir r => r.render
  | .alloc c as _ => s!"alloc {renderKey c.key}#{c.tag} [{renderArgs as}]"
  | .proj x c i => s!"v{x}.{renderKey c}.{i}"

def Edge.render (e : Edge) : String :=
  s!"b{e.target}{if e.back then "^" else ""}({renderArgs e.args})"

def Term.render : Term → String
  | .jump e => s!"jump {e.render}"
  | .switch x alts d =>
    let as := alts.map fun (k, e) => s!"{renderKey k} => {e.render}"
    let dd := match d with
      | some e => s!"; _ => {e.render}"
      | none => ""
    s!"switch v{x} [{"; ".intercalate as}{dd}]"
  | .ret a => s!"ret {a.render}"
  | .tcall f as => s!"tcall f{f} {renderArgs as}"
  | .trap => "trap"

def Block.render (i : BlockId) (b : Block) : String :=
  let ps := " ".intercalate (b.params.map fun (x, _) => s!"v{x}")
  let body := String.join (b.body.map fun | .bind x r => s!"    v{x} := {renderRhs r}\n")
  s!"  b{i}({ps}):\n{body}    {b.term.render}\n"

def Fun.render (f : Fir.FunId) (fd : Fun) : String :=
  s!"f{f} [{fd.key.render}]\n" ++ String.join (fd.blocks.zipIdx.map fun (b, i) => Block.render i b)

def Program.render (P : Program) : String :=
  s!"exports {P.exports}\n" ++ String.join (P.funList.map fun (f, fd) => Fun.render f fd)

end Compilatrix.Cfg
