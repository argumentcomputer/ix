import Compilatrix.Fir.Syntax

/-! # Fir printer

A readable rendering for diagnostics, dumps and test failures: variables
`v3`, join points `j0`, functions `f2`, constructors by source constant and
tag (`C12#1`). Not on the recheck path. -/

namespace Compilatrix.Fir

private def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

def renderKey : Key.CtorKey → String
  | .src c => s!"C{c}"
  | .clo g n => s!"clo({g.render},{n})"

def Arg.render : Arg → String
  | .var x => s!"v{x}"
  | .lit (.nat n) => toString n
  | .lit (.str s) => reprStr s
  | .erased => "□"

def renderArgs (as : List Arg) : String := " ".intercalate (as.map Arg.render)

def Rhs.render : Rhs → String
  | .arg a => a.render
  | .ctor c as => s!"{renderKey c.key}#{c.tag} [{renderArgs as}]"
  | .proj x c i => s!"v{x}.{renderKey c}.{i}"
  | .prim p as => s!"{p.name} {renderArgs as}"
  | .call f as => s!"call f{f} {renderArgs as}"

mutual

def Code.render (ind : Nat) : Code → String
  | .bind x r k => s!"{indent ind}v{x} := {r.render}\n{k.render ind}"
  | .jp j ps r b k =>
    let vs := " ".intercalate (ps.map (s!"v{·}"))
    s!"{indent ind}jp{if r then " rec" else ""} j{j} {vs} =\n{b.render (ind + 1)}{k.render ind}"
  | .jmp j as => s!"{indent ind}jmp j{j} {renderArgs as}\n"
  | .case x alts d =>
    s!"{indent ind}case v{x}\n{Code.renderAlts ind alts}{Code.renderOpt ind d}"
  | .ret a => s!"{indent ind}ret {a.render}\n"
  | .tcall f as => s!"{indent ind}tcall f{f} {renderArgs as}\n"
  | .trap => s!"{indent ind}trap\n"

def Code.renderAlts (ind : Nat) : List Alt → String
  | [] => ""
  | .mk k b :: as => s!"{indent ind}| {renderKey k} =>\n{b.render (ind + 1)}{Code.renderAlts ind as}"

def Code.renderOpt (ind : Nat) : Option Code → String
  | none => ""
  | some c => s!"{indent ind}| _ =>\n{c.render (ind + 1)}"

end

def Fun.render (f : FunId) (fd : Fun) : String :=
  let ps := " ".intercalate (fd.params.map fun (x, _) => s!"v{x}")
  s!"f{f} [{fd.key.render}] {ps} =\n{fd.body.render 1}"

def Program.render (P : Program) : String :=
  s!"exports {P.exports}\n" ++ String.join (P.funList.map fun (f, fd) => fd.render f)

end Compilatrix.Fir
