import Compilatrix.Anf.Syntax

/-! # Anf printer

A readable rendering for diagnostics, reports and test failures: value
variables are named by their de Bruijn *level* (`x0` is a global's first
parameter), join points likewise (`j0`), globals by id (`g3`), constructor
keys by their source constant (`C12`) and, when the table lists it, their tag
and arity. Not on the recheck path. -/

namespace Compilatrix.Anf

private def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

def Atom.render (d : Nat) : Atom → String
  | .var i => if i < d then s!"x{d - 1 - i}" else s!"#{i}?"
  | .lit (.nat n) => toString n
  | .lit (.str s) => s!"{repr s}"
  | .box => "□"

def renderCtor (P : Program) : Key.CtorKey → String
  | .src c =>
    match P.ctor? (.src c) with
    | some i => s!"C{c}#{i.tag}"
    | none => s!"C{c}?"
  | .clo g n => s!"clo({g.render},{n})"

private def atoms (d : Nat) (as : List Atom) : String := " ".intercalate (as.map (·.render d))

mutual

def Exp.render (P : Program) (d dj ind : Nat) : Exp → String
  | .bind _ b e => s!"{indent ind}x{d} := {Bind.render P d ind b}\n{Exp.render P (d + 1) dj ind e}"
  | .join n r b e =>
    let ps := " ".intercalate ((List.range n).map fun i => s!"x{d + i}")
    let jd := if r then dj + 1 else dj
    s!"{indent ind}join{if r then " rec" else ""} j{dj} {ps} =\n{Exp.render P (d + n) jd (ind + 1) b}\n" ++
      Exp.render P d (dj + 1) ind e
  | .jump j as => s!"{indent ind}jump {if j < dj then s!"j{dj - 1 - j}" else s!"#{j}?"} {atoms d as}"
  | .case x alts dflt =>
    s!"{indent ind}case {x.render d}\n{Exp.renderAlts P d dj ind alts}{Exp.renderOpt P d dj ind dflt}"
  | .ret a => s!"{indent ind}ret {a.render d}"
  | .tick e => s!"{indent ind}tick\n{Exp.render P d dj ind e}"
  | .trap => s!"{indent ind}trap"

def Bind.render (P : Program) (d ind : Nat) : Bind → String
  | .atom a => a.render d
  | .con c as => s!"{renderCtor P c} [{atoms d as}]"
  | .proj c i x => s!"{x.render d}.{renderCtor P c}.{i}"
  | .prim p as => s!"{p.name} {atoms d as}"
  | .glob g => s!"g{g}"
  | .call g as => s!"call g{g} {atoms d as}"
  | .app f as => s!"app {f.render d} {atoms d as}"
  | .fn ps b =>
    let xs := " ".intercalate ((List.range ps.length).map fun i => s!"x{d + i}")
    s!"fn {xs} =>\n{Exp.render P (d + ps.length) 0 (ind + 1) b}"

def Exp.renderAlts (P : Program) (d dj ind : Nat) : List Alt → String
  | [] => ""
  | .mk k n b :: as =>
    let fs := " ".intercalate ((List.range n).map fun i => s!"x{d + i}")
    s!"{indent ind}| {renderCtor P k} {fs} =>\n{Exp.render P (d + n) dj (ind + 1) b}\n" ++
      Exp.renderAlts P d dj ind as

def Exp.renderOpt (P : Program) (d dj ind : Nat) : Option Exp → String
  | none => ""
  | some e => s!"{indent ind}| _ =>\n{Exp.render P d dj (ind + 1) e}\n"

end

def GDef.render (P : Program) (g : GlobalId) (gd : GDef) : String :=
  let ps := " ".intercalate ((List.range gd.ps.length).map fun i => s!"x{i}")
  s!"g{g} [{gd.key.render}] {ps} =\n{gd.body.render P gd.ps.length 0 1}\n"

def Program.render (P : Program) : String :=
  s!"roots {P.roots}\n" ++ "\n".intercalate (P.globalList.map fun (g, gd) => gd.render P g)

end Compilatrix.Anf
