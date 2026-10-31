module
public import Ix.Compile.SourceGraph
public import Ix.Ixon

@[expose] public section
namespace Ix.Compile.SourceGraph.Accounting

inductive Issue where
  | neither (name : Name)
  | both (name : Name)
  | outside (name : Name)
  deriving Repr, DecidableEq

def Issue.message : Issue → String
  | .neither n => s!"source accounting: '{n.pretty}' is neither published nor recorded as failed"
  | .both n => s!"source accounting: '{n.pretty}' is both published and recorded as failed"
  | .outside n => s!"source accounting: failure name '{n.pretty}' is outside the original input"

structure Report where
  uncovered : Array Name := #[]
  outside : Array Name := #[]

/-- Collect only failing keys; no complete pair/body array is materialized. -/
def selectKeys (m : Map Name α) (bad : Name → Bool) : Array Name :=
  m.fold (init := #[]) fun acc n _ => if bad n then acc.push n else acc
def scan (nodes : Map Name Node) (named : Map Name Ixon.Named) (failed : Map Name String) : Report :=
  ⟨selectKeys nodes (fun n => named.contains n == failed.contains n),
    selectKeys failed (fun n => !nodes.contains n)⟩
def verdict (failed : Map Name String) (report : Report) : Except Issue Unit :=
  match report.uncovered.toList, report.outside.toList with
  | n :: _, _ => .error (if failed.contains n then .both n else .neither n)
  | [], n :: _ => .error (.outside n)
  | [], [] => .ok ()

/-- Final accounting: generated publications and failed-only partial
results are allowed. This neither checks types nor validates admission. -/
def check (nodes : Map Name Node) (named : Map Name Ixon.Named) (failed : Map Name String) : Except Issue Unit :=
  verdict failed (scan nodes named failed)

end Ix.Compile.SourceGraph.Accounting
