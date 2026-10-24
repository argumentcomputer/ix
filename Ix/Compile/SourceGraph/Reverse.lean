module
public import Ix.Compile.SourceGraph

@[expose] public section
namespace Ix.Compile.SourceGraph.Reverse

abbrev Index := Map Name (Array Name)
abbrev Recursors := Map Name (Array (Name × Name))

/-- Consume each old bucket inside its update. -/
def appendAt (m : Map Name (Array α)) (key : Name) (item : α) : Map Name (Array α) :=
  m.alter key fun old => some ((old.getD #[]).push item)

def recStep (m : Recursors) (p : Name × Node) : Recursors :=
  match p.2.grouping with
  | .recursor all => match all[0]? with
    | some first => appendAt m first (first, p.1)
    | none => m
  | _ => m

def recursors (nodes : Map Name Node) : Recursors :=
  nodes.fold (init := {}) fun m n node => recStep m (n, node)

def addCaller (rs : Recursors) (m : Index) (p : Name × Node) : Index :=
  (dependencies rs p.2).foldl (fun m d => appendAt m d p.1) m

/-- Complete original callers, including missing dependency endpoints. -/
def build (nodes : Map Name Node) : Index :=
  let rs := recursors nodes
  nodes.fold (init := {}) fun m n node => addCaller rs m (n, node)

end Ix.Compile.SourceGraph.Reverse
