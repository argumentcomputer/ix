import IxCC.Anf.Census

/-! # Pruning unreachable globals

The last step of the Phase 1 middle end: keep the globals reachable from the
roots (through `call` and `glob`), renumbered densely in their old order,
with every reference renamed. Unreachable globals are never evaluated, so
the program's behaviour is unchanged. Inlining and specialisation leave the
globals they copied behind; pruning removes them before the Anf → Fir
boundary. Kernel-evaluable: a fuelled worklist over `NatMap`s (D17). -/

namespace IxCC.Anf.Prune

mutual

/-- Rename global references. -/
def Exp.rename (m : Src.NatMap Nat) : Exp → Exp
  | .bind c b e => .bind c (Bind.rename m b) (Exp.rename m e)
  | .join n r b e => .join n r (Exp.rename m b) (Exp.rename m e)
  | .case x alts d => .case x (Exp.renameAlts m alts) (Exp.renameOpt m d)
  | .tick e => .tick (Exp.rename m e)
  | e@(.jump ..) | e@(.ret _) | e@.trap => e

def Bind.rename (m : Src.NatMap Nat) : Bind → Bind
  | .glob g => .glob (m.getD g g)
  | .call g as => .call (m.getD g g) as
  | .fn ps b => .fn ps (Exp.rename m b)
  | b => b

def Exp.renameAlts (m : Src.NatMap Nat) : List Alt → List Alt
  | [] => []
  | .mk k n b :: as => .mk k n (Exp.rename m b) :: Exp.renameAlts m as

def Exp.renameOpt (m : Src.NatMap Nat) : Option Exp → Option Exp
  | none => none
  | some e => some (Exp.rename m e)

end

/-- The globals reachable from `todo` (a fuelled worklist). -/
def reach (P : Program) : Nat → List GlobalId → Src.NatMap Unit → Src.NatMap Unit
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, g :: todo, seen =>
    if seen.contains g then reach P fuel todo seen
    else
      let next := match P.global? g with
        | some gd => gd.body.refs
        | none => []
      reach P fuel (next ++ todo) (seen.insert g ())

/-- Keep the reachable globals. -/
def run (P : Program) : Program :=
  let total := P.globalList.foldl (fun n (_, gd) => n + gd.body.refs.length) 0
  let seen := reach P (P.size + total + P.roots.length + 1) P.roots .leaf
  let kept := (List.range P.size).filter seen.contains
  let m : Src.NatMap Nat := Src.NatMap.ofList (kept.zipIdx)
  let gs := kept.filterMap fun g =>
    (P.global? g).map fun gd => { gd with body := Exp.rename m gd.body }
  { P.withGlobals gs with roots := P.roots.map fun r => m.getD r r }

end IxCC.Anf.Prune
