import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionState
import IxCC.Cfg.Rc.Proof.Ordinary

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own

/-- Bind and increment advance the real accepted Cfg cursor, with the same
source effects proved by projection_increment. Saved Cfg frames are retained. -/
theorem projection_cfg_after
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Cfg.Rc.Program}
    (accepted : Cfg.Rc.checkScopedProgram F bodies P = true)
    {frame : Cfg.Frame} {ρo : Own.Env} {joins : List Own.Plain.JEntry}
    {x y i : Nat} {key : Key.CtorKey} {code : Own.Plain.Code}
    (cursor : Cfg.Rc.At F P frame ρo joins
      (.bind x (.proj y key i) (.act (.inc x 1) code)))
    {H H' : Heap} {value : RVal} (stack : List (Cfg.Frame × Fir.Var))
    (projection : Own.evalRhs .rc {ctors := F.ctors, known := F.known}
      ρo H (.proj y key i) = .ok (value, H))
    (increment : Own.Plain.evalAction (ρo.insert x value) H (.inc x 1) = .ok H') :
    ∃ borrowed next,
      Cfg.Rc.step P (.run frame stack H) = .next (.run borrowed stack H) false ∧
      Cfg.Rc.At F P borrowed (ρo.insert x value) joins (.act (.inc x 1) code) ∧
      Cfg.Rc.step P (.run borrowed stack H) = .next (.run next stack H') false ∧
      Cfg.Rc.At F P next (ρo.insert x value) joins code := by
  have projection' : Own.Plain.evalRhs {ctors := F.ctors, known := F.known}
      ρo H (.proj y key i) = .ok (value, H) := projection
  obtain ⟨borrowed, projectStep, borrowedCursor⟩ := Cfg.Rc.At.bind accepted cursor
    (by intro f args equal; cases equal) (stk := stack) projection'
  obtain ⟨next, incStep, nextCursor⟩ := Cfg.Rc.At.action accepted borrowedCursor
    (stk := stack) increment
  exact ⟨borrowed, next, projectStep, borrowedCursor, incStep, nextCursor⟩


end IxCC.Cfg.Rc.Proof.Physical.Bridge
