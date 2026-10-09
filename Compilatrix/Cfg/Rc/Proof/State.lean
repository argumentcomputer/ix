import Compilatrix.Cfg.Rc.Proof.Scoped
import Compilatrix.Cfg.Rc.Proof.Joins
import Compilatrix.Cfg.Rc.Proof.Frames

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Cfg.Proof (Below Impl spine)

/-- The actual current function, code cursor and real lexical environment.
Marker supply and real-name lower bound are deliberately independent. -/
def At (F : Fir.Program) (P : Program) (fr : Frame) (ρ : Own.Env)
    (saved : List Own.Plain.JEntry) (code : Own.Plain.Code) : Prop :=
  ∃ (fd : Cfg.Fun) (scope : Cfg.Lower.JScope) (params : List (Fir.Var × Own.PSig))
    (acc : List Instr) (next first lo : Nat),
    P.base.fun? fr.fn = some fd ∧ fr.fn < F.size ∧
    Impl fd.block? fr.fn scope fr.blk params acc next (skeleton P.base.size first code) ∧
    fr.rest = spine (skeleton P.base.size first code) ∧ EnvSub ρ fr.env ∧ Below lo ρ ∧
    names lo code = true ∧ Joins P.base.size fd.block? fr.fn fr.env lo scope saved

/-- A checked program derives the exact action table from its actual function
lookup. One successful source action preserves the complete frame invariant,
including all saved join environments and layout witnesses. -/
theorem At.action {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {a : Action} {k : Own.Plain.Code}
    (stateRel : At F P fr ρ saved (.act a k))
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap}
    (effect : Own.Plain.evalAction ρ H a = .ok H') :
    ∃ next, step P (.run fr stk H) = .next (.run next stk H') false ∧ At F P next ρ saved k := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  obtain ⟨fd', table, lookup', tableLookup, source, body, sourceLookup, bodyLookup,
    lowering, bounds, collected⟩ := checked_entry (checkScopedProgram_parts checked).1 range
  have same : fd' = fd := Option.some.inj (lookup'.symm.trans lookup)
  subst fd'
  have size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have functionCheck : checkFunction P.base.size source.vars fd table = true := by
    apply (checkMarkers_iff ..).mpr
    simpa only [size, same] using collected
  let after : Frame := { fr with rest := spine (skeleton P.base.size (first + 1) k) }
  refine ⟨after, checked_frame_action layout cursor functionCheck tableLookup (evalAction_sub env effect), ?_⟩
  exact ⟨fd, scope, params, marker P.base.size first a :: acc, next, first + 1, lo,
    lookup, range, impl_after_action layout, rfl, env, below, scopedNames, joins⟩


end Compilatrix.Cfg.Rc
