import Ix.CompileCert.BlockFrame
import Ix.AuxGen.Recursor

/-! The production source-discovery walk preserves authenticated head claims,
including on errors. This is a state-effect boundary for auxiliary generation;
it does not assert completeness or semantic correctness of discovered families. -/

namespace Ix.CompileCert.HeadWriterFrame

open Ix Ix.CompileM

theorem Frame.auxLookupConst (name : Name) : Frame (Ix.AuxGen.lookupConst? name) :=
  Frame.bind Frame.read fun _ => Frame.pure _

theorem Frame.auxEnvGet (overlay : Option (Std.HashMap Name ConstantInfo)) (name : Name) :
    Frame (Ix.AuxGen.envGet overlay name) := by
  unfold Ix.AuxGen.envGet
  split
  · exact Frame.pure _
  · exact Frame.auxLookupConst name

theorem Frame.tryDetectNestedFVarAt (expr : Expr) (blockNames : Std.HashSet Name)
    (flat : Array Ix.AuxGen.FvarFlatMember)
    (seen : Array (Name × Array Address × Array Address))
    (overlay : Option (Std.HashMap Name ConstantInfo)) (params : Array Name) :
    Frame (Ix.AuxGen.tryDetectNestedFVarAt expr blockNames flat seen overlay params) := by
  unfold Ix.AuxGen.tryDetectNestedFVarAt
  with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.auxEnvGet _ _
    | refine Frame.bind ?_ (fun value => ?_)
    | refine frame_forIn_array _ _ _ (fun value acc => ?_)
    | dsimp only
    | split

theorem Frame.scanNestedFVars (blockNames : Std.HashSet Name)
    (overlay : Option (Std.HashMap Name ConstantInfo)) (params : Array Name)
    (work : List Expr) (flat : Array Ix.AuxGen.FvarFlatMember)
    (seen : Array (Name × Array Address × Array Address)) (visited : Std.HashSet Address) :
    Frame (Ix.AuxGen.scanNestedFVars blockNames overlay params work flat seen visited) := by
  induction work, flat, seen, visited using Ix.AuxGen.scanNestedFVars.induct with
  | case1 flat seen visited =>
    rw [Ix.AuxGen.scanNestedFVars]
    exact Frame.pure _
  | case2 flat seen visited expr rest present ih =>
    rw [Ix.AuxGen.scanNestedFVars]
    simpa only [present, ↓reduceIte] using ih
  | case3 flat seen visited expr rest absent visitedNext restIH childrenIH =>
    rw [Ix.AuxGen.scanNestedFVars]
    simp only [absent]
    apply Frame.bind (Frame.tryDetectNestedFVarAt _ _ _ _ _ _)
    intro result
    rcases result with ⟨recognized, flat, seen⟩
    dsimp only
    split
    · exact restIH _ _
    · cases expr <;> exact childrenIH _ _

theorem Frame.tryDetectNestedFVar (expr : Expr) (blockNames : Std.HashSet Name)
    (flat : Array Ix.AuxGen.FvarFlatMember)
    (seen : Array (Name × Array Address × Array Address))
    (overlay : Option (Std.HashMap Name ConstantInfo)) (params : Array Name) :
    Frame (Ix.AuxGen.tryDetectNestedFVar expr blockNames flat seen overlay params) :=
  Frame.scanNestedFVars _ _ _ _ _ _ _

end Ix.CompileCert.HeadWriterFrame
