import Ix.CompileCert.SemanticFrames
import Ix.CompileCert.O6RecRead
import Ix.CompileCert.OptDispatchOrigin

/-! Frame placement for the actual O3/O4/O6 results. Their input arguments
remain an explicit supplier obligation; this is not value preservation. -/
namespace Ix.CompileCert.OptFrames
open Ix (Name Expr ConstantInfo)
open Ix.CompileM Ix.Compile.Pass Ix.Compile.Pass.Opt
open Ix.Compile.ExactKey (ExactName)
open SemanticFrames OptDispatchOrigin

def ArgsFrames (args : Array Expr) : Prop := ∀ a ∈ args, Frames a

theorem mkAppN_frames {f : Expr} {args : Array Expr} (hf : Frames f) (ha : ArgsFrames args) :
    Frames (Ix.Compile.Canon.mkAppN f args) := by
  unfold Ix.Compile.Canon.mkAppN
  exact Array.foldl_induction (fun _ e => Frames e) hf
    (fun i acc held => And.intro held (ha _ (Array.getElem_mem i.isLt)))

theorem append_frames {xs ys : Array Expr} (hx : ArgsFrames xs) (hy : ArgsFrames ys) :
    ArgsFrames (xs ++ ys) := by
  intro e member
  rcases Array.mem_append.mp member with left | right
  · exact hx e left
  · exact hy e right

theorem extract_frames {xs : Array Expr} (held : ArgsFrames xs) (start stop : Nat) :
    ArgsFrames (xs.extract start stop) := by
  intro e member
  obtain ⟨i, _, equal⟩ := Array.mem_extract_iff_getElem.mp member
  exact held e (Array.mem_of_getElem equal)

private theorem empty_frames : ArgsFrames #[] := by
  intro e absent; simp only [Array.not_mem_empty] at absent

private theorem const_frames (name : Name) (levels : Array Ix.Level) :
    Frames (Expr.mkConst name levels) := trivial

theorem pick_frames {xs ys : Array Expr} {indices : Array Nat} (held : ArgsFrames xs)
    (run : pick xs indices = some ys) : ArgsFrames ys := by
  have selected := O6RecRead.option_mapM run
  have members : ∀ y ∈ ys.toList, Frames y := by
    generalize indices.toList = left at selected
    generalize ys.toList = right at selected ⊢
    induction selected with
    | nil => intro y absent; cases absent
    | cons actual rest ih =>
      intro y member
      rcases List.mem_cons.mp member with rfl | old
      · exact held _ (Array.mem_of_getElem? actual)
      · exact ih y old
  exact fun y member => members y (by simpa using member)

private def Post (p : α → Prop) (action : Option α) : Prop := ∀ out, action = some out → p out

private theorem pureP {p : α → Prop} {value : α} (valid : p value) : Post p (pure value) := by
  intro out run; cases run; exact valid

private theorem noneP {p : α → Prop} : Post p none := by intro out run; cases run

private theorem noneBindP {p : β → Prop} (next : α → Option β) :
    Post p ((none : Option α) >>= next) := by intro out run; cases run

private theorem iteP {condition : Prop} [Decidable condition] {yes no : Option α} {p : α → Prop}
    (left : condition → Post p yes) (right : ¬ condition → Post p no) :
    Post p (if condition then yes else no) := by
  split
  · exact left (by assumption)
  · exact right (by assumption)

private theorem bindP {α β : Type} {action : Option α} {next : α → Option β} {p : β → Prop}
    (rest : ∀ value, action = some value → Post p (next value)) : Post p (action >>= next) := by
  intro out run
  obtain ⟨value, actual, tail⟩ := ImageShape.bind_some run
  exact rest value actual out tail

private theorem bindPickP {α : Type} {xs : Array Expr} {indices : Array Nat} {next : Array Expr → Option α}
    {p : α → Prop} (held : ArgsFrames xs) (rest : ∀ ys, ArgsFrames ys → Post p (next ys)) :
    Post p (pick xs indices >>= next) := bindP (fun ys actual => rest ys (pick_frames held actual))

local macro "selection_frames" held:term : tactic => `(tactic|
  with_reducible repeat' first
    | simp (config := { failIfUnchanged := true }) only [pure_bind]
    | exact noneP
    | exact noneBindP _
    | apply iteP <;> intro condition
    | refine bindPickP ?_ (fun _ _ => ?_)
    | apply pureP
    | apply mkAppN_frames
    | exact const_frames _ _
    | exact $held
    | assumption
    | apply append_frames
    | apply extract_frames
    | exact empty_frames
    | trivial
    | refine bindP (fun _ _ => ?_)
    | split
    | dsimp (config := { failIfUnchanged := true }) only)

theorem O3_frames (env : OptEnv) (o : Occ) {out : Expr} (held : ArgsFrames o.args)
    (run : O3.apply env o = some out) : Frames out := by
  have result : Post Frames (O3.apply env o) := by
    unfold O3.apply
    selection_frames held
  exact result out run

theorem O4_frames (env : OptEnv) (o : Occ) {out : Expr} (held : ArgsFrames o.args)
    (run : O4.apply env o = some out) : Frames out := by
  have result : Post Frames (O4.apply env o) := by
    unfold O4.apply
    selection_frames held
  exact result out run

theorem O6_frames (env : OptEnv) (o : Occ) {out : Expr} (held : ArgsFrames o.args)
    (run : O6.apply env o = some out) : Frames out := by
  have result : Post Frames (O6.apply env o) := by
    unfold O6.apply
    selection_frames held
  exact result out run

/-- Remaining cases are literal successful producer calls, not assumptions
that their outputs preserve frames. The original Branch retains all misses. -/
def OutputCases (fuel : Nat) (env : OptEnv) (o : Occ) (out : Expr) : Prop :=
  Frames out ∨ O11a.apply env o = some out ∨
    ∃ reports, O2.apply (OptDispatchOrigin.recur fuel env) env o = some (out, reports)

theorem branch_frames {fuel : Nat} {env : OptEnv} {o : Occ} {tag : String}
    {out : Expr} {reports : Array String} (held : ArgsFrames o.args)
    (branch : Branch fuel env o tag out reports) : OutputCases fuel env o out := by
  cases branch with
  | o11a hit => exact .inr (.inl hit)
  | o2 miss hit => exact .inr (.inr ⟨_, hit⟩)
  | o3 miss11 miss2 hit => exact .inl (O3_frames env o held hit)
  | o4 miss11 miss2 miss3 hit => exact .inl (O4_frames env o held hit)
  | o6 miss11 miss2 miss3 miss4 hit => exact .inl (O6_frames env o held hit)

theorem engineN_frame_cases {fuel : Nat} {env : OptEnv} {o : Occ} {tag : String}
    {out : Expr} {reports : Array String} (held : ArgsFrames o.args)
    (run : engineN (fuel + 1) env o = some (tag, out, reports)) :
    Branch fuel env o tag out reports ∧ OutputCases fuel env o out :=
  ⟨engineN_origin run, branch_frames held (engineN_origin run)⟩

theorem passConfig_frame_cases {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {site : Option Name} {name : Name} {levels : Array Ix.Level} {args : Array Expr}
    {out : Expr} {constants : Array ConstantInfo} {proofTag : Option String} {reports : Array String}
    (held : ArgsFrames args)
    (hit : (passConfig cenv views sourceAll).opt? site name levels args = some (out, constants, proofTag, reports)) :
    Ix.AuxGen.SourceIdentity.permitsOptimization cenv.env name = true ∧ constants = #[] ∧ proofTag = none ∧
    ∃ tag, engine (driverEnv cenv views sourceAll) { head := name, us := levels, args, site } = some (tag, out, reports) ∧
      Branch 63 (driverEnv cenv views sourceAll) { head := name, us := levels, args, site } tag out reports ∧
      OutputCases 63 (driverEnv cenv views sourceAll) { head := name, us := levels, args, site } out := by
  obtain ⟨permitted, empty, noProof, tag, actual, branch⟩ := passConfig_origin hit
  exact ⟨permitted, empty, noProof, tag, actual, branch, branch_frames held branch⟩

end Ix.CompileCert.OptFrames
