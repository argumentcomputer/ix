import Ix.CompileCert.HeadWriterFrame
import Batteries.Tactic.OpenPrivate

/-! The actual production expression compiler preserves the authenticated head
claim accumulator, including on errors. These are state-effect facts; they do
not assert source/target semantic correspondence or cache-content validity. -/

namespace Ix.CompileCert.HeadWriterFrame

set_option maxHeartbeats 1000000

open Ix (Name Expr Level)
open Ix.CompileM

open private Ix.CompileM.compileKVMap.match_5
  Ix.CompileM.compileKVMap._sparseCasesOn_5 from Ix.CompileM

theorem Frame.allocArenaNode (node : Ixon.ExprMetaData) : Frame (allocArenaNode node) :=
  Frame.modifyGet _ (fun _ => rfl)

theorem Frame.pushUnivPatch (root : UInt64) (univs : Array UInt64) :
    Frame (pushUnivPatch root univs) := Frame.modify _ (fun _ => rfl)

theorem Frame.checkedTableIndex (table : String) (index : Nat) :
    Frame (checkedTableIndex table index) := by
  unfold Ix.CompileM.checkedTableIndex
  split
  · exact Frame.pure _
  · exact Frame.throw _

theorem Frame.discard {action : CompileM α} (framed : Frame action) : Frame (Functor.discard action) := by
  unfold Functor.discard
  exact Frame.map framed (fun _ => ())

theorem Frame.compileUniv (level : Level) : Frame (compileUniv level) := by
  induction level <;> rw [Ix.CompileM.compileUniv]
  all_goals
    apply Frame.bind Frame.get
    intro state
    with_reducible repeat' first
      | assumption
      | exact Frame.pure _
      | exact Frame.throw _
      | exact Frame.readBlock
      | exact Frame.checkedTableIndex _ _
      | refine Frame.bind ?_ (fun value => ?_)
      | apply Frame.modify; intro _; simp only [BlockState.cacheUniv]
      | dsimp only
      | split

theorem Frame.internUniv (univ : Ixon.Univ) : Frame (internUniv univ) := by
  unfold Ix.CompileM.internUniv
  with_reducible repeat' first
    | exact Frame.get
    | exact Frame.pure _
    | exact Frame.checkedTableIndex _ _
    | exact Frame.discard (Frame.checkedTableIndex _ _)
    | refine Frame.bind ?_ (fun _ => ?_)
    | dsimp only
    | split
  all_goals
    apply Frame.modifyGet
    intro state
    simp only [BlockState.internUniv]
    split <;> rfl

theorem Frame.internMetaUniv (univ : Ixon.Univ) : Frame (internMetaUniv univ) := by
  unfold Ix.CompileM.internMetaUniv
  apply Frame.bind Frame.get
  intro state
  dsimp only
  apply Frame.bind (Frame.discard (Frame.checkedTableIndex _ _))
  intro _
  apply Frame.modifyGet
  intro state
  simp only [BlockState.internMetaUniv]
  split <;> rfl

theorem Frame.canonUnivCached (univ : Ixon.Univ) : Frame (canonUnivCached univ) := by
  unfold Ix.CompileM.canonUnivCached
  apply Frame.bind Frame.get
  intro state
  split
  · exact Frame.pure _
  · exact Frame.bind (Frame.modify _ (fun _ => rfl)) (fun _ => Frame.pure _)

theorem Frame.compileAndInternUnivCanon (level : Level) : Frame (compileAndInternUnivCanon level) := by
  unfold Ix.CompileM.compileAndInternUnivCanon
  with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.throw _
    | exact Frame.get
    | exact Frame.compileUniv _
    | exact Frame.canonUnivCached _
    | exact Frame.internUniv _
    | exact Frame.internMetaUniv _
    | refine Frame.bind ?_ (fun value => ?_)
    | dsimp only
    | split

theorem Frame.internRefMeta (address : Address) : Frame (internRefMeta address) := by
  unfold Ix.CompileM.internRefMeta
  with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.get
    | exact Frame.checkedTableIndex _ _
    | refine Frame.bind ?_ (fun value => ?_)
    | apply Frame.modify; intro _; rfl
    | dsimp only
    | split

theorem Frame.internRef (address : Address) : Frame (internRef address) := by
  unfold Ix.CompileM.internRef
  apply Frame.bind Frame.get
  intro state
  split
  · exact Frame.internRefMeta _
  · with_reducible repeat' first
      | exact Frame.get
      | exact Frame.pure _
      | exact Frame.checkedTableIndex _ _
      | exact Frame.discard (Frame.checkedTableIndex _ _)
      | refine Frame.bind ?_ (fun _ => ?_)
      | dsimp only
      | split
    all_goals
      apply Frame.modifyGet
      intro nextState
      simp only [BlockState.internRef]
      split <;> rfl

theorem Frame.lookupConstAddr (name : Name) : Frame (lookupConstAddr name) := by
  unfold Ix.CompileM.lookupConstAddr
  apply Frame.bind Frame.read
  intro env
  apply Frame.bind Frame.get
  intro state
  repeat' first | exact Frame.pure _ | exact Frame.throw _ | split

theorem Frame.storeString (text : String) : Frame (storeString text) :=
  Frame.bind (Frame.modify _ (fun _ => rfl)) (fun _ => Frame.pure _)

theorem Frame.serializeIxSubstring (text : Ix.Substring) : Frame (serializeIxSubstring text) :=
  Frame.bind (Frame.storeString _) (fun _ => Frame.pure _)

theorem Frame.serializeIxSourceInfo (info : Ix.SourceInfo) : Frame (serializeIxSourceInfo info) := by
  cases info <;> unfold Ix.CompileM.serializeIxSourceInfo
  · exact Frame.bind (Frame.serializeIxSubstring _) fun _ =>
      Frame.bind (Frame.serializeIxSubstring _) fun _ => Frame.pure _
  all_goals exact Frame.pure _

theorem Frame.serializeIxSyntaxPreresolved (info : Ix.SyntaxPreresolved) :
    Frame (serializeIxSyntaxPreresolved info) := by
  cases info <;> unfold Ix.CompileM.serializeIxSyntaxPreresolved
  all_goals apply Frame.bind (Frame.compileName _); intro _
  · exact Frame.pure _
  · exact Frame.bind (frame_mapM_array _ _ (fun _ _ => Frame.storeString _)) (fun _ => Frame.pure _)

theorem Frame.serializeIxSyntax (syn : Ix.Syntax) : Frame (serializeIxSyntax syn) := by
  induction syn using Ix.CompileM.serializeIxSyntax.induct with
  | case1 => rw [Ix.CompileM.serializeIxSyntax]; exact Frame.pure _
  | case2 info kind args ih =>
    rw [Ix.CompileM.serializeIxSyntax]
    apply Frame.bind (Frame.compileName _)
    intro _
    apply Frame.bind (Frame.serializeIxSourceInfo _)
    intro _
    apply Frame.bind
    · apply frame_mapM_array
      intro arg _
      exact ih arg
    · intro _; exact Frame.pure _
  | case3 info value =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Frame.bind (Frame.serializeIxSourceInfo _) fun _ =>
      Frame.bind (Frame.storeString _) fun _ => Frame.pure _
  | case4 info raw value resolved =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Frame.bind (Frame.compileName _) fun _ =>
      Frame.bind (Frame.serializeIxSourceInfo _) fun _ =>
      Frame.bind (Frame.serializeIxSubstring _) fun _ =>
      Frame.bind (frame_mapM_array _ _ (fun _ _ => Frame.serializeIxSyntaxPreresolved _))
        fun _ => Frame.pure _

theorem Frame.compileDataValue (value : Ix.DataValue) : Frame (compileDataValue value) := by
  cases value <;> unfold Ix.CompileM.compileDataValue
  all_goals with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.compileName _
    | exact Frame.serializeIxSyntax _
    | refine Frame.bind ?_ (fun value => ?_)
    | apply Frame.modify; intro _; rfl

theorem Frame.compileKVMap (values : Array (Name × Ix.DataValue)) : Frame (compileKVMap values) := by
  rcases values with ⟨_ | ⟨⟨name, value⟩, _ | ⟨next, rest⟩⟩⟩ <;> try cases value
  all_goals unfold Ix.CompileM.compileKVMap
  all_goals delta Ix.CompileM.compileKVMap.match_5
  all_goals simp only [Array.size, List.length_cons, List.length_nil,
    Nat.succ.injEq, Nat.add_one_ne_zero, Nat.reduceEqDiff, ↓reduceDIte]
  all_goals try delta Ix.CompileM.compileKVMap._sparseCasesOn_5
  all_goals try simp only [← Array.getElem_toList, List.getElem_cons_zero]
  all_goals with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.throw _
    | exact Frame.read
    | exact Frame.get
    | exact Frame.compileName _
    | exact Frame.compileDataValue _
    | refine Frame.bind ?_ (fun value => ?_)
    | refine frame_mapM_array _ _ (fun value mem => ?_)
    | dsimp only
    | split

theorem Frame.compileConstExprRaw (name : Name) (levels : Array Level) :
    Frame (compileConstExprRaw name levels) := by
  unfold Ix.CompileM.compileConstExprRaw
  with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.readBlock
    | exact Frame.checkedTableIndex _ _
    | exact Frame.compileName _
    | exact Frame.compileAndInternUnivCanon _
    | exact Frame.allocArenaNode _
    | exact Frame.pushUnivPatch _ _
    | exact Frame.lookupConstAddr _
    | exact Frame.internRef _
    | refine Frame.bind ?_ (fun value => ?_)
    | refine frame_mapM_array _ _ (fun value mem => ?_)
    | dsimp only
    | split

theorem Frame.compileExprPartial (expr : Expr) : Frame (compileExprPartial expr) := by
  induction expr using Ix.CompileM.compileExprPartial.induct with
  | case1 expr ih =>
    rw [Ix.CompileM.compileExprPartial]
    apply Frame.bind Frame.get
    intro state
    split
    · exact Frame.pure _
    · cases expr <;> (try cases ‹Lean.Literal›) <;> dsimp only at ih ⊢
      all_goals with_reducible repeat' first
          | exact Frame.pure _
          | exact Frame.throw _
          | exact Frame.allocArenaNode _
          | exact Frame.pushUnivPatch _ _
          | exact Frame.compileAndInternUnivCanon _
          | exact Frame.compileConstExprRaw _ _
          | exact Frame.compileName _
          | exact Frame.internRef _
          | exact Frame.lookupConstAddr _
          | exact Frame.compileKVMap _
          | exact ih
          | exact ih.1
          | exact ih.2
          | exact ih.2.1
          | exact ih.2.2
          | exact ih.2 _ (by assumption)
          | refine Frame.bind ?_ (fun value => ?_)
          | refine frame_forIn'_array _ _ _ (fun value mem acc => ?_)
          | apply Frame.modify; intro _; rfl
          | dsimp only
          | split

theorem Frame.compileAppSpine (expr : Expr) : Frame (compileAppSpine expr) := by
  unfold Ix.CompileM.compileAppSpine
  split
  apply Frame.bind (Frame.compileExprPartial _)
  rintro ⟨value, root⟩
  apply Frame.bind
  · apply frame_forIn_array
    intro arg acc
    exact Frame.bind (Frame.compileExprPartial arg) fun result =>
      Frame.bind (Frame.allocArenaNode _) fun _ => Frame.pure _
  · intro result; exact Frame.pure _

theorem Frame.compileAppTotal (compile : Expr → CompileM (Ixon.Expr × UInt64))
    (keeps : ∀ expr, Frame (compile expr)) (expr : Expr) : Frame (compileAppTotal compile expr) := by
  induction expr <;> simp only [Ix.CompileM.compileAppTotal]
  case app fn arg hash ihfn iharg =>
    exact Frame.bind ihfn fun fn => Frame.bind (keeps arg) fun arg =>
      Frame.bind (Frame.allocArenaNode _) fun _ => Frame.pure _
  all_goals exact keeps _

theorem Frame.compileExprTotalStep (compile : Expr → CompileM (Ixon.Expr × UInt64))
    (keeps : ∀ expr, Frame (compile expr)) (expr : Expr) : Frame (compileExprTotalStep compile expr) := by
  cases expr <;> (try cases ‹Lean.Literal›) <;> unfold Ix.CompileM.compileExprTotalStep
  all_goals with_reducible repeat' first
    | exact keeps _
    | exact Frame.pure _
    | exact Frame.throw _
    | exact Frame.readBlock
    | exact Frame.allocArenaNode _
    | exact Frame.pushUnivPatch _ _
    | exact Frame.compileAndInternUnivCanon _
    | exact Frame.compileName _
    | exact Frame.internRef _
    | exact Frame.lookupConstAddr _
    | exact Frame.compileKVMap _
    | exact Frame.compileAppTotal _ keeps _
    | refine Frame.bind ?_ (fun value => ?_)
    | refine frame_mapM_array _ _ (fun value mem => ?_)
    | apply Frame.modify; intro _; rfl
    | dsimp only
    | split

theorem Frame.compileExprTotalFuel (fuel : Nat) (expr : Expr) : Frame (compileExprTotalFuel fuel expr) := by
  induction fuel generalizing expr with
  | zero => rw [Ix.CompileM.compileExprTotalFuel]; exact Frame.throw _
  | succ fuel ih =>
    rw [Ix.CompileM.compileExprTotalFuel]
    apply Frame.bind Frame.get
    intro state
    split
    · exact Frame.pure _
    · exact Frame.bind (Frame.compileExprTotalStep _ ih _) fun result =>
        Frame.bind (Frame.modify _ (fun _ => rfl)) fun _ => Frame.pure _

theorem Frame.compileExprTotal (expr : Expr) : Frame (compileExprTotal expr) :=
  Frame.compileExprTotalFuel _ _

theorem Frame.pass3CompileRecords (expr : Expr) : Frame (pass3CompileRecords expr) := by
  unfold Ix.CompileM.pass3CompileRecords
  apply Frame.bind Frame.read
  intro env
  apply Frame.bind
  · apply frame_forIn_array
    intro index acc
    with_reducible repeat' first
      | exact Frame.pure _
      | exact Frame.throw _
      | exact Frame.get
      | exact Frame.compileExprPartial _
      | refine Frame.bind ?_ (fun value => ?_)
      | apply Frame.modify; intro _; rfl
      | dsimp only
      | split
  · intro result; exact Frame.pure _

theorem Frame.compileExpr (expr : Expr) : Frame (compileExpr expr) := by
  unfold Ix.CompileM.compileExpr
  apply Frame.bind Frame.read
  intro env
  with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.compileExprPartial _
    | exact Frame.compileExprTotal _
    | exact Frame.pass3CompileRecords _
    | refine Frame.bind ?_ (fun value => ?_)
    | dsimp only
    | split

end Ix.CompileCert.HeadWriterFrame
