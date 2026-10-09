import Compilatrix.Cfg.Rc.Proof.Physical.CaseSelection
import Compilatrix.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Cfg.Proof (Impl ImplArms ImplOpt spine)
open Cfg.Lower (armEdges count countAlts)

theorem case_arms_layout {P : Program} {fd : Cfg.Fun} {fn : Nat} {scope : Cfg.Lower.JScope}
    {key : Key.CtorKey} {body : Own.Plain.Code} {lo : Nat}
    (alts : List Own.Plain.Alt) (default : Option Own.Plain.Code) (next first : Nat)
    (arms : ImplArms fd.block? fn scope next (skeletonAlts P.base.size first alts))
    (fallback : ImplOpt fd.block? fn scope (next + countAlts (skeletonAlts P.base.size first alts))
      (skeletonOpt P.base.size (first + actionCountAlts alts) default))
    (armNames : namesAlts lo alts = true) (defaultNames : namesOpt lo default = true)
    (selected : ownCase key alts default = some body) :
    ∃ target supply,
      selectEdge key (armEdges next (skeletonAlts P.base.size first alts))
        (default.map fun _ => ({target := next + countAlts (skeletonAlts P.base.size first alts)} : Edge)) =
        some {target} ∧
      Impl fd.block? fn scope target [] [] (target+1) (skeleton P.base.size supply body) ∧
      names lo body = true := by
  match alts, default with
  | [], none => cases selected
  | [], some code =>
    cases selected
    refine ⟨next, first, ?_, ?_, defaultNames⟩
    · simp [skeletonAlts, armEdges, selectEdge, countAlts]
    · simpa only [skeletonAlts, countAlts, actionCountAlts, Nat.add_zero, skeletonOpt, ImplOpt] using fallback
  | .mk tag code :: rest, default =>
    simp only [ownCase] at selected
    simp only [skeletonAlts, ImplArms] at arms
    simp only [namesAlts, Bool.and_eq_true] at armNames
    by_cases equal : tag = key
    · simp only [equal, ↓reduceIte, Option.some.injEq] at selected
      subst code
      refine ⟨next, first, ?_, arms.1, armNames.1⟩
      simp only [skeletonAlts, armEdges, selectEdge, equal, ↓reduceIte]
    · simp only [equal, ↓reduceIte] at selected
      have labels : next + countAlts (skeletonAlts P.base.size first (.mk tag code :: rest)) =
          next + 1 + count (skeleton P.base.size first code) +
            countAlts (skeletonAlts P.base.size (first + actionCount code) rest) := by
        simp only [skeletonAlts, countAlts]
        omega
      have fallback' : ImplOpt fd.block? fn scope
          (next+1+count (skeleton P.base.size first code) +
            countAlts (skeletonAlts P.base.size (first+actionCount code) rest))
          (skeletonOpt P.base.size (first+actionCount code+actionCountAlts rest) default) := by
        rw [← labels]
        simpa only [actionCountAlts, Nat.add_assoc] using fallback
      obtain ⟨target, supply, choice, layout, bodyNames⟩ := case_arms_layout rest default
        (next+1+count (skeleton P.base.size first code)) (first+actionCount code)
        arms.2 fallback' armNames.2 defaultNames selected
      refine ⟨target, supply, ?_, layout, bodyNames⟩
      rw [labels]
      simpa only [skeletonAlts, armEdges, selectEdge, equal, ↓reduceIte] using choice
termination_by alts.length

/-- The selected actual arm opens a parameterless source block. All source
lexical and saved-join environments are retained by its structural layout. -/
theorem case_layout {F : Fir.Program} {P : Program} {source : Cfg.Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {x : Fir.Var} {alts : List Own.Plain.Alt}
    {default : Option Own.Plain.Code} {key : Key.CtorKey} {body : Own.Plain.Code}
    (before : At F P source ρ saved (.case x alts default))
    (selected : ownCase key alts default = some body) :
    ∃ fd block edges fallback edge targetBlock,
      P.base.fun? source.fn = some fd ∧ fd.blocks[source.blk]? = some block ∧
      source.rest = [] ∧ block.term = .switch x edges fallback ∧
      selectEdge key edges fallback = some edge ∧ edge.args = [] ∧ edge.back = false ∧
      fd.blocks[edge.target]? = some targetBlock ∧ targetBlock.params = [] ∧
      At F P {source with blk := edge.target, rest := targetBlock.body} ρ saved body := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := before
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [names, Bool.and_eq_true] at scopedNames
  obtain ⟨label, supply, choice, bodyLayout, bodyNames⟩ :=
    case_arms_layout alts default next first layout.2.1 layout.2.2 scopedNames.1 scopedNames.2 selected
  obtain ⟨terminal, targetLookup⟩ := Cfg.Proof.impl_head bodyLayout
  let edges := armEdges next (skeletonAlts P.base.size first alts)
  let fallback := default.map fun _ => ({target := next+countAlts (skeletonAlts P.base.size first alts)} : Edge)
  let block : Cfg.Block := {params, body := acc.reverse, term := .switch x edges fallback}
  let targetBlock : Cfg.Block := {
    params := []
    body := spine (skeleton P.base.size supply body)
    term := terminal }
  refine ⟨fd, block, edges, fallback, {target := label}, targetBlock, lookup, ?_, cursor, rfl,
    choice, rfl, rfl, ?_, rfl, ?_⟩
  · cases default <;>
      simpa only [Cfg.Fun.block?, Cfg.Proof.caseTerm, skeletonOpt, edges, fallback, block,
        Option.map_none, Option.map_some] using layout.1
  · simpa only [Cfg.Fun.block?, List.reverse_nil, List.nil_append] using targetLookup
  · exact ⟨fd, scope, [], [], label+1, supply, lo, lookup, range, bodyLayout, rfl,
      env, below, bodyNames, joins⟩



end Compilatrix.Cfg.Rc.Native
