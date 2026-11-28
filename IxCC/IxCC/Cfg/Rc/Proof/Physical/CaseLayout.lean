import IxCC.Cfg.Rc.Proof.Physical.CaseSelection
import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Cfg.Proof (Impl ImplArms ImplOpt spine)
open Cfg.Lower (armEdges count countAlts)

theorem case_arms_layout {P : Program} {fd : Cfg.Fun} {fn : Nat} {scope : Cfg.Lower.JScope}
    {key : Key.CtorKey} {body : Own.Plain.Code} {lo slotBase : Nat} {ctors : List Lam.CtorInfo}
    (alts : List Own.Plain.Alt) (default : Option Own.Plain.Code) (next first : Nat)
    (arms : ImplArms fd.block? fn scope next (skeletonAlts P.base.size first alts ctors slotBase))
    (fallback : ImplOpt fd.block? fn scope (next + countAlts (skeletonAlts P.base.size first alts ctors slotBase))
      (skeletonOpt P.base.size (first + actionCountAlts alts) default ctors slotBase))
    (armNames : namesAlts lo alts = true) (defaultNames : namesOpt lo default = true)
    (armVb : varsBelowAlts slotBase alts = true) (defaultVb : varsBelowOpt slotBase default = true)
    (armRc : reuseCtorsOkAlts ctors alts = true) (defaultRc : reuseCtorsOkOpt ctors default = true)
    (selected : ownCase key alts default = some body) :
    ∃ target supply,
      selectEdge key (armEdges next (skeletonAlts P.base.size first alts ctors slotBase))
        (default.map fun _ => ({target := next + countAlts (skeletonAlts P.base.size first alts ctors slotBase)} : Edge)) =
        some {target} ∧
      Impl fd.block? fn scope target [] [] (target+1) (skeleton P.base.size supply body ctors slotBase) ∧
      names lo body = true ∧ varsBelow slotBase body = true ∧ reuseCtorsOk ctors body = true := by
  match alts, default with
  | [], none => cases selected
  | [], some code =>
    cases selected
    refine ⟨next, first, ?_, ?_, defaultNames, defaultVb, defaultRc⟩
    · simp [skeletonAlts, armEdges, selectEdge, countAlts]
    · simpa only [skeletonAlts, countAlts, actionCountAlts, Nat.add_zero, skeletonOpt, ImplOpt] using fallback
  | .mk tag code :: rest, default =>
    simp only [ownCase] at selected
    simp only [skeletonAlts, ImplArms] at arms
    simp only [namesAlts, Bool.and_eq_true] at armNames
    simp only [varsBelowAlts, Bool.and_eq_true] at armVb
    simp only [reuseCtorsOkAlts, Bool.and_eq_true] at armRc
    by_cases equal : tag = key
    · simp only [equal, ↓reduceIte, Option.some.injEq] at selected
      subst code
      refine ⟨next, first, ?_, arms.1, armNames.1, armVb.1, armRc.1⟩
      simp only [skeletonAlts, armEdges, selectEdge, equal, ↓reduceIte]
    · simp only [equal, ↓reduceIte] at selected
      have labels : next + countAlts (skeletonAlts P.base.size first (.mk tag code :: rest) ctors slotBase) =
          next + 1 + count (skeleton P.base.size first code ctors slotBase) +
            countAlts (skeletonAlts P.base.size (first + actionCount code) rest ctors slotBase) := by
        simp only [skeletonAlts, countAlts]
        omega
      have fallback' : ImplOpt fd.block? fn scope
          (next+1+count (skeleton P.base.size first code ctors slotBase) +
            countAlts (skeletonAlts P.base.size (first+actionCount code) rest ctors slotBase))
          (skeletonOpt P.base.size (first+actionCount code+actionCountAlts rest) default ctors slotBase) := by
        rw [← labels, Nat.add_assoc]
        exact fallback
      obtain ⟨target, supply, choice, layout, bodyNames, bodyVb, bodyRc⟩ := case_arms_layout rest default
        (next+1+count (skeleton P.base.size first code ctors slotBase)) (first+actionCount code)
        arms.2 fallback' armNames.2 defaultNames armVb.2 defaultVb armRc.2 defaultRc selected
      refine ⟨target, supply, ?_, layout, bodyNames, bodyVb, bodyRc⟩
      rw [labels]
      simpa only [skeletonAlts, armEdges, selectEdge, equal, ↓reduceIte] using choice
termination_by alts.length

/-- The selected actual arm opens a parameterless source block. All source
lexical and saved-join environments are retained by its structural layout. -/
theorem case_layout {F : Fir.Program} {P : Program} {source : Cfg.Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {x : Fir.Var} {alts : List Own.Plain.Alt}
    {default : Option Own.Plain.Code} {key : Key.CtorKey} {body : Own.Plain.Code}
    {rslots : Src.NatMap Own.RVal}
    (before : At F P source ρ saved (.case x alts default) rslots)
    (selected : ownCase key alts default = some body) :
    ∃ fd block edges fallback edge targetBlock,
      P.base.fun? source.fn = some fd ∧ fd.blocks[source.blk]? = some block ∧
      source.rest = [] ∧ block.term = .switch x edges fallback ∧
      selectEdge key edges fallback = some edge ∧ edge.args = [] ∧ edge.back = false ∧
      fd.blocks[edge.target]? = some targetBlock ∧ targetBlock.params = [] ∧
      At F P {source with blk := edge.target, rest := targetBlock.body} ρ saved body rslots := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := before
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [names, Bool.and_eq_true] at scopedNames
  simp only [varsBelow, Bool.and_eq_true] at vb
  simp only [reuseCtorsOk, Bool.and_eq_true] at rc
  obtain ⟨label, supply, choice, bodyLayout, bodyNames, bodyVb, bodyRc⟩ :=
    case_arms_layout alts default next first layout.2.1 layout.2.2 scopedNames.1 scopedNames.2
      vb.1 vb.2 rc.1 rc.2 selected
  obtain ⟨terminal, targetLookup⟩ := Cfg.Proof.impl_head bodyLayout
  let edges := armEdges next (skeletonAlts P.base.size first alts F.ctors slotBase)
  let fallback := default.map fun _ => ({target := next+countAlts (skeletonAlts P.base.size first alts F.ctors slotBase)} : Edge)
  let block : Cfg.Block := {params, body := acc.reverse, term := .switch x edges fallback}
  let targetBlock : Cfg.Block := {
    params := []
    body := spine (skeleton P.base.size supply body F.ctors slotBase)
    term := terminal }
  refine ⟨fd, block, edges, fallback, {target := label}, targetBlock, lookup, ?_, cursor, rfl,
    choice, rfl, rfl, ?_, rfl, ?_⟩
  · cases default <;>
      simpa only [Cfg.Fun.block?, Cfg.Proof.caseTerm, skeletonOpt, edges, fallback, block,
        Option.map_none, Option.map_some] using layout.1
  · simpa only [Cfg.Fun.block?, List.reverse_nil, List.nil_append] using targetLookup
  · exact ⟨fd, scope, [], [], label+1, supply, lo, slotBase, lookup, range, bodyLayout, rfl,
      env, below, loSlot, slotSub, bodyNames, bodyVb, bodyRc, joins⟩



end IxCC.Cfg.Rc.Native
