import IxSharingVerify.FamilyEncoding

/-! Constant congruence and conditional idempotence for the actual family
normalizer. Ordered semantic roots and unchanged headers/tables are the
inputs; equal canonical DAGs are derived, never assumed at this boundary. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.CanonicalMeaning (SharingMeaning)
open Ix.Sharing.Verify.Tiered (encodingOf)
open Ix.CompileCert.SharingRoots (erase eraseMut)

theorem mapMutConstRoots_count (f : Ixon.Expr → Ixon.Expr) (member : Ixon.MutConst) :
    (mutConstRoots (mapMutConstRoots f member)).length = (mutConstRoots member).length := by
  cases member <;> simp [mapMutConstRoots, mutConstRoots]

theorem erase_root_count (info : Ixon.ConstantInfo) :
    (constantInfoRoots (erase info)).size = (constantInfoRoots info).size := by
  cases info with
  | muts members =>
    simp only [erase, mapRoots, constantInfoRoots, List.size_toArray, Array.toList_map,
      List.length_flatMap, List.map_map, Function.comp_def, mapMutConstRoots_count]
  | _ => simp [erase, mapRoots, constantInfoRoots, mutConstRoots]

theorem withMutConstRoots_erase (member : Ixon.MutConst) (roots : List Ixon.Expr) :
    withMutConstRoots (eraseMut member) roots = withMutConstRoots member roots := by
  cases member <;> simp [eraseMut, mapMutConstRoots, withMutConstRoots, Array.toList_map,
    List.zip_map_left, List.map_toArray, List.map_map, Function.comp_def]

/-- Root write-back ignores every old expression root, including constructor
types and recursor-rule bodies, while retaining their headers and order. -/
theorem withRoots_erase (info : Ixon.ConstantInfo) (roots : Array Ixon.Expr) :
    withRoots (erase info) roots = withRoots info roots := by
  unfold withRoots
  rw [erase_root_count]
  cases info with
  | muts members =>
    have member (m : Ixon.MutConst) (rs : List Ixon.Expr) :
        withMutConstRoots (mapMutConstRoots (fun _ => .sort 0) m) rs = withMutConstRoots m rs :=
      withMutConstRoots_erase m rs
    simp only [erase, mapRoots, Array.forIn_map, member]
  | _ => simp [erase, mapRoots, withMutConstRoots, Array.toList_map,
      List.zip_map_left, List.map_toArray, List.map_map, Function.comp_def]

theorem withRoots_same_header {first second : Ixon.ConstantInfo} (same : erase first = erase second)
    (roots : Array Ixon.Expr) : withRoots first roots = withRoots second roots := by
  rw [← withRoots_erase first roots, same, withRoots_erase second roots]

/-- Complete output constants agree from semantic roots and actual unchanged
fields. Canonical DAG/root equality is derived from the two real expansions. -/
theorem normalizeFamily_congr {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {sources : Array Ixon.Expr} {first second left right : Ixon.Constant}
    {leftResult rightResult : TieredSharingResult}
    (firstMeaning : SharingMeaning sources first.sharing (constantInfoRoots first.info))
    (secondMeaning : SharingMeaning sources second.sharing (constantInfoRoots second.info))
    (headers : erase first.info = erase second.info) (refs : first.refs = second.refs)
    (univs : first.univs = second.univs)
    (firstRun : normalizeFamily cfg layout first limits = .ok (left, leftResult))
    (secondRun : normalizeFamily cfg layout second limits = .ok (right, rightResult)) : left = right := by
  obtain ⟨firstExpanded, firstInfo, expanded1, tiered1, written1, output1⟩ := normalizeFamily_parts firstRun
  obtain ⟨secondExpanded, secondInfo, expanded2, tiered2, written2, output2⟩ := normalizeFamily_parts secondRun
  obtain ⟨dag, roots⟩ := expand_same_meaning firstMeaning secondMeaning expanded1 expanded2
  have encoding := familyExpanded_same_encoding dag roots tiered1 tiered2
  have sharing := congrArg (·.1) encoding
  have rootSeq := congrArg (fun e => e.2.1) encoding
  have written := withRoots_same_header headers rightResult.result.roots
  rw [show leftResult.result.roots = rightResult.result.roots from rootSeq] at written1
  rw [written1, written2] at written
  have infoEq := Except.ok.inj written
  rw [output1, output2]
  change Ixon.Constant.mk firstInfo leftResult.result.sharing first.refs first.univs =
    Ixon.Constant.mk secondInfo rightResult.result.sharing second.refs second.univs
  rw [infoEq, show leftResult.result.sharing = rightResult.result.sharing from sharing, refs, univs]

/-- Byte equality follows from equality of the entire output constant;
performance statistics are outside this comparison. -/
theorem normalizeFamily_bytes_congr {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {sources : Array Ixon.Expr} {first second left right : Ixon.Constant}
    {leftResult rightResult : TieredSharingResult}
    (firstMeaning : SharingMeaning sources first.sharing (constantInfoRoots first.info))
    (secondMeaning : SharingMeaning sources second.sharing (constantInfoRoots second.info))
    (headers : erase first.info = erase second.info) (refs : first.refs = second.refs)
    (univs : first.univs = second.univs)
    (firstRun : normalizeFamily cfg layout first limits = .ok (left, leftResult))
    (secondRun : normalizeFamily cfg layout second limits = .ok (right, rightResult)) :
    Ixon.serConstant left = Ixon.serConstant right :=
  congrArg Ixon.serConstant (normalizeFamily_congr firstMeaning secondMeaning headers refs univs firstRun secondRun)

/-- Repeating normalization is idempotent when both runs succeed with the
same cfg/layout/limits. No second-run success or budget independence is assumed silently. -/
theorem normalizeFamily_idempotent {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input middle output : Ixon.Constant} {first second : TieredSharingResult}
    (firstRun : normalizeFamily cfg layout input limits = .ok (middle, first))
    (secondRun : normalizeFamily cfg layout middle limits = .ok (output, second)) : output = middle := by
  obtain ⟨sources, before, after⟩ := normalizeFamily_meaning firstRun
  obtain ⟨refs, univs, _, _, headers⟩ := normalizeFamily_fields firstRun
  exact (normalizeFamily_congr before after headers.symm refs.symm univs.symm firstRun secondRun).symm

theorem normalizeFamily_idempotent_bytes {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input middle output : Ixon.Constant} {first second : TieredSharingResult}
    (firstRun : normalizeFamily cfg layout input limits = .ok (middle, first))
    (secondRun : normalizeFamily cfg layout middle limits = .ok (output, second)) :
    Ixon.serConstant output = Ixon.serConstant middle :=
  congrArg Ixon.serConstant (normalizeFamily_idempotent firstRun secondRun)

/-- Only the second raw expansion must be supplied here. The remaining
pipeline and write-back succeed by the proved transport/header equations. -/
theorem normalizeFamily_repeat_of_expand {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input middle : Ixon.Constant} {first : TieredSharingResult} {expanded : Expanded}
    (firstRun : normalizeFamily cfg layout input limits = .ok (middle, first))
    (secondExpand : expand limits middle.sharing (constantInfoRoots middle.info) true = .ok expanded) :
    ∃ second, normalizeFamily cfg layout middle limits = .ok (middle, second) ∧ encodingOf second = encodingOf first := by
  obtain ⟨original, info, firstExpand, familyRun, written, output⟩ := normalizeFamily_parts firstRun
  obtain ⟨dag, roots⟩ := normalizeFamily_expansion_eq firstRun firstExpand secondExpand
  let second := recordTieredStats expanded.visits expanded.internedNodes first
  have secondFamily : familyExpanded cfg layout limits expanded = .ok second :=
    familyExpanded_transport_success dag roots familyRun
  obtain ⟨_, _, sharing, _, headers⟩ := normalizeFamily_fields firstRun
  have secondWrite : withRoots middle.info second.result.roots = .ok middle.info := by
    change withRoots middle.info first.result.roots = .ok middle.info
    rw [withRoots_same_header headers, written, output]
  refine ⟨second, ?_, rfl⟩
  unfold normalizeFamily
  rw [secondExpand]
  simp only [bind, Except.bind]
  rw [secondFamily]
  dsimp only
  rw [secondWrite]
  simp only [pure, Except.pure]
  change Except.ok ({ middle with info := middle.info, sharing := first.result.sharing }, second) = .ok (middle, second)
  rw [← sharing]

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.withMutConstRoots_erase [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.withRoots_erase [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.withRoots_same_header [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_congr [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_bytes_congr [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_idempotent [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_idempotent_bytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_repeat_of_expand [propext, Classical.choice, Quot.sound]
