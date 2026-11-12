import Ix.CompileM
import IxC.Ixon.Verify.WireCheck
import IxSharingVerify.Builder

/-! # A built record with its binder data

The compiler gives a block record its binder-data section after the canonical
sharing built it (`Ix.CompileM.withBinderSection`): the record is the built one
with an admissible section (`Sectioned`), so every other field is the built
record's, definitionally. This module transfers what the certification knows of
the built record to the record with its section: it is in the wire domain when
the built one is, its section is canonical and complete, and without its
section it is the built record. -/

namespace Ix.CompileCert.Sectioned

open Ix.CompileM

/-- `c` is `c₀` with a section the compiler admits. -/
def Sectioned (c₀ c : Ixon.Constant) : Prop :=
  ∃ binders, sectionAdmissible c₀ binders = true ∧ c = { c₀ with binders }

theorem of_withBinderSection {annotator? : Option Ix.BinderAnnotator} {names : Array Ix.Name}
    {c₀ c : Ixon.Constant} (h : withBinderSection annotator? names c₀ = .ok c) : Sectioned c₀ c :=
  withBinderSection_ok h

/-- An admitted section is in the wire domain. -/
theorem validBinders_wire {binders : Array Ixon.BinderBlock}
    (h : Ixon.WireCheck.validArray binders Ixon.WireCheck.validBinderBlock = true) :
    Ixon.bindersWireWF binders := by
  simpa [Ixon.bindersWireWF, Ixon.WireCheck.validArray, -Array.all_eq_true, Array.all_eq_true']
    using h

theorem wireWF {c₀ c : Ixon.Constant} (h : Sectioned c₀ c) (wire : c₀.wireWF) : c.wireWF := by
  obtain ⟨binders, ok, rfl⟩ := h
  exact ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1, wire.2.2.2.2.2.1,
    wire.2.2.2.2.2.2.1, validBinders_wire (sectionAdmissible_wire ok)⟩

theorem canonical {c₀ c : Ixon.Constant} (h : Sectioned c₀ c) : c.bindersCanonical = true := by
  obtain ⟨binders, ok, rfl⟩ := h
  exact sectionAdmissible_canonical ok

theorem complete {c₀ c : Ixon.Constant} (h : Sectioned c₀ c) : c.bindersComplete = true := by
  obtain ⟨binders, ok, rfl⟩ := h
  exact sectionAdmissible_complete ok

/-- A record with a root whose section is canonical has fewer than
`Ixon.maxLevelCount` (`2^32`) universe parameters. -/
theorem levels_of_canonical {c : Ixon.Constant} (h : c.bindersCanonical = true)
    (rooted : c.info.binderRoots.isEmpty = false) : c.info.maxLvls < Ixon.maxLevelCount := by
  unfold Ixon.Constant.bindersCanonical at h
  rw [rooted] at h
  cases hd : decide (c.info.maxLvls < Ixon.maxLevelCount)
  · rw [hd] at h
    simp at h
  · exact of_decide_eq_true hd

/-- **The compiler's records are below the level-count bound**: a record built
with an admitted section, with a root, has fewer than `Ixon.maxLevelCount`
universe parameters, so the compiler refuses a declaration with more
(`Ix.CompileM.sectionFor` admits no section for it). -/
theorem levels {c₀ c : Ixon.Constant} (h : Sectioned c₀ c)
    (rooted : c.info.binderRoots.isEmpty = false) : c.info.maxLvls < Ixon.maxLevelCount :=
  levels_of_canonical (canonical h) rooted

/-- Without its section, the record is the built one (which has none). -/
theorem strip {c₀ c : Ixon.Constant} (h : Sectioned c₀ c) (empty : c₀.binders = #[]) :
    { c with binders := #[] } = c₀ := by
  obtain ⟨binders, -, rfl⟩ := h
  cases c₀
  simp only at empty
  subst empty
  rfl

/-- The canonical sharing builds a record without binder data. -/
theorem built_binders {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo}
    {refs : Array Address} {univs : Array Ixon.Univ} {c : Ixon.Constant}
    (h : buildConstantWithSharing limits info refs univs = .ok c) : c.binders = #[] := by
  obtain ⟨_, _, _, _, _, rfl⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok h
  rfl

/-- A built record with its section, without the section, is what the sharing built. -/
theorem built_strip {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo}
    {refs : Array Address} {univs : Array Ixon.Univ} {c₀ c : Ixon.Constant}
    (h : buildConstantWithSharing limits info refs univs = .ok c₀) (s : Sectioned c₀ c) :
    buildConstantWithSharing limits info refs univs = .ok { c with binders := #[] } := by
  rw [strip s (built_binders h)]
  exact h

/-- **A build followed by its section**, as the compiler's mutual builder runs
them: the sharing built the record without its section, and the section is an
admitted one. -/
theorem bind_sectioned {β : Type} {limits : Ix.Sharing.Exact.Limits} {info : Ixon.ConstantInfo}
    {refs : Array Address} {univs : Array Ixon.Univ} {annotator? : Option Ix.BinderAnnotator}
    {names : Array Ix.Name} {f : Ixon.Constant → Except CompileError β} {y : β}
    (h : (buildConstantWithSharing limits info refs univs >>= fun built =>
      withBinderSection annotator? names built >>= f) = .ok y) :
    ∃ block, buildConstantWithSharing limits info refs univs = .ok { block with binders := #[] } ∧
      Sectioned { block with binders := #[] } block ∧ f block = .ok y := by
  obtain ⟨built, hb, rest⟩ := Ix.Sharing.Verify.except_bind_eq_ok h
  obtain ⟨block, hsec, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok rest
  have sec := of_withBinderSection hsec
  have strip' := strip sec (built_binders hb)
  refine ⟨block, by rw [strip']; exact hb, by rw [strip']; exact sec, returned⟩

/-- A record with no root, such as a projection, with the empty section is
canonical and complete. -/
theorem empty_of_rootless {c : Ixon.Constant} (roots : c.info.binderRoots = #[])
    (empty : c.binders = #[]) : c.bindersCanonical = true ∧ c.bindersComplete = true := by
  have rootless : c.info.binderRoots.isEmpty = true := by rw [roots]; rfl
  constructor
  · unfold Ixon.Constant.bindersCanonical
    rw [rootless, empty]
    all_goals rfl
  · unfold Ixon.Constant.bindersComplete
    rw [rootless, empty]
    all_goals rfl

end Ix.CompileCert.Sectioned
