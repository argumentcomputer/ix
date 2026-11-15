import IxVMRefinement.Assembly.StreamState
import Ix.Cert.SourceInstalls

/-! # The actual public declaration closing a generated reader prefix -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (RolesKeyed)

/-- Pinned and unpinned inductive declarations both install all the names they declare. -/
theorem indDecl_names_installs (block : List (ConstantInfo .anon)) (nP : Nat) :
    (Declaration.indDecl block nP).names =
      (IxVM.Consistency.installs (.indDecl block nP)).map (·.name) := by
  simp only [Declaration.names, IxVM.Consistency.installs]
  cases hpin : basisPinHit block with
  | none => rfl
  | some kind =>
    rw [Ix.Cert.SourceInstalls.declsA_names, ← Ix.Cert.SourceInstalls.basisPinHit_names hpin]

theorem readRecord_suffix_nonAux {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {st : State md} {owner : _root_.Address} {c : Ixon.Constant} {r : Read md}
    (h : readRecord cx st owner c = .ok r) :
    ∀ d ∈ r.decls.toList.drop r.generated, ∀ k ∈ d.names, NonAuxKey k := by
  intro d hd k hk
  rcases Ix.Cert.ReaderUnits.readRecord_lowering h with ⟨hzero, hnames⟩ |
      ⟨generated, suffix, hdecls, hcount, _, hnames⟩
  · rw [hzero, List.drop_zero] at hd
    exact isAux_eq_false_iff.mp ((hnames d hd k hk).not_derived hrk)
  · rw [hdecls, hcount, List.drop_left] at hd
    exact isAux_eq_false_iff.mp ((hnames d hd k hk).not_derived hrk)

private theorem readRecord_inductive_layout {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hinfo : c.info = .muts ms)
    (hinds : ms.any (fun | .indc _ => true | _ => false) = true)
    {r : Read md} (h : readRecord cx st owner c = .ok r) :
    ∃ generated block nP tail,
      r.decls.toList = generated ++ (.indDecl block nP :: tail) ∧ r.generated = generated.length := by
  unfold readRecord at h
  simp only [hinfo] at h
  rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨_, h⟩ | ⟨hind, _⟩
  · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
    · obtain ⟨ind, hind, hfinish⟩ := except_bind_ok.mp h
      obtain ⟨lowerState, blockRead, hlower⟩ := Ix.Cert.EvidenceTransfer.readInductive_lower hind
      obtain ⟨generated, hdecls, hcount, _, _⟩ := Ix.Cert.CtxAgree.lowerInductive_ok hlower
      have hlist : ind.decls.toList = generated ++ [Ix.Cert.CtxAgree.indDeclOf blockRead] := by
        rw [hdecls]
        simp
      obtain ⟨block, nP, hshape⟩ :
          ∃ block nP, Ix.Cert.CtxAgree.indDeclOf blockRead = .indDecl block nP := ⟨_, _, rfl⟩
      rw [hshape] at hlist
      rcases finishInductiveRead_spec hfinish with rfl | ⟨twins, _, rfl⟩
      · exact ⟨generated, block, nP, [], hlist, hcount⟩
      · exact ⟨generated, block, nP, twins.decls.toList,
          by simpa only [Array.toList_append, hlist, List.append_assoc, List.singleton_append], hcount⟩
  · exact (hind hinds).elim

/-- An actual record that generates declarations closes that prefix with its inductive
family declaration. Its following declarations, including same-record twins, are not generated. -/
theorem readRecord_generated_closer {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {st : State md} {owner : _root_.Address} {c : Ixon.Constant} {r : Read md}
    (h : readRecord cx st owner c = .ok r) (hpositive : r.generated ≠ 0) :
    ∃ generated block nP tail,
      generated ≠ [] ∧ r.decls.toList = generated ++ (.indDecl block nP :: tail) ∧
      r.generated = generated.length ∧
      (∀ d ∈ generated, d.isGenerated = true) ∧
      (∀ k ∈ (Declaration.indDecl block nP).names, NonAuxKey k) ∧
      (∀ d ∈ (.indDecl block nP :: tail), d.isGenerated = false) := by
  have impossible (hbare : readRecordBare cx st owner c = .ok r) : False :=
    hpositive (readRecordBare_generated_zero hbare)
  have layout : ∃ generated block nP tail,
      r.decls.toList = generated ++ (.indDecl block nP :: tail) ∧ r.generated = generated.length := by
    cases hinfo : c.info with
    | muts ms =>
      by_cases hinds : ms.any (fun | .indc _ => true | _ => false) = true
      · exact readRecord_inductive_layout hinfo hinds h
      · apply False.elim
        apply impossible
        rw [readRecordBare_muts_noInd cx st owner c ms hinfo (Bool.eq_false_iff.mpr hinds)]
        exact h
    | _ => exact (impossible (by simpa only [readRecordBare, hinfo] using h)).elim
  obtain ⟨generated, block, nP, tail, hdecls, hcount⟩ := layout
  refine ⟨generated, block, nP, tail, ?_, hdecls, hcount, ?_, ?_, ?_⟩
  · intro hempty
    rw [hempty] at hcount
    exact hpositive hcount
  · intro d hd
    apply Ix.Cert.EvidenceTransfer.readRecord_generated h d
    rw [hdecls, hcount, List.take_left]
    exact hd
  · intro k hk
    apply readRecord_suffix_nonAux hrk h (.indDecl block nP) _ k hk
    rw [hdecls, hcount, List.drop_left]
    exact List.mem_cons_self
  · intro d hd
    apply readRecord_suffix_notGenerated hrk h d
    rw [hdecls, hcount, List.drop_left]
    exact hd

end IxVM.Refinement.Assembly
