import IxVMRefinement.Assembly.ReadBare

/-! # Relating full and bare inductive lowerings

Both lowerings check the same block header. The full lowering additionally generates model
declarations; its bare counterpart retains the family's own declaration and the same distinct
public names.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel
open Ix.Kernel.Reader

theorem lowerInductiveDeclsBare_of_full {md : Mode} {st : State md}
    {rb : BlockRead md} {r : Read md}
    (h : lowerInductiveDecls st rb = .ok r) :
    ∃ bare, lowerInductiveDeclsBare rb = .ok bare := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  unfold lowerInductiveDecls at h
  unfold lowerInductiveDeclsBare
  simp only [ite_not, bne_iff_ne, ne_eq] at h ⊢
  rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hc, h⟩ | ⟨hc, h⟩
  all_goals
    simp only [hc, ↓reduceIte]
    obtain ⟨result, hloop, _⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    rw [hloop]
    exact ⟨_, rfl⟩

/-- Every successful full inductive lowering has a successful bare lowering. Its actual
generated prefix is kept separate from the bare declaration array. -/
theorem lowerInductive_full_bare {md : Mode} {st : State md}
    {rb : BlockRead md} {full : Read md}
    (h : lowerInductive st rb = .ok full) :
    ∃ (generated : List (Declaration md)) (bare : Read md),
      lowerInductiveBare rb = .ok bare ∧
      full.decls.toList = generated ++ bare.decls.toList ∧
      full.generated = generated.length ∧
      bare.generated = 0 ∧
      (∀ d ∈ generated, d.isGenerated = true) := by
  obtain ⟨generated, hdecls, hcount, _, _⟩ := Ix.Cert.CtxAgree.lowerInductive_ok h
  obtain ⟨bare, hbare⟩ := lowerInductiveDeclsBare_of_full
    (Ix.Cert.LowerDistinct.lowerInductiveDecls_of_ok h)
  obtain ⟨hzero, hbare_decls⟩ := lowerInductiveDeclsBare_spec hbare
  have hbare_eq : bare.decls = #[Ix.Cert.CtxAgree.indDeclOf rb] := hbare_decls
  have hnames := Ix.Cert.LowerDistinct.lowerInductive_names_nodup h
  rw [hdecls] at hnames
  simp only [Array.toList_push, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nodup_append] at hnames
  have hbare_names : (bare.decls.toList.flatMap Declaration.names).Nodup := by
    rw [hbare_eq]
    simpa using hnames.2.1
  have hdistinct := Ix.Cert.LowerDistinct.firstRepeatedKey_eq_none_iff.mpr hbare_names
  have hbare_run : lowerInductiveBare rb = .ok bare := by
    unfold lowerInductiveBare
    rw [hbare]
    simp only [bind, Except.bind, hdistinct, pure, Except.pure]
  refine ⟨generated, bare, hbare_run, ?_, hcount, hzero, ?_⟩
  · rw [hdecls, hbare_eq]
    simp
  · intro d hd
    apply Ix.Cert.SourceNames.lowerInductive_generated h d
    rw [hdecls, hcount]
    simpa using hd

/-- The full inductive record reader and its bare counterpart share the same expression
conversion. Removing generation preserves success and separates the generated prefix. -/
theorem readInductive_full_bare {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    {full : Read md} (h : readInductive cx st owner c ms = .ok full) :
    ∃ (generated : List (Declaration md)) (bare : Read md),
      readInductiveBare cx owner c ms = .ok bare ∧
      full.decls.toList = generated ++ bare.decls.toList ∧
      full.generated = generated.length ∧ bare.generated = 0 ∧
      (∀ d ∈ generated, d.isGenerated = true) := by
  unfold readInductive at h
  unfold readInductiveBare
  split at h
  · dsimp only at h ⊢
    rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hsize, h⟩ | ⟨hsize, h⟩
    · simp only [hsize, ↓reduceIte]
      split at h
      · rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hsafe, h⟩ | ⟨hsafe, h⟩
        · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
        · simp only [hsafe]
          rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hparams, h⟩ | ⟨hparams, h⟩
          · simp only [hparams, ↓reduceIte]
            obtain ⟨types, htypes, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            rw [htypes]
            dsimp only [bind, Except.bind] at h ⊢
            obtain ⟨ctors, hctors, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            rw [hctors]
            dsimp only [bind, Except.bind] at h ⊢
            obtain ⟨recs, hrecs, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            rw [hrecs]
            dsimp only [bind, Except.bind]
            exact lowerInductive_full_bare h
          · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
      · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
    · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
  · exact (Ix.Cert.ReaderUnits.throw_ok h).elim

/-- Appending the same checked twin payloads preserves the full-to-bare declaration split. -/
theorem finishInductiveRead_full_bare {md : Mode} {cx : Ctx md}
    {owner : _root_.Address} {ms : Array Ixon.MutConst}
    {fullInd bareInd full : Read md} {generated : List (Declaration md)}
    (h : finishInductiveRead cx owner ms fullInd = .ok full)
    (hdecls : fullInd.decls.toList = generated ++ bareInd.decls.toList)
    (hcount : fullInd.generated = generated.length) (hzero : bareInd.generated = 0) :
    ∃ bare, finishInductiveRead cx owner ms bareInd = .ok bare ∧
      full.decls.toList = generated ++ bare.decls.toList ∧
      full.generated = generated.length ∧ bare.generated = 0 := by
  unfold finishInductiveRead at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hempty
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst full
    exact ⟨bareInd, by simp [hempty, pure, Except.pure], hdecls, hcount, hzero⟩
  · rename_i hnonempty
    obtain ⟨rTwin, hTwin, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst full
    refine ⟨{ bareInd with decls := bareInd.decls ++ rTwin.decls }, ?_, ?_, hcount, hzero⟩
    · simp [hnonempty, hTwin, bind, Except.bind, pure, Except.pure]
    · simp only [Array.toList_append, hdecls, List.append_assoc]

/-- A successful full record read has a concrete bare read at the same context and state.
Its generated prefix is removed, and same-record twins remain in both declaration arrays. -/
theorem readRecord_full_bare {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {full : Read md}
    (h : readRecord cx st owner c = .ok full) :
    ∃ (generated : List (Declaration md)) (bare : Read md),
      readRecordBare cx st owner c = .ok bare ∧
      full.decls.toList = generated ++ bare.decls.toList ∧
      full.generated = generated.length ∧ bare.generated = 0 ∧
      (∀ d ∈ generated, d.isGenerated = true) := by
  have same (hbare : readRecordBare cx st owner c = .ok full) :
      ∃ (generated : List (Declaration md)) (bare : Read md),
        readRecordBare cx st owner c = .ok bare ∧
        full.decls.toList = generated ++ bare.decls.toList ∧
        full.generated = generated.length ∧ bare.generated = 0 ∧
        (∀ d ∈ generated, d.isGenerated = true) := by
    have hzero := readRecordBare_generated_zero hbare
    exact ⟨[], full, hbare, by simp, hzero, hzero, by simp⟩
  cases hinfo : c.info with
  | muts ms =>
    by_cases hind : ms.any (fun | .indc _ => true | _ => false) = true
    · unfold readRecord at h
      simp only [hinfo, hind, ↓reduceIte] at h
      rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hdefs, h⟩ | ⟨hdefs, h⟩
      · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
      · obtain ⟨fullInd, hInd, hfinish⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
        obtain ⟨generated, bareInd, hbareInd, hdecls, hcount, hzero, hgenerated⟩ :=
          readInductive_full_bare hInd
        obtain ⟨bare, hbare, hdecls', hcount', hzero'⟩ :=
          finishInductiveRead_full_bare hfinish hdecls hcount hzero
        refine ⟨generated, bare, ?_, hdecls', hcount', hzero', hgenerated⟩
        simp only [readRecordBare, hinfo, hind, hdefs, ↓reduceIte, hbareInd,
          bind, Except.bind]
        exact hbare
    · apply same
      simpa only [readRecordBare, hinfo, hind, ↓reduceIte] using h
  | _ =>
    apply same
    simpa only [readRecordBare, hinfo] using h

end IxVM.Refinement.Assembly
