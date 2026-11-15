import IxVMRefinement.Assembly.RecordState

/-! # Reader side data is preserved when generated declarations are omitted -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (RolesKeyed ite_ok fail_bind throw_ok)

private theorem lowerInductiveDeclsBare_sides {md : Mode} {rb : BlockRead md} {r : Read md}
    (h : lowerInductiveDeclsBare rb = .ok r) :
    r.owners = Ix.Cert.CtxAgree.ownersOf rb ∧ r.blocks = Ix.Cert.CtxAgree.blocksOf rb := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  unfold lowerInductiveDeclsBare at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  split at h
  all_goals
    rcases ite_ok h with h | h
    all_goals obtain ⟨_, _, h⟩ := except_bind_ok.mp h
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst r
      exact ⟨rfl, rfl⟩

private theorem lowerInductiveBare_sides {md : Mode} {rb : BlockRead md} {r : Read md}
    (h : lowerInductiveBare rb = .ok r) :
    r.owners = Ix.Cert.CtxAgree.ownersOf rb ∧ r.blocks = Ix.Cert.CtxAgree.blocksOf rb := by
  unfold lowerInductiveBare at h
  obtain ⟨initial, hinitial, h⟩ := except_bind_ok.mp h
  cases hk : firstRepeatedKey (initial.decls.toList.flatMap Declaration.names) with
  | some k => simp [hk, declined, throw, throwThe, MonadExceptOf.throw] at h
  | none =>
    simp only [hk, pure, Except.pure, Except.ok.injEq] at h
    subst r
    exact lowerInductiveDeclsBare_sides hinitial

private theorem lowerInductive_bare_sides {md : Mode} {st : State md}
    {rb : BlockRead md} {full : Read md} (h : lowerInductive st rb = .ok full) :
    ∃ bare, lowerInductiveBare rb = .ok bare ∧
      bare.owners = full.owners ∧ bare.blocks = full.blocks := by
  obtain ⟨_, bare, hbare, _, _, _, _⟩ := lowerInductive_full_bare h
  obtain ⟨_, _, _, hblocks, _⟩ := Ix.Cert.CtxAgree.lowerInductive_ok h
  have howners := Ix.Cert.CtxAgree.lowerInductive_owners h
  obtain ⟨hbareOwners, hbareBlocks⟩ := lowerInductiveBare_sides hbare
  exact ⟨bare, hbare, hbareOwners.trans howners.symm, hbareBlocks.trans hblocks.symm⟩

theorem readInductive_bare_sides {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    {full : Read md} (h : readInductive cx st owner c ms = .ok full) :
    ∃ bare, readInductiveBare cx owner c ms = .ok bare ∧
      bare.owners = full.owners ∧ bare.blocks = full.blocks := by
  unfold readInductive at h
  unfold readInductiveBare
  split at h
  · dsimp only at h ⊢
    rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hsize, h⟩ | ⟨hsize, h⟩
    · simp only [hsize, ↓reduceIte]
      split at h
      · rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hsafe, h⟩ | ⟨hsafe, h⟩
        · exact (fail_bind h).elim
        · simp only [hsafe]
          rcases Ix.Cert.CtxAgree.ite_ok' h with ⟨hparams, h⟩ | ⟨hparams, h⟩
          · simp only [hparams, ↓reduceIte]
            obtain ⟨types, htypes, h⟩ := except_bind_ok.mp h
            rw [htypes]
            dsimp only [bind, Except.bind] at h ⊢
            obtain ⟨ctors, hctors, h⟩ := except_bind_ok.mp h
            rw [hctors]
            dsimp only [bind, Except.bind] at h ⊢
            obtain ⟨recs, hrecs, h⟩ := except_bind_ok.mp h
            rw [hrecs]
            dsimp only [bind, Except.bind]
            exact lowerInductive_bare_sides h
          · exact (fail_bind h).elim
      · exact (throw_ok h).elim
    · exact (fail_bind h).elim
  · exact (throw_ok h).elim

theorem readRecord_inductive_bare_sides {md : Mode} {cx : Ctx md} {source target : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hinfo : c.info = .muts ms)
    (hinds : ms.any (fun | .indc _ => true | _ => false) = true)
    {full bare : Read md} (hfull : readRecord cx source owner c = .ok full)
    (hbare : readRecordBare cx target owner c = .ok bare) :
    bare.owners = full.owners ∧ bare.blocks = full.blocks := by
  unfold readRecord at hfull
  simp only [hinfo] at hfull
  rcases Ix.Cert.CtxAgree.ite_ok' hfull with ⟨_, hfull⟩ | ⟨hind, _⟩
  · rcases ite_ok hfull with hfull | hfull
    · exact (fail_bind hfull).elim
    · obtain ⟨fullInd, hInd, hfinish⟩ := except_bind_ok.mp hfull
      obtain ⟨bareInd, hbareInd, howners, hblocks⟩ := readInductive_bare_sides hInd
      unfold readRecordBare at hbare
      simp only [hinfo] at hbare
      rcases Ix.Cert.CtxAgree.ite_ok' hbare with ⟨_, hbare⟩ | ⟨hind, _⟩
      · rcases ite_ok hbare with hbare | hbare
        · exact (fail_bind hbare).elim
        · obtain ⟨actualInd, hactualInd, hfinishBare⟩ := except_bind_ok.mp hbare
          have heq := Except.ok.inj (hactualInd.symm.trans hbareInd)
          subst actualInd
          obtain ⟨_, _, hfullOwners, hfullBlocks⟩ := finishInductiveRead_data hfinish
          obtain ⟨_, _, hbareOwners, hbareBlocks⟩ := finishInductiveRead_data hfinishBare
          exact ⟨hbareOwners.trans (howners.trans hfullOwners.symm),
            hbareBlocks.trans (hblocks.trans hfullBlocks.symm)⟩
      · exact (hind hinds).elim
  · exact (hind hinds).elim

theorem readRecord_full_bare_replay_sides {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source target : State md} {owner : _root_.Address} {c : Ixon.Constant} {full : Read md}
    (h : readRecord cx source owner c = .ok full) (hzero : full.projRewrites = 0)
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none) :
    ∃ (generated : List (CDecl md)) (bare : Read md),
      readRecordBare cx target owner c = .ok bare ∧
      full.decls.toList = generated ++ bare.decls.toList ∧
      full.generated = generated.length ∧ bare.generated = 0 ∧
      (∀ d ∈ generated, d.isGenerated = true) ∧
      bare.owners = full.owners ∧ bare.blocks = full.blocks := by
  obtain ⟨generated, bare, hbare, hdecls, hcount, hgen, hgenerated⟩ :=
    readRecord_full_bare_replay hrk h hzero hh hempty
  refine ⟨generated, bare, hbare, hdecls, hcount, hgen, hgenerated, ?_⟩
  have same (hno : ∀ ms, c.info = .muts ms →
      ms.any (fun | .indc _ => true | _ => false) = false) :
      bare.owners = full.owners ∧ bare.blocks = full.blocks := by
    have hfullBare := readRecord_noInd_without_rewrite hrk hno h hzero hh hempty
    have heq := Except.ok.inj (hbare.symm.trans hfullBare)
    subst bare
    exact ⟨rfl, rfl⟩
  cases hinfo : c.info with
  | muts ms =>
    by_cases hinds : ms.any (fun | .indc _ => true | _ => false) = true
    · exact readRecord_inductive_bare_sides hinfo hinds h hbare
    · apply same
      intro ms' hinfo'
      have heq := hinfo.symm.trans hinfo'
      cases heq
      exact Bool.eq_false_iff.mpr hinds
  | _ =>
    apply same
    intro ms hms
    rw [hinfo] at hms
    cases hms

end IxVM.Refinement.Assembly
