import IxVMRefinement.Assembly.DefinitionLoop

/-! # Replaying every record with generated reader state removed -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.Cert.ReaderUnits (RolesKeyed)

theorem readRecordBare_muts_noInd (cx : Ctx md) (st : State md) (owner : _root_.Address)
    (c : Ixon.Constant) (ms : Array Ixon.MutConst) (hinfo : c.info = .muts ms)
    (hinds : ms.any (fun | .indc _ => true | _ => false) = false) :
    readRecordBare cx st owner c = readRecord cx st owner c := by
  unfold readRecordBare
  rw [hinfo]
  dsimp only
  split
  · rename_i hind
    have hbad : false = true := hinds.symm.trans hind
    cases hbad
  · rfl

theorem readRecordBare_independent_state (cx : Ctx md) (source target : State md)
    (owner : _root_.Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst)
    (hinfo : c.info = .muts ms)
    (hinds : ms.any (fun | .indc _ => true | _ => false) = true) :
    readRecordBare cx target owner c = readRecordBare cx source owner c := by
  unfold readRecordBare
  rw [hinfo]
  dsimp only
  split
  · rfl
  · rename_i hind
    exact (hind hinds).elim

private theorem readRecord_muts_recs_state (cx : Ctx md) (source target : State md)
    (owner : _root_.Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst)
    (hinfo : c.info = .muts ms)
    (hinds : ms.any (fun | .indc _ => true | _ => false) = false)
    (hrecs : ms.all (fun | .recr _ => true | _ => false) = true) :
    readRecord cx target owner c = readRecord cx source owner c := by
  unfold readRecord
  rw [hinfo]
  dsimp only
  split
  · rename_i hind
    have hbad : false = true := hinds.symm.trans hind
    cases hbad
  · split
    · rfl
    · rename_i hrec
      exact (hrec hrecs).elim

theorem readRecord_noInd_without_rewrite {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source target : State md} {owner : _root_.Address} {c : Ixon.Constant} {full : Read md}
    (hno : ∀ ms, c.info = .muts ms → ms.any (fun | .indc _ => true | _ => false) = false)
    (h : readRecord cx source owner c = .ok full) (hzero : full.projRewrites = 0)
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none) :
    readRecordBare cx target owner c = .ok full := by
  cases hinfo : c.info with
  | defn defn => exact readRecord_defn_without_rewrite hrk hinfo h hzero hh hempty
  | muts ms =>
    have hinds := hno ms hinfo
    rw [readRecordBare_muts_noInd cx target owner c ms hinfo hinds]
    have hread := h
    unfold readRecord at hread
    simp only [hinfo] at hread
    rcases Ix.Cert.CtxAgree.ite_ok' hread with ⟨hind, _⟩ | ⟨_, hread⟩
    · have hbad : false = true := hinds.symm.trans hind
      cases hbad
    · rcases Ix.Cert.CtxAgree.ite_ok' hread with ⟨hrecs, _⟩ | ⟨hrecs, hread⟩
      · rw [readRecord_muts_recs_state cx source target owner c ms hinfo hinds hrecs]
        exact h
      · rcases Ix.Cert.CtxAgree.ite_ok' hread with ⟨hdefs, hread⟩ | ⟨_, hread⟩
        · split at hread
          · exact (Ix.Cert.ReaderUnits.fail_bind hread).elim
          · rename_i hsafe
            have hsafe' : (ms.filterMap (fun | .defn d => some d | _ => none)).findSome?
                safetyDecline = none := by
              cases hs : (ms.filterMap (fun | .defn d => some d | _ => none)).findSome?
                  safetyDecline with
              | none => rfl
              | some reason => exact (hsafe reason hs).elim
            split at hread
            · rename_i order horder
              have hsource := readRecord_mutDefns_eq cx source owner c ms _ order hinfo hinds
                (Bool.eq_false_iff.mpr hrecs) hdefs rfl hsafe' horder
              have htarget := readRecord_mutDefns_eq cx target owner c ms _ order hinfo hinds
                (Bool.eq_false_iff.mpr hrecs) hdefs rfl hsafe' horder
              rw [htarget]
              exact readDefinitionBlock_without_rewrite hrk (hsource.symm.trans h) hzero hh hempty
            · exact (Ix.Cert.ReaderUnits.throw_ok hread).elim
        · exact (Ix.Cert.ReaderUnits.throw_ok hread).elim
  | _ => simpa only [readRecordBare, hinfo, readRecord] using h

/-- A successful full record with zero projection rewrites can be read in a bare state
with the same public heights. The returned declaration array omits only its generated prefix. -/
theorem readRecord_full_bare_replay {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {source target : State md} {owner : _root_.Address} {c : Ixon.Constant} {full : Read md}
    (h : readRecord cx source owner c = .ok full) (hzero : full.projRewrites = 0)
    (hh : ∀ (k : CName md), NonAuxKey k → target.heights[k]? = source.heights[k]?)
    (hempty : ∀ (k : CName md), target.projLevels[k]? = none) :
    ∃ (generated : List (CDecl md)) (bare : Read md),
      readRecordBare cx target owner c = .ok bare ∧
      full.decls.toList = generated ++ bare.decls.toList ∧
      full.generated = generated.length ∧ bare.generated = 0 ∧
      (∀ d ∈ generated, d.isGenerated = true) := by
  have same (hno : ∀ ms, c.info = .muts ms →
      ms.any (fun | .indc _ => true | _ => false) = false) :
      ∃ (generated : List (CDecl md)) (bare : Read md),
        readRecordBare cx target owner c = .ok bare ∧
        full.decls.toList = generated ++ bare.decls.toList ∧
        full.generated = generated.length ∧ bare.generated = 0 ∧
        (∀ d ∈ generated, d.isGenerated = true) := by
    have hbare := readRecord_noInd_without_rewrite hrk hno h hzero hh hempty
    have hgen := readRecordBare_generated_zero hbare
    exact ⟨[], full, hbare, by simp, hgen, hgen, by simp⟩
  cases hinfo : c.info with
  | muts ms =>
    by_cases hinds : ms.any (fun | .indc _ => true | _ => false) = true
    · obtain ⟨generated, bare, hbare, hdecls, hcount, hgen, hgenerated⟩ := readRecord_full_bare h
      refine ⟨generated, bare, ?_, hdecls, hcount, hgen, hgenerated⟩
      rw [readRecordBare_independent_state cx source target owner c ms hinfo hinds]
      exact hbare
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
