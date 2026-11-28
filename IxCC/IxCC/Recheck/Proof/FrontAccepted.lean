import IxCC.Src.Relevance.Proof.P1.Defs
import IxCC.Recheck.Proof.Parts
import IxCC.Recheck.Proof.Front
import IxCC.Lam.Erase.Proof.ProgWF

/-! # P1's consumption: what the front end's acceptance gives

Two facts the narrowing of `Recheck.sound`'s escape (`Front.GoesWrongLive`, `Recheck.Proof.LiveDefs`)
reads off a run `Recheck.run` accepts:

* `front_accepted`: the front end ran both relevance checks on the installed program
  (`Relevance.check`, then `Relevance.checkCanonical` with no error), and the program it hands on,
  the one SrcEval runs, is that program's Lazify image;
* `shapeOk_of_run`: that program has one constructor per inductive and index (`P1.ShapeOk`), from
  erasure's success on it (`Erase.Proof.erase_progWF`, `ProgWF.ctorIn`): the one structural fact P1
  assumes that no check of the front end decides. -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Src.Relevance.Proof.P1

/-- The front end's acceptance: both checks on the installed program, whose Lazify image is the
program SrcEval runs. -/
theorem front_accepted {cfg : Config} {P : Src.Program} {c : Cert} {src : Src.Program}
    {ch : Src.Relevance.Checked} (h : front cfg P c = .ok (src, ch)) :
    ∃ installed, Src.Relevance.check installed c.relevance = .ok ch ∧
      Src.Relevance.checkCanonical installed c.relevance ch = [] ∧
      src = Src.Lazify.run installed ch.keys := by
  unfold front at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hm : checkMidCert c.mid with
  | error e => simp [hm] at h
  | ok u =>
    simp only [hm] at h
    cases htab : Src.Table.ofCert cfg.table P c.table with
    | error e => simp [htab] at h
    | ok table =>
      simp only [htab] at h
      have hkeys : checkRelevanceKeys P c.relevance = .ok () := by
        cases hk : checkRelevanceKeys P c.relevance with
        | error e => simp [hk] at h
        | ok u => cases u; rfl
      simp only [hkeys] at h
      cases hann : Src.Recheck.annotation { P with table } c.relevance with
      | error err =>
        rw [hann] at h
        cases err <;> cases h
      | ok res =>
        rw [hann] at h
        cases h
        unfold Src.Recheck.annotation at hann
        cases hinst : Src.Relevance.install { P with table } c.relevance with
        | error e => simp [hinst] at hann
        | ok installed =>
          simp only [hinst] at hann
          cases hchk : Src.Relevance.check installed c.relevance with
          | error errs =>
            rw [hchk] at hann
            cases hann
          | ok chk =>
            rw [hchk] at hann
            dsimp only at hann
            split at hann
            · cases hann
            · rename_i hne
              cases hann
              refine ⟨installed, hchk, ?_, rfl⟩
              simpa using hne

/-- `ShapeOk` under `Recheck.run`'s acceptance: `Recheck.run` erases the program SrcEval runs
(`runLir`, `run_parts`), and a successful erasure has `ProgWF.ctorIn` (`erase_progWF`). -/
theorem shapeOk_of_run {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (h : run cfg P c = .ok a) : ShapeOk a.src := by
  obtain ⟨-, ⟨st, he⟩, -⟩ := runLir_spec (run_parts h).1
  have hwf := Lam.Erase.Proof.erase_progWF he
  refine ⟨fun c c' sf sf' lv lv' ind j np np' nf nf' ty ty' hc hc' => ?_⟩
  have h1 := hwf.ctorIn (c := c) (sf := sf) (lv := lv) (ind := ind) (cidx := j) (np := np) (nf := nf)
    (ty := ty) hc
  have h2 := hwf.ctorIn (c := c') (sf := sf') (lv := lv') (ind := ind) (cidx := j) (np := np')
    (nf := nf') (ty := ty') hc'
  exact Option.some.inj (h1.symm.trans h2)

end IxCC.Recheck
