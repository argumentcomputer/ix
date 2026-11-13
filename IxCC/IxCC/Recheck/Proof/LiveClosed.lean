import IxCC.Recheck.Proof.Live
import IxCC.Src.Relevance.Proof.P1.Main

/-! # P1's consumption, with P1's root proved

`Front.goesWrong_live` and `sound_live` (`IxCC.Recheck.Proof.Live`) take P1's root as the hypothesis
`hrl : RunLiveStmt`; `run_live` (`IxCC.Src.Relevance.Proof.P1.Main`) proves it. Instantiated, what
remains are the approved statements' own hypotheses: `Recheck.run`'s acceptance and the run's sort
events (`Front.RunSortAgree`), which nothing proves (`tests-p1-twin` tests them on every registered
run). -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Src.Relevance.Proof.P1

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}

/-- **The narrowing.** Under `Recheck.run`'s acceptance and the run's sort events, the source goes
wrong only by being stuck, trapping, or returning a `Live` value the view rejects: never because
of a marker. -/
theorem Front.goesWrong_live_closed (h : run cfg P c = .ok a) {i : Nat × List Nat}
    (hsa : a.front.RunSortAgree c.relevance i) :
    a.front.GoesWrong i → a.front.GoesWrongLive c.relevance i :=
  Front.goesWrong_live run_live h hsa

/-- **`Recheck.sound` with the narrowed escape**, under the run's sort events. -/
theorem sound_live_closed (h : run cfg P c = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (i : Nat × List Nat) (hi : a.front.Covered c i)
    (hsa : a.front.RunSortAgree c.relevance i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrongLive c.relevance i) ∧
    (¬ a.front.GoesWrongLive c.relevance i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
        ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  sound_live run_live h D hD i hi hsa

end IxCC.Recheck
