import IxCC.Recheck.Proof.LiveDefs
import IxCC.Recheck.Proof.FrontAccepted
import IxCC.Recheck.Proof.Soundness
import IxCC.Src.Relevance.Proof.P1.Prefix
import IxCC.Src.Relevance.Proof.P1.Facts
import IxCC.Src.Relevance.Proof.P1.RunLive

/-! # P1's consumption: `Recheck.sound`'s escape narrowed

Under `Recheck.run`'s acceptance and the run's sort events (`Front.RunSortAgree`), the source goes
wrong only by being stuck, trapping, or returning a `Live` value the view rejects
(`Front.goesWrong_live`), and `Recheck.sound` holds with that escape (`sound_live`). Both take P1's
root as a hypothesis (`hrl : RunLiveStmt`, `run_live`'s statement), which is not proved. They
also use L1's facts on the program SrcEval runs (`P1.facts_modeEq`), what the front end's acceptance
gives (`front_accepted`, `shapeOk_of_run`) and `P1.bind_ok_inv`. Engineer PB's proofs, with
`run_live` as the hypothesis `hrl`. -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Src.Relevance.Proof.P1

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}

/-- **The narrowing.** Under `Recheck.run`'s acceptance, the run's sort events and P1's root
(`hrl`), the source goes wrong only by being stuck, trapping, or returning a `Live` value the view
rejects: never because of a marker. -/
theorem Front.goesWrong_live (hrl : RunLiveStmt) (h : run cfg P c = .ok a) {i : Nat × List Nat}
    (hsa : a.front.RunSortAgree c.relevance i) :
    a.front.GoesWrong i → a.front.GoesWrongLive c.relevance i := by
  rintro ⟨k, hgw | ⟨v, hv, hview⟩⟩
  · exact ⟨k, .inl hgw⟩
  · refine ⟨k, .inr ⟨v, hv, ?_, hview⟩⟩
    obtain ⟨hfr, -, -⟩ := runLir_spec (run_parts h).1
    obtain ⟨installed, hchk, hcan, hsrc⟩ := front_accepted hfr
    have hf : Facts a.src c.relevance a.checked := by
      have := facts_modeEq hchk hcan (Src.Lazify.run_modeEq installed a.checked.keys)
      rw [show a.src = a.front.src from rfl, hsrc]
      exact this
    change Lam.Erase.Proof.srcRun ⟨a.src, a.checked⟩ i k = .ok v at hv
    unfold Lam.Erase.Proof.srcRun at hv
    split at hv
    · rename_i x root hr
      obtain ⟨w, hw, hwv⟩ := bind_ok_inv hv
      cases hwv
      exact hrl hf (shapeOk_of_run h) ⟨x, List.mem_of_getElem? hr⟩
        (hsa k root (by simp [Artifact.front, hr])) hw
    · cases hv

/-- **`Recheck.sound` with the narrowed escape**, under P1's root (`hrl`). -/
theorem sound_live (hrl : RunLiveStmt) (h : run cfg P c = .ok a) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) (i : Nat × List Nat) (hi : a.front.Covered c i)
    (hsa : a.front.RunSortAgree c.relevance i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrongLive c.relevance i) ∧
    (¬ a.front.GoesWrongLive c.relevance i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
        ∃ k failure, Lang.run (a.linked D) i k = .resource failure) := by
  obtain ⟨h1, h2, h3⟩ := sound h D hD i hi
  refine ⟨fun k w hw => (h1 k w hw).imp_right (Front.goesWrong_live hrl h hsa), fun hn => h2 ?_, h3⟩
  exact fun hg => hn (Front.goesWrong_live hrl h hsa hg)

end IxCC.Recheck
