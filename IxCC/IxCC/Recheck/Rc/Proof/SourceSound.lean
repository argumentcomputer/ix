import IxCC.Recheck.Rc.Proof.FrontLanguage

/-! The established source-relative soundness clauses for the complete heap
view. Source errors and rejected observations retain the original GoesWrong
qualification; no stronger source adequacy claim is introduced. -/
set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Sem (Lang Obs)
open IxCC.Lam.Erase.Proof (CheckedProgram)

def Front.GoesWrong (f : Front) (input : Nat × List Nat) : Prop :=
  ∃ clock, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) input clock).GoesWrong ∨
    ∃ value, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) input clock = .ok value ∧
      f.view input.1 (Lang.obs value) = none

theorem source_goesWrong {f : Front} {input : Nat × List Nat} {clock : Nat}
    (wrong : (Lang.run f.source input clock).GoesWrong) : f.GoesWrong input := by
  rcases Sem.Viewed.run_goesWrong.1 wrong with source | rejected
  · exact ⟨clock, .inl source⟩
  · exact ⟨clock, .inr rejected⟩

section
variable {f : Front} {O : Type} [Lang (Nat × List Nat) O] {object : O}

theorem Front.sound_of (refinement : Sem.Refines f.source object)
    {input : Nat × List Nat} {clock : Nat} {output : Lang.Val O}
    (success : Lang.run object input clock = .ok output) :
    (∃ sourceClock value,
      Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
      f.view input.1 (Lang.obs value) = some (Lang.obs output)) ∨ f.GoesWrong input := by
  rcases refinement.backward success with ⟨sourceClock, observed, run, same⟩ | ⟨sourceClock, stuck⟩
  · obtain ⟨value, sourceRun, viewed⟩ := Sem.Viewed.run_ok run
    exact .inl ⟨sourceClock, value, sourceRun, viewed.trans (congrArg some same)⟩
  · exact .inr (source_goesWrong (clock := sourceClock) (by rw [stuck]; trivial))

theorem Front.safe_of (refinement : Sem.Refines f.source object)
    {input : Nat × List Nat} (safe : ¬ f.GoesWrong input) (clock : Nat) :
    ¬ (Lang.run object input clock).GoesWrong :=
  refinement.safe (fun _ wrong => safe (source_goesWrong wrong)) clock

theorem Front.diverges_of (refinement : Sem.Refines f.source object)
    {input : Nat × List Nat}
    (diverging : ∀ clock, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) input clock = .timeout) :
    (∀ clock, Lang.run object input clock = .timeout) ∨
      ∃ clock resource, Lang.run object input clock = .resource resource := by
  apply refinement.diverges
  intro clock
  change (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) input clock).bind _ = _
  rw [diverging clock]
  rfl
end





end IxCC.Recheck.RcReplay
