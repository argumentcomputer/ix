import IxCC.Recheck.Run
import IxCC.Anf.Proof.Pass.Closures

/-! # The middle end with the closures step

`anfOf c src lam` is the certificate's middle end (`Anf.Pipeline.run`) and
then the closures step at the source roots' declared counts. It refines its
Lam program on every covered input (`anfOf_refines`): on an input of exactly
the declared count, through the step (`Anf.Pipeline.Proof.closures_correct`,
whose premise `declaredCounts_exact` gives); on every input when the step
left the certificate's program unchanged, by the middle end's theorem alone
(`Anf.Pipeline.Proof.run_correct`). Its output is first order
(`anfOf_firstOrder`), and it is exactly the certificate's program for every
program `Fir.lower` accepted with its roots at their declared counts
(`anfOf_of_lower`): what compiled before the step was added compiles to the
same program, and every input is covered for it (`covered_of_unchanged`). -/

set_option autoImplicit false

namespace IxCC.Recheck

theorem closuresOf_ok {src : Src.Program} {pre A : Anf.Program} (h : closuresOf src pre = .ok A) :
    ∃ decl, declaredCounts src = some decl ∧ Anf.Pipeline.closures decl pre = .ok A := by
  unfold closuresOf at h
  cases hd : declaredCounts src with
  | none => rw [hd] at h; cases h
  | some decl =>
    simp only [hd] at h
    refine ⟨decl, rfl, ?_⟩
    cases hc : Anf.Pipeline.closures decl pre with
    | error e => rw [hc] at h; cases h
    | ok A' => rw [hc] at h; cases h; rfl

theorem anfOf_ok {c : Cert} {src : Src.Program} {lam : Lam.Program} {A : Anf.Program}
    (h : anfOf c src lam = .ok A) :
    ∃ pre, Anf.Pipeline.run c.mid lam = .ok pre ∧ closuresOf src pre = .ok A := by
  unfold anfOf at h
  obtain ⟨pre, hp, hc⟩ := Lam.ModesOk.bind_ok h
  refine ⟨pre, ?_, hc⟩
  cases hr : Anf.Pipeline.run c.mid lam with
  | error e => rw [hr] at hp; cases hp
  | ok p => rw [hr] at hp; cases hp; rfl

/-- **The middle end with the closures step refines** its Lam program on
every covered input. -/
theorem anfOf_refines {c : Cert} {src : Src.Program} {lam : Lam.Program} {A : Anf.Program}
    (h : anfOf c src lam = .ok A) : Sem.RefinesOn (Covered c.mid src lam A) lam A := by
  obtain ⟨pre, hpre, hcl⟩ := anfOf_ok h
  obtain ⟨decl, hd, hc⟩ := closuresOf_ok hcl
  have hstep := (Anf.Pipeline.Proof.closures_correct (Anf.Pipeline.Proof.run_wf hpre) hc).2.2
  have hexact : Sem.RefinesOn (ExactDeclared src) lam A :=
    (((Anf.Pipeline.Proof.run_correct hpre).on _).trans hstep).mono fun _ hi => declaredCounts_exact hd hi
  intro i hi
  rcases hi with hi | hu
  · exact hexact i hi
  · exact Anf.Pipeline.Proof.run_correct hu i

/-- The output is first order. -/
theorem anfOf_firstOrder {c : Cert} {src : Src.Program} {lam : Lam.Program} {A : Anf.Program}
    (h : anfOf c src lam = .ok A) : Anf.FirstOrder A := by
  obtain ⟨pre, -, hcl⟩ := anfOf_ok h
  obtain ⟨decl, -, hc⟩ := closuresOf_ok hcl
  exact Anf.Pipeline.Proof.closures_firstOrder hc

/-- **`fir.closures` is unreachable on the recheck path.** -/
theorem anfOf_lower_ne_closures {c : Cert} {src : Src.Program} {lam : Lam.Program} {A : Anf.Program}
    (h : anfOf c src lam = .ok A) (fns apps globs : List Anf.GlobalId) :
    Fir.lower A ≠ .error (.closures fns apps globs) :=
  Fir.Proof.lower_ne_closures (anfOf_firstOrder h) fns apps globs

/-- **No silent change**: a program whose certificate's middle end gives a
program `Fir.lower` accepts, with every root at its declared count, gets
exactly that program. -/
theorem anfOf_of_lower {c : Cert} {src : Src.Program} {lam : Lam.Program} {pre : Anf.Program}
    {decl : List Nat} {F : Fir.Program} (hpre : Anf.Pipeline.run c.mid lam = .ok pre)
    (hd : declaredCounts src = some decl) (hl : Fir.lower pre = .ok F)
    (hr : Anf.Pipeline.rootsAgree decl pre = true) : anfOf c src lam = .ok pre := by
  unfold anfOf closuresOf
  rw [hpre]
  simp only [Except.mapError, bind, Except.bind, hd, Anf.Pipeline.Proof.closures_of_lower hl hr]

/-- Every input is covered when the closures step left the certificate's
program unchanged. -/
theorem covered_of_unchanged {mid : Anf.Pipeline.Cert} {src : Src.Program} {lam : Lam.Program}
    {anf : Anf.Program} (h : Anf.Pipeline.run mid lam = .ok anf) (i : Nat × List Nat) :
    Covered mid src lam anf i :=
  .inr h

end IxCC.Recheck
