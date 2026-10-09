import Compilatrix.Cfg.Rc.Proof.Language

set_option autoImplicit false
namespace Compilatrix.Fir.Proof
open Compilatrix.Sem (Result ClockMono Obs Lang Sim later)
open Compilatrix.Fir.Lower

/-- Preserve the actual first-order value relation. Partial application keeps
its existing unobserved erased result and cannot satisfy a successful view. -/
def FirWitness (A : Anf.Program) (v : Anf.Val) (w : Fir.Val) : Prop :=
  VR A v w ∨ (Anf.obsV v = none ∧ w = .erased)

theorem FirWitness.observations {A : Anf.Program} {v : Anf.Val} {w : Fir.Val}
    (related : FirWitness A v w) : Anf.obsV v = Fir.obsV w := by
  rcases related with related | ⟨unobserved, rfl⟩
  · exact vr_obs related
  · exact unobserved

variable {A : Anf.Program}

theorem lower_retained {F : Program} (h : lower A = .ok F) : ∀ i, Sim (FirWitness A) (fun k => tickBound A * (k + 1))
      (Anf.anfRun A i) (firRun F i) := by
  intro i
  obtain ⟨r, ns⟩ := i
  show Sim _ _ (Anf.anfRun A (r, ns)) (firRun F (r, ns))
  have hex := (lower_fields h).2.1
  unfold Anf.anfRun firRun
  simp only [hex]
  cases hr : A.roots[r]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some g =>
    simp only
    have hs := (lower_ok h).2.2.1 g (List.mem_of_getElem? hr)
    obtain ⟨gd, hg⟩ := lower_global h hs
    obtain ⟨fd, hfd, hfun⟩ := (setting_of h).funs hg hs
    obtain ⟨st, -, hps⟩ := function_ok hfun
    have hn : fd.params.length = gd.ps.length := by rw [hps]; simp
    simp only [hfd, hn]
    have hobs : ∀ v w, VR A v w → FirWitness A v w :=
      fun _ _ h => .inl h
    by_cases he : ns.length = gd.ps.length
    · simp only [Sem.entryRun, he, ↓reduceIte]
      exact (run_sim h hs hg (vrs_lits ns) (by simpa using he)).mono hobs
    · by_cases hlt : ns.length < gd.ps.length
      · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
        obtain ⟨p, ps, hps'⟩ : ∃ p ps, gd.ps = p :: ps := by
          cases hq : gd.ps with
          | nil => rw [hq] at hlt; simp at hlt
          | cons p ps => exact ⟨p, ps, rfl⟩
        have hclos : ∀ k, Anf.run A k g (ns.map fun n => .lit (.nat n)) =
            Anf.applyN A k (.clos [] gd.ps.length gd.body []) (ns.map fun n => .lit (.nat n)) := by
          intro k
          rw [Anf.run_eq, Anf.evalBind_glob, hg]
          simp only [Result.ofOption, Result.bind_ok, Anf.globVal, hps']
        by_cases hnil : ns = []
        · subst hnil
          simp only [↓reduceIte]
          refine (Sim.okConst (a := Anf.Val.clos [] gd.ps.length gd.body []) (b := Val.erased)
            (R := FirWitness A) (.inr ⟨rfl, rfl⟩)).ofEq ?_ (fun _ => rfl)
          intro k
          rw [hclos k]
          simp [Anf.applyN_nil']
        · simp only [hnil, ↓reduceIte]
          obtain ⟨n₀, ns', rfl⟩ : ∃ n₀ ns', ns = n₀ :: ns' := by
            cases ns with
            | nil => exact absurd rfl hnil
            | cons n₀ ns' => exact ⟨n₀, ns', rfl⟩
          refine (Sim.laterConst
            (a := Anf.Val.clos [] gd.ps.length gd.body ((n₀ :: ns').map fun n => .lit (.nat n)))
            (b := Val.erased) (R := FirWitness A) (.inr ⟨rfl, rfl⟩)
            (fun k hk => absurd hk (Nat.pos_iff_ne_zero.1
              (Nat.mul_pos (setting_of h).pos (Nat.succ_pos k))))).ofEq ?_ (fun _ => rfl)
          intro k
          rw [hclos k, List.map_cons, Anf.applyN_clos]
          cases k with
          | zero => rfl
          | succ k =>
            simp only [Compilatrix.Sem.later_succ, List.length_nil, List.length_cons, Nat.zero_add,
              List.nil_append]
            have : 0 < gd.ps.length := by rw [hps']; simp
            simp only [List.length_cons] at hlt
            simp [this, hlt]
      · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
        have hgt : gd.ps.length < ns.length := by omega
        have hxs : gd.ps.length < (ns.map fun n => Anf.Val.lit (.nat n)).length := by simpa using hgt
        refine Sim.bindStuck (run_sim h hs hg ((vrs_lits ns).take gd.ps.length) (by simp; omega))
          (fun k v hv => ?_) |>.ofEq (fun k => anf_run_over hg hxs) (fun k => ?_)
        · obtain ⟨w, -, hvw⟩ := run_ok h hs hg ((vrs_lits ns).take gd.ps.length) (by simp; omega) hv
          exact applyN_vr hvw (by simp; omega)
        · simp only [litArgs, List.map_take]



end Compilatrix.Fir.Proof
