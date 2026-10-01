import Compilatrix.Fir.Proof.Correct
import Compilatrix.Sem.Entry
import Compilatrix.Sem.TracedTransform

/-! # Fir as a language, and `Fir.lower` as a pass

Fir programs run from an export on `Nat` inputs (`Sem.Lang`, the input
`(root index, arguments)` every Phase 1 level shares), applied as Anf
applies a root (`Sem.entryRun`: a call for the exact arity, a value with no
observation for fewer arguments, the call followed by `stuck` for more),
with values observed as Anf observes them (`Fir.obsV`). Through
`Lang.instTLang` it is also a traced language with `Env := Unit`,
`E := Empty` (decision D-1).

`Fir.lower_refines`: every program `Fir.lower` accepts refines its Anf
program, on every input (`Sem.Refines`): the exact arity by
`Fir.convert_correct`, fewer arguments as a partial application, more as
the first-order result applied to the rest (stuck at both levels).
`lowerPass` packages it as a pass, `lowerTPass` as a traced one. -/

set_option autoImplicit false

namespace Compilatrix.Fir

open Compilatrix.Sem (Result ClockMono Obs Lang Sim)
open Compilatrix.Fir.Proof

/-- `Nat` inputs as Fir values. -/
def litArgs (ns : List Nat) : List Val := ns.map fun n => .lit (.nat n)

/-- A run of export `i.1` on the `Nat` inputs `i.2`, applied as Anf applies
a root. -/
def firRun (F : Program) (i : Nat × List Nat) (k : Nat) : Result Val :=
  match F.exports[i.1]? with
  | some f =>
    match F.fun? f with
    | some fd => Sem.entryRun fd.params.length .erased (fun ns k => run F k f (litArgs ns)) i.2 k
    | none => .stuck
  | none => .stuck

instance : Lang (Nat × List Nat) Program where
  Val := Val
  run := firRun
  mono F i := by
    unfold firRun
    split
    · split
      · exact Sem.entryRun_mono (fun ns => run_mono F _ _) _
      · exact ClockMono.const _
    · exact ClockMono.const _
  obs := obsV

theorem lang_run (F : Program) (i : Nat × List Nat) : Lang.run F i = firRun F i := rfl

end Compilatrix.Fir

namespace Compilatrix.Fir.Proof

open Compilatrix.Sem (Result ClockMono Obs Lang Sim later)
open Compilatrix.Fir.Lower

variable {A : Anf.Program}

/-- Anf applies a root to more arguments than it has parameters by entering
it on as many as it has, then applying the result to the rest. -/
theorem anf_run_over {k : Nat} {g : Anf.GlobalId} {gd : Anf.GDef} (hg : A.global? g = some gd)
    {xs : List Anf.Val} (hl : gd.ps.length < xs.length) :
    Anf.run A k g xs =
      (Anf.run A k g (xs.take gd.ps.length)).bind fun r => Anf.applyN A k r (xs.drop gd.ps.length) := by
  have htl : (xs.take gd.ps.length).length = gd.ps.length := by rw [List.length_take]; omega
  rw [anf_run_eq hg htl, Anf.run_eq, Anf.evalBind_glob, hg]
  simp only [Result.ofOption, Result.bind_ok]
  unfold Anf.callVal
  simp only [htl, ↓reduceIte]
  unfold Anf.globVal
  cases hps : gd.ps with
  | nil =>
    simp only [List.length_nil, List.take_zero, List.drop_zero, List.reverse_nil]
  | cons p ps =>
    simp only [Result.bind_ok]
    cases xs with
    | nil => simp at hl
    | cons v rest =>
      rw [Anf.applyN_clos]
      cases k with
      | zero => rfl
      | succ k =>
        rw [hps] at hl
        simp only [List.length_cons] at hl
        have h1 : ¬ (0 + (rest.length + 1) < ps.length + 1) := by omega
        simp only [Compilatrix.Sem.later_succ, List.length_nil, List.length_cons, Nat.zero_add,
          Nat.zero_lt_succ, ↓reduceIte, Anf.enter, List.nil_append, List.append_nil]
        have h2 : ¬ (rest.length + 1 < ps.length + 1) := by omega
        simp only [h2, ↓reduceIte]

/-- A first-order Anf value applied to arguments is stuck. -/
theorem applyN_vr {v : Anf.Val} {w : Val} (h : VR A v w) {k : Nat} {xs : List Anf.Val} (hxs : xs ≠ []) :
    Anf.applyN A k v xs = .stuck := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons x rest =>
    refine Anf.applyN_not_clos A k v x rest fun ρ n b got e => ?_
    subst e
    cases h

/-- Fir's run of a lowered global on Anf's arguments, exact arity: an Anf
value is a related Fir value at the same clock. -/
theorem run_ok {F : Program} (h : lower A = .ok F) {g : Anf.GlobalId} (hs : g < A.size) {gd : Anf.GDef}
    (hg : A.global? g = some gd) {xs : List Anf.Val} {ws : List Val} (hvs : VRs A xs ws)
    (hl : xs.length = gd.ps.length) {k : Nat} {v : Anf.Val} (hv : Anf.run A k g xs = .ok v) :
    ∃ w, run F k g ws = .ok w ∧ VR A v w := by
  have S := setting_of h
  obtain ⟨fd, hfd, hfun⟩ := S.funs hg hs
  have hc := call_corr S (fun a' _ => stmt S a') hg hs hfun hvs hl (a := k)
  rw [anf_run_eq hg hl] at hv
  obtain ⟨w, hw, hvw⟩ := hc.ok v hv
  exact ⟨w, by rw [run_eq, evalCall_of F k hfd ws]; exact hw, hvw⟩

theorem vrs_lits (ns : List Nat) : VRs A (ns.map fun n => Anf.Val.lit (.nat n)) (litArgs ns) := by
  induction ns with
  | nil => exact .nil
  | cons n ns ih => exact .cons (.lit _) ih

/-- **`Fir.lower` refines**: every Anf program it accepts, on every input. -/
theorem lower_refines {F : Program} (h : lower A = .ok F) : Sem.Refines A F := by
  refine Sem.Refines.of_sim (R := Lang.ObsEq) (fun _ _ h => h) fun i => ⟨fun k => tickBound A * (k + 1), ?_⟩
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
    have hobs : ∀ v w, VR A v w → Lang.ObsEq (S := Anf.Program) (T := Program) v w :=
      fun _ _ h => vr_obs h
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
            (R := Lang.ObsEq (S := Anf.Program) (T := Program)) rfl).ofEq ?_ (fun _ => rfl)
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
            (b := Val.erased) (R := Lang.ObsEq (S := Anf.Program) (T := Program)) rfl
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

/-- `Fir.lower` as a pass: no certificate, no precondition (it checks what
its proof needs); its output is a lowering, which is what later passes'
preconditions read (`Cfg.Proof.bools_of_lower`, `Cfg.Proof.immortal_good`). -/
def lowerPass : Sem.Transform Anf.Program Program where
  name := "Fir.lower"
  pre _ := True
  run A _ := (lower A).mapError (·.render)
  post F := ∃ A, lower A = .ok F
  correct A _ F _ h := by
    have hl : lower A = .ok F := by
      cases hl : lower A with
      | error e => simp [hl, Except.mapError] at h
      | ok F' => simp only [hl, Except.mapError, Except.ok.injEq] at h; subst h; rfl
    exact ⟨⟨A, hl⟩, lower_refines hl⟩

/-- `Fir.lower_refines` in the traced shape (decision D-1). -/
theorem lower_refines_traced {F : Program} (h : lower A = .ok F) : Sem.TRefines A F :=
  Sem.Refines.ofPure (lower_refines h)

/-- `Fir.lower` as a traced pass. -/
def lowerTPass : Sem.TTransform Anf.Program Program := lowerPass.lift

end Compilatrix.Fir.Proof
