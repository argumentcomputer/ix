import IxCC.Anf.Proof.Defun.Fund
import IxCC.Anf.Proof.Defun.WellScoped
import IxCC.Anf.Proof.Pass.Basic
import IxCC.Fir.Proof.Lang
import IxCC.Fir.Proof.FirstOrder

/-! # P8 is correct

`run_refines`: on every input of exactly the root's arity, P8's output
refines its input. The root is an input global, kept at its id with its
parameters and translated body (`Valid.old`), so its value is a function
global's closure on both sides; exact arity enters the body once on each side
(`applyN_exact`), related one clock down by the fundamental lemma (`fund`)
over the arguments' literals, which relate to themselves; a CAF root on no
argument evaluates its body on both sides. Related results observe the same
(`dv_obs`). `Anf.Defun.correct`: with first order (`defun_firstOrder`); scoping, which
nothing downstream needs, is the separate `wellScoped_run`.

As a step of the middle end in isolation (`step_correct`): a program whose
ids are exactly `0 … size - 1` gives one again (`run_wf`), and the roots'
exact-arity inputs are the same before and after the step when the roots are
below the size (`exactArity_run`; an exact-arity input of the output is one
of the input with no premise on the roots, `exactArity_of_run`). Followed by
`Fir.lower`: P8's output is never refused for closures
(`Fir.Proof.lower_ne_closures`), and when lowered
the Fir program refines P8's input on the same inputs (`defun_lower_refines`,
by `Fir.lower_refines`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

open IxCC.Sem (Result ClockMono SimUpTo Sim later later_succ later_zero Lang)
open IxCC.Anf.Rel (Pw)

/-! ## A root's run -/

theorem lits_dv {X : Setting} : ∀ (ns : List Nat),
    Pw (DV X) (ns.map fun n => Val.lit (.nat n)) (ns.map fun n => Val.lit (.nat n))
  | [] => .nil
  | _ :: ns => .cons .lit (lits_dv ns)

theorem globVal_fn {P : Program} {k : Nat} {gd : GDef} (h : gd.ps ≠ []) :
    globVal P k gd = .ok (.clos [] gd.ps.length gd.body []) := by
  unfold globVal
  split
  · rename_i heq; exact absurd heq h
  · rfl

theorem globVal_caf {P : Program} {k : Nat} {gd : GDef} (h : gd.ps = []) :
    globVal P k gd = later k fun k => eval P k [] [] gd.body := by
  unfold globVal
  split
  · rfl
  · rename_i heq; rw [h] at heq; cases heq

/-- A closure with nothing supplied, applied to exactly its arity: one charge,
then the body over the arguments. -/
theorem applyN_exact {P : Program} {k N : Nat} {ρ : List Val} {b : Exp} {xs : List Val} (hl : xs.length = N)
    (hN : 0 < N) : applyN P k (.clos ρ N b []) xs = later k fun k => eval P k (xs.reverse ++ ρ) [] b := by
  obtain ⟨x, xr, rfl⟩ : ∃ x xr, xs = x :: xr := by
    cases xs with
    | nil => simp at hl; omega
    | cons x xr => exact ⟨x, xr, rfl⟩
  rw [applyN_clos]
  congr 1
  funext k'
  have h1 : ([] : List Val).length < N := by simp; omega
  have h2 : ¬ ([] : List Val).length + (x :: xr).length < N := by simp at hl ⊢; omega
  rw [ite_eq_left h1, ite_eq_right h2]
  unfold enter
  rw [List.nil_append, List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
  simp only [applyN_nil', bind_ok_right]

/-- The run from a root, on exactly the root's arity. -/
theorem root_sim {X : Setting} (hX : Valid X) (n : Nat) (r : GlobalId) (ns : List Nat)
    (hi : ∀ gd, X.P.global? r = some gd → ns.length = gd.ps.length) :
    SimUpTo (DV X) n (fun k => Anf.run X.P k r (ns.map fun n => .lit (.nat n)))
      (fun k => Anf.run X.Q k r (ns.map fun n => .lit (.nat n))) := by
  refine SimUpTo.congr ?_ (fun k => run_eq X.P k r _) (fun k => run_eq X.Q k r _)
  cases hg : X.P.global? r with
  | none =>
    exact (SimUpTo.stuck _).congr (fun k => by rw [evalBind_glob, hg]; rfl) (fun _ => rfl)
  | some gd =>
    obtain ⟨gd', hq, hps, htr⟩ := hX.old r gd hg
    have hxl : (ns.map fun n => Val.lit (.nat n)).length = gd.ps.length := by
      rw [List.length_map, hi gd hg]
    by_cases hnil : gd.ps = []
    · have hps' : gd'.ps = [] := by rw [hps, hnil]
      have hxs : (ns.map fun n => Val.lit (.nat n)) = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [hxl, hnil]; rfl
      rw [hnil] at htr
      refine (SimUpTo.bind (d := fun f k => applyN X.P k f []) (d' := fun f k => applyN X.Q k f [])
        (ClockMono.later (eval_mono X.Q [] [] gd'.body)) (fun w => applyN_mono X.Q w [])
        (SimUpTo.later fun i _ => fund hX i htr (Nat.zero_le _) .nil .nil)
        fun v w hvw => (SimUpTo.ok hvw).congr (fun k => applyN_nil' X.P k v) (fun k => applyN_nil' X.Q k w)).congr
        (fun k => ?_) (fun k => ?_)
      · rw [evalBind_glob, hg, hxs]
        show (globVal X.P k gd).bind _ = _
        rw [globVal_caf hnil]
      · rw [evalBind_glob, hq, hxs]
        show (globVal X.Q k gd').bind _ = _
        rw [globVal_caf hps']
    · have hne' : gd'.ps ≠ [] := by rw [hps]; exact hnil
      have hN : 0 < gd.ps.length := List.length_pos_iff.2 hnil
      refine (SimUpTo.later fun i _ => fund hX i htr
        (by rw [List.length_append, List.length_reverse, hxl]; omega)
        (dvs_of_pw ((lits_dv ns).reverse.append .nil)) .nil).congr (fun k => ?_) (fun k => ?_)
      · rw [evalBind_glob, hg]
        show (globVal X.P k gd).bind _ = _
        rw [globVal_fn hnil, Result.bind_ok, applyN_exact hxl hN]
      · rw [evalBind_glob, hq]
        show (globVal X.Q k gd').bind _ = _
        rw [globVal_fn hne', Result.bind_ok, applyN_exact (by rw [hxl, hps]) (by rw [hps]; exact hN)]

/-! ## Correctness -/

/-- **P8 refines its input** on every input of exactly the root's arity. -/
theorem run_refines {P Q : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size)
    (h : run P = .ok Q) : Sem.RefinesOn (ExactArity P) P Q := by
  obtain ⟨X, rfl, rfl, hX⟩ := run_valid hwf h
  intro i hi
  have hsim : Sim (DV X) id (Lang.run X.P i) (Lang.run X.Q i) := SimUpTo.sim fun n => by
    show SimUpTo (DV X) n (anfRun X.P i) (anfRun X.Q i)
    unfold anfRun
    rw [hX.roots]
    cases hr : X.P.roots[i.1]? with
    | none => exact SimUpTo.stuck _
    | some r => exact root_sim hX n r i.2 fun gd hg => hi r gd hr hg
  exact (hsim.refines (Lang.mono X.P i) (Lang.mono X.Q i)).mono fun _ _ h => dv_obs h

theorem defun_run {P Q : Program} (h : Anf.defun P = .ok Q) : run P = .ok Q := by
  unfold Anf.defun at h
  cases hr : run P with
  | error e => rw [hr] at h; cases h
  | ok q => rw [hr] at h; cases h; rfl

/-- **`Anf.Defun.correct`**: P8's output is first order and refines its input
on every input of exactly the root's arity, for an input whose globals lie
below its size. (That the output is well scoped when the input is, which no
later step needs, is `wellScoped_run`.) -/
theorem correct {P Q : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size)
    (h : Anf.defun P = .ok Q) : Anf.FirstOrder Q ∧ Sem.RefinesOn (ExactArity P) P Q :=
  ⟨defun_firstOrder h, run_refines hwf (defun_run h)⟩

/-! ## As a step, and followed by `Fir.lower` -/

theorem mem_numbered_lt {α : Type} : ∀ {k : Nat} {xs : List α} {i : Nat} {x : α},
    (i, x) ∈ numbered k xs → i < k + xs.length
  | _, [], _, _, h => by simp [numbered] at h
  | k, y :: ys, i, x, h => by
    simp only [numbered, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩ | h
    · simp only [List.length_cons]; omega
    · have := mem_numbered_lt h
      simp only [List.length_cons]; omega

/-- **P8 keeps the shape of a program's ids**: if they are exactly
`0 … size - 1`, so are the output's. -/
theorem run_wf {P Q : Program} (hw : P.WF) (h : run P = .ok Q) : Q.WF := by
  obtain ⟨gs, acc, parents, hr, rfl⟩ := run_ran h
  have hgs := globalsGo_ps P.globalList {} [] [] (by simp) (fun g gd hx => by
    obtain ⟨hlt, hgd⟩ := mem_globalList.1 hx
    exact ⟨hgd, hlt⟩) hr.walk
  refine ⟨fun g gd hg => ?_, fun g hg => ?_⟩
  · show g < liftBase P acc + acc.lifted.length
    unfold liftBase
    rcases assemble_cases hg with hm | ⟨i, hi, rfl, -⟩ | hm
    · obtain ⟨_, -, hlt, -⟩ := hgs _ _ hm
      exact Nat.lt_of_lt_of_le hlt (by omega)
    · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) (Nat.le_add_right _ _)
    · obtain ⟨⟨i, l⟩, hli, he⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at he
      rw [← he.1]
      have := mem_numbered_lt hli
      rw [List.length_reverse] at this
      unfold liftBase at this
      exact this
  · change g < liftBase P acc + acc.lifted.length at hg
    by_cases h1 : g < P.size
    · obtain ⟨gd, hgd⟩ := hw.2 g h1
      obtain ⟨gd', -, -, hq, -, -⟩ := assemble_old hr h1 hgd
      exact ⟨gd', hq⟩
    · by_cases h2 : g < P.size + acc.maxApp
      · have hm1 : 1 ≤ g - P.size + 1 := by omega
        have hm2 : g - P.size + 1 ≤ acc.maxApp := by omega
        have hid : dispId P.size (g - P.size + 1) = g := by
          show P.size + (g - P.size + 1) - 1 = g
          omega
        have := assemble_disp hr hm1 hm2
        rw [hid] at this
        exact ⟨_, this⟩
      · have hsz : g < liftBase P acc + acc.lifted.reverse.length := by
          rw [List.length_reverse]; exact hg
        obtain ⟨l, hl⟩ := numbered_get (liftBase P acc) acc.lifted.reverse g (by unfold liftBase; omega) hsz
        exact ⟨_, assemble_lifted hr hl⟩

/-- The roots' exact-arity inputs are the same before and after P8, when the
roots lie below the size. -/
theorem exactArity_run {P Q : Program} (hroots : ∀ r ∈ P.roots, r < P.size) (h : run P = .ok Q)
    (i : Nat × List Nat) : ExactArity Q i ↔ ExactArity P i := by
  obtain ⟨gs, acc, parents, hr, rfl⟩ := run_ran h
  have hgs := globalsGo_ps P.globalList {} [] [] (by simp) (fun g gd hx => by
    obtain ⟨hlt, hgd⟩ := mem_globalList.1 hx
    exact ⟨hgd, hlt⟩) hr.walk
  constructor
  · intro hQ r gd hroot hg
    obtain ⟨gd', a, a', hq, hgl, -⟩ := assemble_old hr (hroots r (List.mem_of_getElem? hroot)) hg
    rw [hQ r gd' hroot hq, global_ps hgl]
  · intro hP r gd' hroot hq
    have hlt := hroots r (List.mem_of_getElem? hroot)
    rcases assemble_mem hq with hm | ⟨hle, -⟩ | ⟨hle, -⟩
    · obtain ⟨gd0, hg0, -, hps⟩ := hgs _ _ hm
      rw [hP r gd0 hroot hg0, hps]
    · exact absurd hle (Nat.not_le.2 hlt)
    · exact absurd hle (Nat.not_le.2 hlt)

/-- An exact-arity input of the output is one of the input, with no premise
on the roots. -/
theorem exactArity_of_run {P Q : Program} (hwf : ∀ g gd, P.global? g = some gd → g < P.size)
    (h : run P = .ok Q) {i : Nat × List Nat} (hQ : ExactArity Q i) : ExactArity P i := by
  obtain ⟨gs, acc, parents, hr, rfl⟩ := run_ran h
  intro r gd hroot hg
  obtain ⟨gd', a, a', hq, hgl, -⟩ := assemble_old hr (hwf r gd hg) hg
  rw [hQ r gd' hroot hq, global_ps hgl]

/-- **P8 as a step of the middle end**, in isolation: from a program whose
ids are exactly `0 … size - 1`, P8's output has that shape again and refines
its input on every input of exactly the root's arity. -/
theorem step_correct {P Q : Program} (hw : P.WF) (h : Anf.defun P = .ok Q) :
    Q.WF ∧ Sem.RefinesOn (ExactArity P) P Q :=
  ⟨run_wf hw (defun_run h), (correct hw.1 h).2⟩

/-- P8's output is never refused by `Fir.lower` for closures. -/
theorem defun_lower_ne_closures {P Q : Program} (h : Anf.defun P = .ok Q) (fns apps globs : List GlobalId) :
    Fir.lower Q ≠ .error (.closures fns apps globs) :=
  Fir.Proof.lower_ne_closures (defun_firstOrder h) fns apps globs

/-- **P8 followed by `Fir.lower`**: the Fir program refines P8's input on
every input of exactly the root's arity. -/
theorem defun_lower_refines {P Q : Program} {F : Fir.Program}
    (hwf : ∀ g gd, P.global? g = some gd → g < P.size) (h : Anf.defun P = .ok Q) (hl : Fir.lower Q = .ok F) :
    Sem.RefinesOn (ExactArity P) P F := fun i hi =>
  (((correct hwf h).2 i hi).trans (Fir.Proof.lower_refines hl i)).mono fun _ _ ⟨_, h1, h2⟩ => h1.trans h2

end IxCC.Anf.Defun.Proof
