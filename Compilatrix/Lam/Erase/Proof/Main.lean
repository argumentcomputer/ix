import Compilatrix.Lam.Erase.Proof.Apply

/-! # The erasure simulation at every clock

By strong induction on the clock bound: at bound `m`, application
(`apply_sim`) needs only the lower bounds, and every erasure (`tr_sim`)
needs the lower bounds and application at `m`. So every erasure simulates
SrcEval at every clock (`tr_correct`, a `Sem.Sim` with the identity clock
map), and a program's run from a root does (`run_correct`): its global is
the root's δ body or its special head's wrapper, at the empty profile that
agrees with the empty levels `Src.run` instantiates (M2.2). -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Head Profile Levels)
open Compilatrix.Sem (Result ClockMono SimUpTo Sim later later_succ)

/-- The profile of a root: every universe parameter zero. -/
abbrev rootProf (I : Input) (c : CId) : Profile := Profile.normalize [] (I.lvls c)

/-- The global of a root (`rootId`): its δ body's, or its special head's
wrapper, at the root profile. -/
inductive RootR (I : Input) (G : Key.GKey → GlobalId → Prop) : CId → GlobalId → Prop
  | const {c : CId} {b : Src.Term} {g : GlobalId} :
      I.deltaBody c = some b → G (.const c (rootProf I c)) g → RootR I G c g
  | wrapper {c : CId} {h : Head} {g : GlobalId} :
      I.headOf c = some h → G (.wrapper h (rootProf I c)) g → RootR I G c g

theorem Lam.run_eq (P : Program) (k : Nat) (root : GlobalId) (xs : List Val) :
    Lam.run P k root xs = (Lam.eval P k [] (.glob root)).bind fun f => Lam.applyAll P k f (xs.map .val) := by
  unfold Lam.run
  cases Lam.eval P k [] (.glob root) <;> rfl

namespace Setting

variable {S : Setting} (wf : ProgWF S.I)
include wf

/-- The simulation at every clock bound. -/
theorem level (m : Nat) : S.Level m :=
  Nat.strongRecOn m fun m ih =>
    ⟨by
      intro cx t t' ht ρ ρ' ls he hag
      exact tr_sim wf ih (apply_sim wf ih) ht he hag, apply_sim wf ih⟩

/-- An erasure simulates SrcEval at every clock, from related environments. -/
theorem tr_correct {cx : Cx} {t : Src.Term} {t' : Term} (h : TR S.I S.G cx t t')
    {ρ : Src.Env} {ρ' : Env} {ls : Levels} (he : EnvR S.I S.G cx ρ ρ') (hag : Agree ls cx.prof) :
    Sim (VR S.I S.G) id (fun k => Src.eval S.p k ls ρ t) (fun k => Lam.eval S.L k ρ' t') :=
  SimUpTo.sim fun m => (level wf m).tr h he hag

/-- Applying related values to related slots simulates at every clock. -/
theorem apply_correct {f : Src.Value} {f' : Val} {s : Src.Slot} {s' : Slot}
    (hf : VR S.I S.G f f') (hs : SR S.I S.G s s') (ha : Applicable f s s') :
    Sim (VR S.I S.G) id (fun k => Src.apply S.p k f s) (fun k => Lam.apply S.L k f' s') :=
  SimUpTo.sim fun m => (level wf m).apply hf hs ha

omit wf in
/-- Applying related values to related value arguments. -/
theorem applyAll_sim {m : Nat} (hap : S.ApplySim m) :
    ∀ {f : Src.Value} {f' : Val} {xs : List Src.Value} {xs' : List Val}, VR S.I S.G f f' →
      Forall2 (VR S.I S.G) xs xs' →
      SimUpTo (VR S.I S.G) m (fun k => Src.applyAll S.p k f (xs.map .val))
        (fun k => Lam.applyAll S.L k f' (xs'.map .val))
  | _, _, [], [], hf, .nil =>
    (SimUpTo.ok hf).congr (fun k => Src.applyAll_nil S.p k _) (fun k => Lam.applyAll_nil S.L k _)
  | _, _, _ :: _, _ :: _, hf, .cons hx hr =>
    (SimUpTo.bind (Lam.apply_mono S.L _ _) (fun v => Lam.applyAll_mono S.L v _)
      (hap hf (.val hx) (.inr ⟨_, _, rfl, rfl⟩)) fun _ _ hv => applyAll_sim hap hv hr).congr
      (fun k => Src.applyAll_cons S.p k _ _ _) (fun k => Lam.applyAll_cons S.L k _ _ _)

/-- A run from a root with a δ body, up to clock bound `m`. -/
theorem run_const {c : CId} {b : Src.Term} {g : GlobalId} (hb : S.I.deltaBody c = some b)
    (hg : S.G (.const c (rootProf S.I c)) g) {xs : List Src.Value} {xs' : List Val}
    (hx : Forall2 (VR S.I S.G) xs xs') (m : Nat) :
    SimUpTo (VR S.I S.G) m (fun k => Src.run S.p k c xs) (fun k => Lam.run S.L k g xs') := by
  have hap : S.ApplySim m := (level wf m).apply
  obtain ⟨gl, hgl, _, hbody⟩ := S.glob_of hg
  cases hbody with
  | const hb' hbt =>
      rw [hb] at hb'
      cases hb'
      refine (SimUpTo.bind (Lam.eval_mono S.L [] gl.body).later
        (fun f => Lam.applyAll_mono S.L f _)
        (SimUpTo.later (n := m) fun m' hm' =>
          (level wf m').tr hbt (EnvR.empty _) (Agree.root _))
        fun f f' hf => applyAll_sim hap hf hx).congr (fun k => ?_) (fun k => ?_)
      · rw [Src.run_eq, evalConst_delta S.p S.ch hb]
      · rw [Lam.run_eq, S.eval_glob_of hgl]

/-- A run from a root that is a special head, up to clock bound `m`. -/
theorem run_wrapper {c : CId} {h : Head} {g : GlobalId} (hh : S.I.headOf c = some h)
    (hg : S.G (.wrapper h (rootProf S.I c)) g) {xs : List Src.Value} {xs' : List Val}
    (hx : Forall2 (VR S.I S.G) xs xs') (m : Nat) :
    SimUpTo (VR S.I S.G) m (fun k => Src.run S.p k c xs) (fun k => Lam.run S.L k g xs') := by
  have hap : S.ApplySim m := (level wf m).apply
  obtain ⟨gl, hgl, _, hbody⟩ := S.glob_of hg
  cases hbody with
  | wrapper hw =>
      obtain ⟨inner, hin⟩ := hw.lams
      rw [hin] at hw
      have hag0 : Agree [] (rootProf S.I c) := Agree.root _
      by_cases h0 : headArity S.I h = 0
      · have hw0 := hw
        refine (SimUpTo.bind (Lam.eval_mono S.L _ inner).later
          (fun f => Lam.applyAll_mono S.L f _)
          (SimUpTo.laterR (Lam.eval_mono S.L _ inner)
            (wrap_fire wf (fun m' _ => level wf m') hw0 hag0 (xs := []) (vs := []) .nil
              (by simp [h0])))
          fun f f' hf => applyAll_sim hap hf hx).congr (fun k => ?_) (fun k => ?_)
        · rw [Src.run_eq, evalConst_head S.p S.ch hh, Src.headValue_eq, ← headArity_eq S.p S.ch]
          simp only [h0, beq_self_eq_true, ↓reduceIte, List.map_nil]
        · rw [Lam.run_eq, S.eval_glob_of hgl]
          cases k with
          | zero => rfl
          | succ k =>
            simp only [later_succ]
            rw [hin, h0, List.replicate_zero]
            rfl
      · have hpos : 0 < headArity S.I h := Nat.pos_of_ne_zero h0
        have hv : VR S.I S.G (.pap h [] [])
            (.clos [] (Term.lams (List.replicate (headArity S.I h - 1) .strict) inner)) := by
          have := VR.pap (args := []) (vs := []) hw hag0 hpos .nil
          simpa using this
        refine (SimUpTo.bind (ClockMono.const _).later (fun f => Lam.applyAll_mono S.L f _)
          (SimUpTo.laterR (ClockMono.const _) (SimUpTo.ok hv))
          fun f f' hf => applyAll_sim hap hf hx).congr (fun k => ?_) (fun k => ?_)
        · rw [Src.run_eq, evalConst_head S.p S.ch hh, Src.headValue_eq, ← headArity_eq S.p S.ch]
          have h0' : (headArity S.I h == 0) = false := by simpa using h0
          simp only [h0', Bool.false_eq_true, ↓reduceIte, Sem.Result.bind_ok]
        · rw [Lam.run_eq, S.eval_glob_of hgl, hin]
          cases k with
          | zero => rfl
          | succ k =>
            simp only [later_succ]
            obtain ⟨a', ha'⟩ : ∃ a', headArity S.I h = a' + 1 :=
              ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
            rw [ha', List.replicate_succ, Lam.eval_lams_cons]
            simp

/-- A run from a root, up to clock bound `m`. -/
theorem run_simUpTo {c : CId} {g : GlobalId} (hr : RootR S.I S.G c g) {xs : List Src.Value}
    {xs' : List Val} (hx : Forall2 (VR S.I S.G) xs xs') (m : Nat) :
    SimUpTo (VR S.I S.G) m (fun k => Src.run S.p k c xs) (fun k => Lam.run S.L k g xs') := by
  cases hr with
  | const hb hg => exact run_const wf hb hg hx m
  | wrapper hh hg => exact run_wrapper wf hh hg hx m

/-- A run from a root simulates at every clock. -/
theorem run_correct {c : CId} {g : GlobalId} (hr : RootR S.I S.G c g) {xs : List Src.Value}
    {xs' : List Val} (hx : Forall2 (VR S.I S.G) xs xs') :
    Sim (VR S.I S.G) id (fun k => Src.run S.p k c xs) (fun k => Lam.run S.L k g xs') :=
  SimUpTo.sim (run_simUpTo wf hr hx)

end Setting

end Compilatrix.Lam.Erase.Proof
