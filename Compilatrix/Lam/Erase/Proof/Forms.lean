import Compilatrix.Lam.Erase.Proof.SimBase
import Compilatrix.Lam.Erase.Proof.Values

/-! # Saturated special heads after their arguments

Once a saturated spine's arguments are bound (SrcEval's slots; Lam's `let`s
and `Ref`s), SrcEval fires the head and Lam evaluates the form erasure put
in its place. These lemmas relate the two for each head, needing only
lower clock bounds (every nested evaluation follows a charge) (M2.2). The
same lemmas serve saturated spines in place and wrapper bodies, whose
arguments are variables bound to values. -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Head Profile Levels)
open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ)

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- A bound argument's reference against SrcEval's slot for it: □ is
`irr`, a level holds a related value, a by-name argument is its thunk. -/
inductive RefSlot (I : Input) (G : Key.GKey → GlobalId → Prop) (ls : Levels) (ρ : Src.Env)
    (ρ'' : Env) : Ref → Src.Slot → Prop
  | box {s : Src.Slot} : IrrSlot s → RefSlot I G ls ρ ρ'' .box s
  | lvl {l : Nat} {v : Src.Value} {v' : Val} :
      l < ρ''.length → ρ''[ρ''.length - 1 - l]? = some (.val v') → VR I G v v' →
      RefSlot I G ls ρ ρ'' (.lvl l) (.val v)
  | name {a : Src.Term} : RefSlot I G ls ρ ρ'' (.name a) (.name a ρ ls)

/-- The references agree with the slots wherever the head reads. -/
structure FormArgs (I : Input) (G : Key.GKey → GlobalId → Prop) (h : Head) (ls : Levels)
    (ρ : Src.Env) (ρ'' : Env) (refs : List Ref) (ss : List Src.Slot) : Prop where
  length : ss.length = refs.length
  at_ : ∀ i ref s, refs[i]? = some ref → ss[i]? = some s → headReads I h i = true →
    RefSlot I G ls ρ ρ'' ref s

/-- Reading a level reference is free and gives the related value. -/
theorem RefSlot.eval_lvl {P : Program} {ls : Levels} {ρ : Src.Env} {ρ'' : Env} {cx : Cx}
    {l : Nat} {s : Src.Slot} (h : RefSlot I G ls ρ ρ'' (.lvl l) s) (hd : cx.depth = ρ''.length)
    (k : Nat) :
    ∃ v v', s = .val v ∧ Lam.eval P k ρ'' (cx.lvl l) = .ok v' ∧ VR I G v v' := by
  cases h with
  | lvl _ hg hv =>
    refine ⟨_, _, rfl, ?_, hv⟩
    rw [Cx.lvl_eq, hd, Lam.eval_var_of P k ρ'' hg, Lam.force_val]

/-- A reference that is not a thunk evaluates freely to a value related to
its slot's (forced) value. -/
theorem RefSlot.eval_ref {P : Program} {p : Src.Program} {ls : Levels} {ρ : Src.Env} {ρ'' : Env}
    {cx : Cx} {ref : Ref} {s : Src.Slot} {e : Term} (h : RefSlot I G ls ρ ρ'' ref s)
    (hr : RefR I G cx ref e) (hn : ∀ a, ref ≠ .name a) (hd : cx.depth = ρ''.length) :
    ∃ v v', VR I G v v' ∧ ∀ k, Src.force p k s = .ok v ∧ Lam.eval P k ρ'' e = .ok v' := by
  cases hr with
  | box =>
    cases h with
    | box hs =>
      obtain ⟨t, ρ₀, ls₀, rfl⟩ := hs
      exact ⟨_, _, VR.irr, fun k => ⟨Src.force_val p k _, Lam.eval_box' P k ρ''⟩⟩
  | lvl =>
    cases h with
    | lvl _ hg hv =>
      exact ⟨_, _, hv, fun k => ⟨Src.force_val p k _,
        by rw [Cx.lvl_eq, hd, Lam.eval_var_of P k ρ'' hg, Lam.force_val]⟩⟩
  | name _ => exact absurd rfl (hn _)

namespace Setting

variable (S : Setting)

theorem isQuotCtor_iff (c : CId) :
    S.p.isQuotCtor c = true ↔ ∃ lv ty, S.p.decl? c = some (.quot .ctor lv ty) := by
  simp only [Src.Program.isQuotCtor]
  split
  · next lv ty h => exact ⟨fun _ => ⟨lv, ty, h⟩, fun _ => rfl⟩
  · next h =>
    constructor
    · intro h'; cases h'
    · rintro ⟨lv, ty, h'⟩; exact absurd h' (h lv ty)

theorem vr_quot_inv {c : CId} {ls : Levels} {ps : List Src.Slot} {a : Src.Value} {v' : Val}
    {lv : Nat} {ty : Src.Term} (hq : S.I.decl? c = some (.quot .ctor lv ty))
    (h : VR S.I S.G (.con c ls ps [a]) v') : VR S.I S.G a v' := by
  cases h with
  | quot _ ha => exact ha
  | unboxed hd => rw [hq] at hd; cases hd
  | con hd => rw [hq] at hd; cases hd

/-- `Quot.mk α r a`: its element. -/
theorem quotMk_form {m : Nat} {c : CId} {lv : Nat} {ty : Src.Term}
    (hq : S.I.decl? c = some (.quot .ctor lv ty)) {ls ls' : Levels} {ρ : Src.Env} {ρ'' : Env}
    {cx : Cx} (hd : cx.depth = ρ''.length) {α r a : Src.Slot} {ref : Ref} {e : Term}
    (hs : RefSlot S.I S.G ls ρ ρ'' ref a) (hr : RefR S.I S.G cx ref e) (hn : ∀ a, ref ≠ .name a) :
    SimUpTo (VR S.I S.G) m (fun k => Src.fire S.p k (.quotMk c) ls' [α, r, a])
      (fun k => Lam.eval S.L k ρ'' e) := by
  obtain ⟨v, v', hvv, hk⟩ := hs.eval_ref hr hn hd (P := S.L) (p := S.p)
  refine (SimUpTo.ok (VR.quot (ls := ls') (ps := [α, r]) hq hvv)).congr (fun k => ?_)
    (fun k => (hk k).2)
  rw [Src.fire_quotMk]; dsimp only; rw [(hk k).1]; rfl

section

variable {S} {m : Nat} (hlt : ∀ m' < m, S.Level m')
include hlt

/-- `Quot.lift α r β f h q`: after the charge, `f` applied to `q`'s element. -/
theorem quotLift_form {c : CId} {ls ls' : Levels} {ρ : Src.Env} {ρ'' : Env} {cx : Cx}
    (hd : cx.depth = ρ''.length) {α r β fs h qs : Src.Slot} {reff refq : Ref} {f x : Term}
    (hsf : RefSlot S.I S.G ls ρ ρ'' reff fs) (hrf : RefR S.I S.G cx reff f)
    (hnf : ∀ a, reff ≠ .name a) (hsq : RefSlot S.I S.G ls ρ ρ'' refq qs)
    (hrq : RefR S.I S.G cx refq x) (hnq : ∀ a, refq ≠ .name a) :
    SimUpTo (VR S.I S.G) m (fun k => Src.fire S.p k (.quotLift c) ls' [α, r, β, fs, h, qs])
      (fun k => Lam.eval S.L k ρ'' (.tick (.app f x .strict))) := by
  obtain ⟨fv, fv', hfv, hkf⟩ := hsf.eval_ref hrf hnf hd (P := S.L) (p := S.p)
  obtain ⟨qv, qv', hqv, hkq⟩ := hsq.eval_ref hrq hnq hd (P := S.L) (p := S.p)
  refine (SimUpTo.later (n := m) (c₁ := fun k =>
      match qv with
      | .con c' _ _ [a] => if S.p.isQuotCtor c' then Src.apply S.p k fv (.val a) else .stuck
      | _ => .stuck)
    (c₂ := fun k => Lam.apply S.L k fv' (.val qv')) fun m' hm' => ?_).congr
    (fun k => ?_) (fun k => ?_)
  · have hap : S.ApplySim m' := (hlt m' (by omega)).apply
    cases qv with
    | con c' ls₀ ps fs₀ =>
      match fs₀ with
      | [a] =>
        dsimp only
        by_cases hq : S.p.isQuotCtor c' = true
        · simp only [hq, ↓reduceIte]
          obtain ⟨lv, ty, hdq⟩ := (S.isQuotCtor_iff c').1 hq
          exact hap hfv (SR.val (S.vr_quot_inv hdq hqv)) (.inr ⟨_, _, rfl, rfl⟩)
        · simp only [hq, Bool.false_eq_true, ↓reduceIte]
          exact SimUpTo.stuck _
      | [] | _ :: _ :: _ => exact SimUpTo.stuck _
    | _ => exact SimUpTo.stuck _
  · rw [Src.fire_quotLift]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ]
      rw [(hkq k).1]
      cases qv with
      | con c' ls₀ ps fs₀ =>
        match fs₀ with
        | [a] =>
          simp only [Sem.Result.bind_ok]
          split
          · rw [(hkf k).1, Sem.Result.bind_ok]
          · rfl
        | [] | _ :: _ :: _ => rfl
      | _ => rfl
  · rw [Lam.eval_tick]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ]
      rw [Lam.eval_app_strict, (hkf k).2, Sem.Result.bind_ok, (hkq k).2, Sem.Result.bind_ok]

end

end Setting

end Compilatrix.Lam.Erase.Proof
