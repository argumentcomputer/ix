import IxCC.Lam.Erase.Proof.Rel
import IxCC.Src.Proof.Spine
import IxCC.Src.Proof.Mono
import IxCC.Lam.Proof.Spine

/-! # The erasure simulation: setting, environments, slots and β

The simulation is proved one clock bound at a time
(`Sem.SimUpTo`): `TRSim S m` says every erasure `TR cx t t'` simulates, up to
clock `m`, from related environments; `ApplySim S m` says applying related
values to related slots does. This module fixes the setting (a Src program,
its checked annotation, an erased program whose globals are described by
`ProgR`), the environment lemmas, and the cases that need only lower clock
bounds: forcing a slot and entering a closure (β). -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later)

/-- What the simulation is about: a Src program and its checked
annotation, and an erased program described by `ProgR` through `G`. -/
structure Setting where
  p : Src.Program
  ch : Src.Relevance.Checked
  L : Program
  G : Key.GKey → GlobalId → Prop
  prog : ProgR (Input.ofProgram p ch) G L
  known : L.known = (Input.ofProgram p ch).lamKnown
  /-- Erasure's `erase-pin` check: `Nat.succ`'s field is kept. -/
  succKept : ∀ s, p.known.natSucc = some s → (Input.ofProgram p ch).kept s [] 0 = true

namespace Setting

variable (S : Setting)

abbrev I : Input := Input.ofProgram S.p S.ch

/-- Every erasure simulates up to clock `m`, from related environments. -/
def TRSim (m : Nat) : Prop :=
  ∀ {cx : Cx} {t : Src.Term} {t' : Term}, TR S.I S.G cx t t' →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
      SimUpTo (VR S.I S.G) m (fun k => Src.eval S.p k ls ρ t) (fun k => Lam.eval S.L k ρ' t')

/-- An application whose argument may be a thunk only if the function is a
closure (by-name arguments meet only λ binders). -/
def Applicable (f : Src.Value) (s : Src.Slot) (s' : Slot) : Prop :=
  (∃ b d body ρ ls, f = .clo b d body ρ ls) ∨ ∃ v v', s = .val v ∧ s' = .val v'

/-- Applying related values to related slots simulates up to clock `m`. -/
def ApplySim (m : Nat) : Prop :=
  ∀ {f : Src.Value} {f' : Val} {s : Src.Slot} {s' : Slot}, VR S.I S.G f f' → SR S.I S.G s s' →
    Applicable f s s' →
    SimUpTo (VR S.I S.G) m (fun k => Src.apply S.p k f s) (fun k => Lam.apply S.L k f' s')

/-- Both, at clock bound `m`. -/
structure Level (m : Nat) : Prop where
  tr : S.TRSim m
  apply : S.ApplySim m

end Setting

/-! ## Environments -/

theorem lookup_mem {β : Type} : ∀ {xs : List (Nat × β)} {a : Nat} {b : β},
    xs.lookup a = some b → (a, b) ∈ xs
  | [], _, _, h => by simp [List.lookup] at h
  | (a', b') :: xs, a, b, h => by
    simp only [List.lookup] at h
    by_cases e : a = a'
    · subst e
      simp only [BEq.rfl, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · rw [show (a == a') = false from beq_false_of_ne e] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

section Env

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

theorem ER.get : ∀ {ctx : List (Option Nat)} {ρ : Src.Env} {ρ' : Env}, ER I G ctx ρ ρ' →
    ∀ {i : Nat} {l : Nat}, ctx[i]? = some (some l) →
      ∃ s s', ρ[i]? = some s ∧ ρ'[ρ'.length - 1 - l]? = some s' ∧ SR I G s s'
  | _, _, _, .nil, _, _, h => by simp at h
  | _, _, _, .lvl _ h₁ h₂ _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨_, _, rfl, h₁, h₂⟩
  | _, _, _, .lvl _ _ _ hr, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.get h
  | _, _, _, .box _ _, 0, _, h => by simp at h
  | _, _, _, .box _ hr, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.get h

theorem ER.getNone : ∀ {ctx : List (Option Nat)} {ρ : Src.Env} {ρ' : Env}, ER I G ctx ρ ρ' →
    ∀ {i : Nat}, ctx[i]? = some none → ∃ s, ρ[i]? = some s ∧ IrrSlot s
  | _, _, _, .nil, _, h => by simp at h
  | _, _, _, .lvl _ _ _ _, 0, h => by simp at h
  | _, _, _, .lvl _ _ _ hr, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.getNone h
  | _, _, _, .box hs _, 0, _ => ⟨_, rfl, hs⟩
  | _, _, _, .box _ hr, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.getNone h

theorem ER.length : ∀ {ctx : List (Option Nat)} {ρ : Src.Env} {ρ' : Env}, ER I G ctx ρ ρ' →
    ctx.length = ρ.length
  | _, _, _, .nil => rfl
  | _, _, _, .lvl _ _ _ hr => by simp [hr.length]
  | _, _, _, .box _ hr => by simp [hr.length]

/-- Lam binders pushed on top do not disturb the levels below. -/
theorem ER.extend (xs : List Slot) : ∀ {ctx : List (Option Nat)} {ρ : Src.Env} {ρ' : Env},
    ER I G ctx ρ ρ' → ER I G ctx ρ (xs ++ ρ')
  | _, _, _, .nil => .nil
  | _, _, ρ', .lvl (l := l) hl hg hs hr => by
    refine .lvl (by simp; omega) ?_ hs (hr.extend xs)
    have e : (xs ++ ρ').length - 1 - l = xs.length + (ρ'.length - 1 - l) := by simp; omega
    rw [e, List.getElem?_append_right (by omega)]
    simpa using hg
  | _, _, _, .box hs hr => .box hs (hr.extend xs)

theorem ER.extend1 (x : Slot) {ctx : List (Option Nat)} {ρ : Src.Env} {ρ' : Env}
    (h : ER I G ctx ρ ρ') : ER I G ctx ρ (x :: ρ') := h.extend [x]

theorem MinorsOk.extend {cx : Cx} {ρ : Src.Env} (n : Nat) (h : MinorsOk cx ρ) :
    MinorsOk (cx.extra n) ρ := h

theorem EnvR.bind {cx : Cx} {ρ : Src.Env} {ρ' : Env} {s : Src.Slot} {s' : Slot}
    (h : EnvR I G cx ρ ρ') (hs : SR I G s s') : EnvR I G cx.bind (s :: ρ) (s' :: ρ') where
  er := .lvl (by simp [h.depth]) (by simp [h.depth]) hs (h.er.extend1 s')
  depth := by simp [Cx.bind, h.depth]
  minors := by
    intro v l sig hv hl hn
    cases v with
    | zero =>
      simp only [Cx.bind, List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      have := h.minorsLt _ (lookup_mem hl)
      simp at this
    | succ v =>
      simp only [Cx.bind, List.getElem?_cons_succ] at hv ⊢
      exact h.minors v l sig hv hl hn
  minorsLt := fun e he => by
    have := h.minorsLt e he
    simp only [Cx.bind]
    omega

theorem EnvR.extra {cx : Cx} {ρ : Src.Env} {ρ' : Env} (h : EnvR I G cx ρ ρ') (xs : List Slot) :
    EnvR I G (cx.extra xs.length) ρ (xs ++ ρ') where
  er := h.er.extend xs
  depth := by simp [Cx.extra, h.depth, Nat.add_comm]
  minors := h.minors
  minorsLt := fun e he => by
    have := h.minorsLt e he
    simp only [Cx.extra]
    omega

theorem EnvR.extra1 {cx : Cx} {ρ : Src.Env} {ρ' : Env} (h : EnvR I G cx ρ ρ') (x : Slot) :
    EnvR I G (cx.extra 1) ρ (x :: ρ') := h.extra [x]

/-- The context of a constant's body: nothing bound. -/
theorem EnvR.empty (q : Profile) : EnvR I G (bodyCx q) [] [] where
  er := .nil
  depth := rfl
  minors := fun _ _ _ h => by simp [bodyCx] at h
  minorsLt := fun _ h => by simp [bodyCx] at h

theorem Cx.lvl_eq (cx : Cx) (l : Nat) : cx.lvl l = .var (cx.depth - 1 - l) := rfl

end Env

/-! ## Forcing and β -/

namespace Setting

variable (S : Setting)

theorem force_sim {m : Nat} (hlt : ∀ m' < m, S.TRSim m') {s : Src.Slot} {s' : Slot}
    (hs : SR S.I S.G s s') :
    SimUpTo (VR S.I S.G) m (fun k => Src.force S.p k s) (fun k => Lam.force S.L k s') := by
  cases hs with
  | val hv =>
    exact (SimUpTo.ok hv).congr (fun k => Src.force_val S.p k _) (fun k => Lam.force_val S.L k _)
  | name ht her hd hmo hml hag =>
    refine (SimUpTo.later fun m' hm' => ?_).congr (fun k => Src.force_name S.p k _ _ _)
      (fun k => Lam.force_name S.L k _ _)
    exact hlt m' (by omega) ht ⟨her, hd, hmo, hml⟩ hag
  | delayed hi hv =>
    refine (SimUpTo.laterR (Lam.eval_mono S.L _ _) ((SimUpTo.ok hv).congr (fun _ => rfl)
      (fun k => ?_))).congr (fun k => Src.force_val S.p k _) (fun k => Lam.force_name S.L k _ _)
    rw [Lam.eval_var, hi]; exact Lam.force_val S.L k _

/-- β: entering a closure charges one clock on both sides. -/
theorem apply_clo_sim {m : Nat} (hlt : ∀ m' < m, S.TRSim m') {b : Src.Binder}
    {d body : Src.Term} {ρ : Src.Env} {ls : Levels} {ρ' : Env} {body' : Term}
    (hf : VR S.I S.G (.clo b d body ρ ls) (.clos ρ' body')) {s : Src.Slot} {s' : Slot}
    (hs : SR S.I S.G s s') :
    SimUpTo (VR S.I S.G) m (fun k => Src.apply S.p k (.clo b d body ρ ls) s)
      (fun k => Lam.apply S.L k (.clos ρ' body') s') := by
  cases hf with
  | clo her hd hmo hml hag ht =>
    rename_i cx
    by_cases hb : b.propWhen.allowsBeta ls = true
    · refine (SimUpTo.later fun m' hm' => ?_).congr
        (fun k => by simp only [Src.apply_clo, hb, ↓reduceIte]; rfl)
        (fun k => by rw [Lam.apply_clos]; rfl)
      exact hlt m' (by omega) ht (EnvR.bind ⟨her, hd, hmo, hml⟩ hs) hag
    · refine (SimUpTo.stuck _).congr (fun k => by simp only [Src.apply_clo, hb, ↓reduceIte,
        Bool.false_eq_true]) (fun _ => rfl)

end Setting

end IxCC.Lam.Erase.Proof
