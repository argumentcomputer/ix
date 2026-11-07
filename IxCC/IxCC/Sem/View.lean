import IxCC.Sem.TracedTransform
import IxCC.Sem.SimUpTo

/-! # Viewing results at a root's type

Every Phase 1 level from SrcEval to Cfg observes a value
program-independently (`obsV`: literals, and constructor trees tagged by the
source constructor), and the levels' refinements (`Sem.Refines`) preserve
exactly that observation. The runtime reads a result word back at the
root's declared type (`Rt.readback`), by tag, and a word cannot tell a `Nat`
from a field-less constructor or □. A source run whose result is not of the
root's type (which Lean's typing excludes, but stage S's `Recheck.run`
does not check) can therefore read back as something else.

`Viewed S` runs a program of `S` on the shared input (root index, `Nat`
arguments) and passes each result's observation through a per-root view:
the observation the view reports (for example the source observation
relabelled by tags at the root's type), or `none` to reject it, which makes
the run **stuck**. A stuck source imposes nothing, so a rejected result is
one more way the source goes wrong (roadmap §1.1's `GoesWrong`, which at
stage S then also covers a result outside the root's type); every other
behaviour is the program's own.

`Viewed.refines`: a view keeps refinement, since it reads only the
observation, which refinement preserves (`behaviour_bind`). -/

set_option autoImplicit false

namespace IxCC.Sem

/-- A program whose results are observed through a per-root view (see the
module note). -/
structure Viewed (S : Type) where
  prog : S
  /-- For a root index and a result's observation: the observation reported,
  or `none` to reject the result (the run is then stuck). -/
  view : Nat → Option Obs → Option (Option Obs)

/-- A view applied to a result: the reported observation, or `stuck`. -/
def viewResult (V : Nat → Option Obs → Option (Option Obs)) (r : Nat) (o : Option Obs) : Result (Option Obs) :=
  match V r o with
  | some o' => .ok o'
  | none => .stuck

theorem viewResult_ne_timeout (V : Nat → Option Obs → Option (Option Obs)) (r : Nat) (o : Option Obs) :
    viewResult V r o ≠ .timeout := by
  unfold viewResult; split <;> simp

theorem viewResult_eq_ok {V : Nat → Option Obs → Option (Option Obs)} {r : Nat} {o o' : Option Obs} :
    viewResult V r o = .ok o' ↔ V r o = some o' := by
  unfold viewResult; split <;> rename_i h <;> simp [h]

theorem viewResult_eq_stuck {V : Nat → Option Obs → Option (Option Obs)} {r : Nat} {o : Option Obs} :
    viewResult V r o = .stuck ↔ V r o = none := by
  unfold viewResult; split <;> rename_i h <;> simp [h]

section

variable {S : Type} [Lang (Nat × List Nat) S]

/-- A run viewed: the program's run, then the view of its result. -/
def Viewed.run (s : Viewed S) (i : Nat × List Nat) (k : Nat) : Result (Option Obs) :=
  (Lang.run s.prog i k).bind fun v => viewResult s.view i.1 (Lang.obs v)

instance : Lang (Nat × List Nat) (Viewed S) where
  Val := Option Obs
  run := Viewed.run
  mono s i := ClockMono.bind (Lang.mono s.prog i) fun _ => ClockMono.const _
  obs := id

theorem Viewed.lang_run (s : Viewed S) (i : Nat × List Nat) : Lang.run s i = Viewed.run s i := rfl

theorem Viewed.lang_obs (o : Lang.Val (Viewed S)) : Lang.obs (S := Viewed S) o = o := rfl

end

/-! ## Behaviours under a view -/

/-- A behaviour followed by a step: a value's step, every other behaviour
kept. -/
def Behaviour.then {α β : Type} (b : Behaviour α) (g : α → Result β) : Behaviour β :=
  match b with
  | .terminates v => (g v).toBehaviour
  | .diverges => .diverges
  | .resource r => .resource r
  | .trap => .trap
  | .stuck => .stuck

/-- The behaviour of a run followed by a step that never times out. -/
theorem behaviour_bind {α β : Type} {c : Nat → Result α} (hc : ClockMono c) (g : α → Result β)
    (hg : ∀ v, g v ≠ .timeout) :
    behaviour (fun k => (c k).bind g) = (behaviour c).then g := by
  by_cases hex : ∃ k, c k ≠ .timeout
  · obtain ⟨k, hk⟩ := hex
    have hk' : (c k).bind g ≠ .timeout := by
      cases h : c k with
      | ok v => simpa using hg v
      | timeout => exact absurd h hk
      | _ => simp [Result.bind]
    rw [behaviour_of_ne_timeout (ClockMono.bind hc fun _ => ClockMono.const _) (k := k) hk',
      behaviour_of_ne_timeout hc hk]
    cases c k <;> rfl
  · have hall : ∀ k, c k = .timeout := fun k => Classical.byContradiction fun hk => hex ⟨k, hk⟩
    rw [behaviour_of_forall_timeout hall, behaviour_of_forall_timeout fun k => by rw [hall k]; rfl]
    rfl

namespace Viewed

variable {S T : Type} [Lang (Nat × List Nat) S] [Lang (Nat × List Nat) T]

theorem behaviour_eq (s : Viewed S) (i : Nat × List Nat) :
    Lang.behaviour s i = (Lang.behaviour s.prog i).then fun v => viewResult s.view i.1 (Lang.obs v) := by
  unfold Lang.behaviour
  change behaviour (fun k => (Lang.run s.prog i k).bind fun v => viewResult s.view i.1 (Lang.obs v)) = _
  exact behaviour_bind (Lang.mono s.prog i) (fun v => viewResult s.view i.1 (Lang.obs v))
    fun _ => viewResult_ne_timeout _ _ _

/-- **A view keeps refinement.** -/
theorem refines {s : S} {t : T} (h : Refines s t) (V : Nat → Option Obs → Option (Option Obs)) :
    Refines (⟨s, V⟩ : Viewed S) (⟨t, V⟩ : Viewed T) := by
  intro i
  rw [behaviour_eq, behaviour_eq]
  have hi := h i
  generalize Lang.behaviour s i = b₁ at hi ⊢
  generalize Lang.behaviour t i = b₂ at hi ⊢
  cases hi with
  | terminates hvw =>
    rename_i v w
    have : Lang.obs v = Lang.obs w := hvw
    simp only [Behaviour.then]
    rw [this]
    cases viewResult V i.1 (Lang.obs w) with
    | ok o => exact .terminates rfl
    | timeout => exact .diverges
    | resource r => exact .resource r
    | trap => exact .trap
    | stuck => exact .stuck
  | diverges => exact .diverges
  | trap => exact .trap
  | stuck => exact .stuck
  | resource failure => exact .resource failure

/-- `refines` in the traced shape (decision D-1). -/
theorem refines_traced {s : S} {t : T} (h : Refines s t) (V : Nat → Option Obs → Option (Option Obs)) :
    TRefines (⟨s, V⟩ : Viewed S) (⟨t, V⟩ : Viewed T) :=
  Refines.ofPure (refines h V)

/-- A viewed run returns the view of a result of the program's run. -/
theorem run_ok {s : Viewed S} {i : Nat × List Nat} {k : Nat} {o : Option Obs}
    (h : Lang.run s i k = .ok o) : ∃ v, Lang.run s.prog i k = .ok v ∧ s.view i.1 (Lang.obs v) = some o := by
  change (Lang.run s.prog i k).bind _ = _ at h
  cases hr : Lang.run s.prog i k with
  | ok v => rw [hr] at h; exact ⟨v, rfl, viewResult_eq_ok.1 h⟩
  | _ => rw [hr] at h; cases h

/-- A viewed run goes wrong exactly where the program's run does or the view
rejects its result. -/
theorem run_goesWrong {s : Viewed S} {i : Nat × List Nat} {k : Nat} :
    (Lang.run s i k).GoesWrong ↔ (Lang.run s.prog i k).GoesWrong ∨
      ∃ v, Lang.run s.prog i k = .ok v ∧ s.view i.1 (Lang.obs v) = none := by
  change ((Lang.run s.prog i k).bind _).GoesWrong ↔ _
  cases hr : Lang.run s.prog i k with
  | ok v =>
    simp only [Result.bind_ok, Result.not_goesWrong_ok, false_or, Result.ok.injEq, exists_eq_left']
    unfold viewResult
    split <;> rename_i h <;> simp [h, Result.GoesWrong]
  | timeout => simp [Result.bind, Result.GoesWrong]
  | resource r => simp [Result.bind, Result.GoesWrong]
  | trap => simp [Result.bind, Result.GoesWrong]
  | stuck => simp [Result.bind, Result.GoesWrong]

end Viewed

/-! ## Simulations for views and entries -/

/-- A source value is matched by a related target value or a target
resource failure. -/
theorem Result.Refines.ok_inv {α β : Type} {R : α → β → Prop} {v : α} {t : Result β}
    (h : Result.Refines R (.ok v) t) : (∃ w, t = .ok w ∧ R v w) ∨ ∃ failure, t = .resource failure := by
  cases h with
  | ok hvw => exact .inl ⟨_, rfl, hvw⟩
  | resource failure => exact .inr ⟨failure, rfl⟩

namespace Sim

variable {α β γ : Type} {R : α → β → Prop} {f : Nat → Nat} {c₁ : Nat → Result α} {c₂ : Nat → Result β}

/-- Constant outcomes, one refining the other. -/
theorem const_refines {r₁ : Result α} {r₂ : Result β} (h : Result.Refines R r₁ r₂) :
    Sim R f (fun _ => r₁) (fun _ => r₂) where
  forward _ _ := ⟨0, h⟩
  timeout _ ht := by
    have ht' : r₁ = .timeout := ht
    subst ht'
    exact Result.Refines.timeout_iff.1 h

/-- Charged constant outcomes, one refining the other, for a clock map that
is zero only at zero. -/
theorem later_refines {r₁ : Result α} {r₂ : Result β} (h : Result.Refines R r₁ r₂)
    (hf : ∀ k, f k = 0 → k = 0) :
    Sim R f (fun k => later k fun _ => r₁) (fun k => later k fun _ => r₂) where
  forward k hk := by
    cases k with
    | zero => exact absurd rfl hk
    | succ k => exact ⟨k + 1, h⟩
  timeout k ht := by
    cases k with
    | zero => exact .inl rfl
    | succ k =>
      change later (f (k + 1)) (fun _ => r₁) = .timeout at ht
      cases hfk : f (k + 1) with
      | zero => exact absurd (hf _ hfk) (Nat.succ_ne_zero k)
      | succ j =>
        rw [hfk] at ht
        change r₁ = .timeout at ht
        subst ht
        exact Result.Refines.timeout_iff.1 h

/-- A target that fails for a resource at every clock simulates anything. -/
theorem to_resource (r : Resource) : Sim R f c₁ (fun _ => .resource r) where
  forward _ _ := ⟨0, .resource r⟩
  timeout _ _ := .inr ⟨r, rfl⟩

/-- A source stuck at every clock is simulated by anything. -/
theorem of_stuck : Sim R f (fun _ => .stuck) c₂ where
  forward _ _ := ⟨0, .stuck⟩
  timeout _ ht := nomatch ht

/-- The target's values mapped. -/
theorem map_right (hs : Sim R f c₁ c₂) (h : β → γ) :
    Sim (fun a c => ∃ b, R a b ∧ c = h b) f c₁ (fun k => (c₂ k).map h) where
  forward k hk := by
    obtain ⟨k', hr⟩ := hs.forward k hk
    refine ⟨k', ?_⟩
    show Result.Refines _ (c₁ k) ((c₂ k').map h)
    generalize c₁ k = x at hr ⊢
    generalize c₂ k' = y at hr ⊢
    cases hr with
    | ok hab => exact .ok ⟨_, hab, rfl⟩
    | timeout => exact .timeout
    | trap => exact .trap
    | stuck => exact .stuck
    | resource failure => exact .resource failure
  timeout k ht := by
    rcases hs.timeout k ht with h' | ⟨failure, h'⟩
    · exact .inl (by simp only [h']; rfl)
    · exact .inr ⟨failure, by simp only [h']; rfl⟩

/-- A step after the source that never times out and is refined by every
related target value. -/
theorem bind_left {R' : γ → β → Prop} {g : α → Result γ} (hs : Sim R f c₁ c₂)
    (hg : ∀ v w, R v w → Result.Refines R' (g v) (.ok w)) (hgt : ∀ v, g v ≠ .timeout) :
    Sim R' f (fun k => (c₁ k).bind g) c₂ where
  forward k hk := by
    show ∃ k', Result.Refines R' ((c₁ k).bind g) (c₂ k')
    change (c₁ k).bind g ≠ .timeout at hk
    cases h₁ : c₁ k with
    | ok v =>
      obtain ⟨k', hr⟩ := hs.forward k (by rw [h₁]; simp)
      rw [h₁] at hr
      refine ⟨k', ?_⟩
      rw [Result.bind_ok]
      rcases hr.ok_inv with ⟨w, hw, hvw⟩ | ⟨fl, hw⟩
      · rw [hw]; exact hg _ _ hvw
      · rw [hw]; exact .resource fl
    | timeout => rw [h₁] at hk; exact absurd rfl hk
    | stuck => exact ⟨0, .stuck⟩
    | trap =>
      obtain ⟨k', hr⟩ := hs.forward k (by rw [h₁]; simp)
      rw [h₁] at hr
      refine ⟨k', ?_⟩
      rcases SimUpTo.refines_trap_inv hr with hw | ⟨fl, hw⟩
      · rw [hw]; exact .trap
      · rw [hw]; exact .resource fl
    | resource fl =>
      obtain ⟨k', hr⟩ := hs.forward k (by rw [h₁]; simp)
      rw [h₁] at hr
      obtain ⟨fl', h'⟩ := hr.of_resource
      exact ⟨k', by rw [h']; exact .resource fl'⟩
  timeout k ht := by
    apply hs.timeout k
    change (c₁ (f k)).bind g = .timeout at ht
    cases h₁ : c₁ (f k) with
    | ok v => rw [h₁, Result.bind_ok] at ht; exact absurd ht (hgt v)
    | timeout => rfl
    | _ => rw [h₁] at ht; cases ht

end Sim

/-- A charged outcome followed by a step. -/
theorem later_bind {α β : Type} (k : Nat) (c : Nat → Result α) (g : α → Result β) :
    (later k c).bind g = later k fun j => (c j).bind g := by
  cases k <;> rfl

/-- A run followed by `stuck`, then a step: `stuck` after the run. -/
theorem bind_stuck_bind {α β γ : Type} (r : Result α) (g : β → Result γ) :
    (r.bind fun _ => (Result.stuck : Result β)).bind g = r.bind fun _ => .stuck := by
  cases r <;> rfl

end IxCC.Sem
