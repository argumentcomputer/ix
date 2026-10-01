import Compilatrix.Fir.Proof.Env
import Compilatrix.Sem.Bind

/-! # One Anf outcome against a Fir computation

`Corr A N a D ra cf`: Anf's outcome `ra` at clock `a` against Fir's
computation `cf` (a function of Fir's clock), as `Fir.convert_correct`
needs it (06 S31):

* **forward at the same clock:** a value at `a` is a related Fir value at
  `a`, a trap a trap (Fir charges a subset of Anf's events, so it runs at
  least as far at the same depth clock);
* **timeout with the tick bound:** a timeout at `a` is a Fir timeout at
  every `k` with `N·k + D ≤ a`, where `D` bounds the Anf-only charges
  (ticks, non-recursive jumps, the jump entering a recursive join point)
  still ahead before the next Fir charge, and `N` bounds them between two
  Fir charges.

The combinators follow the evaluators' bind-form equations (decision D-1):
sequencing (`bind`), an Anf-only charge (`tick`), a charge on both sides
(`charge`), and the constant-tail of a tail call through ticks
(`bindTail`). Also: Fir's run of a `case` arm's projections
(`projections_run`) and the environment it leaves (`EnvR.arm`). -/

set_option autoImplicit false

namespace Compilatrix.Fir.Proof

open Compilatrix.Sem (Result later ClockMono)
open Compilatrix.Fir.Lower

/-- Anf's outcome at clock `a` against a Fir computation (see the module
comment). -/
structure Corr (A : Anf.Program) (N a D : Nat) (ra : Result Anf.Val) (cf : Nat → Result Val) : Prop where
  ok : ∀ v, ra = .ok v → ∃ w, cf a = .ok w ∧ VR A v w
  trap : ra = .trap → cf a = .trap
  res : ∀ f, ra = .resource f → cf a = .resource f
  tmo : ra = .timeout → ∀ k, N * k + D ≤ a → cf k = .timeout

namespace Corr

variable {A : Anf.Program} {N a D : Nat} {ra : Result Anf.Val} {cf : Nat → Result Val}

theorem stuck (cf : Nat → Result Val) : Corr A N a D .stuck cf where
  ok _ h := nomatch h
  trap h := nomatch h
  res _ h := nomatch h
  tmo h := nomatch h

theorem okv {v : Anf.Val} {w : Val} (hvw : VR A v w) (hc : cf a = .ok w) : Corr A N a D (.ok v) cf where
  ok _ h := by cases h; exact ⟨w, hc, hvw⟩
  trap h := nomatch h
  res _ h := nomatch h
  tmo h := nomatch h

theorem trapv (hc : cf a = .trap) : Corr A N a D .trap cf where
  ok _ h := nomatch h
  trap _ := hc
  res _ h := nomatch h
  tmo h := nomatch h

theorem weaken {D' : Nat} (h : Corr A N a D ra cf) (hD : D ≤ D') : Corr A N a D' ra cf where
  ok := h.ok
  trap := h.trap
  res := h.res
  tmo ht k hk := h.tmo ht k (by omega)

theorem congr {cf' : Nat → Result Val} (h : Corr A N a D ra cf) (hc : ∀ k, cf' k = cf k) :
    Corr A N a D ra cf' where
  ok v hv := by rw [hc]; exact h.ok v hv
  trap ht := by rw [hc]; exact h.trap ht
  res f hf := by rw [hc]; exact h.res f hf
  tmo ht k hk := by rw [hc]; exact h.tmo ht k hk

theorem ofEq {ra' : Result Anf.Val} (h : Corr A N a D ra cf) (e : ra' = ra) : Corr A N a D ra' cf :=
  e ▸ h

/-- A partial step on the Anf side: `none` is stuck. -/
theorem ofOption {α : Type} {o : Option α} {f : α → Result Anf.Val}
    (h : ∀ x, o = some x → Corr A N a D (f x) cf) : Corr A N a D ((Result.ofOption o).bind f) cf := by
  cases o with
  | none => exact stuck cf
  | some x => exact h x rfl

/-- Sequencing: the first computation is matched with no Anf-only charge
ahead (it ends in a Fir charge or a value), and Fir is clock monotone. -/
theorem bind (hN : 0 < N) {r : Result Anf.Val} {f : Anf.Val → Result Anf.Val}
    {c : Nat → Result Val} {g : Val → Nat → Result Val} (hc : ClockMono c) (h₁ : Corr A N a 0 r c)
    (h₂ : ∀ v w, r = .ok v → c a = .ok w → VR A v w → Corr A N a D (f v) (g w)) :
    Corr A N a D (r.bind f) (fun k => (c k).bind fun w => g w k) where
  ok v' hv' := by
    obtain ⟨v, hr, hf⟩ := Result.bind_eq_ok_iff.1 hv'
    obtain ⟨w, hw, hvw⟩ := h₁.ok v hr
    obtain ⟨w', hw', hvw'⟩ := (h₂ v w hr hw hvw).ok v' hf
    exact ⟨w', by simp only [hw, Result.bind_ok]; exact hw', hvw'⟩
  trap ht := by
    rcases Result.bind_eq_trap_iff.1 ht with hr | ⟨v, hr, hf⟩
    · simp only [h₁.trap hr]; rfl
    · obtain ⟨w, hw, hvw⟩ := h₁.ok v hr
      simp only [hw, Result.bind_ok]
      exact (h₂ v w hr hw hvw).trap hf
  res fl hr' := by
    rcases Result.bind_eq_resource_iff.1 hr' with hr | ⟨v, hr, hf⟩
    · simp only [h₁.res fl hr]; rfl
    · obtain ⟨w, hw, hvw⟩ := h₁.ok v hr
      simp only [hw, Result.bind_ok]
      exact (h₂ v w hr hw hvw).res fl hf
  tmo ht k hk := by
    rcases Result.bind_eq_timeout_iff.1 ht with hr | ⟨v, hr, hf⟩
    · simp only [h₁.tmo hr k (by omega)]; rfl
    · obtain ⟨w, hw, hvw⟩ := h₁.ok v hr
      have hka : k ≤ a := by
        have : k ≤ N * k := Nat.le_mul_of_pos_left k hN
        omega
      by_cases hck : c k = .timeout
      · simp only [hck]; rfl
      · rw [show c k = .ok w by rw [← hw]; exact (hc hka hck).symm, Result.bind_ok]
        exact (h₂ v w hr hw hvw).tmo hf k hk

/-- An Anf-only charge (a tick, a non-recursive jump, the jump entering a
recursive join point): Fir runs on at the same clock. -/
theorem tick {r : Nat → Result Anf.Val} (hc : ClockMono cf)
    (h : ∀ a', a = a' + 1 → Corr A N a' D (r a') cf) : Corr A N a (D + 1) (later a r) cf := by
  cases a with
  | zero =>
    refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), (fun _ h => nomatch h), fun _ k hk => ?_⟩
    omega
  | succ a' =>
    have h' := h a' rfl
    refine ⟨fun v hv => ?_, fun ht => ?_, fun fl hr => ?_, fun ht k hk => h'.tmo ht k (by omega)⟩
    · obtain ⟨w, hw, hvw⟩ := h'.ok v hv
      exact ⟨w, hc.ok (Nat.le_succ a') hw, hvw⟩
    · rw [hc (Nat.le_succ a') (by rw [h'.trap ht]; simp)]; exact h'.trap ht
    · rw [hc (Nat.le_succ a') (by rw [h'.res fl hr]; simp)]; exact h'.res fl hr

/-- A charge on both sides (a call, a recursive jump inside its own body):
the rest runs one clock down on each, with fewer than `N` Anf-only charges
ahead. -/
theorem charge {r : Nat → Result Anf.Val} (hD : D < N)
    (h : ∀ a', a = a' + 1 → Corr A N a' D (r a') cf) : Corr A N a 0 (later a r) (fun k => later k cf) := by
  cases a with
  | zero =>
    refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), (fun _ h => nomatch h), fun _ k hk => ?_⟩
    have : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · have := Nat.mul_le_mul_left N h; omega
    subst this; rfl
  | succ a' =>
    have h' := h a' rfl
    refine ⟨fun v hv => h'.ok v hv, fun ht => h'.trap ht, fun fl hr => h'.res fl hr, fun ht k hk => ?_⟩
    cases k with
    | zero => rfl
    | succ k => exact h'.tmo ht k (by rw [Nat.mul_succ] at hk; omega)

/-- A tail call through `m` ticks: the call's value is returned once the
ticks pass. -/
theorem bindTail {m : Nat} {r : Result Anf.Val} (h : Corr A N a 0 r cf) :
    Corr A N a m (r.bind fun v => if m ≤ a then .ok v else .timeout) cf where
  ok v' hv' := by
    obtain ⟨v, hr, hf⟩ := Result.bind_eq_ok_iff.1 hv'
    split at hf
    · cases hf; exact h.ok _ hr
    · cases hf
  trap ht := by
    rcases Result.bind_eq_trap_iff.1 ht with hr | ⟨v, _, hf⟩
    · exact h.trap hr
    · split at hf <;> cases hf
  res fl hr' := by
    rcases Result.bind_eq_resource_iff.1 hr' with hr | ⟨v, _, hf⟩
    · exact h.res fl hr
    · split at hf <;> cases hf
  tmo ht k hk := by
    rcases Result.bind_eq_timeout_iff.1 ht with hr | ⟨v, _, hf⟩
    · exact h.tmo hr k (by omega)
    · split at hf
      · cases hf
      · omega

end Corr

/-! ## A `case` arm's projections -/

theorem projections_run (F : Program) {y : Var} {key : Key.CtorKey} {body : Anf.Exp} {wv : Val}
    {ws : List Val} (has : wv.asCtor F.known = some (key, ws)) (Jf : List JEntry) (b : Code) :
    ∀ (fs : List Var) (i : Nat) (ρf : Env), ρf.get? y = some wv → y ∉ fs → fs.Nodup →
      i + fs.length = ws.length →
      ∃ ρf', (∀ k, eval F k ρf Jf (projections y key body fs i b) = eval F k ρf' Jf b) ∧
        (∀ x, x ∉ fs → ρf'.get? x = ρf.get? x) ∧
        (∀ j x, fs[j]? = some x → 0 < body.occ (fs.length - 1 - j) → ρf'.get? x = ws[i + j]?)
  | [], i, ρf, _, _, _, _ => ⟨ρf, fun _ => rfl, fun _ _ => rfl, fun _ _ h => by simp at h⟩
  | f :: fs, i, ρf, hy, hyfs, hnd, hlen => by
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons, not_or] at hyfs
    have hproj : projections y key body (f :: fs) i b =
        if body.occ fs.length > 0 then .bind f (.proj y key i) (projections y key body fs (i + 1) b)
        else projections y key body fs (i + 1) b := by
      simp only [projections]
      rw [show fs.length + i + 1 - 1 - i = fs.length by omega]
    have hi : i < ws.length := by simp at hlen; omega
    obtain ⟨wf, hwf⟩ : ∃ wf, ws[i]? = some wf := ⟨ws[i], by simp [hi]⟩
    by_cases hu : body.occ fs.length > 0
    · have hy' : (ρf.insert f wf).get? y = some wv := by
        rw [Src.NatMap.get?_insert_ne _ _ hyfs.1]; exact hy
      obtain ⟨ρf', hrun, hkeep, hset⟩ :=
        projections_run F has Jf b fs (i + 1) (ρf.insert f wf) hy' hyfs.2 hnd.2 (by simp at hlen ⊢; omega)
      refine ⟨ρf', fun k => ?_, fun x hx => ?_, fun j x hj hocc => ?_⟩
      · rw [hproj]; simp only [hu, ↓reduceIte]; rw [eval_bind_proj, evalRhs_proj, hy]
        simp only [Result.ofOption, Result.bind_ok, projVal, has, ↓reduceIte, hwf]
        exact hrun k
      · simp only [List.mem_cons, not_or] at hx
        rw [hkeep x hx.2, Src.NatMap.get?_insert_ne _ _ hx.1]
      · cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          rw [hkeep f hnd.1, Src.NatMap.get?_insert_self, Nat.add_zero, hwf]
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          rw [hset j x hj (by rw [Nat.sub_sub, Nat.add_comm]; simpa using hocc)]
          congr 1
          omega
    · obtain ⟨ρf', hrun, hkeep, hset⟩ :=
        projections_run F has Jf b fs (i + 1) ρf hy hyfs.2 hnd.2 (by simp at hlen ⊢; omega)
      refine ⟨ρf', fun k => ?_, fun x hx => ?_, fun j x hj hocc => ?_⟩
      · rw [hproj]; simp only [hu, ↓reduceIte]; exact hrun k
      · simp only [List.mem_cons, not_or] at hx
        exact hkeep x hx.2
      · cases j with
        | zero => simp at hocc; omega
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          rw [hset j x hj (by rw [Nat.sub_sub, Nat.add_comm]; simpa using hocc)]
          congr 1
          omega

/-- The environment an arm's body runs in: the used fields bound to the
scrutinee's fields, everything else as before. -/
theorem EnvR.arm {A : Anf.Program} {live : Nat → Prop} {n : Nat} {ρ : List Var}
    {ρa : List Anf.Val} {ρf ρf' : Env} (h : EnvR A (fun i => live (i + n)) ρ ρa ρf) {fs : List Var}
    (hfresh : ∀ x ∈ fs, x ∉ ρ) (hn : fs.length = n) {vs : List Anf.Val} {ws : List Val}
    (hvs : VRs A vs ws) (hvl : vs.length = n) (hkeep : ∀ x, x ∉ fs → ρf'.get? x = ρf.get? x)
    (hset : ∀ j x, fs[j]? = some x → live (n - 1 - j) → ρf'.get? x = ws[j]?) :
    EnvR A live (fs.reverse ++ ρ) (vs.reverse ++ ρa) ρf' := by
  refine ⟨by simp [h.1, hn, hvl], fun i x v hi hx hv => ?_⟩
  by_cases hin : i < n
  · rw [List.getElem?_append_left (by simpa [hn] using hin), List.getElem?_reverse (by omega)] at hx
    rw [List.getElem?_append_left (by simpa [hvl] using hin), List.getElem?_reverse (by omega)] at hv
    rw [hn] at hx
    rw [hvl] at hv
    obtain ⟨w, hw, hvw⟩ := hvs.get hv
    refine ⟨w, ?_, hvw⟩
    rw [hset (n - 1 - i) x hx (by rw [show n - 1 - (n - 1 - i) = i by omega]; exact hi)]
    exact hw
  · rw [List.getElem?_append_right (by simp [hn]; omega)] at hx
    rw [List.getElem?_append_right (by simp [hvl]; omega)] at hv
    simp only [List.length_reverse, hn, hvl] at hx hv
    obtain ⟨w, hw, hvw⟩ := h.2 (i - n) x v (by simpa [Nat.sub_add_cancel (by omega : n ≤ i)] using hi)
      hx hv
    have hxfs : x ∉ fs := fun hm => hfresh x hm (List.mem_of_getElem? hx)
    exact ⟨w, by rw [hkeep x hxfs]; exact hw, hvw⟩

end Compilatrix.Fir.Proof
