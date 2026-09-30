import CompilatrixTests.Sem.Toy.Big
import Compilatrix.Sem.Smallstep

/-!
# Compiling the toy language to a small-step stack machine

The third level: a stack machine whose calls and ticks charge a *total*
clock, run by `Sem.runClocked`, and whose `add` fails with `natOverflow` at
2^64 (an extra target resource failure; the source has exact `Nat`).

- The runner's fuel suffices by a potential (`potential_ok`): the code size
  plus one more than the saved code size per frame. Free steps shrink it and
  a call raises it by at most the largest body, so `Stack.run` `Runs` and is
  clock monotone.
- `eval_fwd`: a source value is reached by the compiled code in any context,
  unless an `add` overflows on the way.
- `eval_timeout`: a source timeout at depth `k` gives a target run that
  spends more than `k` charges (or overflows); a depth-`k` call chain costs
  at least `k` charges in any total clock.
- `sim` assembles both through `Sim.ofStar`, with the identity clock map.
-/

namespace CompilatrixTests.Sem.Toy

open Compilatrix.Sem

inductive Instr where
  | push (n : Nat)
  | arg
  | add
  | sub
  /-- Pop `v`; continue with `t` if `v` is zero, else with `e`. -/
  | ifz (t e : List Instr)
  /-- Pop the argument and call function `f`; charges the clock. -/
  | call (f : Nat)
  /-- Charge the clock. -/
  | tick
  deriving Repr, Inhabited

namespace Stack

/-- Compiled function bodies; function 0 is `main`. -/
abbrev Program := List (List Instr)

/-- A saved caller: the code after the call and the caller's argument. -/
structure Frame where
  code : List Instr
  arg : Nat
  deriving Repr, Inhabited

structure State where
  code : List Instr
  stack : List Nat
  arg : Nat
  frames : List Frame
  deriving Repr, Inhabited

/-- `add` fails for a resource at this bound. -/
def limit : Nat := 2 ^ 64

def step (q : Program) : State → Step State Nat
  | ⟨[], v :: _, _, []⟩ => .done v
  | ⟨[], v :: st, _, fr :: frs⟩ => .next ⟨fr.code, v :: st, fr.arg, frs⟩ false
  | ⟨.push n :: c, st, x, fs⟩ => .next ⟨c, n :: st, x, fs⟩ false
  | ⟨.arg :: c, st, x, fs⟩ => .next ⟨c, x :: st, x, fs⟩ false
  | ⟨.add :: c, b :: a :: st, x, fs⟩ =>
      if a + b < limit then .next ⟨c, (a + b) :: st, x, fs⟩ false else .fail .natOverflow
  | ⟨.sub :: c, b :: a :: st, x, fs⟩ => .next ⟨c, (a - b) :: st, x, fs⟩ false
  | ⟨.ifz t e :: c, v :: st, x, fs⟩ => .next ⟨(if v = 0 then t else e) ++ c, st, x, fs⟩ false
  | ⟨.call f :: c, v :: st, x, fs⟩ =>
      match q[f]? with
      | some body => .next ⟨body, st, v, ⟨c, x⟩ :: fs⟩ true
      | none => .stuck
  | ⟨.tick :: c, st, x, fs⟩ => .next ⟨c, st, x, fs⟩ true
  | _ => .stuck

/-! ## Fuel -/

mutual
def instrSize : Instr → Nat
  | .ifz t e => 1 + codeSize t + codeSize e
  | _ => 1

def codeSize : List Instr → Nat
  | [] => 0
  | i :: c => instrSize i + codeSize c
end

theorem codeSize_append (c c' : List Instr) : codeSize (c ++ c') = codeSize c + codeSize c' := by
  induction c with
  | nil => simp [codeSize]
  | cons i c ih => simp only [List.cons_append, codeSize, ih]; omega

theorem instrSize_pos (i : Instr) : 0 < instrSize i := by
  cases i <;> simp [instrSize] <;> omega

def framesSize : List Frame → Nat
  | [] => 0
  | fr :: frs => codeSize fr.code + 1 + framesSize frs

/-- The potential: code size plus, per frame, one more than its code size. -/
def potential (s : State) : Nat := codeSize s.code + framesSize s.frames

/-- The largest body. -/
def maxBody : Program → Nat
  | [] => 0
  | c :: q => max (codeSize c) (maxBody q)

theorem codeSize_le_maxBody : ∀ {q : Program} {f : Nat} {body : List Instr},
    q[f]? = some body → codeSize body ≤ maxBody q
  | [], _, _, h => by simp at h
  | c :: q, 0, body, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [maxBody]; omega
  | c :: q, f + 1, body, h => by
    simp only [List.getElem?_cons_succ] at h
    have := codeSize_le_maxBody h
    simp only [maxBody]; omega

theorem potential_ok (q : Program) : Potential (step q) (fun _ => True) potential (maxBody q) where
  free := by
    intro s s' _ h
    refine ⟨trivial, ?_⟩
    unfold step at h
    split at h <;> (try split at h) <;>
      simp only [Step.next.injEq, reduceCtorEq, Bool.true_eq_false, and_false] at h
    all_goals
      obtain ⟨rfl, -⟩ := h
      simp only [potential, codeSize, framesSize, codeSize_append, instrSize]
      try split
      all_goals omega
  charge := by
    intro s s' _ h
    refine ⟨trivial, ?_⟩
    unfold step at h
    split at h <;> (try split at h) <;>
      simp only [Step.next.injEq, reduceCtorEq, Bool.false_eq_true, and_false] at h
    all_goals
      obtain ⟨rfl, -⟩ := h
      simp only [potential, codeSize, framesSize, instrSize]
      first
      | omega
      | (have := codeSize_le_maxBody ‹q[_]? = some _›; omega)

/-- Fuel for clock `k`: enough by `potential_ok` for a start at a body. -/
def fuel (q : Program) (k : Nat) : Nat := (k + 1) * (maxBody q + 1)

/-- Run `main` on `x` with clock `k`. -/
def run (q : Program) (x k : Nat) : Result Nat :=
  match q[0]? with
  | some main => runClocked (step q) (fuel q k) k ⟨main, [], x, []⟩
  | none => .stuck

/-- `run` is the clocked outcome of the machine from `main`. -/
theorem run_runs (q : Program) (x : Nat) {main : List Instr} (h : q[0]? = some main) :
    Runs (step q) ⟨main, [], x, []⟩ (run q x) := by
  have hr := (potential_ok q).runs (s := ⟨main, [], x, []⟩) trivial (fuel := fuel q) fun k => by
    have := codeSize_le_maxBody h
    simp only [potential, framesSize, fuel, Nat.succ_mul]
    omega
  intro k
  simp only [run, h]
  exact hr k

theorem run_mono (q : Program) (x : Nat) : ClockMono (run q x) := by
  cases h : q[0]? with
  | none =>
    have : run q x = fun _ => .stuck := funext fun _ => by simp [run, h]
    rw [this]
    exact ClockMono.const _
  | some main => exact (run_runs q x h).clockMono

end Stack

/-- The stack machine. -/
instance : Lang Nat Stack.Program where
  Val := Nat
  run := Stack.run
  mono := Stack.run_mono
  obs v := some (.nat v)

namespace Stack

open Big

/-! ## The compiler -/

def compile : Expr → List Instr
  | .lit n => [.push n]
  | .arg => [.arg]
  | .add a b => compile a ++ compile b ++ [.add]
  | .sub a b => compile a ++ compile b ++ [.sub]
  | .ifz c t e => compile c ++ [.ifz (compile t) (compile e)]
  | .call f a => compile a ++ [.call f]
  | .tick e => .tick :: compile e

def compileProg (p : Prog) : Program := p.map compile

theorem compileProg_get (p : Prog) (f : Nat) : (compileProg p)[f]? = (p[f]?).map compile := by
  simp [compileProg]

/-! ## Runs in context -/

/-- `s` reaches `s'`, or fails for a resource on the way. -/
def Goes (q : Program) (s s' : State) : Prop :=
  (∃ c, Star (step q) s c s') ∨ Fails (step q) s

/-- From `s` the machine spends more than `k` charges, or fails for a
resource. -/
def TimesOut (q : Program) (s : State) (k : Nat) : Prop :=
  ∃ c s', Star (step q) s c s' ∧ (k < c ∨ ∃ failure, step q s' = .fail failure)

section Goes

variable {q : Program} {s s' s'' : State}

theorem Goes.refl : Goes q s s := .inl ⟨0, .refl _⟩

theorem Goes.trans (h₁ : Goes q s s') (h₂ : Goes q s' s'') : Goes q s s'' := by
  rcases h₁ with ⟨c, h₁⟩ | hf
  · rcases h₂ with ⟨c', h₂⟩ | ⟨c', s₃, failure, h₂, hs⟩
    · exact .inl ⟨_, h₁.trans h₂⟩
    · exact .inr ⟨_, s₃, failure, h₁.trans h₂, hs⟩
  · exact .inr hf

theorem Goes.head {b : Bool} (hs : step q s = .next s' b) (h : Goes q s' s'') : Goes q s s'' :=
  Goes.trans (.inl ⟨_, Star.single hs⟩) h

theorem Goes.fail {failure : Resource} (hs : step q s = .fail failure) : Goes q s s' :=
  .inr ⟨0, s, failure, .refl _, hs⟩

theorem TimesOut.of_goes {k : Nat} (h₁ : Goes q s s') (h₂ : TimesOut q s' k) : TimesOut q s k := by
  rcases h₁ with ⟨c, h₁⟩ | ⟨c, s₃, failure, h₁, hs⟩
  · obtain ⟨c', s₃, h₂, hk⟩ := h₂
    refine ⟨c + c', s₃, h₁.trans h₂, ?_⟩
    rcases hk with hk | hk
    · exact .inl (by omega)
    · exact .inr hk
  · exact ⟨c, s₃, h₁, .inr ⟨failure, hs⟩⟩

theorem TimesOut.charge {k : Nat} (hs : step q s = .next s' true) (h : TimesOut q s' k) :
    TimesOut q s (k + 1) := by
  obtain ⟨c, s₃, hst, hk⟩ := h
  refine ⟨c + 1, s₃, .charge hs hst, ?_⟩
  rcases hk with hk | hk
  · exact .inl (by omega)
  · exact .inr hk

theorem TimesOut.charge_zero (hs : step q s = .next s' true) : TimesOut q s 0 :=
  ⟨1, s', .charge hs (.refl _), .inl (by omega)⟩

end Goes

/-! ## The source never traps or fails for a resource -/

/-- An outcome of the toy source: a value, a timeout or stuck. -/
def Basic : Result Nat → Prop
  | .ok _ | .timeout | .stuck => True
  | _ => False

theorem Basic.bind {r : Result Nat} {f : Nat → Result Nat} (hr : Basic r)
    (hf : ∀ v, Basic (f v)) : Basic (r.bind f) := by
  cases r <;> simp_all [Basic, Result.bind]

theorem evalAt_basic {p : Prog} {below : Nat → Expr → Result Nat} {x : Nat}
    (h : ∀ v e, Basic (below v e)) : ∀ e, Basic (evalAt p below x e)
  | .lit _ | .arg => trivial
  | .add a b | .sub a b => Basic.bind (evalAt_basic h a) fun _ =>
      Basic.bind (evalAt_basic h b) fun _ => by exact trivial
  | .ifz c t e => Basic.bind (evalAt_basic h c) fun v => by
      by_cases hv : v = 0
      · simp only [hv, ↓reduceIte]; exact evalAt_basic h t
      · simp only [hv, ↓reduceIte]; exact evalAt_basic h e
  | .call f a => Basic.bind (evalAt_basic h a) fun v => by
      unfold callAt
      split
      · exact h _ _
      · trivial
  | .tick e => h x e

theorem eval_basic (p : Prog) : ∀ k x e, Basic (eval p k x e)
  | 0, _, e => evalAt_basic (below := fun _ _ => .timeout) (fun _ _ => trivial) e
  | k + 1, _, e => evalAt_basic (fun v e => eval_basic p k v e) e

theorem bind_eq_ok {r : Result Nat} {f : Nat → Result Nat} {w : Nat} :
    r.bind f = .ok w ↔ ∃ v, r = .ok v ∧ f v = .ok w := by
  cases r <;> simp [Result.bind]

theorem bind_eq_timeout {r : Result Nat} {f : Nat → Result Nat} :
    r.bind f = .timeout ↔ r = .timeout ∨ ∃ v, r = .ok v ∧ f v = .timeout := by
  cases r <;> simp [Result.bind]

/-! ## Forward: values are reached -/

theorem evalAt_fwd {p : Prog} {below : Nat → Expr → Result Nat} {x : Nat} {q : Program}
    (hcall : ∀ f v w, callAt p below f v = .ok w → ∀ K st fs,
      Goes q ⟨.call f :: K, v :: st, x, fs⟩ ⟨K, w :: st, x, fs⟩)
    (htick : ∀ e w, below x e = .ok w → ∀ K st fs,
      Goes q ⟨.tick :: (compile e ++ K), st, x, fs⟩ ⟨K, w :: st, x, fs⟩) :
    ∀ e w, evalAt p below x e = .ok w → ∀ K st fs,
      Goes q ⟨compile e ++ K, st, x, fs⟩ ⟨K, w :: st, x, fs⟩
  | .lit n, w, h, K, st, fs => by
    cases h
    exact Goes.head (b := false) rfl Goes.refl
  | .arg, w, h, K, st, fs => by
    cases h
    exact Goes.head (b := false) rfl Goes.refl
  | .add a b, w, h, K, st, fs => by
    obtain ⟨va, ha, h⟩ := bind_eq_ok.1 h
    obtain ⟨vb, hb, h⟩ := bind_eq_ok.1 h
    cases h
    rw [show compile (.add a b) ++ K = compile a ++ (compile b ++ (.add :: K)) by
      simp [compile]]
    refine (evalAt_fwd hcall htick a va ha _ st fs).trans
      ((evalAt_fwd hcall htick b vb hb _ (va :: st) fs).trans ?_)
    by_cases hl : va + vb < limit
    · exact Goes.head (b := false) (by simp [step, hl]) Goes.refl
    · exact Goes.fail (failure := .natOverflow) (by simp [step, hl])
  | .sub a b, w, h, K, st, fs => by
    obtain ⟨va, ha, h⟩ := bind_eq_ok.1 h
    obtain ⟨vb, hb, h⟩ := bind_eq_ok.1 h
    cases h
    rw [show compile (.sub a b) ++ K = compile a ++ (compile b ++ (.sub :: K)) by
      simp [compile]]
    exact (evalAt_fwd hcall htick a va ha _ st fs).trans
      ((evalAt_fwd hcall htick b vb hb _ (va :: st) fs).trans
        (Goes.head (b := false) rfl Goes.refl))
  | .ifz c t e, w, h, K, st, fs => by
    obtain ⟨vc, hc, h⟩ := bind_eq_ok.1 h
    rw [show compile (.ifz c t e) ++ K = compile c ++ (.ifz (compile t) (compile e) :: K) by
      simp [compile]]
    refine (evalAt_fwd hcall htick c vc hc _ st fs).trans (Goes.head (b := false) rfl ?_)
    by_cases hv : vc = 0
    · simp only [hv, ↓reduceIte] at h ⊢
      exact evalAt_fwd hcall htick t w h K st fs
    · simp only [hv, ↓reduceIte] at h ⊢
      exact evalAt_fwd hcall htick e w h K st fs
  | .call f a, w, h, K, st, fs => by
    obtain ⟨va, ha, h⟩ := bind_eq_ok.1 h
    rw [show compile (.call f a) ++ K = compile a ++ (.call f :: K) by simp [compile]]
    exact (evalAt_fwd hcall htick a va ha _ st fs).trans (hcall f va w h K st fs)
  | .tick e, w, h, K, st, fs => htick e w h K st fs

/-- A source value is reached by the compiled code in any context, unless
an `add` overflows on the way. -/
theorem eval_fwd (p : Prog) : ∀ k x e w, eval p k x e = .ok w → ∀ K st fs,
    Goes (compileProg p) ⟨compile e ++ K, st, x, fs⟩ ⟨K, w :: st, x, fs⟩
  | 0, _, e, w, h => evalAt_fwd
      (fun f v w h => by unfold callAt at h; split at h <;> simp at h)
      (fun _ _ h => by simp at h) e w h
  | k + 1, x, e, w, h => evalAt_fwd
      (fun f v w h K st fs => by
        unfold callAt at h
        split at h
        · next body hbody =>
          have hq : (compileProg p)[f]? = some (compile body) := by
            simp [compileProg_get, hbody]
          refine Goes.head (b := true) (s' := ⟨compile body, st, v, ⟨K, x⟩ :: fs⟩)
            (by simp [step, hq]) ?_
          have := eval_fwd p k v body w h [] st (⟨K, x⟩ :: fs)
          rw [List.append_nil] at this
          exact this.trans (Goes.head (b := false) rfl Goes.refl)
        · simp at h)
      (fun e w h K st fs => Goes.head (b := true) rfl (eval_fwd p k x e w h K st fs)) e w h

/-! ## Timeout: a depth-`k` timeout spends more than `k` charges -/

theorem evalAt_timeout {p : Prog} {below : Nat → Expr → Result Nat} {x k : Nat} {q : Program}
    (hok : ∀ e w, evalAt p below x e = .ok w → ∀ K st fs,
      Goes q ⟨compile e ++ K, st, x, fs⟩ ⟨K, w :: st, x, fs⟩)
    (hcall : ∀ f v, callAt p below f v = .timeout → ∀ K st fs,
      TimesOut q ⟨.call f :: K, v :: st, x, fs⟩ k)
    (htick : ∀ e, below x e = .timeout → ∀ K st fs,
      TimesOut q ⟨.tick :: (compile e ++ K), st, x, fs⟩ k) :
    ∀ e, evalAt p below x e = .timeout → ∀ K st fs, TimesOut q ⟨compile e ++ K, st, x, fs⟩ k
  | .lit _, h, _, _, _ => by cases h
  | .arg, h, _, _, _ => by cases h
  | .add a b, h, K, st, fs => by
    rw [show compile (.add a b) ++ K = compile a ++ (compile b ++ (.add :: K)) by
      simp [compile]]
    rcases bind_eq_timeout.1 h with ha | ⟨va, ha, h⟩
    · exact evalAt_timeout hok hcall htick a ha _ st fs
    · rcases bind_eq_timeout.1 h with hb | ⟨_, _, h⟩
      · exact TimesOut.of_goes (hok a va ha _ st fs)
          (evalAt_timeout hok hcall htick b hb _ (va :: st) fs)
      · cases h
  | .sub a b, h, K, st, fs => by
    rw [show compile (.sub a b) ++ K = compile a ++ (compile b ++ (.sub :: K)) by
      simp [compile]]
    rcases bind_eq_timeout.1 h with ha | ⟨va, ha, h⟩
    · exact evalAt_timeout hok hcall htick a ha _ st fs
    · rcases bind_eq_timeout.1 h with hb | ⟨_, _, h⟩
      · exact TimesOut.of_goes (hok a va ha _ st fs)
          (evalAt_timeout hok hcall htick b hb _ (va :: st) fs)
      · cases h
  | .ifz c t e, h, K, st, fs => by
    rw [show compile (.ifz c t e) ++ K = compile c ++ (.ifz (compile t) (compile e) :: K) by
      simp [compile]]
    rcases bind_eq_timeout.1 h with hc | ⟨vc, hc, h⟩
    · exact evalAt_timeout hok hcall htick c hc _ st fs
    · refine TimesOut.of_goes (hok c vc hc _ st fs) (TimesOut.of_goes (Goes.head (b := false) rfl
        Goes.refl) ?_)
      by_cases hv : vc = 0
      · simp only [hv, ↓reduceIte] at h ⊢
        exact evalAt_timeout hok hcall htick t h K st fs
      · simp only [hv, ↓reduceIte] at h ⊢
        exact evalAt_timeout hok hcall htick e h K st fs
  | .call f a, h, K, st, fs => by
    rw [show compile (.call f a) ++ K = compile a ++ (.call f :: K) by simp [compile]]
    rcases bind_eq_timeout.1 h with ha | ⟨va, ha, h⟩
    · exact evalAt_timeout hok hcall htick a ha _ st fs
    · exact TimesOut.of_goes (hok a va ha _ st fs) (hcall f va h K st fs)
  | .tick e, h, K, st, fs => htick e h K st fs

/-- A source timeout at depth `k` gives a target run from the compiled code
that spends more than `k` charges, or overflows. -/
theorem eval_timeout (p : Prog) : ∀ k x e, eval p k x e = .timeout → ∀ K st fs,
    TimesOut (compileProg p) ⟨compile e ++ K, st, x, fs⟩ k
  | 0, x, e, h => evalAt_timeout (eval_fwd p 0 x)
      (fun f v h K st fs => by
        unfold callAt at h
        split at h
        · next body hbody =>
          have hq : (compileProg p)[f]? = some (compile body) := by
            simp [compileProg_get, hbody]
          exact TimesOut.charge_zero (s' := ⟨compile body, st, v, ⟨K, x⟩ :: fs⟩)
            (by simp [step, hq])
        · cases h)
      (fun e _ K st fs => TimesOut.charge_zero rfl) e h
  | k + 1, x, e, h => evalAt_timeout (eval_fwd p (k + 1) x)
      (fun f v h K st fs => by
        unfold callAt at h
        split at h
        · next body hbody =>
          have hq : (compileProg p)[f]? = some (compile body) := by
            simp [compileProg_get, hbody]
          refine TimesOut.charge (s' := ⟨compile body, st, v, ⟨K, x⟩ :: fs⟩)
            (by simp [step, hq]) ?_
          have := eval_timeout p k v body h [] st (⟨K, x⟩ :: fs)
          rwa [List.append_nil] at this
        · cases h)
      (fun e h K st fs => TimesOut.charge rfl (eval_timeout p k x e h K st fs)) e h

/-! ## The simulation and the pass -/

/-- The per-input simulation, with the identity clock map. -/
theorem sim (p : Prog) (x : Nat) : Sim Eq id (Big.run p x) (run (compileProg p) x) := by
  cases hmain : p[0]? with
  | none =>
    have h₁ : Big.run p x = fun _ => .stuck := funext fun _ => by simp [Big.run, hmain]
    have h₂ : run (compileProg p) x = fun _ => .stuck := funext fun _ => by
      simp [run, compileProg_get, hmain]
    rw [h₁, h₂]
    exact Sim.refl (fun _ => rfl) _
  | some main =>
    have hq : (compileProg p)[0]? = some (compile main) := by simp [compileProg_get, hmain]
    have hsrc : Big.run p x = fun k => eval p k x main := funext fun _ => by
      simp [Big.run, hmain]
    rw [hsrc]
    refine Sim.ofStar (run_runs _ x hq) ?_ ?_
    · intro k hk hs
      have hw : ∃ w, eval p k x main = .ok w := by
        have := eval_basic p k x main
        revert hk hs this
        cases eval p k x main <;> simp [Basic]
      obtain ⟨w, hw⟩ := hw
      rw [hw]
      rcases eval_fwd p k x main w hw [] [] [] with ⟨c, hst⟩ | ⟨c, s', failure, hst, hs'⟩
      · rw [List.append_nil] at hst
        exact ⟨c, _, _, hst, .done, .ok rfl⟩
      · rw [List.append_nil] at hst
        exact ⟨c, s', _, hst, hs' ▸ .fail, .resource failure⟩
    · intro k hk
      obtain ⟨c, s', hst, h⟩ := eval_timeout p k x main hk [] [] []
      rw [List.append_nil] at hst
      exact ⟨c, s', hst, h⟩

/-- Compilation to the stack machine as a pass (no certificate). -/
def transform : Transform Prog Program where
  name := "stack"
  pre _ := True
  run p _ := if p.isEmpty then .error "no main function" else .ok (compileProg p)
  post q := q ≠ []
  correct p _ q _ h := by
    split at h
    · cases h
    · next hp =>
      cases h
      refine ⟨by simpa [compileProg] using hp, ?_⟩
      exact Refines.of_sim (R := Eq) (fun _ _ h => h ▸ rfl) fun x => ⟨id, sim p x⟩

end Stack

end CompilatrixTests.Sem.Toy
