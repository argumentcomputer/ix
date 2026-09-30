import CompilatrixTests.Sem.Toy.IO.Big
import CompilatrixTests.Sem.Toy.IO.Runner

/-!
# Compiling the IO toy to a stack machine that performs the same events

The target of the IO toy: M2.1's stack machine (`Toy.Stack`), whose calls
and ticks charge a *total* clock and whose `add` fails with `natOverflow`
at 2^64, with two more instructions, `out` (pop a value and perform
`out v`) and `inp` (push the oracle's answer to the events so far and
perform `inp n`). A state carries its events; the run returns the events of
the state where it stopped (`runT`).

The simulation has the identity clock map (`sim`), and exercises the three
clauses of `TSim`:

- **forward** (`eval_fwd`): a source value is reached by the compiled code
  in any context with the same events appended, unless an `add` overflows
  after a prefix of them;
- **timeout** and **progress** (`eval_stop`): a source run that does not
  return a value (a timeout at depth `k`, or stuck) reaches a state with
  exactly the source's events, after more than `k` charges if it timed
  out, or fails for a resource after a prefix of them. More than `k`
  charges gives the timeout clause (the run at clock `k` stops on that path,
  after a prefix of the events); reaching the state gives progress (the run
  at a larger clock passes through it).
-/

namespace CompilatrixTests.Sem.Toy.IO

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
  /-- Pop `v` and perform `out v`. -/
  | out
  /-- Push the oracle's answer to the events so far, performing `inp`. -/
  | inp
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
  /-- The events performed so far. -/
  trace : List Ev
  deriving Repr

/-- `add` fails for a resource at this bound. -/
def limit : Nat := 2 ^ 64

def step (o : Oracle) (q : Program) : State → Step State Nat
  | ⟨[], v :: _, _, [], _⟩ => .done v
  | ⟨[], v :: st, _, fr :: frs, tr⟩ => .next ⟨fr.code, v :: st, fr.arg, frs, tr⟩ false
  | ⟨.push n :: c, st, x, fs, tr⟩ => .next ⟨c, n :: st, x, fs, tr⟩ false
  | ⟨.arg :: c, st, x, fs, tr⟩ => .next ⟨c, x :: st, x, fs, tr⟩ false
  | ⟨.add :: c, b :: a :: st, x, fs, tr⟩ =>
      if a + b < limit then .next ⟨c, (a + b) :: st, x, fs, tr⟩ false else .fail .natOverflow
  | ⟨.sub :: c, b :: a :: st, x, fs, tr⟩ => .next ⟨c, (a - b) :: st, x, fs, tr⟩ false
  | ⟨.ifz t e :: c, v :: st, x, fs, tr⟩ =>
      .next ⟨(if v = 0 then t else e) ++ c, st, x, fs, tr⟩ false
  | ⟨.call f :: c, v :: st, x, fs, tr⟩ =>
      match q[f]? with
      | some body => .next ⟨body, st, v, ⟨c, x⟩ :: fs, tr⟩ true
      | none => .stuck
  | ⟨.tick :: c, st, x, fs, tr⟩ => .next ⟨c, st, x, fs, tr⟩ true
  | ⟨.out :: c, v :: st, x, fs, tr⟩ => .next ⟨c, st, x, fs, tr ++ [.out v]⟩ false
  | ⟨.inp :: c, st, x, fs, tr⟩ => .next ⟨c, o tr :: st, x, fs, tr ++ [.inp (o tr)]⟩ false
  | _ => .stuck

/-- Every step extends the events. -/
theorem step_grows (o : Oracle) (q : Program) : Grows (step o q) State.trace := by
  intro s s' b h
  unfold step at h
  split at h <;> (try split at h) <;>
    simp only [Step.next.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨rfl, -⟩ := h
    simp

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

theorem potential_ok (o : Oracle) (q : Program) :
    Potential (step o q) (fun _ => True) potential (maxBody q) where
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

/-- Run `main` on `x` under oracle `o` with clock `k`, from no events. -/
def run (q : Program) (x : Nat) (o : Oracle) (k : Nat) : Traced Ev Nat :=
  match q[0]? with
  | some main => runT (step o q) State.trace (fuel q k) k ⟨main, [], x, [], []⟩
  | none => ⟨.stuck, []⟩

/-- `run` is the traced clocked outcome of the machine from `main`. -/
theorem run_runs (q : Program) (x : Nat) (o : Oracle) {main : List Instr}
    (h : q[0]? = some main) : RunsT (step o q) State.trace ⟨main, [], x, [], []⟩ (run q x o) := by
  intro k
  simp only [run, h]
  refine reachesT_runT State.trace (potential_ok o q) trivial ?_
  have := codeSize_le_maxBody h
  simp only [potential, framesSize, fuel, Nat.succ_mul]
  omega

theorem run_mono (q : Program) (x : Nat) (o : Oracle) : TraceMono (run q x o) := by
  cases h : q[0]? with
  | none =>
    have : run q x o = fun _ => ⟨.stuck, []⟩ := funext fun _ => by simp [run, h]
    rw [this]
    exact TraceMono.const _
  | some main => exact (run_runs q x o h).traceMono (step_grows o q)

end Stack

/-- The IO stack machine. -/
instance : TLang Oracle Ev Nat Stack.Program where
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
  | .out a e => compile a ++ .out :: compile e
  | .inp => [.inp]

def compileProg (p : Prog) : Program := p.map compile

theorem compileProg_get (p : Prog) (f : Nat) : (compileProg p)[f]? = (p[f]?).map compile := by
  simp [compileProg]

/-! ## Runs in context -/

section Goes

variable {o : Oracle} {q : Program}

/-- `s` reaches `s'`, or fails for a resource on the way after a prefix of
`s'`'s events. -/
def Goes (o : Oracle) (q : Program) (s s' : State) : Prop :=
  (∃ c, Star (step o q) s c s') ∨
    ∃ c s'' failure, Star (step o q) s c s'' ∧ step o q s'' = .fail failure ∧
      s''.trace <+: s'.trace

/-- From `s` the machine reaches a state whose events are `tr`, after more
than `k` charges if `deep`, or fails for a resource after a prefix of
`tr`. -/
def Stops (o : Oracle) (q : Program) (s : State) (tr : List Ev) (deep : Prop) (k : Nat) : Prop :=
  ∃ c s', Star (step o q) s c s' ∧
    ((s'.trace = tr ∧ (deep → k < c)) ∨
      ∃ failure, step o q s' = .fail failure ∧ s'.trace <+: tr)

variable {s s' s'' : State}

theorem Goes.refl : Goes o q s s := .inl ⟨0, .refl _⟩

theorem Goes.trace (h : Goes o q s s') : s.trace <+: s'.trace := by
  rcases h with ⟨c, h⟩ | ⟨c, s₃, _, h, _, hp⟩
  · exact Star.trace_prefix (step_grows o q) h
  · exact (Star.trace_prefix (step_grows o q) h).trans hp

theorem Goes.trans (h₁ : Goes o q s s') (h₂ : Goes o q s' s'') : Goes o q s s'' := by
  rcases h₁ with ⟨c, h₁⟩ | ⟨c, s₃, failure, h₁, hs, hp⟩
  · rcases h₂ with ⟨c', h₂⟩ | ⟨c', s₃, failure, h₂, hs, hp⟩
    · exact .inl ⟨_, h₁.trans h₂⟩
    · exact .inr ⟨_, s₃, failure, h₁.trans h₂, hs, hp⟩
  · exact .inr ⟨c, s₃, failure, h₁, hs, hp.trans h₂.trace⟩

theorem Goes.head {b : Bool} (hs : step o q s = .next s' b) (h : Goes o q s' s'') :
    Goes o q s s'' :=
  Goes.trans (.inl ⟨_, Star.single hs⟩) h

theorem Goes.fail {failure : Resource} (hs : step o q s = .fail failure)
    (hp : s.trace <+: s'.trace) : Goes o q s s' :=
  .inr ⟨0, s, failure, .refl _, hs, hp⟩

variable {tr : List Ev} {deep : Prop} {k : Nat}

theorem Stops.start_prefix (h : Stops o q s tr deep k) : s.trace <+: tr := by
  obtain ⟨c, s₃, hst, ⟨htr, _⟩ | ⟨_, _, hp⟩⟩ := h
  · exact htr ▸ Star.trace_prefix (step_grows o q) hst
  · exact (Star.trace_prefix (step_grows o q) hst).trans hp

theorem Stops.of_goes (h₁ : Goes o q s s') (h₂ : Stops o q s' tr deep k) : Stops o q s tr deep k := by
  rcases h₁ with ⟨c, h₁⟩ | ⟨c, s₃, failure, h₁, hs, hp⟩
  · obtain ⟨c', s₃, h₂, hk⟩ := h₂
    refine ⟨c + c', s₃, h₁.trans h₂, ?_⟩
    rcases hk with ⟨htr, hdeep⟩ | hf
    · exact .inl ⟨htr, fun hd => by have := hdeep hd; omega⟩
    · exact .inr hf
  · exact ⟨c, s₃, h₁, .inr ⟨failure, hs, hp.trans h₂.start_prefix⟩⟩

theorem Stops.charge (hs : step o q s = .next s' true) (h : Stops o q s' tr deep k) :
    Stops o q s tr deep (k + 1) := by
  obtain ⟨c, s₃, hst, hk⟩ := h
  refine ⟨c + 1, s₃, .charge hs hst, ?_⟩
  rcases hk with ⟨htr, hdeep⟩ | hf
  · exact .inl ⟨htr, fun hd => by have := hdeep hd; omega⟩
  · exact .inr hf

theorem Stops.charge_zero (hs : step o q s = .next s' true) (htr : s'.trace = tr) :
    Stops o q s tr deep 0 :=
  ⟨1, s', .charge hs (.refl _), .inl ⟨htr, fun _ => by omega⟩⟩

/-- A state with the source's events, when the source did not time out. -/
theorem Stops.here (htr : s.trace = tr) (hdeep : ¬ deep) : Stops o q s tr deep k :=
  ⟨0, s, .refl _, .inl ⟨htr, fun hd => absurd hd hdeep⟩⟩

end Goes

/-! ## Sequencing -/

section Bind

variable {o : Oracle} {q : Program} {α β : Type}

/-- A sequence that returns a value is reached through the state after its
first part. -/
theorem goes_bind {m : M α} {F : α → M β} {h : List Ev} {s₀ : State}
    {s₁ : α → List Ev → State} {s₂ : β → List Ev → State}
    (hm : ∀ v tr, m h = ⟨.ok v, tr⟩ → Goes o q s₀ (s₁ v (h ++ tr)))
    (hF : ∀ v tr, m h = ⟨.ok v, tr⟩ → ∀ w tr', F v (h ++ tr) = ⟨.ok w, tr'⟩ →
      Goes o q (s₁ v (h ++ tr)) (s₂ w (h ++ tr ++ tr')))
    {w : β} {tr : List Ev} (he : m.bind F h = ⟨.ok w, tr⟩) : Goes o q s₀ (s₂ w (h ++ tr)) := by
  obtain ⟨v, tr₁, tr₂, hm', hF', rfl⟩ := M.bind_eq_ok.1 he
  rw [← List.append_assoc]
  exact (hm v tr₁ hm').trans (hF v tr₁ hm' w tr₂ hF')

/-- A sequence that does not return a value stops in its first part, or in
its second after the state that follows the first. -/
theorem stops_bind {m : M α} {F : α → M β} {h : List Ev} {s₀ : State}
    {s₁ : α → List Ev → State} {k : Nat}
    (hm : ∀ v tr, m h = ⟨.ok v, tr⟩ → Goes o q s₀ (s₁ v (h ++ tr)))
    (hstop : (∀ v, (m h).result ≠ .ok v) →
      Stops o q s₀ (h ++ (m h).trace) ((m h).result = .timeout) k)
    (hF : ∀ v tr, m h = ⟨.ok v, tr⟩ → (∀ w, (F v (h ++ tr)).result ≠ .ok w) →
      Stops o q (s₁ v (h ++ tr)) (h ++ tr ++ (F v (h ++ tr)).trace)
        ((F v (h ++ tr)).result = .timeout) k)
    (hne : ∀ w, (m.bind F h).result ≠ .ok w) :
    Stops o q s₀ (h ++ (m.bind F h).trace) ((m.bind F h).result = .timeout) k := by
  rcases M.bind_stop hne with ⟨hm', htr, hiff⟩ | ⟨v, hv, hne', e⟩
  · rw [htr, hiff]
    exact hstop hm'
  · have hmv : m h = ⟨.ok v, (m h).trace⟩ := Traced.ext hv rfl
    rw [e]
    dsimp only
    rw [← List.append_assoc]
    exact Stops.of_goes (hm v _ hmv) (hF v _ hmv hne')

end Bind

/-! ## The source never traps or fails for a resource -/

/-- An outcome of the toy source: a value, a timeout or stuck. -/
def Basic {α : Type} : Result α → Prop
  | .ok _ | .timeout | .stuck => True
  | _ => False

theorem basic_bind {α β : Type} {m : M α} {F : α → M β} (hm : ∀ h, Basic (m h).result)
    (hF : ∀ v h, Basic (F v h).result) (h : List Ev) : Basic (m.bind F h).result := by
  have := hm h
  cases hr : (m h).result with
  | ok v => rw [M.bind_ok hr]; exact hF _ _
  | _ => rw [hr] at this; simp_all [M.bind, Basic]

theorem callAt_some {p : Prog} {below : Nat → Expr → M Nat} {f v : Nat} {body : Expr}
    (h : p[f]? = some body) : callAt p below f v = below v body := by
  simp [callAt, h]

theorem callAt_none {p : Prog} {below : Nat → Expr → M Nat} {f v : Nat} (h : p[f]? = none) :
    callAt p below f v = M.halt .stuck := by
  simp [callAt, h]

theorem evalAt_basic {o : Oracle} {p : Prog} {below : Nat → Expr → M Nat} {x : Nat}
    (hb : ∀ v e h, Basic (below v e h).result) : ∀ e h, Basic (evalAt o p below x e h).result
  | .lit _, _ | .arg, _ | .inp, _ => trivial
  | .add a b, h | .sub a b, h => by
      simp only [evalAt]
      exact basic_bind (evalAt_basic hb a) (fun _ =>
        basic_bind (evalAt_basic hb b) fun _ _ => by exact trivial) h
  | .ifz c t e, h => by
      simp only [evalAt]
      exact basic_bind (evalAt_basic hb c) (fun v h' => by
        by_cases hv : v = 0
        · simp only [hv, ↓reduceIte]; exact evalAt_basic hb t h'
        · simp only [hv, ↓reduceIte]; exact evalAt_basic hb e h') h
  | .call f a, h => by
      simp only [evalAt]
      exact basic_bind (evalAt_basic hb a) (fun v h' => by
        cases hf : p[f]? with
        | none => rw [callAt_none hf]; trivial
        | some body => rw [callAt_some hf]; exact hb _ _ _) h
  | .tick e, h => hb x e h
  | .out a e, h => by
      simp only [evalAt]
      exact basic_bind (evalAt_basic hb a) (fun _ =>
        basic_bind (fun _ => by exact trivial) fun _ => evalAt_basic hb e) h

theorem eval_basic (o : Oracle) (p : Prog) : ∀ k x e h, Basic (eval o p k x e h).result
  | 0, _, e, h => evalAt_basic (below := fun _ _ => M.halt .timeout) (fun _ _ _ => trivial) e h
  | k + 1, _, e, h => evalAt_basic (fun v e h => eval_basic o p k v e h) e h

/-! ## Forward: values are reached, with the same events -/

theorem evalAt_fwd {o : Oracle} {p : Prog} {below : Nat → Expr → M Nat} {x : Nat} {q : Program}
    (hcall : ∀ f v h w tr, callAt p below f v h = ⟨.ok w, tr⟩ → ∀ K st fs,
      Goes o q ⟨.call f :: K, v :: st, x, fs, h⟩ ⟨K, w :: st, x, fs, h ++ tr⟩)
    (htick : ∀ e h w tr, below x e h = ⟨.ok w, tr⟩ → ∀ K st fs,
      Goes o q ⟨.tick :: (compile e ++ K), st, x, fs, h⟩ ⟨K, w :: st, x, fs, h ++ tr⟩) :
    ∀ e h w tr, evalAt o p below x e h = ⟨.ok w, tr⟩ → ∀ K st fs,
      Goes o q ⟨compile e ++ K, st, x, fs, h⟩ ⟨K, w :: st, x, fs, h ++ tr⟩
  | .lit n, h, w, tr, he, K, st, fs => by
    cases he
    rw [List.append_nil]
    exact Goes.head (b := false) rfl Goes.refl
  | .arg, h, w, tr, he, K, st, fs => by
    cases he
    rw [List.append_nil]
    exact Goes.head (b := false) rfl Goes.refl
  | .inp, h, w, tr, he, K, st, fs => by
    cases he
    exact Goes.head (b := false) rfl Goes.refl
  | .add a b, h, w, tr, he, K, st, fs => by
    rw [show compile (.add a b) ++ K = compile a ++ (compile b ++ (.add :: K)) by simp [compile]]
    exact goes_bind (s₁ := fun va h' => ⟨compile b ++ (.add :: K), va :: st, x, fs, h'⟩)
      (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
      (fun va _ ha => evalAt_fwd hcall htick a _ va _ ha _ st fs)
      (fun va _ _ w _ hb => goes_bind
        (s₁ := fun vb h' => ⟨.add :: K, vb :: va :: st, x, fs, h'⟩)
        (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
        (fun vb _ hb' => evalAt_fwd hcall htick b _ vb _ hb' _ (va :: st) fs)
        (fun vb _ _ w _ hp => by
          cases hp
          rw [List.append_nil]
          by_cases hl : va + vb < limit
          · exact Goes.head (b := false) (by simp [step, hl]) Goes.refl
          · exact Goes.fail (failure := .natOverflow) (by simp [step, hl]) (List.prefix_refl _))
        hb) he
  | .sub a b, h, w, tr, he, K, st, fs => by
    rw [show compile (.sub a b) ++ K = compile a ++ (compile b ++ (.sub :: K)) by simp [compile]]
    exact goes_bind (s₁ := fun va h' => ⟨compile b ++ (.sub :: K), va :: st, x, fs, h'⟩)
      (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
      (fun va _ ha => evalAt_fwd hcall htick a _ va _ ha _ st fs)
      (fun va _ _ w _ hb => goes_bind
        (s₁ := fun vb h' => ⟨.sub :: K, vb :: va :: st, x, fs, h'⟩)
        (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
        (fun vb _ hb' => evalAt_fwd hcall htick b _ vb _ hb' _ (va :: st) fs)
        (fun vb _ _ w _ hp => by
          cases hp
          rw [List.append_nil]
          exact Goes.head (b := false) rfl Goes.refl)
        hb) he
  | .ifz c t e, h, w, tr, he, K, st, fs => by
    rw [show compile (.ifz c t e) ++ K = compile c ++ (.ifz (compile t) (compile e) :: K) by
      simp [compile]]
    exact goes_bind (s₁ := fun vc h' => ⟨.ifz (compile t) (compile e) :: K, vc :: st, x, fs, h'⟩)
      (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
      (fun vc _ hc => evalAt_fwd hcall htick c _ vc _ hc _ st fs)
      (fun vc _ _ w _ hb => by
        refine Goes.head (b := false) rfl ?_
        by_cases hv : vc = 0
        · simp only [hv, ↓reduceIte] at hb ⊢
          exact evalAt_fwd hcall htick t _ w _ hb K st fs
        · simp only [hv, ↓reduceIte] at hb ⊢
          exact evalAt_fwd hcall htick e _ w _ hb K st fs) he
  | .call f a, h, w, tr, he, K, st, fs => by
    rw [show compile (.call f a) ++ K = compile a ++ (.call f :: K) by simp [compile]]
    exact goes_bind (s₁ := fun va h' => ⟨.call f :: K, va :: st, x, fs, h'⟩)
      (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
      (fun va _ ha => evalAt_fwd hcall htick a _ va _ ha _ st fs)
      (fun va _ _ w _ hc => hcall f va _ w _ hc K st fs) he
  | .tick e, h, w, tr, he, K, st, fs => htick e h w tr he K st fs
  | .out a e, h, w, tr, he, K, st, fs => by
    rw [show compile (.out a e) ++ K = compile a ++ (.out :: (compile e ++ K)) by simp [compile]]
    exact goes_bind (s₁ := fun va h' => ⟨.out :: (compile e ++ K), va :: st, x, fs, h'⟩)
      (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
      (fun va _ ha => evalAt_fwd hcall htick a _ va _ ha _ st fs)
      (fun va _ _ w _ hb => goes_bind
        (s₁ := fun _ h' => ⟨compile e ++ K, st, x, fs, h'⟩)
        (s₂ := fun w h' => ⟨K, w :: st, x, fs, h'⟩)
        (fun _ _ hemit => by
          cases hemit
          exact Goes.head (b := false) rfl Goes.refl)
        (fun _ _ _ w _ he' => evalAt_fwd hcall htick e _ w _ he' K st fs)
        hb) he

/-- A source value is reached by the compiled code in any context, with
the same events appended, unless an `add` overflows on the way. -/
theorem eval_fwd (o : Oracle) (p : Prog) : ∀ k x e h w tr, eval o p k x e h = ⟨.ok w, tr⟩ →
    ∀ K st fs, Goes o (compileProg p) ⟨compile e ++ K, st, x, fs, h⟩ ⟨K, w :: st, x, fs, h ++ tr⟩
  | 0, _, e, h, w, tr, he => evalAt_fwd
      (fun f v h w tr hc => by
        cases hf : p[f]? with
        | none => rw [callAt_none hf] at hc; cases hc
        | some body => rw [callAt_some hf] at hc; cases hc)
      (fun _ _ _ _ hc => by cases hc) e h w tr he
  | k + 1, x, e, h, w, tr, he => evalAt_fwd
      (fun f v h w tr hc K st fs => by
        cases hf : p[f]? with
        | none => rw [callAt_none hf] at hc; cases hc
        | some body =>
          rw [callAt_some hf] at hc
          have hq : (compileProg p)[f]? = some (compile body) := by
            simp [compileProg_get, hf]
          refine Goes.head (b := true) (s' := ⟨compile body, st, v, ⟨K, x⟩ :: fs, h⟩)
            (by simp [step, hq]) ?_
          have := eval_fwd o p k v body h w tr hc [] st (⟨K, x⟩ :: fs)
          rw [List.append_nil] at this
          exact this.trans (Goes.head (b := false) rfl Goes.refl))
      (fun e h w tr hc K st fs => Goes.head (b := true) rfl (eval_fwd o p k x e h w tr hc K st fs))
      e h w tr he

/-! ## Stops: timeouts and stuck runs reach the source's events -/

theorem evalAt_stop {o : Oracle} {p : Prog} {below : Nat → Expr → M Nat} {x k : Nat}
    {q : Program}
    (hok : ∀ e h w tr, evalAt o p below x e h = ⟨.ok w, tr⟩ → ∀ K st fs,
      Goes o q ⟨compile e ++ K, st, x, fs, h⟩ ⟨K, w :: st, x, fs, h ++ tr⟩)
    (hcall : ∀ f v h, (∀ w, (callAt p below f v h).result ≠ .ok w) → ∀ K st fs,
      Stops o q ⟨.call f :: K, v :: st, x, fs, h⟩ (h ++ (callAt p below f v h).trace)
        ((callAt p below f v h).result = .timeout) k)
    (htick : ∀ e h, (∀ w, (below x e h).result ≠ .ok w) → ∀ K st fs,
      Stops o q ⟨.tick :: (compile e ++ K), st, x, fs, h⟩ (h ++ (below x e h).trace)
        ((below x e h).result = .timeout) k) :
    ∀ e h, (∀ w, (evalAt o p below x e h).result ≠ .ok w) → ∀ K st fs,
      Stops o q ⟨compile e ++ K, st, x, fs, h⟩ (h ++ (evalAt o p below x e h).trace)
        ((evalAt o p below x e h).result = .timeout) k
  | .lit n, _, hne, _, _, _ => absurd rfl (hne n)
  | .arg, _, hne, _, _, _ => absurd rfl (hne x)
  | .inp, h, hne, _, _, _ => absurd rfl (hne (o h))
  | .add a b, h, hne, K, st, fs => by
    rw [show compile (.add a b) ++ K = compile a ++ (compile b ++ (.add :: K)) by simp [compile]]
    exact stops_bind (s₁ := fun va h' => ⟨compile b ++ (.add :: K), va :: st, x, fs, h'⟩)
      (fun va _ ha => hok a _ va _ ha _ st fs)
      (fun ha => evalAt_stop hok hcall htick a h ha _ st fs)
      (fun va _ _ hne' => stops_bind
        (s₁ := fun vb h' => ⟨.add :: K, vb :: va :: st, x, fs, h'⟩)
        (fun vb _ hb => hok b _ vb _ hb _ (va :: st) fs)
        (fun hb => evalAt_stop hok hcall htick b _ hb _ (va :: st) fs)
        (fun vb _ _ hne'' => absurd rfl (hne'' (va + vb))) hne') hne
  | .sub a b, h, hne, K, st, fs => by
    rw [show compile (.sub a b) ++ K = compile a ++ (compile b ++ (.sub :: K)) by simp [compile]]
    exact stops_bind (s₁ := fun va h' => ⟨compile b ++ (.sub :: K), va :: st, x, fs, h'⟩)
      (fun va _ ha => hok a _ va _ ha _ st fs)
      (fun ha => evalAt_stop hok hcall htick a h ha _ st fs)
      (fun va _ _ hne' => stops_bind
        (s₁ := fun vb h' => ⟨.sub :: K, vb :: va :: st, x, fs, h'⟩)
        (fun vb _ hb => hok b _ vb _ hb _ (va :: st) fs)
        (fun hb => evalAt_stop hok hcall htick b _ hb _ (va :: st) fs)
        (fun vb _ _ hne'' => absurd rfl (hne'' (va - vb))) hne') hne
  | .ifz c t e, h, hne, K, st, fs => by
    rw [show compile (.ifz c t e) ++ K = compile c ++ (.ifz (compile t) (compile e) :: K) by
      simp [compile]]
    exact stops_bind (s₁ := fun vc h' => ⟨.ifz (compile t) (compile e) :: K, vc :: st, x, fs, h'⟩)
      (fun vc _ hc => hok c _ vc _ hc _ st fs)
      (fun hc => evalAt_stop hok hcall htick c h hc _ st fs)
      (fun vc _ _ hne' => by
        refine Stops.of_goes (Goes.head (b := false) rfl Goes.refl) ?_
        by_cases hv : vc = 0
        · simp only [hv, ↓reduceIte] at hne' ⊢
          exact evalAt_stop hok hcall htick t _ hne' K st fs
        · simp only [hv, ↓reduceIte] at hne' ⊢
          exact evalAt_stop hok hcall htick e _ hne' K st fs) hne
  | .call f a, h, hne, K, st, fs => by
    rw [show compile (.call f a) ++ K = compile a ++ (.call f :: K) by simp [compile]]
    exact stops_bind (s₁ := fun va h' => ⟨.call f :: K, va :: st, x, fs, h'⟩)
      (fun va _ ha => hok a _ va _ ha _ st fs)
      (fun ha => evalAt_stop hok hcall htick a h ha _ st fs)
      (fun va _ _ hne' => hcall f va _ hne' K st fs) hne
  | .tick e, h, hne, K, st, fs => htick e h hne K st fs
  | .out a e, h, hne, K, st, fs => by
    rw [show compile (.out a e) ++ K = compile a ++ (.out :: (compile e ++ K)) by simp [compile]]
    exact stops_bind (s₁ := fun va h' => ⟨.out :: (compile e ++ K), va :: st, x, fs, h'⟩)
      (fun va _ ha => hok a _ va _ ha _ st fs)
      (fun ha => evalAt_stop hok hcall htick a h ha _ st fs)
      (fun va _ _ hne' => stops_bind
        (s₁ := fun _ h' => ⟨compile e ++ K, st, x, fs, h'⟩)
        (fun _ _ hemit => by
          cases hemit
          exact Goes.head (b := false) rfl Goes.refl)
        (fun hemit => absurd rfl (hemit ()))
        (fun _ _ _ hne'' => evalAt_stop hok hcall htick e _ hne'' K st fs) hne') hne

/-- A source run at depth `k` that does not return a value reaches, from
the compiled code in any context, a state with exactly its events, after
more than `k` charges if it timed out; or it fails for a resource after a
prefix of them. -/
theorem eval_stop (o : Oracle) (p : Prog) : ∀ k x e h, (∀ w, (eval o p k x e h).result ≠ .ok w) →
    ∀ K st fs, Stops o (compileProg p) ⟨compile e ++ K, st, x, fs, h⟩
      (h ++ (eval o p k x e h).trace) ((eval o p k x e h).result = .timeout) k
  | 0, x, e, h, hne => evalAt_stop (eval_fwd o p 0 x)
      (fun f v h _ K st fs => by
        cases hf : p[f]? with
        | none =>
          rw [callAt_none hf]
          exact Stops.here (by simp [M.halt]) (by simp [M.halt])
        | some body =>
          rw [callAt_some hf]
          have hq : (compileProg p)[f]? = some (compile body) := by
            simp [compileProg_get, hf]
          exact Stops.charge_zero (s' := ⟨compile body, st, v, ⟨K, x⟩ :: fs, h⟩)
            (by simp [step, hq]) (by simp [M.halt]))
      (fun e h _ K st fs => Stops.charge_zero (s' := ⟨compile e ++ K, st, x, fs, h⟩) rfl
        (by simp [M.halt])) e h hne
  | k + 1, x, e, h, hne => evalAt_stop (eval_fwd o p (k + 1) x)
      (fun f v h hne' K st fs => by
        cases hf : p[f]? with
        | none =>
          rw [callAt_none hf]
          exact Stops.here (by simp [M.halt]) (by simp [M.halt])
        | some body =>
          rw [callAt_some hf] at hne' ⊢
          have hq : (compileProg p)[f]? = some (compile body) := by
            simp [compileProg_get, hf]
          refine Stops.charge (s' := ⟨compile body, st, v, ⟨K, x⟩ :: fs, h⟩)
            (by simp [step, hq]) ?_
          have := eval_stop o p k v body h hne' [] st (⟨K, x⟩ :: fs)
          rwa [List.append_nil] at this)
      (fun e h hne' K st fs => Stops.charge rfl (eval_stop o p k x e h hne' K st fs)) e h hne

/-! ## The traced simulation and the pass -/

/-- The per-input traced simulation, with the identity clock map. -/
theorem sim (p : Prog) (x : Nat) : TSim Eq id (Big.run p x) (run (compileProg p) x) := by
  cases hmain : p[0]? with
  | none =>
    have h₁ : Big.run p x = fun _ _ => ⟨.stuck, []⟩ :=
      funext fun _ => funext fun _ => by simp [Big.run, hmain]
    have h₂ : run (compileProg p) x = fun _ _ => ⟨.stuck, []⟩ :=
      funext fun _ => funext fun _ => by simp [run, compileProg_get, hmain]
    rw [h₁, h₂]
    exact TSim.refl (fun _ => rfl) _
  | some main =>
    have hq : (compileProg p)[0]? = some (compile main) := by simp [compileProg_get, hmain]
    have hsrc : Big.run p x = fun o k => eval o p k x main [] :=
      funext fun _ => funext fun _ => by simp [Big.run, hmain]
    rw [hsrc]
    have hruns := fun o => run_runs (compileProg p) x o hq
    have hg : ∀ o, Grows (step o (compileProg p)) State.trace := fun o => @step_grows o _
    -- A source value: the machine returns it with the same events, or overflows.
    have hval : ∀ o k w tr, eval o p k x main [] = ⟨.ok w, tr⟩ →
        ∃ k', Traced.Refines Eq (eval o p k x main []) (run (compileProg p) x o k') := by
      intro o k w tr he
      rw [he]
      rcases eval_fwd o p k x main [] w tr he [] [] [] with ⟨c, hst⟩ | ⟨c, s', failure, hst, hs', hp⟩
      · rw [List.append_nil] at hst
        refine ⟨c, ?_⟩
        rw [(hruns o).eq (ReachesT.of_final hst .done (Nat.le_refl _))]
        exact .result rfl (.ok rfl)
      · rw [List.append_nil] at hst
        refine ⟨c, ?_⟩
        rw [(hruns o).eq (ReachesT.of_final hst (by rw [hs']; exact Final.fail) (Nat.le_refl _))]
        exact .resource failure rfl hp
    exact {
      forward := fun o k hk => by
        have hb := eval_basic o p k x main []
        have hk : (eval o p k x main []).result ≠ .timeout := hk
        generalize ht : eval o p k x main [] = t at hk hb ⊢
        obtain ⟨r, tr⟩ := t
        cases r with
        | ok w => rw [← ht]; exact hval o k w tr ht
        | stuck => exact ⟨0, .stuck rfl⟩
        | timeout => exact absurd rfl hk
        | trap => exact absurd hb id
        | resource _ => exact absurd hb id
      timeout := fun o k hk => by
        have hk : (eval o p k x main []).result = .timeout := hk
        show ((run (compileProg p) x o k).result = .timeout ∨ _) ∧
          (run (compileProg p) x o k).trace <+: (eval o p k x main []).trace
        obtain ⟨c, s', hst, ⟨htr, hdeep⟩ | ⟨failure, hf, hp⟩⟩ :=
          eval_stop o p k x main [] (fun w e => by rw [hk] at e; cases e) [] [] []
        · rw [List.append_nil] at hst
          obtain ⟨tr', hr, hp'⟩ := ReachesT.timeout_of_star (hg o) hst (hdeep hk)
          rw [(hruns o).eq hr]
          exact ⟨.inl rfl, hp'.trans (by rw [htr]; exact List.prefix_refl _)⟩
        · rw [List.append_nil] at hst
          by_cases hc : c ≤ k
          · rw [(hruns o).eq (ReachesT.of_final hst (by rw [hf]; exact Final.fail) hc)]
            exact ⟨.inr ⟨failure, rfl⟩, hp⟩
          · obtain ⟨tr', hr, hp'⟩ := ReachesT.timeout_of_star (k := k) (hg o) hst (by omega)
            rw [(hruns o).eq hr]
            exact ⟨.inl rfl, hp'.trans hp⟩
      progress := fun o k => by
        by_cases hok : ∃ w, (eval o p k x main []).result = .ok w
        · obtain ⟨w, hw⟩ := hok
          obtain ⟨k', hr⟩ := hval o k w _ (Traced.ext hw rfl)
          refine ⟨k', ?_⟩
          rcases hr.trace_live with hp | hf | hs
          · exact .inl hp
          · exact .inr hf
          · rw [hw] at hs; cases hs
        · have hne : ∀ w, (eval o p k x main []).result ≠ .ok w := fun w e => hok ⟨w, e⟩
          obtain ⟨c, s', hst, ⟨htr, _⟩ | ⟨failure, hf, _⟩⟩ :=
            eval_stop o p k x main [] hne [] [] []
          · rw [List.append_nil] at hst
            refine ⟨c, .inl ?_⟩
            have := ReachesT.passes (hg o) hst (Nat.le_refl _) ((hruns o) c)
            rw [htr] at this
            exact this
          · rw [List.append_nil] at hst
            refine ⟨c, .inr ⟨failure, ?_⟩⟩
            rw [(hruns o).eq (ReachesT.of_final hst (by rw [hf]; exact Final.fail) (Nat.le_refl _))] }

/-- Compilation to the IO stack machine as a traced pass (no
certificate). -/
def transform : TTransform Prog Program where
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
      exact TRefines.of_sim (R := Eq) (fun _ _ h => h ▸ rfl) fun x => ⟨id, sim p x⟩

end Stack

end CompilatrixTests.Sem.Toy.IO
