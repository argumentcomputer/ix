import Compilatrix.Cfg.Proof.Layout
import Compilatrix.Own.Proof.Unfold

/-! # Cfg steps, and what a Cfg run does for an Own outcome

One equation per Cfg step the Own → Cfg simulation takes (entering a
function, an instruction, a call, a return, each terminator, an edge), and
`Reach`: what the Cfg run from a state does when Own's outcome at depth
clock `k` is `r`, returning to the stack `stk`:

* a value: the run reaches `.ret v stk H'` (with some number of charges);
* a trap: the run reaches a state whose step traps;
* a timeout: the run spends **more than `k` charges** (a depth-`k`
  timeout forces more than `k` charges on the total clock, `Sim.ofStar`'s
  timeout premise with the identity clock map);
* stuck: nothing; Own never fails for a resource.

The combinators chain them: a free step, a charge (`Sem.later` on the Own
side), and a call followed by the rest of the caller (`Reach.call`). -/

set_option autoImplicit false

namespace Compilatrix.Cfg.Proof

open Compilatrix.Sem (Result Star)
open Compilatrix.Own (RVal Heap AllocPol Env)
open Compilatrix.Fir (Var FunId JoinId Arg)

variable {pol : AllocPol} {P : Program}

/-! ## Steps -/

theorem step_call {f : FunId} {args : List RVal} {stk : List (Frame × Var)} {H : Heap} {fd : Fun}
    {b : Block} (hf : P.fun? f = some fd) (hb : fd.block? 0 = some b) (hl : args.length = b.params.length) :
    step pol P (.call f args stk H) =
      .next (.run { fn := f, blk := 0, rest := b.body, env := Own.bindAll .leaf (b.params.map (·.1)) args }
        stk H) true := by
  simp only [step, hf, hb, hl, ↓reduceIte]

theorem step_ret_nil {v : RVal} {H : Heap} : step pol P (.ret v [] H) = .done (v, H) := rfl

theorem step_ret_cons {v : RVal} {fr : Frame} {x : Var} {stk : List (Frame × Var)} {H : Heap} :
    step pol P (.ret v ((fr, x) :: stk) H) = .next (.run { fr with env := fr.env.insert x v } stk H) false :=
  rfl

theorem step_run_call {fr : Frame} {stk : List (Frame × Var)} {H : Heap} {x : Var} {f : FunId}
    {as : List Arg} {is : List Instr} {vs : List RVal} (hr : fr.rest = .bind x (.fir (.call f as)) :: is)
    (hv : Own.evalArgs fr.env as = some vs) :
    step pol P (.run fr stk H) = .next (.call f vs (({ fr with rest := is }, x) :: stk) H) false := by
  simp only [step, hr, hv]

theorem step_run_bind {fr : Frame} {stk : List (Frame × Var)} {H : Heap} {x : Var} {r : Own.Rhs}
    {is : List Instr} (hr : fr.rest = .bind x r :: is) (hnc : ∀ f as, r ≠ .fir (.call f as)) :
    step pol P (.run fr stk H) =
      match Own.evalRhs pol P.tables fr.env H r with
      | .ok (v, H') => .next (.run { fr with rest := is, env := fr.env.insert x v } stk H') false
      | .resource r => .fail r
      | .trap => .trap
      | .timeout | .stuck => .stuck := by
  cases r with
  | fir e =>
    cases e with
    | call g as => exact absurd rfl (hnc g as)
    | _ => simp only [step, hr]; rfl
  | _ => simp only [step, hr]; rfl

/-- The step of a frame at the end of its block. -/
def termStep (P : Program) (fd : Fun) (fr : Frame) (stk : List (Frame × Var)) (H : Heap) :
    Term → Sem.Step State (RVal × Heap)
  | .jump e => takeEdge fd fr stk H e
  | .switch x alts d =>
    match fr.env.get? x with
    | some v =>
      match v.asCtor P.known H with
      | some (key, _) =>
        match selectEdge key alts d with
        | some e => takeEdge fd fr stk H e
        | none => .stuck
      | none => .stuck
    | none => .stuck
  | .ret a =>
    match Own.evalArg fr.env a with
    | some v => .next (.ret v stk H) false
    | none => .stuck
  | .tcall f as =>
    match Own.evalArgs fr.env as with
    | some vs => .next (.call f vs stk H) false
    | none => .stuck
  | .trap => .trap

theorem step_run_term {fr : Frame} {stk : List (Frame × Var)} {H : Heap} {fd : Fun} {b : Block}
    (hr : fr.rest = []) (hf : P.fun? fr.fn = some fd) (hb : fd.block? fr.blk = some b) :
    step pol P (.run fr stk H) = termStep P fd fr stk H b.term := by
  simp only [step, hr, hf, hb]
  cases b.term <;> rfl

theorem takeEdge_eq {fd : Fun} {fr : Frame} {stk : List (Frame × Var)} {H : Heap} {e : Edge} {b : Block}
    {vs : List RVal} (hb : fd.block? e.target = some b) (hv : Own.evalArgs fr.env e.args = some vs)
    (hl : vs.length = b.params.length) :
    takeEdge fd fr stk H e =
      .next (.run { fr with blk := e.target, rest := b.body, env := Own.bindAll fr.env (b.params.map (·.1)) vs }
        stk H) e.back := by
  simp only [takeEdge, hb, hv, hl, ↓reduceIte]

/-! ## What a run does for an Own outcome -/

/-- What the Cfg run from `s` does when Own's outcome at depth clock `k` is
`r`, returning to `stk` (see the module comment). -/
def Reach (pol : AllocPol) (P : Program) (k : Nat) (s : State) (stk : List (Frame × Var)) :
    Result (RVal × Heap) → Prop
  | .ok (v, H') => ∃ n, Star (step pol P) s n (.ret v stk H')
  | .trap => ∃ n s', Star (step pol P) s n s' ∧ step pol P s' = .trap
  | .timeout => ∃ n s', Star (step pol P) s n s' ∧ k < n
  | .stuck => True
  | .resource _ => False

namespace Reach

variable {k : Nat} {s s' : State} {stk : List (Frame × Var)}

theorem stuck : Reach pol P k s stk .stuck := trivial

/-- A free step first. -/
theorem free {r : Result (RVal × Heap)} (hs : step pol P s = .next s' false) (h : Reach pol P k s' stk r) :
    Reach pol P k s stk r := by
  match r, h with
  | .ok (v, H'), ⟨n, hn⟩ => exact ⟨n, .free hs hn⟩
  | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨n, s'', .free hs hn, ht⟩
  | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨n, s'', .free hs hn, hk⟩
  | .stuck, _ => trivial
  | .resource _, h => exact h.elim

/-- Free steps first. -/
theorem star {r : Result (RVal × Heap)} (hs : Star (step pol P) s 0 s') (h : Reach pol P k s' stk r) :
    Reach pol P k s stk r := by
  match r, h with
  | .ok (v, H'), ⟨n, hn⟩ => exact ⟨0 + n, hs.trans hn⟩
  | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨0 + n, s'', hs.trans hn, ht⟩
  | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨0 + n, s'', hs.trans hn, by omega⟩
  | .stuck, _ => trivial
  | .resource _, h => exact h.elim

/-- A charge: Own's `Sem.later k` against a charged step. -/
theorem charge {r : Nat → Result (RVal × Heap)} (hs : step pol P s = .next s' true)
    (h : ∀ k', k = k' + 1 → Reach pol P k' s' stk (r k')) : Reach pol P k s stk (Sem.later k r) := by
  cases k with
  | zero => exact ⟨1, s', .charge hs (.refl _), by omega⟩
  | succ k' =>
    simp only [Sem.later_succ]
    have h' := h k' rfl
    generalize r k' = r' at h'
    match r', h' with
    | .ok (v, H'), ⟨n, hn⟩ => exact ⟨n + 1, .charge hs hn⟩
    | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨n + 1, s'', .charge hs hn, ht⟩
    | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨n + 1, s'', .charge hs hn, by omega⟩
    | .stuck, _ => trivial
    | .resource _, h => exact h.elim

/-- A non-tail call, then the rest of the caller. -/
theorem call {fr : Frame} {x : Var} {f : FunId} {vs : List RVal} {is : List Instr} {H : Heap}
    {r : Result (RVal × Heap)} {g : RVal × Heap → Result (RVal × Heap)}
    (hs : step pol P (.run fr stk H) = .next (.call f vs (({ fr with rest := is }, x) :: stk) H) false)
    (h₁ : Reach pol P k (.call f vs (({ fr with rest := is }, x) :: stk) H) (({ fr with rest := is }, x) :: stk) r)
    (h₂ : ∀ v H', r = .ok (v, H') →
      Reach pol P k (.run { fr with rest := is, env := fr.env.insert x v } stk H') stk (g (v, H'))) :
    Reach pol P k (.run fr stk H) stk (r.bind g) := by
  match r, h₁ with
  | .ok (v, H'), ⟨n, hn⟩ =>
    simp only [Result.bind_ok]
    have hc := h₂ v H' rfl
    generalize g (v, H') = r' at hc
    have hpre : Star (step pol P) (.run fr stk H) n
        (.run { fr with rest := is, env := fr.env.insert x v } stk H') := by
      have := (Star.free hs hn).trans (Star.free (s' := .run { fr with rest := is, env := fr.env.insert x v } stk H')
        step_ret_cons (.refl _))
      simpa using this
    match r', hc with
    | .ok (v', H''), ⟨n', hn'⟩ => exact ⟨n + n', hpre.trans hn'⟩
    | .trap, ⟨n', s'', hn', ht⟩ => exact ⟨n + n', s'', hpre.trans hn', ht⟩
    | .timeout, ⟨n', s'', hn', hk⟩ => exact ⟨n + n', s'', hpre.trans hn', by omega⟩
    | .stuck, _ => trivial
    | .resource _, h => exact h.elim
  | .trap, ⟨n, s'', hn, ht⟩ => exact ⟨n, s'', .free hs hn, ht⟩
  | .timeout, ⟨n, s'', hn, hk⟩ => exact ⟨n, s'', .free hs hn, hk⟩
  | .stuck, _ => trivial
  | .resource _, h => exact h.elim

end Reach

end Compilatrix.Cfg.Proof
