import Compilatrix.Xv.Stacking.Proof.WrapperExit
import Compilatrix.Sem.Smallstep

/-!
# The stacked program simulates Xl

`step_sim`: from a state the invariant (`Match`) relates to the machine,
every Xl step is matched by checked machine steps. A step that continues
reaches the invariant again with at least one machine step per clock charge
(a call, a tail call or a backward edge), or the program exits with status
2 when a callee's stack check fails; a run that ends leaves through the
export wrapper with the matching status, and a return from the outermost
activation with status 0 and `Final`.

`sim`: by induction over a clocked run (`Sem.Reaches`), the machine run from
a matched state ends as the Xl run does (`Outcome`): a timeout at clock `k`
is a running machine after at least `k` checked steps, and every exit's
stack pointer is readable data, which layout needs to transport it.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- How the machine ends after `n` checked steps, against Xl's outcome `r`
at clock `k`: a failed stack check (status 2), or `r`'s own exit: status 0
with `Final`, a running machine after at least `k` steps for a timeout,
the status of a resource failure or a trap. Every exit's stack pointer is
readable data. -/
def Outcome (core₀ : Core) (retAddr : Word) (k n : Nat) (holes : Holes) (after : Machine) (r : Lir.Outcome) :
    Prop :=
  (∃ val, Exit core₀ retAddr 2 val after ∧ ReadableData holes (after.core.readReg .rsp) 8) ∨
    match r with
    | .ok v => ∃ val, Exit core₀ retAddr 0 val after ∧ Final v val after.core.memory holes ∧
        ReadableData holes (after.core.readReg .rsp) 8
    | .timeout => k ≤ n ∧ after.status = .running
    | .resource failure => ∃ val, Exit core₀ retAddr (UInt64.ofNat (statusOf failure)) val after ∧
        ReadableData holes (after.core.readReg .rsp) 8
    | .trap => ∃ val, Exit core₀ retAddr 4 val after ∧ ReadableData holes (after.core.readReg .rsp) 8
    | .stuck => True

theorem Outcome.mono {core₀ : Core} {retAddr : Word} {k n n' : Nat} {holes : Holes} {after : Machine}
    {r : Lir.Outcome} (h : Outcome core₀ retAddr k n holes after r) (hn : n ≤ n') :
    Outcome core₀ retAddr k n' holes after r := by
  rcases h with h | h
  · exact .inl h
  · right
    cases r with
    | timeout => exact ⟨by have := h.1; omega, h.2⟩
    | _ => exact h

theorem Outcome.succ {core₀ : Core} {retAddr : Word} {k n : Nat} {holes : Holes} {after : Machine}
    {r : Lir.Outcome} (h : Outcome core₀ retAddr k n holes after r) :
    Outcome core₀ retAddr (k + 1) (n + 1) holes after r := by
  rcases h with h | h
  · exact .inl h
  · right
    cases r with
    | timeout => exact ⟨by have := h.1; omega, h.2⟩
    | _ => exact h

/-- What one Xl step's outcome needs of the machine. -/
def StepOk (S : Stk) (W : Wrap) (m : Machine) (holes : Holes) : Xl.LStep → Prop
  | .next s' c =>
      (∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
        Exit W.core₀ W.retAddr 2 0 after ∧ ReadableData holes' (after.core.readReg .rsp) 8) ∨
      ∃ n holes' m' fr' a' ret' below', c.toNat ≤ n ∧ SafeSteps Runtime.rejecting S.cs n holes m holes' m' ∧
        Match S W s' m' holes' fr' a' ret' below'
  | .done v => ∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
      ∃ val, Exit W.core₀ W.retAddr 0 val after ∧ Final v val after.core.memory holes' ∧
        ReadableData holes' (after.core.readReg .rsp) 8
  | .fail failure => ∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
      Exit W.core₀ W.retAddr (UInt64.ofNat (statusOf failure)) 0 after ∧
        ReadableData holes' (after.core.readReg .rsp) 8
  | .trap => ∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
      Exit W.core₀ W.retAddr 4 0 after ∧ ReadableData holes' (after.core.readReg .rsp) 8
  | .stuck => True

/-- The stacked code of a failure or a trap: a jump to the exit group's
`fail_k`. -/
theorem term_fail {c : FnCtx} {r : Sem.Resource} {k : Nat} {post : List Instr} {t : X86.Terminator} {x : Term Loc}
    (hx : x = .fail r ∧ k = statusOf r ∨ x = .trap ∧ k = trapStatus) (h : c.term x = .ok (post, t)) :
    post = [] ∧ t = .jump (c.failBlock k) := by
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [FnCtx.term, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  · simp only [FnCtx.term, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩

theorem statusOf_range (r : Sem.Resource) : 1 ≤ statusOf r ∧ statusOf r ≤ 4 := by
  cases r <;> simp [statusOf]

/-- One Xl step from a matched state, as checked machine steps. -/
theorem step_sim {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    (hwc : WrapCont S W) : StepOk S W m holes (Xl.step S.p S.env s) := by
  obtain ⟨f, l, pl, htop⟩ := hm.top
  obtain ⟨b, codes, post, t, hpos, hpc⟩ := htop.code
  have hfunc := htop.fn.func
  have hblock := hpos.block
  obtain ⟨smem, sctx, sregs, sstack⟩ := s
  have hstk : sstack = fr :: below.map (·.1) := hm.stack
  subst hstk
  unfold Xl.step
  simp only [hfunc, hblock]
  split
  · -- A body instruction
    rename_i hlt
    obtain ⟨x, hx⟩ : ∃ x, b.body[fr.pos]? = some x := ⟨_, Array.getElem?_eq_getElem hlt⟩
    have hxe : b.body[fr.pos] = x := by
      rw [Array.getElem?_eq_getElem hlt] at hx; exact Option.some.inj hx
    rw [hxe]
    cases x with
    | call g args rets =>
      dsimp only
      split
      · trivial
      · rename_i hconv
        simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_or, Bool.not_eq_false] at hconv
        split
        · rename_i callee regs' hce
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hce
          obtain ⟨vals, hread, henter⟩ := hce
          rcases step_call hm htop hpos hpc hx hconv.1 hread henter with h | ⟨n, holes', m', a', ret', hn, hst, hm'⟩
          · exact .inl h
          · exact .inr ⟨n, holes', m', _, a', ret', _, by simpa using hn, hst, hm'⟩
        · trivial
    | op o defs args =>
      dsimp only
      split
      · rename_i regs' fr'' mem' hexec
        obtain ⟨holes', m', hst, hm'⟩ := step_op hm htop hpos hpc hx hexec
        exact .inr ⟨1, holes', m', _, a, ret, below, by simp, hst, hm'⟩
      · trivial
    | fused p pargs q defs cargs =>
      dsimp only
      split
      · rename_i regs' fr'' mem' hexec
        obtain ⟨n, holes', m', hst, hm'⟩ := step_fused hm htop hpos hpc hx hexec
        exact .inr ⟨n, holes', m', _, a, ret, below, by simp, hst, hm'⟩
      · trivial
    | move dst src =>
      dsimp only
      split
      · rename_i regs' fr'' mem' hexec
        obtain ⟨n, holes', m', hst, hm'⟩ := step_move hm htop hpos hpc hx hexec
        exact .inr ⟨n, holes', m', _, a, ret, below, by simp, hst, hm'⟩
      · trivial
    | zero y =>
      dsimp only
      split
      · rename_i regs' fr'' mem' hexec
        obtain ⟨holes', m', hst, hm'⟩ := step_zero hm htop hpos hpc hx hexec
        exact .inr ⟨1, holes', m', _, a, ret, below, by simp, hst, hm'⟩
      · trivial
  · -- The terminator
    rename_i hge
    have hend : fr.pos = b.body.size := by have := hpos.pos; omega
    cases hterm : b.term with
    | jmp e =>
      dsimp only
      refine (fun st hst => ?_ : ∀ st, Xl.takeEdge f ⟨smem, sctx, sregs, fr :: below.map (·.1)⟩ fr (below.map (·.1)) sregs e = st →
        StepOk S W m holes st) _ rfl
      cases st with
      | next s' c =>
        obtain ⟨m', hsteps, hc, hm'⟩ := step_jmp hm htop hpos hpc hend hterm hst
        exact .inr ⟨1, holes, m', _, a, ret, below, hc, hsteps, hm'⟩
      | stuck => trivial
      | done v => simp [Xl.takeEdge] at hst; split at hst <;> (try split at hst) <;> simp at hst
      | fail r => simp [Xl.takeEdge] at hst; split at hst <;> (try split at hst) <;> simp at hst
      | trap => simp [Xl.takeEdge] at hst; split at hst <;> (try split at hst) <;> simp at hst
    | jcc p pargs defs cond e₁ e₂ =>
      dsimp only
      split
      · rename_i regs' fr'' mem' taken hrun
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hrun
        obtain ⟨bs, hbs, ⟨regs₁, fr₁, mem₁, flags⟩, hexec, tk, htk, he⟩ := hrun
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        refine (fun st hst => ?_ : ∀ st, Xl.takeEdge f ⟨mem₁, sctx, sregs, fr :: below.map (·.1)⟩ fr₁ (below.map (·.1)) regs₁
          (if tk then e₁ else e₂) = st → StepOk S W m holes st) _ rfl
        cases st with
        | next s' c =>
          obtain ⟨holes', m', hsteps, hc, hm'⟩ := step_jcc hm htop hpos hpc hend hterm hbs hexec htk hst
          exact .inr ⟨1, holes', m', _, a, ret, below, hc, hsteps, hm'⟩
        | stuck => trivial
        | done v => simp [Xl.takeEdge] at hst; split at hst <;> (try split at hst) <;> simp at hst
        | fail r => simp [Xl.takeEdge] at hst; split at hst <;> (try split at hst) <;> simp at hst
        | trap => simp [Xl.takeEdge] at hst; split at hst <;> (try split at hst) <;> simp at hst
      · trivial
    | ret vs =>
      dsimp only
      split
      · trivial
      · rename_i hcr
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hcr
        split
        · trivial
        · rename_i vals hread
          cases below with
          | nil =>
            simp only [List.map_nil]
            have hres : f.results = 1 := (hm.chain f l pl htop.fn).results
            exact step_done hm htop hpos hpc hend hterm hcr hread hres hwc
          | cons x rest =>
            obtain ⟨fr₁, a₁, ret₁⟩ := x
            simp only [List.map_cons]
            split
            · trivial
            · rename_i hres
              simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hres
              obtain ⟨n, m', hst, hm'⟩ := step_ret hm htop hpos hpc hend hterm hcr hread hres
              exact .inr ⟨n, holes, m', _, a₁, ret₁, rest, by simp, hst, hm'⟩
    | tail g args =>
      dsimp only
      split
      · trivial
      · rename_i hconv
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, not_or,
          Nat.not_lt, Bool.not_eq_false] at hconv
        split
        · rename_i callee regs' hce
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hce
          obtain ⟨vals, hread, henter⟩ := hce
          rcases step_tail hm htop hpos hpc hend hterm hconv.1 hconv.2 hread henter with
            h | ⟨n, holes', m', a', hn, hst, hm'⟩
          · exact .inl h
          · exact .inr ⟨n, holes', m', _, a', ret, below, by simpa using hn, hst, hm'⟩
        · trivial
    | fail r =>
      dsimp only
      have hk := statusOf_range r
      have ht := term_fail (k := statusOf r) (.inl ⟨rfl, rfl⟩) (hterm ▸ hpos.term)
      obtain ⟨n, after, hst, hexit, hdata⟩ := step_fail hm htop hpos hpc hend hk.1 hk.2 ht
      exact ⟨n, holes, after, hst, hexit, hdata⟩
    | trap =>
      dsimp only
      have ht := term_fail (r := .heap) (k := trapStatus) (.inr ⟨rfl, rfl⟩) (hterm ▸ hpos.term)
      obtain ⟨n, after, hst, hexit, hdata⟩ := step_fail hm htop hpos hpc hend (by decide) (by decide) ht
      exact ⟨n, holes, after, hst, hexit, hdata⟩

/-- **The stacking simulation.** From a state the invariant relates to the
machine, the machine's checked run ends as Xl's clocked run does. -/
theorem sim {S : Stk} {W : Wrap} (hwc : WrapCont S W) {s : Xl.State} {k : Nat} {r : Lir.Outcome}
    (hr : Sem.Reaches (Xl.step S.p S.env) s k r) :
    ∀ {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act} {ret : ReturnFrame}
      {below : List (Xl.Frame × Act × ReturnFrame)}, Match S W s m holes fr a ret below →
      ∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
        Outcome W.core₀ W.retAddr k n holes' after r := by
  induction hr with
  | @final s k r hf =>
    intro m holes fr a ret below hm
    have hstep := step_sim hm hwc
    generalize Xl.step S.p S.env s = st at hf hstep
    cases hf with
    | done =>
      obtain ⟨n, holes', after, hst, val, hexit, hfin, hdata⟩ := hstep
      exact ⟨n, holes', after, hst, .inr ⟨val, hexit, hfin, hdata⟩⟩
    | fail =>
      obtain ⟨n, holes', after, hst, hexit, hdata⟩ := hstep
      exact ⟨n, holes', after, hst, .inr ⟨0, hexit, hdata⟩⟩
    | trap =>
      obtain ⟨n, holes', after, hst, hexit, hdata⟩ := hstep
      exact ⟨n, holes', after, hst, .inr ⟨0, hexit, hdata⟩⟩
    | stuck => exact ⟨0, holes, m, .refl _ _, .inr trivial⟩
  | @free s s' k r hs _ ih =>
    intro m holes fr a ret below hm
    have hstep := step_sim hm hwc
    rw [hs] at hstep
    rcases hstep with ⟨n, holes', after, hst, hexit, hdata⟩ | ⟨n, holes', m', fr', a', ret', below', -, hst, hm'⟩
    · exact ⟨n, holes', after, hst, .inl ⟨0, hexit, hdata⟩⟩
    · obtain ⟨n', holes'', after, hst', hout⟩ := ih hm'
      exact ⟨n + n', holes'', after, hst.append hst', hout.mono (by omega)⟩
  | @charge s s' k r hs _ ih =>
    intro m holes fr a ret below hm
    have hstep := step_sim hm hwc
    rw [hs] at hstep
    rcases hstep with ⟨n, holes', after, hst, hexit, hdata⟩ | ⟨n, holes', m', fr', a', ret', below', hn, hst, hm'⟩
    · exact ⟨n, holes', after, hst, .inl ⟨0, hexit, hdata⟩⟩
    · obtain ⟨n', holes'', after, hst', hout⟩ := ih hm'
      simp only [Bool.toNat_true] at hn
      refine ⟨n + n', holes'', after, hst.append hst', ?_⟩
      have := hout.succ.mono (n' := n + n') (by omega)
      exact this
  | timeout hs =>
    intro m holes fr a ret below hm
    exact ⟨0, holes, m, .refl _ _, .inr ⟨Nat.le_refl 0, hm.running⟩⟩

end Compilatrix.Xv.Stacking.Proof
