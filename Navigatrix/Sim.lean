import Navigatrix.Ixon.Eval
import Navigatrix.IxIR0.Mono
import Navigatrix.Erase

/-!
# The erasure simulation, stage 1: the pure fragment

The first theorem of the backend: **erasure preserves termination and
values** on the pure λ-fragment of Ixon — variables, `lam`, `app`,
strict `let`, and type occurrences (`sort`/`all` as term-position
values), with erased-binder redexes included. "No inductives" is
exactly the staging the plan prescribed; recursors/ctors/literals are
exercised today by `Erase.lean`'s differential guards and enter the
theorem at the next stage.

Structure (the CompCert-style split): the theorem is proved against a
**relational** erasure spec `PErase` — the executable pass agrees
with it on the fragment (spot-checked by `#guard`s; the differential
suite covers the rest of the pass). The value relation `ValRel` is
syntactic: types relate to `◻`, and closures relate when their
environments relate slot-wise and their bodies are related erasures
under the extended mask.

Key design points the proof forced (all mirrored in `Erase.lean`):

- **Dropped slots are unconstrained.** `EnvRel`'s `drop` rule relates
  *any* source value to *any* target value at a dropped slot — sound
  because erased occurrences never survive as target variable reads
  (they erase to `◻` literals), so the slot is dead. This is what
  makes the theorem true *without a typing hypothesis*.
- **Dropped-binder occurrences are outside the relation.** A `var`
  only relates at a kept slot. (The executable pass maps dropped-var
  occurrences to `◻` — sound under typing for the sort-like case;
  that refinement needs the typed relation, recorded.)
- **The erased-argument case needs the syntactic lam.** `appE` drops
  an argument's *evaluation* only when the redex shows its binder;
  the target argument is the unevaluated `◻`. The source derivation
  still evaluates the argument — the theorem's direction (source
  terminates ⟹ target terminates) is exactly why that's fine, and
  the reverse direction is precisely the kernel-totality corner of
  gate A, deliberately not claimed.
- Both fuels are handled by `IxIR0.eval_mono`: sub-derivations at
  different target fuels lift to their sum.

The statement quantifies over both evaluation contexts — the fragment
touches neither resolver, store, nor oracle.
-/

namespace Navigatrix.Sim

open Navigatrix.Ixon (Uses)

/-- Syntactic type-scheme test — share-free restriction of
`Erase.sortLike`. -/
def sortLikeP : Ixon.Expr → Bool
  | .sort _ => true
  | .all _ _ _ cod => sortLikeP cod
  | _ => false

/-- Is a binder with this mode and domain erased? Mirrors
`Erase.dropBinder` on the fragment. -/
def dropB (u : Uses) (dom : Ixon.Expr) : Bool :=
  u == .erased || sortLikeP dom

/-- Relational erasure on the pure fragment. The mask records, per
context slot, whether the binder was kept; dropped binders keep their
slot (arity-preserving erasure) but admit no variable occurrences. -/
inductive PErase : List Bool → Ixon.Expr → IxIR0.Expr → Prop where
  | var {mask : List Bool} {i : UInt64} :
      mask[i.toNat]? = some true →
      PErase mask (.var i) (.var i.toNat)
  | sortE {mask : List Bool} {u : UInt64} :
      PErase mask (.sort u) .erased
  | allE {mask : List Bool} {u : Uses} {o : Navigatrix.Ixon.Owned}
      {dom cod : Ixon.Expr} :
      PErase mask (.all u o dom cod) .erased
  | lamK {mask : List Bool} {u : Uses} {dom body : Ixon.Expr}
      {body' : IxIR0.Expr} :
      dropB u dom = false →
      PErase (true :: mask) body body' →
      PErase mask (.lam u dom body) (.lam u body')
  | lamD {mask : List Bool} {u : Uses} {dom body : Ixon.Expr}
      {body' : IxIR0.Expr} :
      dropB u dom = true →
      PErase (false :: mask) body body' →
      PErase mask (.lam u dom body) (.lam .many body')
  | app {mask : List Bool} {f a : Ixon.Expr} {f' a' : IxIR0.Expr} :
      PErase mask f f' →
      PErase mask a a' →
      PErase mask (.app f a) (.app f' a')
  | appE {mask : List Bool} {u : Uses} {dom body a : Ixon.Expr}
      {f' : IxIR0.Expr} :
      dropB u dom = true →
      PErase mask (.lam u dom body) f' →
      PErase mask (.app (.lam u dom body) a) (.app f' .erased)
  | letE {mask : List Bool} {nd : Bool} {ty val body : Ixon.Expr}
      {val' body' : IxIR0.Expr} :
      PErase mask val val' →
      PErase (true :: mask) body body' →
      PErase mask (.letE nd ty val body) (.letE .many val' body')

mutual
  /-- Source and target values related by erasure. Types are `◻`;
  closures relate through related environments and related bodies. -/
  inductive ValRel : Ixon.Eval.Value → IxIR0.Value → Prop where
    | sort {l} : ValRel (.sortV l) .erased
    | pi {u o F env dom cod} : ValRel (.piV u o F env dom cod) .erased
    | clos {mask : List Bool} {b : Bool} {u : Uses}
        {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value}
        {dom body : Ixon.Expr} {u' : Uses} {ρ : List IxIR0.Value}
        {body' : IxIR0.Expr} :
        EnvRel mask env ρ →
        PErase (b :: mask) body body' →
        ValRel (.closV u F env dom body) (.clos u' ρ body')

  /-- Environments related slot-wise along the mask. Dropped slots
  are unconstrained on both sides: no surviving occurrence reads
  them. -/
  inductive EnvRel : List Bool → List Ixon.Eval.Value →
      List IxIR0.Value → Prop where
    | nil : EnvRel [] [] []
    | keep {mask env ρ v v'} :
        ValRel v v' → EnvRel mask env ρ →
        EnvRel (true :: mask) (v :: env) (v' :: ρ)
    | drop {mask env ρ v v'} :
        EnvRel mask env ρ →
        EnvRel (false :: mask) (v :: env) (v' :: ρ)
end

private theorem bindOk {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem bindErr {ε α β : Type} (er : ε) (f : α → Except ε β) :
    ((Except.error er : Except ε α) >>= f) = Except.error er := rfl

private theorem envRel_lookup : ∀ (i : Nat) {mask : List Bool}
    {env : List Ixon.Eval.Value} {ρ : List IxIR0.Value},
    EnvRel mask env ρ →
    ∀ (v : Ixon.Eval.Value), mask[i]? = some true →
      env[i]? = some v → ∃ v', ρ[i]? = some v' ∧ ValRel v v' := by
  intro i
  induction i with
  | zero =>
    intro mask env ρ h v hm he
    cases h with
    | nil => simp at hm
    | keep hv henv =>
      simp only [List.getElem?_cons_zero] at he ⊢
      injection he with he'
      subst he'
      exact ⟨_, rfl, hv⟩
    | drop henv => simp at hm
  | succ j ihj =>
    intro mask env ρ h v hm he
    cases h with
    | nil => simp at hm
    | keep hv henv =>
      simp only [List.getElem?_cons_succ] at hm he ⊢
      exact ihj henv v hm he
    | drop henv =>
      simp only [List.getElem?_cons_succ] at hm he ⊢
      exact ihj henv v hm he

private theorem strongNat {P : Nat → Prop}
    (step : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have aux : ∀ k n, n < k → P n := by
    intro k
    induction k with
    | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
    | succ k ihk =>
      intro n hn
      exact step n fun m hm =>
        ihk m (Nat.lt_of_lt_of_le hm (Nat.lt_succ_iff.mp hn))
  exact fun n => aux (n + 1) n (Nat.lt_succ_self n)

private def SimAt (fuel : Nat) : Prop :=
  ∀ (ectx : Ixon.Eval.EvalCtx) (F : Ixon.Eval.Frame)
    (env : List Ixon.Eval.Value) (e : Ixon.Expr) (v : Ixon.Eval.Value)
    (mask : List Bool) (ρ : List IxIR0.Value) (e' : IxIR0.Expr)
    (ictx : IxIR0.Ctx),
    Ixon.Eval.eval ectx fuel F env e = .ok v →
    PErase mask e e' →
    EnvRel mask env ρ →
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧ ValRel v v'

private theorem simAt : ∀ fuel, SimAt fuel := by
  refine strongNat ?_
  intro fuel ih
  cases fuel with
  | zero =>
    intro ectx F env e v mask ρ e' ictx hev hpe henv
    rw [Ixon.Eval.eval.eq_def] at hev
    simp at hev
  | succ n =>
    intro ectx F env e v mask ρ e' ictx hev hpe henv
    cases hpe with
    | var hm =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      split at hev
      · rename_i w heq
        injection hev with hv
        subst hv
        obtain ⟨v', hρ, hrel⟩ := envRel_lookup _ henv _ hm heq
        refine ⟨1, v', ?_, hrel⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hρ]
      · simp at hev
    | sortE =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      split at hev
      · rename_i u heq
        injection hev with hv
        subst hv
        exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], ValRel.sort⟩
      · simp at hev
    | allE =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], ValRel.pi⟩
    | lamK hnd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], ValRel.clos henv hpb⟩
    | lamD hd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], ValRel.clos henv hpb⟩
    | letE hpv hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i nd ty val body val' body'
      cases hval : Ixon.Eval.eval ectx n F env val with
      | error err => rw [hval, bindErr] at hev; simp at hev
      | ok w =>
        rw [hval, bindOk] at hev
        obtain ⟨n₁, w', hw', hrelW⟩ :=
          ih n (by omega) ectx F env val w mask ρ val' ictx hval hpv henv
        obtain ⟨n₂, v', hv', hrel⟩ :=
          ih n (by omega) ectx F (w :: env) body v (true :: mask)
            (w' :: ρ) body' ictx hev hpb (EnvRel.keep hrelW henv)
        refine ⟨n₁ + n₂ + 1, v', ?_, hrel⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ by omega) hw', bindOk]
        exact IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ by omega) hv'
    | app hpf hpa =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i fS aS fT aT
      cases hf : Ixon.Eval.eval ectx n F env fS with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env aS with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, fv', hfv', hrelF⟩ :=
            ih n (by omega) ectx F env fS fv mask ρ fT ictx hf hpf henv
          obtain ⟨n₂, av', hav', hrelA⟩ :=
            ih n (by omega) ectx F env aS av mask ρ aT ictx ha hpa henv
          cases hrelF with
          | sort =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | pi =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | clos henvC hbodyC =>
            rename_i maskC bC uC FC envC domC bodyC uC' ρC bodyC'
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              have henv' : EnvRel (bC :: maskC) (av :: envC) (av' :: ρC) := by
                cases bC
                · exact EnvRel.drop henvC
                · exact EnvRel.keep hrelA henvC
              obtain ⟨n₃, v', hv', hrel⟩ :=
                ih g (by omega) ectx FC (av :: envC) bodyC v (bC :: maskC)
                  (av' :: ρC) bodyC' ictx hev hbodyC henv'
              refine ⟨n₁ + n₂ + n₃ + 2, v', ?_, hrel⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hfv', bindOk]
              rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hav', bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact IxIR0.eval_mono (show n₃ ≤ n₁ + n₂ + n₃ by omega) hv'
    | appE hd hlam =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i u dom body aS fT
      cases hf : Ixon.Eval.eval ectx n F env (.lam u dom body) with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env aS with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          cases n with
          | zero => rw [Ixon.Eval.eval.eq_def] at hf; simp at hf
          | succ g =>
            rw [Ixon.Eval.eval.eq_def] at hf
            dsimp only at hf
            injection hf with hfv
            subst hfv
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases hlam with
            | lamK hnd hpb => rw [hd] at hnd; simp at hnd
            | lamD hd' hpb =>
              rename_i bodyT
              obtain ⟨n₃, v', hv', hrel⟩ :=
                ih g (by omega) ectx F (av :: env) body v (false :: mask)
                  (.erased :: ρ) bodyT ictx hev hpb (EnvRel.drop henv)
              have hlamT : IxIR0.eval ictx (n₃ + 1) ρ (.lam .many bodyT) =
                  .ok (.clos .many ρ bodyT) := by rw [IxIR0.eval.eq_def]
              have hboxT : IxIR0.eval ictx (n₃ + 1) ρ .erased =
                  .ok .erased := by rw [IxIR0.eval.eq_def]
              refine ⟨n₃ + 2, v', ?_, hrel⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hlamT, bindOk, hboxT, bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact hv'

/-- **The erasure simulation (pure fragment).** If a source term
terminates with a value under the Ixon reference semantics, its
erasure terminates under the IxIR₀ semantics with a related value —
for any resolver, store, and oracle, since the fragment touches none
of them. -/
theorem erasure_sim {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value} {e : Ixon.Expr}
    {v : Ixon.Eval.Value} {mask : List Bool} {ρ : List IxIR0.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase mask e e') (henv : EnvRel mask env ρ) :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧ ValRel v v' :=
  simAt fuel ectx F env e v mask ρ e' ictx hev hpe henv

/-- Closed-term corollary. -/
theorem erasure_sim_closed {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase [] e e') :
    ∃ fuel' v', IxIR0.eval ictx fuel' [] e' = .ok v' ∧ ValRel v v' :=
  erasure_sim hev hpe EnvRel.nil

/-! Executable-pass agreement spot checks: on fragment terms, the
`Erase.eraseExpr` output is exactly a `PErase`-related target. -/

private def ectx₀ : Erase.EraseCtx := { resolve := fun _ => none }

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.lam .many (.var 9) (.var 0)) with
  | .ok (.lam .many (.var 0)) => true
  | _ => false)

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.lam .many (.sort 0) (.lam .many (.var 0) (.var 0))) with
  | .ok (.lam .many (.lam .many (.var 0))) => true
  | _ => false)

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.app (.lam .many (.sort 0) (.sort 1)) (.sort 0)) with
  | .ok (.app (.lam .many .erased) .erased) => true
  | _ => false)

example : PErase [] (.lam .many (.var 9) (.var 0)) (.lam .many (.var 0)) :=
  .lamK rfl (.var rfl)

example :
    PErase [] (.lam .many (.sort 0) (.lam .many (.var 0) (.var 0)))
      (.lam .many (.lam .many (.var 0))) :=
  .lamD rfl (.lamK rfl (.var rfl))

end Navigatrix.Sim
