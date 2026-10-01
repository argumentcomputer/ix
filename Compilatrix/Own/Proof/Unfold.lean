import Compilatrix.Own.Semantics
import Compilatrix.Sem.Agrees

/-! # Own: the evaluator in `bind` form

One equation per rule of `Own.eval`, `evalAlts` and `evalCall`, with every
sequencing step written as `Result.bind`, every charge as `Sem.later` and
every partial lookup as `Result.ofOption` (decision D-1, M2.4). Clock
monotonicity (`Own.Proof.Mono`), the Fir → Own refinement and the Own → Cfg
simulation reason through these equations only. -/

set_option autoImplicit false

namespace Compilatrix.Own

open Compilatrix.Sem (Result later)
open Compilatrix.Fir (Var FunId JoinId Arg)

variable (pol : AllocPol) (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (H : Heap)

/-! ## Arguments -/

theorem evalArgs_nil : evalArgs ρ [] = some [] := rfl

theorem evalArgs_cons (a : Arg) (as : List Arg) :
    evalArgs ρ (a :: as) = (evalArg ρ a).bind fun v => (evalArgs ρ as).map (v :: ·) := by
  simp only [evalArgs]
  cases evalArg ρ a <;> cases evalArgs ρ as <;> rfl

theorem evalArgs_length : ∀ {as : List Arg} {vs : List RVal}, evalArgs ρ as = some vs →
    vs.length = as.length
  | [], vs, h => by simp [evalArgs] at h; subst h; rfl
  | a :: as, vs, h => by
    rw [evalArgs_cons] at h
    cases ha : evalArg ρ a with
    | none => rw [ha] at h; cases h
    | some v =>
      rw [ha] at h
      cases hs : evalArgs ρ as with
      | none => rw [hs] at h; cases h
      | some ws =>
        rw [hs] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [evalArgs_length hs]

/-! ## Calls and jumps -/

/-- Entering function `fd` on argument values: charged. -/
def callFun (k : Nat) (fd : Fun) (vs : List RVal) (H : Heap) : Result (RVal × Heap) :=
  if vs.length = fd.params.length then
    later k fun k => eval pol P k (bindAll .leaf fd.params vs) [] H fd.body
  else .stuck

theorem evalCall_eq (f : FunId) (vs : List RVal) :
    evalCall pol P k f vs H = (Result.ofOption (P.fun? f)).bind fun fd => callFun pol P k fd vs H := by
  rw [evalCall]
  cases P.fun? f with
  | none => rfl
  | some fd =>
    simp only [Result.ofOption, Result.bind_ok, callFun]
    split
    · cases k <;> rfl
    · rfl

theorem evalCall_of {f : FunId} {fd : Fun} (h : P.fun? f = some fd) (vs : List RVal) :
    evalCall pol P k f vs H = callFun pol P k fd vs H := by
  rw [evalCall_eq, h]; rfl

theorem run_eq (f : FunId) (args : List RVal) : run pol P k f args H = evalCall pol P k f args H := rfl

/-- A jump to entry `e` with the stack `rest` below it: charged inside the
entry's own body. -/
def jumpTo (k : Nat) (e : JEntry) (rest : List JEntry) (vs : List RVal) (H : Heap) :
    Result (RVal × Heap) :=
  if vs.length = e.params.length then
    if e.charged then later k fun k => eval pol P k (bindAll e.env e.params vs) (e.after rest) H e.body
    else eval pol P k (bindAll e.env e.params vs) (e.after rest) H e.body
  else .stuck

/-! ## Code -/

theorem eval_bindCall (x : Var) (f : FunId) (as : List Arg) (c : Code) :
    eval pol P k ρ J H (.bind x (.fir (.call f as)) c) =
      (Result.ofOption (evalArgs ρ as)).bind fun vs =>
        (evalCall pol P k f vs H).bind fun p => eval pol P k (ρ.insert x p.1) J p.2 c := by
  rw [eval]
  cases evalArgs ρ as with
  | none => rfl
  | some vs => simp only [Result.ofOption, Result.bind_ok]; cases evalCall pol P k f vs H <;> rfl

theorem eval_bindRhs (x : Var) (r : Rhs) (c : Code) (hr : ∀ f as, r ≠ .fir (.call f as)) :
    eval pol P k ρ J H (.bind x r c) =
      (evalRhs pol P.tables ρ H r).bind fun p => eval pol P k (ρ.insert x p.1) J p.2 c := by
  rw [eval]
  · cases evalRhs pol P.tables ρ H r <;> rfl
  · intro f as h; exact hr f as h

theorem eval_jp (j : JoinId) (ps : List (Var × PSig)) (φ : List (Var × Nat)) (r : Bool) (b c : Code) :
    eval pol P k ρ J H (.jp j ps φ r b c) =
      eval pol P k ρ ({ id := j, charged := false, env := ρ, params := ps.map (·.1), body := b
                        isRec := r } :: J) H c := by
  rw [eval]

theorem eval_jmp (j : JoinId) (as : List Arg) :
    eval pol P k ρ J H (.jmp j as) =
      (Result.ofOption (lookupJ j J)).bind fun p =>
        (Result.ofOption (evalArgs ρ as)).bind fun vs => jumpTo pol P k p.1 p.2 vs H := by
  rw [eval]
  split
  · next _ e rest vs h₁ h₂ =>
    rw [h₁, h₂]
    simp only [Result.ofOption, Result.bind_ok, jumpTo]
    split
    · split
      · cases k <;> rfl
      · rfl
    · rfl
  · next _ hne =>
    cases h₁ : lookupJ j J with
    | none => rfl
    | some p =>
      cases h₂ : evalArgs ρ as with
      | none => simp [Result.ofOption, Result.bind]
      | some vs => exact absurd h₂ (hne p.1 p.2 vs h₁)

theorem eval_case (x : Var) (alts : List Alt) (d : Option Code) :
    eval pol P k ρ J H (.case x alts d) = (Result.ofOption (ρ.get? x)).bind fun v =>
      match v.asCtor P.known H with
      | some (key, _) => evalAlts pol P k ρ J H key alts d
      | none => .stuck := by
  rw [eval]; cases ρ.get? x <;> rfl

theorem eval_ret (a : Arg) :
    eval pol P k ρ J H (.ret a) = (Result.ofOption (evalArg ρ a)).bind fun v => .ok (v, H) := by
  rw [eval]; cases evalArg ρ a <;> rfl

theorem eval_tcall (f : FunId) (as : List Arg) :
    eval pol P k ρ J H (.tcall f as) =
      (Result.ofOption (evalArgs ρ as)).bind fun vs => evalCall pol P k f vs H := by
  rw [eval]; cases evalArgs ρ as <;> rfl

theorem eval_trap : eval pol P k ρ J H .trap = .trap := by
  rw [eval]

/-! ## Alternatives -/

theorem evalAlts_nil (key : Key.CtorKey) (d : Option Code) :
    evalAlts pol P k ρ J H key [] d =
      (match d with | some c => eval pol P k ρ J H c | none => .stuck) := by
  cases d <;> rw [evalAlts]

theorem evalAlts_cons (key key' : Key.CtorKey) (body : Code) (rest : List Alt) (d : Option Code) :
    evalAlts pol P k ρ J H key (.mk key' body :: rest) d =
      if key' = key then eval pol P k ρ J H body else evalAlts pol P k ρ J H key rest d := by
  rw [evalAlts]

end Compilatrix.Own
