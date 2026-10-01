import Compilatrix.Fir.Semantics
import Compilatrix.Sem.Agrees

/-! # Fir: the evaluator in `bind` form

One equation per rule of `Fir.eval`, `evalAlts` and `evalCall`, with every
sequencing step written as `Result.bind`, every charge as `Sem.later` and
every partial lookup as `Result.ofOption` (decision D-1, M2.4). Clock
monotonicity (`Fir.Proof.Mono`), the Anf → Fir simulation and the Fir → Own
refinement reason through these equations only. -/

set_option autoImplicit false

namespace Compilatrix.Fir

open Compilatrix.Sem (Result later)

variable (P : Program) (k : Nat) (ρ : Env) (J : List JEntry)

/-! ## Arguments -/

theorem evalArgs_nil : evalArgs ρ [] = some [] := rfl

theorem evalArgs_cons (a : Arg) (as : List Arg) :
    evalArgs ρ (a :: as) = (a.eval ρ).bind fun v => (evalArgs ρ as).map (v :: ·) := by
  simp only [evalArgs]
  cases a.eval ρ <;> cases evalArgs ρ as <;> rfl

theorem evalArgs_length : ∀ {as : List Arg} {vs : List Val}, evalArgs ρ as = some vs →
    vs.length = as.length
  | [], vs, h => by simp [evalArgs] at h; subst h; rfl
  | a :: as, vs, h => by
    rw [evalArgs_cons] at h
    cases ha : a.eval ρ with
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
def callFun (k : Nat) (fd : Fun) (vs : List Val) : Result Val :=
  if vs.length = fd.params.length then
    later k fun k => eval P k (bindAll .leaf (fd.params.map (·.1)) vs) [] fd.body
  else .stuck

theorem evalCall_eq (f : FunId) (vs : List Val) :
    evalCall P k f vs = (Result.ofOption (P.fun? f)).bind fun fd => callFun P k fd vs := by
  rw [evalCall]
  cases P.fun? f with
  | none => rfl
  | some fd =>
    simp only [Result.ofOption, Result.bind_ok, callFun]
    split
    · cases k <;> rfl
    · rfl

theorem evalCall_of {f : FunId} {fd : Fun} (h : P.fun? f = some fd) (vs : List Val) :
    evalCall P k f vs = callFun P k fd vs := by
  rw [evalCall_eq, h]; rfl

theorem run_eq (f : FunId) (args : List Val) : run P k f args = evalCall P k f args := rfl

/-- A jump to entry `e` with the stack `rest` below it: charged inside the
entry's own body. -/
def jumpTo (k : Nat) (e : JEntry) (rest : List JEntry) (vs : List Val) : Result Val :=
  if vs.length = e.params.length then
    if e.charged then later k fun k => eval P k (bindAll e.env e.params vs) (e.after rest) e.body
    else eval P k (bindAll e.env e.params vs) (e.after rest) e.body
  else .stuck

/-! ## Code -/

theorem eval_bindCall (x : Var) (f : FunId) (as : List Arg) (c : Code) :
    eval P k ρ J (.bind x (.call f as) c) =
      (Result.ofOption (evalArgs ρ as)).bind fun vs =>
        (evalCall P k f vs).bind fun v => eval P k (ρ.insert x v) J c := by
  rw [eval]
  cases evalArgs ρ as with
  | none => rfl
  | some vs => simp only [Result.ofOption, Result.bind_ok]; cases evalCall P k f vs <;> rfl

theorem eval_bindRhs (x : Var) (r : Rhs) (c : Code) (hr : ∀ f as, r ≠ .call f as) :
    eval P k ρ J (.bind x r c) = (evalRhs P ρ r).bind fun v => eval P k (ρ.insert x v) J c := by
  cases r with
  | call f as => exact absurd rfl (hr f as)
  | _ =>
    rw [eval]
    all_goals first
      | (intro _ _ h; cases h)
      | (cases evalRhs P ρ _ <;> rfl)

theorem eval_bind_arg (x : Var) (a : Arg) (c : Code) :
    eval P k ρ J (.bind x (.arg a) c) =
      (evalRhs P ρ (.arg a)).bind fun v => eval P k (ρ.insert x v) J c :=
  eval_bindRhs P k ρ J x _ c (by intro _ _ h; cases h)

theorem eval_bind_ctor (x : Var) (ci : CtorInfo) (as : List Arg) (c : Code) :
    eval P k ρ J (.bind x (.ctor ci as) c) =
      (evalRhs P ρ (.ctor ci as)).bind fun v => eval P k (ρ.insert x v) J c :=
  eval_bindRhs P k ρ J x _ c (by intro _ _ h; cases h)

theorem eval_bind_proj (x y : Var) (ci : Key.CtorKey) (i : Nat) (c : Code) :
    eval P k ρ J (.bind x (.proj y ci i) c) =
      (evalRhs P ρ (.proj y ci i)).bind fun v => eval P k (ρ.insert x v) J c :=
  eval_bindRhs P k ρ J x _ c (by intro _ _ h; cases h)

theorem eval_bind_prim (x : Var) (op : Lam.Prim) (as : List Arg) (c : Code) :
    eval P k ρ J (.bind x (.prim op as) c) =
      (evalRhs P ρ (.prim op as)).bind fun v => eval P k (ρ.insert x v) J c :=
  eval_bindRhs P k ρ J x _ c (by intro _ _ h; cases h)

theorem eval_jp (j : JoinId) (ps : List Var) (r : Bool) (b c : Code) :
    eval P k ρ J (.jp j ps r b c) =
      eval P k ρ ({ id := j, charged := false, env := ρ, params := ps, body := b, isRec := r } :: J) c := by
  rw [eval]

theorem eval_jmp (j : JoinId) (as : List Arg) :
    eval P k ρ J (.jmp j as) =
      (Result.ofOption (lookupJ j J)).bind fun p =>
        (Result.ofOption (evalArgs ρ as)).bind fun vs => jumpTo P k p.1 p.2 vs := by
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

theorem eval_jmp_of {j : JoinId} {as : List Arg} {e : JEntry} {rest : List JEntry} {vs : List Val}
    (h₁ : lookupJ j J = some (e, rest)) (h₂ : evalArgs ρ as = some vs) :
    eval P k ρ J (.jmp j as) = jumpTo P k e rest vs := by
  rw [eval_jmp, h₁, h₂]; rfl

theorem eval_case (x : Var) (alts : List Alt) (d : Option Code) :
    eval P k ρ J (.case x alts d) = (Result.ofOption (ρ.get? x)).bind fun v =>
      match v.asCtor P.known with
      | some (key, _) => evalAlts P k ρ J key alts d
      | none => .stuck := by
  rw [eval]; cases ρ.get? x <;> rfl

theorem eval_ret (a : Arg) : eval P k ρ J (.ret a) = Result.ofOption (a.eval ρ) := by
  rw [eval]

theorem eval_tcall (f : FunId) (as : List Arg) :
    eval P k ρ J (.tcall f as) =
      (Result.ofOption (evalArgs ρ as)).bind fun vs => evalCall P k f vs := by
  rw [eval]; cases evalArgs ρ as <;> rfl

theorem eval_trap : eval P k ρ J .trap = .trap := by
  rw [eval]

/-! ## Alternatives -/

theorem evalAlts_nil (key : Key.CtorKey) (d : Option Code) :
    evalAlts P k ρ J key [] d = (match d with | some c => eval P k ρ J c | none => .stuck) := by
  cases d <;> rw [evalAlts]

theorem evalAlts_cons (key key' : Key.CtorKey) (body : Code) (rest : List Alt) (d : Option Code) :
    evalAlts P k ρ J key (.mk key' body :: rest) d =
      if key' = key then eval P k ρ J body else evalAlts P k ρ J key rest d := by
  rw [evalAlts]

/-! ## Right-hand sides -/

theorem evalRhs_arg (a : Arg) : evalRhs P ρ (.arg a) = Result.ofOption (a.eval ρ) := rfl

theorem evalRhs_ctor (c : CtorInfo) (as : List Arg) :
    evalRhs P ρ (.ctor c as) = (Result.ofOption (evalArgs ρ as)).bind fun vs =>
      if vs.length = c.arity then .ok (.ctor c vs) else .stuck := by
  simp only [evalRhs]; cases evalArgs ρ as <;> rfl

/-- A projection of a value. -/
def projVal (c : Key.CtorKey) (i : Nat) (v : Val) : Result Val :=
  match v.asCtor P.known with
  | some (c', fs) => if c' = c then Result.ofOption fs[i]? else .stuck
  | none => .stuck

theorem evalRhs_proj (x : Var) (c : Key.CtorKey) (i : Nat) :
    evalRhs P ρ (.proj x c i) = (Result.ofOption (ρ.get? x)).bind (projVal P c i) := by
  simp only [evalRhs]; cases ρ.get? x <;> rfl

theorem evalRhs_prim (op : Lam.Prim) (as : List Arg) :
    evalRhs P ρ (.prim op as) = (Result.ofOption (evalArgs ρ as)).bind (primResult P op) := by
  simp only [evalRhs]; cases evalArgs ρ as <;> rfl

end Compilatrix.Fir
