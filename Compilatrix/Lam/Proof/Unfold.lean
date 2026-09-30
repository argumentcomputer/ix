import Compilatrix.Lam.Semantics

/-! # Lam: the evaluator in `bind` form

One equation per rule of `Lam.eval`, `apply`, `force`, `evalList` and
`evalAlts`, with every sequencing step written as `Result.bind` (M2.2). The
definitions spell each step out as a five-way `match`; these equations let
clock monotonicity and the erasure simulation reason one bind at a time. -/

namespace Compilatrix.Lam

open Compilatrix.Sem (Result)

variable (P : Program) (k : Nat) (ρ : Env)

theorem eval_var (i : Nat) :
    eval P k ρ (.var i) = (match ρ[i]? with | some s => force P k s | none => .stuck) := by
  rw [eval]; rfl

theorem eval_glob (g : GlobalId) :
    eval P k ρ (.glob g) = (match P.global? g with
      | some gl => (match k with | 0 => .timeout | k + 1 => eval P k [] gl.body)
      | none => .stuck) := by
  rw [eval]; rfl

theorem eval_lam (m : Mode) (c : Ixon.V3.BinderContract) (b : Term) :
    eval P k ρ (.lam m c b) = .ok (.clos ρ b) := by
  rw [eval]

theorem eval_app (f a : Term) (m : Mode) :
    eval P k ρ (.app f a m) = (eval P k ρ f).bind fun fv =>
      match m with
      | .strict => (eval P k ρ a).bind fun av => apply P k fv (.val av)
      | .name => apply P k fv (.name ρ a) := by
  rw [eval]
  cases eval P k ρ f <;> cases m <;> (try cases eval P k ρ a) <;> rfl

theorem eval_app_strict (f a : Term) :
    eval P k ρ (.app f a .strict) = (eval P k ρ f).bind fun fv =>
      (eval P k ρ a).bind fun av => apply P k fv (.val av) := eval_app P k ρ f a .strict

theorem eval_app_name (f a : Term) :
    eval P k ρ (.app f a .name) = (eval P k ρ f).bind fun fv => apply P k fv (.name ρ a) :=
  eval_app P k ρ f a .name

theorem eval_letE (c : Ixon.V3.LetContract) (v b : Term) :
    eval P k ρ (.letE c v b) = (eval P k ρ v).bind fun x => eval P k (.val x :: ρ) b := by
  rw [eval]; cases eval P k ρ v <;> rfl

theorem eval_con (c : Key.CtorKey) (fs : List Term) :
    eval P k ρ (.con c fs) = (evalList P k ρ fs).bind fun vs => .ok (.con c vs) := by
  rw [eval]; cases evalList P k ρ fs <;> rfl

theorem eval_case (s : Term) (alts : List Alt) (d : Option Term) :
    eval P k ρ (.case s alts d) = (eval P k ρ s).bind fun v =>
      match v.asCtor P.known with
      | some (c, fs) => evalAlts P k ρ c fs alts d
      | none => .stuck := by
  rw [eval]; cases eval P k ρ s <;> rfl

theorem eval_proj (c : Key.CtorKey) (i : Nat) (s : Term) :
    eval P k ρ (.proj c i s) = (eval P k ρ s).bind fun v =>
      match v with
      | .con c' fs => if c' = c then Result.ofOption fs[i]? else .stuck
      | _ => .stuck := by
  rw [eval]
  cases eval P k ρ s with
  | ok v => cases v <;> rfl
  | _ => rfl

theorem eval_lit (l : Lit) : eval P k ρ (.lit l) = .ok (.lit l) := by
  rw [eval]

theorem eval_prim (p : Prim) (args : List Term) :
    eval P k ρ (.prim p args) = (evalList P k ρ args).bind (primResult P.known p) := by
  rw [eval]; cases evalList P k ρ args <;> rfl

theorem eval_tick (t : Term) :
    eval P k ρ (.tick t) = (match k with | 0 => .timeout | k + 1 => eval P k ρ t) := by
  rw [eval.eq_def]; rfl

theorem eval_box' : eval P k ρ .box = .ok .box := by
  rw [eval]

theorem eval_trap' : eval P k ρ .trap = .trap := by
  rw [eval]

theorem apply_clos (ρ' : Env) (b : Term) (s : Slot) :
    apply P k (.clos ρ' b) s = (match k with | 0 => .timeout | k + 1 => eval P k (s :: ρ') b) := by
  rw [apply.eq_def]; rfl

theorem apply_not_clos (f : Val) (s : Slot) (h : ∀ ρ' b, f ≠ .clos ρ' b) :
    apply P k f s = .stuck := by
  rw [apply.eq_def]
  split
  · next ρ' b => exact absurd rfl (h ρ' b)
  · rfl

theorem force_val (v : Val) : force P k (.val v) = .ok v := by
  rw [force]

theorem force_name (ρ' : Env) (t : Term) :
    force P k (.name ρ' t) = (match k with | 0 => .timeout | k + 1 => eval P k ρ' t) := by
  rw [force.eq_def]; rfl

theorem evalList_nil : evalList P k ρ [] = .ok [] := by
  rw [evalList]

theorem evalList_cons (t : Term) (ts : List Term) :
    evalList P k ρ (t :: ts) = (eval P k ρ t).bind fun v =>
      (evalList P k ρ ts).bind fun vs => .ok (v :: vs) := by
  rw [evalList]
  cases eval P k ρ t <;> (try cases evalList P k ρ ts) <;> rfl

theorem evalAlts_nil (c : Key.CtorKey) (fs : List Val) (d : Option Term) :
    evalAlts P k ρ c fs [] d = (match d with | some t => eval P k ρ t | none => .stuck) := by
  rw [evalAlts.eq_def]; rfl

theorem evalAlts_cons (c : Key.CtorKey) (fs : List Val) (key : Key.CtorKey) (n : Nat)
    (body : Term) (rest : List Alt) (d : Option Term) :
    evalAlts P k ρ c fs (.mk key n body :: rest) d =
      if key = c ∧ n = fs.length then eval P k (fs.reverse.map .val ++ ρ) body
      else evalAlts P k ρ c fs rest d := by
  rw [evalAlts]

theorem applyAll_nil (f : Val) : applyAll P k f [] = .ok f := rfl

theorem applyAll_cons (f : Val) (s : Slot) (ss : List Slot) :
    applyAll P k f (s :: ss) = (apply P k f s).bind fun v => applyAll P k v ss := by
  simp only [applyAll]; cases apply P k f s <;> rfl

end Compilatrix.Lam
