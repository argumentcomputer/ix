import Compilatrix.Own.Plain.Semantics
import Compilatrix.Sem.Agrees

/-! Bind-form interface for the scratch plain-RC evaluator. Future simulation
proofs use these equations instead of depending on evaluator match structure.
-/

set_option autoImplicit false
namespace Compilatrix.Own.Plain
open Compilatrix.Sem (Result later)
open Compilatrix.Fir (Var FunId JoinId Arg)

variable (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry) (H : Own.Heap)

def callFun (k : Nat) (fd : Fir.Fun) (body : Code) (vs : List RVal) (H : Heap) :
    Result (RVal × Heap) :=
  if vs.length = fd.params.length then
    later k fun k => eval P k (Own.bindAll .leaf (fd.params.map (·.1)) vs) [] H body
  else .stuck

theorem evalCall_eq (f : FunId) (vs : List RVal) :
    evalCall P k f vs H = (Result.ofOption (P.source.fun? f)).bind fun fd =>
      (Result.ofOption (P.bodies.get? f)).bind fun body => callFun P k fd body vs H := by
  rw [evalCall]
  cases P.source.fun? f with
  | none => cases P.bodies.get? f <;> rfl
  | some fd =>
    cases P.bodies.get? f with
    | none => rfl
    | some body =>
      simp only [Result.ofOption, Result.bind_ok, callFun]
      split
      · cases k <;> rfl
      · rfl

theorem evalCall_of {f : FunId} {fd : Fir.Fun} {body : Code}
    (hf : P.source.fun? f = some fd) (hb : P.bodies.get? f = some body) (vs : List RVal) :
    evalCall P k f vs H = callFun P k fd body vs H := by
  rw [evalCall_eq, hf, hb]; rfl

def jumpTo (k : Nat) (e : JEntry) (rest : List JEntry) (vs : List RVal) (H : Heap) :
    Result (RVal × Heap) :=
  if vs.length = e.params.length then
    if e.charged then later k fun k => eval P k (Own.bindAll e.env e.params vs) (e.after rest) H e.body
    else eval P k (Own.bindAll e.env e.params vs) (e.after rest) H e.body
  else .stuck

theorem eval_act (a : Action) (c : Code) :
    eval P k ρ J H (.act a c) = (evalAction ρ H a).bind fun H' => eval P k ρ J H' c := by
  rw [eval]
  cases evalAction ρ H a <;> rfl

theorem eval_bindCall (x : Var) (f : FunId) (args : List Arg) (c : Code) :
    eval P k ρ J H (.bind x (.call f args) c) =
      (Result.ofOption (Own.evalArgs ρ args)).bind fun vs =>
        (evalCall P k f vs H).bind fun p => eval P k (ρ.insert x p.1) J p.2 c := by
  rw [eval]
  cases Own.evalArgs ρ args with
  | none => rfl
  | some vs =>
    simp only [Result.ofOption, Result.bind_ok]
    cases evalCall P k f vs H <;> rfl

theorem eval_bindRhs (x : Var) (r : Fir.Rhs) (c : Code) (hr : ∀ f args, r ≠ .call f args) :
    eval P k ρ J H (.bind x r c) =
      (evalRhs P.tables ρ H r).bind fun p => eval P k (ρ.insert x p.1) J p.2 c := by
  rw [eval]
  · cases evalRhs P.tables ρ H r <;> rfl
  · intro f args h; exact hr f args h

theorem eval_jp (j : JoinId) (ps captured : List Var) (rec : Bool) (body c : Code) :
    eval P k ρ J H (.jp j ps captured rec body c) =
      eval P k ρ ({
        id := j, charged := false, env := ρ, params := ps, body, isRec := rec } :: J) H c := by
  rw [eval]

theorem eval_jmp (j : JoinId) (args : List Arg) :
    eval P k ρ J H (.jmp j args) =
      (Result.ofOption (lookupJ j J)).bind fun p =>
        (Result.ofOption (Own.evalArgs ρ args)).bind fun vs => jumpTo P k p.1 p.2 vs H := by
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
      cases h₂ : Own.evalArgs ρ args with
      | none => simp [Result.ofOption, Result.bind]
      | some vs => exact absurd h₂ (hne p.1 p.2 vs h₁)

theorem eval_case (x : Var) (alts : List Alt) (d : Option Code) :
    eval P k ρ J H (.case x alts d) = (Result.ofOption (ρ.get? x)).bind fun v =>
      match v.asCtor P.source.known H with
      | some (key, _) => evalAlts P k ρ J H key alts d
      | none => .stuck := by
  rw [eval]; cases ρ.get? x <;> rfl

theorem eval_ret (a : Arg) :
    eval P k ρ J H (.ret a) = (Result.ofOption (Own.evalArg ρ a)).bind fun v => .ok (v, H) := by
  rw [eval]; cases Own.evalArg ρ a <;> rfl

theorem eval_tcall (f : FunId) (args : List Arg) :
    eval P k ρ J H (.tcall f args) =
      (Result.ofOption (Own.evalArgs ρ args)).bind fun vs => evalCall P k f vs H := by
  rw [eval]; cases Own.evalArgs ρ args <;> rfl

theorem eval_trap : eval P k ρ J H .trap = .trap := by rw [eval]

theorem evalAlts_nil (key : Key.CtorKey) (d : Option Code) :
    evalAlts P k ρ J H key [] d =
      (match d with | some c => eval P k ρ J H c | none => .stuck) := by
  cases d <;> rw [evalAlts]

theorem evalAlts_cons (key key' : Key.CtorKey) (body : Code) (rest : List Alt) (d : Option Code) :
    evalAlts P k ρ J H key (.mk key' body :: rest) d =
      if key' = key then eval P k ρ J H body else evalAlts P k ρ J H key rest d := by
  rw [evalAlts]


end Compilatrix.Own.Plain
