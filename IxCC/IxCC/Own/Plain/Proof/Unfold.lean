import IxCC.Own.Plain.Semantics
import IxCC.Sem.Agrees

/-! Bind-form interface for the scratch plain-RC evaluator. Future simulation
proofs use these equations instead of depending on evaluator match structure.
-/

set_option autoImplicit false
namespace IxCC.Own.Plain
open IxCC.Sem (Result later)
open IxCC.Fir (Var FunId JoinId Arg)

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

theorem eval_act (a : Action) (c : Code) {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.act a c) slots = (evalAction ρ H a).bind fun H' => eval P k ρ J H' c slots := by
  rw [eval]
  cases evalAction ρ H a <;> rfl

theorem eval_bindCall (x : Var) (f : FunId) (args : List Arg) (c : Code)
    {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.bind x (.call f args) c) slots =
      (Result.ofOption (Own.evalArgs ρ args)).bind fun vs =>
        (evalCall P k f vs H).bind fun p => eval P k (ρ.insert x p.1) J p.2 c slots := by
  rw [eval]
  cases Own.evalArgs ρ args with
  | none => rfl
  | some vs =>
    simp only [Result.ofOption, Result.bind_ok]
    cases evalCall P k f vs H <;> rfl

theorem eval_bindRhs (x : Var) (r : Fir.Rhs) (c : Code) (hr : ∀ f args, r ≠ .call f args)
    {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.bind x r c) slots =
      (evalRhs P.tables ρ H r).bind fun p => eval P k (ρ.insert x p.1) J p.2 c slots := by
  rw [eval]
  · cases evalRhs P.tables ρ H r <;> rfl
  · intro f args h; exact hr f args h

theorem eval_reset (s : Nat) (x : Var) (ctor : Fir.CtorInfo) (fields : List (Option Var))
    (uniq : Bool) (c : Code) {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.reset s x ctor fields uniq c) slots =
      (evalResetMask ρ H x ctor (fieldsMask fields) uniq).bind fun p =>
        eval P k ρ J p.2 c (slots.insert s p.1) := by
  rw [eval]
  cases evalResetMask ρ H x ctor (fieldsMask fields) uniq <;> rfl

theorem eval_reuse (x : Var) (s : Nat) (ctor : Fir.CtorInfo) (args : List Arg)
    (uniq : Bool) (c : Code) {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.reuse x s ctor args uniq c) slots =
      (Result.ofOption (slots.get? s)).bind fun sv =>
        (evalReuseVal ρ H sv ctor args uniq).bind fun p =>
          eval P k (ρ.insert x p.1) J p.2 c (slots.erase s) := by
  rw [eval]
  cases slots.get? s with
  | none => rfl
  | some sv =>
    simp only [Result.ofOption, Result.bind_ok]
    cases evalReuseVal ρ H sv ctor args uniq <;> rfl

theorem eval_dropSlot (s : Nat) (c : Code) {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.dropSlot s c) slots =
      (Result.ofOption (slots.get? s)).bind fun sv =>
        (evalDropVal H sv).bind fun H' =>
          eval P k ρ J H' c (slots.erase s) := by
  rw [eval]
  cases slots.get? s with
  | none => rfl
  | some sv =>
    simp only [Result.ofOption, Result.bind_ok]
    cases evalDropVal H sv <;> rfl

theorem eval_jp (j : JoinId) (ps captured : List Var) (rec : Bool) (body c : Code)
    {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.jp j ps captured rec body c) slots =
      eval P k ρ ({
        id := j, charged := false, env := ρ, params := ps, body, isRec := rec } :: J) H c slots := by
  rw [eval]

theorem eval_jmp (j : JoinId) (args : List Arg) {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.jmp j args) slots =
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

theorem eval_case (x : Var) (alts : List Alt) (d : Option Code)
    {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.case x alts d) slots = (Result.ofOption (ρ.get? x)).bind fun v =>
      match v.asCtor P.source.known H with
      | some (key, _) => evalAlts P k ρ J H key alts d slots
      | none => .stuck := by
  rw [eval]; cases ρ.get? x <;> rfl

theorem eval_ret (a : Arg) {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.ret a) slots = (Result.ofOption (Own.evalArg ρ a)).bind fun v => .ok (v, H) := by
  rw [eval]; cases Own.evalArg ρ a <;> rfl

theorem eval_tcall (f : FunId) (args : List Arg) {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H (.tcall f args) slots =
      (Result.ofOption (Own.evalArgs ρ args)).bind fun vs => evalCall P k f vs H := by
  rw [eval]; cases Own.evalArgs ρ args <;> rfl

theorem eval_trap {slots : Src.NatMap Own.RVal} :
    eval P k ρ J H .trap slots = .trap := by rw [eval]

theorem evalAlts_nil (key : Key.CtorKey) (d : Option Code)
    {slots : Src.NatMap Own.RVal} :
    evalAlts P k ρ J H key [] d slots =
      (match d with | some c => eval P k ρ J H c slots | none => .stuck) := by
  cases d <;> rw [evalAlts]

theorem evalAlts_cons (key key' : Key.CtorKey) (body : Code) (rest : List Alt) (d : Option Code)
    {slots : Src.NatMap Own.RVal} :
    evalAlts P k ρ J H key (.mk key' body :: rest) d slots =
      if key' = key then eval P k ρ J H body slots else evalAlts P k ρ J H key rest d slots := by
  rw [evalAlts]


end IxCC.Own.Plain
