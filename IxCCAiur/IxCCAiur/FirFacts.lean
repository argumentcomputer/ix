import IxCC.Fir.Proof.Mono
import IxCC.Src.Proof.NatMap

/-! # Facts about `IxCC.Fir` in the forms the lowering's proofs use

The lowering to Formal Aiur (`IxCCAiur.Lower`) and its backward simulation
(`IxCCAiur.Backward`) are stated over the compiler's own `IxCC.Fir`. Three
families of facts are used there in a form the compiler's proofs do not state:

* clock monotonicity as "a value at clock `k` is the value at every later
  clock" (the compiler states `Sem.ClockMono`; these are its instances);
* a lookup at another key after an insertion, with the keys in the order the
  proofs' call sites give them;
* the meaning of each `Nat` primitive on literals as an equation
  (`Lam.Prim.sem` is defined through `Src.PrimOp.eval2`).

Nothing here is new about `Fir`; every lemma is one line from the compiler's. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.FirFacts

/-! ## Clock monotonicity, on values -/

theorem eval_mono (P : Fir.Program) {k k' : Nat} {ρ : Fir.Env} {J : List Fir.JEntry}
    {c : Fir.Code} {v : Fir.Val} (hok : Fir.eval P k ρ J c = .ok v) (hk : k ≤ k') :
    Fir.eval P k' ρ J c = .ok v :=
  (Fir.eval_agrees P k k' hk ρ J c (by rw [hok]; intro h; cases h)).trans hok

theorem evalCall_mono (P : Fir.Program) {k k' : Nat} {f : Fir.FunId} {vs : List Fir.Val}
    {v : Fir.Val} (hok : Fir.evalCall P k f vs = .ok v) (hk : k ≤ k') :
    Fir.evalCall P k' f vs = .ok v :=
  (Fir.evalCall_agrees P hk f vs (by rw [hok]; intro h; cases h)).trans hok

theorem run_mono (P : Fir.Program) {k k' : Nat} {f : Fir.FunId} {vs : List Fir.Val}
    {v : Fir.Val} (hok : Fir.run P k f vs = .ok v) (hk : k ≤ k') :
    Fir.run P k' f vs = .ok v :=
  evalCall_mono P hok hk

/-! ## Lookups -/

/-- A lookup at key `k'` after an insertion at another key `k`. -/
theorem get?_insert_ne {α : Type} (m : Src.NatMap α) {k k' : Nat} (x : α) (hne : k ≠ k') :
    (m.insert k x).get? k' = m.get? k' :=
  Src.NatMap.get?_insert_ne m x (Ne.symm hne)

/-! ## The `Nat` primitives on literals -/

@[simp] theorem sem_natAdd (a b : Nat) :
    Lam.Prim.sem .natAdd [a, b] = some (.nat (a + b)) := rfl

@[simp] theorem sem_natSub (a b : Nat) :
    Lam.Prim.sem .natSub [a, b] = some (.nat (a - b)) := rfl

@[simp] theorem sem_natMul (a b : Nat) :
    Lam.Prim.sem .natMul [a, b] = some (.nat (a * b)) := rfl

@[simp] theorem sem_natDiv (a b : Nat) :
    Lam.Prim.sem .natDiv [a, b] = some (.nat (if b == 0 then 0 else a / b)) := rfl

@[simp] theorem sem_natMod (a b : Nat) :
    Lam.Prim.sem .natMod [a, b] = some (.nat (if b == 0 then a else a % b)) := rfl

@[simp] theorem sem_natPow (a b : Nat) :
    Lam.Prim.sem .natPow [a, b] = some (.nat (a ^ b)) := rfl

@[simp] theorem sem_natGcd (a b : Nat) :
    Lam.Prim.sem .natGcd [a, b] = some (.nat (Nat.gcd a b)) := rfl

@[simp] theorem sem_natBeq (a b : Nat) :
    Lam.Prim.sem .natBeq [a, b] = some (.bool (a == b)) := rfl

@[simp] theorem sem_natBle (a b : Nat) :
    Lam.Prim.sem .natBle [a, b] = some (.bool (decide (a ≤ b))) := rfl

@[simp] theorem sem_natBlt (a b : Nat) :
    Lam.Prim.sem .natBlt [a, b] = some (.bool (decide (a < b))) := rfl

@[simp] theorem sem_natLand (a b : Nat) :
    Lam.Prim.sem .natLand [a, b] = some (.nat (a &&& b)) := rfl

@[simp] theorem sem_natLor (a b : Nat) :
    Lam.Prim.sem .natLor [a, b] = some (.nat (a ||| b)) := rfl

@[simp] theorem sem_natXor (a b : Nat) :
    Lam.Prim.sem .natXor [a, b] = some (.nat (a ^^^ b)) := rfl

@[simp] theorem sem_natShl (a b : Nat) :
    Lam.Prim.sem .natShl [a, b] = some (.nat (a * 2 ^ b)) := rfl

@[simp] theorem sem_natShr (a b : Nat) :
    Lam.Prim.sem .natShr [a, b] = some (.nat (if a.log2 < b then 0 else a / 2 ^ b)) := rfl

@[simp] theorem sem_natPred (a : Nat) :
    Lam.Prim.sem .natPred [a] = some (.nat (a - 1)) := rfl

end IxCC.AiurBackend.FirFacts
