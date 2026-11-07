import IxCC.Own.Plain.Proof.RhsSteps

/-! Constructor bind refinement. Copied fields become actual heap edges;
the caller's old roots are suspended during allocation and restored beside
the returned constructor. Fieldless constructors remain immediate. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

theorem constructor_step {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo)
    (P : Program) (k : Nat) (x : Fir.Var) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (body : Fir.Code)
    {w : Fir.Val} (hx : x ∉ live) (hs : args.all (argIn live) = true)
    (hw : Fir.evalRhs P.source ρf (.ctor ctor args) = .ok w) :
    BindProgress h P k x (.ctor ctor args) body w := by
  obtain ⟨vs, ws, ho, hf, hd⟩ := args_den h.env args hs
  by_cases harity : ws.length = ctor.arity
  · have hw' : Fir.Val.ctor ctor ws = w := by
      simpa [Fir.evalRhs, hf, harity] using hw
    subst w
    have hvlen : vs.length = ctor.arity := hd.length.trans harity
    obtain ⟨Hcopy, hcopy, hbcopy, hvalues⟩ := copies_sound ρo H args h.counts
      (argsOwned_of_scope h.env h.roots hs) ho
    have hp : ∀ root value, Proof.Den H root value → Proof.Den Hcopy root value := by
      intro root value hd
      change Hcopy.value? root = some value
      rw [← hvalues root]
      exact hd
    have hfields : Sem.Forall2 (Proof.Den Hcopy) vs ws := hd.mono hp
    by_cases hz : ctor.arity = 0
    · have hvs : vs = [] := by simpa using (hvlen.trans hz)
      have hws : ws = [] := by simpa using (harity.trans hz)
      subst vs
      subst ws
      have hb : Balance Hcopy external roots := by simpa using hbcopy
      have hresult : Proof.Den Hcopy (.ctor0 ctor) (.ctor ctor []) := Proof.den_ctor0 Hcopy ctor
      have hb' : Balance Hcopy external (roots ++ [.ctor0 ctor]) :=
        balance_append_comm (show Balance Hcopy external ([.ctor0 ctor] ++ roots) from
          balance_immediate hb (by intro l; simp))
      refine ⟨.ctor0 ctor, Hcopy, ?_, h.bind_den x hx hresult hb' hp, hp⟩
      simp only [lowerCode]
      rw [eval_actionPrefix, hcopy, Result.bind_ok]
      rw [eval_bindRhs P k ρo Jo Hcopy x (.ctor ctor args) _ (by intro f as he; cases he)]
      have hr : evalRhs P.tables ρo Hcopy (.ctor ctor args) = .ok (.ctor0 ctor, Hcopy) := by
        simp [evalRhs, Own.evalRhs, ho, Fir.CtorInfo.fieldless, hz]
      rw [hr, Result.bind_ok]
    · have hpos : 0 < ctor.arity := by omega
      have held : Balance Hcopy (holdRoots external roots) vs := balance_hold.mp hbcopy
      obtain ⟨hr, hb, hresult, hpreserve⟩ :=
        evalRhs_alloc_owned (T := P.tables) ho hvlen hpos held hfields
      let allocated := Hcopy.alloc .rc { ctor, fields := vs }
      have hp' : ∀ root value, Proof.Den H root value → Proof.Den allocated.2 root value := by
        intro root value hd
        exact hpreserve root value (hp root value hd)
      refine ⟨allocated.1, allocated.2, ?_, h.bind_den x hx hresult (balance_resume hb) hp', hp'⟩
      simp only [lowerCode]
      rw [eval_actionPrefix, hcopy, Result.bind_ok]
      rw [eval_bindRhs P k ρo Jo Hcopy x (.ctor ctor args) _ (by intro f as he; cases he)]
      rw [hr, Result.bind_ok]
  · simp [Fir.evalRhs, hf, harity] at hw


theorem nonCall_step {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo)
    (P : Program) (k : Nat) (x : Fir.Var) (rhs : Fir.Rhs) (body : Fir.Code)
    {w : Fir.Val} (hpins : BoolPinsOk P.source) (hx : x ∉ live)
    (hs : rhsIn functions live rhs = true)
    (hn : ∀ f args, rhs ≠ .call f args)
    (hw : Fir.evalRhs P.source ρf rhs = .ok w) :
    BindProgress h P k x rhs body w := by
  cases rhs with
  | arg a => exact argument_step h P k x a body hx hs hw
  | ctor ctor args =>
    have ha : args.all (argIn live) = true := by
      simp only [rhsIn, Bool.and_eq_true] at hs
      exact hs.1.1.1.2
    exact constructor_step h P k x ctor args body hx ha hw
  | proj y key i =>
    exact projection_step h P k x y key i body hx (by simpa [rhsIn] using hs) hw
  | prim op args =>
    have ha : args.all (argIn live) = true := by
      simp only [rhsIn, Bool.and_eq_true] at hs
      exact hs.2
    exact primitive_step h P k x op args body hpins hx ha hw
  | call f args => exact False.elim (hn f args rfl)


end IxCC.Own.Plain
