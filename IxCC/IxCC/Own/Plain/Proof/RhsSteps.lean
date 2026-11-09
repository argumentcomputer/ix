import IxCC.Own.Plain.Proof.ValidRoots
import IxCC.Own.Plain.Proof.Frames
import IxCC.Own.Plain.Proof.TailCall
import IxCC.Own.Plain.Proof.Projection
import IxCC.Own.Plain.Proof.Scalars

/-! Successful non-call bind steps for the canonical producer. Old successful
full denotations are preserved through copying and allocation. This supplies
actual successor states for the code induction, not a simulated execution
among the premises. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)


def BindProgress {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (_h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (P : Program) (k : Nat) (x : Fir.Var) (r : Fir.Rhs) (body : Fir.Code) (w : Fir.Val) : Prop :=
  ∃ v H',
    eval P k ρo Jo H (lowerCode live joins (.bind x r body) imm) =
      eval P k (ρo.insert x v) Jo H' (lowerCode (live ++ [x]) joins body (nextImm imm x r)) ∧
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo (nextImm imm x r) ∧
    ∀ root value, Proof.Den H root value → Proof.Den H' root value

theorem argument_step {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (P : Program) (k : Nat) (x : Fir.Var) (a : Fir.Arg) (body : Fir.Code)
    {w : Fir.Val} (hx : x ∉ live) (hs : argIn live a = true)
    (hw : Fir.evalRhs P.source ρf (.arg a) = .ok w) :
    BindProgress h P k x (.arg a) body w := by
  obtain ⟨v, value, ho, hf, hd⟩ := arg_den h.env hs
  have he : value = w := by simpa [Fir.evalRhs, hf, Result.ofOption] using hw
  subst w
  have has : [a].all (argIn live) = true := by simpa using hs
  obtain ⟨H', hcopy, hb, hv⟩ := copies_heapArgs_sound ρo H [a] (values := [v]) h.immOk h.counts
    (argsOwned_of_scope h.env h.roots has) (by simp [Own.evalArgs, ho])
  have hden : ∀ root value, Proof.Den H root value → Proof.Den H' root value := by
    intro root value hd
    change H'.value? root = some value
    rw [← hv root]
    exact hd
  have himm_rhs : isImmRhs imm (.arg a) = true → ImmVal v :=
    fun hr => immVal_of_isImmArg h.immOk hr ho
  refine ⟨v, H', ?_, h.bind_den_rhs x (.arg a) hx himm_rhs (hden v value hd) (balance_append_comm hb) hden, hden⟩
  simp only [lowerCode]
  rw [eval_actionPrefix, hcopy, Result.bind_ok]
  rw [eval_bindRhs P k ρo Jo H' x (.arg a) _ (by intro f args he; cases he)]
  have hr : evalRhs P.tables ρo H' (.arg a) = .ok (v, H') := by
    simp [evalRhs, Own.evalRhs, ho]
  rw [hr, Result.bind_ok]

theorem primitive_step {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (P : Program) (k : Nat) (x : Fir.Var) (op : Lam.Prim) (args : List Fir.Arg) (body : Fir.Code)
    {w : Fir.Val} (hpins : BoolPinsOk P.source) (hx : x ∉ live)
    (hs : args.all (argIn live) = true)
    (hw : Fir.evalRhs P.source ρf (.prim op args) = .ok w) :
    BindProgress h P k x (.prim op args) body w := by
  obtain ⟨vs, ws, ho, hf, hd⟩ := args_den h.env args hs
  have hprim : Fir.primResult P.source op ws = .ok w := by
    simpa [Fir.evalRhs, hf] using hw
  obtain ⟨v, hrun, hden, hb, himm_v⟩ := primitive_owned P k ρo Jo H x op args
    (lowerCode (live ++ [x]) joins body (nextImm imm x (.prim op args))) hpins h.counts ho hd hprim
  have hb' : Balance H external (roots ++ [v]) :=
    balance_append_comm (show Balance H external ([v] ++ roots) from hb)
  have hargs_imm : ImmEnv ρo (argVars args) :=
    immEnv_argVars ho (primResult_args_immediate hd hprim)
  exact ⟨v, H, hrun, h.bind_den_prim x op args hx hs hargs_imm himm_v hden hb' (fun _ _ hd => hd),
    fun _ _ hd => hd⟩

theorem projection_step {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (P : Program) (k : Nat) (x y : Fir.Var) (key : Key.CtorKey) (i : Nat) (body : Fir.Code)
    {w : Fir.Val} (hx : x ∉ live) (hy : y ∈ live)
    (hw : Fir.evalRhs P.source ρf (.proj y key i) = .ok w) :
    BindProgress h P k x (.proj y key i) body w := by
  obtain ⟨parent, source, ho, hf, hd⟩ := h.env y hy
  simp only [Fir.evalRhs, hf] at hw
  cases hc : source.asCtor P.source.known with
  | none => simp [hc] at hw
  | some pair =>
    obtain ⟨key', fields⟩ := pair
    by_cases hk : key' = key
    · subst key'
      have hindex : fields[i]? = some w := by
        cases hi : fields[i]? with
        | none => simp [hc, hi, Result.ofOption] at hw
        | some value =>
          have he : value = w := by simpa [hc, hi, Result.ofOption] using hw
          simpa [he] using hi
      by_cases hy_imm : imm.contains y = true
      · obtain ⟨parent', ho', hp_imm⟩ := h.immOk y (List.contains_iff_mem.mp hy_imm)
        have hpeq : parent' = parent := Option.some.inj (ho'.symm.trans ho)
        subst parent'
        obtain ⟨v, hrun, hb, hden, himm_v⟩ := projection_imm_owned P k ρo Jo H x y key i
          (lowerCode (live ++ [x]) joins body (nextImm imm x (.proj y key i))) h.counts ho hp_imm hd hc hindex
        have hb' : Balance H external (roots ++ [v]) :=
          balance_append_comm (show Balance H external ([v] ++ roots) from hb)
        have hrun' : eval P k ρo Jo H (lowerCode live joins (.bind x (.proj y key i) body) imm) =
            eval P k (ρo.insert x v) Jo H (lowerCode (live ++ [x]) joins body (nextImm imm x (.proj y key i))) := by
          dsimp only [lowerCode]
          rw [if_pos hy_imm]
          exact hrun
        exact ⟨v, H, hrun', h.bind_den_rhs x (.proj y key i) hx (fun _ => himm_v) hden hb' (fun _ _ hd => hd),
          fun _ _ hd => hd⟩
      · obtain ⟨v, H', hrun, hb, hden, hv, _⟩ := projection_owned P k ρo Jo H x y key i
          (lowerCode (live ++ [x]) joins body (nextImm imm x (.proj y key i))) h.counts ho hd hc hindex
        have hp : ∀ root value, Proof.Den H root value → Proof.Den H' root value := by
          intro root value hd
          change H'.value? root = some value
          rw [← hv root]
          exact hd
        have hb' : Balance H' external (roots ++ [v]) :=
          balance_append_comm (show Balance H' external ([v] ++ roots) from hb)
        have hrun' : eval P k ρo Jo H (lowerCode live joins (.bind x (.proj y key i) body) imm) =
            eval P k (ρo.insert x v) Jo H' (lowerCode (live ++ [x]) joins body (nextImm imm x (.proj y key i))) := by
          dsimp only [lowerCode]
          rw [if_neg hy_imm]
          exact hrun
        exact ⟨v, H', hrun', h.bind_den_rhs x (.proj y key i) hx
          (fun hr => False.elim (hy_imm hr)) hden hb' hp, hp⟩
    · simp [hc, hk] at hw


end IxCC.Own.Plain
