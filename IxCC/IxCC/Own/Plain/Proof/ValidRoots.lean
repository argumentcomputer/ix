import IxCC.Own.Plain.Proof.State
import IxCC.Own.Plain.Proof.Scope

/-! Actual evaluated live roots have full source denotations. Allocation transports these successful denotations; no claim about arbitrary None locations is needed. -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc

theorem den_member {H : Heap} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) {v : RVal} (hm : v ∈ vs) :
    ∃ w, Proof.Den H v w := by
  induction hd with
  | nil => simp at hm
  | cons hv hvs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, hv⟩
    · exact ih hm

theorem EnvRoots.den_member {H : Heap} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    (hr : EnvRoots ρo live roots) (he : EnvDen H live ρf ρo)
    {v : RVal} (hm : v ∈ roots) : ∃ w, Proof.Den H v w := by
  have hs : (live.map Fir.Arg.var).all (argIn live) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    simpa [argIn] using hx
  obtain ⟨vs, ws, ho, _, hd⟩ := args_den he _ hs
  have hev : vs = roots := Option.some.inj (ho.symm.trans hr)
  subst vs
  exact Plain.den_member hd hm

theorem State.bind_den {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (x : Fir.Var) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (hd : Proof.Den H' v w) (hb : Balance H' external (roots ++ [v]))
    (hp : ∀ root value, Proof.Den H root value → Proof.Den H' root value) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo imm := by
  apply h.bind x hx hd hb
  intro root hm
  obtain ⟨value, hd⟩ := h.roots.den_member h.env hm
  exact hd.trans (hp root value hd).symm

theorem State.bind_den_rhs {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (x : Fir.Var) (r : Fir.Rhs) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (himm : isImmRhs imm r = true → ImmVal v)
    (hd : Proof.Den H' v w) (hb : Balance H' external (roots ++ [v]))
    (hp : ∀ root value, Proof.Den H root value → Proof.Den H' root value)
    (hnotPrim : ∀ op args, r ≠ .prim op args := by intro op args h; cases h) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo (nextImm imm x r) := by
  apply h.bind_rhs x r hx himm hd hb _ hnotPrim
  intro root hm
  obtain ⟨value, hd⟩ := h.roots.den_member h.env hm
  exact hd.trans (hp root value hd).symm

theorem State.bind_den_prim {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (x : Fir.Var) (op : Lam.Prim) (args : List Fir.Arg) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (hs : args.all (argIn live) = true)
    (hargs : ImmEnv ρo (argVars args))
    (himm : ImmVal v)
    (hd : Proof.Den H' v w) (hb : Balance H' external (roots ++ [v]))
    (hp : ∀ root value, Proof.Den H root value → Proof.Den H' root value) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo (nextImm imm x (.prim op args)) := by
  apply h.bind_prim x op args hx hs hargs himm hd hb
  intro root hm
  obtain ⟨value, hd⟩ := h.roots.den_member h.env hm
  exact hd.trans (hp root value hd).symm

end IxCC.Own.Plain
