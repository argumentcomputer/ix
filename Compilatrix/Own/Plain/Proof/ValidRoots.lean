import Compilatrix.Own.Plain.Proof.State
import Compilatrix.Own.Plain.Proof.Scope

/-! Actual evaluated live roots have full source denotations. Allocation transports these successful denotations; no claim about arbitrary None locations is needed. -/

set_option autoImplicit false
namespace Compilatrix.Own.Plain
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
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo)
    (x : Fir.Var) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (hd : Proof.Den H' v w) (hb : Balance H' external (roots ++ [v]))
    (hp : ∀ root value, Proof.Den H root value → Proof.Den H' root value) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo := by
  apply h.bind x hx hd hb
  intro root hm
  obtain ⟨value, hd⟩ := h.roots.den_member h.env hm
  exact hd.trans (hp root value hd).symm

end Compilatrix.Own.Plain
