import Compilatrix.Own.Plain.Proof.ValidRoots
import Compilatrix.Own.Plain.Proof.Results

/-! Call suspension and resumption use actual root counts. Caller tokens are
held externally while a callee owns copied arguments, then restored beside
the returned token; no caller map entries are assumed safe across mutation. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc

theorem balance_resume {H : Heap} {external : Nat → Nat} {held active : List RVal}
    (h : Balance H (holdRoots external held) active) : Balance H external (held ++ active) :=
  balance_append_comm (balance_hold.mpr h)

theorem State.resume {functions : Signatures} {H Hcall H' : Heap} {external : Nat → Nat}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo)
    (x : Fir.Var) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (hcopy : ∀ root, H.value? root = Hcall.value? root)
    (hd : Proof.Den H' v w) (hb : Balance H' (holdRoots external roots) [v])
    (hreturn : ExternalPreserved Hcall H' (holdRoots external roots)) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo ∧
      ExternalPreserved H H' external := by
  refine ⟨h.bind x hx hd (balance_resume hb) ?_, ?_⟩
  · intro root hm
    obtain ⟨value, hold⟩ := h.roots.den_member h.env hm
    have hcall : Proof.Den Hcall root value := by
      change Hcall.value? root = some value
      rw [← hcopy root]
      exact hold
    exact hold.trans (hreturn root value (held_external hm) hcall).symm
  · intro root value hr hd
    apply hreturn root value (external_hold hr)
    change Hcall.value? root = some value
    rw [← hcopy root]
    exact hd


end Compilatrix.Own.Plain
