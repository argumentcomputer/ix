import Compilatrix.Own.Plain.Proof.State
import Compilatrix.Own.Plain.Proof.StackRetain
import Compilatrix.Own.Plain.Proof.JoinLookup

/-! Reconstruct a complete body-entry invariant after a real jump's canonical
copies/cleanup schedule. Saved captures and argument tokens are then rebound;
the first-jump/charged distinction remains in the actual paired after-stacks. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

theorem dens_preserve {H H' : Heap} {vs : List RVal} {ws : List Fir.Val}
    (h : Sem.Forall2 (Proof.Den H) vs ws)
    (hv : ∀ v, v ∈ vs → H.value? v = H'.value? v) : Sem.Forall2 (Proof.Den H') vs ws := by
  induction h with
  | nil => exact .nil
  | @cons v w vs ws hd hs ih =>
    refine .cons ?_ (ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)))
    change H'.value? v = some w
    rw [← hv v (by simp)]
    exact hd

theorem jump_state {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {owned kept vs : List RVal} {ws : List Fir.Val} {captured live : List Fir.Var} {older : Joins}
    {ef : Fir.JEntry} {eo : JEntry} {restf : List Fir.JEntry} {resto : List JEntry} {ρ : Own.Env}
    (he : EntryDen H owned captured older ef eo) (hc : CaptureView eo.env ρ captured live)
    (hs : EntryScope functions captured restf ef) (hdTail : StackDen H owned older restf resto)
    (hvTail : StackViews eo.env captured older resto) (hsTail : StackScope functions captured older restf)
    (hr : EnvRoots ρ (retained captured live) kept)
    (hb : Rc.Balance H' external (vs ++ kept))
    (hp : ∀ v, v ∈ vs ++ kept → H.value? v = H'.value? v)
    (hargs : Sem.Forall2 (Proof.Den H) vs ws) (hlen : vs.length = ef.params.length) :
    State functions H' external (captured ++ ef.params)
      (Fir.bindAll ef.env ef.params ws) (Own.bindAll eo.env eo.params vs) (kept ++ vs)
      (if ef.isRec then (ef.id, captured) :: older else older) (ef.after restf) (eo.after resto) ∧
      scopeOk functions (captured ++ ef.params) (stackArities (ef.after restf)) ef.body = true := by
  have hroots := hc.retained_roots hr
  have hpKept : ∀ v, v ∈ kept → H.value? v = H'.value? v :=
    fun v hm => hp v (List.mem_append_right _ hm)
  have hpArgs : ∀ v, v ∈ vs → H.value? v = H'.value? v :=
    fun v hm => hp v (List.mem_append_left _ hm)
  have henv := he.env.transport hroots hpKept
  have hargs' := dens_preserve hargs hpArgs
  have hentry : EntryDen H' kept captured older ef eo :=
    { he with env := henv, borrowed := ⟨kept, hroots, fun _ hm => hm⟩ }
  have htail := hdTail.retain hvTail hroots hpKept
  have hentry' := hentry.reframe (owned' := kept ++ vs) (fun _ hm => List.mem_append_left _ hm)
  have htail' := htail.reframe (owned' := kept ++ vs) (fun _ hm => List.mem_append_left _ hm)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, balance_append_comm hb, fresh_nodup_append hc.captured_nodup hs.1,
      StackDen.after hentry' htail', ?_, StackScope.after hs hsTail⟩
    · simpa only [he.params] using henv.bindAll ef.params hargs' hlen
    · simpa only [he.params] using hroots.bindAll ef.params vs hlen hs.1
    · have hf : fresh captured eo.params = true := by simpa only [he.params] using hs.1
      simpa only [he.params, he.id, he.isRec] using
        hvTail.after hc.captured_nodup hf vs
  · rw [stackArities_after]
    exact hs.2


end Compilatrix.Own.Plain
