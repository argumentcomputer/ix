import IxCC.Own.Plain.Proof.Selected
import IxCC.Own.Plain.Proof.JumpState
import IxCC.Own.Plain.Proof.Transfers
import IxCC.Own.Plain.Proof.Scope
import IxCC.Own.Plain.Proof.ResultCompose
import IxCC.Fir.Proof.Unfold

/-! A canonical jump's concrete copies/cleanup schedule reconstructs the
selected captured environment and charged stack. The code induction uses
this operational progress fact without assuming any body simulation. -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc
open IxCC.Sem (Result)

theorem jump_progress {F : Fir.Program} {k : Nat} {H : Heap} {external : Nat → Nat}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (state : State (signatures F) H external live ρf ρo owned joins Jf Jo)
    {j : Fir.JoinId} {args : List Fir.Arg} {ef : Fir.JEntry} {restf : List Fir.JEntry}
    (lookup : Fir.lookupJ j Jf = some (ef, restf))
    (scope : args.all (argIn live) = true) {ws : List Fir.Val}
    (values : Fir.evalArgs ρf args = some ws) (arity : ws.length = ef.params.length) :
    ∃ captured older eo resto H' kept vs,
      eo.params = ef.params ∧ eo.charged = ef.charged ∧
      eo.body = lowerCode (captured ++ ef.params)
        (if ef.isRec then (ef.id, captured) :: older else older) ef.body ∧
      State (signatures F) H' external (captured ++ ef.params)
        (Fir.bindAll ef.env ef.params ws) (Own.bindAll eo.env eo.params vs) (kept ++ vs)
        (if ef.isRec then (ef.id, captured) :: older else older) (ef.after restf) (eo.after resto) ∧
      scopeOk (signatures F) (captured ++ ef.params) (stackArities (ef.after restf)) ef.body = true ∧
      vs.length = eo.params.length ∧
      Fir.eval F k ρf Jf (.jmp j args) = Fir.jumpTo F k ef restf ws ∧
      eval (Program.canonical F) k ρo Jo H (lowerCode live joins (.jmp j args)) =
        jumpTo (Program.canonical F) k eo resto vs H' ∧ ExternalPreserved H H' external := by
  obtain ⟨captured, older, eo, resto, hlo, hm, he, hc, hs, hd, hv, ht⟩ :=
    lookup_ready state.stack state.views state.scope lookup
  obtain ⟨vs, ws', hvo, hwf, hdargs⟩ := args_den state.env args scope
  have hws : ws' = ws := Option.some.inj (hwf.symm.trans values)
  subst ws'
  have hlen : vs.length = ef.params.length := hdargs.length.trans arity
  obtain ⟨H', kept, hrun, hr, hb, _, hp, hext⟩ :=
    transfer_sound (Program.canonical F) k ρo Jo H live captured args (.jmp j args)
      state.roots state.counts (argsOwned_of_scope state.env state.roots scope) hvo
  obtain ⟨hstate, hscope⟩ := jump_state he hc hs hd hv ht hr hb hp hdargs hlen
  refine ⟨captured, older, eo, resto, H', kept, vs, he.params, he.charged,
    he.body, hstate, hscope, ?_, ?_, ?_, ExternalPreserved.of_values hext⟩
  · simpa only [← he.params] using hlen
  · exact Fir.eval_jmp_of F k ρf Jf lookup values
  · rw [lowerCode, hm]
    simp only [Option.getD_some]
    rw [hrun, eval_jmp, hlo, hvo]
    rfl

end IxCC.Own.Plain
