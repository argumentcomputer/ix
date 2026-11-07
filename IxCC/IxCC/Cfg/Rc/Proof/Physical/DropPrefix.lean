import IxCC.Cfg.Rc.Proof.Physical.DropStep
import IxCC.Cfg.Rc.Proof.Physical.DropTokens

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Traverse the canonical cleanup of lexical variables. Captured roots are
held while later markers run, and restored with their original bindings.
Reclaimed slots and free lists come from actual decrement traces; aliases in
carried arguments are preserved even when the same value loses a local root. -/
theorem drop_prefix
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    (captured live : List Fir.Var) {first : Nat} {tail : List Cfg.Instr}
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (head : source.rest = encodePrefix P.base.size first (Own.Plain.drops captured live) ++ tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (absent : ∀ dummy, first ≤ dummy → ρo.get? dummy = none)
    (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ kept H' mem' slots' lists' final cost,
      Own.Plain.evalActions ρo H (Own.Plain.drops captured live) = .ok H' ∧
      Tokens H' external held (Own.Plain.retained captured live) ρf ρo kept ∧
      AllocatorReady H' addresses mem' (holdRoots external (kept ++ held))
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} cost
        {mem := mem', ctx := context, stack := final :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail} final ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo final.env ∧
      final.dsts = [] ∧ (∀ root ∈ held, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  induction live generalizing first source target H held roots mem slots lists with
  | nil =>
    have empty : roots = [] := by simpa [Own.Plain.EnvRoots, Own.evalArgs] using before.exactRoots.symm
    subst roots
    have same : {source with rest := tail} = source := by
      have rest : source.rest = tail := by simpa [Own.Plain.drops, encodePrefix] using head
      cases source
      simp_all
    exact .inl ⟨[], H, mem, slots, lists, target, 0, rfl, before, ready, .refl _,
      by rw [same]; exact cursor, registers, running, fun _ _ => rfl⟩
  | cons x live ih =>
    cases retain : captured.contains x with
    | true =>
      have retainProp : x ∈ captured := by simpa using retain
      obtain ⟨value, remaining, lookup, equal, heldTokens⟩ := Tokens.hold_head before
      have rebase : holdRoots external (roots ++ held) =
          holdRoots external (remaining ++ value :: held) := by
        funext location
        rw [equal]
        simp only [holdRoots, refsIn_append, refsIn]
        omega
      have nextReady := ready
      rw [rebase] at nextReady
      have nextHead : source.rest = encodePrefix P.base.size first
          (Own.Plain.drops captured live) ++ tail := by simpa [Own.Plain.drops, retainProp] using head
      rcases ih cursor nextHead sourceLookup heldTokens nextReady registers absent running with success | failure
      · obtain ⟨kept, H', mem', slots', lists', final, cost, actions, tokens, restored,
          trace, next, words, finished, values⟩ := success
        obtain ⟨actual, logical, ownLookup, sourceValue, den⟩ := before.den x (by simp)
        have sameValue : actual = value := Option.some.inj (ownLookup.symm.trans lookup)
        subst actual
        have den' : Own.Proof.Den H' value logical := by
          change H'.value? value = some logical
          rw [← values value (by simp)]
          exact den
        have fresh : x ∉ Own.Plain.retained captured live := by
          intro member
          exact (List.nodup_cons.mp before.distinct).1 (List.mem_filter.mp member).1
        have finalTokens := Tokens.restore_head tokens lookup sourceValue den' fresh
        have output : holdRoots external (kept ++ value :: held) =
            holdRoots external ((value :: kept) ++ held) := by
          funext location
          simp only [holdRoots, refsIn_append, refsIn, List.cons_append]
          omega
        rw [output] at restored
        refine .inl ⟨value :: kept, H', mem', slots', lists', final, cost, ?_, ?_, restored,
          trace, next, words, finished, fun root member => values root (by simp [member])⟩
        · simpa [Own.Plain.drops, retainProp] using actions
        · simpa only [Own.Plain.retained, List.filter_cons, retain, ↓reduceIte] using finalTokens
      · exact .inr failure
    | false =>
      have retainProp : x ∉ captured := by simpa using retain
      have markerHead : source.rest = marker P.base.size first (.dec x) ::
          (encodePrefix P.base.size (first+1) (Own.Plain.drops captured live) ++ tail) := by
        simpa [Own.Plain.drops, retainProp, encodePrefix] using head
      rcases drop_marker_step functions main cursor markerHead sourceLookup before ready
          registers (absent first (by omega)) running callers with success | failure
      · obtain ⟨value, remaining, H₁, mem₁, slots₁, lists₁, charges, lookup, equal,
          action, tokens, ready₁, trace₁, next, words, values₁⟩ := success
        rcases ih next rfl sourceLookup tokens ready₁ words
            (fun dummy h => absent dummy (by omega)) rfl with success | failure
        · obtain ⟨kept, H₂, mem₂, slots₂, lists₂, final, cost, actions, tokens₂, ready₂,
            trace₂, cursor₂, words₂, running₂, values₂⟩ := success
          refine .inl ⟨kept, H₂, mem₂, slots₂, lists₂, final, 2+charges+cost, ?_, ?_, ready₂,
            trace₁.trans trace₂, cursor₂, words₂, running₂,
            fun root member => (values₁ root member).trans (values₂ root member)⟩
          · simp [Own.Plain.drops, retainProp, Own.Plain.evalActions, action, actions, Sem.Result.bind]
          · simpa only [Own.Plain.retained, List.filter_cons, retain, Bool.false_eq_true, if_false] using tokens₂
        · obtain ⟨cost, terminal, resource, trace₂, failed⟩ := failure
          exact .inr ⟨2+charges+cost, terminal, resource, trace₁.trans trace₂, failed⟩
      · exact .inr failure


end IxCC.Cfg.Rc.Native
