import Ix.CompileCert.PrimaryAddressFrame

/-! # Auxiliary writes of the actual image-block producer

These origins concern the producer snapshot. They do not identify its
addresses with a later live merge's old auxiliary addresses.
-/

namespace Ix.CompileCert.ImageAuxOrigins

open Ix (Name ConstantInfo)
open Ix.CompileM Ix.Compile.Pass
open Ix.Compile.ExactKey (ExactName nameEq)

abbrev Image := Name × BlockResult × BlockState

def ImageCall (producer : CompileEnv) (x : Image) : Prop :=
  ∃ known ci, compileImage producer known ci = .ok (x.2.1, x.2.2)

/-- Every output retains its SAME successful call through all real rounds.
An unsuccessful attempt does not supply an output origin. -/
theorem compileImageBlock_calls {producer : CompileEnv} {all : Ix.Set Name}
    {imgs : Array Image} {pub : Published} (run : compileImageBlock producer all = .ok (imgs, pub)) :
    ∀ x ∈ imgs, ImageCall producer x := by
  unfold compileImageBlock at run
  dsimp only at run
  obtain ⟨_, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨_, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨_, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨out, rounds, run⟩ := Loop.except_bind_ok.mp run
  have origins : ∀ x ∈ out.2.2.1, ImageCall producer x := by
    refine Ix.Cert.Claims.forIn_range_inv (fun s : Array (Name × ConstantInfo) ×
      Std.HashMap ExactName Address × Array Image × String =>
        ∀ x ∈ s.2.2.1, ImageCall producer x) _ _ ?_ (fun _ absent => by simp at absent) rounds
    intro _ s r held ran
    split at ran
    · cases ran; exact held
    · obtain ⟨next, walked, ran⟩ := Loop.except_bind_ok.mp ran
      cases ran
      refine Ix.Cert.Claims.forIn_array_inv (fun t : Std.HashMap ExactName Address ×
        Array Image × String × Array (Name × ConstantInfo) =>
          ∀ x ∈ t.2.1, ImageCall producer x) _ _ ?_ held walked
      intro x _ u q prior step
      split at step
      · rename_i r bs actual
        cases step
        intro y member
        rcases Array.mem_push.mp member with old | rfl
        · exact prior y old
        · exact ⟨u.1, x.2, actual⟩
      · cases step; exact prior
  split at run
  · obtain ⟨_, failed, _⟩ := Loop.except_bind_ok.mp run; cases failed
  · cases run; exact origins

structure Writes (pre : List Image) (lo : ExactName) (s : BlockState × Option BlockResult) : Prop where
  addresses : s.1.auxNameToAddr = pre.foldl (fun m x => m.insert x.1 x.2.1.blockAddr) {}
  extra : s.1.auxGenExtraNames = {}
  named : ∀ x ∈ pre, ∃ nd, (x.1, nd) ∈ s.1.auxNamed ∧ nd.addr = x.2.1.blockAddr
  selected : s.2.map BlockResult.blockAddr = s.1.auxNameToAddr.get? lo

private theorem selected_insert (lo key : ExactName) (table : Std.HashMap ExactName Address)
    (selected : Option BlockResult) (r : BlockResult)
    (held : selected.map BlockResult.blockAddr = table.get? lo) :
    (if nameEq key lo then some r else selected).map BlockResult.blockAddr =
      (table.insert key r.blockAddr).get? lo := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  change (if nameEq key lo then some r else selected).map BlockResult.blockAddr =
    if nameEq key lo then some r.blockAddr else table.get? lo
  split <;> simp_all

/-- A trace of the ACTUAL output loop, before lookup-origin assembly. -/
theorem runImageBlock_trace
    {original : CompileEnv → Name → Ix.Set Name → Except CompileError (BlockResult × BlockState)}
    {producer : CompileEnv} {all : Ix.Set Name} {lo : Name} {result : BlockResult}
    {cache : BlockState} {pub : Published}
    (run : runImageBlock original producer all lo = .ok (result, cache, pub)) :
    ∃ imgs pub0 origRes origCache,
      compileImageBlock producer all = .ok (imgs, pub0) ∧
      original producer lo all = .ok (origRes, origCache) ∧
      Writes imgs.toList lo (cache, some result) := by
  unfold runImageBlock at run
  dsimp only at run
  obtain ⟨⟨imgs, pub0⟩, images, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨⟨origRes, origCache⟩, originalRun, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨out, loop, run⟩ := Loop.except_bind_ok.mp run
  have traced : Writes imgs.toList lo out := by
    refine Loop.forIn_inv_array (fun pre s => Writes pre lo s) _ imgs ?_ ?_ loop
    · intro pre x post s r _ held ran
      obtain ⟨n, r0, bs⟩ := x
      have selected := selected_insert lo n s.1.auxNameToAddr s.2 r0 held.selected
      split at ran
      all_goals
        rename_i chosen
        cases ran
        refine ⟨_, rfl, ?_⟩
        constructor
        · simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
            congrArg (fun m : Std.HashMap ExactName Address => m.insert n r0.blockAddr) held.addresses
        · exact held.extra
        · intro x member
          rcases List.mem_append.mp member with old | added
          · obtain ⟨nd, present, addr⟩ := held.named x old
            exact ⟨nd, Array.mem_push.mpr (.inl present), addr⟩
          · cases List.mem_singleton.mp added
            exact ⟨_, Array.mem_push.mpr (.inr rfl), rfl⟩
        · simpa only [chosen, Bool.false_eq_true, ↓reduceIte] using selected
    · exact ⟨rfl, rfl, (by intro _ absent; cases absent),
        (Std.HashMap.getElem?_empty (a := (show ExactName from lo))).symm⟩
  split at run
  · rename_i r selected
    cases run
    exact ⟨imgs, pub0, origRes, origCache, Ix.Cert.Claims.mapError_ok images, originalRun,
      by rw [← selected]; exact traced⟩
  · cases run

end Ix.CompileCert.ImageAuxOrigins
