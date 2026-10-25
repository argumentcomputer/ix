import Ix.CompileCert.PrimaryAddressFrame
import Ix.CompileCert.Canon.QSort

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

/-- A final exact-key hit comes from an actual ordered write, including
when later writes overwrite earlier ones. -/
theorem fold_hit_origin (imgs : List Image) {n : ExactName} {addr : Address}
    (hit : (imgs.foldl (fun m x => m.insert x.1 x.2.1.blockAddr)
      ({} : Std.HashMap ExactName Address)).get? n = some addr) :
    ∃ x ∈ imgs, x.1 = n ∧ x.2.1.blockAddr = addr := by
  have origins : ∀ (key : ExactName) value,
      (imgs.foldl (fun m x => m.insert x.1 x.2.1.blockAddr)
        ({} : Std.HashMap ExactName Address)).get? key = some value →
      ∃ x ∈ imgs, x.1 = key ∧ x.2.1.blockAddr = value := by
    apply List.foldlRecOn (motive := fun table : Std.HashMap ExactName Address =>
      ∀ (key : ExactName) value, table.get? key = some value →
        ∃ x ∈ imgs, x.1 = key ∧ x.2.1.blockAddr = value)
    · intro key value absent
      have impossible := (Std.HashMap.getElem?_empty (a := key)).symm.trans absent
      cases impossible
    · intro table prior x member key value found
      change (table.insert (show ExactName from x.1) x.2.1.blockAddr).get? key = some value at found
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at found
      split at found
      · rename_i same
        have equal : (show ExactName from x.1) = key := eq_of_beq same
        cases found
        exact ⟨x, member, equal, rfl⟩
      · exact prior key value found
  exact origins n addr hit

/-- One actual image/original run supplies every final hit's matching image,
Named row and result-producing compile call. No source fidelity or equality
to an address in a later LIVE state follows from these origins. -/
theorem runImageBlock_aux_origins
    {original : CompileEnv → Name → Ix.Set Name → Except CompileError (BlockResult × BlockState)}
    {producer : CompileEnv} {all : Ix.Set Name} {lo : Name} {result : BlockResult}
    {cache : BlockState} {pub : Published}
    (run : runImageBlock original producer all lo = .ok (result, cache, pub)) :
    ∃ imgs pub0 origRes origCache,
      compileImageBlock producer all = .ok (imgs, pub0) ∧
      original producer lo all = .ok (origRes, origCache) ∧
      cache.auxGenExtraNames = {} ∧
      cache.auxNameToAddr = imgs.foldl (fun m (n, r, _) => m.insert n r.blockAddr) {} ∧
      result.projections = #[] ∧ primaryClaims lo result = #[(lo, result.blockAddr)] ∧
      cache.auxNameToAddr.get? lo = some result.blockAddr ∧
      (∀ x ∈ imgs, ImageCall producer x) ∧
      ∀ (n : Name) addr, cache.auxNameToAddr.get? n = some addr →
        ∃ r bs named known ci,
          (n, r, bs) ∈ imgs ∧ r.blockAddr = addr ∧ r.projections = #[] ∧
          (n, named) ∈ cache.auxNamed ∧ named.addr = addr ∧
          compileImage producer known ci = .ok (r, bs) := by
  obtain ⟨imgs, pub0, origRes, origCache, images, originalRun, traced⟩ := runImageBlock_trace run
  have lone := Ix.Cert.Claims.runImageBlock_lone run
  have calls := compileImageBlock_calls images
  refine ⟨imgs, pub0, origRes, origCache, images, originalRun, traced.extra, ?_, lone,
    by simp only [primaryClaims, lone, Array.isEmpty_empty, ↓reduceIte], traced.selected.symm, calls, ?_⟩
  · simpa only [Array.foldl_toList] using traced.addresses
  · intro n addr hit
    rw [traced.addresses] at hit
    obtain ⟨⟨name, r, bs⟩, member, same, address⟩ := fold_hit_origin imgs.toList hit
    dsimp only at same address
    subst name
    have actualMember := Array.mem_toList_iff.mp member
    obtain ⟨named, present, namedAddr⟩ := traced.named (n, r, bs) member
    obtain ⟨known, ci, compiled⟩ := calls (n, r, bs) actualMember
    exact ⟨r, bs, named, known, ci, actualMember, address,
      Ix.Cert.Claims.compileImageBlock_lone images (n, r, bs) actualMember,
      present, namedAddr.trans address, compiled⟩

/-- The real declaration/round loops retain structural request membership,
including memo hits, failed attempts, rest lists and the early-break branch. -/
theorem compileImageBlock_keys {producer : CompileEnv} {request : Ix.Set Name}
    {imgs : Array Image} {pub : Published}
    (run : compileImageBlock producer request = .ok (imgs, pub)) :
    ∀ x ∈ imgs, x.1 ∈ request.toArray.toList := by
  unfold compileImageBlock at run
  dsimp only at run
  obtain ⟨_, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨_, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨declared, declarations, run⟩ := Loop.except_bind_ok.mp run
  have declaredKeys : ∀ p ∈ declared.2.1, p.1 ∈ request.toArray.toList := by
    refine Ix.Cert.Claims.forIn_array_inv (fun s : RwState × Array (Name × ConstantInfo) ×
      Array (Name × Expansion × Ix.Expr) => ∀ p ∈ s.2.1, p.1 ∈ request.toArray.toList)
      _ _ ?_ (fun _ absent => by simp at absent) declarations
    intro a member s r held stepped
    have original := Array.mem_toList_iff.mpr (Canon.mem_qsort.mp member)
    repeat' first
      | obtain ⟨_, _, stepped⟩ := Loop.except_bind_ok.mp stepped
      | split at stepped
    all_goals first
      | (cases stepped; done)
      | (cases stepped; exact held)
      | (cases stepped
         intro p present
         rcases Array.mem_push.mp present with old | rfl
         exacts [held p old, original])
  obtain ⟨out, rounds, run⟩ := Loop.except_bind_ok.mp run
  have bounded : (∀ p ∈ out.1, p.1 ∈ request.toArray.toList) ∧
      ∀ x ∈ out.2.2.1, x.1 ∈ request.toArray.toList := by
    refine Ix.Cert.Claims.forIn_range_inv (fun s : Array (Name × ConstantInfo) ×
      Std.HashMap ExactName Address × Array Image × String =>
        (∀ p ∈ s.1, p.1 ∈ request.toArray.toList) ∧
        ∀ x ∈ s.2.2.1, x.1 ∈ request.toArray.toList) _ _ ?_
      ⟨declaredKeys, fun _ absent => by simp at absent⟩ rounds
    intro _ s r held stepped
    split at stepped
    · cases stepped; exact held
    · obtain ⟨next, walked, stepped⟩ := Loop.except_bind_ok.mp stepped
      cases stepped
      refine Ix.Cert.Claims.forIn_array_inv (fun t : Std.HashMap ExactName Address ×
        Array Image × String × Array (Name × ConstantInfo) =>
          (∀ x ∈ t.2.1, x.1 ∈ request.toArray.toList) ∧
          ∀ p ∈ t.2.2.2, p.1 ∈ request.toArray.toList) _ _ ?_
        ⟨held.2, fun _ absent => by simp at absent⟩ walked |>.symm
      intro x member u q prior step
      split at step
      · cases step
        refine ⟨fun y present => ?_, prior.2⟩
        rcases Array.mem_push.mp present with old | rfl
        exacts [prior.1 y old, held.1 x member]
      · cases step
        refine ⟨prior.1, fun y present => ?_⟩
        rcases Array.mem_push.mp present with old | rfl
        exacts [prior.2 y old, held.1 x member]
  split at run
  · obtain ⟨_, failed, _⟩ := Loop.except_bind_ok.mp run; cases failed
  · cases run; exact bounded.2

end Ix.CompileCert.ImageAuxOrigins
