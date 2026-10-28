import Ix.Cert.Resolution
import Ix.CompileCert.Loop

/-! # The actual checked merge's primary-address writes

The real ordered claim walk covers duplicate writes and its local shadow
of old primary hits. The merge projection identifies exactly those writes;
no frame is asserted for unrelated cache or publication fields.
-/

namespace Ix.CompileCert.PrimaryAddressFrame

open Ix (Name)
open Ix.CompileM
open Ix.Compile.ExactKey (ExactName)

def PrimaryAgrees (before : CompileEnv) (writes : Array (Name × Address)) : Prop :=
  ∀ (n : Name) addr, (n, addr) ∈ writes → ∀ old,
    before.nameToAddr.get? n = some old → addr = old

def WalkOk (before : CompileEnv) (done : List (Name × Address))
    (checked : Std.HashMap ExactName Address) : Prop :=
  (∀ (n : Name) addr, (n, addr) ∈ done → checked.get? n = some addr) ∧
  ∀ (n : ExactName) addr, checked.get? n = some addr → ∀ old,
    before.nameToAddr.get? n = some old → addr = old

private theorem insert_keeps {table : Std.HashMap ExactName Address} {key q : ExactName} {addr old : Address}
    (agrees : ∀ a, table.get? key = some a → a = addr) (hit : table.get? q = some old) :
    (table.insert key addr).get? q = some old := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  split
  · rename_i same
    have equal : key = q := eq_of_beq same
    subst q
    exact congrArg some (agrees old hit).symm
  · exact hit

theorem WalkOk.insert {before done checked} (held : WalkOk before done checked)
    {key : ExactName} {addr : Address}
    (localAgree : ∀ a, checked.get? key = some a → a = addr)
    (oldAgree : ∀ a, before.nameToAddr.get? key = some a → a = addr) :
    WalkOk before (done ++ [(show Name × Address from (key, addr))]) (checked.insert key addr) := by
  constructor
  · intro n a member
    rcases List.mem_append.mp member with prior | added
    · exact insert_keeps localAgree (held.1 n a prior)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp added)
      exact Std.HashMap.getElem?_insert_self
  · intro n a hit old prior
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hit
    split at hit
    · rename_i same
      have equal : key = n := eq_of_beq same
      subst n
      cases hit
      exact (oldAgree old prior).symm
    · exact held.2 n a hit old prior

/-- The actual first loop checks EVERY ordered write, including repeated
keys whose earlier local entry shadows the old primary lookup. -/
theorem checkBlockClaims_primary_agrees {before : CompileEnv} {writes : Array (Name × Address)}
    {cache : BlockState} (run : checkBlockClaims before writes cache = .ok ()) :
    PrimaryAgrees before writes := by
  unfold checkBlockClaims at run
  obtain ⟨checked, walk, tail⟩ := Loop.except_bind_ok.mp run
  clear run tail
  have valid : WalkOk before writes.toList checked := by
    refine Loop.forIn_inv_array (fun pre table => WalkOk before pre table) _ writes ?_ ?_ walk
    · intro pre pair post table step _ held ran
      obtain ⟨key, addr⟩ := pair
      dsimp only at ran
      have agree : ∀ old, ((table.get? key).orElse fun _ => before.nameToAddr.get? key) = some old → old = addr := by
        intro old found
        by_contra different
        have bad : (old != addr) = true := by simp [different]
        cases auxiliary : before.auxNameToAddr.get? key with
        | none =>
          simp only [auxiliary, found, bad, ↓reduceIte, bind, Except.bind,
            throw, throwThe, MonadExceptOf.throw] at ran
          cases ran
        | some a =>
          by_cases denied : (a != addr) = true
          · simp only [auxiliary, denied, ↓reduceIte, bind, Except.bind,
              throw, throwThe, MonadExceptOf.throw] at ran
            cases ran
          · simp only [auxiliary, denied, found, bad, ↓reduceIte, bind, Except.bind,
              throw, throwThe, MonadExceptOf.throw] at ran
            cases ran
      have returned : step = .yield (table.insert key addr) := by
        repeat' first
          | split at ran
          | simp only [pure, Except.pure, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at ran
        all_goals cases ran <;> rfl
      cases returned
      have localAgree : ∀ a, table.get? key = some a → a = addr := by
        intro a found
        apply agree a
        simp only [found, Option.orElse_some]
      have oldAgree : ∀ a, before.nameToAddr.get? key = some a → a = addr := by
        intro a prior
        cases found : table.get? key with
        | none => exact agree a (by simp only [found, Option.orElse_none]; exact prior)
        | some earlier => exact (held.2 key earlier found a prior).symm.trans (localAgree earlier found)
      exact ⟨table.insert key addr, rfl, held.insert localAgree oldAgree⟩
    · constructor
      · intro _ _ impossible; cases impossible
      · intro _ _ impossible; simp at impossible
  intro n addr member old prior
  exact valid.2 n addr (valid.1 n addr (Array.mem_toList_iff.mpr member)) old prior

theorem checkCompiledBlock_primary_agrees {before : CompileEnv} {lo : Name} {result : BlockResult}
    {cache : BlockState}
    (run : checkCompiledBlock before lo result cache = .ok ()) :
    PrimaryAgrees before (primaryClaims lo result) := by
  obtain ⟨_, claims, _⟩ := Loop.except_bind_ok.mp run
  exact checkBlockClaims_primary_agrees claims

private theorem loop_field_bind {α σ β γ : Type} (xs : Array α) (init : σ)
    (body : α → σ → Id (ForInStep σ)) (k : σ → Id β) (field : σ → γ)
    (put : γ → α → γ) (P : β → Prop)
    (continues : ∀ x s, body x s = .yield (body x s).value)
    (step : ∀ s x, field (body x s).value = put (field s) x)
    (next : ∀ s, field s = xs.foldl put (field init) → P (k s)) :
    P (forIn (m := Id) xs init body >>= k) := by
  apply next
  rw [Loop.forIn_id_array body continues, ← Array.foldl_hom field (fun s x => (step s x).symm)]

set_option hygiene false in
local macro "finish_primary" held:term : tactic => `(tactic| (
  refine Ix.Cert.Resolution.loop_bind
    (P := fun d : DriverAcc => d.cenv.nameToAddr = goalMap)
    (I := fun _ : Array Name => True) _ _ _ _ trivial (fun _ _ _ _ => trivial) ?_
  intro _ _; exact $held))

set_option hygiene false in
local macro "merge_primary_tail" held:term : tactic => `(tactic| (
  refine Ix.Cert.Resolution.loop_bind
    (P := fun d : DriverAcc => d.cenv.nameToAddr = goalMap)
    (I := fun c : CompileEnv => c.nameToAddr = goalMap) _ _ _ _ $held (fun _ _ _ h => h) ?_
  intro L hL
  refine Ix.Cert.Resolution.loop_bind
    (P := fun d : DriverAcc => d.cenv.nameToAddr = goalMap)
    (I := fun c : CompileEnv => c.nameToAddr = goalMap) _ _ _ _ hL ?_ ?_
  · intro _ _ _ h; split <;> exact h
  · intro L' hL'
    split
    · refine Ix.Cert.Resolution.loop_bind
        (P := fun d : DriverAcc => d.cenv.nameToAddr = goalMap)
        (I := fun c : CompileEnv => c.nameToAddr = goalMap) _ _ _ _ hL' ?_ ?_
      · intro cls _ s hs
        exact Ix.Cert.Resolution.forIn_inv_array
          (fun c : CompileEnv => c.nameToAddr = goalMap) _ cls (by intros; assumption) s hs
      · intro _ h; finish_primary h
    · finish_primary hL'))

/-- Exact serialization, hash, duplicates and order of the ACTUAL primary
registrations. Reclaimed-name checks affect only the Named map. -/
theorem mergeCompiledBlock_primary (acc : DriverAcc) (lo : Name) (result : BlockResult)
    (cache : BlockState) :
    (mergeCompiledBlock acc lo result cache).cenv.nameToAddr =
      (primaryClaims lo result).foldl (fun table (name, addr) => table.insert name addr) acc.cenv.nameToAddr := by
  let goalMap := (primaryClaims lo result).foldl (fun table (name, addr) => table.insert name addr) acc.cenv.nameToAddr
  change _ = goalMap
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · rename_i empty
    split <;> merge_primary_tail (by simp [goalMap, primaryClaims, empty])
  · rename_i nonempty
    refine loop_field_bind (field := CompileEnv.nameToAddr)
      (put := fun table (name, proj, _) => table.insert name (Address.admissionHash (Ixon.ser proj)))
      (P := fun d : DriverAcc => d.cenv.nameToAddr = goalMap) _ _ _ _ ?_ ?_ ?_
    · intro _ _; split <;> rfl
    · intro _ _; split <;> rfl
    · intro L hL
      have actual : L.nameToAddr = goalMap := by
        simpa only [goalMap, primaryClaims, nonempty, Bool.false_eq_true, ↓reduceIte, Array.foldl_map] using hL
      merge_primary_tail actual

/-- An agreed write sequence preserves an exact old hit, including through
duplicates. The table may freely acquire other entries. -/
theorem PrimaryAgrees.foldl_keeps {before : CompileEnv} {writes : Array (Name × Address)}
    (agrees : PrimaryAgrees before writes) {n : ExactName} {addr : Address}
    (old : before.nameToAddr.get? n = some addr) :
    (writes.foldl (fun table (key, value) => table.insert key value) before.nameToAddr).get? n = some addr := by
  rw [← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun table : Std.HashMap ExactName Address => table.get? n = some addr)
  · exact old
  · intro table held ⟨key, value⟩ member
    change (table.insert (show ExactName from key) value).get? n = some addr
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    split
    · rename_i same
      have equal : (show ExactName from key) = n := eq_of_beq same
      have agreed : value = addr := agrees key value (Array.mem_toList_iff.mp member)
        addr ((congrArg (fun q : ExactName => before.nameToAddr.get? q) equal).trans old)
      exact congrArg some agreed
    · exact held

end Ix.CompileCert.PrimaryAddressFrame
