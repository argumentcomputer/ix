import Ix.Compiler.IxIR1.Sim
import Ix.Compiler.IxIR1.Mono

/-!
# Progress foundations for the IxIR₁ evaluator

The ownership development proves partial correctness: if an evaluator call
succeeds, exact roots are conserved.  Progress also needs the complementary
fact that well-owned states cannot take a dynamic memory-error branch.

This file starts with the recursive release core.  At every fuel, a shared
drop or unique deep free from its matching owned root either exhausts fuel or
succeeds while consuming exactly that root.  In particular, no `.mem`,
ordinary `.stuck`, or closed-world error is reachable inside the deep-release
mutual recursion.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim

/-- The only permitted failure in a progress approximation is fuel
exhaustion. -/
def SucceedsOrFuel {alpha : Type} (result : Except Err alpha) : Prop :=
  result = .error .fuel ∨ ∃ value, result = .ok value

/-- A finite evaluator observation that has genuinely settled without a
memory-discipline failure or a closed-world lookup failure.  Unlike
`SucceedsOrFuel`, this judgment still admits ordinary stuckness, but excludes
fuel exhaustion, `Err.mem`, and `Err.unknownRef`.  The latter strengthening
lets the source-guided call/extern contracts expose their closed-world
content independently of the remaining projection-admissibility boundary. -/
inductive SettlesWithoutMemory {alpha : Type} (result : Except Err alpha) :
    Prop where
  | success (value : alpha) (hrun : result = .ok value)
  | stuck (message : String) (hrun : result = .error (.stuck message))

private theorem bindOk {error alpha beta : Type} (value : alpha)
    (next : alpha → Except error beta) :
    (Except.ok value >>= next) = next value := rfl

private theorem bindErr {error alpha beta : Type} (err : error)
    (next : alpha → Except error beta) :
    ((Except.error err : Except error alpha) >>= next) = .error err := rfl

/-! A proof-oriented count of live slots.  Unlike the public counter-facing
`Store.live`, this recursive list presentation makes the strict decrease of
`Store.kill` transparent to the termination argument below. -/

private def liveSlotsList {alpha : Type} : List (Option alpha) → Nat
  | [] => 0
  | none :: rest => liveSlotsList rest
  | some _ :: rest => liveSlotsList rest + 1

private def Store.liveSlots (store : Store) : Nat :=
  liveSlotsList store.nodes.toList

private theorem liveSlotsList_set_none {alpha : Type} :
    ∀ {values : List (Option alpha)} {index : Nat} {value : alpha},
      values[index]? = some (some value) →
      liveSlotsList (values.set index none) + 1 = liveSlotsList values
  | [], index, value, hget => by simp at hget
  | head :: tail, 0, value, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst head
      simp [liveSlotsList]
  | head :: tail, index + 1, value, hget => by
      simp only [List.getElem?_cons_succ] at hget
      have ih := liveSlotsList_set_none hget
      cases head <;> simp [liveSlotsList] at ih ⊢ <;> omega

private theorem liveSlotsList_set_some {alpha : Type} :
    ∀ {values : List (Option alpha)} {index : Nat} {old new : alpha},
      values[index]? = some (some old) →
      liveSlotsList (values.set index (some new)) = liveSlotsList values
  | [], index, old, new, hget => by simp at hget
  | head :: tail, 0, old, new, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst head
      simp [liveSlotsList]
  | head :: tail, index + 1, old, new, hget => by
      simp only [List.getElem?_cons_succ] at hget
      have ih := liveSlotsList_set_some (new := new) hget
      cases head <;> simp [liveSlotsList] at ih ⊢ <;> omega

private theorem Store.liveSlots_rcTick (store : Store) :
    store.rcTick.liveSlots = store.liveSlots := rfl

private theorem Store.liveSlots_kill {store : Store} {loc : Nat}
    {box : NodeBox} (hget : store.get? loc = some box) :
    (store.kill loc).liveSlots + 1 = store.liveSlots := by
  have hnodes := nodes_get?_of_get? hget
  have hlist : store.nodes.toList[loc]? = some (some box) := by
    simpa using hnodes
  simp only [Store.liveSlots, Store.kill, Array.toList_set!]
  exact liveSlotsList_set_none hlist

private theorem Store.liveSlots_setBox {store : Store} {loc : Nat}
    {old new : NodeBox} (hget : store.get? loc = some old) :
    (store.setBox loc new).liveSlots = store.liveSlots := by
  have hnodes := nodes_get?_of_get? hget
  have hlist : store.nodes.toList[loc]? = some (some old) := by
    simpa using hnodes
  simp only [Store.liveSlots, Store.setBox, Array.toList_set!]
  exact liveSlotsList_set_some hlist

private theorem Store.liveSlots_decRcStore {store : Store} {loc : Nat}
    {box : NodeBox} (hget : store.get? loc = some box) :
    (decRcStore store loc box).liveSlots = store.liveSlots := by
  unfold decRcStore
  rw [Store.liveSlots_setBox]
  · exact Store.liveSlots_rcTick store
  · simpa using hget

private def DropSafeAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ store value rest,
    RootOwnership store (⟨.shared, value⟩ :: rest) →
      dropVal ctx fuel store value = .error .fuel ∨
        ∃ store', dropVal ctx fuel store value = .ok store' ∧
          RootOwnership store' rest) ∧
  (∀ store values rest,
    RootOwnership store (rootsFor .shared values ++ rest) →
      dropMany ctx fuel store values = .error .fuel ∨
        ∃ store', dropMany ctx fuel store values = .ok store' ∧
          RootOwnership store' rest)

private def DropUSafeAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ store value rest,
    RootOwnership store (⟨.unique, value⟩ :: rest) →
      dropUVal ctx fuel store value = .error .fuel ∨
        ∃ store', dropUVal ctx fuel store value = .ok store' ∧
          RootOwnership store' rest) ∧
  (∀ store values rest,
    RootOwnership store (rootsFor .unique values ++ rest) →
      dropManyU ctx fuel store values = .error .fuel ∨
        ∃ store', dropManyU ctx fuel store values = .ok store' ∧
          RootOwnership store' rest)

private def DropSafetyAt (ctx : Ctx) (fuel : Nat) : Prop :=
  DropSafeAt ctx fuel ∧ DropUSafeAt ctx fuel

/-- Shared and unique deep-release safety follow one evaluator-fuel
traversal.  The owner-sensitive single-root cases remain separate, while the
zero-fuel and sequential-release recursion are established together. -/
private theorem dropSafetyAt (ctx : Ctx) : ∀ fuel, DropSafetyAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro store value rest hown
      left
      simp [dropVal]
    · intro store values rest hown
      left
      simp [dropMany]
    · intro store value rest hown
      left
      simp [dropUVal]
    · intro store values rest hown
      left
      simp [dropManyU]
  | succ fuel ih =>
    obtain ⟨⟨ihVal, ihMany⟩, ⟨ihUVal, ihManyU⟩⟩ := ih
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro store value rest hown
      cases value with
      | lit literal =>
        right
        exact ⟨store, by simp [dropVal], hown.dropNoLocation rfl⟩
      | erased =>
        right
        exact ⟨store, by simp [dropVal], hown.dropNoLocation rfl⟩
      | loc loc =>
        have hworld := hown.roots_world
          (⟨.shared, .loc loc⟩ : Root) (by simp)
        obtain ⟨box, hget, hboxWorld⟩ := hworld
        cases box with
        | mk world rc node =>
          change world = .shared at hboxWorld
          subst world
          by_cases hrc : rc = 1
          · subst rc
            have htickGet :
                store.rcTick.get? loc = some ⟨.shared, 1, node⟩ := by
              simpa using hget
            have hchildren : RootOwnership (store.rcTick.kill loc)
                (rootsFor .shared (nodeChildren node) ++ rest) :=
              (hown.rcTick).killSharedOne htickGet
            cases node with
            | ctorN cid fields =>
              simpa [dropVal, hget] using
                ihMany (store.rcTick.kill loc) fields.toList rest hchildren
            | papN address arity args =>
              simpa [dropVal, hget] using
                ihMany (store.rcTick.kill loc) args.toList rest hchildren
          · have hrcPos : 0 < rc := hown.shared_rc_pos hget
            have hrcMany : 1 < rc := by omega
            right
            exact ⟨decRcStore store loc ⟨.shared, rc, node⟩,
              dropVal_shared_many (ctx := ctx) (fuel := fuel)
                hrcMany hget,
              hown.dropSharedMany hrcMany hget⟩
    · intro store values rest hown
      cases values with
      | nil =>
        right
        exact ⟨store, by simp [dropMany], by
          simpa [rootsFor] using hown⟩
      | cons value values =>
        have hfirstOwn : RootOwnership store
            (⟨.shared, value⟩ ::
              (rootsFor .shared values ++ rest)) := by
          simpa [rootsFor] using hown
        rcases ihVal store value _ hfirstOwn with
          hfirstFuel | ⟨middle, hfirst, hmiddle⟩
        · left
          rw [dropMany.eq_def]
          dsimp only
          rw [hfirstFuel, bindErr]
        · rcases ihMany middle values rest hmiddle with
            hrestFuel | ⟨store', hrest, hfinal⟩
          · left
            rw [dropMany.eq_def]
            dsimp only
            rw [hfirst, bindOk]
            exact hrestFuel
          · right
            refine ⟨store', ?_, hfinal⟩
            rw [dropMany.eq_def]
            dsimp only
            rw [hfirst, bindOk]
            exact hrest
    · intro store value rest hown
      cases value with
      | lit literal =>
        right
        exact ⟨store, by simp [dropUVal], hown.dropNoLocation rfl⟩
      | erased =>
        right
        exact ⟨store, by simp [dropUVal], hown.dropNoLocation rfl⟩
      | loc loc =>
        have hworld := hown.roots_world
          (⟨.unique, .loc loc⟩ : Root) (by simp)
        obtain ⟨box, hget, hboxWorld⟩ := hworld
        cases box with
        | mk world rc node =>
          change world = .unique at hboxWorld
          subst world
          have hrc : rc = 1 := (hown.counts hget).1
          subst rc
          cases node with
          | ctorN cid fields =>
            have hchildren : RootOwnership (store.kill loc)
                (rootsFor .unique fields.toList ++ rest) :=
              hown.killUniqueOne hget
            simpa [dropUVal, hget] using
              ihManyU (store.kill loc) fields.toList rest hchildren
          | papN address arity args =>
            have hshared : (Owned.unique : Owned) = .shared :=
              hown.pap_shared hget rfl
            contradiction
    · intro store values rest hown
      cases values with
      | nil =>
        right
        exact ⟨store, by simp [dropManyU], by
          simpa [rootsFor] using hown⟩
      | cons value values =>
        have hfirstOwn : RootOwnership store
            (⟨.unique, value⟩ ::
              (rootsFor .unique values ++ rest)) := by
          simpa [rootsFor] using hown
        rcases ihUVal store value _ hfirstOwn with
          hfirstFuel | ⟨middle, hfirst, hmiddle⟩
        · left
          rw [dropManyU.eq_def]
          dsimp only
          rw [hfirstFuel, bindErr]
        · rcases ihManyU middle values rest hmiddle with
            hrestFuel | ⟨store', hrest, hfinal⟩
          · left
            rw [dropManyU.eq_def]
            dsimp only
            rw [hfirst, bindOk]
            exact hrestFuel
          · right
            refine ⟨store', ?_, hfinal⟩
            rw [dropManyU.eq_def]
            dsimp only
            rw [hfirst, bindOk]
            exact hrest

/-- A well-owned shared root can only succeed or exhaust fuel during deep
release, and success consumes exactly that root. -/
theorem dropVal_safe {ctx : Ctx} {fuel : Nat} {store : Store}
    {value : RVal} {rest : List Root}
    (hown : RootOwnership store (⟨.shared, value⟩ :: rest)) :
    dropVal ctx fuel store value = .error .fuel ∨
      ∃ store', dropVal ctx fuel store value = .ok store' ∧
        RootOwnership store' rest :=
  (dropSafetyAt ctx fuel).1.1 store value rest hown

/-- Sequential shared release has the same fuel-or-success progress
property. -/
theorem dropMany_safe {ctx : Ctx} {fuel : Nat} {store : Store}
    {values : List RVal} {rest : List Root}
    (hown : RootOwnership store (rootsFor .shared values ++ rest)) :
    dropMany ctx fuel store values = .error .fuel ∨
      ∃ store', dropMany ctx fuel store values = .ok store' ∧
        RootOwnership store' rest :=
  (dropSafetyAt ctx fuel).1.2 store values rest hown

/-- A well-owned unique root can only succeed or exhaust fuel during deep
free, and success consumes exactly that root. -/
theorem dropUVal_safe {ctx : Ctx} {fuel : Nat} {store : Store}
    {value : RVal} {rest : List Root}
    (hown : RootOwnership store (⟨.unique, value⟩ :: rest)) :
    dropUVal ctx fuel store value = .error .fuel ∨
      ∃ store', dropUVal ctx fuel store value = .ok store' ∧
        RootOwnership store' rest :=
  (dropSafetyAt ctx fuel).2.1 store value rest hown

/-- Sequential unique deep free has the same fuel-or-success progress
property. -/
theorem dropManyU_safe {ctx : Ctx} {fuel : Nat} {store : Store}
    {values : List RVal} {rest : List Root}
    (hown : RootOwnership store (rootsFor .unique values ++ rest)) :
    dropManyU ctx fuel store values = .error .fuel ∨
      ∃ store', dropManyU ctx fuel store values = .ok store' ∧
        RootOwnership store' rest :=
  (dropSafetyAt ctx fuel).2.2 store values rest hown

/-! ## Deep-release termination -/

private def DropValProgressAt (ctx : Ctx) (store : Store) : Prop :=
  ∀ value rest,
    RootOwnership store (⟨.shared, value⟩ :: rest) →
    ∃ fuel store',
      dropVal ctx fuel store value = .ok store' ∧
      RootOwnership store' rest ∧
      store'.liveSlots ≤ store.liveSlots

private def DropManyProgressAt (ctx : Ctx) (store : Store) : Prop :=
  ∀ values rest,
    RootOwnership store (rootsFor .shared values ++ rest) →
    ∃ fuel store',
      dropMany ctx fuel store values = .ok store' ∧
      RootOwnership store' rest ∧
      store'.liveSlots ≤ store.liveSlots

/-- Unique single-root termination half of the combined deep-release
judgment. -/
private def DropUValProgressAt (ctx : Ctx) (store : Store) : Prop :=
  ∀ value rest,
    RootOwnership store (⟨.unique, value⟩ :: rest) →
    ∃ fuel store',
      dropUVal ctx fuel store value = .ok store' ∧
      RootOwnership store' rest ∧
      store'.liveSlots ≤ store.liveSlots

/-- Unique sequential termination half of the combined deep-release
judgment. -/
private def DropManyUProgressAt (ctx : Ctx) (store : Store) : Prop :=
  ∀ values rest,
    RootOwnership store (rootsFor .unique values ++ rest) →
    ∃ fuel store',
      dropManyU ctx fuel store values = .ok store' ∧
      RootOwnership store' rest ∧
      store'.liveSlots ≤ store.liveSlots

private def DropProgressAt (ctx : Ctx) (store : Store) : Prop :=
  (DropValProgressAt ctx store ∧ DropManyProgressAt ctx store) ∧
    (DropUValProgressAt ctx store ∧ DropManyUProgressAt ctx store)

/-- Shared and unique deep-release termination use one strong induction on
the number of live heap slots.  Each owner keeps its local destruction rule;
recursive child release and sequential fuel synchronization share the same
well-founded traversal. -/
private theorem dropProgressAt (ctx : Ctx) : ∀ live store,
    store.liveSlots = live →
    DropProgressAt ctx store := by
  intro live
  induction live using Nat.strongRecOn with
  | ind live ih =>
    have hval : ∀ store, store.liveSlots = live →
        DropValProgressAt ctx store := by
      intro store hlive value rest hown
      cases value with
      | lit literal =>
        exact ⟨1, store, by simp [dropVal],
          hown.dropNoLocation rfl, Nat.le_refl _⟩
      | erased =>
        exact ⟨1, store, by simp [dropVal],
          hown.dropNoLocation rfl, Nat.le_refl _⟩
      | loc loc =>
        have hworld := hown.roots_world
          (⟨.shared, .loc loc⟩ : Root) (by simp)
        obtain ⟨box, hget, hboxWorld⟩ := hworld
        cases box with
        | mk world rc node =>
          change world = .shared at hboxWorld
          subst world
          by_cases hrc : rc = 1
          · subst rc
            have htickGet :
                store.rcTick.get? loc = some ⟨.shared, 1, node⟩ := by
              simpa using hget
            let killed := store.rcTick.kill loc
            have hkilledOwn : RootOwnership killed
                (rootsFor .shared (nodeChildren node) ++ rest) := by
              dsimp only [killed]
              exact (hown.rcTick).killSharedOne htickGet
            have hkilledEq : killed.liveSlots + 1 = live := by
              have hk : killed.liveSlots + 1 = store.liveSlots := by
                dsimp only [killed]
                have hkill := Store.liveSlots_kill htickGet
                rw [Store.liveSlots_rcTick] at hkill
                exact hkill
              exact hk.trans hlive
            have hkilledLt : killed.liveSlots < live := by omega
            have hsmall := ih killed.liveSlots hkilledLt killed rfl
            cases node with
            | ctorN cid fields =>
              obtain ⟨fuel, store', hrun, hown', hslots⟩ :=
                hsmall.1.2 fields.toList rest (by
                  simpa [nodeChildren] using hkilledOwn)
              refine ⟨fuel + 1, store', ?_, hown', ?_⟩
              · simpa [dropVal, hget] using hrun
              · exact Nat.le_trans hslots (by omega)
            | papN address arity args =>
              obtain ⟨fuel, store', hrun, hown', hslots⟩ :=
                hsmall.1.2 args.toList rest (by
                  simpa [nodeChildren] using hkilledOwn)
              refine ⟨fuel + 1, store', ?_, hown', ?_⟩
              · simpa [dropVal, hget] using hrun
              · exact Nat.le_trans hslots (by omega)
          · have hrcPos : 0 < rc := hown.shared_rc_pos hget
            have hrcMany : 1 < rc := by omega
            let store' := decRcStore store loc ⟨.shared, rc, node⟩
            refine ⟨1, store', ?_, ?_, ?_⟩
            · exact dropVal_shared_many (ctx := ctx) (fuel := 0)
                hrcMany hget
            · exact hown.dropSharedMany hrcMany hget
            · exact Nat.le_of_eq (Store.liveSlots_decRcStore hget)
    have hvalLe : ∀ store, store.liveSlots ≤ live →
        DropValProgressAt ctx store := by
      intro store hle
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · exact hval store heq
      · exact (ih store.liveSlots hlt store rfl).1.1
    have hmanyLe : ∀ values store rest,
        store.liveSlots ≤ live →
        RootOwnership store (rootsFor .shared values ++ rest) →
        ∃ fuel store',
          dropMany ctx fuel store values = .ok store' ∧
          RootOwnership store' rest ∧
          store'.liveSlots ≤ store.liveSlots := by
      intro values
      induction values with
      | nil =>
        intro store rest hle hown
        exact ⟨1, store, by simp [dropMany], by
          simpa [rootsFor] using hown, Nat.le_refl _⟩
      | cons value values ihValues =>
        intro store rest hle hown
        have hfirstOwn : RootOwnership store
            (⟨.shared, value⟩ ::
              (rootsFor .shared values ++ rest)) := by
          simpa [rootsFor] using hown
        obtain ⟨firstFuel, middle, hfirst, hmiddle, hmiddleSlots⟩ :=
          hvalLe store hle value _ hfirstOwn
        obtain ⟨restFuel, store', hrest, hfinal, hfinalSlots⟩ :=
          ihValues middle rest (Nat.le_trans hmiddleSlots hle) hmiddle
        let common := max firstFuel restFuel
        have hfirst' : dropVal ctx common store value = .ok middle :=
          dropVal_mono (Nat.le_max_left _ _) hfirst
        have hrest' : dropMany ctx common middle values = .ok store' :=
          dropMany_mono (Nat.le_max_right _ _) hrest
        refine ⟨common + 1, store', ?_, hfinal,
          Nat.le_trans hfinalSlots hmiddleSlots⟩
        rw [dropMany.eq_def]
        dsimp only
        rw [hfirst', bindOk]
        exact hrest'
    have hshared : ∀ store, store.liveSlots = live →
        DropValProgressAt ctx store ∧ DropManyProgressAt ctx store := by
      intro store hlive
      exact ⟨hval store hlive, fun values rest hown =>
        hmanyLe values store rest (by omega) hown⟩
    have huval : ∀ store, store.liveSlots = live →
        DropUValProgressAt ctx store := by
      intro store hlive value rest hown
      cases value with
      | lit literal =>
        exact ⟨1, store, by simp [dropUVal],
          hown.dropNoLocation rfl, Nat.le_refl _⟩
      | erased =>
        exact ⟨1, store, by simp [dropUVal],
          hown.dropNoLocation rfl, Nat.le_refl _⟩
      | loc loc =>
        have hworld := hown.roots_world
          (⟨.unique, .loc loc⟩ : Root) (by simp)
        obtain ⟨box, hget, hboxWorld⟩ := hworld
        cases box with
        | mk world rc node =>
          change world = .unique at hboxWorld
          subst world
          have hrc : rc = 1 := (hown.counts hget).1
          subst rc
          cases node with
          | ctorN cid fields =>
            let killed := store.kill loc
            have hkilledOwn : RootOwnership killed
                (rootsFor .unique fields.toList ++ rest) := by
              dsimp only [killed]
              simpa [nodeChildren] using hown.killUniqueOne hget
            have hkilledEq : killed.liveSlots + 1 = live := by
              have hk : killed.liveSlots + 1 = store.liveSlots := by
                dsimp only [killed]
                exact Store.liveSlots_kill hget
              exact hk.trans hlive
            have hkilledLt : killed.liveSlots < live := by omega
            have hsmall := ih killed.liveSlots hkilledLt killed rfl
            obtain ⟨fuel, store', hrun, hown', hslots⟩ :=
              hsmall.2.2 fields.toList rest hkilledOwn
            refine ⟨fuel + 1, store', ?_, hown', ?_⟩
            · simpa [dropUVal, hget] using hrun
            · exact Nat.le_trans hslots (by omega)
          | papN address arity args =>
            have hshared : (Owned.unique : Owned) = .shared :=
              hown.pap_shared hget rfl
            contradiction
    have huvalLe : ∀ store, store.liveSlots ≤ live →
        DropUValProgressAt ctx store := by
      intro store hle
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · exact huval store heq
      · exact (ih store.liveSlots hlt store rfl).2.1
    have hmanyULe : ∀ values store rest,
        store.liveSlots ≤ live →
        RootOwnership store (rootsFor .unique values ++ rest) →
        ∃ fuel store',
          dropManyU ctx fuel store values = .ok store' ∧
          RootOwnership store' rest ∧
          store'.liveSlots ≤ store.liveSlots := by
      intro values
      induction values with
      | nil =>
        intro store rest hle hown
        exact ⟨1, store, by simp [dropManyU], by
          simpa [rootsFor] using hown, Nat.le_refl _⟩
      | cons value values ihValues =>
        intro store rest hle hown
        have hfirstOwn : RootOwnership store
            (⟨.unique, value⟩ ::
              (rootsFor .unique values ++ rest)) := by
          simpa [rootsFor] using hown
        obtain ⟨firstFuel, middle, hfirst, hmiddle, hmiddleSlots⟩ :=
          huvalLe store hle value _ hfirstOwn
        obtain ⟨restFuel, store', hrest, hfinal, hfinalSlots⟩ :=
          ihValues middle rest (Nat.le_trans hmiddleSlots hle) hmiddle
        let common := max firstFuel restFuel
        have hfirst' : dropUVal ctx common store value = .ok middle :=
          dropUVal_mono (Nat.le_max_left _ _) hfirst
        have hrest' : dropManyU ctx common middle values = .ok store' :=
          dropManyU_mono (Nat.le_max_right _ _) hrest
        refine ⟨common + 1, store', ?_, hfinal,
          Nat.le_trans hfinalSlots hmiddleSlots⟩
        rw [dropManyU.eq_def]
        dsimp only
        rw [hfirst', bindOk]
        exact hrest'
    intro store hlive
    exact ⟨hshared store hlive,
      ⟨huval store hlive, fun values rest hown =>
        hmanyULe values store rest (by omega) hown⟩⟩

/-- Every well-owned shared root has some successful deep-release fuel. -/
theorem dropVal_progress {ctx : Ctx} {store : Store} {value : RVal}
    {rest : List Root}
    (hown : RootOwnership store (⟨.shared, value⟩ :: rest)) :
    ∃ fuel store', dropVal ctx fuel store value = .ok store' ∧
      RootOwnership store' rest := by
  obtain ⟨fuel, store', hrun, hown', _⟩ :=
    (dropProgressAt ctx store.liveSlots store rfl).1.1 value rest hown
  exact ⟨fuel, store', hrun, hown'⟩

/-- Every well-owned vector of shared roots has some successful sequential
release fuel. -/
theorem dropMany_progress {ctx : Ctx} {store : Store}
    {values : List RVal} {rest : List Root}
    (hown : RootOwnership store (rootsFor .shared values ++ rest)) :
    ∃ fuel store', dropMany ctx fuel store values = .ok store' ∧
      RootOwnership store' rest := by
  obtain ⟨fuel, store', hrun, hown', _⟩ :=
    (dropProgressAt ctx store.liveSlots store rfl).1.2 values rest hown
  exact ⟨fuel, store', hrun, hown'⟩

/-- Every well-owned unique root has some successful deep-free fuel. -/
theorem dropUVal_progress {ctx : Ctx} {store : Store} {value : RVal}
    {rest : List Root}
    (hown : RootOwnership store (⟨.unique, value⟩ :: rest)) :
    ∃ fuel store', dropUVal ctx fuel store value = .ok store' ∧
      RootOwnership store' rest := by
  obtain ⟨fuel, store', hrun, hown', _⟩ :=
    (dropProgressAt ctx store.liveSlots store rfl).2.1 value rest hown
  exact ⟨fuel, store', hrun, hown'⟩

/-- Every well-owned vector of unique roots has some successful sequential
deep-free fuel. -/
theorem dropManyU_progress {ctx : Ctx} {store : Store}
    {values : List RVal} {rest : List Root}
    (hown : RootOwnership store (rootsFor .unique values ++ rest)) :
    ∃ fuel store', dropManyU ctx fuel store values = .ok store' ∧
      RootOwnership store' rest := by
  obtain ⟨fuel, store', hrun, hown', _⟩ :=
    (dropProgressAt ctx store.liveSlots store rfl).2.2 values rest hown
  exact ⟨fuel, store', hrun, hown'⟩

/-! ## Callable progress contracts -/

/-- Successful body execution exists for every well-owned argument frame.
This is the total-correctness companion of `FnOwnershipContract`; keeping the
two contracts separate lets the established ownership development remain a
reusable partial-correctness layer. -/
structure FnProgressContract (ctx : Ctx) (d : FnDef)
    (argWorlds : List Owned) : Prop where
  arity_eq : argWorlds.length = d.arity
  progresses : ∀ {store : Store} {args : List RVal} {rest : List Root},
    args.length = argWorlds.length →
    RootOwnership store (rootsForWorlds argWorlds args ++ rest) →
    ∃ fuel store' value,
      runCode ctx fuel d store args.reverse d.body = .ok (store', value)

/-- Entering a known function terminates when its body has a progress
contract.  The existing ownership contract proves the constructed body
result passes the evaluator's dynamic result-world check. -/
theorem invoke_fn_progress {ctx : Ctx} {address : Ixon.Address}
    {d : FnDef} {argWorlds : List Owned} {args : List RVal}
    {store : Store} {rest : List Root}
    (hdecl : ctx.decls address = some (.fn d))
    (hprogress : FnProgressContract ctx d argWorlds)
    (hownership : FnOwnershipContract ctx d argWorlds)
    (hlength : args.length = argWorlds.length)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest)) :
    ∃ fuel store' value,
      invoke ctx fuel address args store = .ok (store', value) := by
  obtain ⟨bodyFuel, store', value, hbody⟩ :=
    hprogress.progresses hlength hown
  have hout : RootOwnership store' (⟨d.result, value⟩ :: rest) :=
    hownership.preserves hlength hown hbody
  have hworld : HasWorld store' d.result value :=
    hout.roots_world ⟨d.result, value⟩ (by simp)
  have hcheck : checkResultWorld d.result (store', value) =
      .ok (store', value) := by
    simp [checkResultWorld, rval_hasWorld_eq_true_iff.mpr hworld]
  have harity : args.length = d.arity :=
    hlength.trans hprogress.arity_eq
  refine ⟨bodyFuel + 1, store', value, ?_⟩
  rw [invoke.eq_def]
  dsimp only
  rw [hdecl]
  dsimp only
  simp only [harity]
  simp
  rw [hbody, bindOk]
  exact hcheck

/-- Operation-level direct-call progress, with exact result ownership ready
for the caller continuation. -/
theorem runOp_call_progress {ctx : Ctx} {cur d : FnDef}
    {address : Ixon.Address} {atoms : Array Atom} {args : List RVal}
    {argWorlds : List Owned} {store : Store} {env : List RVal}
    {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok args)
    (hdecl : ctx.decls address = some (.fn d))
    (hprogress : FnProgressContract ctx d argWorlds)
    (hownership : FnOwnershipContract ctx d argWorlds)
    (hlength : args.length = argWorlds.length)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest)) :
    ∃ fuel store' value,
      runOp ctx fuel cur store env (.call address atoms) =
          .ok (store', value) ∧
        RootOwnership store' (⟨d.result, value⟩ :: rest) := by
  obtain ⟨invokeFuel, store', value, hinvoke⟩ :=
    invoke_fn_progress hdecl hprogress hownership hlength hown
  have hrun : runOp ctx (invokeFuel + 1) cur store env
      (.call address atoms) = .ok (store', value) := by
    rw [runOp.eq_def]
    dsimp only
    rw [hargs, bindOk]
    exact hinvoke
  refine ⟨invokeFuel + 1, store', value, hrun, ?_⟩
  exact runOp_call_owned (fuel := invokeFuel) hargs hdecl hownership
    hown hrun

/-- Recursive self-call progress.  The progress contract supplies a body
run; its ownership twin proves that run passes `checkResultWorld`. -/
theorem runOp_callSelf_progress {ctx : Ctx} {cur : FnDef}
    {atoms : Array Atom} {args : List RVal}
    {argWorlds : List Owned} {store : Store} {env : List RVal}
    {rest : List Root}
    (hargs : resolveAtoms env atoms = .ok args)
    (hprogress : FnProgressContract ctx cur argWorlds)
    (hownership : FnOwnershipContract ctx cur argWorlds)
    (hlength : args.length = argWorlds.length)
    (hown : RootOwnership store
      (rootsForWorlds argWorlds args ++ rest)) :
    ∃ fuel store' value,
      runOp ctx fuel cur store env (.callSelf atoms) =
          .ok (store', value) ∧
        RootOwnership store' (⟨cur.result, value⟩ :: rest) := by
  obtain ⟨bodyFuel, store', value, hbody⟩ :=
    hprogress.progresses hlength hown
  have hout : RootOwnership store'
      (⟨cur.result, value⟩ :: rest) :=
    hownership.preserves hlength hown hbody
  have hworld : HasWorld store' cur.result value :=
    hout.roots_world ⟨cur.result, value⟩ (by simp)
  have hcheck : checkResultWorld cur.result (store', value) =
      .ok (store', value) := by
    simp [checkResultWorld, rval_hasWorld_eq_true_iff.mpr hworld]
  have harity : args.length = cur.arity :=
    hlength.trans hprogress.arity_eq
  have hrun : runOp ctx (bodyFuel + 1) cur store env
      (.callSelf atoms) = .ok (store', value) := by
    rw [runOp.eq_def]
    dsimp only
    rw [hargs, bindOk]
    simp only [harity]
    simp
    rw [hbody, bindOk]
    exact hcheck
  exact ⟨bodyFuel + 1, store', value, hrun, hout⟩

end Ix.Compiler.IxIR1
