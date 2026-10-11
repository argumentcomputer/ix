import Ix.CompileCert.Canon.AllocationSteps

/-!
UNCOMPILED. The trace is constructed from the actual callback-generic query,
recursive walk, constructor write, queue and successful initializer. Internal
cache correctness is discharged from initialization, never a final premise.
-/

namespace Ix.CompileCert.Canon.ExpansionHistory
open Ix.Compile.Canon
open Ix (Name Expr)

theorem replaceIfNested_history (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt) (cache : CacheCorrect cx st) :
    Runs cx st (ExpansionCore.replaceIfNested cx np owner e depth st).2 := by
  rw [replaceIfNested_class_def]
  dsimp only [Id.run]
  repeat' (first | exact Runs.refl cx st | exact Runs.keyError cx st _ | split)
  all_goals
    show Runs cx st (forIn (m := Id) (β := XSt × Option Expr) (_ : Array (Array Name)) _ _).1
    refine forIn_id_inv_array (fun r : XSt × Option Expr => Runs cx st r.1)
      _ ?_ _ _ (Runs.refl cx st)
    intro cls current history
    apply history.trans
    apply classStep_history
    exact history.cache cache

theorem replaceAll_history (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name) :
    ∀ (e : Expr) (d : Nat) (st : XSt), CacheCorrect cx st →
      Runs cx st (ExpansionCore.replaceAll cx np owner e d st).2 := by
  intro e
  induction e with
  | app f a h ihf iha =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.app f a h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.app f a h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihf d st1 (hR.cache cache)
        revert h1
        cases ExpansionCore.replaceAll cx np owner f d st1 with
        | mk f' st2 =>
          intro h1
          have h2 := iha d st2 (h1.cache (hR.cache cache))
          revert h2
          cases ExpansionCore.replaceAll cx np owner a d st2 with
          | mk a' st3 => intro h2; exact hR.trans (h1.trans h2)
  | lam n t b bi h iht ihb =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.lam n t b bi h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.lam n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1 (hR.cache cache)
        revert h1
        cases ExpansionCore.replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2 (h1.cache (hR.cache cache))
          revert h2
          cases ExpansionCore.replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | forallE n t b bi h iht ihb =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.forallE n t b bi h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.forallE n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1 (hR.cache cache)
        revert h1
        cases ExpansionCore.replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2 (h1.cache (hR.cache cache))
          revert h2
          cases ExpansionCore.replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact hR.trans (h1.trans h2)
  | letE n t v b nd h iht ihv ihb =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.letE n t v b nd h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.letE n t v b nd h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1 (hR.cache cache)
        revert h1
        cases ExpansionCore.replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihv d st2 (h1.cache (hR.cache cache))
          revert h2
          cases ExpansionCore.replaceAll cx np owner v d st2 with
          | mk v' st3 =>
            intro h2
            have h3 := ihb (d + 1) st3 (h2.cache (h1.cache (hR.cache cache)))
            revert h3
            cases ExpansionCore.replaceAll cx np owner b (d + 1) st3 with
            | mk b' st4 => intro h3; exact hR.trans (h1.trans (h2.trans h3))
  | proj n i s h ihs =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.proj n i s h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.proj n i s h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihs d st1 (hR.cache cache)
        revert h1
        cases ExpansionCore.replaceAll cx np owner s d st1 with
        | mk s' st2 => intro h1; exact hR.trans h1
  | mdata md x h ihx =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.mdata md x h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.mdata md x h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihx d st1 (hR.cache cache)
        revert h1
        cases ExpansionCore.replaceAll cx np owner x d st1 with
        | mk x' st2 => intro h1; exact hR.trans h1
  | bvar i h =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.bvar i h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.bvar i h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | fvar n h =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.fvar n h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.fvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | mvar n h =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.mvar n h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.mvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | sort u h =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.sort u h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.sort u h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | const n us h =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.const n us h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.const n us h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | lit l h =>
    intro d st cache
    rw [ExpansionCore.replaceAll.eq_1]
    have hR := replaceIfNested_history cx np owner (.lit l h) d st cache
    revert hR
    cases ExpansionCore.replaceIfNested cx np owner (.lit l h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR


theorem walkCtor_history (cx : ExpansionCore.Ctx) (qi ci : Nat) (st : XSt)
    (cache : CacheCorrect cx st) : Runs cx st (ExpansionCore.walkCtor cx qi ci st) := by
  unfold ExpansionCore.walkCtor
  split
  · exact Runs.refl cx st
  · rename_i member foundMember
    split
    · exact Runs.refl cx st
    · rename_i ctor foundCtor
      generalize telescope : peelForalls cx.nParams ctor.typ #[] = pair
      obtain ⟨binders,body⟩ := pair
      dsimp only
      have history := replaceAll_history cx binders.size member.sourceOwner body 0 st cache
      revert history
      cases ExpansionCore.replaceAll cx binders.size member.sourceOwner body 0 st with
      | mk body' next =>
        intro history
        exact history.trans (Runs.ctorType cx next qi ci (mkForalls binders body'))

/-- No queue error is turned into a successful trace. The original run equality
is required and the two key-error/fuel failures are eliminated from that equality. -/
theorem walkQueue_history (cx : ExpansionCore.Ctx) :
    ∀ (fuel qi : Nat) (st final : XSt), CacheCorrect cx st →
      ExpansionCore.walkQueue cx fuel qi st = .ok final → Runs cx st final
  | 0,qi,st,final,cache,run => by
    rw [ExpansionCore.walkQueue.eq_1] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases except_pure_ok run
        exact Runs.refl cx st
  | fuel+1,qi,st,final,cache,run => by
    rw [ExpansionCore.walkQueue.eq_2] at run
    split at run
    · cases run
    · split at run
      · cases except_pure_ok run
        exact Runs.refl cx st
      · rename_i member found
        have prefixRun : Runs cx st
            ((List.range member.ctors.size).foldl (fun s ci => ExpansionCore.walkCtor cx qi ci s) st) := by
          refine list_foldl_inv (fun current => Runs cx st current)
            _ ?_ _ _ (Runs.refl cx st)
          intro current index history
          exact history.trans (walkCtor_history cx qi index current (history.cache cache))
        exact prefixRun.trans (walkQueue_history cx fuel (qi+1) _ final (prefixRun.cache cache) run)

/-- The initializer in the generic runtime, including all lookup failures. -/
def initialMembers (cx : ExpansionCore.Ctx) (ordered : Array Name)
    (aliases : Std.HashMap Name Name) : Except String XSt :=
  forIn ordered ({} : XSt) fun n st => do
    let some view := cx.ind? n | .error s!"expand: {namePretty n} is not an inductive"
    let constructors := view.ctors.map fun (cn,ct,nf) =>
      {name := cn, typ := canonicalizeConstNames aliases ct, nFields := nf : XCtor}
    return .yield (st.push {
      name := n, sourceOwner := n,
      typ := canonicalizeConstNames aliases view.type,
      ctors := constructors, nParams := cx.nParams, nIndices := view.numIndices})

theorem initialMembers_fields (cx : ExpansionCore.Ctx) (ordered : Array Name)
    (aliases : Std.HashMap Name Name) {st : XSt}
    (run : initialMembers cx ordered aliases = .ok st) :
    skel st = ordered.toList.map (fun n => (n,n)) ∧
      st.nextAuxIdx = 1 ∧ st.sourceNames? = none ∧
      st.allocatedNames = [] ∧ st.allocatedCtorRoots = [] := by
  unfold initialMembers at run
  apply forIn_except_array _ (fun pre state =>
    skel state = pre.map (fun n => (n,n)) ∧
      state.nextAuxIdx = 1 ∧ state.sourceNames? = none ∧
      state.allocatedNames = [] ∧ state.allocatedCtorRoots = [])
      ?_ ordered ⟨rfl,rfl,rfl,rfl,rfl⟩ run
  intro pre name before step fields success
  split at success
  · cases except_pure_ok success
    refine ⟨_,rfl,?_,fields.2⟩
    unfold skel XSt.push
    rw [Array.toList_push, List.map_append, List.map_append]
    unfold skel at fields
    rw [fields.1]
    rfl
  · cases success

/-- The exact context assembled after the original first-member checks. -/
def context (protect : Unit → List Lean.Name) (ind? : Name → Option IndView)
    (dedup : Dedup) (groupOf : ExpansionCore.GroupCallback)
    (keyAddr? : Option (Name → Option _root_.Address)) (first : Name) (fi : IndView) :
    ExpansionCore.Ctx :=
  {protect, ind?, dedup, groupOf, keyAddr?, all0 := fi.all[0]?.getD first,
    blockLevels := fi.levelParams.map Ix.Level.mkParam, levelParams := fi.levelParams.toList,
    nParams := fi.numParams, paramBinders := (peelForalls fi.numParams fi.type #[]).1}

/-- Full output/state decomposition of a successful actual generic expansion.
Every callback remains arbitrary. Cache correctness and the operational
allocation history are derived, with no source-representation hypothesis. -/
theorem expand_history {protect : Unit → List Lean.Name} {ind? : Name → Option IndView}
    {dedup : Dedup} {ordered : Array Name} {aliases : Std.HashMap Name Name}
    {groups : ExpansionCore.GroupCallback} {keyAddr? : Option (Name → Option _root_.Address)}
    {x : Expanded}
    (run : ExpansionCore.expand protect ind? dedup ordered aliases groups keyAddr? = .ok x) :
    ∃ (first : Name) (fi : IndView), ordered[0]? = some first ∧ ind? first = some fi ∧
      let cx := context protect ind? dedup groups keyAddr? first fi
      ∃ (initial final : XSt) (events : List (Event cx)),
        initialMembers cx ordered aliases = .ok initial ∧
        ExpansionCore.walkQueue cx expansionBound 0 initial = .ok final ∧
        History cx initial events final ∧
        skel initial = ordered.toList.map (fun n => (n,n)) ∧
        initial.nextAuxIdx = 1 ∧ initial.sourceNames? = none ∧
        initial.allocatedNames = [] ∧ initial.allocatedCtorRoots = [] ∧
        x = {
          types := final.types, auxToNested := final.auxToNested,
          auxCtorMap := final.auxCtorMap, nOriginals := initial.types.size,
          levelParams := fi.levelParams, nParams := fi.numParams,
          all0 := cx.all0, sourceNames := final.sourceNames?.getD []} := by
  unfold ExpansionCore.expand at run
  dsimp only at run
  split at run
  · rename_i first firstFound
    split at run
    · rename_i fi viewFound
      refine ⟨first,fi,firstFound,viewFound,?_⟩
      dsimp only
      obtain ⟨initial,initialRun,run⟩ := except_bind_ok.1 run
      obtain ⟨final,queueRun,run⟩ := except_bind_ok.1 run
      cases except_pure_ok run
      let cx := context protect ind? dedup groups keyAddr? first fi
      have initialized : initialMembers cx ordered aliases = .ok initial := initialRun
      have fields := initialMembers_fields cx ordered aliases initialized
      obtain ⟨events,history⟩ := walkQueue_history cx expansionBound 0 initial final
        (.inl fields.2.2.1) queueRun
      exact ⟨initial,final,events,initialized,queueRun,history,
        fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2,rfl⟩
    · cases run
  · cases run

/-- The history's event at auxiliary index k carries that actual auxiliary's
name/owner and pre-allocation counter. Constructors allocated between events
remain in the full pre-state rather than being discarded from the name input. -/
theorem expand_aux_events {protect : Unit → List Lean.Name} {ind? : Name → Option IndView}
    {dedup : Dedup} {ordered : Array Name} {aliases : Std.HashMap Name Name}
    {groups : ExpansionCore.GroupCallback} {keyAddr? : Option (Name → Option _root_.Address)}
    {x : Expanded}
    (run : ExpansionCore.expand protect ind? dedup ordered aliases groups keyAddr? = .ok x) :
    ∃ (first : Name) (fi : IndView), ordered[0]? = some first ∧ ind? first = some fi ∧
      let cx := context protect ind? dedup groups keyAddr? first fi
      ∃ (initial final : XSt) (events : List (Event cx)),
        initialMembers cx ordered aliases = .ok initial ∧
        ExpansionCore.walkQueue cx expansionBound 0 initial = .ok final ∧
        History cx initial events final ∧
        x = {
          types := final.types, auxToNested := final.auxToNested,
          auxCtorMap := final.auxCtorMap, nOriginals := initial.types.size,
          levelParams := fi.levelParams, nParams := fi.numParams,
          all0 := cx.all0, sourceNames := final.sourceNames?.getD []} ∧
        events.length = x.aux.size ∧
        ∀ (k : Nat) (member : XMember), x.aux[k]? = some member →
          ∃ event, events[k]? = some event ∧ event.name = member.name ∧
            event.owner = member.sourceOwner ∧ event.before.nextAuxIdx = k + 1 := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,events,
    initialRun,queueRun,history,members,counter,empty,allocated,ctorRoots,output⟩ := expand_history run
  cases output
  have shape := history.fields.1
  have size : final.types.size = initial.types.size + events.length := by
    have := congrArg List.length shape
    simpa only [skel_length, List.length_append, List.length_map] using this
  have bound : initial.types.size ≤ final.types.size := by omega
  refine ⟨first,fi,firstFound,viewFound,initial,final,events,
    initialRun,queueRun,history,rfl,?_,?_⟩
  · show events.length = (final.types.extract initial.types.size final.types.size).size
    rw [Array.size_extract, Nat.min_self, size]
    omega
  · intro k member found
    rw [aux_getElem?_eq _ k bound] at found
    have position : (skel final)[initial.types.size + k]? = some (member.name,member.sourceOwner) := by
      rw [skel_getElem?, found]
      rfl
    rw [shape, List.getElem?_append_right (by rw [skel_length]; omega),
      skel_length, Nat.add_sub_cancel_left, List.getElem?_map,
      Option.map_eq_some_iff] at position
    obtain ⟨event,eventFound,matched⟩ := position
    simp only [Prod.mk.injEq] at matched
    refine ⟨event,eventFound,matched.1,matched.2,?_⟩
    rw [history.index k event eventFound, counter]
    omega

end Ix.CompileCert.Canon.ExpansionHistory
