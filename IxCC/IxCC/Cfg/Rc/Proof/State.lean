import IxCC.Cfg.Rc.Proof.Scoped
import IxCC.Cfg.Rc.Proof.Joins
import IxCC.Cfg.Rc.Proof.Frames

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (Below Impl spine)

/-- Reset slots live in `[slotBase, slotBase + slotBound)`, disjoint from source variables `< slotBase`. -/
def SlotSub (slotBase : Nat) (slots : Src.NatMap Own.RVal) (env : Own.Env) : Prop :=
  ∀ s v, slots.get? s = some v → env.get? (slotBase + s) = some v

theorem SlotSub.leaf (slotBase : Nat) (env : Own.Env) : SlotSub slotBase .leaf env :=
  fun _ _ h => by cases h

theorem SlotSub.insert_var {slotBase : Nat} {slots : Src.NatMap Own.RVal} {env : Own.Env}
    (h : SlotSub slotBase slots env) {x : Fir.Var} (hx : x < slotBase) (v : Own.RVal) :
    SlotSub slotBase slots (env.insert x v) := by
  intro s sv hs
  rw [Src.NatMap.get?_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hx (Nat.le_add_right slotBase s)))]
  exact h s sv hs

theorem SlotSub.insert_slot {slotBase : Nat} {slots : Src.NatMap Own.RVal} {env : Own.Env}
    (h : SlotSub slotBase slots env) (s : Nat) (sv : Own.RVal) :
    SlotSub slotBase (slots.insert s sv) (env.insert (slotBase + s) sv) := by
  intro s' sv' hs'
  by_cases eq : s' = s
  · subst eq
    rw [Src.NatMap.get?_insert_self] at hs'
    cases hs'
    exact Src.NatMap.get?_insert_self _ _ _
  · rw [Src.NatMap.get?_insert_ne _ _ eq] at hs'
    rw [Src.NatMap.get?_insert_ne _ _ (by omega : slotBase + s' ≠ slotBase + s)]
    exact h s' sv' hs'

theorem SlotSub.erase {slotBase : Nat} {slots : Src.NatMap Own.RVal} {env : Own.Env}
    (h : SlotSub slotBase slots env) (s : Nat) :
    SlotSub slotBase (slots.erase s) env := by
  intro s' sv' hs'
  have he := Src.NatMap.get?_setF (s + 1) slots s none s' (Nat.lt_succ_self s)
  change (slots.erase s).get? s' = if s' = s then none else slots.get? s' at he
  rw [he] at hs'
  split at hs'
  · cases hs'
  · exact h s' sv' hs'

theorem generate_ctors {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {raw : RawLayout} {P : Program} (h : generate F bodies raw = some P) : P.base.ctors = F.ctors := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    subst P
    rfl

/-- The actual current function, code cursor and real lexical environment.
Marker supply and real-name lower bound are deliberately independent. -/
def At (F : Fir.Program) (P : Program) (fr : Frame) (ρ : Own.Env)
    (saved : List Own.Plain.JEntry) (code : Own.Plain.Code)
    (slots : Src.NatMap Own.RVal := .leaf) : Prop :=
  ∃ (fd : Cfg.Fun) (scope : Cfg.Lower.JScope) (params : List (Fir.Var × Own.PSig))
    (acc : List Instr) (next first lo slotBase : Nat),
    P.base.fun? fr.fn = some fd ∧ fr.fn < F.size ∧
    Impl fd.block? fr.fn scope fr.blk params acc next (skeleton P.base.size first code F.ctors slotBase) ∧
    fr.rest = spine (skeleton P.base.size first code F.ctors slotBase) ∧
    EnvSub ρ fr.env ∧ Below lo ρ ∧ lo ≤ slotBase ∧
    SlotSub slotBase slots fr.env ∧
    names lo code = true ∧ varsBelow slotBase code = true ∧ reuseCtorsOk F.ctors code = true ∧
    Joins P.base.size F.ctors slotBase fd.block? fr.fn fr.env lo scope saved

/-- A checked program derives the exact action table from its actual function
lookup. One successful source action preserves the complete frame invariant,
including all saved join environments and layout witnesses. -/
theorem At.action {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {a : Action} {k : Own.Plain.Code}
    {slots : Src.NatMap Own.RVal}
    (stateRel : At F P fr ρ saved (.act a k) slots)
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap}
    (effect : Own.Plain.evalAction ρ H a = .ok H') :
    ∃ next, step P (.run fr stk H) = .next (.run next stk H') false ∧ At F P next ρ saved k slots := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := stateRel
  obtain ⟨fd', table, lookup', tableLookup, source, body, sourceLookup, bodyLookup,
    lowering, bounds, collected⟩ := checked_entry (checkScopedProgram_parts checked).1 range
  have same : fd' = fd := Option.some.inj (lookup'.symm.trans lookup)
  subst fd'
  have size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have functionCheck : checkFunction P.base.size (source.vars + Own.Plain.slotBound body) fd table = true := by
    apply (checkMarkers_iff ..).mpr
    simpa only [size, same] using collected
  let after : Frame := { fr with rest := spine (skeleton P.base.size (first + 1) k F.ctors slotBase) }
  refine ⟨after, checked_frame_action layout cursor functionCheck tableLookup (evalAction_sub env effect), ?_⟩
  exact ⟨fd, scope, params, marker P.base.size first a :: acc, next, first + 1, lo, slotBase,
    lookup, range, impl_after_action layout, rfl, env, below, loSlot, slotSub,
    scopedNames, vb, rc, joins⟩

theorem At.reset {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {fr : Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {s : Nat} {x : Fir.Var} {ctor : Fir.CtorInfo} {fields : List (Option Fir.Var)} {uniq : Bool}
    {k : Own.Plain.Code} {slots : Src.NatMap Own.RVal}
    (stateRel : At F P fr ρ saved (.reset s x ctor fields uniq k) slots)
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap} {sv : Own.RVal}
    (effect : Own.Plain.evalResetMask ρ H x ctor (Own.Plain.fieldsMask fields) uniq = .ok (sv, H')) :
    ∃ after, step P (.run fr stk H) = .next (.run after stk H') false ∧
      At F P after ρ saved k (slots.insert s sv) := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := stateRel
  simp only [reuseCtorsOk, Bool.and_eq_true, decide_eq_true_eq] at rc
  have hctors : P.base.ctors = F.ctors :=
    generate_ctors (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have hctor : heapCtorAt P.base.ctors (heapCtorIndex F.ctors ctor.key) = some ctor := by
    rw [hctors]; exact heapCtorAt_heapCtorIndex rc.1.1 rc.1.2
  let ins := resetMarker P.base.size (slotBase + s) x (heapCtorIndex F.ctors ctor.key)
    (Own.Plain.fieldsMask fields) uniq
  change Impl fd.block? fr.fn scope fr.blk params (ins :: acc) next
    (skeleton P.base.size first k F.ctors slotBase) at layout
  change fr.rest = ins :: spine (skeleton P.base.size first k F.ctors slotBase) at cursor
  let after : Frame := {
    fr with
    rest := spine (skeleton P.base.size first k F.ctors slotBase)
    env := fr.env.insert (slotBase + s) sv }
  refine ⟨after, step_reset cursor hctor (evalResetMask_sub env effect), ?_⟩
  refine ⟨fd, scope, params, ins :: acc, next, first, lo, slotBase,
    lookup, range, layout, rfl, ?_, below, loSlot, slotSub.insert_slot s sv,
    scopedNames, vb, rc.2, ?_⟩
  · intro y v hy
    have hlt := below y v hy
    rw [Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ slotBase + s)]
    exact env y v hy
  · apply joins.agree
    intro y hy
    exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ slotBase + s)

theorem At.reuse {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {fr : Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {x : Fir.Var} {s : Nat} {ctor : Fir.CtorInfo} {args : List Fir.Arg} {uniq : Bool}
    {k : Own.Plain.Code} {slots : Src.NatMap Own.RVal}
    (stateRel : At F P fr ρ saved (.reuse x s ctor args uniq k) slots)
    {sv : Own.RVal} (hslot : slots.get? s = some sv)
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap} {v : Own.RVal}
    (effect : Own.Plain.evalReuseVal ρ H sv ctor args uniq = .ok (v, H')) :
    ∃ after, step P (.run fr stk H) = .next (.run after stk H') false ∧
      At F P after (ρ.insert x v) saved k (slots.erase s) := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := stateRel
  simp only [names, Bool.and_eq_true, decide_eq_true_eq] at scopedNames
  simp only [varsBelow, Bool.and_eq_true, decide_eq_true_eq] at vb
  simp only [reuseCtorsOk, Bool.and_eq_true, decide_eq_true_eq] at rc
  have hctors : P.base.ctors = F.ctors :=
    generate_ctors (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have hctor : heapCtorAt P.base.ctors (heapCtorIndex F.ctors ctor.key) = some ctor := by
    rw [hctors]; exact heapCtorAt_heapCtorIndex rc.1.1 rc.1.2
  let ins := reuseMarker P.base.size x (slotBase + s) (heapCtorIndex F.ctors ctor.key) uniq args
  change Impl fd.block? fr.fn scope fr.blk params (ins :: acc) next
    (skeleton P.base.size first k F.ctors slotBase) at layout
  change fr.rest = ins :: spine (skeleton P.base.size first k F.ctors slotBase) at cursor
  let after : Frame := {
    fr with
    rest := spine (skeleton P.base.size first k F.ctors slotBase)
    env := fr.env.insert x v }
  refine ⟨after, step_reuse cursor hctor (slotSub s sv hslot) (evalReuseVal_sub env effect), ?_⟩
  refine ⟨fd, scope, params, ins :: acc, next, first, x + 1, slotBase,
    lookup, range, layout, rfl, Cfg.Proof.Sub.insert env x v, ?_, vb.1,
    (slotSub.erase s).insert_var vb.1 v, scopedNames.2, vb.2, rc.2, ?_⟩
  · intro y value hy
    by_cases eq : y = x
    · subst y; exact Nat.lt_succ_self x
    · rw [Src.NatMap.get?_insert_ne _ _ eq] at hy
      exact Nat.lt_of_lt_of_le (below y value hy) (by omega)
  · apply (joins.agree ?_).mono (show lo ≤ x + 1 by omega)
    intro y hy
    exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ x)

theorem At.dropSlot {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {fr : Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {s : Nat} {k : Own.Plain.Code} {slots : Src.NatMap Own.RVal}
    (stateRel : At F P fr ρ saved (.dropSlot s k) slots)
    {sv : Own.RVal} (hslot : slots.get? s = some sv)
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap}
    (effect : Own.Plain.evalDropVal H sv = .ok H') :
    ∃ next, step P (.run fr stk H) = .next (.run next stk H') false ∧
      At F P next ρ saved k (slots.erase s) := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := stateRel
  obtain ⟨fd', table, lookup', tableLookup, source, body, sourceLookup, bodyLookup,
    lowering, bounds, collected⟩ := checked_entry (checkScopedProgram_parts checked).1 range
  have same : fd' = fd := Option.some.inj (lookup'.symm.trans lookup)
  subst fd'
  have size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have functionCheck : checkFunction P.base.size (source.vars + Own.Plain.slotBound body) fd table = true := by
    apply (checkMarkers_iff ..).mpr
    simpa only [size, same] using collected
  have hact : Own.Plain.evalAction fr.env H (.dec (slotBase + s)) = .ok H' := by
    simp only [Own.Plain.evalAction, slotSub s sv hslot]
    exact effect
  let after : Frame := { fr with rest := spine (skeleton P.base.size (first + 1) k F.ctors slotBase) }
  refine ⟨after, checked_frame_dropSlot layout cursor functionCheck tableLookup hact, ?_⟩
  exact ⟨fd, scope, params, marker P.base.size first (.dec (slotBase + s)) :: acc, next, first + 1,
    lo, slotBase, lookup, range, impl_after_dropSlot layout, rfl, env, below, loSlot,
    slotSub.erase s, scopedNames, vb, rc, joins⟩


end IxCC.Cfg.Rc
