import Ix.CompileCert.Opt.O11aFields

/-!
F-1: finite source peeling, recursive-field origins, and the actual O11a
field-prefix count. This proof-only leaf is UNCOMPILED. It changes no runtime
helper, callback, error or output. The finite peeler preserves protection even
on failure. Field indices come from the actual declaration array, independently
of every target-reader answer, and successful binder prefixes supply their own
field-array size.

Growth through auxMotiveSigsWith/findSourceRecTargetWith's unbounded telescope
loops, the complete source-preparation protection chain, callback conversion,
final abstraction and the original general O2/O11a endpoints remain open.
-/

namespace Ix.CompileCert.Opt.O11aSourceBounds

open Ix (Name Level Expr RecursorVal)
open Ix.AuxGen (FreshFVars LocalDecl SourceRecTarget AuxMotiveSig)
open Ix.Compile.Pass.Opt
open Ix.CompileCert.Canon (except_bind_ok)
open Ix.CompileCert.Opt.FreshFVarsProof
open Ix.CompileCert.Opt.O11aFields

def Grows (before after : FreshFVars) : Prop :=
  ∀ key, key ∈ before.used → key ∈ after.used

theorem grows_refl (supply : FreshFVars) : Grows supply supply := fun _ h => h

theorem grows_trans {a b c : FreshFVars} (ab : Grows a b) (bc : Grows b c) :
    Grows a c := fun key h => bc key (ab key h)

/-- The actual early-return slot and mutable-variable declaration order. -/
abbrev PeelResult := Array LocalDecl × Array Expr × Expr
abbrev PeelState := Option (Option PeelResult) × Expr × Array LocalDecl × Array Expr

def peelStep (pfx : String) (offset i : Nat) (state : PeelState) :
    StateM FreshFVars (ForInStep PeelState) := fun supply =>
  let (_, cur, decls, fvars) := state
  match cur with
  | .forallE name dom body info _ =>
      let made := supply.fresh pfx (offset + i)
      let decl : LocalDecl := { fvarName := made.1.1, binderName := name,
        domain := Ix.AuxGen.consumeTypeAnnotations dom, info := info }
      (.yield (none, Ix.AuxGen.instantiate1 body made.1.2,
        decls.push decl, fvars.push made.1.2), made.2)
  | _ => (.done (some none, cur, decls, fvars), supply)

def peelFinish (state : PeelState) : Option PeelResult :=
  match state.1 with
  | some result => result
  | none => some (state.2.2.1, state.2.2.2, state.2.1)

def peelWith (cur : Expr) (count : Nat) (pfx : String) (offset : Nat) :
    StateM FreshFVars (Option PeelResult) := do
  modify (·.protectExpr cur)
  let state ← forIn [0:count] (none, cur, #[], #[]) (peelStep pfx offset)
  return peelFinish state

/-- Whole StateM equality, including the supply retained by an early refusal. -/
theorem peelBindersWith_eq (cur : Expr) (count : Nat) (pfx : String) (offset : Nat) :
    Ix.AuxGen.peelBindersWith cur count pfx offset = peelWith cur count pfx offset := by
  unfold Ix.AuxGen.peelBindersWith peelWith peelStep peelFinish Ix.AuxGen.freshFVarM
  rfl

theorem state_forIn_cons {α σ τ : Type} (body : α → τ → StateM σ (ForInStep τ))
    (x : α) (xs : List α) (state : τ) (supply : σ) :
    (forIn (x :: xs) state body).run supply =
      let answer := (body x state).run supply
      match answer.1 with
      | .done out => (out, answer.2)
      | .yield out => (forIn xs out body).run answer.2 := by
  rw [List.forIn_cons]
  rfl

theorem state_forIn_grows {α τ : Type}
    (body : α → τ → StateM FreshFVars (ForInStep τ))
    (step : ∀ x state supply, Grows supply ((body x state).run supply).2) :
    ∀ (xs : List α) (state : τ) (supply : FreshFVars),
      Grows supply ((forIn xs state body).run supply).2
  | [], _, supply => grows_refl supply
  | x :: xs, state, supply => by
      rw [state_forIn_cons]
      have grow := step x state supply
      generalize (body x state).run supply = answer at grow ⊢
      rcases answer with ⟨out, nextSupply⟩
      cases out with
      | done out => exact grow
      | yield out => exact grows_trans grow (state_forIn_grows body step xs out nextSupply)

theorem peelStep_grows (pfx : String) (offset i : Nat) (state : PeelState)
    (supply : FreshFVars) : Grows supply ((peelStep pfx offset i state).run supply).2 := by
  rcases state with ⟨flag, cur, decls, fvars⟩
  cases cur with
  | forallE name dom body info hash => exact fresh_grows supply pfx (offset + i)
  | _ => exact grows_refl supply

/-- The peeler never drops a protected name, whether it returns some or none. -/
theorem peelBindersWith_grows (cur : Expr) (count : Nat) (pfx : String)
    (offset : Nat) (supply : FreshFVars) :
    Grows supply ((Ix.AuxGen.peelBindersWith cur count pfx offset).run supply).2 := by
  rw [peelBindersWith_eq]
  change Grows supply ((forIn [0:count] (none, cur, #[], #[])
    (peelStep pfx offset)).run (supply.protectExpr cur)).2
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact grows_trans (protectExpr_grows supply cur)
    (state_forIn_grows _ (peelStep_grows pfx offset) _ _ _)

theorem peelBindersWith_protects (cur : Expr) (count : Nat) (pfx : String)
    (offset : Nat) (supply : FreshFVars) :
    Protects ((Ix.AuxGen.peelBindersWith cur count pfx offset).run supply).2 cur := by
  rw [peelBindersWith_eq]
  change Protects ((forIn [0:count] (none, cur, #[], #[])
    (peelStep pfx offset)).run (supply.protectExpr cur)).2 cur
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact protects_mono _ _ cur
    (state_forIn_grows _ (peelStep_grows pfx offset) _ _ _)
    (protectExpr_protects supply cur)

theorem peelStep_count (pfx : String) (offset i : Nat) (state : PeelState)
    (supply : FreshFVars) :
    ((peelStep pfx offset i state).run supply).1 =
        .done (some none, state.2.1, state.2.2.1, state.2.2.2) ∨
      ∃ next, ((peelStep pfx offset i state).run supply).1 = .yield next ∧
        next.1 = none ∧ next.2.2.1.size = state.2.2.1.size + 1 ∧
        next.2.2.2.size = state.2.2.2.size + 1 := by
  rcases state with ⟨flag, cur, decls, fvars⟩
  cases cur with
  | forallE name dom body info hash =>
      exact .inr ⟨_, rfl, rfl, Array.size_push _, Array.size_push _⟩
  | _ => exact .inl rfl

theorem peelLoop_count (pfx : String) (offset : Nat) :
    ∀ (xs : List Nat) (state : PeelState) (supply : FreshFVars)
      (out : PeelState) (finalSupply : FreshFVars), state.1 = none →
      (forIn xs state (peelStep pfx offset)).run supply = (out, finalSupply) →
      out.1 = some none ∨
        (out.1 = none ∧ out.2.2.1.size = state.2.2.1.size + xs.length ∧
          out.2.2.2.size = state.2.2.2.size + xs.length)
  | [], state, supply, out, finalSupply, active, run => by
      change (state, supply) = (out, finalSupply) at run
      cases run
      exact .inr ⟨active, by simp, by simp⟩
  | i :: xs, state, supply, out, finalSupply, _, run => by
      rw [state_forIn_cons] at run
      have shape := peelStep_count pfx offset i state supply
      generalize observed : (peelStep pfx offset i state).run supply = answer at shape run
      rcases answer with ⟨step, nextSupply⟩
      rcases shape with failed | ⟨next, continued, active, declCount, fieldCount⟩
      · subst step
        cases run
        exact .inl rfl
      · subst step
        have tail := peelLoop_count pfx offset xs next nextSupply out finalSupply active run
        rcases tail with failed | ⟨active, decls, fields⟩
        · exact .inl failed
        · exact .inr ⟨active, by simp only [List.length_cons]; omega,
            by simp only [List.length_cons]; omega⟩

/-- A successful actual peel yields exactly the requested number of fields.
No well-formedness, closed-input or callback assumption is needed. -/
theorem peelBindersWith_count (cur : Expr) (count : Nat) (pfx : String) (offset : Nat)
    (supply finalSupply : FreshFVars) (decls : Array LocalDecl) (fields : Array Expr)
    (body : Expr)
    (run : (Ix.AuxGen.peelBindersWith cur count pfx offset).run supply =
      (some (decls, fields, body), finalSupply)) :
    decls.size = count ∧ fields.size = count := by
  rw [peelBindersWith_eq] at run
  change (peelFinish ((forIn [0:count] (none, cur, #[], #[])
      (peelStep pfx offset)).run (supply.protectExpr cur)).1,
      ((forIn [0:count] (none, cur, #[], #[])
      (peelStep pfx offset)).run (supply.protectExpr cur)).2) = _ at run
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at run
  generalize observed : (forIn (List.range' 0 count) (none, cur, #[], #[])
    (peelStep pfx offset)).run (supply.protectExpr cur) = answer at run
  rcases answer with ⟨state, nextSupply⟩
  have counts := peelLoop_count pfx offset (List.range' 0 count)
    (none, cur, #[], #[]) (supply.protectExpr cur) state nextSupply rfl observed
  rcases counts with failed | ⟨active, declCount, fieldCount⟩
  · have impossible : (none : Option PeelResult) = some (decls, fields, body) := by
      simpa only [peelFinish, failed] using congrArg Prod.fst run
    cases impossible
  · simp only [peelFinish, active] at run
    have equal := Option.some.inj (congrArg Prod.fst run)
    have counts : state.2.2.1.size = count ∧ state.2.2.2.size = count := by
      simpa only [List.length_range', Array.size_empty, Nat.zero_add] using
        And.intro declCount fieldCount
    exact ⟨(congrArg (fun result : PeelResult => result.1.size) equal).symm.trans counts.1,
      (congrArg (fun result : PeelResult => result.2.1.size) equal).symm.trans counts.2⟩

/-- The source collector's callback is unrestricted, including its returned
supply. Only the caller's actual zipIdx index is inserted. -/
abbrev TargetRead := LocalDecl → Nat → FreshFVars → Option SourceRecTarget × FreshFVars
abbrev TargetState := FreshFVars × Array (Nat × SourceRecTarget)

def targetStep (readTarget : TargetRead) (entry : LocalDecl × Nat)
    (state : TargetState) : O11aM (ForInStep TargetState) :=
  let answer := readTarget entry.1 entry.2 state.1
  match answer.1 with
  | none => .ok (.yield (answer.2, state.2))
  | some target => .ok (.yield (answer.2, state.2.push (entry.2, target)))

def collectTargets (readTarget : TargetRead) (decls : Array LocalDecl)
    (supply : FreshFVars) : O11aM TargetState :=
  forIn decls.zipIdx (supply, #[]) (targetStep readTarget)

def actualTargetRead (rv : RecursorVal) (ps : Array Expr) (env : Ix.Environment)
    (auxSigs : Array AuxMotiveSig) : TargetRead := fun decl index supply =>
  (Ix.AuxGen.findSourceRecTargetWith decl.domain rv.all ps env
    "split_xs" index auxSigs).run supply

/-- Literal source loop, with its complete returned supply and target array. -/
theorem collectTargets_eq_loop (readTarget : TargetRead) (decls : Array LocalDecl)
    (initial : FreshFVars) : collectTargets readTarget decls initial = (do
      let mut supply := initial
      let mut recFields : Array (Nat × SourceRecTarget) := #[]
      for (decl, fieldIdx) in decls.zipIdx do
        let (target?, nextSupply) := readTarget decl fieldIdx supply
        supply := nextSupply
        if let some target := target? then
          recFields := recFields.push (fieldIdx, target)
      return (supply, recFields) : O11aM TargetState) := by
  unfold collectTargets targetStep
  simp only [bind_pure]

theorem collectTargets_origin (readTarget : TargetRead) (decls : Array LocalDecl)
    (supply : FreshFVars) (out : TargetState)
    (run : collectTargets readTarget decls supply = .ok out) :
    ∀ entry ∈ out.2, ∃ decl, decls[entry.1]? = some decl := by
  unfold collectTargets at run
  refine Ix.CompileCert.Canon.forIn_except_array_mem (targetStep readTarget)
    (fun _ state => ∀ entry ∈ state.2, ∃ decl, decls[entry.1]? = some decl)
    decls.zipIdx ?_ (by simp) run
  rintro preRun ⟨decl, index⟩ ⟨current, entries⟩ step member valid succeeded
  have found := Array.mk_mem_zipIdx_iff_getElem?.1 (Array.mem_toList_iff.1 member)
  unfold targetStep at succeeded
  generalize readTarget decl index current = answer at succeeded
  rcases answer with ⟨target, nextSupply⟩
  cases target with
  | none =>
      cases succeeded
      exact ⟨_, rfl, valid⟩
  | some target =>
      cases succeeded
      refine ⟨_, rfl, ?_⟩
      intro entry member
      rcases Array.mem_push.1 member with old | rfl
      · exact valid entry old
      · exact ⟨decl, found⟩

theorem collectTargets_bound (readTarget : TargetRead) (decls : Array LocalDecl)
    (supply : FreshFVars) (out : TargetState)
    (run : collectTargets readTarget decls supply = .ok out) :
    ∀ entry ∈ out.2, entry.1 < decls.size := by
  intro entry member
  obtain ⟨decl, found⟩ := collectTargets_origin readTarget decls supply out run entry member
  exact (Array.getElem?_eq_some_iff.1 found).1

/-- The actual source-preparation fragment from the field peel through target
collection. The caller's constructor/minor reads and their failures are outside
this fragment, while the original peeler refusal is preserved exactly. -/
def prepareFields (minorTy : Expr) (numFields : Nat) (supply : FreshFVars)
    (readTarget : TargetRead) (unread : String) : O11aM TargetState := do
  let (fields?, supply) :=
    (Ix.AuxGen.peelBindersWith minorTy numFields "split_field" 0).run supply
  let (decls, _, _) ← O11aM.side fields? unread
  collectTargets readTarget decls supply

/-- The source fragment before any binder/callback work, with every original
Option refusal and the full target-collection result intact. -/
theorem prepareFields_eq_sourceLoop (minorTy : Expr) (numFields : Nat)
    (initial : FreshFVars) (rv : RecursorVal) (ps : Array Expr)
    (env : Ix.Environment) (auxSigs : Array AuxMotiveSig) (unread : String) :
    prepareFields minorTy numFields initial (actualTargetRead rv ps env auxSigs) unread = (do
      let (fields?, supply) :=
        (Ix.AuxGen.peelBindersWith minorTy numFields "split_field" 0).run initial
      let (fieldDecls, _, _) ← O11aM.side fields? unread
      let mut supply := supply
      let mut recFields : Array (Nat × SourceRecTarget) := #[]
      for (decl, fieldIdx) in fieldDecls.zipIdx do
        let (target?, nextSupply) := (Ix.AuxGen.findSourceRecTargetWith decl.domain rv.all
          ps env "split_xs" fieldIdx auxSigs).run supply
        supply := nextSupply
        if let some target := target? then
          recFields := recFields.push (fieldIdx, target)
      return (supply, recFields) : O11aM TargetState) := by
  simp only [prepareFields, collectTargets_eq_loop, actualTargetRead]

/-- The actual public helper with just its source-preparation fragment named.
No source read, callback, error, optional absence or raw result is discarded. -/
def minorPrepared (env : OptEnv) (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) : O11aM (Option Expr) := do
  let initial := (FreshFVars.protectExpr {} rv.cnst.type).protectExprs (ps ++ ms ++ mins)
  let (auxSigs, supply) := (Ix.AuxGen.auxMotiveSigsWith rv us ps ms env.ienv).run initial
  let unread := s!"the constructor and minor type of minor {j} cannot be read"
  let (_, ctor) ← O11aM.side (Ix.AuxGen.sourceCtorForMinor j rv env.ienv auxSigs) unread
  let minorTy ← O11aM.side (Ix.AuxGen.sourceMinorType rv us ps ms mins j) unread
  let prepared ← prepareFields minorTy ctor.numFields supply
    (actualTargetRead rv ps env.ienv auxSigs) unread
  if !prepared.2.any (fun (_, target) => !(inBlock.getD target.sourcePos false)) then
    return none
  let minor ← O11aM.side mins[j]? unread
  let out ← binderLoopWith rawFieldRead inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
    ctor.numFields j unread (ctor.numFields + prepared.2.size) prepared.1 minor
  return some (Ix.AuxGen.mkLambda out.2.1 out.2.2.1)

theorem sizeOfMinorWith_eq_prepared (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) :
    sizeOfMinorWith env inst? rv inBlock us ps ms mins j =
      minorPrepared env inst? rv inBlock us ps ms mins j := by
  rw [sizeOfMinorWith_eq_raw]
  unfold minorWithReader minorPrepared
  simp only [prepareFields_eq_sourceLoop, bind_assoc, pure_bind]

theorem prepareFields_bound (minorTy : Expr) (numFields : Nat) (supply : FreshFVars)
    (readTarget : TargetRead) (unread : String) (out : TargetState)
    (run : prepareFields minorTy numFields supply readTarget unread = .ok out) :
    ∀ entry ∈ out.2, entry.1 < numFields := by
  unfold prepareFields at run
  generalize peeled : (Ix.AuxGen.peelBindersWith minorTy numFields "split_field" 0).run
    supply = answer at run
  rcases answer with ⟨fields, nextSupply⟩
  obtain ⟨parts, read, collected⟩ := except_bind_ok.1 run
  rcases parts with ⟨decls, fvars, body⟩
  have found := side_ok read
  have peeled' := peeled
  rw [found] at peeled'
  have count := (peelBindersWith_count minorTy numFields "split_field" 0 supply
    nextSupply decls fvars body peeled').1
  simpa only [count] using collectTargets_bound readTarget decls nextSupply out collected

/-- Growth and field count of each actual successful O11a body step. These
facts do not require BinderInv or any property of the arbitrary callback. -/
theorem binderStep_count_grows (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String) (i : Nat)
    (state : BinderState) (out : ForInStep BinderState)
    (run : binderStepWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread i state = .ok out) :
    ∃ next, out = .yield next ∧ Grows state.1 next.1 ∧
      next.2.2.2.size = state.2.2.2.size + if i < numFields then 1 else 0 := by
  rcases state with ⟨supply, cur, decls, fvars⟩
  unfold binderStepWith at run
  obtain ⟨parts, _, run⟩ := except_bind_ok.1 run
  rcases parts with ⟨name, dom, body, info⟩
  dsimp only at run
  split at run
  · rename_i isField
    cases run
    refine ⟨_, rfl, fresh_grows supply "o11a" i, ?_⟩
    simp only [isField, ↓reduceIte, Array.size_push]
  · rename_i isIH
    dsimp only at run
    split at run
    · cases run
      refine ⟨_, rfl, fresh_grows supply "o11a" i, ?_⟩
      simp only [isIH, ↓reduceIte, Nat.add_zero]
    · obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨_, _, run⟩ := except_bind_ok.1 run
      obtain ⟨answer, _, run⟩ := except_bind_ok.1 run
      rcases answer with ⟨inst, level⟩
      obtain ⟨field, _, run⟩ := except_bind_ok.1 run
      cases run
      refine ⟨_, rfl, fresh_grows supply "o11a" i, ?_⟩
      simp only [isIH, ↓reduceIte, Nat.add_zero]

theorem binderRange_count (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String) :
    ∀ (count start : Nat) (state out : BinderState),
      state.2.2.2.size = min start numFields →
      forIn (List.range' start count) state (binderStepWith rawFieldRead inst? rv inBlock
        recFields telescope numFields j unread) = .ok out →
      out.2.2.2.size = min (start + count) numFields
  | 0, start, state, out, size, run => by
      change Except.ok state = Except.ok out at run
      cases run
      simpa only [Nat.add_zero] using size
  | count + 1, start, state, out, size, run => by
      rw [List.range'_succ, List.forIn_cons] at run
      obtain ⟨step, succeeded, run⟩ := except_bind_ok.1 run
      obtain ⟨next, rfl, _, countStep⟩ := binderStep_count_grows inst? rv inBlock
        recFields telescope numFields j unread start state step succeeded
      have sizeNext : next.2.2.2.size = min (start + 1) numFields := by
        by_cases field : start < numFields
        · simp only [field, ↓reduceIte] at countStep
          omega
        · simp only [field, ↓reduceIte, Nat.add_zero] at countStep
          omega
      simpa only [Nat.add_assoc, Nat.add_comm 1 count] using
        binderRange_count inst? rv inBlock recFields telescope numFields j unread
          count (start + 1) next out sizeNext run

theorem binderLoop_count (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out) :
    out.2.2.2.size = min count numFields := by
  unfold binderLoopWith at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at run
  simpa only [Nat.zero_add] using
    binderRange_count inst? rv inBlock recFields telescope numFields j unread
      count 0 (supply, minor, #[], #[]) out (by simp) run

theorem binderLoop_grows (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (recFields : Array (Nat × SourceRecTarget))
    (telescope : Array Expr) (numFields j : Nat) (unread : String)
    (count : Nat) (supply : FreshFVars) (minor : Expr) (out : BinderState)
    (run : binderLoopWith rawFieldRead inst? rv inBlock recFields telescope
      numFields j unread count supply minor = .ok out) : Grows supply out.1 := by
  unfold binderLoopWith at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  refine Ix.CompileCert.Canon.forIn_except_list _
    (fun _ state => Grows supply state.1) ?_ _ [] _ out (grows_refl supply) run
  intro preRun i state step valid succeeded
  obtain ⟨next, rfl, grow, _⟩ := binderStep_count_grows inst? rv inBlock recFields
    telescope numFields j unread i state step succeeded
  exact ⟨next, rfl, grows_trans valid grow⟩

/-- A successful actual field peel and source target collection discharge
the field lookup bound at every successful IH prefix. No index/count/freshness
premise is imposed on a final compiler caller. -/
theorem prepared_prefix_field (minorTy : Expr) (numFields : Nat) (initial : FreshFVars)
    (readTarget : TargetRead) (unread : String) (prepared : TargetState)
    (prepareRun : prepareFields minorTy numFields initial readTarget unread = .ok prepared)
    (inst? : Name → Array Expr → O11aM (Name × Level)) (rv : RecursorVal)
    (inBlock : Array Bool) (telescope : Array Expr) (j count : Nat) (minor : Expr)
    (out : BinderState)
    (prefixRun : binderLoopWith rawFieldRead inst? rv inBlock prepared.2 telescope
      numFields j unread count prepared.1 minor = .ok out)
    (isIH : numFields ≤ count) (inLoop : count < numFields + prepared.2.size) :
    ∃ field, rawFieldRead out.2.2.2 (prepared.2[count - numFields]!).1 unread = .ok field ∧
      IsFieldFVar field ∧ Protects out.1 field := by
  have slot : count - numFields < prepared.2.size := by omega
  have member : prepared.2[count - numFields]! ∈ prepared.2 := by
    rw [getElem!_pos _ _ slot]
    exact Array.getElem_mem _
  have indexBound := prepareFields_bound minorTy numFields initial readTarget unread
    prepared prepareRun _ member
  have fieldCount := binderLoop_count inst? rv inBlock prepared.2 telescope
    numFields j unread count prepared.1 minor out prefixRun
  have validIndex : (prepared.2[count - numFields]!).1 < out.2.2.2.size := by omega
  let field := out.2.2.2[(prepared.2[count - numFields]!).1]'validIndex
  have found : out.2.2.2[(prepared.2[count - numFields]!).1]? = some field :=
    Array.getElem?_eq_getElem validIndex
  have fieldShape := binderLoop_field_access inst? rv inBlock prepared.2 telescope
    numFields j unread count prepared.1 minor out prefixRun _ field found
  exact ⟨field, by simp only [rawFieldRead, found, O11aM.side], fieldShape⟩

/-- The successful public helper itself supplies the preparation and loop
witnesses. This is a success projection of the complete Except equality above;
it does not turn source-read or callback success into a final-domain premise. -/
theorem sizeOfMinorWith_success_fields (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) (output : Expr)
    (run : sizeOfMinorWith env inst? rv inBlock us ps ms mins j = .ok (some output)) :
    let initial := (FreshFVars.protectExpr {} rv.cnst.type).protectExprs (ps ++ ms ++ mins)
    let aux := (Ix.AuxGen.auxMotiveSigsWith rv us ps ms env.ienv).run initial
    let unread := s!"the constructor and minor type of minor {j} cannot be read"
    ∃ (sourcePos : Nat) (ctor : Ix.ConstructorVal) (minorTy : Expr)
      (prepared : TargetState) (minor : Expr) (opened : BinderState),
      Ix.AuxGen.sourceCtorForMinor j rv env.ienv aux.1 = some (sourcePos, ctor) ∧
      Ix.AuxGen.sourceMinorType rv us ps ms mins j = some minorTy ∧
      prepareFields minorTy ctor.numFields aux.2
        (actualTargetRead rv ps env.ienv aux.1) unread = .ok prepared ∧
      mins[j]? = some minor ∧
      binderLoopWith rawFieldRead inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
        ctor.numFields j unread (ctor.numFields + prepared.2.size) prepared.1 minor = .ok opened ∧
      opened.2.2.2.size = ctor.numFields ∧
      (∀ entry ∈ prepared.2, entry.1 < ctor.numFields) ∧
      output = Ix.AuxGen.mkLambda opened.2.1 opened.2.2.1 := by
  dsimp only
  rw [sizeOfMinorWith_eq_prepared] at run
  unfold minorPrepared at run
  obtain ⟨sourceCtor, sourceRead, run⟩ := except_bind_ok.1 run
  rcases sourceCtor with ⟨sourcePos, ctor⟩
  obtain ⟨minorTy, typeRead, run⟩ := except_bind_ok.1 run
  obtain ⟨prepared, prepareRun, run⟩ := except_bind_ok.1 run
  split at run
  · cases run
  · obtain ⟨minor, minorRead, run⟩ := except_bind_ok.1 run
    obtain ⟨opened, loopRun, run⟩ := except_bind_ok.1 run
    refine ⟨sourcePos, ctor, minorTy, prepared, minor, opened,
      side_ok sourceRead, side_ok typeRead, prepareRun, side_ok minorRead, loopRun, ?_,
      prepareFields_bound _ _ _ _ _ _ prepareRun, ?_⟩
    · have count := binderLoop_count inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
        ctor.numFields j _ (ctor.numFields + prepared.2.size) prepared.1 minor opened loopRun
      omega
    · exact (Option.some.inj (Except.ok.inj run)).symm

/-- Out-of-range forged tables are still rejected; the bound above is derived
from the actual preparation, not asserted for arbitrary manufactured arrays. -/
theorem out_of_range_field_refusal (fields : Array Expr) (index : Nat) (cause : String)
    (outside : fields.size ≤ index) : rawFieldRead fields index cause = .error (some cause) := by
  simp only [rawFieldRead, Array.getElem?_eq_none outside, O11aM.side]

/-- A zero-length peel succeeds on any raw expression and still protects it. -/
theorem zero_peel_neighbour (cur : Expr) (pfx : String) (offset : Nat) (supply : FreshFVars) :
    (Ix.AuxGen.peelBindersWith cur 0 pfx offset).run supply =
      (some (#[], #[], cur), supply.protectExpr cur) := by
  rw [peelBindersWith_eq]
  rfl

/-- Requesting a binder from an open FVar refuses, retaining protection of
that input; the zero-peel neighbour above succeeds on the same expression. -/
theorem open_fvar_peel_refusal (name : Name) (hash : _root_.Address)
    (pfx : String) (offset : Nat) (supply : FreshFVars) :
    (Ix.AuxGen.peelBindersWith (.fvar name hash) 1 pfx offset).run supply =
      (none, supply.protectExpr (.fvar name hash)) := by
  rw [peelBindersWith_eq]
  rfl

end Ix.CompileCert.Opt.O11aSourceBounds
