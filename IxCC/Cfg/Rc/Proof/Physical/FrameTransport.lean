import IxCC.Cfg.Rc.Proof.Physical.TokenEnvironments
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedDomain
import IxCC.Own.Plain.Proof.ShapeOps

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Successful release changes cell contents, never the logical index range.
This includes stale environment locations and needs no denotation premise. -/
theorem dropAll_size (H : Heap) (pending : List RVal) {H' : Heap}
    (result : dropAll H pending = some H') : H'.size = H.size := by
  match pending with
  | [] =>
    simp only [dropAll] at result
    cases result
    rfl
  | value :: rest =>
    rw [dropAll] at result
    cases step : releaseOne H value rest with
    | none => rw [step] at result; cases result
    | some pair =>
      obtain ⟨next, remaining⟩ := pair
      rw [step] at result
      exact (dropAll_size next remaining result).trans (releaseOne_size step)
termination_by (mass H, pending.length)
decreasing_by
  have decrease := Prod.lex_def.mp (releaseOne_decreases step)
  apply Prod.lex_def.mpr
  rcases decrease with decrease | ⟨equal, decrease⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨equal, by omega⟩

theorem action_size {H H' : Heap} {ρ : Own.Env} {action : Action}
    (result : Own.Plain.evalAction ρ H action = .ok H') : H'.size = H.size := by
  cases action with
  | inc x n =>
    cases lookup : ρ.get? x with
    | none => simp [Own.Plain.evalAction, lookup] at result
    | some value =>
      cases operation : inc H value n with
      | none => simp [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption] at result
      | some after =>
        simp only [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption, Sem.Result.ok.injEq] at result
        subst H'
        exact (changeCount_sameBodies operation).1.symm
  | dec x =>
    cases lookup : ρ.get? x with
    | none => simp [Own.Plain.evalAction, lookup] at result
    | some value =>
      cases operation : dropAll H [value] with
      | none => simp [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption] at result
      | some after =>
        simp only [Own.Plain.evalAction, lookup, operation, Sem.Result.ofOption, Sem.Result.ok.injEq] at result
        subst H'
        exact dropAll_size H [value] operation

theorem actions_size {H H' : Heap} {ρ : Own.Env} {actions : List Action}
    (result : Own.Plain.evalActions ρ H actions = .ok H') : H'.size = H.size := by
  induction actions generalizing H with
  | nil => cases result; rfl
  | cons action actions ih =>
    cases step : Own.Plain.evalAction ρ H action with
    | ok next =>
      have tail : Own.Plain.evalActions ρ next actions = .ok H' := by
        simpa only [Own.Plain.evalActions, step, Sem.Result.bind_ok] using result
      exact (ih tail).trans (action_size step)
    | timeout | resource _ | trap | stuck =>
      simp [Own.Plain.evalActions, step, Sem.Result.bind] at result

/-- Apply to the exact caller register insertion returned by an inc/dec
trace. The source map may contain stale bindings outside lexical ownership. -/
theorem frame_marker_transport {H H' : Heap} {ρ : Own.Env} {action : Action}
    (result : Own.Plain.evalAction ρ H action = .ok H')
    {addresses : AddressMap} {D : Nat → Prop} {bound dummy : Nat}
    {source : Own.Env} {target : Lir.Env}
    (words : FusedWords addresses D bound source target)
    (bounded : Own.Plain.EnvBounded H.size source)
    (absent : source.get? dummy = none) (word : Lir.Word) :
    FusedWords addresses D bound source (target.insert dummy word) ∧
      Own.Plain.EnvBounded H'.size source :=
  ⟨words.marker_fresh absent word, by rw [action_size result]; exact bounded⟩

/-- Publication extends the complete actual source frame, including inactive
bindings. Only old index bounds are used; stale roots need not remain live. -/
theorem frame_allocation_transport {H : Heap} {body : Own.Body}
    {allocated : Own.RVal × Own.Heap} (result : H.alloc .rc body = allocated)
    {addresses : AddressMap} {D : Nat → Prop} {bound x : Nat}
    {source : Own.Env} {target : Lir.Env}
    (words : FusedWords addresses D bound source target)
    (bounded : Own.Plain.EnvBounded H.size source) (real : x < bound) (address : Lir.Word) :
    FusedWords (placeFresh addresses H.size address) D bound
      (source.insert x allocated.1) (target.insert x address) ∧
    Own.Plain.EnvBounded allocated.2.size (source.insert x allocated.1) := by
  subst allocated
  have size : (H.alloc .rc body).2.size = H.size + 1 := by simp [Own.Heap.alloc, Own.Heap.size]
  refine ⟨words.publish real bounded address, ?_⟩
  rw [size]
  apply (bounded.mono (by omega : H.size ≤ H.size+1)).insert x
  change H.size < H.size + 1
  omega





end IxCC.Cfg.Rc.Native
