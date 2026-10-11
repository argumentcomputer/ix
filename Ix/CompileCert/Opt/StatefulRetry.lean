import Ix.CompileCert.Opt.Engine
import Init.Data.Array.Lemmas
import Init.Data.List.Monadic

-- V10 proof-body proposal only; V9 is RED and no successor gate is included.
/-!
UNCOMPILED candidate against ce9cb85bb688e94f74877c86acde6c3ca1fc2c52.

F14: the actual production engine's retry without a site is empty after
a proof-justified hit. This is a control-flow statement for arbitrary
OptEnv, names, levels and arguments. It assumes no EngineLaws, hash law,
freshness, closedness, source validity, or successful image construction.
It does not yet prove the stateful Translate.rw simulation.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Pass.Opt

/-- Any full-engine result with no site is definitional, and the same
result occurs at every site. The emitting passes cannot fire without one. -/
theorem engineFull_siteFree_lift {env : OptEnv} {n : Name}
    {us : Array Level} {args : Array Expr} {nm : String}
    {e : Expr} {cs : Array ConstantInfo}
    (h : engineFull env ⟨n, us, args, none⟩ = some (nm, e, cs)) :
    isProofJustified nm = false ∧
      ∀ site, engineFull env ⟨n, us, args, site⟩ = some (nm, e, cs) := by
  have hs : (⟨n, us, args, none⟩ : Occ).site = none := rfl
  obtain ⟨-, -, h9, h10, h12⟩ := pj_site_none (env := env) hs
  rcases engineFull_cases h with
    ⟨he, rfl⟩ | ⟨-, ⟨-, hp⟩ | ⟨-, hp⟩ | ⟨-, hp⟩⟩
  · have hdef := engineN_site_none hs he
    refine ⟨hdef, ?_⟩
    intro site
    have he' := (engineN_site_iff (s := site) hdef).2 he
    unfold engineFull engine
    rw [he']
  · rw [h9] at hp
    cases hp
  · rw [h10] at hp
    cases hp
  · rw [h12] at hp
    cases hp

/-- A proof-justified result rules out every result without a site.
This includes O7/O8 and the O9/O10/O12 emitting branch of engineFull. -/
theorem engineFull_pj_retry_none {env : OptEnv} {site : Option Name}
    {n : Name} {us : Array Level} {args : Array Expr} {nm : String}
    {e : Expr} {cs : Array ConstantInfo}
    (hit : engineFull env ⟨n, us, args, site⟩ = some (nm, e, cs))
    (hpj : isProofJustified nm = true) :
    engineFull env ⟨n, us, args, none⟩ = none := by
  cases retry : engineFull env ⟨n, us, args, none⟩ with
  | none => rfl
  | some result =>
    exfalso
    obtain ⟨nm', e', cs'⟩ := result
    obtain ⟨hdef, same⟩ := engineFull_siteFree_lift retry
    have pairEq := Option.some.inj (hit.symm.trans (same site))
    have nameEq : nm = nm' := congrArg (fun x : String × Expr × Array ConstantInfo => x.1) pairEq
    have hfalse : isProofJustified nm = false := by
      rw [nameEq]
      exact hdef
    rw [hpj] at hfalse
    cases hfalse

/-- The engine-backed callback, at arbitrary arguments: a tagged result
implies that its retry with site = none returns none. -/
theorem hookOf_pj_retry_none {env : OptEnv} {site : Option Name}
    {n : Name} {us : Array Level} {args : Array Expr}
    {e : Expr} {cs : Array ConstantInfo} {pass : String}
    (hit : hookOf env site n us args = some (e, cs, some pass)) :
    hookOf env none n us args = none := by
  unfold hookOf at hit ⊢
  split at hit <;> rename_i allowed
  · contradiction
  rw [ite_eq_right allowed]
  obtain ⟨⟨nm, e', cs'⟩, fullHit, mapped⟩ := omap_some hit
  have tagEq := congrArg
    (fun x : Expr × Array ConstantInfo × Option String => x.2.2) mapped
  change (if isProofJustified nm then some nm else none) = some pass at tagEq
  have hpj : isProofJustified nm = true := by
    cases hp : isProofJustified nm with
    | false =>
      rw [hp] at tagEq
      cases tagEq
    | true => rfl
  rw [engineFull_pj_retry_none fullHit hpj]
  rfl

/-- The exact callback installed by Driver.prepareBlock satisfies the
empty-retry fact for every CompileEnv and block table. -/
theorem optLookup_pj_retry_none (cenv : Ix.CompileM.CompileEnv)
    (blocks : Std.HashMap Name OptBlock) {site : Option Name}
    {n : Name} {us : Array Level} {args : Array Expr}
    {e : Expr} {cs : Array ConstantInfo} {pass : String}
    (hit : Ix.Compile.Pass.optLookup cenv blocks site n us args = some (e, cs, some pass)) :
    Ix.Compile.Pass.optLookup cenv blocks none n us args = none := by
  rw [optLookup_eq] at hit ⊢
  exact hookOf_pj_retry_none hit

/-- Exactly the choice in Translate.rw's tagged, non-in-place branch:
both values of skipPjRetry give none for the production callback. -/
theorem optLookup_pj_retry_choice (cenv : Ix.CompileM.CompileEnv)
    (blocks : Std.HashMap Name OptBlock) {site : Option Name}
    {n : Name} {us : Array Level} {args : Array Expr}
    {e : Expr} {cs : Array ConstantInfo} {pass : String}
    (hit : Ix.Compile.Pass.optLookup cenv blocks site n us args = some (e, cs, some pass))
    (skip : Bool) :
    (if skip then none else
      (Ix.Compile.Pass.optLookup cenv blocks none n us args).map
        (fun (e, cs, _) => (e, cs))) = none := by
  rw [optLookup_pj_retry_none cenv blocks hit]
  cases skip <;> rfl

end Ix.CompileCert.Opt


/-!
UNCOMPILED V6 proof repair. `EmptyRetry` is the unchanged excluded five-root
dependency accepted separately. V2, V3, V4 and V5 were strictly RED; none of their
additional roots is accepted.

The subject is the actual mutually recursive stateful Translate evaluator.
All caches are arbitrary and equal in the two initial states. `StateRel`
allows exactly one changed field, the performance flag; it also retains the
production hook internally so that the relation composes through binds.
No new caller-domain hypothesis or semantic cache-key property is introduced.
-/

namespace Ix.CompileCert.Opt.RetryStateDraft

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Pass (RwState RwM Expansion)
open Ix.Compile.Pass.Opt (OptEnv)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)

def enableSkip (s : RwState) : RwState := { s with skipPjRetry := true }

def StateRel (env : OptEnv) (s t : RwState) : Prop :=
  s.opt? = hookOf env ∧ t = enableSkip s

def ResultRel (env : OptEnv) {α : Type}
    (x y : Except String (α × RwState)) : Prop :=
  match x, y with
  | .error e, .error e' => e = e'
  | .ok (a, s), .ok (b, t) => a = b ∧ StateRel env s t
  | _, _ => False

def Sim (env : OptEnv) {α : Type} (m n : RwM α) : Prop :=
  ∀ s t, StateRel env s t → ResultRel env (m.run s) (n.run t)

abbrev Stable (env : OptEnv) {α : Type} (m : RwM α) : Prop := Sim env m m

theorem sim_pure (env : OptEnv) {α : Type} (a : α) : Stable env (pure a) := by
  intro s t h
  exact ⟨rfl, h⟩

theorem sim_bind {env : OptEnv} {α β : Type} {m n : RwM α}
    {k l : α → RwM β} (hm : Sim env m n)
    (hk : ∀ a, Sim env (k a) (l a)) : Sim env (m >>= k) (n >>= l) := by
  intro s t hst
  have h := hm s t hst
  change ResultRel env
    (Except.bind (m.run s) fun p => (k p.1).run p.2)
    (Except.bind (n.run t) fun p => (l p.1).run p.2)
  cases hx : m.run s with
  | error e =>
    cases hy : n.run t with
    | error e' =>
      have same : e = e' := by simpa only [hx, hy, ResultRel] using h
      exact same
    | ok q =>
      simp only [hx, hy, ResultRel] at h
  | ok p =>
    obtain ⟨a, s'⟩ := p
    cases hy : n.run t with
    | error e =>
      simp only [hx, hy, ResultRel] at h
    | ok q =>
      obtain ⟨b, t'⟩ := q
      have hp : a = b ∧ StateRel env s' t' := by
        simpa only [hx, hy, ResultRel] using h
      obtain ⟨rfl, hst'⟩ := hp
      exact hk a s' t' hst'

theorem stable_bind {env : OptEnv} {α β : Type} {m : RwM α}
    {k : α → RwM β} (hm : Stable env m) (hk : ∀ a, Stable env (k a)) :
    Stable env (m >>= k) := sim_bind hm hk

/-- `get` returns unequal records; its continuations receive the exact related
records. Treating `get` itself as an equal-value action would be incorrect. -/
theorem sim_get_bind {env : OptEnv} {α : Type} {k l : RwState → RwM α}
    (h : ∀ s, s.opt? = hookOf env → Sim env (k s) (l (enableSkip s))) :
    Sim env (get >>= k) (get >>= l) := by
  intro s t hst
  obtain ⟨hs, rfl⟩ := hst
  exact h s hs s (enableSkip s) ⟨hs, rfl⟩

theorem sim_modify {env : OptEnv} {f : RwState → RwState}
    (h : ∀ s, s.opt? = hookOf env →
      (f s).opt? = hookOf env ∧ f (enableSkip s) = enableSkip (f s)) :
    Stable env (modify f) := by
  intro s t hst
  obtain ⟨hs, rfl⟩ := hst
  exact ⟨rfl, h s hs⟩

theorem sim_set {env : OptEnv} {s t : RwState} (h : StateRel env s t) :
    Sim env (set s) (set t) := by
  intro u v _
  exact ⟨rfl, h⟩

theorem sim_lift (env : OptEnv) {α : Type} (x : Except String α) :
    Stable env (liftM x) := by
  intro s t hst
  cases x with
  | error e => exact rfl
  | ok a => exact ⟨rfl, hst⟩

theorem sim_throw (env : OptEnv) {α : Type} (e : String) :
    Stable env (throw e : RwM α) := sim_lift env (.error e)

theorem sim_forIn_list {env : OptEnv} {α β : Type}
    (xs : List α) (f : α → β → RwM (ForInStep β))
    (h : ∀ a b, Stable env (f a b)) (b : β) :
    Stable env (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using sim_pure env b
  | cons a xs ih =>
    rw [List.forIn_cons]
    apply stable_bind (h a b)
    intro step
    cases step with
    | done b => exact sim_pure env b
    | yield b => exact ih b

/-- The actual Array loop, including the ordered accumulator and error path. -/
theorem sim_forIn_array {env : OptEnv} {α β : Type}
    (xs : Array α) (f : α → β → RwM (ForInStep β))
    (h : ∀ a b, Stable env (f a b)) (b : β) :
    Stable env (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact sim_forIn_list xs.toList f h b

/-- Exact effectful tagged-hit fragment of Translate.rw, including the
ordered PJ record update. This helper is proof-local only. -/
def hookStep (site : Option Name) (n : Name) (us : Array Level)
    (args : Array Expr) : RwM (Option (Expr × Array ConstantInfo)) := do
  let st ← get
  match st.opt? site n us args with
  | some (e, cs, none) => pure (some (e, cs))
  | some (e, cs, some pass) =>
    if st.inPlace then pure (some (e, cs))
    else do
      modify fun st => { st with
        pjFired := true
        pjPasses := if st.pjPasses.contains pass then st.pjPasses else st.pjPasses.push pass }
      pure (if st.skipPjRetry then none else
        (st.opt? none n us args).map fun (e, cs, _) => (e, cs))
  | none => pure none

theorem hookStep_sim (env : OptEnv) (site : Option Name) (n : Name)
    (us : Array Level) (args : Array Expr) : Stable env (hookStep site n us args) := by
  unfold hookStep
  apply sim_get_bind
  intro st hopt
  dsimp only [enableSkip]
  simp only [hopt]
  cases hit : hookOf env site n us args with
  | none => exact sim_pure env none
  | some result =>
    obtain ⟨e, cs, tag⟩ := result
    cases tag with
    | none => exact sim_pure env (some (e, cs))
    | some pass =>
      by_cases place : st.inPlace = true
      · simp only [place, ↓reduceIte]
        exact sim_pure env (some (e, cs))
      · simp only [place, ↓reduceIte]
        have empty := hookOf_pj_retry_none hit
        simp only [empty, Option.map_none]
        cases st.skipPjRetry <;>
          apply stable_bind
        all_goals first
          | (apply sim_modify; intro s hs; exact ⟨hs, rfl⟩)
          | (intro _; exact sim_pure env none)

/- The following two bodies are proof-local factorizations. The two equality
lemmas below are essential: these are not substituted specifications or
new runtime implementations. `rec` and `exp` are the actual fuel-smaller
functions when the factorization is used. -/

def expansionStep (expansion? : Name → Except String (Option Expansion))
    (rec : Bool → Expr → RwM Expr) (n : Name) : RwM (Option Expansion) := do
  if let some x := (← get).exps.get? n then return some x
  match ← liftM (expansion? n) with
  | none => return none
  | some x =>
    let x ← if x.needsRewrite then do
        let site := (← get).site
        modify fun st => { st with site := none }
        let v ← rec false x.value
        modify fun st => { st with site }
        pure { x with value := v, needsRewrite := false }
      else pure x
    modify fun st => { st with exps := st.exps.insert n x }
    return some x

def rwStep (rec : Bool → Expr → RwM Expr)
    (exp : Name → RwM (Option Expansion)) (record : Bool) (e : Expr) : RwM Expr := do
  let site := (← get).site
  if let some r := (← get).cache.get? (e, record, site) then
    if let some ds := (← get).declineCache.get? (e, record, site) then
      modify fun st => { st with declines := st.declines ++ ds }
    return r
  let before := (← get).declines.size
  let r ← match e with
    | .app .. | .const .. => do
      let (h, args) := getAppFnArgs e
      match h with
      | .const n us _ =>
        match ← exp n with
        | some x =>
          let mut args' : Array Expr := #[]
          for a in args do args' := args'.push (← rec false a)
          if args.size < x.arity then
            return mkAppN (Expr.mkConst n us) args'
          let res ← hookStep site n us args'
          let body ← match res with
            | some (e, cs) =>
              if !cs.isEmpty then
                modify fun st => { st with canon := cs.foldl (fun acc c =>
                  if acc.any (·.getCnst.name == c.getCnst.name) then acc else acc.push c) st.canon }
              pure e
            | none => do
              let f ← match (← get).levelCache.get? (n, us) with
                | some f => pure f
                | none => do
                  let f := substLevels x.levelParams us x.value
                  modify fun st => { st with levelCache := st.levelCache.insert (n, us) f }
                  pure f
              let dev0 := (← get).dev
              modify fun st => { st with dev := {} }
              let (body, dev) ← liftM (Ix.Compile.Image.instantiateWith dev0 f args')
              modify fun st => { st with dev }
              pure body
          if let some cause := (← get).decline? n us args' then
            modify fun st => { st with declines := st.declines.push cause }
          if record then
            let st ← get
            let k := st.base + st.sources.size
            set { st with sources := st.sources.push e }
            pure (Expr.mkMData #[(Ix.Compile.Pass.inlineKey, .ofNat k)] body)
          else pure body
        | none =>
          let mut args' : Array Expr := #[]
          for a in args do args' := args'.push (← rec record a)
          pure (mkAppN h args')
      | _ =>
        let h' ← rec record h
        let mut args' : Array Expr := #[]
        for a in args do args' := args'.push (← rec record a)
        pure (mkAppN h' args')
    | .lam n t b bi _ => do
      pure (Expr.mkLam n (← rec record t) (← rec record b) bi)
    | .forallE n t b bi _ => do
      pure (Expr.mkForallE n (← rec record t) (← rec record b) bi)
    | .letE n t v b nd _ => do
      pure (Expr.mkLetE n (← rec record t) (← rec record v) (← rec record b) nd)
    | .proj s i x _ => do pure (Expr.mkProj s i (← rec record x))
    | .mdata md x _ => do pure (Expr.mkMData md (← rec record x))
    | e => pure e
  modify fun st => { st with
    cache := st.cache.insert (e, record, site) r
    declineCache := if st.declines.size == before then st.declineCache
      else st.declineCache.insert (e, record, site) (st.declines.extract before st.declines.size) }
  return r

theorem expansionOf_succ_eq (expansion? : Name → Except String (Option Expansion))
    (fuel : Nat) (n : Name) :
    Ix.Compile.Pass.expansionOf expansion? (fuel + 1) n =
      expansionStep expansion? (Ix.Compile.Pass.rw expansion? fuel) n := by
  rfl

/- Extracting hookStep associates binds and distributes the same continuation
through its branch tests. Follow equal monadic actions with bind_congr, keeping
StateT, Except and recursive results opaque. Only finite branch tests are split;
no callback, cache, or state invariant is assumed. -/
theorem rw_succ_eq (expansion? : Name → Except String (Option Expansion))
    (fuel : Nat) (record : Bool) (e : Expr) :
    Ix.Compile.Pass.rw expansion? (fuel + 1) record e =
      rwStep (Ix.Compile.Pass.rw expansion? fuel)
        (Ix.Compile.Pass.expansionOf expansion? fuel) record e := by
  rw [Ix.Compile.Pass.rw]
  -- Keep the actual smaller-fuel computations opaque while comparing one step.
  generalize hrec : Ix.Compile.Pass.rw expansion? fuel = rec
  generalize hexp : Ix.Compile.Pass.expansionOf expansion? fuel = exp
  clear hrec hexp
  unfold rwStep
  apply bind_congr
  intro siteState
  apply bind_congr
  intro cacheState
  -- Both programs inspect this exact lookup. `split` reduced only the left
  -- matcher in V7, leaving the right program at its original cache branch.
  cases cached : cacheState.cache.get? (e, record, siteState.site) with
  | some r => rfl
  | none =>
    apply bind_congr
    intro beforeState
    generalize hspine : getAppFnArgs e = spine
    obtain ⟨head, args⟩ := spine
    clear hspine
    cases e
    case app | const =>
      cases head
      case const n us hash =>
        dsimp only
        apply bind_congr
        intro found
        cases found with
        | none => rfl
        | some x =>
          apply bind_congr
          intro args'
          by_cases short : args.size < x.arity
          · simp only [short, ↓reduceIte]
          · simp only [short, ↓reduceIte]
            -- Reassociate only the factored right-hand hook. This is core
            -- Lean's conv syntax, not the unavailable `conv_rhs` tactic.
            conv =>
              rhs
              rw [hookStep, bind_assoc]
            apply bind_congr
            intro hookState
            cases hit : hookState.opt? siteState.site n us args' with
            | none => simp only [pure_bind] ; rfl
            | some answer =>
              obtain ⟨value, constants, tag⟩ := answer
              cases tag with
              | none => simp only [pure_bind] ; rfl
              | some pass =>
                by_cases place : hookState.inPlace = true
                · simp only [place, ↓reduceIte, pure_bind] ; rfl
                · simp only [ite_eq_right place, bind_assoc, pure_bind] ; rfl
      all_goals rfl
    all_goals rfl


/- Each tactic step follows one monadic constructor without unfolding
Sim, recursive evaluators or whole StateT computations during failed matches.
Reducible transparency still opens the Stable/RwM/getThe abbreviations and
class projections. In particular a get is handled by sim_get_bind, not by
inventing an equal-value simulation of its unequal returned records.

All state fields and error paths remain in the original relation. These
proof-only search changes are UNCOMPILED; V3's partial printing accepted no
additional roots. -/
syntax "retry_walk " ident ident : tactic
macro_rules
  | `(tactic| retry_walk $hr:ident $he:ident) => `(tactic| with_reducible first
      | exact $hr:ident _ _
      | exact $he:ident _
      | exact hookStep_sim _ _ _ _ _
      | exact sim_pure _ _
      | exact sim_lift _ _
      | (apply sim_modify; intro s hs; exact ⟨hs, rfl⟩)
      | (apply sim_set; exact ⟨by assumption, rfl⟩)
      | (apply sim_get_bind
         intro s hs
         dsimp only [enableSkip]
         retry_walk $hr:ident $he:ident)
      | (apply stable_bind
         · retry_walk $hr:ident $he:ident
         · intro a
           retry_walk $hr:ident $he:ident)
      | (apply sim_forIn_array
         intro a b
         retry_walk $hr:ident $he:ident)
      | (split <;> retry_walk $hr:ident $he:ident))

theorem expansionStep_sim (env : OptEnv)
    (expansion? : Name → Except String (Option Expansion))
    (rec : Bool → Expr → RwM Expr)
    (hr : ∀ record e, Stable env (rec record e)) (n : Name) :
    Stable env (expansionStep expansion? rec n) := by
  have he : ∀ n, Stable env (liftM (expansion? n)) := fun n => sim_lift env (expansion? n)
  unfold expansionStep
  retry_walk hr he

theorem rwStep_sim (env : OptEnv) (rec : Bool → Expr → RwM Expr)
    (exp : Name → RwM (Option Expansion))
    (hr : ∀ record e, Stable env (rec record e))
    (he : ∀ n, Stable env (exp n)) (record : Bool) (e : Expr) :
    Stable env (rwStep rec exp record e) := by
  -- The continuation shared by branches that reach the final cache write.
  -- The earlier partial-application return is handled by sim_pure below.
  -- Keeping this local avoids repeating its two large record-update proofs.
  let finish (key : Expr) (site : Option Name) (before : Nat) (r : Expr) : RwM Expr := do
    modify fun st => { st with
      cache := st.cache.insert (key, record, site) r
      declineCache := if st.declines.size == before then st.declineCache
        else st.declineCache.insert (key, record, site) (st.declines.extract before st.declines.size) }
    pure r
  have finish_ok (key : Expr) (site : Option Name) (before : Nat) (r : Expr) :
      Stable env (finish key site before r) := by
    dsimp only [finish]
    apply stable_bind
    · apply sim_modify
      intro s hs
      exact ⟨hs, rfl⟩
    · intro _
      exact sim_pure env r
  let recorded (key : Expr) (site : Option Name) (before : Nat) (body : Expr) : RwM Expr := do
    if record then
      let st ← get
      let k := st.base + st.sources.size
      set { st with sources := st.sources.push key }
      finish key site before (Expr.mkMData #[(Ix.Compile.Pass.inlineKey, .ofNat k)] body)
    else finish key site before body
  have recorded_ok (key : Expr) (site : Option Name) (before : Nat) (body : Expr) :
      Stable env (recorded key site before body) := by
    dsimp only [recorded]
    cases record with
    | false => exact finish_ok key site before body
    | true =>
      apply sim_get_bind
      intro s hs
      dsimp only [enableSkip]
      apply sim_bind
      · apply sim_set
        exact ⟨hs, rfl⟩
      · intro _
        exact finish_ok key site before _
  let after (key : Expr) (site : Option Name) (before : Nat)
      (n : Name) (us : Array Level) (args : Array Expr) (body : Expr) : RwM Expr := do
    if let some cause := (← get).decline? n us args then
      modify fun st => { st with declines := st.declines.push cause }
    recorded key site before body
  have after_ok (key : Expr) (site : Option Name) (before : Nat)
      (n : Name) (us : Array Level) (args : Array Expr) (body : Expr) :
      Stable env (after key site before n us args body) := by
    dsimp only [after]
    apply sim_get_bind
    intro s _
    dsimp only [enableSkip]
    cases cause : s.decline? n us args with
    | none => exact recorded_ok key site before body
    | some cause =>
      apply stable_bind
      · apply sim_modify
        intro s hs
        exact ⟨hs, rfl⟩
      · intro _
        exact recorded_ok key site before body
  let develop (key : Expr) (site : Option Name) (before : Nat)
      (n : Name) (us : Array Level) (args : Array Expr) (f : Expr) : RwM Expr := do
    let dev0 := (← get).dev
    modify fun st => { st with dev := {} }
    let (body, dev) ← liftM (Ix.Compile.Image.instantiateWith dev0 f args)
    modify fun st => { st with dev }
    after key site before n us args body
  have develop_ok (key : Expr) (site : Option Name) (before : Nat)
      (n : Name) (us : Array Level) (args : Array Expr) (f : Expr) :
      Stable env (develop key site before n us args f) := by
    dsimp only [develop]
    apply sim_get_bind
    intro s _
    dsimp only [enableSkip]
    apply stable_bind
    · apply sim_modify
      intro s hs
      exact ⟨hs, rfl⟩
    · intro _
      apply stable_bind (sim_lift env (Ix.Compile.Image.instantiateWith s.dev f args))
      intro result
      obtain ⟨body, dev⟩ := result
      apply stable_bind
      · apply sim_modify
        intro s hs
        exact ⟨hs, rfl⟩
      · intro _
        exact after_ok key site before n us args body
  have args_ok (record' : Bool) (args : Array Expr) :
      Stable env (forIn args (#[] : Array Expr) fun a acc => do
        let a' ← rec record' a
        pure (ForInStep.yield (acc.push a'))) := by
    apply sim_forIn_array
    intro a acc
    apply stable_bind (hr record' a)
    intro a'
    exact sim_pure env (ForInStep.yield (acc.push a'))
  unfold rwStep
  apply sim_get_bind
  intro siteState _
  dsimp only [enableSkip]
  apply sim_get_bind
  intro cacheState _
  dsimp only [enableSkip]
  cases cached : cacheState.cache.get? (e, record, siteState.site) with
  | some r =>
    apply sim_get_bind
    intro declineState _
    dsimp only [enableSkip]
    cases declines : declineState.declineCache.get? (e, record, siteState.site) with
    | none => exact sim_pure env r
    | some ds =>
      apply stable_bind
      · apply sim_modify
        intro s hs
        exact ⟨hs, rfl⟩
      · intro _
        exact sim_pure env r
  | none =>
    apply sim_get_bind
    intro beforeState _
    dsimp only [enableSkip]
    generalize hspine : getAppFnArgs e = spine
    obtain ⟨head, args⟩ := spine
    clear hspine
    cases e
    case lam name ty body info hash | forallE name ty body info hash =>
      apply stable_bind (hr record ty)
      intro ty'
      apply stable_bind (hr record body)
      intro body'
      simpa only [pure_bind] using finish_ok _ siteState.site beforeState.declines.size _
    case letE name ty value body nonDep hash =>
      apply stable_bind (hr record ty)
      intro ty'
      apply stable_bind (hr record value)
      intro value'
      apply stable_bind (hr record body)
      intro body'
      simpa only [pure_bind] using finish_ok _ siteState.site beforeState.declines.size _
    case mdata metadata value hash | proj name idx value hash =>
      apply stable_bind (hr record value)
      intro value'
      simpa only [pure_bind] using finish_ok _ siteState.site beforeState.declines.size _
    case bvar | fvar | mvar | sort | lit =>
      simpa only [pure_bind] using finish_ok _ siteState.site beforeState.declines.size _
    case app | const =>
      cases head
      case const n us hash =>
        apply stable_bind (he n)
        intro found
        cases found with
        | none =>
          apply stable_bind (args_ok record args)
          intro args'
          simpa only [pure_bind] using finish_ok _ siteState.site beforeState.declines.size _
        | some x =>
          apply stable_bind (args_ok false args)
          intro args'
          by_cases short : args.size < x.arity
          · simp only [short, ↓reduceIte]
            exact sim_pure env _
          · simp only [short, ↓reduceIte]
            apply stable_bind (hookStep_sim env siteState.site n us args')
            intro result
            cases result with
            | some answer =>
              obtain ⟨body, constants⟩ := answer
              -- Reduce the known option/pair matcher before choosing its
              -- Boolean branch; V7 split that matcher a second time.
              dsimp only
              by_cases nonempty : (!constants.isEmpty) = true
              · simp only [nonempty, ↓reduceIte]
                apply stable_bind
                · apply sim_modify
                  intro s hs
                  exact ⟨hs, rfl⟩
                · intro _
                  simpa only [pure_bind] using
                    after_ok _ siteState.site beforeState.declines.size n us args' body
              · simp only [ite_eq_right nonempty]
                simpa only [pure_bind] using
                  after_ok _ siteState.site beforeState.declines.size n us args' body
            | none =>
              apply sim_get_bind
              intro levelState _
              dsimp only [enableSkip]
              cases level : levelState.levelCache.get? (n, us) with
              | some f =>
                simpa only [pure_bind] using
                  develop_ok _ siteState.site beforeState.declines.size n us args' f
              | none =>
                apply stable_bind
                · apply sim_modify
                  intro s hs
                  exact ⟨hs, rfl⟩
                · intro _
                  simpa only [pure_bind] using
                    develop_ok _ siteState.site beforeState.declines.size n us args'
                      (substLevels x.levelParams us x.value)
      all_goals
        apply stable_bind (hr record _)
        intro head'
        apply stable_bind (args_ok record args)
        intro args'
        simpa only [pure_bind] using finish_ok _ siteState.site beforeState.declines.size _


/-- Mutual induction on the actual runtime's fuel. The hypotheses on the
two step lemmas are discharged here, not added to the final theorem. -/
theorem runtime_sim (env : OptEnv)
    (expansion? : Name → Except String (Option Expansion)) (fuel : Nat) :
    (∀ n, Stable env (Ix.Compile.Pass.expansionOf expansion? fuel n)) ∧
    (∀ record e, Stable env (Ix.Compile.Pass.rw expansion? fuel record e)) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ => sim_throw env _, fun _ _ => sim_throw env _⟩
  | succ fuel ih =>
    refine ⟨?_, ?_⟩
    · intro n
      rw [expansionOf_succ_eq]
      exact expansionStep_sim env expansion? _ ih.2 n
    · intro record e
      rw [rw_succ_eq]
      exact rwStep_sim env _ _ ih.2 ih.1 record e

def enableResult {α : Type} (x : Except String (α × RwState)) :
    Except String (α × RwState) := x.map fun (a, s) => (a, enableSkip s)

theorem sim_run_eq {env : OptEnv} {α : Type} {m n : RwM α}
    (h : Sim env m n) (s : RwState) (hs : s.opt? = hookOf env) :
    n.run (enableSkip s) = enableResult (m.run s) := by
  have hr := h s (enableSkip s) ⟨hs, rfl⟩
  cases hm : m.run s with
  | error e =>
    cases hn : n.run (enableSkip s) with
    | error e' =>
      have same : e = e' := by simpa only [hm, hn, ResultRel] using hr
      subst e'
      rfl
    | ok q =>
      simp only [hm, hn, ResultRel] at hr
  | ok p =>
    obtain ⟨a, s'⟩ := p
    cases hn : n.run (enableSkip s) with
    | error e =>
      simp only [hm, hn, ResultRel] at hr
    | ok q =>
      obtain ⟨b, t'⟩ := q
      have hp : a = b ∧ StateRel env s' t' := by
        simpa only [hm, hn, ResultRel] using hr
      obtain ⟨rfl, _, rfl⟩ := hp
      rfl

def prodState (env : OptEnv) (skip : Bool) (s : RwState) : RwState :=
  { s with opt? := hookOf env, skipPjRetry := skip }

/-- Exact values/errors and complete final states for the production hook.
Arbitrary raw expansion lookup, fuel, site, inPlace, initial records and
all caches remain quantified. This is the runtime flag-refinement target. -/
theorem runtime_skip_eq (env : OptEnv)
    (expansion? : Name → Except String (Option Expansion)) (fuel : Nat) :
    (∀ n s,
      (Ix.Compile.Pass.expansionOf expansion? fuel n).run (prodState env true s) =
        enableResult ((Ix.Compile.Pass.expansionOf expansion? fuel n).run
          (prodState env false s))) ∧
    (∀ record e s,
      (Ix.Compile.Pass.rw expansion? fuel record e).run (prodState env true s) =
        enableResult ((Ix.Compile.Pass.rw expansion? fuel record e).run
          (prodState env false s))) := by
  obtain ⟨he, hr⟩ := runtime_sim env expansion? fuel
  exact ⟨fun n s => sim_run_eq (he n) (prodState env false s) rfl,
    fun record e s => sim_run_eq (hr record e) (prodState env false s) rfl⟩

end Ix.CompileCert.Opt.RetryStateDraft


/-!
UNCOMPILED V4 repair of the production consumers of the stateful F14 simulation.
The initial five engine roots are independently checked, but V2 and V3 were strictly
RED; every addition still requires complete strict elaboration and an axiom audit.
No runtime source, original theorem domain or semantic premise is changed.
-/

namespace Ix.CompileCert.Opt.RetryStateDraft

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Pass (RwState RwM Expansion BlockRewrite)
open Ix.Compile.Pass.Opt (OptEnv OptBlock)

theorem rewriteConstM_sim (env : OptEnv)
    (expansion? : Name → Except String (Option Expansion)) (ci : ConstantInfo) :
    Stable env (Ix.Compile.Pass.rewriteConstM expansion? ci) := by
  obtain ⟨he, hr⟩ := runtime_sim env expansion? Ix.Compile.Pass.rewriteFuel
  cases ci <;> unfold Ix.Compile.Pass.rewriteConstM <;>
    dsimp only <;> retry_walk hr he

theorem rewriteConstM_skip_eq (env : OptEnv)
    (expansion? : Name → Except String (Option Expansion))
    (ci : ConstantInfo) (s : RwState) :
    (Ix.Compile.Pass.rewriteConstM expansion? ci).run (prodState env true s) =
      enableResult ((Ix.Compile.Pass.rewriteConstM expansion? ci).run
        (prodState env false s)) :=
  sim_run_eq (rewriteConstM_sim env expansion? ci) (prodState env false s) rfl

def productionEnv (cenv : Ix.CompileM.CompileEnv)
    (blocks : Std.HashMap Name OptBlock) : OptEnv :=
  { ienv := cenv.env
    resolves := fun n => (Ix.Compile.Pass.resolveAddr cenv n).isSome
    blockOf := fun h => (cenv.p3Heads.get? h).bind blocks.get?
    addrOf := Ix.Compile.Pass.resolveAddr cenv
    ixForm? := Ix.Compile.Pass.ixFormOf cenv }

/-- The actual Driver callback, with arbitrary caller state and expansion
lookup. The engine configuration is constructed, not assumed as a law. -/
theorem runtime_optLookup_skip_eq (cenv : Ix.CompileM.CompileEnv)
    (blocks : Std.HashMap Name OptBlock)
    (expansion? : Name → Except String (Option Expansion)) (fuel : Nat) :
    (∀ n (s : RwState),
      (Ix.Compile.Pass.expansionOf expansion? fuel n).run
        { s with opt? := Ix.Compile.Pass.optLookup cenv blocks, skipPjRetry := true } =
      enableResult ((Ix.Compile.Pass.expansionOf expansion? fuel n).run
        { s with opt? := Ix.Compile.Pass.optLookup cenv blocks, skipPjRetry := false })) ∧
    (∀ record e (s : RwState),
      (Ix.Compile.Pass.rw expansion? fuel record e).run
        { s with opt? := Ix.Compile.Pass.optLookup cenv blocks, skipPjRetry := true } =
      enableResult ((Ix.Compile.Pass.rw expansion? fuel record e).run
        { s with opt? := Ix.Compile.Pass.optLookup cenv blocks, skipPjRetry := false })) := by
  simpa only [prodState, productionEnv, optLookup_eq] using
    runtime_skip_eq (productionEnv cenv blocks) expansion? fuel

theorem rewriteConstM_optLookup_skip_eq (cenv : Ix.CompileM.CompileEnv)
    (blocks : Std.HashMap Name OptBlock)
    (expansion? : Name → Except String (Option Expansion))
    (ci : ConstantInfo) (s : RwState) :
    (Ix.Compile.Pass.rewriteConstM expansion? ci).run
      { s with opt? := Ix.Compile.Pass.optLookup cenv blocks, skipPjRetry := true } =
    enableResult ((Ix.Compile.Pass.rewriteConstM expansion? ci).run
      { s with opt? := Ix.Compile.Pass.optLookup cenv blocks, skipPjRetry := false }) := by
  simpa only [prodState, productionEnv, optLookup_eq] using
    rewriteConstM_skip_eq (productionEnv cenv blocks) expansion? ci s

/- A small relation for the actual outer Except loop. Its accumulator
contains the full RwState; equality of just emitted expressions would not
justify the next member's execution. -/
def ExceptRel {α β : Type} (R : α → β → Prop) : Except String α → Except String β → Prop
  | .error e, .error e' => e = e'
  | .ok a, .ok b => R a b
  | _, _ => False

def StepRel {α β : Type} (R : α → β → Prop) : ForInStep α → ForInStep β → Prop
  | .done a, .done b => R a b
  | .yield a, .yield b => R a b
  | _, _ => False

theorem exceptRel_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β}
    (h : R a b) : ExceptRel R (pure a) (pure b) := h

theorem exceptRel_refl {α : Type} (x : Except String α) : ExceptRel Eq x x := by
  cases x <;> exact rfl

theorem exceptRel_eq {α : Type} {x y : Except String α}
    (h : ExceptRel Eq x y) : x = y := by
  cases x <;> cases y <;> dsimp only [ExceptRel] at h <;> cases h <;> rfl

theorem exceptRel_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Except String α} {y : Except String β}
    {f : α → Except String γ} {g : β → Except String δ}
    (hxy : ExceptRel R x y) (hfg : ∀ a b, R a b → ExceptRel S (f a) (g b)) :
    ExceptRel S (x >>= f) (y >>= g) := by
  cases x with
  | error e =>
    cases y with
    | error e' => exact hxy
    | ok b => exact hxy.elim
  | ok a =>
    cases y with
    | error e => exact hxy.elim
    | ok b => exact hfg a b hxy

theorem exceptRel_forIn_list {α β γ : Type} (R : β → γ → Prop)
    (f : α → β → Except String (ForInStep β))
    (g : α → γ → Except String (ForInStep γ))
    (hstep : ∀ a b c, R b c → ExceptRel (StepRel R) (f a b) (g a c))
    (xs : List α) {b : β} {c : γ} (hbc : R b c) :
    ExceptRel R (forIn xs b f) (forIn xs c g) := by
  induction xs generalizing b c with
  | nil => simpa only [List.forIn_nil] using exceptRel_pure hbc
  | cons a xs ih =>
    simp only [List.forIn_cons]
    apply exceptRel_bind (hstep a b c hbc)
    intro rb rc h
    cases rb <;> cases rc
    · exact exceptRel_pure h
    · exact h.elim
    · exact h.elim
    · exact ih h

theorem exceptRel_forIn_array {α β γ : Type} (R : β → γ → Prop)
    (f : α → β → Except String (ForInStep β))
    (g : α → γ → Except String (ForInStep γ))
    (hstep : ∀ a b c, R b c → ExceptRel (StepRel R) (f a b) (g a c))
    (xs : Array α) {b : β} {c : γ} (hbc : R b c) :
    ExceptRel R (forIn xs b f) (forIn xs c g) := by
  simpa only [Array.forIn_toList] using
    exceptRel_forIn_list R f g hstep xs.toList hbc

theorem resultRel_exceptRel {env : OptEnv} {α : Type}
    {x y : Except String (α × RwState)} (h : ResultRel env x y) :
    ExceptRel (fun p q => p.1 = q.1 ∧ StateRel env p.2 q.2) x y := by
  cases x with
  | error e =>
    cases y <;> exact h
  | ok p =>
    obtain ⟨a, s⟩ := p
    cases y with
    | error e => exact h
    | ok q =>
      obtain ⟨b, t⟩ := q
      exact h

abbrev BlockAcc := RwState × Array (Name × ConstantInfo) × Array (Name × String)

def enableAcc (a : BlockAcc) : BlockAcc := (enableSkip a.1, a.2.1, a.2.2)

def AccRel (env : OptEnv) (a b : BlockAcc) : Prop :=
  a.1.opt? = hookOf env ∧ b = enableAcc a

/-- Exact body of the actual member loop, with its three mutable variables
made explicit in declaration order: state, overlay, declines. -/
def blockStep (expansion? : Name → Except String (Option Expansion))
    (member : Name × ConstantInfo) (acc : BlockAcc) : Except String (ForInStep BlockAcc) := do
  let (n, ci) := member
  let st := acc.1
  let mut overlay := acc.2.1
  let mut declines := acc.2.2
  let before := st.declines.size
  let (ci', st') ← (Ix.Compile.Pass.rewriteConstM expansion? ci).run st
  let st := st'
  for c in st.declines.extract before st.declines.size do
    unless declines.contains (n, c) do declines := declines.push (n, c)
  if ci' != ci then overlay := overlay.push (n, ci')
  pure (.yield (st, overlay, declines))

def blockResult (acc : BlockAcc) : BlockRewrite :=
  { overlay := acc.2.1, sources := acc.1.sources, needed := acc.1.needed,
    declines := acc.2.2, canon := acc.1.canon, pjForms := acc.1.pjForms }

/-- This factorization is a proof obligation about the original executable
definition. No specification or alternative driver is substituted. -/
theorem rewriteBlock_eq_forIn
    (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo))
    (opt? : Option Name → Name → Array Level → Array Expr →
      Option (Expr × Array ConstantInfo × Option String))
    (decline? : Name → Array Level → Array Expr → Option String)
    (inPlace skip : Bool) :
    Ix.Compile.Pass.rewriteBlock expansion? members opt? decline? inPlace skip = (do
      let acc ← forIn members
        (({ base := 0, opt?, decline?, inPlace, skipPjRetry := skip } : RwState), #[], #[])
        (blockStep expansion?)
      pure (blockResult acc)) := by
  rfl

theorem blockStep_rel (env : OptEnv)
    (expansion? : Name → Except String (Option Expansion))
    (member : Name × ConstantInfo) (a b : BlockAcc) (h : AccRel env a b) :
    ExceptRel (StepRel (AccRel env)) (blockStep expansion? member a)
      (blockStep expansion? member b) := by
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨n, ci⟩ := member
  obtain ⟨st, overlay, declines⟩ := a
  unfold blockStep
  dsimp only [enableAcc, enableSkip]
  apply exceptRel_bind
  · exact resultRel_exceptRel
      (rewriteConstM_sim env expansion? ci st (enableSkip st) ⟨hs, rfl⟩)
  · intro lhsResult rhsResult hres
    obtain ⟨ci', st'⟩ := lhsResult
    obtain ⟨ci'', st''⟩ := rhsResult
    obtain ⟨rfl, hs', rfl⟩ := hres
    dsimp only [enableSkip]
    apply exceptRel_bind (exceptRel_refl _)
    intro ds ds' same
    subst ds'
    split <;> exact ⟨hs', rfl⟩

theorem blockResult_eq {env : OptEnv} {a b : BlockAcc} (h : AccRel env a b) :
    blockResult a = blockResult b := by
  obtain ⟨_, rfl⟩ := h
  rfl

theorem rewriteBlock_hook_skip_eq (env : OptEnv)
    (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo))
    (decline? : Name → Array Level → Array Expr → Option String) (inPlace : Bool) :
    Ix.Compile.Pass.rewriteBlock expansion? members (hookOf env) decline? inPlace true =
      Ix.Compile.Pass.rewriteBlock expansion? members (hookOf env) decline? inPlace false := by
  simp only [rewriteBlock_eq_forIn]
  let a : BlockAcc :=
    ({ base := 0, opt? := hookOf env, decline?, inPlace, skipPjRetry := false }, #[], #[])
  have hloop := exceptRel_forIn_array (AccRel env) (blockStep expansion?) (blockStep expansion?)
    (fun m a b h => blockStep_rel env expansion? m a b h) members
    (b := a) (c := enableAcc a) ⟨rfl, rfl⟩
  have hresult : ExceptRel Eq
      (forIn members a (blockStep expansion?) >>= fun acc => pure (blockResult acc))
      (forIn members (enableAcc a) (blockStep expansion?) >>= fun acc => pure (blockResult acc)) :=
    exceptRel_bind hloop (fun a b h => exceptRel_pure (blockResult_eq h))
  exact (exceptRel_eq hresult).symm

/-- Exact flag refinement at the production Driver.prepareBlock hookup.
Includes all errors, member order, decline order/deduplication and every
returned BlockRewrite field. No runtime-to-core or Conv claim is made. -/
theorem rewriteBlock_optLookup_skip_eq (cenv : Ix.CompileM.CompileEnv)
    (blocks : Std.HashMap Name OptBlock)
    (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo))
    (decline? : Name → Array Level → Array Expr → Option String) (inPlace : Bool) :
    Ix.Compile.Pass.rewriteBlock expansion? members
        (Ix.Compile.Pass.optLookup cenv blocks) decline? inPlace true =
      Ix.Compile.Pass.rewriteBlock expansion? members
        (Ix.Compile.Pass.optLookup cenv blocks) decline? inPlace false := by
  simpa only [productionEnv, optLookup_eq] using
    rewriteBlock_hook_skip_eq (productionEnv cenv blocks) expansion? members decline? inPlace

end Ix.CompileCert.Opt.RetryStateDraft


#print axioms Ix.CompileCert.Opt.engineFull_siteFree_lift
#print axioms Ix.CompileCert.Opt.engineFull_pj_retry_none
#print axioms Ix.CompileCert.Opt.hookOf_pj_retry_none
#print axioms Ix.CompileCert.Opt.optLookup_pj_retry_none
#print axioms Ix.CompileCert.Opt.optLookup_pj_retry_choice
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_pure
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_bind
#print axioms Ix.CompileCert.Opt.RetryStateDraft.stable_bind
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_get_bind
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_modify
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_set
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_lift
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_throw
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_forIn_list
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_forIn_array
#print axioms Ix.CompileCert.Opt.RetryStateDraft.hookStep_sim
#print axioms Ix.CompileCert.Opt.RetryStateDraft.expansionOf_succ_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rw_succ_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.expansionStep_sim
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rwStep_sim
#print axioms Ix.CompileCert.Opt.RetryStateDraft.runtime_sim
#print axioms Ix.CompileCert.Opt.RetryStateDraft.sim_run_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.runtime_skip_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rewriteConstM_sim
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rewriteConstM_skip_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.runtime_optLookup_skip_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rewriteConstM_optLookup_skip_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.exceptRel_pure
#print axioms Ix.CompileCert.Opt.RetryStateDraft.exceptRel_refl
#print axioms Ix.CompileCert.Opt.RetryStateDraft.exceptRel_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.exceptRel_bind
#print axioms Ix.CompileCert.Opt.RetryStateDraft.exceptRel_forIn_list
#print axioms Ix.CompileCert.Opt.RetryStateDraft.exceptRel_forIn_array
#print axioms Ix.CompileCert.Opt.RetryStateDraft.resultRel_exceptRel
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rewriteBlock_eq_forIn
#print axioms Ix.CompileCert.Opt.RetryStateDraft.blockStep_rel
#print axioms Ix.CompileCert.Opt.RetryStateDraft.blockResult_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rewriteBlock_hook_skip_eq
#print axioms Ix.CompileCert.Opt.RetryStateDraft.rewriteBlock_optLookup_skip_eq
