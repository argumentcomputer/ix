import Ix.CompileCert.Opt.O11aSourceBounds
import Init.Internal.Order.While

/-!
F-1: growth of the actual repeated source readers and transport of the initial
protected operands into O11a. This additive proof leaf is UNCOMPILED. It changes
no runtime clause, callback, result, error, cache or source domain. The repeat
proof uses the pinned Lean loop equation and a measure of raw forall spines;
neither hash correctness nor an assumed terminating/fresh caller is required.

This supplies a decreasing repeat, not a runtime termination proof for the
remaining partial pure helpers called before/around it. Conversion of the
instance callback, final abstraction and the full O2/O11a conversion/totality
endpoints remain separate obligations.
-/

namespace Ix.CompileCert.Opt.O11aReaderGrowth

open Ix (Name Level Expr RecursorVal)
open Ix.AuxGen (FreshFVars LocalDecl SourceRecTarget AuxMotiveSig)
open Ix.Compile.Pass.Opt
open Ix.CompileCert.Canon (except_bind_ok)
open Ix.CompileCert.Opt.FreshFVarsProof
open Ix.CompileCert.Opt.O11aFields
open Ix.CompileCert.Opt.O11aSourceBounds

/-- Only the raw leading forall constructors matter to these two repeats.
Metadata, names, domains and cached hashes are not trusted as a measure. -/
def forallDepth : Expr → Nat
  | .forallE _ _ body _ _ => forallDepth body + 1
  | _ => 0

/-- Opening with any raw FVar preserves the remaining forall spine. This is
stronger than a well-formed/canonically hashed-input specialization. -/
theorem forallDepth_instantiate1At_fvar (e : Expr) (name : Name)
    (hash : _root_.Address) (depth : Nat) :
    forallDepth (Ix.AuxGen.instantiate1At e (.fvar name hash) depth) = forallDepth e := by
  induction e generalizing depth with
  | bvar index oldHash =>
      unfold Ix.AuxGen.instantiate1At
      split
      · rfl
      · split <;> rfl
  | forallE binder domain body info oldHash ihd ihb =>
      exact congrArg (· + 1) (ihb (depth + 1))
  | _ => rfl

theorem forallDepth_fresh_open (body : Expr) (supply : FreshFVars)
    (pfx : String) (index : Nat) :
    forallDepth (Ix.AuxGen.instantiate1 body (supply.fresh pfx index).1.2) =
      forallDepth body := by
  rw [fresh_pair_expr]
  exact forallDepth_instantiate1At_fvar body _ _ 0

/-- Supply preservation is stated on the actual StateM answer, not a projected
Option success. Refusals therefore retain the same obligation. -/
def Preserves {α : Type} (action : StateM FreshFVars α) : Prop :=
  ∀ supply, Grows supply (action.run supply).2

theorem preserves_pure {α : Type} (value : α) :
    Preserves (pure value : StateM FreshFVars α) := grows_refl

theorem preserves_bind {α β : Type} (action : StateM FreshFVars α)
    (next : α → StateM FreshFVars β) (actionGrows : Preserves action)
    (rest : ∀ value, Preserves (next value)) : Preserves (action >>= next) := by
  intro supply
  exact grows_trans (actionGrows supply) (rest (action.run supply).1 (action.run supply).2)

theorem protects_array_grows (supply : FreshFVars) (values : Array Expr) :
    Grows supply (supply.protectExprs values) := by
  intro key old
  exact (protectExprs_mem values supply key).2 (.inl old)

theorem protects_array_member (supply : FreshFVars) (values : Array Expr)
    (value : Expr) (member : value ∈ values) : Protects (supply.protectExprs values) value := by
  intro key occurs
  exact (protectExprs_mem values supply key).2
    (.inr ⟨value, Array.mem_toList_iff.2 member, occurs⟩)

theorem preserves_protectExpr (value : Expr) :
    Preserves (modify (·.protectExpr value) : StateM FreshFVars Unit) :=
  fun supply => protectExpr_grows supply value

theorem preserves_protectExprs (values : Array Expr) :
    Preserves (modify (·.protectExprs values) : StateM FreshFVars Unit) :=
  fun supply => protects_array_grows supply values

theorem preserves_protect_inputs (value : Expr) (values : Array Expr) :
    Preserves (modify (fun supply => (supply.protectExpr value).protectExprs values) :
      StateM FreshFVars Unit) := fun supply =>
  grows_trans (protectExpr_grows supply value) (protects_array_grows _ values)

theorem preserves_fresh (pfx : String) (index : Nat) :
    Preserves (Ix.AuxGen.freshFVarM pfx index) := fun supply => fresh_grows supply pfx index

theorem preserves_forIn_array {α τ : Type} (values : Array α) (initial : τ)
    (body : α → τ → StateM FreshFVars (ForInStep τ))
    (step : ∀ value state, Preserves (body value state)) :
    Preserves (forIn values initial body) := by
  intro supply
  rw [← Array.forIn_toList]
  exact state_forIn_grows body step values.toList initial supply

theorem preserves_forIn_range {τ : Type} (values : Std.Legacy.Range) (initial : τ)
    (body : Nat → τ → StateM FreshFVars (ForInStep τ))
    (step : ∀ value state, Preserves (body value state)) :
    Preserves (forIn values initial body) := by
  intro supply
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn_grows body step _ initial supply

/-- The current Lean equation is used at the actual StateM instantiation. -/
theorem state_repeat_eq {τ : Type} (body : Unit → τ → StateM FreshFVars (ForInStep τ))
    (state : τ) (supply : FreshFVars) :
    (Lean.Loop.forIn {} state body).run supply =
      let answer := (body () state).run supply
      match answer.1 with
      | .done out => (out, answer.2)
      | .yield out => (Lean.Loop.forIn {} out body).run answer.2 := by
  have runBind (action : StateM FreshFVars (ForInStep τ))
      (next : ForInStep τ → StateM FreshFVars τ) :
      (action >>= next).run supply =
        (next (action.run supply).1).run (action.run supply).2 := rfl
  rw [Lean.Loop.forIn_eq_of_monadTail, runBind]
  generalize (body () state).run supply = answer
  rcases answer with ⟨step, nextSupply⟩
  cases step <;> rfl

/-- An internal well-founded rule; each actual reader below proves its own
step/decrease facts, so no final caller receives these as new premises. -/
theorem state_repeat_grows {τ : Type}
    (body : Unit → τ → StateM FreshFVars (ForInStep τ)) (rank : τ → Nat)
    (step : ∀ state, Preserves (body () state))
    (decreases : ∀ state supply next after,
      (body () state).run supply = (.yield next, after) → rank next < rank state) :
    ∀ state, Preserves (Lean.Loop.forIn {} state body) := by
  intro state
  induction state using (measure rank).wf.induction with
  | h state ih =>
      intro supply
      rw [state_repeat_eq]
      have grow := step state supply
      generalize observed : (body () state).run supply = answer at grow ⊢
      rcases answer with ⟨out, nextSupply⟩
      cases out with
      | done next => exact grow
      | yield next =>
          exact grows_trans grow (ih next (decreases state supply next nextSupply observed) nextSupply)

/-- Mutable variables of the aux-signature telescope in declaration order. -/
abbrev SigState := Expr × Option Expr × Nat

def sigStep (motiveIndex : Nat) (_ : Unit) (state : SigState) :
    StateM FreshFVars (ForInStep SigState) := do
  let (cur, lastDomain, index) := state
  match cur with
  | .forallE _ domain body _ _ =>
      let (_, fv) ← Ix.AuxGen.freshFVarM "aux_sig_idx" (motiveIndex * 64 + index)
      return .yield (Ix.AuxGen.instantiate1 body fv,
        some (Ix.AuxGen.consumeTypeAnnotations domain), index + 1)
  | _ => return .done (cur, lastDomain, index)

theorem sigStep_grows (motiveIndex : Nat) (state : SigState) :
    Preserves (sigStep motiveIndex () state) := by
  rcases state with ⟨cur, lastDomain, index⟩
  cases cur with
  | forallE name domain body info hash =>
      exact fun supply => fresh_grows supply "aux_sig_idx" (motiveIndex * 64 + index)
  | _ => exact preserves_pure _

theorem sigStep_decreases (motiveIndex : Nat) (state : SigState) (supply : FreshFVars)
    (next : SigState) (after : FreshFVars)
    (run : (sigStep motiveIndex () state).run supply = (.yield next, after)) :
    forallDepth next.1 < forallDepth state.1 := by
  rcases state with ⟨cur, lastDomain, index⟩
  cases cur with
  | forallE name domain body info hash =>
      cases run
      change forallDepth (Ix.AuxGen.instantiate1 body
        (supply.fresh "aux_sig_idx" (motiveIndex * 64 + index)).1.2) < forallDepth body + 1
      rw [forallDepth_fresh_open]
      exact Nat.lt_succ_self _
  | _ => cases run

theorem sigLoop_grows (motiveIndex : Nat) (state : SigState) :
    Preserves (Lean.Loop.forIn {} state (sigStep motiveIndex)) :=
  state_repeat_grows (sigStep motiveIndex) (fun state => forallDepth state.1)
    (sigStep_grows motiveIndex) (sigStep_decreases motiveIndex) state

/-- Mutable variables of the recursive-field telescope in declaration order. -/
abbrev TargetPeelState := Expr × Array LocalDecl × Array Expr

def targetPeelStep (pfx : String) (fieldIndex : Nat) (_ : Unit) (state : TargetPeelState) :
    StateM FreshFVars (ForInStep TargetPeelState) := do
  let (cur, decls, fvars) := state
  match cur with
  | .forallE name domain body info _ =>
      let (fvName, fv) ← Ix.AuxGen.freshFVarM pfx (fieldIndex * 1024 + fvars.size)
      let decl : LocalDecl := {
        fvarName := fvName
        binderName := name
        domain := Ix.AuxGen.consumeTypeAnnotations domain
        info := info }
      return .yield (Ix.AuxGen.instantiate1 body fv, decls.push decl, fvars.push fv)
  | _ => return .done (cur, decls, fvars)

theorem targetPeelStep_grows (pfx : String) (fieldIndex : Nat) (state : TargetPeelState) :
    Preserves (targetPeelStep pfx fieldIndex () state) := by
  rcases state with ⟨cur, decls, fvars⟩
  cases cur with
  | forallE name domain body info hash =>
      exact fun supply => fresh_grows supply pfx (fieldIndex * 1024 + fvars.size)
  | _ => exact preserves_pure _

theorem targetPeelStep_decreases (pfx : String) (fieldIndex : Nat)
    (state : TargetPeelState) (supply : FreshFVars) (next : TargetPeelState)
    (after : FreshFVars)
    (run : (targetPeelStep pfx fieldIndex () state).run supply = (.yield next, after)) :
    forallDepth next.1 < forallDepth state.1 := by
  rcases state with ⟨cur, decls, fvars⟩
  cases cur with
  | forallE name domain body info hash =>
      cases run
      change forallDepth (Ix.AuxGen.instantiate1 body
        (supply.fresh pfx (fieldIndex * 1024 + fvars.size)).1.2) < forallDepth body + 1
      rw [forallDepth_fresh_open]
      exact Nat.lt_succ_self _
  | _ => cases run

theorem targetPeelLoop_grows (pfx : String) (fieldIndex : Nat) (state : TargetPeelState) :
    Preserves (Lean.Loop.forIn {} state (targetPeelStep pfx fieldIndex)) :=
  state_repeat_grows (targetPeelStep pfx fieldIndex) (fun state => forallDepth state.1)
    (targetPeelStep_grows pfx fieldIndex) (targetPeelStep_decreases pfx fieldIndex) state

private theorem preserves_repeat_congr {τ : Type} (state : τ)
    (actual expected : Unit → τ → StateM FreshFVars (ForInStep τ))
    (same : ∀ token current, actual token current = expected token current)
    (growth : Preserves (Lean.Loop.forIn {} state expected)) :
    Preserves (Lean.Loop.forIn {} state actual) := by
  have equal : actual = expected := funext fun token => funext fun current => same token current
  rw [equal]
  exact growth

/-- No result or environment lookup is replaced by a spec. The bind/finite-loop
rules traverse the actual definition; only its two well-founded repeat bodies
are recognized by their exact step definitions above. -/
theorem auxMotiveSigsWith_grows (rv : RecursorVal) (levels : Array Level)
    (params motives : Array Expr) (env : Ix.Environment) :
    Preserves (Ix.AuxGen.auxMotiveSigsWith rv levels params motives env) := by
  unfold Ix.AuxGen.auxMotiveSigsWith
  apply preserves_bind
  · exact preserves_protect_inputs _ _
  · intro _
    dsimp only
    split
    · exact preserves_pure _
    · apply preserves_bind
      · apply preserves_forIn_array
        rintro arg ⟨_, cur⟩
        cases cur <;> exact preserves_pure _
      · rintro ⟨early, cur⟩
        cases early with
        | some out => exact preserves_pure _
        | none =>
            apply preserves_bind
            · apply preserves_forIn_array
              rintro ⟨motive, motiveIndex⟩ ⟨_, out, cur⟩
              dsimp only
              split
              · exact preserves_pure _
              · cases cur with
                | forallE name domain body info hash =>
                    dsimp only
                    split
                    · apply preserves_bind
                      · refine preserves_repeat_congr _ _ (sigStep motiveIndex) ?_
                          (sigLoop_grows motiveIndex _)
                        rintro token ⟨cur, lastDomain, index⟩
                        cases cur <;> rfl
                      · rintro ⟨cur, lastDomain, index⟩
                        dsimp only
                        cases lastDomain with
                        | none => exact preserves_pure _
                        | some domain =>
                            dsimp only
                            cases Ix.AuxGen.decomposeApps domain with
                            | mk head args =>
                                dsimp only
                                cases head with
                                | const extName levels hash =>
                                    dsimp only
                                    cases env.get? extName with
                                    | none => exact preserves_pure _
                                    | some info =>
                                        cases info with
                                        | inductInfo ind =>
                                            dsimp only
                                            split <;> exact preserves_pure _
                                        | _ => exact preserves_pure _
                                | _ => exact preserves_pure _
                    · exact preserves_pure _
                | _ => exact preserves_pure _
            · rintro ⟨early, out, cur⟩
              cases early <;> exact preserves_pure _

/-- Includes every none/failed-match path, every aux-signature protection pass,
and arbitrary environment lookup answers. No target match is assumed. -/
theorem findSourceRecTargetWith_grows (dom : Expr) (originalAll : Array Name)
    (params : Array Expr) (env : Ix.Environment) (pfx : String)
    (fieldIndex : Nat) (auxSigs : Array AuxMotiveSig) :
    Preserves (Ix.AuxGen.findSourceRecTargetWith dom originalAll params env pfx fieldIndex auxSigs) := by
  unfold Ix.AuxGen.findSourceRecTargetWith
  apply preserves_bind
  · exact preserves_protect_inputs _ _
  · intro _
    apply preserves_bind
    · apply preserves_forIn_array
      intro sig _
      apply preserves_bind
      · exact preserves_protectExprs sig.specs
      · intro _
        exact preserves_pure _
    · intro _
      apply preserves_bind
      · refine preserves_repeat_congr _ _ (targetPeelStep pfx fieldIndex) ?_
          (targetPeelLoop_grows pfx fieldIndex _)
        rintro token ⟨cur, decls, fvars⟩
        cases cur <;> rfl
      · rintro ⟨cur, decls, fvars⟩
        dsimp only
        cases Ix.AuxGen.decomposeApps cur with
        | mk head args =>
            dsimp only
            cases head with
            | const targetName levels hash =>
                dsimp only
                cases originalAll.findIdx? (· == targetName) with
                | none =>
                    dsimp only
                    split <;> exact preserves_pure _
                | some sourcePos =>
                    dsimp only
                    cases env.get? targetName with
                    | none => exact preserves_pure _
                    | some info =>
                        dsimp only
                        cases info with
                        | inductInfo ind =>
                            dsimp only
                            split
                            · exact preserves_pure _
                            · apply preserves_bind
                              · apply preserves_forIn_range
                                intro index state
                                split <;> exact preserves_pure _
                              · intro early
                                split <;> exact preserves_pure _
                        | _ => exact preserves_pure _
            | _ => exact preserves_pure _

/-- The outer collector uses this concrete source reader, not a callback
premise asserting preservation for arbitrary fabricated TargetRead values. -/
theorem actualTargetRead_grows (rv : RecursorVal) (ps : Array Expr)
    (env : Ix.Environment) (auxSigs : Array AuxMotiveSig)
    (decl : LocalDecl) (index : Nat) (supply : FreshFVars) :
    Grows supply (actualTargetRead rv ps env auxSigs decl index supply).2 :=
  findSourceRecTargetWith_grows decl.domain rv.all ps env "split_xs" index auxSigs supply

theorem collectActualTargets_grows (rv : RecursorVal) (ps : Array Expr)
    (env : Ix.Environment) (auxSigs : Array AuxMotiveSig) (decls : Array LocalDecl)
    (supply : FreshFVars) (out : TargetState)
    (run : collectTargets (actualTargetRead rv ps env auxSigs) decls supply = .ok out) :
    Grows supply out.1 := by
  unfold collectTargets at run
  refine Ix.CompileCert.Canon.forIn_except_array _
    (fun _ state => Grows supply state.1) ?_ _ (grows_refl supply) run
  rintro _ ⟨decl, index⟩ ⟨current, entries⟩ step valid succeeded
  have grow := actualTargetRead_grows rv ps env auxSigs decl index current
  unfold targetStep at succeeded
  generalize actualTargetRead rv ps env auxSigs decl index current = answer at grow succeeded
  rcases answer with ⟨target, nextSupply⟩
  cases target with
  | none =>
      cases succeeded
      exact ⟨_, rfl, grows_trans valid grow⟩
  | some target =>
      cases succeeded
      exact ⟨_, rfl, grows_trans valid grow⟩

theorem prepareActualFields_grows (minorTy : Expr) (numFields : Nat) (supply : FreshFVars)
    (rv : RecursorVal) (ps : Array Expr) (env : Ix.Environment)
    (auxSigs : Array AuxMotiveSig) (unread : String) (out : TargetState)
    (run : prepareFields minorTy numFields supply (actualTargetRead rv ps env auxSigs) unread =
      .ok out) : Grows supply out.1 := by
  unfold prepareFields at run
  generalize observed : (Ix.AuxGen.peelBindersWith minorTy numFields "split_field" 0).run
    supply = answer at run
  rcases answer with ⟨fields, nextSupply⟩
  obtain ⟨parts, _, collected⟩ := except_bind_ok.1 run
  rcases parts with ⟨decls, _, _⟩
  have grow := peelBindersWith_grows minorTy numFields "split_field" 0 supply
  rw [observed] at grow
  exact grows_trans grow (collectActualTargets_grows rv ps env auxSigs decls nextSupply out collected)

/-- Exactly O11a's existing initial protected set. -/
def initialSupply (rv : RecursorVal) (ps ms mins : Array Expr) : FreshFVars :=
  (FreshFVars.protectExpr {} rv.cnst.type).protectExprs (ps ++ ms ++ mins)

theorem initialSupply_type (rv : RecursorVal) (ps ms mins : Array Expr) :
    Protects (initialSupply rv ps ms mins) rv.cnst.type :=
  protects_mono _ _ rv.cnst.type (protects_array_grows _ _)
    (protectExpr_protects {} rv.cnst.type)

theorem initialSupply_operand (rv : RecursorVal) (ps ms mins : Array Expr)
    (value : Expr) (member : value ∈ ps ++ ms ++ mins) :
    Protects (initialSupply rv ps ms mins) value :=
  protects_array_member _ _ value member

theorem initialSupply_minor (rv : RecursorVal) (ps ms mins : Array Expr)
    (index : Nat) (minor : Expr) (read : mins[index]? = some minor) :
    Protects (initialSupply rv ps ms mins) minor :=
  initialSupply_operand rv ps ms mins minor
    (Array.mem_append_right (ps ++ ms) (Array.mem_of_getElem? read))

/-- The first source reader preserves this full initial set even if it finds
no auxiliary signatures, including its early-return paths. -/
theorem initial_to_aux_grows (rv : RecursorVal) (levels : Array Level)
    (ps ms mins : Array Expr) (env : Ix.Environment) :
    Grows (initialSupply rv ps ms mins)
      ((Ix.AuxGen.auxMotiveSigsWith rv levels ps ms env).run
        (initialSupply rv ps ms mins)).2 :=
  auxMotiveSigsWith_grows rv levels ps ms env _

/-- Complete source-preparation transport, with the actual auxiliary and
target readers. Successful preparation is a local execution observation, not
a new source-domain or callback precondition. -/
theorem initial_to_prepared_grows (rv : RecursorVal) (levels : Array Level)
    (ps ms mins : Array Expr) (env : Ix.Environment) (minorTy : Expr)
    (numFields : Nat) (unread : String) (prepared : TargetState) :
    let aux := (Ix.AuxGen.auxMotiveSigsWith rv levels ps ms env).run
      (initialSupply rv ps ms mins)
    prepareFields minorTy numFields aux.2 (actualTargetRead rv ps env aux.1) unread =
        .ok prepared →
      Grows (initialSupply rv ps ms mins) prepared.1 := by
  dsimp only
  intro run
  exact grows_trans (initial_to_aux_grows rv levels ps ms mins env)
    (prepareActualFields_grows minorTy numFields _ rv ps env _ unread prepared run)

theorem prepared_minor_protected (rv : RecursorVal) (levels : Array Level)
    (ps ms mins : Array Expr) (env : Ix.Environment) (minorTy : Expr)
    (numFields index : Nat) (unread : String) (prepared : TargetState)
    (minor : Expr) (read : mins[index]? = some minor) :
    let aux := (Ix.AuxGen.auxMotiveSigsWith rv levels ps ms env).run
      (initialSupply rv ps ms mins)
    prepareFields minorTy numFields aux.2 (actualTargetRead rv ps env aux.1) unread =
        .ok prepared → Protects prepared.1 minor := by
  dsimp only
  intro run
  exact protects_mono _ _ minor
    (initial_to_prepared_grows rv levels ps ms mins env minorTy numFields unread prepared run)
    (initialSupply_minor rv ps ms mins index minor read)

/-- Every actual successful binder prefix retains protection of the original
minor and of its current opened body. The arbitrary instance callback may
return any result or error; no semantic callback/freshness law is used. -/
theorem prepared_prefix_protected (rv : RecursorVal) (levels : Array Level)
    (ps ms mins : Array Expr) (env : Ix.Environment) (minorTy : Expr)
    (numFields index : Nat) (unread : String) (prepared : TargetState)
    (minor : Expr) (read : mins[index]? = some minor)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (inBlock : Array Bool) (count : Nat) (out : BinderState) :
    let aux := (Ix.AuxGen.auxMotiveSigsWith rv levels ps ms env).run
      (initialSupply rv ps ms mins)
    prepareFields minorTy numFields aux.2 (actualTargetRead rv ps env aux.1) unread =
        .ok prepared →
      binderLoopWith rawFieldRead inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
        numFields index unread count prepared.1 minor = .ok out →
      Protects out.1 minor ∧ Protects out.1 out.2.1 := by
  dsimp only
  intro prepareRun loopRun
  have original := prepared_minor_protected rv levels ps ms mins env minorTy
    numFields index unread prepared minor read prepareRun
  have grow := binderLoop_grows inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
    numFields index unread count prepared.1 minor out loopRun
  have retained := protects_mono prepared.1 out.1 minor grow original
  refine ⟨retained, ?_⟩
  intro key occurs
  rcases binderLoop_source_support inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
      numFields index unread count prepared.1 minor out loopRun key occurs with old | allocated
  · exact retained key old
  · exact allocated

/-- The next actual allocator call avoids the current minor body without a
caller-supplied freshness condition or an extra protection pass. -/
theorem prepared_prefix_next_fresh (rv : RecursorVal) (levels : Array Level)
    (ps ms mins : Array Expr) (env : Ix.Environment) (minorTy : Expr)
    (numFields index : Nat) (unread : String) (prepared : TargetState)
    (minor : Expr) (read : mins[index]? = some minor)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (inBlock : Array Bool) (count : Nat) (out : BinderState) :
    let aux := (Ix.AuxGen.auxMotiveSigsWith rv levels ps ms env).run
      (initialSupply rv ps ms mins)
    prepareFields minorTy numFields aux.2 (actualTargetRead rv ps env aux.1) unread =
        .ok prepared →
      binderLoopWith rawFieldRead inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
        numFields index unread count prepared.1 minor = .ok out →
      ¬ Occurs (Ix.Compile.Canon.keyName (out.1.fresh "o11a" count).1.1) out.2.1 := by
  dsimp only
  intro prepareRun loopRun occurs
  have covered := (prepared_prefix_protected rv levels ps ms mins env minorTy
    numFields index unread prepared minor read inst? inBlock count out prepareRun loopRun).2
  exact fresh_not_mem out.1 "o11a" count (covered _ occurs)

/-- This projection starts from the public helper's success itself, and
obtains all preparation/binder witnesses internally. The inherited full
Except equality remains the connection for errors and optional absence. -/
theorem sizeOfMinorWith_success_protection (env : OptEnv)
    (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (levels : Array Level)
    (ps ms mins : Array Expr) (index : Nat) (output : Expr)
    (run : sizeOfMinorWith env inst? rv inBlock levels ps ms mins index = .ok (some output)) :
    ∃ opened : BinderState,
      output = Ix.AuxGen.mkLambda opened.2.1 opened.2.2.1 ∧
      Grows (initialSupply rv ps ms mins) opened.1 ∧
      Protects opened.1 rv.cnst.type ∧
      (∀ value ∈ ps ++ ms ++ mins, Protects opened.1 value) ∧
      Protects opened.1 opened.2.1 := by
  obtain ⟨_, ctor, minorTy, prepared, minor, opened, _, _, prepareRun,
    minorRead, loopRun, _, _, outputEq⟩ :=
    sizeOfMinorWith_success_fields env inst? rv inBlock levels ps ms mins index output run
  have grow := grows_trans
    (initial_to_prepared_grows rv levels ps ms mins env.ienv minorTy ctor.numFields
      _ prepared prepareRun)
    (binderLoop_grows inst? rv inBlock prepared.2 (ps ++ ms ++ mins)
      ctor.numFields index _ _ prepared.1 minor opened loopRun)
  refine ⟨opened, outputEq, grow,
    protects_mono _ _ _ grow (initialSupply_type rv ps ms mins), ?_, ?_⟩
  · intro value member
    exact protects_mono _ _ value grow (initialSupply_operand rv ps ms mins value member)
  · exact (prepared_prefix_protected rv levels ps ms mins env.ienv minorTy
      ctor.numFields index _ prepared minor minorRead inst? inBlock _ opened prepareRun loopRun).2

/-- Valid open-input neighbour: no forall means no allocation by the repeat,
and the complete initial loop state and supply are retained. -/
theorem target_repeat_fvar_neighbour (name : Name) (hash : _root_.Address)
    (decls : Array LocalDecl) (fvars : Array Expr) (pfx : String) (index : Nat)
    (supply : FreshFVars) :
    (Lean.Loop.forIn {} (.fvar name hash, decls, fvars)
      (targetPeelStep pfx index)).run supply = ((.fvar name hash, decls, fvars), supply) := by
  rw [state_repeat_eq]
  rfl

/-- A non-FVar replacement can introduce a forall, so the progress lemma
must use the allocator's actual FVar result. This does not narrow the raw
opening helper's independent arbitrary-replacement contract. -/
theorem nonFVar_replacement_depth_control (name : Name) (domain : Expr)
    (info : Lean.BinderInfo) (hash : _root_.Address) :
    forallDepth (Ix.AuxGen.instantiate1At (.bvar 0 hash)
      (.forallE name domain (.fvar name hash) info hash) 0) = 1 ∧
      forallDepth (.bvar 0 hash) = 0 := by
  rw [opening_target_as_is]
  exact ⟨rfl, rfl⟩

end Ix.CompileCert.Opt.O11aReaderGrowth
