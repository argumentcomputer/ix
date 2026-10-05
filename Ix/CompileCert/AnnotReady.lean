import Ix.CompileCert.AnnotLaws

/-! Literal support follows from actual successful annotation readings.
This lets rule transport discharge its literal premises from the independent
installed models, without adding a global support flag or source-domain guard. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

def literalReady (env : Kernel.Env) : Kernel.Expr → Bool
  | .lit (.natVal _) => Kernel.natLitSupported env
  | .lit (.strVal _) => Kernel.strLitSupported env
  | .app f a => literalReady env f && literalReady env a
  | .lam ty body _ | .forallE ty body _ => literalReady env ty && literalReady env body
  | .proj _ _ e => literalReady env e
  | _ => true

theorem literalReady_instantiateFVar (env : Kernel.Env) (e : Kernel.Expr)
    (index : Nat) (type : Kernel.Expr) (k : Nat) :
    literalReady env (e.instantiate1 (.fvar index type) k) = literalReady env e := by
  induction e generalizing k with
  | bvar i =>
    simp only [Kernel.Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | lit => rfl
  | app f a ihf iha => simp only [Kernel.Expr.instantiate1, literalReady, ihf, iha]
  | lam ty body metadata iht ihb => simp only [Kernel.Expr.instantiate1, literalReady, iht, ihb]
  | forallE ty body metadata iht ihb => simp only [Kernel.Expr.instantiate1, literalReady, iht, ihb]
  | proj owner field e ih => exact ih k
  | letE => rfl

theorem literalReady_of_reading {env : Kernel.Env}
    {acval : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm} {levels : Kernel.Name → Nat}
    {d : Nat} {e : Kernel.Expr} {annotation : AnnotTerm}
    (reading : denoteMeta acval env levels d e = some annotation) : literalReady env e = true := by
  induction d, e using denoteMeta.induct (env := env) generalizing annotation with
  | case1 => rfl
  | case2 => rfl
  | case3 => rfl
  | case4 => rfl
  | case5 => rfl
  | case6 d ty body mb iht ihb =>
    rw [denoteMeta] at reading
    cases ht : denoteMeta acval env levels d ty with
    | none => simp [ht] at reading
    | some ta =>
      cases hb : denoteMeta acval env levels (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => simp [ht, hb] at reading
      | some ba =>
        have bodyReady := ihb hb
        rw [literalReady_instantiateFVar] at bodyReady
        simp only [literalReady, iht ht, bodyReady, Bool.and_self]
  | case7 d ty body mb iht ihb =>
    rw [denoteMeta] at reading
    cases ht : denoteMeta acval env levels d ty with
    | none => simp [ht] at reading
    | some ta =>
      cases hb : denoteMeta acval env levels (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => simp [ht, hb] at reading
      | some ba =>
        have bodyReady := ihb hb
        rw [literalReady_instantiateFVar] at bodyReady
        simp only [literalReady, iht ht, bodyReady, Bool.and_self]
  | case8 d f a ihf iha =>
    obtain ⟨fa, aa, hf, ha, _⟩ := denoteMeta_app_inv reading
    simp only [literalReady, ihf hf, iha ha, Bool.and_self]
  | case9 => rfl
  | case10 d owner field operand ih =>
    rw [denoteMeta] at reading
    cases h : denoteMeta acval env levels d operand with
    | none => simp [h] at reading
    | some value => exact ih h
  | case11 d n supported => exact supported
  | case12 d n unsupported => simp [denoteMeta, unsupported] at reading
  | case13 d s supported => exact supported
  | case14 d s unsupported => simp [denoteMeta, unsupported] at reading
  | case15 d e hs hf hc hp hl ha he hj hn ht =>
    cases e with
    | bvar => rfl
    | sort u => exact absurd rfl (hs u)
    | fvar i t => exact absurd rfl (hf i t)
    | const n us => exact absurd rfl (hc n us)
    | forallE t b m => exact absurd rfl (hp t b m)
    | lam t b m => exact absurd rfl (hl t b m)
    | app f a => exact absurd rfl (ha f a)
    | letE t v b => exact absurd rfl (he t v b)
    | proj n i e => exact absurd rfl (hj n i e)
    | lit l => cases l with
      | natVal n => exact absurd rfl (hn n)
      | strVal s => exact absurd rfl (ht s)

/-- A successful structural comparison plus independently readable inputs
discharges expression-local literal agreement. Extra ambient target support
is irrelevant when the expression does not use it. -/
theorem checkInstalledExpr_literal_support {sourceEnv targetEnv : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} {image : UniverseImage}
    {source target : Kernel.Expr}
    (checked : checkInstalledExpr sourceEnv targetEnv names image source target = some true)
    (sourceReady : literalReady sourceEnv source = true)
    (targetReady : literalReady targetEnv target = true) :
    checkExprLiteralSupport sourceEnv targetEnv source = true := by
  induction source generalizing target with
  | bvar => rfl
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | letE => rfl
  | app f a ihf iha =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case app tf ta =>
      obtain ⟨cf, ca⟩ := bothChecks_true checked
      have sr : literalReady sourceEnv f = true ∧ literalReady sourceEnv a = true := by
        simpa only [literalReady, Bool.and_eq_true] using sourceReady
      have tr : literalReady targetEnv tf = true ∧ literalReady targetEnv ta = true := by
        simpa only [literalReady, Bool.and_eq_true] using targetReady
      simp only [checkExprLiteralSupport, ihf cf sr.1 tr.1, iha ca sr.2 tr.2, Bool.and_self]
  | lam ty body metadata iht ihb =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case lam tt tb tm =>
      obtain ⟨_, parts⟩ := bothChecks_true checked
      obtain ⟨ct, cb⟩ := bothChecks_true parts
      have sr : literalReady sourceEnv ty = true ∧ literalReady sourceEnv body = true := by
        simpa only [literalReady, Bool.and_eq_true] using sourceReady
      have tr : literalReady targetEnv tt = true ∧ literalReady targetEnv tb = true := by
        simpa only [literalReady, Bool.and_eq_true] using targetReady
      simp only [checkExprLiteralSupport, iht ct sr.1 tr.1, ihb cb sr.2 tr.2, Bool.and_self]
  | forallE ty body metadata iht ihb =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case forallE tt tb tm =>
      obtain ⟨_, parts⟩ := bothChecks_true checked
      obtain ⟨ct, cb⟩ := bothChecks_true parts
      have sr : literalReady sourceEnv ty = true ∧ literalReady sourceEnv body = true := by
        simpa only [literalReady, Bool.and_eq_true] using sourceReady
      have tr : literalReady targetEnv tt = true ∧ literalReady targetEnv tb = true := by
        simpa only [literalReady, Bool.and_eq_true] using targetReady
      simp only [checkExprLiteralSupport, iht ct sr.1 tr.1, ihb cb sr.2 tr.2, Bool.and_self]
  | proj owner field e ih =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case proj _ _ _ => exact ih (bothChecks_true checked).2 sourceReady targetReady
  | lit value =>
    cases target <;> try simp only [checkInstalledExpr] at checked <;> try contradiction
    case lit other =>
      cases value <;> cases other <;> simp only [checkInstalledExpr] at checked <;> try contradiction
      all_goals
        simp only [literalReady] at sourceReady targetReady
        simp only [checkExprLiteralSupport, sourceReady, targetReady, decide_true]

theorem checkInstalledExpr_literal_support_of_readings {sourceEnv targetEnv : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} {image : UniverseImage}
    {source target : Kernel.Expr}
    {sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm}
    {sourceLevels targetLevels : Kernel.Name → Nat} {sourceDepth targetDepth : Nat}
    {sourceAnnotation targetAnnotation : AnnotTerm}
    (checked : checkInstalledExpr sourceEnv targetEnv names image source target = some true)
    (sourceRead : denoteMeta sourceValues sourceEnv sourceLevels sourceDepth source = some sourceAnnotation)
    (targetRead : denoteMeta targetValues targetEnv targetLevels targetDepth target = some targetAnnotation) :
    checkExprLiteralSupport sourceEnv targetEnv source = true :=
  checkInstalledExpr_literal_support checked (literalReady_of_reading sourceRead) (literalReady_of_reading targetRead)

theorem checkInstalledMemberExpr_literal_support_of_readings {sourceEnv targetEnv : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} {name : Kernel.Name} {source target : Kernel.Expr}
    {sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm}
    {sourceLevels targetLevels : Kernel.Name → Nat} {sourceDepth targetDepth : Nat}
    {sourceAnnotation targetAnnotation : AnnotTerm}
    (checked : checkInstalledMemberExpr sourceEnv targetEnv names name source target = some true)
    (sourceRead : denoteMeta sourceValues sourceEnv sourceLevels sourceDepth source = some sourceAnnotation)
    (targetRead : denoteMeta targetValues targetEnv targetLevels targetDepth target = some targetAnnotation) :
    checkExprLiteralSupport sourceEnv targetEnv source = true := by
  cases sourceLookup : sourceEnv.find? name with
  | none => simp [checkInstalledMemberExpr, sourceLookup] at checked
  | some sourceEntry =>
    cases targetLookup : targetEnv.find? (names name) with
    | none => simp [checkInstalledMemberExpr, sourceLookup, targetLookup] at checked
    | some targetEntry =>
      simp only [checkInstalledMemberExpr, sourceLookup, targetLookup] at checked
      split at checked
      · exact checkInstalledExpr_literal_support_of_readings checked sourceRead targetRead
      · contradiction

/-- Type-literal guards are already entailed by the two actual installations
and the existing all-row type comparison. Their execution is not an extra
restriction on independently admitted source/target pairs. -/
theorem checkTypeLiteralSupport_of_installed {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} (sourceModel : StrongInstalledModel V source)
    (targetModel : StrongInstalledModel V target) {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledTypes source target names = true) :
    checkTypeLiteralSupport source target = true := by
  apply List.all_eq_true.mpr
  intro entry present
  obtain ⟨_, targetEntry, targetLookup, compared⟩ := checkInstalledTypes_member checked present
  obtain ⟨sourceAnnotation, sourceRead⟩ := sourceModel.internal.type_reads entry present (fun _ => 0)
  obtain ⟨targetAnnotation, targetRead⟩ := targetModel.internal.type_reads targetEntry
    (Kernel.Semantics.Env.find?_mem targetLookup) (fun _ => 0)
  exact checkInstalledMemberExpr_literal_support_of_readings compared sourceRead targetRead

theorem checkDefinitionLiteralSupport_of_installed {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} (sourceModel : StrongInstalledModel V source)
    (targetModel : StrongInstalledModel V target) {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledDefinitions source target names = true) :
    checkDefinitionLiteralSupport source target = true := by
  apply List.all_eq_true.mpr
  intro entry present
  cases entry with
  | defnInfo header value hint =>
    obtain ⟨_, targetHeader, targetValue, targetHint, targetLookup, compared⟩ :=
      checkInstalledDefinitions_member checked present
    have sourceRead := sourceModel.internal.defn_reads (fun _ => 0) header value ⟨hint, present⟩
    have targetRead := targetModel.internal.defn_reads (fun _ => 0) targetHeader targetValue
      ⟨targetHint, Kernel.Semantics.Env.find?_mem targetLookup⟩
    exact checkInstalledMemberExpr_literal_support_of_readings compared sourceRead targetRead
  | _ => rfl

/-- On the stated independently installed source/target premises, the local
literal guards cannot reject a pair accepted by the prior association and
reserved-name check. This does not infer source installation from the target. -/
theorem checkAnnotatedAssociation_of_installed {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} (sourceModel : StrongInstalledModel V source)
    (targetModel : StrongInstalledModel V target) {names : Kernel.Name → Kernel.Name}
    (association : checkInstalledAssociation source target names = some true)
    (reserved : checkReservedNameMap source names = true) :
    checkAnnotatedAssociation source target names = some true := by
  have fields := checkInstalledAssociation_sound association
  have types := checkTypeLiteralSupport_of_installed sourceModel targetModel fields.types
  have definitions := checkDefinitionLiteralSupport_of_installed sourceModel targetModel fields.definitions
  simp only [checkAnnotatedAssociation, association, reserved, types, definitions, bothChecks, Bool.and_self]

end Ix.CompileCert
