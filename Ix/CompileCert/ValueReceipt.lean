import Ix.CompileCert.AnnotEntry

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- A closed target value equation with explicitly bound endpoints and
universes. The certificate name merely selects a row: its complete theorem
type and telescope must match this request. -/
structure ValueEquationRequest where
  certificate : Kernel.Name
  levelParams : List Kernel.Name
  level : Kernel.Level
  carrier : Kernel.Expr
  left : Kernel.Name
  leftLevels : List Kernel.Level
  right : Kernel.Name
  rightLevels : List Kernel.Level

def ValueEquationRequest.type (request : ValueEquationRequest) : Kernel.Expr :=
  .app (.app (.app (.const Kernel.eqName [request.level]) request.carrier)
    (.const request.left request.leftLevels)) (.const request.right request.rightLevels)

structure CheckedValueEquation (env : Kernel.Env) (request : ValueEquationRequest) where
  header : Kernel.ConstantVal
  proof : Kernel.Expr
  lookup : env.find? request.certificate = some (.thmInfo header proof)
  parameters : header.levelParams = request.levelParams
  statement : header.type = request.type

inductive ValueEquationEvidence (env : Kernel.Env) (request : ValueEquationRequest) : Prop
  | identity (name : request.left = request.right) (levels : request.leftLevels = request.rightLevels)
  | theoremRow (checked : CheckedValueEquation env request)

structure CheckedValueEndpoints (env : Kernel.Env) (request : ValueEquationRequest) where
  leftEntry : Kernel.ConstantInfo
  rightEntry : Kernel.ConstantInfo
  leftLookup : env.find? request.left = some leftEntry
  rightLookup : env.find? request.right = some rightEntry
  leftArity : request.leftLevels.length = leftEntry.toConstantVal.levelParams.length
  rightArity : request.rightLevels.length = rightEntry.toConstantVal.levelParams.length
  closed : request.type.looseBVarsBounded 0 = true ∧ request.type.hasFvar = false ∧
    request.type.allLevelParamsDefined request.levelParams = true
  evidence : ValueEquationEvidence env request

/-- Identical actual endpoints need no additional theorem. Otherwise this
reads an exact installed theorem row; it never substitutes a same-named
definition/axiom, reverse alias, or unverified certificate payload. -/
def readCheckedValueEndpoints (env : Kernel.Env) (request : ValueEquationRequest) :
    Option (CheckedValueEndpoints env request) := do
  let some leftEntry := env.find? request.left | none
  let some rightEntry := env.find? request.right | none
  if leftLookup : env.find? request.left = some leftEntry then
    if rightLookup : env.find? request.right = some rightEntry then
      if leftArity : request.leftLevels.length = leftEntry.toConstantVal.levelParams.length then
        if rightArity : request.rightLevels.length = rightEntry.toConstantVal.levelParams.length then
          if closed : request.type.looseBVarsBounded 0 = true ∧ request.type.hasFvar = false ∧
              request.type.allLevelParamsDefined request.levelParams = true then
            if same : request.left = request.right ∧ request.leftLevels = request.rightLevels then
              some ⟨leftEntry, rightEntry, leftLookup, rightLookup, leftArity, rightArity, closed,
                .identity same.1 same.2⟩
            else
              let some (.thmInfo header proof) := env.find? request.certificate | none
              if lookup : env.find? request.certificate = some (.thmInfo header proof) then
                if parameters : header.levelParams = request.levelParams then
                  if statement : header.type = request.type then
                    some ⟨leftEntry, rightEntry, leftLookup, rightLookup, leftArity, rightArity, closed,
                      .theoremRow ⟨header, proof, lookup, parameters, statement⟩⟩
                  else none
                else none
              else none
          else none
        else none
      else none
    else none
  else none

/-- Equality is obtained from the actual target model's checked theorem
grading and membership. An unchecked environment row cannot supply the
independent StrongInstalledModel premise. -/
theorem CheckedValueEndpoints.value_eq {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {request : ValueEquationRequest}
    (receipt : CheckedValueEndpoints env request) (target : StrongInstalledModel V env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    target.public.cval request.left
      (Kernel.Level.substFn levels receipt.leftEntry.toConstantVal.levelParams request.leftLevels) =
    target.public.cval request.right
      (Kernel.Level.substFn levels receipt.rightEntry.toConstantVal.levelParams request.rightLevels) := by
  cases receipt.evidence with
  | identity sameName sameLevels =>
    have sameEntry : receipt.leftEntry = receipt.rightEntry := by
      have lookup := receipt.leftLookup
      rw [sameName, receipt.rightLookup] at lookup
      exact (Option.some.inj lookup).symm
    rw [sameName, sameLevels, sameEntry]
  | theoremRow certificate =>
    apply target.theorem_eq certificate.header certificate.proof (Kernel.Semantics.Env.find?_mem certificate.lookup)
      (levels := levels) (ρ := ρ) (arguments := [])
    · rw [certificate.statement]
      exact InstalledTelescope.nil
    · exact Kernel.Denotes.const receipt.leftLookup receipt.leftArity
    · exact Kernel.Denotes.const receipt.rightLookup receipt.rightArity

/-- The map binding is constructed, not supplied as an unbound left-hand
endpoint. This operation-family interface is monomorphic; general universe
instances remain explicit in ValueEquationRequest above. -/
def mappedValueRequest (names : Kernel.Name → Kernel.Name) (sourceName canonical certificate : Kernel.Name)
    (level : Kernel.Level) (carrier : Kernel.Expr) : ValueEquationRequest :=
  ⟨certificate, [], level, carrier, names sourceName, [], canonical, []⟩

structure CheckedMappedValue (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (sourceName canonical certificate : Kernel.Name) (level : Kernel.Level) (carrier : Kernel.Expr) where
  sourceEntry : Kernel.ConstantInfo
  sourceLookup : source.find? sourceName = some sourceEntry
  sourceMonomorphic : sourceEntry.toConstantVal.levelParams = []
  endpoints : CheckedValueEndpoints target (mappedValueRequest names sourceName canonical certificate level carrier)

def readCheckedMappedValue (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (sourceName canonical certificate : Kernel.Name) (level : Kernel.Level) (carrier : Kernel.Expr) :
    Option (CheckedMappedValue source target names sourceName canonical certificate level carrier) := do
  let some sourceEntry := source.find? sourceName | none
  if sourceLookup : source.find? sourceName = some sourceEntry then
    if sourceMonomorphic : sourceEntry.toConstantVal.levelParams = [] then
      let endpoints ← readCheckedValueEndpoints target (mappedValueRequest names sourceName canonical certificate level carrier)
      some ⟨sourceEntry, sourceLookup, sourceMonomorphic, endpoints⟩
    else none
  else none

/-- Both the identity and admitted-theorem cases yield equality on the exact
existing pulled carrier. No source operation name is forced to map to itself.
This is semantic receipt soundness, not a completeness claim for its producer. -/
theorem CheckedMappedValue.value_eq {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {sourceName canonical certificate : Kernel.Name} {level : Kernel.Level} {carrier : Kernel.Expr}
    (receipt : CheckedMappedValue source target names sourceName canonical certificate level carrier)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    interp V ρ ((association.modelCore sourceFacts targetModel).base.acval sourceName levels) =
      interp V ρ (targetModel.internal.base2.acval canonical levels) := by
  have leftParams : receipt.endpoints.leftEntry.toConstantVal.levelParams = [] := by
    have arity := receipt.endpoints.leftArity
    exact List.eq_nil_of_length_eq_zero arity.symm
  have rightParams : receipt.endpoints.rightEntry.toConstantVal.levelParams = [] := by
    have arity := receipt.endpoints.rightArity
    exact List.eq_nil_of_length_eq_zero arity.symm
  have result := receipt.endpoints.value_eq targetModel levels ρ
  simp only [mappedValueRequest, leftParams, rightParams, Kernel.Level.substFn] at result
  have targetLookup : target.find? (names sourceName) = some receipt.endpoints.leftEntry := receipt.endpoints.leftLookup
  have carrierEq : (association.modelCore sourceFacts targetModel).base.acval sourceName levels =
      targetModel.internal.base2.acval (names sourceName) levels := by
    change (PullbackMap.fromEnvs source target names).annotations targetModel.internal.base2.acval sourceName levels = _
    simp only [PullbackMap.annotations, PullbackMap.fromEnvs, receipt.sourceLookup,
      targetLookup, receipt.sourceMonomorphic, leftParams, List.map_nil, Kernel.Level.substFn]
  rw [carrierEq]
  simpa only [StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM,
    interp_cvalOf targetModel.internal.base2.cval_closedL] using result

end Ix.CompileCert
