module

public import Ix.IxonMode

/-!
# Source contracts before canonicalization

These records refer to elaborated source syntax, before source sharing,
canonicalization, specialization, or erasure. They carry intent; they do not
prove that a term satisfies a usage or ownership discipline.

The input owns both its selected constants and its explicit contract registry.
No environment extension or source file is needed to validate this data.
-/

public section

namespace Ix.Compile

/-- The two expression roots of a source declaration. -/
inductive SourceRoot where
  | type
  | body
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable, Ord

/-- A structural edge in the elaborated expression tree. Metadata wrappers
are explicit edges, so two occurrences of an equal subterm stay distinct. -/
inductive SourceStep where
  | appFn
  | appArg
  | binderType
  | binderBody
  | letType
  | letValue
  | letBody
  | metadata
  | projection
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable, Ord

/-- A binder occurrence, independent of its name or source location. -/
structure BinderSite where
  root : SourceRoot
  path : List SourceStep := []
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable, Ord

inductive SourceBinderKind where
  | lam
  | all
  deriving BEq, DecidableEq, Repr, Inhabited

/-- An explicit source annotation. `owned` describes the bound value (`! x`),
independently of `resultOwned`, which describes an arrow's result. A region
names a declaration parameter; it does not create a loan. -/
structure BinderContract where
  site : BinderSite
  uses : Ixon.Uses
  resultOwned : Option Ixon.Owned := none
  owned : Ixon.Owned := .shared
  region : Option Lean.Name := none
  deriving BEq, Repr, Inhabited

/-- Contract binding uses an exact source snapshot, including the type, body,
universe parameters, binder information, and metadata. The snapshot is shared
Lean data, not a second environment. In particular, a 64-bit expression hash
alone cannot authorize reusing contracts for different source syntax. -/
structure SourceContract where
  source : Lean.ConstantInfo
  binders : Array BinderContract
  regions : Array Lean.Name := #[]
  deriving Repr, Inhabited

/-- User-facing selectors are resolved once to elaborated telescope positions.
Positions are zero-based and include implicit and instance arguments. -/
inductive BinderSelector where
  | position (index : Nat)
  | name (name : Lean.Name)
  deriving BEq, Repr, Inhabited

/-- Declaration shorthand that annotates corresponding type/body binders.
Bound-value ownership and region apply to both occurrences; result ownership
applies only to this position's arrow. -/
structure TelescopeContract where
  binder : BinderSelector
  uses : Ixon.Uses
  resultOwned : Option Ixon.Owned := none
  owned : Ixon.Owned := .shared
  region : Option Lean.Name := none
  deriving Repr, Inhabited

/-- Optional recursion information, bound to the exact source declaration.
The argument position includes erased, implicit, and instance binders. A
fixed-step proposal neither inserts fuel nor certifies target termination. -/
structure MeasureHint where
  source : Lean.ConstantInfo
  argument : BinderSelector
  fixedStep : Option Nat := none
  deriving Repr, Inhabited

/-- Pure frontend input. Semantic contracts have no implicit empty default.
Plain-source callers must opt into the explicitly named convenience API. -/
structure CompileInput where
  constants : List (Lean.Name × Lean.ConstantInfo)
  contracts : Array SourceContract
  measureHints : Array MeasureHint := #[]

def CompileInput.plain (constants : List (Lean.Name × Lean.ConstantInfo)) : CompileInput :=
  { constants, contracts := #[] }

/-- Diagnostic names and binder information are retained after resolving a
site. On arrows, resultOwned is always populated, including the shared default.
On lambdas it is absent. -/
structure ResolvedBinderContract where
  site : BinderSite
  kind : SourceBinderKind
  name : Lean.Name
  binderInfo : Lean.BinderInfo
  uses : Ixon.Uses
  resultOwned : Option Ixon.Owned
  owned : Ixon.Owned
  /-- Zero-based index into this declaration's region parameters. -/
  region : Option Nat
  deriving Repr, Inhabited

structure ResolvedSourceContract where
  source : Lean.ConstantInfo
  binders : Array ResolvedBinderContract
  /-- Names are diagnostic source data; resolved references use bound indices. -/
  regions : Array Lean.Name
  deriving Repr, Inhabited

/-- The resolved assertion at one source occurrence, without diagnostic names.
This is source contract data, not an Ixon expression or wire encoding. -/
structure BinderContractSemantics where
  site : BinderSite
  kind : SourceBinderKind
  uses : Ixon.Uses
  resultOwned : Option Ixon.Owned
  owned : Ixon.Owned
  region : Option Nat
  deriving BEq, Repr, Inhabited

/-- Region parameters are identified by their binding positions. Names and the
exact source snapshot belong to validation and diagnostics, not these assertions.
Source paths still refer to the elaborated tree; do not hash this as an artifact. -/
structure SourceContractSemantics where
  regionParameterCount : Nat
  binders : Array BinderContractSemantics
  deriving BEq, Repr, Inhabited

def ResolvedSourceContract.semantics (contract : ResolvedSourceContract) : SourceContractSemantics :=
  { regionParameterCount := contract.regions.size
    binders := contract.binders.map fun binder => {
      site := binder.site, kind := binder.kind, uses := binder.uses
      resultOwned := binder.resultOwned, owned := binder.owned, region := binder.region } }

structure ResolvedMeasureHint where
  source : Lean.ConstantInfo
  argument : Nat
  site : BinderSite
  fixedStep : Option Nat
  deriving Repr, Inhabited

/-- Validation output for transport into a compiler. A consumer accepting
untrusted serialized records must rerun validation; a record is not a proof. -/
structure ResolvedCompileInput where
  constants : List (Lean.Name × Lean.ConstantInfo)
  contracts : Array ResolvedSourceContract
  measureHints : Array ResolvedMeasureHint

inductive SourceContractError where
  | missingDeclaration (name : Lean.Name)
  | duplicateDeclaration (name : Lean.Name)
  | declarationNameMismatch (key actual : Lean.Name)
  | duplicateContract (name : Lean.Name)
  | staleSource (name : Lean.Name)
  | invalidSite (name : Lean.Name) (site : BinderSite)
  | expectedBinder (name : Lean.Name) (site : BinderSite)
  | ownershipOnLambda (name : Lean.Name) (site : BinderSite)
  | duplicateSite (name : Lean.Name) (site : BinderSite)
  | argumentOutOfRange (name : Lean.Name) (index : Nat)
  | unknownBinder (declaration binder : Lean.Name)
  | ambiguousBinder (declaration binder : Lean.Name)
  | missingBodyBinder (name : Lean.Name) (index : Nat)
  | inconsistentTelescope (name : Lean.Name) (index : Nat)
      (typeUses bodyUses : Ixon.Uses)
  | inconsistentOwnership (name : Lean.Name) (index : Nat)
      (typeOwned bodyOwned : Ixon.Owned)
  | inconsistentRegion (name : Lean.Name) (index : Nat)
      (typeRegion bodyRegion : Option Nat)
  | duplicateRegion (declaration region : Lean.Name)
  | unknownRegion (declaration region : Lean.Name)
  | conflictingRegions (declaration : Lean.Name)
  | annotatedRecursorRule (declaration : Lean.Name)
  | malformedAnnotation (declaration : Lean.Name) (site : BinderSite) (reason : String)
  | misplacedAnnotation (declaration : Lean.Name) (site : BinderSite)
  | annotationBinderMismatch (declaration : Lean.Name) (site : BinderSite)
      (expected actual : Lean.Name)
  | duplicateAnnotation (declaration : Lean.Name) (root : SourceRoot) (origin : Nat)
  | missingAnnotation (declaration : Lean.Name) (site : BinderSite)
  | conflictingAnnotation (declaration : Lean.Name) (site : BinderSite)
  | missingContract (declaration : Lean.Name)
  | duplicateMeasure (name : Lean.Name)
  | zeroFixedStep (name : Lean.Name)
  deriving BEq, Repr

instance : ToString SourceContractError where
  toString error := s!"source contract: {repr error}"

end Ix.Compile

end
