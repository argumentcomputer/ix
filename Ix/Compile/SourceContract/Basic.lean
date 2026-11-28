module

public import Ix.Common
public import IxCK.Ixon.Types.Modes

/-!
# Source contracts before canonicalization

These records refer to elaborated source syntax, before source sharing,
canonicalization, specialization, or erasure. They carry intent directly in the
Ixon v5 mode vocabulary (`Ixon.BinderMode`, `Ixon.ResultMode`, `Ixon.LetMode`,
`Ixon.FieldMode`, `Ixon.DefAsserts`); they do not prove that a term satisfies a
resource discipline.

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
  | letE
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Independent input and result modes at a binder occurrence. `isBorrow` is
meaningful only at a `letE` occurrence with `mode = .borrowed` (`LetMode.borrow`). -/
structure BinderContract where
  site : BinderSite
  mode : Ixon.BinderMode := .many
  result : Option Ixon.ResultMode := none
  isBorrow : Bool := false
  deriving BEq, Repr, Inhabited

/-- A constructor field's `FieldMode` (`inherited` or `shared`), indexed by
zero-based field position past `numParams`. -/
structure FieldModeContract where
  fieldIndex : Nat
  mode : Ixon.FieldMode := .inherited
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Contract binding uses an exact source snapshot, including the type, body,
universe parameters, binder information, and metadata. The snapshot is shared
Lean data, not a second environment. In particular, a 64-bit expression hash
alone cannot authorize reusing contracts for different source syntax. -/
structure SourceContract where
  source : Lean.ConstantInfo
  binders : Array BinderContract := #[]
  fieldModes : Array FieldModeContract := #[]
  defAsserts : Ixon.DefAsserts := {}
  deriving Repr, Inhabited

/-- User-facing selectors are resolved once to elaborated telescope positions.
Positions are zero-based and include implicit and instance arguments. -/
inductive BinderSelector where
  | position (index : Nat)
  | name (name : Lean.Name)
  deriving BEq, Repr, Inhabited

/-- Declaration shorthand that annotates corresponding type/body binders.
The input mode applies to both occurrences; the independent result mode
applies only to this position's arrow. -/
structure TelescopeContract where
  binder : BinderSelector
  mode : Ixon.BinderMode := .many
  result : Option Ixon.ResultMode := none
  isBorrow : Bool := false
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
site. On arrows, `result` is always populated, including the shared default.
On lambdas and lets it is absent. -/
structure ResolvedBinderContract where
  site : BinderSite
  kind : SourceBinderKind
  name : Lean.Name
  binderInfo : Lean.BinderInfo
  mode : Ixon.BinderMode
  result : Option Ixon.ResultMode
  isBorrow : Bool
  deriving Repr, Inhabited

structure ResolvedSourceContract where
  source : Lean.ConstantInfo
  binders : Array ResolvedBinderContract
  fieldModes : Array FieldModeContract := #[]
  defAsserts : Ixon.DefAsserts := {}
  deriving Repr, Inhabited

/-- The resolved assertion at one source occurrence, without diagnostic names.
This is source contract data, not an Ixon expression or wire encoding. -/
structure BinderContractSemantics where
  site : BinderSite
  kind : SourceBinderKind
  mode : Ixon.BinderMode
  result : Option Ixon.ResultMode
  isBorrow : Bool
  deriving BEq, Repr, Inhabited

/-- Names and the exact source snapshot belong to validation and diagnostics.
Source paths still refer to the elaborated tree; do not hash this as an artifact. -/
structure SourceContractSemantics where
  binders : Array BinderContractSemantics
  fieldModes : Array FieldModeContract := #[]
  defAsserts : Ixon.DefAsserts := {}
  deriving BEq, Repr, Inhabited

def ResolvedSourceContract.semantics (contract : ResolvedSourceContract) : SourceContractSemantics :=
  { binders := contract.binders.map fun binder => {
      site := binder.site, kind := binder.kind, mode := binder.mode
      result := binder.result, isBorrow := binder.isBorrow }
    fieldModes := contract.fieldModes
    defAsserts := contract.defAsserts }

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
  | resultOnNonArrow (name : Lean.Name) (site : BinderSite)
  | borrowOnNonLet (name : Lean.Name) (site : BinderSite)
  | invalidBorrowView (name : Lean.Name) (site : BinderSite)
  | duplicateSite (name : Lean.Name) (site : BinderSite)
  | argumentOutOfRange (name : Lean.Name) (index : Nat)
  | unknownBinder (declaration binder : Lean.Name)
  | ambiguousBinder (declaration binder : Lean.Name)
  | missingBodyBinder (name : Lean.Name) (index : Nat)
  | inconsistentTelescope (name : Lean.Name) (index : Nat)
      (typeMode bodyMode : Ixon.BinderMode)
  | annotatedRecursorRule (declaration : Lean.Name)
  | malformedAnnotation (declaration : Lean.Name) (site : BinderSite) (reason : String)
  | misplacedAnnotation (declaration : Lean.Name) (site : BinderSite)
  | annotationBinderMismatch (declaration : Lean.Name) (site : BinderSite)
      (expected actual : Lean.Name)
  | duplicateAnnotation (declaration : Lean.Name) (root : SourceRoot) (origin : Nat)
  | missingAnnotation (declaration : Lean.Name) (site : BinderSite)
  | conflictingAnnotation (declaration : Lean.Name) (site : BinderSite)
  | missingContract (declaration : Lean.Name)
  | fieldModeOnNonCtor (name : Lean.Name)
  | fieldOutOfRange (name : Lean.Name) (index : Nat)
  | duplicateFieldMode (name : Lean.Name) (index : Nat)
  | erasedSharedField (name : Lean.Name) (index : Nat)
  | invalidDefAsserts (name : Lean.Name) (reason : String)
  | conflictingDefAsserts (name : Lean.Name) (reason : String)
  | duplicateMeasure (name : Lean.Name)
  | zeroFixedStep (name : Lean.Name)
  deriving BEq, Repr

instance : ToString SourceContractError where
  toString error := s!"source contract: {repr error}"

end Ix.Compile

end
