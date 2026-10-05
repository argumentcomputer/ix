import Ix.CompileCert.Domain
import IxC.Kernel.Admission.Theorems
import IxC.Kernel.Verify.Cached.PushChain
import IxC.Kernel.Verify.Cached.BridgeCS4
import IxC.Kernel.Model.IndUnitLaw
import IxC.Kernel.Model.IOLicense
import IxC.Kernel.Model.Rules.RedSoundKit
import IxC.Kernel.Model.Rules.IotaSoundKit

/-! # The installed strong model and the installed checks

The strong installed model (`StrongInstalledModel`) of a checked environment,
the finite pull-back checks between installed environments (telescopes,
constants, pins, projections, expressions, member expressions, recursor
rules, types, definitions) with their soundness, and annotated applications
(`AnnotatedApplication`, `ArgumentAnnotation`) with the fired and public
recursor applications built on them.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-! The semantic tier must keep one strong witness throughout: separately
choosing a public model and a model with value equations would not establish
that the recursor rules and those values describe the same interpretation. -/

structure StrongInstalledModel (V : Type u) [Kernel.SetTheory V] (env : Kernel.Env) where
  internal : Kernel.Model.EnvModelM V .verified env
  definition_values : ∀ header value hint,
    Kernel.ConstantInfo.defnInfo header value hint ∈ env.consts →
      ∀ φ ρ, Kernel.Denotes (Kernel.Model.Model.ofEnvModelM internal).cval env φ ρ value
        ((Kernel.Model.Model.ofEnvModelM internal).cval header.name φ)

noncomputable def StrongInstalledModel.public {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env) : Kernel.Model V env :=
  Kernel.Model.Model.ofEnvModelM strong.internal

/-- Interpretation-level name and universe selection. A many-to-one map
does not select an arbitrary reverse representative: every source name has
its own explicit target instance. Its connection to the checked source map
and actual installation streams is a separate association obligation. -/
structure PullbackMap where
  name : Kernel.Name → Kernel.Name
  levels : Kernel.Name → (Kernel.Name → Nat) → (Kernel.Name → Nat)

def PullbackMap.values {V : Type u} (map : PullbackMap)
    (target : Kernel.Name → (Kernel.Name → Nat) → V) : Kernel.Name → (Kernel.Name → Nat) → V :=
  fun name levels => target (map.name name) (map.levels name levels)

/-- The direct C1 telescope association is positional and checks distinct
formals on both sides. General level selections remain a separate interface;
this check does not redefine the full compiler domain. -/
def TelescopeEntry (source target : Kernel.ConstantInfo) : Prop :=
  source.toConstantVal.levelParams.Nodup ∧ target.toConstantVal.levelParams.Nodup ∧
    source.toConstantVal.levelParams.length = target.toConstantVal.levelParams.length

instance (source target : Kernel.ConstantInfo) : Decidable (TelescopeEntry source target) :=
  inferInstanceAs (Decidable (source.toConstantVal.levelParams.Nodup ∧
    target.toConstantVal.levelParams.Nodup ∧
    source.toConstantVal.levelParams.length = target.toConstantVal.levelParams.length))

def checkTelescopes (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    match target.find? (names entry.name) with
    | none => false
    | some targetEntry => decide (TelescopeEntry entry targetEntry)

def TelescopeAssociation (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Prop :=
  ∀ name entry, source.find? name = some entry →
    ∃ targetEntry, target.find? (names name) = some targetEntry ∧ TelescopeEntry entry targetEntry

theorem checkTelescopes_sound {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkTelescopes source target names = true) : TelescopeAssociation source target names := by
  intro name entry lookup
  have checkedEntry := List.all_eq_true.mp checked entry (Kernel.Semantics.Env.find?_mem lookup)
  have named := Kernel.Semantics.Env.find?_name lookup
  simp only [named] at checkedEntry
  cases targetLookup : target.find? (names name) with
  | none => simp [targetLookup] at checkedEntry
  | some targetEntry =>
    simp only [targetLookup] at checkedEntry
    exact ⟨targetEntry, rfl, of_decide_eq_true checkedEntry⟩

/-- The interpretation's level assignment is derived from actual member
telescopes. The fallback is a total semantic function only: missing members
make `checkTelescopes` fail and supply no constant-image theorem. -/
def PullbackMap.fromEnvs (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : PullbackMap where
  name := names
  levels := fun name valuation =>
    match source.find? name, target.find? (names name) with
    | some sourceEntry, some targetEntry =>
      Kernel.Level.substFn valuation targetEntry.toConstantVal.levelParams
        (sourceEntry.toConstantVal.levelParams.map Kernel.Level.param)
    | _, _ => valuation

/-- Selected target parameters must depend only on the actual source
member's universe telescope. Missing/unrelated ambient parameters cannot
silently affect a pulled-back source constant. -/
def PullbackMap.LevelLocality (map : PullbackMap) (sourceEnv targetEnv : Kernel.Env) : Prop :=
  ∀ name sourceInfo, sourceEnv.find? name = some sourceInfo →
    ∃ targetInfo, targetEnv.find? (map.name name) = some targetInfo ∧
      ∀ first second : Kernel.Name → Nat,
        (∀ parameter ∈ sourceInfo.toConstantVal.levelParams, first parameter = second parameter) →
        ∀ parameter ∈ targetInfo.toConstantVal.levelParams,
          map.levels name first parameter = map.levels name second parameter

theorem StrongInstalledModel.value_params {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {info : Kernel.ConstantInfo} (lookup : env.find? name = some info)
    (first second : Kernel.Name → Nat)
    (agree : ∀ parameter ∈ info.toConstantVal.levelParams, first parameter = second parameter) :
    strong.public.cval name first = strong.public.cval name second := by
  change Kernel.Semantics.interp V (fun _ => Kernel.SetTheory.empty) (strong.internal.base2.acval name first) =
    Kernel.Semantics.interp V (fun _ => Kernel.SetTheory.empty) (strong.internal.base2.acval name second)
  rw [strong.internal.base2.acval_params name info lookup first second agree]

theorem PullbackMap.fromEnvs_locality {source target : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation source target names) :
    (PullbackMap.fromEnvs source target names).LevelLocality source target := by
  intro name sourceEntry sourceLookup
  obtain ⟨targetEntry, targetLookup, sourceUnique, targetUnique, sameArity⟩ :=
    association name sourceEntry sourceLookup
  refine ⟨targetEntry, targetLookup, ?_⟩
  intro first second agree parameter present
  simp only [PullbackMap.fromEnvs, sourceLookup, targetLookup]
  obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp present
  rw [levelSubst_get _ targetUnique (by simp [sameArity]) index inside,
    levelSubst_get _ targetUnique (by simp [sameArity]) index inside]
  simp only [List.getElem_map, Kernel.Level.eval]
  exact agree _ (List.getElem_mem (by omega))

/-- Equal positional argument meanings induce the same selected target
instance on its actual formals, even when ambient assignments differ. -/
theorem PullbackMap.fromEnvs_instance {sourceEnv targetEnv : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (parameter : Kernel.Name) (present : parameter ∈ targetEntry.toConstantVal.levelParams) :
    (PullbackMap.fromEnvs sourceEnv targetEnv names).levels name
      (Kernel.Level.substFn sourceLevels sourceEntry.toConstantVal.levelParams sourceUs) parameter =
      Kernel.Level.substFn targetLevels targetEntry.toConstantVal.levelParams targetUs parameter := by
  obtain ⟨entry, lookup, sourceUnique, targetUnique, sameArity⟩ := association name sourceEntry sourceLookup
  have equal := Option.some.inj (lookup.symm.trans targetLookup)
  subst entry
  obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp present
  simp only [PullbackMap.fromEnvs, sourceLookup, targetLookup]
  rw [levelSubst_get _ targetUnique (by simp [sameArity]) index inside,
    levelSubst_get _ targetUnique targetArity index inside]
  simp only [List.getElem_map, Kernel.Level.eval]
  rw [levelSubst_get _ sourceUnique sourceArity index (by omega)]
  have sourceBound : index < sourceUs.length := by omega
  have targetBound : index < targetUs.length := by omega
  have atIndex := congrArg (fun values : List Nat => values[index]?) arguments
  simpa [List.getElem?_map, List.getElem?_eq_getElem sourceBound,
    List.getElem?_eq_getElem targetBound] using atIndex

/-- Constant occurrences at semantically corresponding concrete universe
arguments, using only actual lookups and target parameter locality. -/
theorem PullbackMap.fromEnvs_constant_instance {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (.const name sourceUs) (.const (names name) targetUs) := by
  apply InstalledExprImage.constant sourceLookup targetLookup sourceArity targetArity
  apply target.value_params targetLookup
  exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
    sourceUs targetUs sourceArity targetArity arguments

/-- Derive constant-instance value equality from actual telescope lookup and
the target model's proved parameter locality. No per-occurrence value equality
or source-name injectivity is assumed, including for compatible alias fibers. -/
theorem PullbackMap.fromEnvs_constant {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {name : Kernel.Name} {entry : Kernel.ConstantInfo} (lookup : sourceEnv.find? name = some entry)
    (arguments : List Kernel.Level) (arity : arguments.length = entry.toConstantVal.levelParams.length) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv (image.valuation targetLevels) targetLevels
      (.const name arguments) (.const (names name) (arguments.map image.level)) := by
  obtain ⟨targetEntry, targetLookup, sourceUnique, targetUnique, sameArity⟩ := association name entry lookup
  apply InstalledExprImage.constant lookup targetLookup arity (by simp [arity, sameArity])
  apply target.value_params targetLookup
  intro parameter present
  simp only [PullbackMap.fromEnvs, lookup, targetLookup]
  exact image.telescope_instance targetLevels sourceUnique targetUnique sameArity arity parameter present

/-- Compare actual installed constant occurrences. `none` preserves the
underlying level comparison's unavailable result; it is not inequivalence. -/
def checkInstalledConstant (source : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) (sourceName targetName : Kernel.Name)
    (sourceUs targetUs : List Kernel.Level) : Option Bool :=
  match source.find? sourceName with
  | none => some false
  | some entry =>
    if targetName = names sourceName ∧ sourceUs.length = entry.toConstantVal.levelParams.length then
      Kernel.Level.isEquivList (sourceUs.map image.level) targetUs
    else some false

theorem checkInstalledConstant_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {sourceName targetName : Kernel.Name} {sourceUs targetUs : List Kernel.Level}
    (checked : checkInstalledConstant sourceEnv names image sourceName targetName sourceUs targetUs = some true) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv (image.valuation targetLevels) targetLevels
      (.const sourceName sourceUs) (.const targetName targetUs) := by
  cases lookup : sourceEnv.find? sourceName with
  | none => simp [checkInstalledConstant, lookup] at checked
  | some entry =>
    simp only [checkInstalledConstant, lookup] at checked
    split at checked
    · rename_i conditions
      obtain ⟨rfl, arity⟩ := conditions
      have base := PullbackMap.fromEnvs_constant target association image targetLevels lookup sourceUs arity
      exact base.constant_equivalent_levels checked
    · contradiction

def bothChecks (first second : Option Bool) : Option Bool :=
  match first with
  | some true => second
  | some false => some false
  | none => none

theorem bothChecks_true {first second : Option Bool} (checked : bothChecks first second = some true) :
    first = some true ∧ second = some true := by
  cases first with
  | none => contradiction
  | some value => cases value <;> simp_all [bothChecks]

def checkInstalledPins (source : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) : List (Kernel.Name × List Kernel.Level) → Option Bool
  | [] => some true
  | (name, levels) :: rest => bothChecks
      (checkInstalledConstant source names image name name levels levels)
      (checkInstalledPins source names image rest)

theorem checkInstalledPins_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {pins : List (Kernel.Name × List Kernel.Level)}
    (checked : checkInstalledPins sourceEnv names image pins = some true) :
    ∀ pin ∈ pins, InstalledExprImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv (image.valuation targetLevels) targetLevels
      (.const pin.1 pin.2) (.const pin.1 pin.2) := by
  induction pins with
  | nil => simp
  | cons pin rest ih =>
    obtain ⟨first, remaining⟩ := bothChecks_true checked
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact checkInstalledConstant_sound target association image targetLevels first
    · exact ih remaining selected member

def naturalImagePins : List (Kernel.Name × List Kernel.Level) :=
  [(Kernel.natZeroName, []), (Kernel.natSuccName, [])]

def stringImagePins : List (Kernel.Name × List Kernel.Level) := naturalImagePins ++
  [(Kernel.charName, []), (Kernel.charOfNatName, []), (Kernel.listNilName, [.zero]),
    (Kernel.listConsName, [.zero]), (Kernel.stringOfListName, [])]

theorem checked_natural_image {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (checked : checkInstalledPins sourceEnv names image naturalImagePins = some true) (value : Nat) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv (image.valuation targetLevels) targetLevels
      (.lit (.natVal value)) (.lit (.natVal value)) := by
  have pins := checkInstalledPins_sound target association image targetLevels checked
  exact InstalledExprImage.natural (pins (Kernel.natZeroName, []) (by simp [naturalImagePins]))
    (pins (Kernel.natSuccName, []) (by simp [naturalImagePins])) value

theorem checked_string_image {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (checked : checkInstalledPins sourceEnv names image stringImagePins = some true) (value : String) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv (image.valuation targetLevels) targetLevels
      (.lit (.strVal value)) (.lit (.strVal value)) := by
  have pins := checkInstalledPins_sound target association image targetLevels checked
  apply InstalledExprImage.string (value := value)
  · exact pins (Kernel.natZeroName, []) (by simp [stringImagePins, naturalImagePins])
  · exact pins (Kernel.natSuccName, []) (by simp [stringImagePins, naturalImagePins])
  · exact pins (Kernel.charName, []) (by simp [stringImagePins, naturalImagePins])
  · exact pins (Kernel.charOfNatName, []) (by simp [stringImagePins, naturalImagePins])
  · exact pins (Kernel.listNilName, [.zero]) (by simp [stringImagePins, naturalImagePins])
  · exact pins (Kernel.listConsName, [.zero]) (by simp [stringImagePins, naturalImagePins])
  · exact pins (Kernel.stringOfListName, []) (by simp [stringImagePins, naturalImagePins])

/-- Compare actual projection table positions, including the two official
fallback cases. A missing table at any other index supplies no image proof. -/
def checkInstalledProjection (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (sourceOwner targetOwner : Kernel.Name) (sourceIndex targetIndex : Nat) : Bool :=
  decide (targetOwner = names sourceOwner) &&
    match source.findProj? sourceOwner sourceIndex, target.findProj? targetOwner targetIndex with
    | some sourceEntry, some targetEntry => decide (sourceIndex + sourceEntry.off = targetIndex + targetEntry.off)
    | none, none => decide ((sourceIndex = 0 ∧ targetIndex = 0) ∨ (sourceIndex = 1 ∧ targetIndex = 1))
    | _, _ => false

theorem checkInstalledProjection_sound {V : Type u} [Kernel.SetTheory V]
    {sv tv sourceEnv targetEnv sl tl} {names : Kernel.Name → Kernel.Name}
    {sourceOwner targetOwner : Kernel.Name} {sourceIndex targetIndex : Nat} {source target : Kernel.Expr}
    (checked : checkInstalledProjection sourceEnv targetEnv names sourceOwner targetOwner sourceIndex targetIndex = true)
    (operand : InstalledExprImage (V := V) sv tv sourceEnv targetEnv sl tl source target) :
    InstalledExprImage sv tv sourceEnv targetEnv sl tl
      (.proj sourceOwner sourceIndex source) (.proj targetOwner targetIndex target) := by
  simp only [checkInstalledProjection, Bool.and_eq_true] at checked
  have position := checked.2
  cases sourceTable : sourceEnv.findProj? sourceOwner sourceIndex with
  | none =>
    cases targetTable : targetEnv.findProj? targetOwner targetIndex with
    | some entry => simp [sourceTable, targetTable] at position
    | none =>
      simp only [sourceTable, targetTable, decide_eq_true_eq] at position
      rcases position with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .projFst sourceTable targetTable operand
      · exact .projSnd sourceTable targetTable operand
  | some sourceEntry =>
    cases targetTable : targetEnv.findProj? targetOwner targetIndex with
    | none => simp [sourceTable, targetTable] at position
    | some targetEntry =>
      simp only [sourceTable, targetTable, decide_eq_true_eq] at position
      exact .projTable sourceTable targetTable position operand

/-- A conditional installed-expression image check, separate from raw reader
fidelity and source/target admission. It compares universe meanings and actual
binder data. `none` means no certificate (including open/let forms); it is not
an established negative equality or a new definition of the compiler domain.
Projection lowering with a different expression shape needs its own proved
normalization relation and is not silently accepted here. -/
def checkInstalledExpr (sourceEnv targetEnv : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) : Kernel.Expr → Kernel.Expr → Option Bool
  | .bvar source, .bvar target => some (decide (source = target))
  | .sort source, .sort target => Kernel.Level.isEquiv (image.level source) target
  | .const sourceName sourceUs, .const targetName targetUs =>
      checkInstalledConstant sourceEnv names image sourceName targetName sourceUs targetUs
  | .app sf sa, .app tf ta => bothChecks
      (checkInstalledExpr sourceEnv targetEnv names image sf tf)
      (checkInstalledExpr sourceEnv targetEnv names image sa ta)
  | .lam sd sb sm, .lam td tb tm
  | .forallE sd sb sm, .forallE td tb tm => bothChecks
      (some (decide (tm.pw = image.datum sm.pw))) (bothChecks
        (checkInstalledExpr sourceEnv targetEnv names image sd td)
        (checkInstalledExpr sourceEnv targetEnv names image sb tb))
  | .proj so si se, .proj to ti te => bothChecks
      (some (checkInstalledProjection sourceEnv targetEnv names so to si ti))
      (checkInstalledExpr sourceEnv targetEnv names image se te)
  | .lit (.natVal source), .lit (.natVal target) => bothChecks (some (decide (source = target)))
      (checkInstalledPins sourceEnv names image naturalImagePins)
  | .lit (.strVal source), .lit (.strVal target) => bothChecks (some (decide (source = target)))
      (checkInstalledPins sourceEnv names image stringImagePins)
  | .fvar .., _ | .letE .., _ | _, .fvar .. | _, .letE .. => none
  | _, _ => some false

/-- Every accepted installed-expression comparison yields the semantic image
for every target universe valuation. Source values are the explicit target
pull-back. Admission, actual declaration association and projection lowering
are separate premises/relations and are not supplied by this expression check. -/
theorem checkInstalledExpr_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {source target : Kernel.Expr}
    (checked : checkInstalledExpr sourceEnv targetEnv names image source target = some true) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values targetModel.public.cval)
      targetModel.public.cval sourceEnv targetEnv (image.valuation targetLevels) targetLevels source target := by
  induction source generalizing target with
  | bvar index =>
    cases target <;> simp [checkInstalledExpr] at checked
    case bvar other => subst other; exact .bvar index
  | fvar index type ih => cases target <;> simp [checkInstalledExpr] at checked
  | sort level =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case sort targetLevel =>
      exact .sort ((image.eval targetLevels level).symm.trans
        (Kernel.Level.isEquiv_sound checked targetLevels))
  | const name levels =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case const targetName targetUs =>
      exact checkInstalledConstant_sound targetModel association image targetLevels checked
  | app function argument ihF ihA =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case app targetFunction targetArgument =>
      obtain ⟨functionCheck, argumentCheck⟩ := bothChecks_true checked
      exact .app (ihF functionCheck) (ihA argumentCheck)
  | lam domain body metadata ihD ihB =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case lam targetDomain targetBody targetMetadata =>
      obtain ⟨datumCheck, rest⟩ := bothChecks_true checked
      obtain ⟨domainCheck, bodyCheck⟩ := bothChecks_true rest
      have datum := of_decide_eq_true (Option.some.inj datumCheck)
      apply InstalledExprImage.lam (ihD domainCheck) (ihB bodyCheck)
      rw [datum]
      exact (image.regime targetLevels metadata).symm
  | forallE domain body metadata ihD ihB =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case forallE targetDomain targetBody targetMetadata =>
      obtain ⟨datumCheck, rest⟩ := bothChecks_true checked
      obtain ⟨domainCheck, bodyCheck⟩ := bothChecks_true rest
      have datum := of_decide_eq_true (Option.some.inj datumCheck)
      apply InstalledExprImage.forallE (ihD domainCheck) (ihB bodyCheck)
      rw [datum]
      exact (image.regime targetLevels metadata).symm
  | letE type value body ihT ihV ihB => cases target <;> simp [checkInstalledExpr] at checked
  | lit literal =>
    cases literal with
    | natVal value =>
      cases target <;> try simp only [checkInstalledExpr] at checked <;> try contradiction
      case lit targetLiteral =>
        cases targetLiteral <;> simp only [checkInstalledExpr] at checked <;> try contradiction
        case natVal other =>
          obtain ⟨equal, pins⟩ := bothChecks_true checked
          have same := of_decide_eq_true (Option.some.inj equal)
          subst other
          exact checked_natural_image targetModel association image targetLevels pins value
    | strVal value =>
      cases target <;> try simp only [checkInstalledExpr] at checked <;> try contradiction
      case lit targetLiteral =>
        cases targetLiteral <;> simp only [checkInstalledExpr] at checked <;> try contradiction
        case strVal other =>
          obtain ⟨equal, pins⟩ := bothChecks_true checked
          have same := of_decide_eq_true (Option.some.inj equal)
          subst other
          exact checked_string_image targetModel association image targetLevels pins value
  | proj owner index operand ih =>
    cases target <;> simp only [checkInstalledExpr] at checked <;> try contradiction
    case proj targetOwner targetIndex targetOperand =>
      obtain ⟨projectionCheck, operandCheck⟩ := bothChecks_true checked
      exact checkInstalledProjection_sound (Option.some.inj projectionCheck) (ih operandCheck)

theorem PullbackMap.values_params {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (map : PullbackMap) (target : StrongInstalledModel V targetEnv)
    (locality : map.LevelLocality sourceEnv targetEnv)
    {name : Kernel.Name} {info : Kernel.ConstantInfo} (lookup : sourceEnv.find? name = some info)
    (first second : Kernel.Name → Nat)
    (agree : ∀ parameter ∈ info.toConstantVal.levelParams, first parameter = second parameter) :
    map.values target.public.cval name first = map.values target.public.cval name second := by
  obtain ⟨targetInfo, targetLookup, selection⟩ := locality name info lookup
  exact target.value_params targetLookup _ _ (selection first second agree)

/-- Compare expressions in an actual source member's universe telescope.
The caller still identifies whether these are its type, value or rule. -/
def checkInstalledMemberExpr (sourceEnv targetEnv : Kernel.Env)
    (names : Kernel.Name → Kernel.Name) (name : Kernel.Name)
    (source target : Kernel.Expr) : Option Bool :=
  match sourceEnv.find? name, targetEnv.find? (names name) with
  | some sourceEntry, some targetEntry =>
    if source.allLevelParamsDefined sourceEntry.toConstantVal.levelParams then
      checkInstalledExpr sourceEnv targetEnv names
        (UniverseImage.select sourceEntry.toConstantVal.levelParams
          (targetEntry.toConstantVal.levelParams.map Kernel.Level.param)) source target
    else some false
  | _, _ => some false

/-- Successful comparison yields an image at every original source universe
assignment. The executable check establishes parameter coverage,
including binder metadata; target model locality handles unused ambient
assignments rather than assuming equality of whole valuation functions. -/
theorem checkInstalledMemberExpr_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some sourceEntry)
    {source target : Kernel.Expr}
    (checked : checkInstalledMemberExpr sourceEnv targetEnv names name source target = some true)
    (sourceLevels : Kernel.Name → Nat) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values targetModel.public.cval)
      targetModel.public.cval sourceEnv targetEnv sourceLevels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name sourceLevels) source target := by
  obtain ⟨targetEntry, targetLookup, sourceUnique, targetUnique, sameArity⟩ := association name sourceEntry lookup
  simp only [checkInstalledMemberExpr, lookup, targetLookup] at checked
  split at checked
  next bounded =>
    have image := checkInstalledExpr_sound targetModel association _
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name sourceLevels) checked
    refine image.source_levels ?_ bounded ?_
    · intro constant info present first second agree
      exact PullbackMap.values_params _ targetModel
        (PullbackMap.fromEnvs_locality association) present first second agree
    · intro parameter present
      simp only [PullbackMap.fromEnvs, lookup, targetLookup]
      exact (UniverseImage.telescope_recovery sourceLevels sourceUnique targetUnique sameArity parameter present).symm
  next => contradiction

/-- Instantiate a checked actual member field at arbitrary universe
arguments with equal meanings. Target parameter coverage comes from the
actual installed field's well-formedness, not from a raw-source guess. -/
theorem PullbackMap.fromEnvs_instantiated_image {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    {source target : Kernel.Expr}
    (targetBounded : target.allLevelParamsDefined targetEntry.toConstantVal.levelParams = true)
    (images : ∀ levels, InstalledExprImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values targetModel.public.cval)
      targetModel.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) source target)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values targetModel.public.cval)
      targetModel.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (source.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs)
      (target.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs) := by
  have sourceLocality := fun name info lookup first second agree =>
    PullbackMap.values_params (PullbackMap.fromEnvs sourceEnv targetEnv names) targetModel
      (PullbackMap.fromEnvs_locality association) (name := name) (info := info) lookup first second agree
  have targetLocality := fun name info lookup first second agree =>
    targetModel.value_params (name := name) (info := info) lookup first second agree
  have image := images (Kernel.Level.substFn sourceLevels sourceEntry.toConstantVal.levelParams sourceUs)
  have atInstance := image.symm.source_levels targetLocality targetBounded (fun parameter present =>
    (PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
      sourceUs targetUs sourceArity targetArity arguments parameter present).symm)
  exact atInstance.symm.instantiateLevels _ _ _ _ sourceLocality targetLocality

theorem checkInstalledMemberExpr_instance {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    {source target : Kernel.Expr}
    (targetBounded : target.allLevelParamsDefined targetEntry.toConstantVal.levelParams = true)
    (checked : checkInstalledMemberExpr sourceEnv targetEnv names name source target = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values targetModel.public.cval)
      targetModel.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (source.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs)
      (target.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs) :=
  PullbackMap.fromEnvs_instantiated_image targetModel association sourceLookup targetLookup targetBounded
    (checkInstalledMemberExpr_sound targetModel association sourceLookup checked)
    sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments

def checkInstalledMemberExprs (source target : Kernel.Env)
    (names : Kernel.Name → Kernel.Name) (name : Kernel.Name) :
    List Kernel.Expr → List Kernel.Expr → Option Bool
  | [], [] => some true
  | sourceExpr :: sources, targetExpr :: targets => bothChecks
      (checkInstalledMemberExpr source target names name sourceExpr targetExpr)
      (checkInstalledMemberExprs source target names name sources targets)
  | _, _ => some false

theorem checkInstalledMemberExprs_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some sourceEntry)
    {sources targets : List Kernel.Expr}
    (checked : checkInstalledMemberExprs sourceEnv targetEnv names name sources targets = some true)
    (levels : Kernel.Name → Nat) :
    InstalledSpineImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) sources targets := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp [checkInstalledMemberExprs] at checked; exact .nil
  | cons source sources ih =>
    cases targets with
    | nil => simp [checkInstalledMemberExprs] at checked
    | cons targetExpr targets =>
      obtain ⟨head, tail⟩ := bothChecks_true checked
      exact .cons (checkInstalledMemberExpr_sound target association lookup head levels) (ih tail)

/-- Installed firing correspondence, including every nested level and pin
position. This relation does not itself prove application admissibility or
transfer a strong recursor law; those use the actual typed spines. -/
inductive InstalledFireImage {V : Type u} [Kernel.SetTheory V]
    (sv tv : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat) :
    Kernel.RecRuleFire → Kernel.RecRuleFire → Prop
  | inert : InstalledFireImage sv tv sourceEnv targetEnv sourceLevels targetLevels .inert .inert
  | plain : InstalledFireImage sv tv sourceEnv targetEnv sourceLevels targetLevels .plain .plain
  | nested {sourceUs targetUs sourcePins targetPins}
      (levels : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
      (pins : InstalledSpineImage sv tv sourceEnv targetEnv sourceLevels targetLevels sourcePins targetPins) :
      InstalledFireImage sv tv sourceEnv targetEnv sourceLevels targetLevels
        (.nested sourceUs sourcePins) (.nested targetUs targetPins)

def checkInstalledFire (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) : Kernel.RecRuleFire → Kernel.RecRuleFire → Option Bool
  | .inert, .inert | .plain, .plain => some true
  | .nested sourceUs sourcePins, .nested targetUs targetPins => bothChecks
      (checkInstalledMemberExprs source target names name
        (sourceUs.map Kernel.Expr.sort) (targetUs.map Kernel.Expr.sort))
      (checkInstalledMemberExprs source target names name sourcePins targetPins)
  | _, _ => some false

theorem checkInstalledFire_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some sourceEntry)
    {sourceFire targetFire : Kernel.RecRuleFire}
    (checked : checkInstalledFire sourceEnv targetEnv names name sourceFire targetFire = some true)
    (levels : Kernel.Name → Nat) :
    InstalledFireImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) sourceFire targetFire := by
  cases sourceFire <;> cases targetFire <;> simp only [checkInstalledFire] at checked
  all_goals try contradiction
  · exact .inert
  · exact .plain
  · obtain ⟨universeCheck, pinCheck⟩ := bothChecks_true checked
    exact .nested (checkInstalledMemberExprs_sound target association lookup universeCheck levels).sorts
      (checkInstalledMemberExprs_sound target association lookup pinCheck levels)

def InstalledRuleHeader (names : Kernel.Name → Kernel.Name) (source target : Kernel.RecRule) : Prop :=
  names source.ctor = target.ctor ∧ source.nfields = target.nfields ∧
    source.ctorParams = target.ctorParams ∧ source.k = target.k ∧ source.eta = target.eta ∧
    source.paramsBlind = target.paramsBlind

instance (names : Kernel.Name → Kernel.Name) (source target : Kernel.RecRule) :
    Decidable (InstalledRuleHeader names source target) :=
  inferInstanceAs (Decidable (names source.ctor = target.ctor ∧ source.nfields = target.nfields ∧
    source.ctorParams = target.ctorParams ∧ source.k = target.k ∧ source.eta = target.eta ∧
    source.paramsBlind = target.paramsBlind))

structure InstalledRuleImage {V : Type u} [Kernel.SetTheory V]
    (sv tv : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat)
    (names : Kernel.Name → Kernel.Name) (source target : Kernel.RecRule) : Prop where
  header : InstalledRuleHeader names source target
  fire : InstalledFireImage sv tv sourceEnv targetEnv sourceLevels targetLevels source.fire target.fire
  rhs : InstalledExprImage sv tv sourceEnv targetEnv sourceLevels targetLevels source.rhs target.rhs

inductive InstalledRulesImage {V : Type u} [Kernel.SetTheory V]
    (sv tv : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv targetEnv : Kernel.Env) (sourceLevels targetLevels : Kernel.Name → Nat)
    (names : Kernel.Name → Kernel.Name) : List Kernel.RecRule → List Kernel.RecRule → Prop
  | nil : InstalledRulesImage sv tv sourceEnv targetEnv sourceLevels targetLevels names [] []
  | cons {source target sources targets}
      (head : InstalledRuleImage sv tv sourceEnv targetEnv sourceLevels targetLevels names source target)
      (tail : InstalledRulesImage sv tv sourceEnv targetEnv sourceLevels targetLevels names sources targets) :
      InstalledRulesImage sv tv sourceEnv targetEnv sourceLevels targetLevels names (source :: sources) (target :: targets)

theorem InstalledRulesImage.length {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl names sources targets}
    (image : InstalledRulesImage (V := V) sv tv se te sl tl names sources targets) :
    sources.length = targets.length := by
  induction image with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem InstalledRulesImage.at {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl names sources targets}
    (image : InstalledRulesImage (V := V) sv tv se te sl tl names sources targets)
    (index : Nat) (inside : index < sources.length) :
    InstalledRuleImage sv tv se te sl tl names sources[index]
      (targets[index]'(by rw [← image.length]; exact inside)) := by
  induction image generalizing index with
  | nil => simp at inside
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index (by simpa using inside)

def checkInstalledRules (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) : List Kernel.RecRule → List Kernel.RecRule → Option Bool
  | [], [] => some true
  | sourceRule :: sources, targetRule :: targets => bothChecks
      (some (decide (InstalledRuleHeader names sourceRule targetRule))) (bothChecks
        (checkInstalledFire source target names name sourceRule.fire targetRule.fire) (bothChecks
          (checkInstalledMemberExpr source target names name sourceRule.rhs targetRule.rhs)
          (checkInstalledRules source target names name sources targets)))
  | _, _ => some false

theorem checkInstalledRules_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some sourceEntry)
    {sources targets : List Kernel.RecRule}
    (checked : checkInstalledRules sourceEnv targetEnv names name sources targets = some true)
    (levels : Kernel.Name → Nat) :
    InstalledRulesImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) names sources targets := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp [checkInstalledRules] at checked; exact .nil
  | cons source sources ih =>
    cases targets with
    | nil => simp [checkInstalledRules] at checked
    | cons targetRule targets =>
      obtain ⟨header, rest⟩ := bothChecks_true checked
      obtain ⟨fire, rest⟩ := bothChecks_true rest
      obtain ⟨rhs, tail⟩ := bothChecks_true rest
      exact .cons ⟨of_decide_eq_true (Option.some.inj header),
        checkInstalledFire_sound target association lookup fire levels,
        checkInstalledMemberExpr_sound target association lookup rhs levels⟩ (ih tail)

/-- Recursor rows are checked in their actual installed form, after the
fold computed their firing modes and rescue bits. Original raw rule/block
records and their installation association remain separate evidence. -/
def checkInstalledRecursors (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry => match entry with
    | .recInfo header major rulePrefix rules =>
      decide (source.find? header.name = some entry) &&
      match target.find? (names header.name) with
      | some (.recInfo _ targetMajor targetPrefix targetRules) =>
        decide (major = targetMajor ∧ rulePrefix = targetPrefix) &&
          decide (checkInstalledRules source target names header.name rules targetRules = some true)
      | _ => false
    | _ => true

theorem checkInstalledRecursors_member {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledRecursors source target names = true)
    {header : Kernel.ConstantVal} {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (present : Kernel.ConstantInfo.recInfo header major rulePrefix rules ∈ source.consts) :
    source.find? header.name = some (.recInfo header major rulePrefix rules) ∧
    ∃ targetHeader targetRules,
      target.find? (names header.name) = some (.recInfo targetHeader major rulePrefix targetRules) ∧
      checkInstalledRules source target names header.name rules targetRules = some true := by
  have row := List.all_eq_true.mp checked (.recInfo header major rulePrefix rules) present
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  refine ⟨row.1, ?_⟩
  cases lookup : target.find? (names header.name) with
  | none => simp [lookup] at row
  | some entry =>
    cases entry <;> simp only [lookup, Bool.and_eq_true, decide_eq_true_eq] at row
    case recInfo targetHeader targetMajor targetPrefix targetRules =>
      obtain ⟨_, ⟨rfl, rfl⟩, comparison⟩ := row
      exact ⟨targetHeader, targetRules, rfl, comparison⟩
    all_goals simp at row

theorem checkInstalledRecursors_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledRecursors sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (present : Kernel.ConstantInfo.recInfo header major rulePrefix rules ∈ sourceEnv.consts) :
    ∃ targetHeader targetRules,
      targetEnv.find? (names header.name) = some (.recInfo targetHeader major rulePrefix targetRules) ∧
      ∀ levels, InstalledRulesImage
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        target.public.cval sourceEnv targetEnv levels
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels) names rules targetRules := by
  obtain ⟨sourceLookup, targetHeader, targetRules, targetLookup, comparison⟩ :=
    checkInstalledRecursors_member checked present
  exact ⟨targetHeader, targetRules, targetLookup,
    fun levels => checkInstalledRules_sound target association sourceLookup comparison levels⟩

/-- The actual rule at a checked ordinal has corresponding instantiated
RHS semantics. Target RHS parameter coverage is extracted from the strong
model's installed well-formedness, rather than supplied by the generator. -/
theorem checkInstalledRecursors_rhs_instance {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledRecursors sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (present : Kernel.ConstantInfo.recInfo header major rulePrefix rules ∈ sourceEnv.consts) :
    ∃ targetHeader targetRules,
      targetEnv.find? (names header.name) = some (.recInfo targetHeader major rulePrefix targetRules) ∧
      ∀ index (inside : index < rules.length), ∃ targetRule,
        targetRules[index]? = some targetRule ∧
        ∀ sourceLevels targetLevels sourceUs targetUs,
          sourceUs.length = header.levelParams.length →
          targetUs.length = targetHeader.levelParams.length →
          sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels) →
          InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
            target.public.cval sourceEnv targetEnv sourceLevels targetLevels
            (rules[index].rhs.instantiateLevelParams header.levelParams sourceUs)
            (targetRule.rhs.instantiateLevelParams targetHeader.levelParams targetUs) := by
  obtain ⟨sourceLookup, targetHeader, targetRules, targetLookup, comparison⟩ :=
    checkInstalledRecursors_member checked present
  have images := checkInstalledRules_sound target association sourceLookup comparison
  refine ⟨targetHeader, targetRules, targetLookup, ?_⟩
  intro index inside
  have targetInside : index < targetRules.length := by rw [← (images (fun _ => 0)).length]; exact inside
  refine ⟨targetRules[index], List.getElem?_eq_getElem targetInside, ?_⟩
  intro sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments
  have wf := target.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetLookup)
  have rhsWf := wf.2.2.2.2.2.1 targetHeader major rulePrefix targetRules rfl
    targetRules[index] (List.getElem_mem targetInside)
  exact PullbackMap.fromEnvs_instantiated_image target association sourceLookup targetLookup rhsWf.2.1
    (fun levels => ((images levels).at index inside).rhs)
    sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments

/-- Check every actual source row, including every member of an alias
fiber. The source lookup check prevents a shadowed row from borrowing the
telescope of another row with the same name. Extra target support is allowed.
This checks type fields only; it neither erases nor certifies other fields. -/
def checkInstalledTypes (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    decide (source.find? entry.name = some entry) &&
    match target.find? (names entry.name) with
    | none => false
    | some targetEntry => decide (checkInstalledMemberExpr source target names entry.name
        entry.toConstantVal.type targetEntry.toConstantVal.type = some true)

theorem checkInstalledTypes_member {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledTypes source target names = true)
    {entry : Kernel.ConstantInfo} (present : entry ∈ source.consts) :
    source.find? entry.name = some entry ∧
    ∃ targetEntry, target.find? (names entry.name) = some targetEntry ∧
      checkInstalledMemberExpr source target names entry.name
        entry.toConstantVal.type targetEntry.toConstantVal.type = some true := by
  have row := List.all_eq_true.mp checked entry present
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  refine ⟨row.1, ?_⟩
  cases lookup : target.find? (names entry.name) with
  | none => simp [lookup] at row
  | some targetEntry =>
    exact ⟨targetEntry, rfl, of_decide_eq_true (by simpa only [lookup] using row.2)⟩

theorem checkInstalledTypes_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledTypes sourceEnv targetEnv names = true)
    (sourceConstant : Kernel.ConstantInfo) (present : sourceConstant ∈ sourceEnv.consts)
    (sourceLevels : Kernel.Name → Nat) :
    ∃ targetConstant, targetConstant ∈ targetEnv.consts ∧
      targetConstant.name = names sourceConstant.name ∧
      InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        target.public.cval sourceEnv targetEnv sourceLevels
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels sourceConstant.name sourceLevels)
        sourceConstant.toConstantVal.type targetConstant.toConstantVal.type := by
  obtain ⟨sourceLookup, targetEntry, targetLookup, comparison⟩ := checkInstalledTypes_member checked present
  exact ⟨targetEntry, Kernel.Semantics.Env.find?_mem targetLookup,
    Kernel.Semantics.Env.find?_name targetLookup,
    checkInstalledMemberExpr_sound target association sourceLookup comparison sourceLevels⟩

/-- Exact semantic premises of the public model pull-back. In particular,
types are related to actual target members and False/Eq are related to the
target model's pinned interpretations, not just to similarly spelled names.
The source interpretation is defined from the target, never independently
chosen and subsequently asserted equal to it. -/
structure PullbackTypeEvidence {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} (target : Kernel.Model V targetEnv)
    (sourceEnv : Kernel.Env) (map : PullbackMap) : Prop where
  member : ∀ sourceConstant ∈ sourceEnv.consts, ∀ sourceLevels,
    ∃ targetConstant, targetConstant ∈ targetEnv.consts ∧
      targetConstant.name = map.name sourceConstant.name ∧
      InstalledExprImage (map.values target.cval) target.cval sourceEnv targetEnv
        sourceLevels (map.levels sourceConstant.name sourceLevels)
        sourceConstant.toConstantVal.type targetConstant.toConstantVal.type
  falseImage : ∀ sourceLevels, ∃ targetLevels,
    InstalledExprImage (map.values target.cval) target.cval sourceEnv targetEnv
      sourceLevels targetLevels (.const Kernel.falseName []) (.const Kernel.falseName [])
  equalityImage : ∀ sourceLevel sourceLevels, ∃ targetLevel targetLevels,
    Kernel.Level.eval sourceLevels sourceLevel = Kernel.Level.eval targetLevels targetLevel ∧
    InstalledExprImage (map.values target.cval) target.cval sourceEnv targetEnv
      sourceLevels targetLevels (.const Kernel.eqName [sourceLevel]) (.const Kernel.eqName [targetLevel])

/-- Pin checks are source-owned exact-name and arity checks. No reverse
alias representative is selected and no pinned identity is replaced. -/
def checkInstalledPin (source : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) (arity : Nat) : Bool :=
  match source.find? name with
  | none => false
  | some entry => decide (names name = name ∧ entry.toConstantVal.levelParams.length = arity)

theorem checkInstalledPin_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {arity : Nat} (checked : checkInstalledPin sourceEnv names name arity = true)
    (arguments : List Kernel.Level) (argumentArity : arguments.length = arity)
    (levels : Kernel.Name → Nat) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels levels (.const name arguments) (.const name arguments) := by
  cases lookup : sourceEnv.find? name with
  | none => simp [checkInstalledPin, lookup] at checked
  | some entry =>
    have facts : names name = name ∧ entry.toConstantVal.levelParams.length = arity := by
      simpa [checkInstalledPin, lookup] using checked
    have image := PullbackMap.fromEnvs_constant target association UniverseImage.identity levels lookup
      arguments (argumentArity.trans facts.2.symm)
    have identityLevels : UniverseImage.identity.level = id := funext UniverseImage.identity_level
    simpa only [UniverseImage.identity_valuation, identityLevels,
      List.map_id, facts.1] using image

theorem checkedPullbackTypes {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name}
    (telescopes : checkTelescopes sourceEnv targetEnv names = true)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (falsePin : checkInstalledPin sourceEnv names Kernel.falseName 0 = true)
    (eqPin : checkInstalledPin sourceEnv names Kernel.eqName 1 = true) :
    PullbackTypeEvidence target.public sourceEnv (PullbackMap.fromEnvs sourceEnv targetEnv names) := by
  have association := checkTelescopes_sound telescopes
  constructor
  · exact checkInstalledTypes_sound target association types
  · intro levels
    exact ⟨levels, checkInstalledPin_sound target association falsePin [] rfl levels⟩
  · intro level levels
    exact ⟨level, levels, rfl, checkInstalledPin_sound target association eqPin [level] rfl levels⟩

/-- The public source model, constructed from the target interpretation.
This generic semantic theorem does not discharge the actual source fold,
raw-source/installed correspondence, or strong recursor/capability laws. -/
noncomputable def PullbackTypeEvidence.model {V : Type u} [Kernel.SetTheory V]
    {targetEnv sourceEnv : Kernel.Env} {target : Kernel.Model V targetEnv} {map : PullbackMap}
    (evidence : PullbackTypeEvidence target sourceEnv map) : Kernel.Model V sourceEnv where
  cval := map.values target.cval
  mem := by
    intro constant present levels valuation
    obtain ⟨targetConstant, targetPresent, targetName, image⟩ := evidence.member constant present levels
    obtain ⟨type, typeRead, member⟩ := target.mem targetConstant targetPresent
      (map.levels constant.name levels) valuation
    refine ⟨type, image.symm.denotes typeRead, ?_⟩
    simpa only [PullbackMap.values, targetName] using member
  false_empty := by
    intro levels valuation value read
    obtain ⟨targetLevels, image⟩ := evidence.falseImage levels
    exact target.false_empty targetLevels valuation value (image.denotes read)
  eq_equality := by
    intro level levels valuation equality type left right read typeMember leftMember rightMember
    obtain ⟨targetLevel, targetLevels, evaluation, image⟩ := evidence.equalityImage level levels
    apply target.eq_equality targetLevel targetLevels valuation equality type left right
      (image.denotes read) _ leftMember rightMember
    simpa only [← evaluation] using typeMember

/-- Definition values in addition to the public type model. This deliberately
does not call itself a strong model: fired recursor/capability laws are still
required for the full source pull-back theorem. -/
structure PublicValueModel (V : Type u) [Kernel.SetTheory V] (env : Kernel.Env) where
  model : Kernel.Model V env
  parameters : ∀ name info, env.find? name = some info → ∀ first second : Kernel.Name → Nat,
    (∀ parameter ∈ info.toConstantVal.levelParams, first parameter = second parameter) →
      model.cval name first = model.cval name second
  definitions : ∀ header value hint,
    Kernel.ConstantInfo.defnInfo header value hint ∈ env.consts →
      ∀ levels valuation, Kernel.Denotes model.cval env levels valuation value
        (model.cval header.name levels)

structure PullbackDefinitionEvidence {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    (sourceEnv : Kernel.Env) (map : PullbackMap) : Prop where
  definition : ∀ header value hint,
    Kernel.ConstantInfo.defnInfo header value hint ∈ sourceEnv.consts → ∀ sourceLevels,
    ∃ targetHeader targetValue targetHint,
      Kernel.ConstantInfo.defnInfo targetHeader targetValue targetHint ∈ targetEnv.consts ∧
      targetHeader.name = map.name header.name ∧
      InstalledExprImage (map.values target.public.cval) target.public.cval sourceEnv targetEnv
        sourceLevels (map.levels header.name sourceLevels) value targetValue

/-- Definition-body checking preserves the target's actual definition kind.
Theorem records cannot supply definition equations; their checking bodies
need a separate relation. Reducibility hints are retained by both lookups,
but no operational equivalence is inferred from their possible difference. -/
def checkInstalledDefinitions (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    match entry with
    | .defnInfo header value _ =>
      decide (source.find? header.name = some entry) &&
      match target.find? (names header.name) with
      | some (.defnInfo _ targetValue _) =>
        decide (checkInstalledMemberExpr source target names header.name value targetValue = some true)
      | _ => false
    | _ => true

theorem checkInstalledDefinitions_member {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledDefinitions source target names = true)
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Kernel.ConstantInfo.defnInfo header value hint ∈ source.consts) :
    source.find? header.name = some (.defnInfo header value hint) ∧
    ∃ targetHeader targetValue targetHint,
      target.find? (names header.name) = some (.defnInfo targetHeader targetValue targetHint) ∧
      checkInstalledMemberExpr source target names header.name value targetValue = some true := by
  have row := List.all_eq_true.mp checked (.defnInfo header value hint) present
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  refine ⟨row.1, ?_⟩
  cases lookup : target.find? (names header.name) with
  | none => simp [lookup] at row
  | some targetEntry =>
    cases targetEntry <;> simp only [lookup] at row
    case defnInfo targetHeader targetValue targetHint =>
      exact ⟨targetHeader, targetValue, targetHint, rfl, of_decide_eq_true row.2⟩
    all_goals simp at row

theorem checkInstalledDefinitions_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledDefinitions sourceEnv targetEnv names = true) :
    PullbackDefinitionEvidence target sourceEnv (PullbackMap.fromEnvs sourceEnv targetEnv names) := by
  constructor
  intro header value hint present levels
  obtain ⟨sourceLookup, targetHeader, targetValue, targetHint, targetLookup, comparison⟩ :=
    checkInstalledDefinitions_member checked present
  exact ⟨targetHeader, targetValue, targetHint, Kernel.Semantics.Env.find?_mem targetLookup,
    Kernel.Semantics.Env.find?_name targetLookup,
    checkInstalledMemberExpr_sound target association sourceLookup comparison levels⟩

/-- Definition equations are pulled back from actual target definitions.
Opaque/theorem checking bodies supply no premise of this kind. Source
admission and full annotation correspondence remain separate obligations. -/
noncomputable def PullbackDefinitionEvidence.valueModel {V : Type u} [Kernel.SetTheory V]
    {targetEnv sourceEnv : Kernel.Env} {target : StrongInstalledModel V targetEnv} {map : PullbackMap}
    (types : PullbackTypeEvidence target.public sourceEnv map)
    (values : PullbackDefinitionEvidence target sourceEnv map)
    (locality : map.LevelLocality sourceEnv targetEnv) : PublicValueModel V sourceEnv where
  model := types.model
  parameters := by
    intro name info lookup first second agree
    exact map.values_params target locality lookup first second agree
  definitions := by
    intro header value hint present levels valuation
    obtain ⟨targetHeader, targetValue, targetHint, targetPresent, targetName, image⟩ :=
      values.definition header value hint present levels
    have read := image.symm.denotes
      (target.definition_values targetHeader targetValue targetHint targetPresent
        (map.levels header.name levels) valuation)
    simpa only [PullbackTypeEvidence.model, PullbackMap.values, targetName,
      StrongInstalledModel.public] using read

private theorem noFvars_below_zero :
    ∀ {e : Kernel.Expr}, e.hasFvar = false → Kernel.Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [Kernel.Expr.fvarsBelow, Kernel.Expr.hasFvar]

/-- Public value equations and the internal recursor laws come from the
same accepting fold, not two independently selected model witnesses.
Theorem/opaque body checking does not become a transparent value equation. -/
theorem strongInstalledModel_exists (V : Type u) [Kernel.SetTheory V]
    (pins : List Kernel.NatOpPinSet) (declarations : Array Kernel.Declaration) (env : Kernel.Env)
    (checked : Kernel.Cached.checkDecls .verified pins declarations = .ok env) :
    Nonempty (StrongInstalledModel V env) := by
  obtain ⟨model⟩ := Kernel.Cached.checkDecls_sound (V := V) rfl checked
  refine ⟨⟨model, ?_⟩⟩
  intro header value hint present φ ρ
  have read := model.defn_reads φ header value ⟨hint, present⟩
  have valid := (model.base2.wf _ present).2.2.2.2.1 header value hint rfl
  have denoted := Kernel.Model.Denotes_of_denoteMeta (V := V) model.base2.cval_closedL
    0 value read (noFvars_below_zero valid.1) valid.2.2.2 ρ
    ⟨model.base2.acval_wellDenoted _ φ ρ, model.acval_validV _ φ ρ⟩
  rw [Kernel.Expr.closeN_of_hasFvar _ 0 0 valid.1,
    Kernel.Model.interp_cvalOf model.base2.cval_closedL] at denoted
  exact denoted

/-- A conditional executable endpoint for the public type and definition
interpretation of two independently accepted streams. The original source
installation is witnessed separately; it is never inferred from target
acceptance. This does not yet provide source recursor/capability laws or a
relation from either stream to immutable compiler input or reader bytes. -/
theorem checkedStreams_publicValueModel (V : Type u) [Kernel.SetTheory V]
    (sourcePins targetPins : List Kernel.NatOpPinSet)
    (sourceDeclarations targetDeclarations : Array Kernel.Declaration)
    (sourceEnv targetEnv : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (sourceChecked : Kernel.Cached.checkDecls .verified sourcePins sourceDeclarations = .ok sourceEnv)
    (targetChecked : Kernel.Cached.checkDecls .verified targetPins targetDeclarations = .ok targetEnv)
    (telescopes : checkTelescopes sourceEnv targetEnv names = true)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (definitions : checkInstalledDefinitions sourceEnv targetEnv names = true)
    (falsePin : checkInstalledPin sourceEnv names Kernel.falseName 0 = true)
    (eqPin : checkInstalledPin sourceEnv names Kernel.eqName 1 = true) :
    Nonempty (StrongInstalledModel V sourceEnv) ∧
    ∃ target : StrongInstalledModel V targetEnv, ∃ source : PublicValueModel V sourceEnv,
      source.model.cval = (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval := by
  refine ⟨strongInstalledModel_exists V sourcePins sourceDeclarations sourceEnv sourceChecked, ?_⟩
  obtain ⟨target⟩ := strongInstalledModel_exists V targetPins targetDeclarations targetEnv targetChecked
  have association := checkTelescopes_sound telescopes
  let typeEvidence := checkedPullbackTypes target telescopes types falsePin eqPin
  let definitionEvidence := checkInstalledDefinitions_sound target association definitions
  exact ⟨target, definitionEvidence.valueModel typeEvidence (PullbackMap.fromEnvs_locality association), rfl⟩

/-- One acyclic definition step at the actual installed bodies. Compatibility
is needed only for the body's explicitly supported dependencies, excluding
the source owner itself. Thus the conclusion is not assumed as a constant
case of the renaming law. Recursive/mutual definitions need their separate
simultaneous block argument; theorem/opaque entries supply no such equation.
The exact correspondence of the two annotation outputs remains a premise. -/
theorem StrongInstalledModel.acyclic_definition_value {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env}
    (source : StrongInstalledModel V sourceEnv) (target : StrongInstalledModel V targetEnv)
    {sourceHeader targetHeader : Kernel.ConstantVal} {sourceBody targetBody : Kernel.Expr}
    {sourceHint targetHint : Kernel.ReducibilityHint}
    (sourcePresent : Kernel.ConstantInfo.defnInfo sourceHeader sourceBody sourceHint ∈ sourceEnv.consts)
    (targetPresent : Kernel.ConstantInfo.defnInfo targetHeader targetBody targetHint ∈ targetEnv.consts)
    (rename : InstalledRenaming) (earlier : Kernel.Name → Prop)
    (sourceLevels targetLevels : Kernel.Name → Nat) (ρ : Nat → V)
    (supported : ConstantSupport (fun name => name ≠ sourceHeader.name ∧ earlier name) sourceBody)
    (laws : rename.ScopedLaws (fun name => name ≠ sourceHeader.name ∧ earlier name)
      source.public.cval target.public.cval sourceEnv targetEnv sourceLevels targetLevels)
    (bodyImage : targetBody = rename.expr sourceBody) :
    source.public.cval sourceHeader.name sourceLevels =
      target.public.cval targetHeader.name targetLevels := by
  have sourceRead := source.definition_values _ _ _ sourcePresent sourceLevels ρ
  have transported := InstalledRenaming.denotes_on laws supported sourceRead
  rw [← bodyImage] at transported
  exact Kernel.Denotes_functional transported
    (target.definition_values _ _ _ targetPresent targetLevels ρ)

/-- This exposes the actual fired rule interface, including its universe,
typing, constructor and nested-pin premises. An inert rule supplies no law.
Its currency is still internal AnnotTerm; the public rule bridge remains
an explicit obligation rather than a stronger claim attached to this API. -/
theorem StrongInstalledModel.recursor_rule {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (name : Kernel.Name) (header : Kernel.ConstantVal)
    (major params : Nat) (rules : List Kernel.RecRule)
    (lookup : env.find? name = some (.recInfo header major params rules))
    (rule : Kernel.RecRule) (present : rule ∈ rules) (fires : rule.fire ≠ .inert) :
    Kernel.Model.RecRuleLaw strong.internal.base2 φ name header major params rule :=
  strong.internal.rec_rules φ name header major params rules lookup rule present fires

/-- Public reading of the exact instantiated RHS of a fired stored rule.
The internal witness is retained for the rule's typed/index/nested-pin law;
inert rules provide no such contract. No arbitrary RHS is substituted. -/
theorem StrongInstalledModel.recursor_rhs {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (levels : Kernel.Name → Nat) (name : Kernel.Name) (header : Kernel.ConstantVal)
    (major params : Nat) (rules : List Kernel.RecRule)
    (lookup : env.find? name = some (.recInfo header major params rules))
    (rule : Kernel.RecRule) (present : rule ∈ rules) (fires : rule.fire ≠ .inert)
    (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length) :
    ∃ annotation : Kernel.Semantics.AnnotTerm,
      Kernel.Model.denoteMeta strong.internal.base2.acval env levels 0
        (rule.rhs.instantiateLevelParams header.levelParams universes) = some annotation ∧
      (∀ ρ, Kernel.Model.WellDenotedV V ρ annotation) ∧
      ∀ ρ, Kernel.Denotes strong.public.cval env levels ρ
        (rule.rhs.instantiateLevelParams header.levelParams universes)
        (Kernel.Semantics.interp V ρ annotation) := by
  obtain ⟨annotation, reading, graded, _, _⟩ :=
    (strong.recursor_rule levels name header major params rules lookup rule present fires).2 universes arity
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have ruleWf := wf.2.2.2.2.2.1 header major params rules rfl rule present
  have noFree : (rule.rhs.instantiateLevelParams header.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact ruleWf.1
  have bounded : (rule.rhs.instantiateLevelParams header.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact ruleWf.2.2.2.1
  refine ⟨annotation, reading, graded, ?_⟩
  intro ρ
  have read := Kernel.Model.Denotes_of_denoteMeta strong.internal.base2.cval_closedL
    0 _ reading (noFvars_below_zero noFree) bounded ρ (graded ρ)
  rw [Kernel.Expr.closeN_of_hasFvar _ 0 0 noFree] at read
  exact read

open Kernel Kernel.Model Kernel.Semantics in
/-- The actual fired-rule frame. Every original law premise is retained,
including universe selection, constructor parameter/index positions, both
typed telescopes, and nested pin interpretation. Establishing these internal
frame witnesses from public caller checking remains a separate bridge. -/
structure FiredRecursorFrame {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (header : Kernel.ConstantVal) (major params : Nat) (rule : Kernel.RecRule) (universes : List Kernel.Level) where
  constructor : Kernel.ConstantVal
  constructorParams : Nat
  constructorFields : Nat
  constructorLookup : env.find? rule.ctor =
    some (.ctorInfo constructor constructorParams constructorFields)
  constructorUniverses : List Kernel.Level
  valuation : Nat → V
  arguments : List AnnotTerm
  fields : List AnnotTerm
  recursorType : AnnotTerm
  constructorType : AnnotTerm
  recursorResult : AnnotTerm
  constructorResult : AnnotTerm
  argumentCount : arguments.length = major
  fieldCount : fields.length = rule.ctorParams + rule.nfields
  constructorArity : constructorUniverses.length = constructor.levelParams.length
  universeSelection : Level.substFn levels constructor.levelParams constructorUniverses =
    Level.substFn levels constructor.levelParams
      (recFireComparands rule header.levelParams universes constructor.levelParams [] params).1
  plainParameters : rule.paramsBlind = false → rule.fire = .plain →
    ∀ i, i < rule.ctorParams → i < major →
      interp V valuation (fields.getD i default) = interp V valuation (arguments.getD i default)
  nestedParameters : ∀ lvls pins, rule.fire = .nested lvls pins →
    ∀ i, i < rule.ctorParams → ∀ pin : AnnotTerm,
      denoteMeta strong.internal.base2.acval env levels params
        (Kernel.Verify.openRev 0 params ((pins.getD i default).instantiateLevelParams
          header.levelParams universes)) = some pin →
      interp V valuation (fields.getD i default) =
        interp V valuation (Kernel.Model.AnnotTerm.instRevChain (arguments.take params) pin)
  indexPin : IotaIndexPin valuation constructorResult rule.ctorParams major params arguments
  recursorTypeRead : denoteMeta strong.internal.base2.acval env levels 0
    (header.type.instantiateLevelParams header.levelParams universes) = some recursorType
  constructorTypeRead : denoteMeta strong.internal.base2.acval env levels 0
    (constructor.type.instantiateLevelParams constructor.levelParams constructorUniverses) = some constructorType
  recursorTyped : TeleFitPA V valuation recursorType
    (arguments ++ [AnnotTerm.mkAppN (strong.internal.base2.acval rule.ctor
      (Level.substFn levels constructor.levelParams constructorUniverses)) fields]) recursorResult
  constructorTyped : TeleFitPA V valuation constructorType fields constructorResult

open Kernel Kernel.Model Kernel.Semantics Kernel.SetTheory in
/-- The stored fired law at public semantic values. The RHS reading and
equality share the same internal witness. The frame hypotheses are precisely
the original non-inert rule's hypotheses, not a caller-supplied equality. -/
theorem StrongInstalledModel.recursor_computation {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (levels : Kernel.Name → Nat) (name : Kernel.Name) (header : Kernel.ConstantVal) (major params : Nat)
    (rules : List Kernel.RecRule) (lookup : env.find? name = some (.recInfo header major params rules))
    (rule : Kernel.RecRule) (present : rule ∈ rules) (fires : rule.fire ≠ .inert)
    (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (frame : FiredRecursorFrame strong levels header major params rule universes) :
    ∃ rhsValue : V,
      Denotes strong.public.cval env levels frame.valuation
        (rule.rhs.instantiateLevelParams header.levelParams universes) rhsValue ∧
      app (frame.arguments.foldl (fun value argument => app value (interp V frame.valuation argument))
        (strong.public.cval name (Level.substFn levels header.levelParams universes)))
        (frame.fields.foldl (fun value field => app value (interp V frame.valuation field))
          (strong.public.cval rule.ctor
            (Level.substFn levels frame.constructor.levelParams frame.constructorUniverses))) =
        (frame.arguments.take params ++ frame.fields.drop rule.ctorParams).foldl
          (fun value argument => app value (interp V frame.valuation argument)) rhsValue := by
  obtain ⟨annotation, reading, _, _, law⟩ :=
    (strong.recursor_rule levels name header major params rules lookup rule present fires).2 universes arity
  obtain ⟨publicAnnotation, publicReading, _, publicRead⟩ :=
    strong.recursor_rhs levels name header major params rules lookup rule present fires universes arity
  have same := Option.some.inj (reading.symm.trans publicReading)
  subst publicAnnotation
  have equality := (law frame.constructor frame.constructorParams frame.constructorFields frame.constructorLookup
    frame.constructorUniverses frame.valuation frame.arguments frame.fields frame.recursorType
    frame.constructorType frame.recursorResult frame.constructorResult frame.argumentCount frame.fieldCount
    frame.constructorArity frame.universeSelection frame.plainParameters frame.nestedParameters frame.indexPin
    frame.recursorTypeRead frame.constructorTypeRead frame.recursorTyped frame.constructorTyped).1
  refine ⟨interp V frame.valuation annotation, publicRead frame.valuation, ?_⟩
  simpa only [interp_mkAppN, List.foldl_append, List.foldl_cons, List.foldl_nil,
    interp_cvalOf strong.internal.base2.cval_closedL, StrongInstalledModel.public,
    Kernel.Model.Model.ofEnvModelM] using equality

open Kernel.SetTheory in
/-- Public expression-level reading of both sides of the fired recursor rule.
The argument spines are aligned to the exact internal frame values; the frame
still records the original law's typing/index/nested-pin premises explicitly. -/
theorem StrongInstalledModel.recursor_denotes {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (levels : Kernel.Name → Nat) (name : Kernel.Name) (header : Kernel.ConstantVal) (major params : Nat)
    (rules : List Kernel.RecRule) (lookup : env.find? name = some (.recInfo header major params rules))
    (rule : Kernel.RecRule) (present : rule ∈ rules) (fires : rule.fire ≠ .inert)
    (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (frame : FiredRecursorFrame strong levels header major params rule universes)
    (arguments fields : List Kernel.Expr)
    (argumentRead : DenotesSpine strong.public.cval env levels frame.valuation arguments
      (frame.arguments.map (Kernel.Semantics.interp V frame.valuation)))
    (fieldRead : DenotesSpine strong.public.cval env levels frame.valuation fields
      (frame.fields.map (Kernel.Semantics.interp V frame.valuation))) :
    ∃ value : V,
      Kernel.Denotes strong.public.cval env levels frame.valuation
        (Kernel.Expr.mkAppN (.const name universes)
          (arguments ++ [Kernel.Expr.mkAppN (.const rule.ctor frame.constructorUniverses) fields])) value ∧
      Kernel.Denotes strong.public.cval env levels frame.valuation
        (Kernel.Expr.mkAppN (rule.rhs.instantiateLevelParams header.levelParams universes)
          (arguments.take params ++ fields.drop rule.ctorParams)) value := by
  obtain ⟨rhsValue, rhsRead, computation⟩ := strong.recursor_computation levels name header major params
    rules lookup rule present fires universes arity frame
  have recursorRead := Kernel.Denotes.const (cval := strong.public.cval) (φ := levels)
    (ρ := frame.valuation) (us := universes) lookup arity
  have constructorRead := Kernel.Denotes.const (cval := strong.public.cval) (φ := levels)
    (ρ := frame.valuation) (us := frame.constructorUniverses) frame.constructorLookup frame.constructorArity
  have leftRead := denotes_mkAppN recursorRead
    (argumentRead.append (.cons (denotes_mkAppN constructorRead fieldRead) .nil))
  have rightRead := denotes_mkAppN rhsRead ((argumentRead.take params).append (fieldRead.drop rule.ctorParams))
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_map,
    Kernel.ConstantInfo.toConstantVal] at leftRead
  simp only [← List.map_take, ← List.map_drop, ← List.map_append, List.foldl_map] at rightRead
  rw [computation] at leftRead
  exact ⟨_, leftRead, rightRead⟩

open Kernel.SetTheory in
/-- Equality soundness at the very same strong interpretation. Membership
in the equality's universe and both endpoint types is indispensable: the
set-theoretic application operation has unspecified behaviour off-domain. -/
theorem StrongInstalledModel.eq_sound {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (level : Kernel.Level) (φ : Kernel.Name → Nat) (ρ : Nat → V)
    (E A left right proof : V)
    (eqDenotes : Kernel.Denotes strong.public.cval env φ ρ (.const Kernel.eqName [level]) E)
    (universeMember : A ∈ˢ univ (Kernel.Level.eval φ level))
    (leftTyped : left ∈ˢ A) (rightTyped : right ∈ˢ A)
    (proved : proof ∈ˢ app (app (app E A) left) right) : left = right := by
  have equality := strong.public.eq_equality level φ ρ E A left right eqDenotes universeMember leftTyped rightTyped
  rw [equality] at proved
  exact mem_eqv proved

open Kernel.SetTheory Kernel.Semantics Kernel.SetModel Kernel.Model in
/-- Recover all three Eq argument domains from the exact internal grading.
The pinned Eq type has three graph-regime binders; graph-domain uniqueness
identifies the otherwise existential application domains. -/
theorem StrongInstalledModel.graded_eq_arguments {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (lookup : env.find? Kernel.eqName = some Kernel.eqA)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (carrier left right : AnnotTerm)
    (graded : WellDenotedV V ρ
      (.app (.app (.app (strong.internal.base2.acval Kernel.eqName levels) carrier) left) right)) :
    interp V ρ carrier ∈ˢ univ (levels Kernel.uN) ∧
      interp V ρ left ∈ˢ interp V ρ carrier ∧ interp V ρ right ∈ˢ interp V ρ carrier := by
  have carrierTyped := eqSlot_univ strong.internal lookup levels graded
  obtain ⟨type, read, _, member⟩ := strong.internal.acval_memType lookup levels
  rw [denoteMeta_eqA_type_gen] at read
  obtain rfl : type = eqTy levels := (Option.some.inj read).symm
  have eqTyped := member ρ
  rw [eqTy_interp] at eqTyped
  have firstTyped : interp V ρ (.app (strong.internal.base2.acval Kernel.eqName levels) carrier)
      ∈ˢ piR 1 (interp V ρ carrier) (fun _ => piR 1 (interp V ρ carrier) (fun _ => univZero)) := by
    rw [interp_app]
    exact app_mem_piR_pos Nat.one_ne_zero eqTyped carrierTyped
  have rightSlot := graded.1
  rw [WellDenoted_app] at rightSlot
  have leftSlot := rightSlot.1
  rw [WellDenoted_app] at leftSlot
  obtain ⟨_, _, _, _, _, leftFunction, leftArgument, _⟩ := leftSlot
  have leftTyped := io_domain_transfer Nat.one_ne_zero leftFunction leftArgument firstTyped
  have secondTyped : interp V ρ
      (.app (.app (strong.internal.base2.acval Kernel.eqName levels) carrier) left)
      ∈ˢ piR 1 (interp V ρ carrier) (fun _ => univZero) := by
    rw [interp_app]
    exact app_mem_piR_pos Nat.one_ne_zero firstTyped leftTyped
  obtain ⟨_, _, _, _, _, rightFunction, rightArgument, _⟩ := rightSlot
  exact ⟨carrierTyped, leftTyped,
    io_domain_transfer Nat.one_ne_zero rightFunction rightArgument secondTyped⟩

open Kernel.SetTheory Kernel.Semantics Kernel.SetModel Kernel.Model in
/-- A graded, inhabited exact Eq spine proves equality in the same strong
model. Grading is indispensable and remains explicit at this interface. -/
theorem StrongInstalledModel.graded_eq_sound {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (lookup : env.find? Kernel.eqName = some Kernel.eqA)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (carrier left right : AnnotTerm)
    (graded : WellDenotedV V ρ
      (.app (.app (.app (strong.internal.base2.acval Kernel.eqName levels) carrier) left) right))
    {proof : V} (member : proof ∈ˢ interp V ρ
      (.app (.app (.app (strong.internal.base2.acval Kernel.eqName levels) carrier) left) right)) :
    interp V ρ left = interp V ρ right := by
  obtain ⟨carrierTyped, leftTyped, rightTyped⟩ :=
    strong.graded_eq_arguments lookup levels ρ carrier left right graded
  have law := (strong.internal.eq_law lookup levels).1 ρ
    (interp V ρ carrier) (interp V ρ left) (interp V ρ right) carrierTyped leftTyped rightTyped
  simp only [interp_app] at member
  rw [law] at member
  exact mem_eqv member

open Kernel.Semantics Kernel.Model in
/-- A public installed expression with its exact scoped internal reading.
The closure equation retains the actual annotation, including all binder bits. -/
def GradedReading {V : Type u} [Kernel.SetTheory V]
    (acval : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm)
    (env : Kernel.Env) (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (expression : Kernel.Expr) : Prop :=
  ∃ depth opened annotation,
    denoteMeta acval env levels depth opened = some annotation ∧
    Kernel.Expr.fvarsBelow depth opened ∧ opened.looseBVarsBounded 0 = true ∧
    opened.closeN depth = expression ∧ WellDenotedV V ρ annotation

open Kernel.Semantics Kernel.Model in
/-- Public typed telescope application preserves the actual internal grading.
Every binder is opened and closed through the existing proved closure law;
public denotation alone is not substituted for the stronger invariant. -/
theorem InstalledTelescope.graded_reading {V : Type u} [Kernel.SetTheory V]
    {acval : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm}
    (closed : ∀ name levels, Kernel.Term.Term.Closed (acval name levels).erase)
    {env : Kernel.Env} {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope (cvalOf acval) env levels ρ expression arguments finalρ result)
    (read : GradedReading acval env levels ρ expression) :
    GradedReading acval env levels finalρ result := by
  revert read
  induction typed with
  | nil => exact fun read => read
  | cons domainDenoted argumentTyped rest ih =>
    intro read
    obtain ⟨depth, opened, annotation, reading, scope, bounded, image, graded⟩ := read
    cases opened <;> simp only [Kernel.Expr.closeN] at image
    all_goals try cases image
    case cons.forallE.refl =>
      rename_i rawDomain rawBody
      obtain ⟨domainAnnotation, bodyAnnotation, domainRead, bodyRead, rfl⟩ :=
        denoteMeta_forallE_inv reading
      have scopedParts : Kernel.Expr.fvarsBelow depth rawDomain ∧
          Kernel.Expr.fvarsBelow depth rawBody := scope
      have boundedParts : rawDomain.looseBVarsBounded 0 = true ∧
          rawBody.looseBVarsBounded 1 = true := by
        simpa only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] using bounded
      have domainGrade := graded.1
      have domainBits := graded.2
      rw [WellDenoted_pi] at domainGrade
      rw [AnnotValid_pi] at domainBits
      have publicDomain := Denotes_of_denoteMeta closed depth rawDomain domainRead
        scopedParts.1 boundedParts.1 _ ⟨domainGrade.1, domainBits.1⟩
      have same := Kernel.Denotes_functional domainDenoted publicDomain
      rw [same] at argumentTyped
      apply ih
      refine ⟨depth + 1, rawBody.instantiate1 (.fvar depth rawDomain), bodyAnnotation,
        bodyRead, Kernel.Expr.fvarsBelow_instantiate1 0 scopedParts.2,
        Kernel.looseBVarsBounded_instantiate1 rawBody 0 boundedParts.2,
        Kernel.Expr.closeN_instantiate1 rawBody 0 boundedParts.2 scopedParts.2, ?_⟩
      rw [push_eq_cons]
      exact ⟨domainGrade.2 _ argumentTyped, domainBits.2.1 _ argumentTyped⟩

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- A public typed application spine with exact scoped argument readings.
Unlike a value-only telescope, its residual is the actual capture-avoiding
substitution of each expression, as required by the fired recursor law. The
argument reading/grading premises must come from caller checking; they are
not inferred from public denotation alone. -/
inductive AnnotatedApplication {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (depth : Nat) (ρ : Nat → V) :
    Kernel.Expr → List Kernel.Expr → List AnnotTerm → Kernel.Expr → Prop
  | nil {type} : AnnotatedApplication strong levels depth ρ type [] [] type
  | cons {domain body binder expression annotation expressions annotations residual A}
      (domainRead : Kernel.Denotes strong.public.cval env levels ρ (domain.closeN depth) A)
      (argumentRead : denoteMeta strong.internal.base2.acval env levels depth expression = some annotation)
      (argumentScope : Kernel.Expr.WScoped depth expression)
      (argumentBounded : expression.looseBVarsBounded 0 = true)
      (argumentGraded : WellDenotedV V ρ annotation)
      (argumentTyped : interp V ρ annotation ∈ˢ A)
      (rest : AnnotatedApplication strong levels depth ρ (body.instantiate1 expression)
        expressions annotations residual) :
      AnnotatedApplication strong levels depth ρ (.forallE domain body binder)
        (expression :: expressions) (annotation :: annotations) residual

open Kernel.Semantics Kernel.Model in
/-- The actual internal reading of one argument. Semantic domain membership
is supplied separately by the public dependent application, not assumed here. -/
structure ArgumentAnnotation {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (depth : Nat) (ρ : Nat → V) (expression : Kernel.Expr) (annotation : AnnotTerm) : Prop where
  reading : denoteMeta strong.internal.base2.acval env levels depth expression = some annotation
  scope : Kernel.Expr.WScoped depth expression
  bounded : expression.looseBVarsBounded 0 = true
  graded : WellDenotedV V ρ annotation

inductive ArgumentAnnotations {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (depth : Nat) (ρ : Nat → V) : List Kernel.Expr → List Kernel.Semantics.AnnotTerm → Prop
  | nil : ArgumentAnnotations strong levels depth ρ [] []
  | cons {expression annotation expressions annotations}
      (head : ArgumentAnnotation strong levels depth ρ expression annotation)
      (tail : ArgumentAnnotations strong levels depth ρ expressions annotations) :
      ArgumentAnnotations strong levels depth ρ (expression :: expressions) (annotation :: annotations)

open Kernel.Semantics Kernel.Model in
theorem ArgumentAnnotation.app_inv {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {function argument : Kernel.Expr} {annotation : AnnotTerm}
    (evidence : ArgumentAnnotation strong levels depth ρ (.app function argument) annotation) :
    ∃ functionAnnotation argumentAnnotation,
      ArgumentAnnotation strong levels depth ρ function functionAnnotation ∧
      ArgumentAnnotation strong levels depth ρ argument argumentAnnotation ∧
      annotation = .app functionAnnotation argumentAnnotation := by
  obtain ⟨functionAnnotation, argumentAnnotation, functionRead, argumentRead, rfl⟩ :=
    denoteMeta_app_inv evidence.reading
  have scope : Kernel.Expr.WScoped depth function ∧ Kernel.Expr.WScoped depth argument := by
    simpa only [Kernel.Expr.WScoped] using evidence.scope
  have bounded : function.looseBVarsBounded 0 = true ∧ argument.looseBVarsBounded 0 = true := by
    simpa only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] using evidence.bounded
  exact ⟨functionAnnotation, argumentAnnotation,
    ⟨functionRead, scope.1, bounded.1, WellDenotedV_app_fn evidence.graded⟩,
    ⟨argumentRead, scope.2, bounded.2, WellDenotedV_app_arg evidence.graded⟩, rfl⟩

open Kernel.Semantics Kernel.Model in
/-- Decompose an actual graded residual reading into its actual head and
argument readings. Grading/scoping is inherited, not supplied per index. -/
theorem ArgumentAnnotation.spine {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {head : Kernel.Expr} {expressions : List Kernel.Expr} {annotation : AnnotTerm}
    (evidence : ArgumentAnnotation strong levels depth ρ (Kernel.Expr.mkAppN head expressions) annotation) :
    ∃ headAnnotation annotations,
      ArgumentAnnotation strong levels depth ρ head headAnnotation ∧
      ArgumentAnnotations strong levels depth ρ expressions annotations ∧
      annotation = AnnotTerm.mkAppN headAnnotation annotations := by
  induction expressions generalizing head annotation with
  | nil => exact ⟨annotation, [], evidence, .nil, rfl⟩
  | cons expression expressions ih =>
    obtain ⟨applicationAnnotation, annotations, applicationRead, restRead, shape⟩ := ih evidence
    obtain ⟨headAnnotation, argumentAnnotation, headRead, argumentRead, applicationShape⟩ := applicationRead.app_inv
    exact ⟨headAnnotation, argumentAnnotation :: annotations, headRead, .cons argumentRead restRead,
      by simpa only [applicationShape, AnnotTerm.mkAppN] using shape⟩

open Kernel.Semantics Kernel.Model in
theorem ArgumentAnnotations.denotes {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth ρ expressions annotations) :
    DenotesSpine strong.public.cval env levels ρ (expressions.map (Kernel.Expr.closeN depth))
      (annotations.map (interp V ρ)) := by
  induction readings with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth _ head.reading
      head.scope.fvarsBelow head.bounded ρ head.graded) ih

theorem ArgumentAnnotations.append {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {left right : List Kernel.Expr}
    {leftRead rightRead : List Kernel.Semantics.AnnotTerm}
    (first : ArgumentAnnotations strong levels depth ρ left leftRead)
    (second : ArgumentAnnotations strong levels depth ρ right rightRead) :
    ArgumentAnnotations strong levels depth ρ (left ++ right) (leftRead ++ rightRead) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

open Kernel.Semantics Kernel.Model in
theorem ArgumentAnnotations.facts {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth ρ expressions annotations) :
    DenoteMetaSpine strong.internal.base2.acval env levels depth expressions annotations ∧
      (∀ expression ∈ expressions, Kernel.Expr.WScoped depth expression ∧
        expression.looseBVarsBounded 0 = true) ∧
      (∀ annotation ∈ annotations, WellDenotedV V ρ annotation) := by
  induction readings with
  | nil => exact ⟨.nil, by simp, by simp⟩
  | cons head tail ih =>
    refine ⟨.cons head.reading ih.1, ?_, ?_⟩
    · intro expression member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨head.scope, head.bounded⟩
      · exact ih.2.1 expression member
    · intro annotation member
      rcases List.mem_cons.mp member with rfl | member
      · exact head.graded
      · exact ih.2.2 annotation member

open Kernel.Semantics Kernel.Model in
/-- Build the internal index pin from an actual graded residual reading and
public meanings of its index spine. The equality premise is a semantic
comparison of index values, not a guessed equality of syntax or lengths. -/
theorem ArgumentAnnotation.index_pin {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {head : Kernel.Expr} {expressions : List Kernel.Expr} {annotation : AnnotTerm}
    (evidence : ArgumentAnnotation strong levels depth ρ (Kernel.Expr.mkAppN head expressions) annotation)
    (values : List V)
    (read : DenotesSpine strong.public.cval env levels ρ (expressions.map (Kernel.Expr.closeN depth)) values)
    (arguments : List AnnotTerm) (constructorParams major rulePrefix : Nat)
    (argumentCount : arguments.length = major) (ordered : rulePrefix ≤ major)
    (indices : values.drop constructorParams = (arguments.drop rulePrefix).map (interp V ρ)) :
    IotaIndexPin ρ annotation constructorParams major rulePrefix arguments := by
  obtain ⟨headAnnotation, annotations, _, readings, shape⟩ := evidence.spine
  have meanings := readings.denotes.functional read
  have compared : (annotations.drop constructorParams).map (interp V ρ) =
      (arguments.drop rulePrefix).map (interp V ρ) := by
    rw [List.map_drop, meanings]
    exact indices
  have counts := congrArg List.length compared
  simp only [List.length_map, List.length_drop, argumentCount] at counts
  have lengthCondition : major = rulePrefix ∨ annotations.length = constructorParams + (major - rulePrefix) := by
    omega
  refine ⟨headAnnotation, annotations, shape, lengthCondition, ?_⟩
  intro index inside
  have bounded : index < (annotations.drop constructorParams).length := by
    simp only [List.length_drop]
    omega
  have constructorBound : constructorParams + index < annotations.length := by
    simp only [List.length_drop] at bounded
    omega
  have argumentBound : rulePrefix + index < arguments.length := by omega
  have equal := congrArg (fun values : List V => values[index]?) compared
  simp only [List.getElem?_map, List.getElem?_drop,
    List.getElem?_eq_getElem constructorBound, List.getElem?_eq_getElem argumentBound,
    Option.map_some, Option.some.injEq] at equal
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem constructorBound,
    List.getElem?_eq_getElem argumentBound, Option.getD_some] using equal

open Kernel.Semantics Kernel.Model in
/-- Transport the source's public index-value equation into the target's
actual internal index pin. Target residual and argument annotations are
real graded readings; component images carry the source meanings into them.
The source index equation remains the exact reduction premise to discharge. -/
theorem ArgumentAnnotation.index_pin_image {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} {target : StrongInstalledModel V targetEnv}
    {targetLevels : Kernel.Name → Nat} {depth : Nat} {ρ : Nat → V}
    {head : Kernel.Expr} {targetIndices targetArguments : List Kernel.Expr}
    {annotation : AnnotTerm} {arguments : List AnnotTerm}
    (evidence : ArgumentAnnotation target targetLevels depth ρ (Kernel.Expr.mkAppN head targetIndices) annotation)
    (argumentReadings : ArgumentAnnotations target targetLevels depth ρ targetArguments arguments)
    {sourceValues : Kernel.Name → (Kernel.Name → Nat) → V} {sourceEnv : Kernel.Env}
    {sourceLevels : Kernel.Name → Nat} {sourceIndices sourceArguments : List Kernel.Expr}
    {indexValues argumentValues : List V}
    (indexRead : DenotesSpine sourceValues sourceEnv sourceLevels ρ sourceIndices indexValues)
    (argumentRead : DenotesSpine sourceValues sourceEnv sourceLevels ρ sourceArguments argumentValues)
    (indexImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceIndices (targetIndices.map (Kernel.Expr.closeN depth)))
    (argumentImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceArguments (targetArguments.map (Kernel.Expr.closeN depth)))
    (constructorParams major rulePrefix : Nat)
    (argumentCount : arguments.length = major) (ordered : rulePrefix ≤ major)
    (sourceEquation : indexValues.drop constructorParams = argumentValues.drop rulePrefix) :
    IotaIndexPin ρ annotation constructorParams major rulePrefix arguments := by
  have argumentMeanings := (argumentRead.image argumentImages).functional argumentReadings.denotes
  apply evidence.index_pin indexValues (indexRead.image indexImages) arguments constructorParams major rulePrefix
    argumentCount ordered
  rw [sourceEquation, argumentMeanings, List.map_drop]

theorem AnnotatedApplication.argument_annotations {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual) :
    ArgumentAnnotations strong levels depth ρ expressions annotations := by
  induction application with
  | nil => exact .nil
  | cons _ reading scope bounded graded _ _ ih => exact .cons ⟨reading, scope, bounded, graded⟩ ih

open Kernel.Semantics Kernel.Model in
/-- Assemble an internal annotated application from the public dependent fit
and the arguments' actual scoped readings. Closing/substitution correspondence
preserves the exact residual; no independently chosen type is substituted. -/
theorem AnnotatedApplication.of_public {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type publicResidual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth ρ expressions annotations)
    (application : DenotedApplication strong.public.cval env levels ρ (type.closeN depth)
      (expressions.map (Kernel.Expr.closeN depth)) (annotations.map (interp V ρ)) publicResidual)
    (bounded : type.looseBVarsBounded 0 = true) :
    ∃ residual, AnnotatedApplication strong levels depth ρ type expressions annotations residual ∧
      residual.closeN depth = publicResidual := by
  induction readings generalizing type publicResidual with
  | nil =>
    have equal : publicResidual = type.closeN depth := by
      generalize type.closeN depth = closedType at application ⊢
      cases application
      rfl
    exact ⟨type, .nil, equal.symm⟩
  | @cons expression annotation expressions annotations evidence tail ih =>
    cases type with
    | forallE domain body binder =>
      cases application with
      | cons domainRead argumentRead argumentTyped rest =>
        have bounds : domain.looseBVarsBounded 0 = true ∧ body.looseBVarsBounded 1 = true := by
          simpa only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] using bounded
        have converted : DenotedApplication strong.public.cval env levels ρ
            ((body.instantiate1 expression).closeN depth)
            (expressions.map (Kernel.Expr.closeN depth))
            (annotations.map (interp V ρ)) publicResidual := by
          rw [closeN_substitution body expression depth evidence.bounded 0 bounds.2]
          exact rest
        obtain ⟨residual, fitted, equal⟩ := ih converted
          (Kernel.Expr.looseBVarsBounded_instantiate1_gen evidence.bounded bounds.2)
        exact ⟨residual, .cons domainRead evidence.reading evidence.scope evidence.bounded
          evidence.graded argumentTyped fitted, equal⟩
    | _ => cases application

open Kernel.Semantics in
/-- Independently typed tuples can use one shared caller valuation. Their
actual expression readings must represent exactly the original semantic
arguments; ambient values outside the closed installed type are irrelevant. -/
theorem AnnotatedApplication.represented_arguments {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {ρ finalρ target : Nat → V} {type result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope strong.public.cval env levels ρ type arguments finalρ result)
    (bounded : type.looseBVarsBounded 0 = true) (noFvars : type.hasFvar = false)
    {depth : Nat} {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth target expressions annotations)
    (represented : annotations.map (interp V target) = arguments) :
    ∃ residual, AnnotatedApplication strong levels depth target type expressions annotations residual := by
  obtain ⟨_, rebased⟩ := typed.rebase bounded
    (target := target) (fun index impossible => False.elim (Nat.not_lt_zero index impossible))
  have valuesRead := readings.denotes
  rw [represented] at valuesRead
  obtain ⟨publicResidual, applied⟩ := DenotedApplication.of_telescope rebased valuesRead
  have aligned : DenotedApplication strong.public.cval env levels target (type.closeN depth)
      (expressions.map (Kernel.Expr.closeN depth)) (annotations.map (interp V target)) publicResidual := by
    rw [Kernel.Expr.closeN_of_hasFvar type _ _ noFvars, represented]
    exact applied
  obtain ⟨residual, fitted, _⟩ := AnnotatedApplication.of_public readings aligned bounded
  exact ⟨residual, fitted⟩

/-- Symbolic arguments, with their metadata supplied explicitly by the caller.
The semantic representation theorem checks scope only; it does not claim that
the supplied metadata has passed inference or is the argument's source type. -/
def argumentFVars (count : Nat) (metadata : Nat → Kernel.Expr) : List Kernel.Expr :=
  (List.range count).map fun index => .fvar index (metadata index)

def argumentReadings (count : Nat) : List Kernel.Semantics.AnnotTerm :=
  (List.range count).map fun index => .bvar (count - 1 - index)

open Kernel.Semantics Kernel.Model in
theorem ArgumentAnnotation.variable {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (depth : Nat) (ρ : Nat → V) (index : Nat) (metadata : Kernel.Expr)
    (inside : index < depth) (scope : Kernel.Expr.WScoped index metadata) :
    ArgumentAnnotation strong levels depth ρ (.fvar index metadata)
      (.bvar (depth - 1 - index)) := by
  constructor
  · simp [denoteMeta]
  · simpa only [Kernel.Expr.WScoped] using And.intro inside scope
  · rfl
  · simp [WellDenotedV]

theorem ArgumentAnnotations.variables {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (depth : Nat) (ρ : Nat → V) (metadata : Nat → Kernel.Expr)
    (scope : ∀ index, index < depth → Kernel.Expr.WScoped index (metadata index)) :
    ArgumentAnnotations strong levels depth ρ (argumentFVars depth metadata) (argumentReadings depth) := by
  have all : ∀ indices : List Nat, (∀ index ∈ indices, index < depth) →
      ArgumentAnnotations strong levels depth ρ
        (indices.map fun index => .fvar index (metadata index))
        (indices.map fun index => .bvar (depth - 1 - index)) := by
    intro indices
    induction indices with
    | nil => intro _; exact .nil
    | cons index rest ih =>
      intro inside
      have bound := inside index (by simp)
      exact .cons (ArgumentAnnotation.variable strong levels depth ρ index (metadata index)
        bound (scope index bound)) (ih fun i hi => inside i (by simp [hi]))
  exact all (List.range depth) (by intro index inside; exact List.mem_range.mp inside)

theorem argumentFVars_closed (count : Nat) (metadata : Nat → Kernel.Expr) :
    (argumentFVars count metadata).map (Kernel.Expr.closeN count) = argumentVariables count := by
  simp [argumentFVars, argumentVariables, List.map_map, Kernel.Expr.closeN]

open Kernel.Semantics in
theorem argumentReadings_values {V : Type u} [Kernel.SetTheory V]
    (ρ : Nat → V) (arguments : List V) :
    (argumentReadings arguments.length).map (interp V (pushArguments ρ arguments)) = arguments := by
  apply List.ext_getElem
  · simp [argumentReadings]
  · intro index first second
    simpa [argumentReadings] using pushArguments_get arguments ρ index second

open Kernel.Semantics in
/-- An arbitrary tuple against a closed installed type yields the exact
internal annotated application. The argument annotations are derived from
actual `denoteMeta` variable readings, not assumed as arbitrary witnesses. -/
theorem AnnotatedApplication.arbitrary_arguments {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {ρ finalρ : Nat → V} {type result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope strong.public.cval env levels ρ type arguments finalρ result)
    (bounded : type.looseBVarsBounded 0 = true) (noFvars : type.hasFvar = false)
    (metadata : Nat → Kernel.Expr)
    (scope : ∀ index, index < arguments.length → Kernel.Expr.WScoped index (metadata index)) :
    ∃ residual, AnnotatedApplication strong levels arguments.length (pushArguments ρ arguments)
      type (argumentFVars arguments.length metadata) (argumentReadings arguments.length) residual := by
  obtain ⟨publicResidual, applied⟩ := DenotedApplication.arbitrary_arguments typed bounded
  have aligned : DenotedApplication strong.public.cval env levels (pushArguments ρ arguments)
      (type.closeN arguments.length)
      ((argumentFVars arguments.length metadata).map (Kernel.Expr.closeN arguments.length))
      ((argumentReadings arguments.length).map (interp V (pushArguments ρ arguments))) publicResidual := by
    rw [Kernel.Expr.closeN_of_hasFvar type _ _ noFvars, argumentFVars_closed, argumentReadings_values]
    exact applied
  obtain ⟨residual, fitted, _⟩ := AnnotatedApplication.of_public
    (ArgumentAnnotations.variables strong levels arguments.length (pushArguments ρ arguments) metadata scope)
    aligned bounded
  exact ⟨residual, fitted⟩

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Construct the recursor law's exact substitution-peeling fit from the
public domain typings. The residual reading is proved for the actual
instantiated expression, not chosen merely to have an equal interpretation. -/
theorem AnnotatedApplication.internal_fit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual)
    {typeAnnotation : AnnotTerm}
    (typeRead : denoteMeta strong.internal.base2.acval env levels depth type = some typeAnnotation)
    (typeScope : Kernel.Expr.WScoped depth type)
    (typeBounded : type.looseBVarsBounded 0 = true)
    (typeGraded : WellDenotedV V ρ typeAnnotation) :
    ∃ residualAnnotation,
      TeleFitPA V ρ typeAnnotation annotations residualAnnotation ∧
      denoteMeta strong.internal.base2.acval env levels depth residual = some residualAnnotation ∧
      WellDenotedV V ρ residualAnnotation := by
  induction application generalizing typeAnnotation with
  | nil => exact ⟨typeAnnotation, .nil, typeRead, typeGraded⟩
  | @cons domain body binder expression annotation expressions annotations residual A
      domainRead argumentRead argumentScope argumentBounded argumentGraded argumentTyped rest ih =>
    obtain ⟨domainAnnotation, bodyAnnotation, domainReading, bodyReading, rfl⟩ :=
      denoteMeta_forallE_inv typeRead
    have scopeParts : Kernel.Expr.WScoped depth domain ∧ Kernel.Expr.WScoped depth body := by
      simpa only [Kernel.Expr.WScoped] using typeScope
    have boundParts : domain.looseBVarsBounded 0 = true ∧ body.looseBVarsBounded 1 = true := by
      simpa only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] using typeBounded
    have domainGrade := typeGraded.1
    have domainBits := typeGraded.2
    rw [WellDenoted_pi] at domainGrade
    rw [AnnotValid_pi] at domainBits
    have publicDomain := Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth domain
      domainReading scopeParts.1.fvarsBelow boundParts.1 ρ ⟨domainGrade.1, domainBits.1⟩
    have same := Kernel.Denotes_functional domainRead publicDomain
    rw [same] at argumentTyped
    have bodyRun : denoteMeta strong.internal.base2.acval env levels depth
        (body.instantiate1 expression) = some (bodyAnnotation.inst annotation) := by
      rw [denoteMeta_beta strong.internal.base2.acval_closed (acval_inst_self strong.internal.base2)
        scopeParts.2.fvarsBelow argumentScope argumentBounded argumentRead 0, bodyReading]
      rfl
    have bodyGrade : WellDenotedV V ρ (bodyAnnotation.inst annotation) :=
      (WellDenotedV_inst0 argumentGraded).mpr
        ⟨domainGrade.2 _ argumentTyped, domainBits.2.1 _ argumentTyped⟩
    obtain ⟨result, fit, reading, graded⟩ := ih bodyRun
      (Kernel.Expr.WScoped.instantiate1_gen argumentScope 0 scopeParts.2)
      (Kernel.Expr.looseBVarsBounded_instantiate1_gen argumentBounded boundParts.2) bodyGrade
    exact ⟨result, .cons argumentTyped fit, reading, graded⟩

open Kernel.Semantics Kernel.Model in
theorem AnnotatedApplication.denotes_arguments {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual) :
    DenotesSpine strong.public.cval env levels ρ (expressions.map (Kernel.Expr.closeN depth))
      (annotations.map (interp V ρ)) := by
  induction application with
  | nil => exact .nil
  | cons _ argumentRead argumentScope argumentBounded argumentGraded _ _ ih =>
    exact .cons (Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth _ argumentRead
      argumentScope.fvarsBelow argumentBounded ρ argumentGraded) ih

open Kernel.Semantics Kernel.Model in
/-- Construct the target's actual annotated dependent application from the
source public application and semantic component images. Actual target
readings determine the argument values; their equality is proved, not assumed.
The output retains the image of the complete substituted residual. -/
theorem AnnotatedApplication.from_source {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} {target : StrongInstalledModel V targetEnv}
    {targetLevels : Kernel.Name → Nat} {depth : Nat} {ρ : Nat → V}
    {targetType : Kernel.Expr} {targetExpressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations target targetLevels depth ρ targetExpressions annotations)
    {sourceValues : Kernel.Name → (Kernel.Name → Nat) → V} {sourceEnv : Kernel.Env}
    {sourceLevels : Kernel.Name → Nat} {sourceType sourceResidual : Kernel.Expr}
    {sourceExpressions : List Kernel.Expr} {values : List V}
    (application : DenotedApplication sourceValues sourceEnv sourceLevels ρ
      sourceType sourceExpressions values sourceResidual)
    (typeImage : InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceType (targetType.closeN depth))
    (argumentImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceExpressions (targetExpressions.map (Kernel.Expr.closeN depth)))
    (bounded : targetType.looseBVarsBounded 0 = true) :
    ∃ residual, AnnotatedApplication target targetLevels depth ρ targetType targetExpressions annotations residual ∧
      InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
        sourceResidual (residual.closeN depth) := by
  have equalValues := (application.arguments.image argumentImages).functional readings.denotes
  obtain ⟨publicResidual, targetApplication, residualImage⟩ := application.image typeImage argumentImages
  rw [equalValues] at targetApplication
  obtain ⟨residual, actual, closed⟩ := AnnotatedApplication.of_public readings targetApplication bounded
  exact ⟨residual, actual, by simpa only [closed] using residualImage⟩

open Kernel.Semantics Kernel.Model in
/-- Specialize application transport to the type fields checked in the
actual installed source/target rows. Target scope/bounds and type-image
premises are discharged by installation and executable type association. -/
theorem AnnotatedApplication.from_checked_type {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourcePresent : sourceEntry ∈ sourceEnv.consts)
    (targetLookup : targetEnv.find? (names sourceEntry.name) = some targetEntry)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    {depth : Nat} {ρ : Nat → V} {targetExpressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations target targetLevels depth ρ targetExpressions annotations)
    {sourceExpressions : List Kernel.Expr} {values : List V} {sourceResidual : Kernel.Expr}
    (application : DenotedApplication
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels ρ
      (sourceEntry.toConstantVal.type.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs)
      sourceExpressions values sourceResidual)
    (argumentImages : InstalledSpineImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceExpressions (targetExpressions.map (Kernel.Expr.closeN depth))) :
    ∃ residual, AnnotatedApplication target targetLevels depth ρ
      (targetEntry.toConstantVal.type.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs)
      targetExpressions annotations residual ∧
      InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        target.public.cval sourceEnv targetEnv sourceLevels targetLevels sourceResidual (residual.closeN depth) := by
  obtain ⟨sourceLookup, found, foundLookup, comparison⟩ := checkInstalledTypes_member types sourcePresent
  have same := Option.some.inj (foundLookup.symm.trans targetLookup)
  subst found
  have wf := target.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetLookup)
  have typeImage := checkInstalledMemberExpr_instance target association sourceLookup targetLookup wf.2.1
    comparison sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
  have noFree : (targetEntry.toConstantVal.type.instantiateLevelParams
      targetEntry.toConstantVal.levelParams targetUs).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact wf.1
  have bounded : (targetEntry.toConstantVal.type.instantiateLevelParams
      targetEntry.toConstantVal.levelParams targetUs).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact wf.2.2.2.1
  apply AnnotatedApplication.from_source readings application _ argumentImages bounded
  simpa only [Kernel.Expr.closeN_of_hasFvar _ depth 0 noFree] using typeImage

theorem AnnotatedApplication.residual_shape {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual) :
    Kernel.piResidual type expressions = some residual := by
  induction application with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => exact ih

theorem AnnotatedApplication.residual_scope {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual)
    (typeScope : Kernel.Expr.WScoped depth type) (typeBounded : type.looseBVarsBounded 0 = true) :
    Kernel.Expr.WScoped depth residual ∧ residual.looseBVarsBounded 0 = true := by
  induction application with
  | nil => exact ⟨typeScope, typeBounded⟩
  | cons _ _ argumentScope argumentBounded _ _ _ ih =>
    simp only [Kernel.Expr.WScoped] at typeScope
    simp only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at typeBounded
    exact ih (Kernel.Expr.WScoped.instantiate1_gen argumentScope 0 typeScope.2)
      (Kernel.Expr.looseBVarsBounded_instantiate1_gen argumentBounded typeBounded.2)

open Kernel.Semantics Kernel.Model in
/-- Public residual denotation, attached to the exact checker `piResidual`.
This supplies the semantic residual without conflating value-level argument
extension with the recursor law's syntactic substitution chain. -/
theorem AnnotatedApplication.denotes_residual {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual)
    {typeAnnotation : AnnotTerm}
    (typeRead : denoteMeta strong.internal.base2.acval env levels depth type = some typeAnnotation)
    (typeScope : Kernel.Expr.WScoped depth type)
    (typeBounded : type.looseBVarsBounded 0 = true)
    (typeGraded : WellDenotedV V ρ typeAnnotation) :
    ∃ residualAnnotation,
      Kernel.piResidual type expressions = some residual ∧
      TeleFitPA V ρ typeAnnotation annotations residualAnnotation ∧
      denoteMeta strong.internal.base2.acval env levels depth residual = some residualAnnotation ∧
      Kernel.Denotes strong.public.cval env levels ρ (residual.closeN depth)
        (interp V ρ residualAnnotation) := by
  obtain ⟨annotation, fit, reading, graded⟩ :=
    application.internal_fit typeRead typeScope typeBounded typeGraded
  obtain ⟨scope, bounded⟩ := application.residual_scope typeScope typeBounded
  exact ⟨annotation, application.residual_shape, fit, reading,
    Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth residual reading
      scope.fvarsBelow bounded ρ graded⟩

open Kernel.Semantics Kernel.Model in
theorem StrongInstalledModel.graded_type {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (constant : Kernel.ConstantInfo) (present : constant ∈ env.consts)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    GradedReading strong.internal.base2.acval env levels ρ constant.toConstantVal.type := by
  obtain ⟨annotation, read⟩ := strong.internal.type_reads constant present levels
  have wellFormed := strong.internal.base2.wf constant present
  exact ⟨0, constant.toConstantVal.type, annotation, read,
    noFvars_below_zero wellFormed.1, wellFormed.2.2.2.1,
    Kernel.Expr.closeN_of_hasFvar _ 0 0 wellFormed.1,
    strong.internal.type_wellDenotedV constant present levels annotation read ρ⟩

open Kernel.Semantics Kernel.Model in
/-- Initial reading/grading for an application comes from the actual stored
constant at its actual universe instance. The same annotation reads at depth
zero and at the caller's open depth because the installed type is closed. -/
theorem StrongInstalledModel.instantiated_type {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (levels : Kernel.Name → Nat) (depth : Nat) (name : Kernel.Name) (constant : Kernel.ConstantInfo)
    (lookup : env.find? name = some constant) (termEntry : constant.isTowerEntry = false)
    (universes : List Kernel.Level) (arity : universes.length = constant.toConstantVal.levelParams.length) :
    ∃ annotation,
      denoteMeta strong.internal.base2.acval env levels 0
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes) =
          some annotation ∧
      denoteMeta strong.internal.base2.acval env levels depth
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes) =
          some annotation ∧
      ∀ ρ, WellDenotedV V ρ annotation := by
  obtain ⟨annotation, reading, graded, _⟩ := strong.internal.constType
    (φ := levels) 0 name constant universes lookup termEntry arity
  have wf := strong.internal.base2.wf constant (Kernel.Semantics.Env.find?_mem lookup)
  have noFree : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact wf.1
  have bounded : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact wf.2.2.2.1
  have closed : ∀ k : Nat, annotation.liftN 1 k = annotation := fun k =>
    denoteMeta_closed strong.internal.base2.acval_erase strong.internal.base2.cval_closed
      noFree bounded reading 1 k
  exact ⟨annotation, reading,
    denoteMeta_depth_of_closed strong.internal.base2.acval_closed noFree closed reading depth, graded⟩

open Kernel.Semantics Kernel.Model in
/-- Actual installed-member application: initial annotation/grading and
well-formedness are derived; public argument domains and their checked
scoped readings supply the exact internal telescope and residual. -/
theorem AnnotatedApplication.installed_fit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (constant : Kernel.ConstantInfo)
    (lookup : env.find? name = some constant) (termEntry : constant.isTowerEntry = false)
    (universes : List Kernel.Level) (arity : universes.length = constant.toConstantVal.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
      expressions annotations residual) :
    ∃ typeAnnotation residualAnnotation,
      denoteMeta strong.internal.base2.acval env levels 0
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes) =
          some typeAnnotation ∧
      TeleFitPA V ρ typeAnnotation annotations residualAnnotation ∧
      denoteMeta strong.internal.base2.acval env levels depth residual = some residualAnnotation ∧
      Kernel.piResidual
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
        expressions = some residual ∧
      Kernel.Denotes strong.public.cval env levels ρ (residual.closeN depth)
        (interp V ρ residualAnnotation) := by
  obtain ⟨typeAnnotation, reading0, reading, graded⟩ :=
    strong.instantiated_type levels depth name constant lookup termEntry universes arity
  have wf := strong.internal.base2.wf constant (Kernel.Semantics.Env.find?_mem lookup)
  have noFree : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact wf.1
  have bounded : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact wf.2.2.2.1
  obtain ⟨result, shape, fit, resultRead, denoted⟩ := application.denotes_residual reading
    (Kernel.Expr.WScoped.of_not_hasFvar noFree) bounded (graded ρ)
  exact ⟨typeAnnotation, result, reading0, fit, resultRead, shape, denoted⟩

open Kernel.Semantics Kernel.Model in
/-- The actual application residual has its scoped graded reading. This
supplies index-spine annotation evidence directly from the installed type
and typed application, without a per-index grading assumption. -/
theorem AnnotatedApplication.installed_residual {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (constant : Kernel.ConstantInfo)
    (lookup : env.find? name = some constant) (termEntry : constant.isTowerEntry = false)
    (universes : List Kernel.Level) (arity : universes.length = constant.toConstantVal.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
      expressions annotations residual) :
    ∃ annotation, ArgumentAnnotation strong levels depth ρ residual annotation := by
  obtain ⟨typeAnnotation, _, reading, graded⟩ :=
    strong.instantiated_type levels depth name constant lookup termEntry universes arity
  have wf := strong.internal.base2.wf constant (Kernel.Semantics.Env.find?_mem lookup)
  have noFree : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact wf.1
  have bounded : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact wf.2.2.2.1
  have scope := Kernel.Expr.WScoped.of_not_hasFvar (d := depth) noFree
  obtain ⟨annotation, _, annotationRead, annotationGrade⟩ := application.internal_fit reading scope bounded (graded ρ)
  obtain ⟨residualScope, residualBounded⟩ := application.residual_scope scope bounded
  exact ⟨annotation, ⟨annotationRead, residualScope, residualBounded, annotationGrade⟩⟩

open Kernel.Semantics Kernel.Model in
/-- The whole applied installed constant has its actual scoped annotation
and grading. For a constructor this supplies the recursor's exact major
argument, rather than a fresh variable merely assigned an equal value. -/
theorem AnnotatedApplication.applied_argument {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (constant : Kernel.ConstantInfo)
    (lookup : env.find? name = some constant) (termEntry : constant.isTowerEntry = false)
    (universes : List Kernel.Level) (arity : universes.length = constant.toConstantVal.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
      expressions annotations residual) :
    ArgumentAnnotation strong levels depth ρ (Kernel.Expr.mkAppN (.const name universes) expressions)
      (AnnotTerm.mkAppN (strong.internal.base2.acval name
        (Kernel.Level.substFn levels constant.toConstantVal.levelParams universes)) annotations) := by
  obtain ⟨typeAnnotation, result, typeRead, fit, _⟩ :=
    application.installed_fit name constant lookup termEntry universes arity
  obtain ⟨actualType, actualRead, typeGraded, member⟩ :=
    strong.internal.constType 0 name constant universes lookup termEntry arity
  have equal := Option.some.inj (actualRead.symm.trans typeRead)
  subst actualType
  obtain ⟨spine, frames, grades⟩ := application.argument_annotations.facts
  constructor
  · exact denoteMeta_mkAppN spine (by simp [denoteMeta, lookup, arity])
  · exact Kernel.Expr.WScoped.mkAppN (by simp [Kernel.Expr.WScoped])
      (fun expression present => (frames expression present).1)
  · exact Kernel.looseBVarsBounded_mkAppN rfl
      (fun expression present => (frames expression present).2)
  · exact (Kernel.Model.Rules.mkAppN_of_fitA annotations (typeGraded ρ)
      ⟨strong.internal.base2.acval_wellDenoted _ _ ρ, strong.internal.acval_validV _ _ ρ⟩
      grades (member ρ) fit).1

open Kernel.Semantics Kernel.Model in
/-- Derive the strong invariant's exact telescope fit for arbitrary public
values at an actual installed universe instance. Closedness, type reading,
grading and the symbolic argument readings are all derived. The metadata
scope premise is not a claim of successful inference on a generated context. -/
theorem StrongInstalledModel.arbitrary_installed_fit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (name : Kernel.Name) (constant : Kernel.ConstantInfo)
    (lookup : env.find? name = some constant) (termEntry : constant.isTowerEntry = false)
    (universes : List Kernel.Level) (arity : universes.length = constant.toConstantVal.levelParams.length)
    {ρ finalρ : Nat → V} {arguments : List V} {result : Kernel.Expr}
    (typed : InstalledTelescope strong.public.cval env levels ρ
      (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
      arguments finalρ result)
    (metadata : Nat → Kernel.Expr)
    (scope : ∀ index, index < arguments.length → Kernel.Expr.WScoped index (metadata index)) :
    ∃ residual typeAnnotation residualAnnotation,
      AnnotatedApplication strong levels arguments.length (pushArguments ρ arguments)
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
        (argumentFVars arguments.length metadata) (argumentReadings arguments.length) residual ∧
      denoteMeta strong.internal.base2.acval env levels 0
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes) =
          some typeAnnotation ∧
      TeleFitPA V (pushArguments ρ arguments) typeAnnotation
        (argumentReadings arguments.length) residualAnnotation ∧
      denoteMeta strong.internal.base2.acval env levels arguments.length residual = some residualAnnotation ∧
      Kernel.piResidual
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
        (argumentFVars arguments.length metadata) = some residual ∧
      Kernel.Denotes strong.public.cval env levels (pushArguments ρ arguments)
        (residual.closeN arguments.length) (interp V (pushArguments ρ arguments) residualAnnotation) := by
  have wf := strong.internal.base2.wf constant (Kernel.Semantics.Env.find?_mem lookup)
  have noFree : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact wf.1
  have bounded : (constant.toConstantVal.type.instantiateLevelParams
      constant.toConstantVal.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact wf.2.2.2.1
  obtain ⟨residual, application⟩ :=
    AnnotatedApplication.arbitrary_arguments typed bounded noFree metadata scope
  obtain ⟨typeAnnotation, residualAnnotation, proof⟩ :=
    application.installed_fit name constant lookup termEntry universes arity
  exact ⟨residual, typeAnnotation, residualAnnotation, application, proof⟩

open Kernel.Semantics Kernel.Model in
/-- The exact residual of an actually installed type is graded after any
publicly typed argument tuple. This derives, rather than assumes, the
grading premise needed at a checked theorem's Eq leaf. -/
theorem StrongInstalledModel.graded_telescope {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (constant : Kernel.ConstantInfo) (present : constant ∈ env.consts)
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {arguments : List V} {result : Kernel.Expr}
    (typed : InstalledTelescope strong.public.cval env levels ρ constant.toConstantVal.type
      arguments finalρ result) :
    GradedReading strong.internal.base2.acval env levels finalρ result :=
  typed.graded_reading strong.internal.base2.cval_closedL (strong.graded_type constant present levels ρ)

theorem AnnotatedApplication.length {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual) :
    expressions.length = annotations.length := by
  induction application with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

open Kernel Kernel.Semantics Kernel.Model in
/-- Caller-side data for a fired rule, with both telescope fits derived from
public typed applications. Comparison certificates remain explicit: nested
and indexed families must not inherit a plain unindexed shortcut. -/
structure FiredRecursorApplication {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (header : Kernel.ConstantVal) (major params : Nat) (rule : Kernel.RecRule)
    (universes : List Kernel.Level) where
  constructor : Kernel.ConstantVal
  constructorParams : Nat
  constructorFields : Nat
  constructorLookup : env.find? rule.ctor =
    some (.ctorInfo constructor constructorParams constructorFields)
  constructorUniverses : List Kernel.Level
  depth : Nat
  valuation : Nat → V
  argumentExpressions : List Kernel.Expr
  fieldExpressions : List Kernel.Expr
  arguments : List AnnotTerm
  fields : List AnnotTerm
  recursorResidual : Kernel.Expr
  constructorResidual : Kernel.Expr
  argumentCount : arguments.length = major
  fieldCount : fields.length = rule.ctorParams + rule.nfields
  constructorArity : constructorUniverses.length = constructor.levelParams.length
  universeSelection : Kernel.Level.substFn levels constructor.levelParams constructorUniverses =
    Kernel.Level.substFn levels constructor.levelParams
      (recFireComparands rule header.levelParams universes constructor.levelParams [] params).1
  plainParameters : rule.paramsBlind = false → rule.fire = .plain →
    ∀ i, i < rule.ctorParams → i < major →
      interp V valuation (fields.getD i default) = interp V valuation (arguments.getD i default)
  nestedParameters : ∀ lvls pins, rule.fire = .nested lvls pins →
    ∀ i, i < rule.ctorParams → ∀ pin : AnnotTerm,
      denoteMeta strong.internal.base2.acval env levels params
        (Kernel.Verify.openRev 0 params ((pins.getD i default).instantiateLevelParams
          header.levelParams universes)) = some pin →
      interp V valuation (fields.getD i default) =
        interp V valuation (Kernel.Model.AnnotTerm.instRevChain (arguments.take params) pin)
  recursorApplication : AnnotatedApplication strong levels depth valuation
    (header.type.instantiateLevelParams header.levelParams universes)
    (argumentExpressions ++ [Kernel.Expr.mkAppN (.const rule.ctor constructorUniverses) fieldExpressions])
    (arguments ++ [AnnotTerm.mkAppN (strong.internal.base2.acval rule.ctor
      (Kernel.Level.substFn levels constructor.levelParams constructorUniverses)) fields]) recursorResidual
  constructorApplication : AnnotatedApplication strong levels depth valuation
    (constructor.type.instantiateLevelParams constructor.levelParams constructorUniverses)
    fieldExpressions fields constructorResidual
  indexPin : ∀ result : AnnotTerm,
    denoteMeta strong.internal.base2.acval env levels depth constructorResidual = some result →
    IotaIndexPin valuation result rule.ctorParams major params arguments

open Kernel.Semantics Kernel.Model in
/-- Public fired-rule denotation with the two internal telescope fits
constructed, not supplied. The checked argument readings and comparison
certificates remain visible in `FiredRecursorApplication`. -/
theorem FiredRecursorApplication.denotes {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {header : Kernel.ConstantVal} {major params : Nat} {rule : Kernel.RecRule}
    {universes : List Kernel.Level}
    (application : FiredRecursorApplication strong levels header major params rule universes)
    (name : Kernel.Name) (rules : List Kernel.RecRule)
    (lookup : env.find? name = some (.recInfo header major params rules))
    (present : rule ∈ rules) (fires : rule.fire ≠ .inert)
    (arity : universes.length = header.levelParams.length) :
    ∃ value : V,
      Kernel.Denotes strong.public.cval env levels application.valuation
        (Kernel.Expr.mkAppN (.const name universes)
          (application.argumentExpressions.map (Kernel.Expr.closeN application.depth) ++
            [Kernel.Expr.mkAppN (.const rule.ctor application.constructorUniverses)
              (application.fieldExpressions.map (Kernel.Expr.closeN application.depth))])) value ∧
      Kernel.Denotes strong.public.cval env levels application.valuation
        (Kernel.Expr.mkAppN (rule.rhs.instantiateLevelParams header.levelParams universes)
          ((application.argumentExpressions.map (Kernel.Expr.closeN application.depth)).take params ++
            (application.fieldExpressions.map (Kernel.Expr.closeN application.depth)).drop rule.ctorParams)) value := by
  obtain ⟨recursorType, recursorResult, recursorRead, recursorFit, _, _, _⟩ :=
    application.recursorApplication.installed_fit name (.recInfo header major params rules)
      lookup rfl universes arity
  obtain ⟨constructorType, constructorResult, constructorRead, constructorFit, constructorResidualRead, _, _⟩ :=
    application.constructorApplication.installed_fit rule.ctor
      (.ctorInfo application.constructor application.constructorParams application.constructorFields)
      application.constructorLookup rfl application.constructorUniverses application.constructorArity
  let frame : FiredRecursorFrame strong levels header major params rule universes := {
    constructor := application.constructor
    constructorParams := application.constructorParams
    constructorFields := application.constructorFields
    constructorLookup := application.constructorLookup
    constructorUniverses := application.constructorUniverses
    valuation := application.valuation
    arguments := application.arguments
    fields := application.fields
    recursorType, constructorType, recursorResult, constructorResult
    argumentCount := application.argumentCount
    fieldCount := application.fieldCount
    constructorArity := application.constructorArity
    universeSelection := application.universeSelection
    plainParameters := application.plainParameters
    nestedParameters := application.nestedParameters
    indexPin := application.indexPin constructorResult constructorResidualRead
    recursorTypeRead := recursorRead
    constructorTypeRead := constructorRead
    recursorTyped := recursorFit
    constructorTyped := constructorFit }
  have count : application.argumentExpressions.length = application.arguments.length := by
    have length := application.recursorApplication.length
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_right_cancel_iff] using length
  have argumentRead := application.recursorApplication.denotes_arguments.take application.argumentExpressions.length
  simp only [List.map_append, List.map_cons, List.map_nil] at argumentRead
  have expressionTake := List.take_left
    (l₁ := application.argumentExpressions.map (Kernel.Expr.closeN application.depth))
    (l₂ := [(Kernel.Expr.mkAppN (.const rule.ctor application.constructorUniverses)
      application.fieldExpressions).closeN application.depth])
  have annotationTake := List.take_left
    (l₁ := application.arguments.map (interp V application.valuation))
    (l₂ := [interp V application.valuation (AnnotTerm.mkAppN (strong.internal.base2.acval rule.ctor
      (Kernel.Level.substFn levels application.constructor.levelParams application.constructorUniverses)) application.fields)])
  simp only [List.length_map] at expressionTake annotationTake
  rw [expressionTake, count, annotationTake] at argumentRead
  exact strong.recursor_denotes levels name header major params rules lookup rule present fires universes arity
    frame _ _ argumentRead application.constructorApplication.denotes_arguments

open Kernel Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Public typed inputs to a fired rule. Both telescope premises contain only
semantic argument values. Actual scoped readings and the original comparison
conditions remain explicit; no internal `TeleFitPA` is supplied by the caller. -/
structure PublicRecursorApplication {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env}
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    (header : Kernel.ConstantVal) (major params : Nat) (rule : Kernel.RecRule)
    (universes : List Kernel.Level) where
  constructor : Kernel.ConstantVal
  constructorParams : Nat
  constructorFields : Nat
  constructorLookup : env.find? rule.ctor = some (.ctorInfo constructor constructorParams constructorFields)
  constructorUniverses : List Kernel.Level
  constructorArity : constructorUniverses.length = constructor.levelParams.length
  depth : Nat
  valuation : Nat → V
  argumentExpressions : List Kernel.Expr
  fieldExpressions : List Kernel.Expr
  arguments : List AnnotTerm
  fields : List AnnotTerm
  argumentReadings : ArgumentAnnotations strong levels depth valuation argumentExpressions arguments
  fieldReadings : ArgumentAnnotations strong levels depth valuation fieldExpressions fields
  argumentCount : arguments.length = major
  fieldCount : fields.length = rule.ctorParams + rule.nfields
  universeSelection : Level.substFn levels constructor.levelParams constructorUniverses =
    Level.substFn levels constructor.levelParams
      (recFireComparands rule header.levelParams universes constructor.levelParams [] params).1
  plainParameters : rule.paramsBlind = false → rule.fire = .plain →
    ∀ i, i < rule.ctorParams → i < major →
      interp V valuation (fields.getD i default) = interp V valuation (arguments.getD i default)
  nestedParameters : ∀ lvls pins, rule.fire = .nested lvls pins →
    ∀ i, i < rule.ctorParams → ∀ pin : AnnotTerm,
      denoteMeta strong.internal.base2.acval env levels params
        (Kernel.Verify.openRev 0 params ((pins.getD i default).instantiateLevelParams
          header.levelParams universes)) = some pin →
      interp V valuation (fields.getD i default) =
        interp V valuation (Kernel.Model.AnnotTerm.instRevChain (arguments.take params) pin)
  constructorTyped : ∃ final result,
    InstalledTelescope strong.public.cval env levels valuation
      (constructor.type.instantiateLevelParams constructor.levelParams constructorUniverses)
      (fields.map (interp V valuation)) final result
  recursorTyped : ∃ final result,
    InstalledTelescope strong.public.cval env levels valuation
      (header.type.instantiateLevelParams header.levelParams universes)
      (arguments.map (interp V valuation) ++
        [(fields.map (interp V valuation)).foldl app (strong.public.cval rule.ctor
          (Level.substFn levels constructor.levelParams constructorUniverses))]) final result
  indexPin : ∀ residual result,
    Kernel.piResidual (constructor.type.instantiateLevelParams constructor.levelParams constructorUniverses)
      fieldExpressions = some residual →
    denoteMeta strong.internal.base2.acval env levels depth residual = some result →
    IotaIndexPin valuation result rule.ctorParams major params arguments

open Kernel.Semantics Kernel.Model in
/-- Assemble the exact fired recursor from public typed tuples. Constructor
application annotation/grading and both internal telescope fits are derived
inside the same strong model. The rule's index/nested comparison premises are
retained verbatim, rather than inferred from tuple lengths or fixture success. -/
theorem PublicRecursorApplication.denotes {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {header : Kernel.ConstantVal} {major params : Nat} {rule : Kernel.RecRule}
    {universes : List Kernel.Level}
    (application : PublicRecursorApplication strong levels header major params rule universes)
    (name : Kernel.Name) (rules : List Kernel.RecRule)
    (lookup : env.find? name = some (.recInfo header major params rules))
    (present : rule ∈ rules) (fires : rule.fire ≠ .inert)
    (arity : universes.length = header.levelParams.length) :
    ∃ value : V,
      Kernel.Denotes strong.public.cval env levels application.valuation
        (Kernel.Expr.mkAppN (.const name universes)
          (application.argumentExpressions.map (Kernel.Expr.closeN application.depth) ++
            [Kernel.Expr.mkAppN (.const rule.ctor application.constructorUniverses)
              (application.fieldExpressions.map (Kernel.Expr.closeN application.depth))])) value ∧
      Kernel.Denotes strong.public.cval env levels application.valuation
        (Kernel.Expr.mkAppN (rule.rhs.instantiateLevelParams header.levelParams universes)
          ((application.argumentExpressions.map (Kernel.Expr.closeN application.depth)).take params ++
            (application.fieldExpressions.map (Kernel.Expr.closeN application.depth)).drop rule.ctorParams)) value := by
  have constructorWf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem application.constructorLookup)
  have recursorWf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have constructorBounded : (application.constructor.type.instantiateLevelParams
      application.constructor.levelParams application.constructorUniverses).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact constructorWf.2.2.2.1
  have constructorClosed : (application.constructor.type.instantiateLevelParams
      application.constructor.levelParams application.constructorUniverses).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact constructorWf.1
  have recursorBounded : (header.type.instantiateLevelParams header.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact recursorWf.2.2.2.1
  have recursorClosed : (header.type.instantiateLevelParams header.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact recursorWf.1
  obtain ⟨_, _, constructorTyped⟩ := application.constructorTyped
  obtain ⟨constructorResidual, constructorApplication⟩ := AnnotatedApplication.represented_arguments
    constructorTyped constructorBounded constructorClosed application.fieldReadings rfl
  have majorReading := constructorApplication.applied_argument rule.ctor
    (.ctorInfo application.constructor application.constructorParams application.constructorFields)
    application.constructorLookup rfl application.constructorUniverses application.constructorArity
  have allReadings := application.argumentReadings.append (.cons majorReading .nil)
  obtain ⟨_, _, recursorTyped⟩ := application.recursorTyped
  have represented :
      (application.arguments ++ [AnnotTerm.mkAppN (strong.internal.base2.acval rule.ctor
        (Kernel.Level.substFn levels application.constructor.levelParams application.constructorUniverses))
        application.fields]).map (interp V application.valuation) =
      application.arguments.map (interp V application.valuation) ++
        [(application.fields.map (interp V application.valuation)).foldl Kernel.SetTheory.app
          (strong.public.cval rule.ctor
            (Kernel.Level.substFn levels application.constructor.levelParams application.constructorUniverses))] := by
    simp only [List.map_append, List.map_cons, List.map_nil, interp_mkAppN, List.foldl_map,
      interp_cvalOf strong.internal.base2.cval_closedL, StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM]
  obtain ⟨recursorResidual, recursorApplication⟩ := AnnotatedApplication.represented_arguments
    recursorTyped recursorBounded recursorClosed allReadings represented
  let prepared : FiredRecursorApplication strong levels header major params rule universes := {
    constructor := application.constructor
    constructorParams := application.constructorParams
    constructorFields := application.constructorFields
    constructorLookup := application.constructorLookup
    constructorUniverses := application.constructorUniverses
    depth := application.depth
    valuation := application.valuation
    argumentExpressions := application.argumentExpressions
    fieldExpressions := application.fieldExpressions
    arguments := application.arguments
    fields := application.fields
    recursorResidual, constructorResidual
    argumentCount := application.argumentCount
    fieldCount := application.fieldCount
    constructorArity := application.constructorArity
    universeSelection := application.universeSelection
    plainParameters := application.plainParameters
    nestedParameters := application.nestedParameters
    recursorApplication, constructorApplication
    indexPin := fun result reading => application.indexPin constructorResidual result
      constructorApplication.residual_shape reading }
  exact prepared.denotes name rules lookup present fires arity

/-- Pull back the actual target fired equation through its component
images. The target application still carries its real typed telescopes,
annotation readings and constructor/index/nested-pin conditions; this lemma
does not replace any of them with rule-list equality or a length check. -/
theorem PublicRecursorApplication.pullback {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} {target : StrongInstalledModel V targetEnv}
    {targetLevels : Kernel.Name → Nat} {header : Kernel.ConstantVal}
    {major params : Nat} {rule : Kernel.RecRule} {universes : List Kernel.Level}
    (application : PublicRecursorApplication target targetLevels header major params rule universes)
    (name : Kernel.Name) (rules : List Kernel.RecRule)
    (lookup : targetEnv.find? name = some (.recInfo header major params rules))
    (present : rule ∈ rules) (fires : rule.fire ≠ .inert)
    (arity : universes.length = header.levelParams.length)
    (sourceValues : Kernel.Name → (Kernel.Name → Nat) → V)
    (sourceEnv : Kernel.Env) (sourceLevels : Kernel.Name → Nat)
    (sourceName sourceConstructor : Kernel.Name) (sourceUs sourceConstructorUs : List Kernel.Level)
    (sourceRhs : Kernel.Expr) (sourceArguments sourceFields : List Kernel.Expr)
    (recursorImage : InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (.const sourceName sourceUs) (.const name universes))
    (constructorImage : InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (.const sourceConstructor sourceConstructorUs) (.const rule.ctor application.constructorUniverses))
    (rhsImage : InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceRhs (rule.rhs.instantiateLevelParams header.levelParams universes))
    (argumentImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceArguments (application.argumentExpressions.map (Kernel.Expr.closeN application.depth)))
    (fieldImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceFields (application.fieldExpressions.map (Kernel.Expr.closeN application.depth))) :
    ∃ value : V,
      Kernel.Denotes sourceValues sourceEnv sourceLevels application.valuation
        (Kernel.Expr.mkAppN (.const sourceName sourceUs)
          (sourceArguments ++ [Kernel.Expr.mkAppN (.const sourceConstructor sourceConstructorUs) sourceFields])) value ∧
      Kernel.Denotes sourceValues sourceEnv sourceLevels application.valuation
        (Kernel.Expr.mkAppN sourceRhs (sourceArguments.take params ++ sourceFields.drop rule.ctorParams)) value := by
  have appliedImage := (argumentImages.append (.cons (fieldImages.mkAppN constructorImage) .nil)).mkAppN recursorImage
  have resultImage := ((argumentImages.take params).append (fieldImages.drop rule.ctorParams)).mkAppN rhsImage
  obtain ⟨value, left, right⟩ := application.denotes name rules lookup present fires arity
  exact ⟨value, appliedImage.symm.denotes left, resultImage.symm.denotes right⟩

private theorem closeN_app_inv {opened function argument : Kernel.Expr} {depth : Nat}
    (image : opened.closeN depth = .app function argument) :
    ∃ rawFunction rawArgument, opened = .app rawFunction rawArgument ∧
      rawFunction.closeN depth = function ∧ rawArgument.closeN depth = argument := by
  cases opened <;> simp only [Kernel.Expr.closeN, Kernel.Expr.app.injEq, reduceCtorEq] at image
  case app rawFunction rawArgument => exact ⟨rawFunction, rawArgument, rfl, image⟩

/-- Recover the actual open spine from its closed expression image. This
is purely structural and does not substitute normalization for alignment. -/
theorem closeN_spine_inv {opened head : Kernel.Expr} {expressions : List Kernel.Expr} {depth : Nat}
    (image : opened.closeN depth = Kernel.Expr.mkAppN head expressions) :
    ∃ rawHead rawExpressions, opened = Kernel.Expr.mkAppN rawHead rawExpressions ∧
      rawHead.closeN depth = head ∧ rawExpressions.map (Kernel.Expr.closeN depth) = expressions := by
  induction expressions generalizing opened head with
  | nil => exact ⟨opened, [], rfl, image, rfl⟩
  | cons expression expressions ih =>
    obtain ⟨rawApp, rawExpressions, shape, headImage, images⟩ := ih image
    obtain ⟨rawHead, rawArgument, appShape, headClosed, argumentClosed⟩ := closeN_app_inv headImage
    exact ⟨rawHead, rawArgument :: rawExpressions, by simpa only [appShape, Kernel.Expr.mkAppN] using shape,
      headClosed, by simp only [List.map_cons, argumentClosed, images]⟩

open Kernel.Semantics Kernel.Model in
/-- The target residual's actual index spine is derived from the complete
residual image. No separately asserted target application shape or per-index
annotation is needed. Semantic source index equality remains explicit. -/
theorem ArgumentAnnotation.index_pin_of_residual_image {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} {target : StrongInstalledModel V targetEnv}
    {targetLevels : Kernel.Name → Nat} {depth : Nat} {ρ : Nat → V}
    {residual : Kernel.Expr} {annotation : AnnotTerm} {targetArguments : List Kernel.Expr}
    {arguments : List AnnotTerm}
    (evidence : ArgumentAnnotation target targetLevels depth ρ residual annotation)
    (argumentReadings : ArgumentAnnotations target targetLevels depth ρ targetArguments arguments)
    {sourceValues : Kernel.Name → (Kernel.Name → Nat) → V} {sourceEnv : Kernel.Env}
    {sourceLevels : Kernel.Name → Nat} {sourceHead : Kernel.Expr} {sourceIndices sourceArguments : List Kernel.Expr}
    {indexValues argumentValues : List V}
    (residualImage : InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (Kernel.Expr.mkAppN sourceHead sourceIndices) (residual.closeN depth))
    (indexRead : DenotesSpine sourceValues sourceEnv sourceLevels ρ sourceIndices indexValues)
    (argumentRead : DenotesSpine sourceValues sourceEnv sourceLevels ρ sourceArguments argumentValues)
    (argumentImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceArguments (targetArguments.map (Kernel.Expr.closeN depth)))
    (constructorParams major rulePrefix : Nat)
    (argumentCount : arguments.length = major) (ordered : rulePrefix ≤ major)
    (sourceEquation : indexValues.drop constructorParams = argumentValues.drop rulePrefix) :
    IotaIndexPin ρ annotation constructorParams major rulePrefix arguments := by
  obtain ⟨targetHead, targetIndices, closedShape, _, indexImages⟩ := residualImage.spine_inv
  obtain ⟨rawHead, rawIndices, rawShape, _, indicesClosed⟩ := closeN_spine_inv closedShape
  rw [rawShape] at evidence
  apply evidence.index_pin_image argumentReadings indexRead argumentRead _ argumentImages
    constructorParams major rulePrefix argumentCount ordered sourceEquation
  simpa only [indicesClosed] using indexImages

private theorem closeN_const_inv {opened : Kernel.Expr} {depth : Nat}
    {name : Kernel.Name} {levels : List Kernel.Level}
    (image : opened.closeN depth = .const name levels) : opened = .const name levels := by
  cases opened <;> simp_all only [Kernel.Expr.closeN, Kernel.Expr.const.injEq, reduceCtorEq]

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Public equality from the exact graded installed Eq expression. All Eq
typing premises are recovered from that grading in the same strong model. -/
theorem StrongInstalledModel.graded_public_eq_sound {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {levels : Kernel.Name → Nat} {ρ : Nat → V} {level : Kernel.Level}
    {carrier left right : Kernel.Expr} {type proof leftValue rightValue : V}
    (gradedRead : GradedReading strong.internal.base2.acval env levels ρ
      (.app (.app (.app (.const Kernel.eqName [level]) carrier) left) right))
    (read : Kernel.Denotes strong.public.cval env levels ρ
      (.app (.app (.app (.const Kernel.eqName [level]) carrier) left) right) type)
    (member : proof ∈ˢ type)
    (leftRead : Kernel.Denotes strong.public.cval env levels ρ left leftValue)
    (rightRead : Kernel.Denotes strong.public.cval env levels ρ right rightValue) :
    leftValue = rightValue := by
  obtain ⟨_, headRead⟩ := denotes_mkAppN_head [carrier, left, right]
    (function := .const Kernel.eqName [level]) read
  have ⟨constant, lookup, arity⟩ : ∃ constant,
      env.find? Kernel.eqName = some constant ∧
      [level].length = constant.toConstantVal.levelParams.length := by
    cases headRead with
    | const lookup arity => exact ⟨_, lookup, arity⟩
  have pinned := (strong.internal.base2.basis_pinned _ _ lookup (by decide)).1
  change constant = Kernel.eqA at pinned
  subst constant
  obtain ⟨depth, opened, annotation, reading, scope, bounded, image, graded⟩ := gradedRead
  have publicRead := Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth opened reading
    scope bounded ρ graded
  rw [image] at publicRead
  have sameType := Kernel.Denotes_functional read publicRead
  rw [sameType] at member
  obtain ⟨rawFunction, rawRight, rfl, functionImage, rightImage⟩ := closeN_app_inv image
  obtain ⟨rawPrefix, rawLeft, rfl, prefixImage, leftImage⟩ := closeN_app_inv functionImage
  obtain ⟨rawHead, rawCarrier, rfl, headImage, carrierImage⟩ := closeN_app_inv prefixImage
  have headEq := closeN_const_inv headImage
  subst rawHead
  obtain ⟨functionAnnotation, rightAnnotation, functionRead, rightReading, rfl⟩ :=
    denoteMeta_app_inv reading
  obtain ⟨prefixAnnotation, leftAnnotation, prefixRead, leftReading, rfl⟩ :=
    denoteMeta_app_inv functionRead
  obtain ⟨headAnnotation, carrierAnnotation, headReading, _, rfl⟩ :=
    denoteMeta_app_inv prefixRead
  rw [denoteMeta_const lookup arity] at headReading
  obtain rfl := (Option.some.inj headReading).symm
  have leftGrade := WellDenotedV_app_arg (WellDenotedV_app_fn graded)
  have rightGrade := WellDenotedV_app_arg graded
  have bounds := bounded
  simp only [Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at bounds
  have leftBound : rawLeft.looseBVarsBounded 0 = true := bounds.1.2
  have rightBound : rawRight.looseBVarsBounded 0 = true := bounds.2
  have publicLeft := Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth rawLeft
    leftReading scope.1.2 leftBound ρ leftGrade
  have publicRight := Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth rawRight
    rightReading scope.2 rightBound ρ rightGrade
  rw [leftImage] at publicLeft
  rw [rightImage] at publicRight
  have leftEq := Kernel.Denotes_functional leftRead publicLeft
  have rightEq := Kernel.Denotes_functional rightRead publicRight
  exact leftEq.trans ((strong.graded_eq_sound lookup _ ρ carrierAnnotation leftAnnotation
    rightAnnotation graded member).trans rightEq.symm)

open Kernel.SetTheory in
/-- A checked installed theorem, specialized at an actually typed tuple to
an exact Eq expression, proves equality of its public endpoint values.
The source of grading is the installed theorem, not an extra hypothesis. -/
theorem StrongInstalledModel.theorem_eq {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (header : Kernel.ConstantVal) (value : Kernel.Expr)
    (present : Kernel.ConstantInfo.thmInfo header value ∈ env.consts)
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V} {arguments : List V}
    {level : Kernel.Level} {carrier left right : Kernel.Expr} {leftValue rightValue : V}
    (typed : InstalledTelescope strong.public.cval env levels ρ header.type arguments finalρ
      (.app (.app (.app (.const Kernel.eqName [level]) carrier) left) right))
    (leftRead : Kernel.Denotes strong.public.cval env levels finalρ left leftValue)
    (rightRead : Kernel.Denotes strong.public.cval env levels finalρ right rightValue) :
    leftValue = rightValue := by
  have graded := strong.graded_telescope (.thmInfo header value) present typed
  obtain ⟨type, read, member⟩ := typed.model_apply strong.public present
  exact strong.graded_public_eq_sound graded read member leftRead rightRead

end Ix.CompileCert
