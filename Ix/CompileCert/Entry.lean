import Ix.CompileCert.Domain
import Ix.Kernel.Admission.Theorems
import Ix.Kernel.Verify.Cached.PushChain
import Ix.Kernel.Verify.Cached.BridgeCS4
import Ix.Kernel.Model.IndUnitLaw
import Ix.Kernel.Model.IOLicense
import Ix.Kernel.Model.Rules.RedSoundKit

/-! # Admission-connected direct-cone certification

The executable reads and admits the exact bytes before comparing an
independent source export against the reader stream. Its result carries
proofs of the checks actually performed. No producer-supplied proposition,
Boolean verdict, or `Named.original` field is accepted as correspondence.

This is a conservative foundation of C1, not completed W. Singleton definitions
may use the proved raw reader-normalization relation; its semantic pull-back
and complete source/export refinement remain separate obligations.
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

namespace AnnotationTrace

open Kernel Kernel.Cached

/-- The exact pure trace of an actual cached annotation, including memo
hits. The fuel belongs to the proved specification trace; it is not asserted
equal to the cached knot's fuel or to another installation's fuel. -/
theorem cached_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {expression result : Kernel.Expr} {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth expression)
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth expression initial = .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      ∃ pureFuel, annotateCore mode env pureFuel depth expression = .ok result := by
  obtain ⟨state', pureResult, ⟨same, resultScope⟩, pureFuel, pureRun⟩ :=
    (ssimC verified env environment fuel).annotate state rfl scope result final run
  cases same
  exact ⟨state', resultScope, pureFuel, pureRun⟩

theorem constant_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {name : Kernel.Name} {levels : List Kernel.Level} {result : Kernel.Expr}
    (run : annotateCore mode env fuel depth (.const name levels) = .ok result) :
    result = .const name levels := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel =>
    rw [annotateCore_succ] at run
    simpa only [annotateBody, pure, Except.pure, Except.ok.injEq] using run.symm

/-- Actual constant annotation keeps the exact name/levels on a cache hit
as well as a miss. This is a syntax statement, not proof that the constant
resolves or that two models assign its instance the same value. -/
theorem constant_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {name : Kernel.Name} {levels : List Kernel.Level} {result : Kernel.Expr}
    {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial)
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (.const name levels) initial =
      .ok (result, final)) : result = .const name levels := by
  obtain ⟨_, _, _, pureRun⟩ := cached_pure verified environment state
    (Kernel.Expr.WScoped.of_not_hasFvar rfl) run
  exact constant_pure pureRun

/-- Two independently successful constant annotations retain the supplied
name/universe image without equating the installations or their cache states. -/
theorem paired_constant_cached {sourceMode targetMode : CheckMode}
    {sourceEnv targetEnv : Env} {sourceFuel targetFuel depth : Nat}
    {sourceInitial sourceFinal targetInitial targetFinal : CState}
    {name : Kernel.Name} {levels : List Kernel.Level} {sourceResult targetResult : Kernel.Expr}
    (rename : InstalledRenaming)
    (sourceVerified : sourceMode.verifiedChecks = true) (targetVerified : targetMode.verifiedChecks = true)
    (sourceEnvironment : EnvWF sourceEnv) (targetEnvironment : EnvWF targetEnv)
    (sourceState : CSOK sourceMode sourceEnv sourceInitial) (targetState : CSOK targetMode targetEnv targetInitial)
    (sourceRun : (coreKnotI sourceMode (mkFEnv sourceEnv) sourceFuel).annotate depth (.const name levels)
      sourceInitial = .ok (sourceResult, sourceFinal))
    (targetRun : (coreKnotI targetMode (mkFEnv targetEnv) targetFuel).annotate depth
      (.const (rename.name name) (rename.universes name levels)) targetInitial = .ok (targetResult, targetFinal)) :
    targetResult = rename.expr sourceResult := by
  rw [constant_cached sourceVerified sourceEnvironment sourceState sourceRun,
    constant_cached targetVerified targetEnvironment targetState targetRun]
  rfl

/-- The pure specification's actual application subtraces. This does not
claim that a cached hit reruns either subexpression. -/
def ApplicationAnnotation (mode : CheckMode) (env : Env) (depth : Nat)
    (function argument result : Kernel.Expr) : Prop :=
  ∃ fuel, ∃ annotatedFunction annotatedArgument,
    annotateCore mode env fuel depth function = .ok annotatedFunction ∧
    annotateCore mode env fuel depth argument = .ok annotatedArgument ∧
    result = .app annotatedFunction annotatedArgument

theorem application_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {function argument result : Kernel.Expr}
    (run : annotateCore mode env fuel depth (.app function argument) = .ok result) :
    ApplicationAnnotation mode env depth function argument result := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel =>
    obtain ⟨annotatedFunction, annotatedArgument, functionRun, argumentRun, shape⟩ := annotateCore_app_inv run
    exact ⟨fuel, annotatedFunction, annotatedArgument, functionRun, argumentRun, shape⟩

theorem application_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {function argument result : Kernel.Expr} {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth (.app function argument))
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (.app function argument) initial =
      .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      ApplicationAnnotation mode env depth function argument result := by
  obtain ⟨state', resultScope, _, pureRun⟩ := cached_pure verified environment state scope run
  exact ⟨state', resultScope, application_pure pureRun⟩

inductive AnnotationBinder where
  | lam | pi

def AnnotationBinder.expr : AnnotationBinder → Kernel.Expr → Kernel.Expr → BinderMeta → Kernel.Expr
  | .lam => .lam
  | .pi => .forallE

def AnnotationBinder.write (kind : AnnotationBinder) (mode : CheckMode) (env : Env)
    (fuel depth : Nat) (body : Kernel.Expr) : CheckM PropWhen :=
  match kind with
  | .lam => annotPwLam (pureFns mode env fuel) env depth body
  | .pi => annotPwPi (pureFns mode env fuel) env depth body

/-- Actual binder annotation data, including the write/reuse branch for
its PropWhen datum. The datum's semantic validity and cross-installation
regime agreement are not conclusions of this annotation-only receipt. -/
structure BinderAnnotationTrace (kind : AnnotationBinder) (mode : CheckMode) (env : Env)
    (depth : Nat) (type body : Kernel.Expr) (metadata : BinderMeta) (result : Kernel.Expr) where
  fuel : Nat
  annotatedType : Kernel.Expr
  annotatedBody : Kernel.Expr
  datum : PropWhen
  typeRun : annotateCore mode env fuel depth type = .ok annotatedType
  bodyRun : annotateCore mode env fuel (depth + 1)
    (body.instantiate1 (.fvar depth annotatedType)) = .ok annotatedBody
  datumRun :
    (pwWritten metadata.pw = false ∧
      kind.write mode env fuel (depth + 1) annotatedBody = .ok datum) ∨
    (pwWritten metadata.pw = true ∧ datum = metadata.pw)
  shape : result = kind.expr annotatedType (annotatedBody.abstract1 depth) ⟨datum⟩

private theorem annotate_binder_succ (kind : AnnotationBinder) (mode : CheckMode) (env : Env)
    (fuel depth : Nat) (type body : Kernel.Expr) (metadata : BinderMeta) :
    annotateCore mode env (fuel + 1) depth (kind.expr type body metadata) = (do
      let annotatedType ← annotateCore mode env fuel depth type
      let annotatedBody ← annotateCore mode env fuel (depth + 1)
        (body.instantiate1 (.fvar depth annotatedType))
      let datum ← if !pwWritten metadata.pw then
          kind.write mode env fuel (depth + 1) annotatedBody
        else pure metadata.pw
      pure (kind.expr annotatedType (annotatedBody.abstract1 depth) ⟨datum⟩)) := by
  cases kind <;> rw [annotateCore_succ] <;> rfl

theorem binder_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type body result : Kernel.Expr} {metadata : BinderMeta} (kind : AnnotationBinder)
    (run : annotateCore mode env fuel depth (kind.expr type body metadata) = .ok result) :
    Nonempty (BinderAnnotationTrace kind mode env depth type body metadata result) := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel =>
    rw [annotate_binder_succ] at run
    cases typeRun : annotateCore mode env fuel depth type with
    | error reason => simp [typeRun, bind, Except.bind] at run
    | ok annotatedType =>
      simp only [typeRun, bind, Except.bind] at run
      cases bodyRun : annotateCore mode env fuel (depth + 1)
          (body.instantiate1 (.fvar depth annotatedType)) with
      | error reason => simp [bodyRun] at run
      | ok annotatedBody =>
        simp only [bodyRun] at run
        cases written : pwWritten metadata.pw with
        | false =>
          simp only [written, Bool.not_false, ↓reduceIte] at run
          cases datumRun : kind.write mode env fuel (depth + 1) annotatedBody with
          | error reason => simp [datumRun] at run
          | ok datum =>
            simp only [datumRun, pure, Except.pure, Except.ok.injEq] at run
            exact ⟨⟨fuel, annotatedType, annotatedBody, datum, typeRun, bodyRun,
              .inl ⟨written, datumRun⟩, run.symm⟩⟩
        | true =>
          simp [written, pure, Except.pure] at run
          exact ⟨⟨fuel, annotatedType, annotatedBody, metadata.pw, typeRun, bodyRun,
            .inr ⟨written, rfl⟩, run.symm⟩⟩

theorem binder_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type body result : Kernel.Expr} {metadata : BinderMeta} {initial final : CState}
    (kind : AnnotationBinder)
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth (kind.expr type body metadata))
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (kind.expr type body metadata) initial =
      .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      Nonempty (BinderAnnotationTrace kind mode env depth type body metadata result) := by
  obtain ⟨state', resultScope, _, pureRun⟩ := cached_pure verified environment state scope run
  exact ⟨state', resultScope, binder_pure kind pureRun⟩

/-- Reassembly uses the actual annotated domain, opened body and datum on
each side. In particular the datum correspondence remains an explicit
obligation; raw source normalization cannot supply it. -/
theorem BinderAnnotationTrace.paired_image {kind : AnnotationBinder}
    {sourceMode targetMode : CheckMode} {sourceEnv targetEnv : Env} {depth : Nat}
    {sourceType sourceBody sourceResult targetType targetBody targetResult : Kernel.Expr}
    {sourceMetadata targetMetadata : BinderMeta}
    (source : BinderAnnotationTrace kind sourceMode sourceEnv depth sourceType sourceBody sourceMetadata sourceResult)
    (target : BinderAnnotationTrace kind targetMode targetEnv depth targetType targetBody targetMetadata targetResult)
    (rename : InstalledRenaming)
    (domainImage : target.annotatedType = rename.expr source.annotatedType)
    (bodyImage : target.annotatedBody = rename.expr source.annotatedBody)
    (datumImage : (⟨target.datum⟩ : BinderMeta) = rename.binder ⟨source.datum⟩) :
    targetResult = rename.expr sourceResult := by
  rw [source.shape, target.shape, domainImage, bodyImage, datumImage, ← rename.abstract1]
  cases kind <;> rfl

/-- Semantic binder reassembly from the actual annotation receipts. The
domain/body premises are semantic images, not syntactic/canonical equality.
The exact selected-universe datum image supplies regime agreement; no such
agreement is inferred merely from both annotation runs succeeding. -/
theorem BinderAnnotationTrace.semantic_image {V : Type u} [Kernel.SetTheory V]
    {kind : AnnotationBinder} {sourceMode targetMode : CheckMode}
    {sourceEnv targetEnv : Env} {depth : Nat}
    {sourceType sourceBody sourceResult targetType targetBody targetResult : Kernel.Expr}
    {sourceMetadata targetMetadata : BinderMeta}
    (source : BinderAnnotationTrace kind sourceMode sourceEnv depth sourceType sourceBody sourceMetadata sourceResult)
    (target : BinderAnnotationTrace kind targetMode targetEnv depth targetType targetBody targetMetadata targetResult)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    (sourceValues targetValues : Kernel.Name → (Kernel.Name → Nat) → V)
    (domainImage : InstalledExprImage sourceValues targetValues sourceEnv targetEnv
      (image.valuation targetLevels) targetLevels source.annotatedType target.annotatedType)
    (bodyImage : InstalledExprImage sourceValues targetValues sourceEnv targetEnv
      (image.valuation targetLevels) targetLevels (source.annotatedBody.abstract1 depth)
      (target.annotatedBody.abstract1 depth))
    (datumImage : target.datum = image.datum source.datum) :
    InstalledExprImage sourceValues targetValues sourceEnv targetEnv
      (image.valuation targetLevels) targetLevels sourceResult targetResult := by
  have regimes : Kernel.regime (image.valuation targetLevels) source.datum =
      Kernel.regime targetLevels target.datum := by
    rw [datumImage]
    exact (image.regime targetLevels ⟨source.datum⟩).symm
  rw [source.shape, target.shape]
  cases kind with
  | lam => exact .lam domainImage bodyImage regimes
  | pi => exact .forallE domainImage bodyImage regimes

/-- The checked let-elimination trace, including all official let checks.
The reduct substitutes the immutable original value, not the independently
annotated value. The latter remains the subject of value-type checking. -/
def LetAnnotation (mode : CheckMode) (env : Env) (depth : Nat)
    (type value body result : Kernel.Expr) : Prop :=
  ∃ fuel, ∃ annotatedType annotatedValue : Kernel.Expr,
    annotateCore mode env fuel depth type = .ok annotatedType ∧
    annotateCore mode env fuel depth value = .ok annotatedValue ∧
    annotateCore mode env fuel depth (body.instantiate1 value) = .ok result ∧
    ∃ typeType sortLevel valueType,
      inferTypeCore mode env fuel depth annotatedType = .ok typeType ∧
      ensureSortCore mode env fuel depth typeType = .ok sortLevel ∧
      inferTypeCore mode env fuel depth annotatedValue = .ok valueType ∧
      isDefEqCore mode env fuel depth valueType annotatedType = .ok true

theorem let_pure {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type value body result : Kernel.Expr}
    (run : annotateCore mode env fuel depth (.letE type value body) = .ok result) :
    LetAnnotation mode env depth type value body result := by
  cases fuel with
  | zero => simp [annotateCore_zero, throw, throwThe] at run
  | succ fuel => exact ⟨fuel, annotateCore_letE_inv run⟩

/-- Actual cached-call attachment using the existing invariant-state
simulation. Prefix `EnvWF`/`CSOK` remain explicit; neither a cache hit nor a
successful target installation is used to invent a source-prefix invariant. -/
theorem let_cached {mode : CheckMode} {env : Env} {fuel depth : Nat}
    {type value body result : Kernel.Expr} {initial final : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env)
    (state : CSOK mode env initial) (scope : Kernel.Expr.WScoped depth (.letE type value body))
    (run : (coreKnotI mode (mkFEnv env) fuel).annotate depth (.letE type value body) initial =
      .ok (result, final)) :
    CSOK mode env final ∧ Kernel.Expr.WScoped depth result ∧
      LetAnnotation mode env depth type value body result := by
  obtain ⟨state', pureResult, ⟨same, resultScope⟩, pureFuel, pureRun⟩ :=
    (ssimC verified env environment fuel).annotate state rfl scope result final run
  cases same
  exact ⟨state', resultScope, let_pure pureRun⟩

/-- Both successful let annotations reach the exact related raw residuals.
Their fuels and checking/annotation traces remain independent. This records
the endpoint square needed by a recursive annotation simulation; it does not
assert that merely normalizing the source relates the final annotations. -/
theorem LetAnnotation.paired_residuals {sourceMode targetMode : CheckMode}
    {sourceEnv targetEnv : Env} {depth : Nat}
    {type value body sourceResult targetResult : Kernel.Expr}
    (rename : InstalledRenaming)
    (source : LetAnnotation sourceMode sourceEnv depth type value body sourceResult)
    (target : LetAnnotation targetMode targetEnv depth (rename.expr type) (rename.expr value)
      (rename.expr body) targetResult) :
    ∃ sourceFuel targetFuel,
      annotateCore sourceMode sourceEnv sourceFuel depth (body.instantiate1 value) = .ok sourceResult ∧
      annotateCore targetMode targetEnv targetFuel depth (rename.expr (body.instantiate1 value)) =
        .ok targetResult := by
  obtain ⟨sourceFuel, _, _, _, _, sourceRun, _⟩ := source
  obtain ⟨targetFuel, _, _, _, _, targetRun, _⟩ := target
  exact ⟨sourceFuel, targetFuel, sourceRun, (rename.instantiate1 body value 0).symm ▸ targetRun⟩

/-- Full header provenance for the actual cached annotation call. This is
not a claim that annotation preserves the raw expression's denotation. -/
theorem header_fields {mode : CheckMode} {fe : FEnv} {cv cvA : Kernel.ConstantVal}
    {jty : Kernel.Expr} {initial final : CState}
    (run : annotConstantValC mode fe cv initial = .ok ((cvA, jty), final)) :
    cvA = { cv with type := jty } ∧ ∃ afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 cv.type initial = .ok (jty, afterAnnotation) := by
  unfold annotConstantValC at run
  by_cases h1 : (fe.find? cv.name).isSome = true
  · rw [ite_eq_left h1] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h1] at run
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [ite_eq_left h2] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h2] at run
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [ite_eq_left h3] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h3] at run
  by_cases h4 : Kernel.Name.nodup cv.levelParams = true
  case neg => rw [ite_eq_right h4] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h4] at run
  by_cases h5 : Kernel.Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [ite_eq_right h5] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h5] at run
  by_cases h6 : Kernel.Expr.hasFvar cv.type = true
  · rw [ite_eq_left h6] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h6] at run
  obtain ⟨annotated, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases h7 : Kernel.Expr.allLevelParamsDefinedC cv.levelParams annotated = true
  case neg => rw [ite_eq_right h7] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h7] at run
  by_cases h8 : constsResolveFC fe annotated = true
  case neg => rw [ite_eq_right h8] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h8] at run
  obtain ⟨result, _⟩ := pureC_ok run
  have pair := Prod.mk.inj result
  obtain rfl := pair.2
  exact ⟨pair.1.symm, afterAnnotation, annotation⟩

theorem theorem_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (run : annotStepC mode pins index fe pending (.thmDecl header value) initial =
      .ok ((fe', pending'), final)) :
    ∃ annotated afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed =
        .ok (annotated, afterAnnotation) ∧
      fe'.env.consts = .thmInfo { header with type := annotated } value :: fe.env.consts := by
  unfold annotStepC at run
  simp only [] at run
  obtain ⟨_, afterFlush, flush, run⟩ := bindC_ok run
  rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
  have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
  subst flushed
  obtain ⟨pair, afterHeader, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, annotated⟩ := pair
  obtain ⟨rfl, afterAnnotation, annotation⟩ := header_fields headerRun
  obtain ⟨_, afterRecord, _, run⟩ := bindC_ok run
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
  exact ⟨annotated, afterAnnotation, annotation, rfl⟩

/-- Exact annotation call for the value half; the guards and cache record
are not confused with a raw-to-annotated semantic preservation theorem. -/
theorem value_fields {mode : CheckMode} {fe : FEnv} {header : Kernel.ConstantVal}
    {type value annotated : Kernel.Expr} {record : Bool} {initial final : CState}
    (run : annotValC mode fe header type value record initial = .ok (annotated, final)) :
    ∃ afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 value initial = .ok (annotated, afterAnnotation) := by
  unfold annotValC at run
  by_cases bounded : value.looseBVarsBounded 0 = true
  case neg => rw [ite_eq_right bounded] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left bounded] at run
  by_cases free : value.hasFvar = true
  · rw [ite_eq_left free] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right free] at run
  obtain ⟨image, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases levels : image.allLevelParamsDefinedC header.levelParams = true
  case neg => rw [ite_eq_right levels] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left levels] at run
  by_cases resolved : constsResolveFC fe image = true
  case neg => rw [ite_eq_right resolved] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left resolved] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨rfl, _⟩ := pureC_ok run
  exact ⟨afterAnnotation, annotation⟩

theorem prepared_value_fields {mode : CheckMode} {fe : FEnv}
    {header installedHeader : Kernel.ConstantVal} {value type annotated : Kernel.Expr}
    {record : Bool} {initial final : CState}
    (run : annotValueC mode fe header value record initial = .ok ((installedHeader, type, annotated), final)) :
    installedHeader = { header with type := type } ∧
    ∃ afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode fe header initial.flushed = .ok ((installedHeader, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) := by
  unfold annotValueC at run
  obtain ⟨_, afterFlush, flush, run⟩ := bindC_ok run
  rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
  have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
  subst flushed
  obtain ⟨pair, beforeValue, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, typeA⟩ := pair
  obtain ⟨image, _, valueRun, run⟩ := bindC_ok run
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ result
  obtain ⟨headerShape, afterType, typeRun⟩ := header_fields headerRun
  obtain ⟨afterValue, annotation⟩ := value_fields valueRun
  exact ⟨headerShape, afterType, beforeValue, afterValue, typeRun, headerRun, annotation⟩

/-- Primitive paths use the checking header routine, which performs inference
after annotation. Its final cache state must not be identified with the
ordinary install-only header routine's state. -/
theorem checked_header_fields {mode : CheckMode} {fe : FEnv}
    {header installedHeader : Kernel.ConstantVal} {type : Kernel.Expr} {initial final : CState}
    (run : checkConstantValC mode fe header initial = .ok ((installedHeader, type), final)) :
    installedHeader = { header with type := type } ∧ ∃ afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial = .ok (type, afterAnnotation) := by
  unfold checkConstantValC at run
  by_cases h1 : (fe.find? header.name).isSome = true
  · rw [ite_eq_left h1] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h1] at run
  by_cases h2 : reservedBasisNames.contains header.name = true
  · rw [ite_eq_left h2] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h2] at run
  by_cases h3 : header.name.isProjFnShape = true
  · rw [ite_eq_left h3] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h3] at run
  by_cases h4 : Kernel.Name.nodup header.levelParams = true
  case neg => rw [ite_eq_right h4] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h4] at run
  by_cases h5 : Kernel.Expr.looseBVarsBounded 0 header.type = true
  case neg => rw [ite_eq_right h5] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h5] at run
  by_cases h6 : Kernel.Expr.hasFvar header.type = true
  · rw [ite_eq_left h6] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right h6] at run
  obtain ⟨annotated, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases h7 : Kernel.Expr.allLevelParamsDefinedC header.levelParams annotated = true
  case neg => rw [ite_eq_right h7] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h7] at run
  by_cases h8 : constsResolveFC fe annotated = true
  case neg => rw [ite_eq_right h8] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left h8] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨result, _⟩ := pureC_ok run
  have pair := Prod.mk.inj result
  obtain rfl := pair.2
  exact ⟨pair.1.symm, afterAnnotation, annotation⟩

theorem checked_definition_fields {mode : CheckMode} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {type value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (run : checkDefnValC mode fe header type value hint initial = .ok (finalEnv, final)) :
    ∃ annotated afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 value initial = .ok (annotated, afterAnnotation) ∧
      finalEnv = fe.push (.defnInfo header annotated hint) := by
  unfold checkDefnValC at run
  by_cases bounded : value.looseBVarsBounded 0 = true
  case neg => rw [ite_eq_right bounded] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left bounded] at run
  by_cases free : value.hasFvar = true
  · rw [ite_eq_left free] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right free] at run
  obtain ⟨image, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases levels : image.allLevelParamsDefinedC header.levelParams = true
  case neg => rw [ite_eq_right levels] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left levels] at run
  by_cases resolved : constsResolveFC fe image = true
  case neg => rw [ite_eq_right resolved] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left resolved] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨equal, _, _, run⟩ := bindC_ok run
  cases equal with
  | false => exact absurd run throwC_bind_ok
  | true =>
    obtain ⟨result, _⟩ := pureC_ok run
    exact ⟨image, afterAnnotation, annotation, result.symm⟩

theorem checked_opaque_fields {mode : CheckMode} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {type value : Kernel.Expr} {initial final : CState}
    (run : checkOpaqueValC mode fe header type value initial = .ok (finalEnv, final)) :
    ∃ annotated afterAnnotation,
      (coreKnotI mode fe checkFuel).annotate 0 value initial = .ok (annotated, afterAnnotation) ∧
      finalEnv = fe.push (.axiomInfo header) := by
  unfold checkOpaqueValC at run
  by_cases bounded : value.looseBVarsBounded 0 = true
  case neg => rw [ite_eq_right bounded] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left bounded] at run
  by_cases free : value.hasFvar = true
  · rw [ite_eq_left free] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_right free] at run
  obtain ⟨image, afterAnnotation, annotation, run⟩ := bindC_ok run
  by_cases levels : image.allLevelParamsDefinedC header.levelParams = true
  case neg => rw [ite_eq_right levels] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left levels] at run
  by_cases resolved : constsResolveFC fe image = true
  case neg => rw [ite_eq_right resolved] at run; exact absurd run throwC_bind_ok
  rw [ite_eq_left resolved] at run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨_, _, _, run⟩ := bindC_ok run
  obtain ⟨equal, _, _, run⟩ := bindC_ok run
  cases equal with
  | false => exact absurd run throwC_bind_ok
  | true =>
    obtain ⟨result, _⟩ := pureC_ok run
    exact ⟨image, afterAnnotation, annotation, result.symm⟩

private theorem yields_result {α : Type} {action : CheckCM α} {initial final : CState}
    {result : α} {property : α → Prop}
    (run : action initial = .ok (result, final)) (guarantee : Yields action property) : property result :=
  guarantee initial result final run

theorem checked_definition_decl {mode : CheckMode} {pins : List NatOpPinSet} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (run : checkDeclC mode pins fe (.defnDecl header value hint) initial = .ok (finalEnv, final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial = .ok (type, afterType) ∧
      checkConstantValC mode fe header initial =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      finalEnv = fe.push (.defnInfo { header with type := type } annotated hint) := by
  unfold checkDeclC at run
  obtain ⟨pair, beforeValue, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type⟩ := pair
  obtain ⟨rfl, afterType, typeRun⟩ := checked_header_fields headerRun
  by_cases pinned : (natOpNames.contains header.name || natDivModNames.contains header.name) = true
  · simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, valueRun, run⟩ := bindC_ok run
    have unchanged : finalEnv = checkedEnv := yields_result (property := fun result => result = checkedEnv) run (by
      yields
      all_goals exact Yields.pure rfl)
    subst finalEnv
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_definition_fields valueRun
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩
  · simp only [pinned] at run
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_definition_fields run
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩

theorem checked_opaque_decl {mode : CheckMode} {pins : List NatOpPinSet} {fe finalEnv : FEnv}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (run : checkDeclC mode pins fe (.opaqueDecl header value) initial = .ok (finalEnv, final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial = .ok (type, afterType) ∧
      checkConstantValC mode fe header initial =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      finalEnv = fe.push (.axiomInfo { header with type := type }) := by
  unfold checkDeclC at run
  obtain ⟨pair, beforeValue, headerRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type⟩ := pair
  obtain ⟨rfl, afterType, typeRun⟩ := checked_header_fields headerRun
  by_cases pinned : reduceOpNames.contains header.name = true
  · simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, valueRun, run⟩ := bindC_ok run
    obtain ⟨_, _, _, run⟩ := bindC_ok run
    obtain ⟨rfl, _⟩ := pureC_ok run
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_opaque_fields valueRun
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩
  · simp only [pinned] at run
    obtain ⟨annotated, afterValue, annotation, result⟩ := checked_opaque_fields run
    exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, result⟩

/-- Ordinary definitions retain both actual annotation calls and their real
prefix/cache states. Nat-operation pin routes are separate, not silently
included in this branch's statement or excluded from the source domain. -/
def DefinitionInstalled (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (hint : Kernel.ReducibilityHint) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
    ∃ type annotated : Kernel.Expr,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      Kernel.ConstantInfo.defnInfo { header with type := type } annotated hint ∈ env.consts

theorem definition_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false)
    (run : annotStepC mode pins index fe pending (.defnDecl header value hint) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode fe header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      fe'.env.consts = .defnInfo { header with type := type } annotated hint :: fe.env.consts := by
  unfold annotStepC at run
  simp only [ordinary, Bool.false_eq_true, ↓reduceIte] at run
  obtain ⟨triple, _, valueRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type, annotated⟩ := triple
  obtain ⟨rfl, afterType, beforeValue, afterValue, typeRun, headerRun, annotation⟩ :=
    prepared_value_fields valueRun
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
  exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, rfl⟩

theorem definition_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint}
    (ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false)
    (present : Declaration.defnDecl header value hint ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    DefinitionInstalled mode header value hint finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, installed⟩ :=
        definition_step ordinary stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, afterType, beforeValue, afterValue, type, annotated,
        typeRun, headerRun, valueRun, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem definition_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false)
    (present : Declaration.defnDecl header value hint ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    DefinitionInstalled mode header value hint env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact definition_run ordinary (Array.mem_toList_iff.mpr present) run rfl

open Kernel.SetTheory in
theorem DefinitionInstalled.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalled mode header value hint env)
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
      ∃ type annotated : Kernel.Expr, ∃ semanticType : V,
        (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
        annotConstantValC mode before header initial.flushed =
          .ok (({ header with type := type }, type), beforeValue) ∧
        (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
        Kernel.Denotes strong.public.cval env levels ρ type semanticType ∧
        strong.public.cval header.name levels ∈ˢ semanticType ∧
        Kernel.Denotes strong.public.cval env levels ρ annotated (strong.public.cval header.name levels) := by
  obtain ⟨before, initial, afterType, beforeValue, afterValue, type, annotated,
    typeRun, headerRun, valueRun, present⟩ := receipt
  obtain ⟨semanticType, typeRead, member⟩ := strong.public.mem _ present levels ρ
  exact ⟨before, initial, afterType, beforeValue, afterValue, type, annotated, semanticType,
    typeRun, headerRun, valueRun, typeRead, member,
    strong.definition_values _ _ _ present levels ρ⟩

/-- Opaque body annotation/checking is retained as provenance, while its
installed semantic entry is an axiom. No transparent value equation follows. -/
def OpaqueInstalled (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
    ∃ type annotated : Kernel.Expr,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      Kernel.ConstantInfo.axiomInfo { header with type := type } ∈ env.consts

theorem opaque_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (ordinary : reduceOpNames.contains header.name = false)
    (run : annotStepC mode pins index fe pending (.opaqueDecl header value) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated afterType beforeValue afterValue,
      (coreKnotI mode fe checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
      annotConstantValC mode fe header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∧
      (coreKnotI mode fe checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue) ∧
      fe'.env.consts = .axiomInfo { header with type := type } :: fe.env.consts := by
  unfold annotStepC at run
  simp only [ordinary, Bool.false_eq_true, ↓reduceIte] at run
  obtain ⟨triple, _, valueRun, run⟩ := bindC_ok run
  obtain ⟨headerA, type, annotated⟩ := triple
  obtain ⟨rfl, afterType, beforeValue, afterValue, typeRun, headerRun, annotation⟩ :=
    prepared_value_fields valueRun
  obtain ⟨result, _⟩ := pureC_ok run
  obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
  exact ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, annotation, rfl⟩

theorem opaque_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (ordinary : reduceOpNames.contains header.name = false)
    (present : Declaration.opaqueDecl header value ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    OpaqueInstalled mode header value finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, installed⟩ :=
        opaque_step ordinary stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, afterType, beforeValue, afterValue, type, annotated,
        typeRun, headerRun, valueRun, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem opaque_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (ordinary : reduceOpNames.contains header.name = false)
    (present : Declaration.opaqueDecl header value ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    OpaqueInstalled mode header value env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact opaque_run ordinary (Array.mem_toList_iff.mpr present) run rfl

/-- Both real header routes, with the branch's exact final state retained.
The disjunction distinguishes install-only annotation from primitive checking;
it does not assert their caches or operational behavior coincide. -/
def ValueAnnotationCalls (mode : CheckMode) (before : FEnv) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (initial : CState) (type annotated : Kernel.Expr) : Prop :=
  ∃ afterType beforeValue afterValue : CState,
    (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed = .ok (type, afterType) ∧
    (annotConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue) ∨
      checkConstantValC mode before header initial.flushed =
        .ok (({ header with type := type }, type), beforeValue)) ∧
    (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (annotated, afterValue)

/-- Let checking at the actual value-annotation state. Both the ordinary
header-annotation branch and the primitive header-check branch preserve the
required invariant; their states are not identified with each other. -/
theorem ValueAnnotationCalls.let_trace {mode : CheckMode} {env : Env}
    {header : Kernel.ConstantVal} {type value body annotatedType annotatedValue : Kernel.Expr}
    {initial : CState}
    (verified : mode.verifiedChecks = true) (environment : EnvWF env) (state : CSOKF initial)
    (scope : Kernel.Expr.WScoped 0 (.letE type value body))
    (calls : ValueAnnotationCalls mode (mkFEnv env) header (.letE type value body)
      initial annotatedType annotatedValue) :
    LetAnnotation mode env 0 type value body annotatedValue := by
  obtain ⟨afterType, beforeValue, afterValue, _, headerRun, valueRun⟩ := calls
  have valueState : CSOK mode env beforeValue := by
    rcases headerRun with install | check
    · exact (annotConstantValC_run verified environment (flushC_csok state) install).1
    · exact (checkConstantValC_sim verified environment (flushC_csok state) rfl
        _ beforeValue check).1
  exact (let_cached verified environment valueState scope valueRun).2.2

def DefinitionInstalledAll (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (hint : Kernel.ReducibilityHint) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.defnInfo { header with type := type } annotated hint ∈ env.consts

def OpaqueInstalledAll (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.axiomInfo { header with type := type } ∈ env.consts

theorem definition_all_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    {initial final : CState}
    (run : annotStepC mode pins index fe pending (.defnDecl header value hint) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated, ValueAnnotationCalls mode fe header value initial type annotated ∧
      fe'.env.consts = .defnInfo { header with type := type } annotated hint :: fe.env.consts := by
  by_cases ordinary : (natOpNames.contains header.name || natDivModNames.contains header.name) = false
  · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, stored⟩ :=
      definition_step ordinary run
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inl headerRun, valueRun⟩, stored⟩
  · have pinned : (natOpNames.contains header.name || natDivModNames.contains header.name) = true := by
      cases h : (natOpNames.contains header.name || natDivModNames.contains header.name) <;> simp_all
    unfold annotStepC at run
    simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, checkedRun, run⟩ := bindC_ok run
    obtain ⟨result, _⟩ := pureC_ok run
    obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
    unfold checkDeclStepC at checkedRun
    obtain ⟨_, afterFlush, flush, checkedRun⟩ := bindC_ok checkedRun
    rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
    have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
    subst flushed
    obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, rfl⟩ :=
      checked_definition_decl checkedRun
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inr headerRun, valueRun⟩, rfl⟩

theorem opaque_all_step {mode : CheckMode} {pins : List NatOpPinSet}
    {index : Nat} {fe fe' : FEnv} {pending pending' : Array PendingCheck}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {initial final : CState}
    (run : annotStepC mode pins index fe pending (.opaqueDecl header value) initial =
      .ok ((fe', pending'), final)) :
    ∃ type annotated, ValueAnnotationCalls mode fe header value initial type annotated ∧
      fe'.env.consts = .axiomInfo { header with type := type } :: fe.env.consts := by
  by_cases ordinary : reduceOpNames.contains header.name = false
  · obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, stored⟩ :=
      opaque_step ordinary run
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inl headerRun, valueRun⟩, stored⟩
  · have pinned : reduceOpNames.contains header.name = true := by
      cases h : reduceOpNames.contains header.name <;> simp_all
    unfold annotStepC at run
    simp only [pinned, ↓reduceIte] at run
    obtain ⟨checkedEnv, _, checkedRun, run⟩ := bindC_ok run
    obtain ⟨result, _⟩ := pureC_ok run
    obtain ⟨rfl, _⟩ := Prod.mk.injEq .. ▸ result
    unfold checkDeclStepC at checkedRun
    obtain ⟨_, afterFlush, flush, checkedRun⟩ := bindC_ok checkedRun
    rw [show (flushC : CheckCM Unit) initial = .ok ((), initial.flushed) from rfl] at flush
    have flushed : initial.flushed = afterFlush := congrArg Prod.snd (Except.ok.inj flush)
    subst flushed
    obtain ⟨type, annotated, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun, rfl⟩ :=
      checked_opaque_decl checkedRun
    exact ⟨type, annotated, ⟨afterType, beforeValue, afterValue, typeRun, .inr headerRun, valueRun⟩, rfl⟩

theorem definition_all_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    DefinitionInstalledAll mode header value hint finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, calls, installed⟩ := definition_all_step stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, type, annotated, calls, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

/-- Full definition provenance with the actual prefix's environment and
fresh-state invariants. These come from the accepting fold's model walk,
including its pending checks, rather than from the final target environment. -/
def DefinitionCheckedPrefix (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (hint : Kernel.ReducibilityHint) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    before = mkFEnv before.env ∧ EnvWF before.env ∧ CSOKF initial ∧
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.defnInfo { header with type := type } annotated hint ∈ env.consts

/-- The actual installation boundary of any declaration kind, including
mutual/inductive blocks. Both prefix states, canonical indices and the full
extension to the final environment are retained. This is operational
provenance; kind-specific annotation and semantic laws remain separate. -/
def CheckedDeclarationPrefix (mode : CheckMode) (pins : List NatOpPinSet)
    (declaration : Declaration) (env : Env) : Prop :=
  ∃ index, ∃ before : FEnv, ∃ pending : Array PendingCheck, ∃ initial : CState,
    ∃ next : FEnv, ∃ nextPending : Array PendingCheck, ∃ after : CState,
      before = mkFEnv before.env ∧ EnvWF before.env ∧ CSOKF initial ∧
      annotStepC mode pins index before pending declaration initial = .ok ((next, nextPending), after) ∧
      next = mkFEnv next.env ∧ EnvWF next.env ∧ CSOKF after ∧
      PushChain next.env (mkFEnv env)

theorem declaration_prefix_run {V : Type u} [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : List Declaration} {declaration : Declaration}
    (present : declaration ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env)
    (model : Kernel.Model.EnvModelOk V mode start.2.1.env) (state : CSOKF initial)
    (unique : NodupNames finish.2.1.env)
    (checked : ∀ pc ∈ finish.2.2.toList, ∃ after, checkPending mode finish.2.1 pc {} = .ok ((), after)) :
    CheckedDeclarationPrefix mode pins declaration finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons current rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 current
        initial (nextEnv, nextPending) afterStep stepRun).1
    obtain ⟨tailChain, newPending, pending⟩ :=
      installRun_trace mode restRun (PushChain.self chain.canon)
    obtain ⟨nextModel, nextState, _⟩ :=
      annotStepC_model verified canonical chain.canon model state stepRun tailChain pending unique checked
    rcases List.mem_cons.mp present with rfl | restPresent
    · have beforeWF : EnvWF start.2.1.env := by
        obtain ⟨witness⟩ := model.1
        exact witness.toEnvFacts.wf
      have nextWF : EnvWF nextEnv.env := by
        obtain ⟨witness⟩ := nextModel.1
        exact witness.toEnvFacts.wf
      refine ⟨start.1, start.2.1, start.2.2, initial, nextEnv, nextPending, afterStep,
        canonical, beforeWF, state, stepRun, chain.canon, nextWF, nextState, ?_⟩
      rw [← tailChain.canon]
      exact tailChain
    · exact ih restPresent chain.canon nextModel nextState unique checked

/-- Every actual input declaration receives the boundary above from the
same accepting fold. No restriction to singleton definition/theorem records
is used in this provenance theorem. -/
theorem declaration_prefix_checked (V : Type u) [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : Array Declaration} {env : Env} {declaration : Declaration}
    (present : declaration ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    CheckedDeclarationPrefix mode pins declaration env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  have chain := installRun_trace mode run (PushChain.refl Env.empty)
  exact declaration_prefix_run (V := V) verified (Array.mem_toList_iff.mpr present) run rfl
    ⟨⟨Kernel.Model.EnvModelM.empty V mode⟩, Kernel.EtaFamiliesClosed.empty⟩
    CSOKF.empty (chain.1.2.2 List.nodup_nil) fullyChecked.records

theorem CheckedDeclarationPrefix.definition {mode : CheckMode} {pins : List NatOpPinSet}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {hint : Kernel.ReducibilityHint} {env : Env}
    (receipt : CheckedDeclarationPrefix mode pins (.defnDecl header value hint) env) :
    DefinitionCheckedPrefix mode header value hint env := by
  obtain ⟨_, before, _, initial, _, _, _, canonical, environment, state, step, _, _, _, chain⟩ := receipt
  obtain ⟨type, annotated, calls, stored⟩ := definition_all_step step
  refine ⟨before, initial, type, annotated, canonical, environment, state, calls, ?_⟩
  obtain ⟨new, extension⟩ := chain.2.1
  change env.consts = _ at extension
  rw [extension]
  exact List.mem_append_right _ (stored ▸ List.mem_cons_self)

/-- An opaque body is checked and annotated at its actual prefix, but its
stored semantic entry is an axiom. This records no equation between the
opaque value and its checking body. -/
def OpaqueCheckedPrefix (mode : CheckMode) (header : Kernel.ConstantVal)
    (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr,
    before = mkFEnv before.env ∧ EnvWF before.env ∧ CSOKF initial ∧
    ValueAnnotationCalls mode before header value initial type annotated ∧
    Kernel.ConstantInfo.axiomInfo { header with type := type } ∈ env.consts

theorem CheckedDeclarationPrefix.opaque_value {mode : CheckMode} {pins : List NatOpPinSet}
    {header : Kernel.ConstantVal} {value : Kernel.Expr} {env : Env}
    (receipt : CheckedDeclarationPrefix mode pins (.opaqueDecl header value) env) :
    OpaqueCheckedPrefix mode header value env := by
  obtain ⟨_, before, _, initial, _, _, _, canonical, environment, state, step, _, _, _, chain⟩ := receipt
  obtain ⟨type, annotated, calls, stored⟩ := opaque_all_step step
  refine ⟨before, initial, type, annotated, canonical, environment, state, calls, ?_⟩
  obtain ⟨new, extension⟩ := chain.2.1
  change env.consts = _ at extension
  rw [extension]
  exact List.mem_append_right _ (stored ▸ List.mem_cons_self)

theorem definition_prefix_run {V : Type u} [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env)
    (model : Kernel.Model.EnvModelOk V mode start.2.1.env) (state : CSOKF initial)
    (unique : NodupNames finish.2.1.env)
    (checked : ∀ pc ∈ finish.2.2.toList, ∃ after, checkPending mode finish.2.1 pc {} = .ok ((), after)) :
    DefinitionCheckedPrefix mode header value hint finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    obtain ⟨tailChain, newPending, pending⟩ :=
      installRun_trace mode restRun (PushChain.self chain.canon)
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, calls, installed⟩ := definition_all_step stepRun
      have beforeWF : EnvWF start.2.1.env := by
        obtain ⟨witness⟩ := model.1
        exact witness.toEnvFacts.wf
      refine ⟨start.2.1, initial, type, annotated, canonical, beforeWF, state, calls, ?_⟩
      obtain ⟨_, ⟨new, extension⟩, _⟩ := tailChain
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · obtain ⟨nextModel, nextState, _⟩ :=
        annotStepC_model verified canonical chain.canon model state stepRun tailChain pending unique checked
      exact ih restPresent chain.canon nextModel nextState unique checked

theorem definition_prefix_checked (V : Type u) [Kernel.SetTheory V]
    {mode : CheckMode} {pins : List NatOpPinSet}
    (verified : mode.verifiedChecks = true)
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    DefinitionCheckedPrefix mode header value hint env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  have chain := installRun_trace mode run (PushChain.refl Env.empty)
  exact definition_prefix_run (V := V) verified (Array.mem_toList_iff.mpr present) run rfl
    ⟨⟨Kernel.Model.EnvModelM.empty V mode⟩, Kernel.EtaFamiliesClosed.empty⟩
    CSOKF.empty (chain.1.2.2 List.nodup_nil) fullyChecked.records

/-- An admitted let-bodied definition supplies the actual prefix and
annotation-state evidence needed by the let bridge. Only raw input scope
remains a separate source-export obligation here. -/
theorem DefinitionCheckedPrefix.let_trace {mode : CheckMode}
    {header : Kernel.ConstantVal} {type value body : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} {env : Env}
    (verified : mode.verifiedChecks = true)
    (receipt : DefinitionCheckedPrefix mode header (.letE type value body) hint env)
    (scope : Kernel.Expr.WScoped 0 (.letE type value body)) :
    ∃ priorEnv : Env, ∃ initial : CState, ∃ annotatedType annotatedValue : Kernel.Expr,
      EnvWF priorEnv ∧ CSOKF initial ∧
      ValueAnnotationCalls mode (mkFEnv priorEnv) header (.letE type value body)
        initial annotatedType annotatedValue ∧
      LetAnnotation mode priorEnv 0 type value body annotatedValue ∧
      Kernel.ConstantInfo.defnInfo { header with type := annotatedType } annotatedValue hint ∈ env.consts := by
  obtain ⟨before, initial, annotatedType, annotatedValue, canonical, environment, state, calls, present⟩ := receipt
  have actual : ValueAnnotationCalls mode (mkFEnv before.env) header (.letE type value body)
      initial annotatedType annotatedValue := canonical ▸ calls
  exact ⟨before.env, initial, annotatedType, annotatedValue, environment, state, actual,
    actual.let_trace verified environment state scope, present⟩

theorem opaque_all_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.opaqueDecl header value ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    OpaqueInstalledAll mode header value finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨type, annotated, calls, installed⟩ := opaque_all_step stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, type, annotated, calls, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem definition_all_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (present : Declaration.defnDecl header value hint ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    DefinitionInstalledAll mode header value hint env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact definition_all_run (Array.mem_toList_iff.mpr present) run rfl

theorem opaque_all_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.opaqueDecl header value ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    OpaqueInstalledAll mode header value env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact opaque_all_run (Array.mem_toList_iff.mpr present) run rfl

/-- Actual checked folds have unique stored names, including the complete
ordinary, primitive and block installation paths. -/
theorem checked_unique_names {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env}
    (checked : checkDecls mode pins declarations = .ok env) : NodupNames env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  have chain := (installRun_trace mode run (PushChain.refl Env.empty)).1
  exact chain.2.2 (by simp [NodupNames, Env.empty])

theorem unique_member {constants : List Kernel.ConstantInfo}
    (unique : (constants.map Kernel.ConstantInfo.name).Nodup)
    {first second : Kernel.ConstantInfo}
    (firstPresent : first ∈ constants) (secondPresent : second ∈ constants)
    (names : first.name = second.name) : first = second := by
  induction constants with
  | nil => exact absurd firstPresent List.not_mem_nil
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp firstPresent with rfl | firstRest
    · rcases List.mem_cons.mp secondPresent with rfl | secondRest
      · rfl
      · exact False.elim (parts.1 (names ▸ List.mem_map.mpr ⟨second, secondRest, rfl⟩))
    · rcases List.mem_cons.mp secondPresent with rfl | secondRest
      · exact False.elim (parts.1 (names ▸ List.mem_map.mpr ⟨first, firstRest, rfl⟩))
      · exact ih parts.2 firstRest secondRest

theorem DefinitionInstalled.exact {mode : CheckMode} {header installedHeader : Kernel.ConstantVal}
    {value installedValue : Kernel.Expr} {hint installedHint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalled mode header value hint env) (unique : NodupNames env)
    (lookup : env.find? header.name = some (.defnInfo installedHeader installedValue installedHint)) :
    installedHeader = { header with type := installedHeader.type } ∧ installedHint = hint ∧
    ∃ before : FEnv, ∃ initial afterType beforeValue afterValue : CState,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed =
        .ok (installedHeader.type, afterType) ∧
      annotConstantValC mode before header initial.flushed =
        .ok ((installedHeader, installedHeader.type), beforeValue) ∧
      (coreKnotI mode before checkFuel).annotate 0 value beforeValue = .ok (installedValue, afterValue) := by
  obtain ⟨before, initial, afterType, beforeValue, afterValue, type, annotated,
    typeRun, headerRun, valueRun, present⟩ := receipt
  have same := unique_member unique present (Kernel.Semantics.Env.find?_mem lookup)
    (by simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal] using
      (Kernel.Semantics.Env.find?_name lookup).symm)
  cases same
  exact ⟨rfl, rfl, before, initial, afterType, beforeValue, afterValue, typeRun, headerRun, valueRun⟩

theorem DefinitionInstalledAll.exact {mode : CheckMode} {header installedHeader : Kernel.ConstantVal}
    {value installedValue : Kernel.Expr} {hint installedHint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalledAll mode header value hint env) (unique : NodupNames env)
    (lookup : env.find? header.name = some (.defnInfo installedHeader installedValue installedHint)) :
    installedHeader = { header with type := installedHeader.type } ∧ installedHint = hint ∧
    ∃ before : FEnv, ∃ initial : CState,
      ValueAnnotationCalls mode before header value initial installedHeader.type installedValue := by
  obtain ⟨before, initial, type, annotated, calls, present⟩ := receipt
  have same := unique_member unique present (Kernel.Semantics.Env.find?_mem lookup)
    (by simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal] using
      (Kernel.Semantics.Env.find?_name lookup).symm)
  cases same
  exact ⟨rfl, rfl, before, initial, calls⟩

open Kernel.SetTheory in
theorem DefinitionInstalledAll.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} {env : Env}
    (receipt : DefinitionInstalledAll mode header value hint env)
    (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr, ∃ semanticType : V,
      ValueAnnotationCalls mode before header value initial type annotated ∧
      Kernel.Denotes strong.public.cval env levels ρ type semanticType ∧
      strong.public.cval header.name levels ∈ˢ semanticType ∧
      Kernel.Denotes strong.public.cval env levels ρ annotated (strong.public.cval header.name levels) := by
  obtain ⟨before, initial, type, annotated, calls, present⟩ := receipt
  obtain ⟨semanticType, typeRead, member⟩ := strong.public.mem _ present levels ρ
  exact ⟨before, initial, type, annotated, semanticType, calls, typeRead, member,
    strong.definition_values _ _ _ present levels ρ⟩

open Kernel.SetTheory in
theorem OpaqueInstalledAll.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr} {env : Env}
    (receipt : OpaqueInstalledAll mode header value env)
    (model : Kernel.Model V env) (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial : CState, ∃ type annotated : Kernel.Expr, ∃ semanticType : V,
      ValueAnnotationCalls mode before header value initial type annotated ∧
      Kernel.Denotes model.cval env levels ρ type semanticType ∧
      model.cval header.name levels ∈ˢ semanticType := by
  obtain ⟨before, initial, type, annotated, calls, present⟩ := receipt
  obtain ⟨semanticType, typeRead, member⟩ := model.mem _ present levels ρ
  exact ⟨before, initial, type, annotated, semanticType, calls, typeRead, member⟩

/-- The full theorem header, not merely its name/kind skeleton, survives
to the final environment. The prefix and annotation state are from its
actual installation step; the raw theorem proof remains opaque. -/
def TheoremInstalled (mode : CheckMode) (header : Kernel.ConstantVal) (value : Kernel.Expr) (env : Env) : Prop :=
  ∃ before : FEnv, ∃ initial afterAnnotation : CState, ∃ annotated : Kernel.Expr,
    (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed =
      .ok (annotated, afterAnnotation) ∧
    Kernel.ConstantInfo.thmInfo { header with type := annotated } value ∈ env.consts

theorem theorem_run {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : List Declaration} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.thmDecl header value ∈ declarations)
    {start finish : Nat × FEnv × Array PendingCheck} {initial final : CState}
    (run : InstallRun mode pins declarations start initial finish final)
    (canonical : start.2.1 = mkFEnv start.2.1.env) :
    TheoremInstalled mode header value finish.2.1.env := by
  induction run with
  | nil => exact absurd present List.not_mem_nil
  | @cons declaration rest start middle finish initial afterStep final step restRun ih =>
    obtain ⟨nextEnv, nextPending, rfl, stepRun⟩ := annotDeclStep_ok step
    have chain : PushChain start.2.1.env nextEnv :=
      (annotStepC_push mode start.1 (PushChain.self canonical) start.2.2 declaration
        initial (nextEnv, nextPending) afterStep stepRun).1
    rcases List.mem_cons.mp present with rfl | restPresent
    · obtain ⟨annotated, afterAnnotation, annotation, installed⟩ := theorem_step stepRun
      obtain ⟨⟨_, ⟨new, extension⟩, _⟩, _⟩ :=
        installRun_trace mode restRun (PushChain.self chain.canon)
      refine ⟨start.2.1, initial, afterAnnotation, annotated, annotation, ?_⟩
      rw [extension]
      exact List.mem_append_right _ (installed ▸ List.mem_cons_self)
    · exact ih restPresent chain.canon

theorem theorem_checked {mode : CheckMode} {pins : List NatOpPinSet}
    {declarations : Array Declaration} {env : Env} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Declaration.thmDecl header value ∈ declarations)
    (checked : checkDecls mode pins declarations = .ok env) :
    TheoremInstalled mode header value env := by
  obtain ⟨fullyChecked, rfl⟩ := checkDecls_fullyChecked mode checked
  obtain ⟨_, _, run⟩ := fullyChecked.1.run
  exact theorem_run (Array.mem_toList_iff.mpr present) run rfl

open Kernel.SetTheory in
/-- Read the theorem through its actual installed type, retaining the
annotation call that produced that type. This does not read the raw input
type as though its binder regimes and lets had already been repaired. -/
theorem TheoremInstalled.denotes {V : Type u} [SetTheory V]
    {mode : CheckMode} {header : Kernel.ConstantVal} {value : Kernel.Expr} {env : Env}
    (receipt : TheoremInstalled mode header value env) (model : Kernel.Model V env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ before : FEnv, ∃ initial afterAnnotation : CState, ∃ annotated : Kernel.Expr, ∃ type : V,
      (coreKnotI mode before checkFuel).annotate 0 header.type initial.flushed =
        .ok (annotated, afterAnnotation) ∧
      Kernel.Denotes model.cval env levels ρ annotated type ∧
      model.cval header.name levels ∈ˢ type := by
  obtain ⟨before, initial, afterAnnotation, annotated, annotation, present⟩ := receipt
  obtain ⟨type, denoted, member⟩ := model.mem _ present levels ρ
  exact ⟨before, initial, afterAnnotation, annotated, type, annotation, denoted, member⟩

end AnnotationTrace

/-- Every original source entry is compared against the full declaration
entries actually submitted to the independent source checker. Exact equality
retains bodies, hints, constructor arities and ordered recursor rules. -/
def SourceEntryMatches (ci : Lean.ConstantInfo) (declarations : Array Kernel.Declaration) : Prop :=
  match exportSourceEntry ci with
  | .error _ => False
  | .ok expected => expected ∈ streamEntries declarations

instance (ci : Lean.ConstantInfo) (declarations : Array Kernel.Declaration) :
    Decidable (SourceEntryMatches ci declarations) :=
  match h : exportSourceEntry ci with
  | .error _ => by simp only [SourceEntryMatches, h]; infer_instance
  | .ok _ => by simp only [SourceEntryMatches, h]; infer_instance

def SourceEntryCorrespondence (source : Source) (declarations : Array Kernel.Declaration) : Prop :=
  ∀ ci ∈ source.declarations, SourceEntryMatches ci declarations

instance (source : Source) (declarations : Array Kernel.Declaration) :
    Decidable (SourceEntryCorrespondence source declarations) :=
  inferInstanceAs (Decidable (∀ ci ∈ source.declarations, SourceEntryMatches ci declarations))

/-- An independent source installation attempt has no target map, reader,
bytes, hint oracle or target normalization state. Empty accelerator pins
request ordinary verified checking of the actual source definitions. -/
structure SourceInstallation (source : Source) (roots : List Lean.Name) where
  complete : CompleteSource source roots
  declarations : Array Kernel.Declaration
  exported : exportSourceDeclarations source = .ok declarations
  members : SourceEntryCorrespondence source declarations
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified [] declarations = .ok env

inductive SourceInstallError where
  | incomplete
  | exportFailure (reason : String)
  | correspondence
  | checking (error : Kernel.CheckError) (position : Nat)

/-- Success is evidence of this run, not a definition of the intended Dom.
Establishing success over that domain and the source/target annotation
simulation remain separate obligations. -/
def installSource (source : Source) (roots : List Lean.Name) :
    Except SourceInstallError (SourceInstallation source roots) :=
  if hc : CompleteSource source roots then
    match he : exportSourceDeclarations source with
    | .error reason => .error (.exportFailure reason)
    | .ok declarations =>
      if hm : SourceEntryCorrespondence source declarations then
        match hk : Kernel.Cached.checkDecls .verified [] declarations with
        | .error (error, position) => .error (.checking error position)
        | .ok env => .ok ⟨hc, declarations, he, hm, env, hk⟩
      else .error .correspondence
  else .error .incomplete

theorem SourceInstallation.has_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceInstallation source roots) :
    Nonempty (Kernel.Model V installed.env) :=
  Kernel.model_exists V [] installed.declarations installed.env installed.checked

/-- The source witness retains the checker's actual installed skeletons;
it does not identify raw binder annotations with installed annotations. -/
theorem SourceInstallation.skels {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) :
    Kernel.Cached.envSkels installed.env =
      Kernel.Cached.streamSkels installed.declarations.toList :=
  Kernel.Cached.checkDecls_skels installed.checked

theorem SourceInstallation.groups {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) :
    ∃ groups, exportSourceGroups source = .ok groups ∧ SourceGroupsCover source groups ∧
      orderSourceGroups (groups.length + 1) groups [] [] = .ok installed.declarations.toList :=
  exportSourceDeclarations_groups installed.exported

/-- The checked stream is a permutation of the independently exported
complete declaration groups: scheduling cannot discard or alter a body,
type, constructor, recursor rule, or any other declaration field. -/
theorem SourceInstallation.declarations_perm {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) :
    ∃ groups, SourceGroupsCover source groups ∧
      installed.declarations.toList.Perm (groups.map SourceDeclGroup.declaration) := by
  obtain ⟨groups, _, covered, ordered⟩ := installed.groups
  exact ⟨groups, covered, by simpa using orderSourceGroups_perm ordered⟩

/-- Each original source member has an exact entry in an actual declaration
of the accepted source fold. This retains full fields, not just membership
of an installation skeleton. Annotation pull-back remains a separate proof. -/
theorem SourceInstallation.member {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧
      declaration ∈ installed.declarations.toList ∧ entry ∈ readerEntries declaration ∧
      Kernel.Cached.checkDecls .verified [] installed.declarations = .ok installed.env := by
  have matched := installed.members ci present
  cases he : exportSourceEntry ci with
  | error reason => simp [SourceEntryMatches, he] at matched
  | ok entry =>
    have hm : entry ∈ installed.declarations.toList.flatMap readerEntries := by
      simpa only [SourceEntryMatches, he, streamEntries] using matched
    obtain ⟨declaration, hd, hm⟩ := List.mem_flatMap.mp hm
    exact ⟨entry, declaration, rfl, hd, hm, installed.checked⟩

/-- For declarations with the existing kernel's singleton install receipt,
the source-entry provenance reaches an actual environment constant. Block
members still use the full-stream skeleton theorem; this statement does not
invent a singleton receipt for inductive or quotient declarations. -/
theorem SourceInstallation.member_installed {source : Source} {roots : List Lean.Name}
    (installed : SourceInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧
      declaration ∈ installed.declarations.toList ∧ entry ∈ readerEntries declaration ∧
      ∀ skeleton, Kernel.Cached.declSkel declaration = some skeleton →
        ∃ actual ∈ installed.env.consts, Kernel.Cached.ciSkel actual = skeleton := by
  obtain ⟨entry, declaration, exported, presentDecl, entryMem, checked⟩ := installed.member present
  exact ⟨entry, declaration, exported, presentDecl, entryMem,
    fun _ hs => Kernel.Cached.checkDecls_installs checked (by simpa using presentDecl) hs⟩

/-- Source-only proposal context. It starts empty and is populated solely
from original source declarations and this bundle's proposed model records. -/
structure SourceModelState where
  types : Std.HashMap Kernel.Name (List Kernel.Name × Kernel.Expr) := {}
  heights : Std.HashMap Kernel.Name Nat := {}
  blocks : Std.HashMap Kernel.Name Kernel.Frontend.InModel.BlockRec := {}

def SourceModelState.note (state : SourceModelState) (declaration : Kernel.Declaration) :
    SourceModelState :=
  let values : List (Kernel.ConstantVal × Option Nat) := match declaration with
    | .axiomDecl cv | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv => [(cv, none)]
    | .defnDecl cv _ hint => [(cv, some (Kernel.Frontend.InModel.hintHeight hint))]
    | .indDecl block _ => block.map (fun ci => (ci.toConstantVal, none))
    | .basisDecl kind => kind.decls.map (fun ci => (ci.toConstantVal, none))
  values.foldl (fun state (cv, height) =>
    let heights := match height with
      | none => state.heights
      | some h => state.heights.insert cv.name h
    { state with types := state.types.insert cv.name (cv.levelParams, cv.type), heights }) state

structure SourceModelProposal (source : Source) where
  declarations : Array Kernel.Declaration
  blocks : List (SourceBlockEvidence source)
  basisSupport : List Kernel.BasisKind

/-- Fixed source-model support identities, defined by the kernel's own raw
Eq/PUnit basis (Basis/Eq.lean and Basis/PUnit.lean). Both are finite closed
blocks. They are submitted as explicit declarations, never imported from
target pin bytes or used to overwrite a source-owned declaration. -/
def sourceModelBasisSupport : List (Kernel.Name × Kernel.BasisKind) :=
  [(Kernel.eqName, .eqK), (Kernel.punitName, .punitK)]

/-- Reference closure of the finite raw basis terms. Literals and non-basis
record forms are refused here, so no implicit literal dependency is hidden. -/
def sourceSupportExprClosed (names : List Kernel.Name) : Kernel.Expr → Bool
  | .bvar _ | .sort _ => true
  | .const name _ => names.contains name
  | .fvar _ type => sourceSupportExprClosed names type
  | .app f a => sourceSupportExprClosed names f && sourceSupportExprClosed names a
  | .lam type body _ | .forallE type body _ =>
    sourceSupportExprClosed names type && sourceSupportExprClosed names body
  | .letE type value body => sourceSupportExprClosed names type &&
    sourceSupportExprClosed names value && sourceSupportExprClosed names body
  | .proj owner _ value => names.contains owner && sourceSupportExprClosed names value
  | .lit _ => false

def sourceBasisSupportClosed (kind : Kernel.BasisKind) : Bool :=
  let records := kind.decls
  let names := records.map Kernel.ConstantInfo.name
  records.all fun
    | .indInfo cv _ | .ctorInfo cv _ _ => sourceSupportExprClosed names cv.type
    | .recInfo cv _ _ rules => sourceSupportExprClosed names cv.type &&
        rules.all (fun rule => names.contains rule.ctor && sourceSupportExprClosed names rule.rhs)
    | _ => false

theorem sourceModelBasisSupport_closed :
    ∀ row ∈ sourceModelBasisSupport, sourceBasisSupportClosed row.2 = true := by decide

/-- Untrusted coverage proposal. The existing modeller has partial helpers;
this use does not prove termination or correspondence. Original declarations
are appended unchanged; independent checks below validate preservation and
submit every proposed record to the verified fold. No projection rewriting
or target data participates. -/
def proposeSourceModels (source : Source) (original : Array Kernel.Declaration) :
    ExportM (SourceModelProposal source) := do
  let groups ← exportSourceGroups source
  let mut state : SourceModelState := {}
  let mut declarations := #[]
  let mut evidence := []
  let mut basisSupport := []
  for declaration in original do
    if let .indDecl _ _ := declaration then
      let some group := groups.find? (fun group => decide (group.declaration = declaration))
        | throw "source model preparation could not associate an original group"
      let some owner := group.members.head? | throw "source model group has no owner"
      let block ← exportSourceBlockEvidence source owner
      unless decide (block.group.declaration = declaration) do
        throw "source model block evidence differs from the original declaration"
      evidence := evidence ++ [block]
      for type in block.shape.types do
        state := { state with blocks := state.blocks.insert type.cv.name block.shape }
      if Kernel.Frontend.InModel.wants block.shape then
        for (name, kind) in sourceModelBasisSupport do
          if (state.types[name]?).isNone then
            if original.any (fun d => d.names.contains name) then
              throw s!"source-owned support {repr name} is scheduled after a model that requires it"
            let support := Kernel.Declaration.basisDecl kind
            declarations := declarations.push support
            basisSupport := basisSupport ++ [kind]
            state := state.note support
        let context : Kernel.Frontend.InModel.Ctx :=
          ⟨fun n => state.types[n]?, fun n => state.heights.getD n 0, fun n => state.blocks[n]?⟩
        let proposed ← Kernel.Frontend.InModel.generate context block.shape
        for auxiliary in proposed do
          declarations := declarations.push auxiliary
          state := state.note auxiliary
    declarations := declarations.push declaration
    state := state.note declaration
  return ⟨declarations, evidence, basisSupport⟩

structure SourceModelInstallation (source : Source) (roots : List Lean.Name) where
  complete : CompleteSource source roots
  original : Array Kernel.Declaration
  exported : exportSourceDeclarations source = .ok original
  proposal : SourceModelProposal source
  proposed : proposeSourceModels source original = .ok proposal
  original_preserved : original.toList.Sublist proposal.declarations.toList
  members : SourceEntryCorrespondence source proposal.declarations
  support_checked : ∀ kind ∈ proposal.basisSupport,
    Kernel.Declaration.basisDecl kind ∈ proposal.declarations.toList ∧
      sourceBasisSupportClosed kind = true
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified [] proposal.declarations = .ok env

inductive SourceModelError where
  | incomplete
  | exportFailure (reason : String)
  | proposalFailure (reason : String)
  | changedOriginal
  | correspondence
  | supportMismatch
  | checking (error : Kernel.CheckError) (position : Nat)

def installSourceModels (source : Source) (roots : List Lean.Name) :
    Except SourceModelError (SourceModelInstallation source roots) :=
  if hc : CompleteSource source roots then
    match he : exportSourceDeclarations source with
    | .error reason => .error (.exportFailure reason)
    | .ok original =>
      match hp : proposeSourceModels source original with
      | .error reason => .error (.proposalFailure reason)
      | .ok proposal =>
        if hs : original.toList.Sublist proposal.declarations.toList then
          if hm : SourceEntryCorrespondence source proposal.declarations then
            if hb : ∀ kind ∈ proposal.basisSupport,
                Kernel.Declaration.basisDecl kind ∈ proposal.declarations.toList ∧
                  sourceBasisSupportClosed kind = true then
              match hk : Kernel.Cached.checkDecls .verified [] proposal.declarations with
              | .error (error, position) => .error (.checking error position)
              | .ok env => .ok ⟨hc, original, he, proposal, hp, hs, hm, hb, env, hk⟩
            else .error .supportMismatch
          else .error .correspondence
        else .error .changedOriginal
  else .error .incomplete

theorem SourceModelInstallation.has_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceModelInstallation source roots) :
    Nonempty (Kernel.Model V installed.env) :=
  Kernel.model_exists V [] installed.proposal.declarations installed.env installed.checked

/-- This is about actual installed definitions, including checked auxiliary
models. Pulling it back to original source expressions remains strong S. -/
theorem SourceModelInstallation.has_model_values (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceModelInstallation source roots) :
    ∃ model : Kernel.Model V installed.env, ∀ header value hint,
      Kernel.ConstantInfo.defnInfo header value hint ∈ installed.env.consts →
        ∀ φ ρ, Kernel.Denotes model.cval installed.env φ ρ value (model.cval header.name φ) :=
  Kernel.Cached.checkDecls_model_defn_values V [] installed.proposal.declarations
    installed.env installed.checked

theorem SourceModelInstallation.member {source : Source} {roots : List Lean.Name}
    (installed : SourceModelInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧
      declaration ∈ installed.proposal.declarations.toList ∧ entry ∈ readerEntries declaration ∧
      Kernel.Cached.checkDecls .verified [] installed.proposal.declarations = .ok installed.env := by
  have matched := installed.members ci present
  cases he : exportSourceEntry ci with
  | error reason => simp [SourceEntryMatches, he] at matched
  | ok entry =>
    have hm : entry ∈ installed.proposal.declarations.toList.flatMap readerEntries := by
      simpa only [SourceEntryMatches, he, streamEntries] using matched
    obtain ⟨declaration, hd, hm⟩ := List.mem_flatMap.mp hm
    exact ⟨entry, declaration, rfl, hd, hm, installed.checked⟩

theorem SourceModelInstallation.original_decl {source : Source} {roots : List Lean.Name}
    (installed : SourceModelInstallation source roots) {declaration : Kernel.Declaration}
    (present : declaration ∈ installed.original.toList) :
    declaration ∈ installed.proposal.declarations.toList :=
  installed.original_preserved.subset present

/-- A checked equation proposal uses the original constructor telescope.
Every argument is symbolic. In particular the selected field's type is
lifted from its original prefix into the complete constructor telescope.
The universe is only a proposal: the independent fold checks this theorem. -/
def sourceProjectionEquation {source : Source} (site : SourceProjectionSite source)
    (projection : Kernel.ConstantVal) (level : Kernel.Level) : ExportM Kernel.Declaration := do
  let .ctor constructor _ _ ← exportSourceEntry (.ctorInfo site.ctor)
    | throw "source projection equation has no original constructor export"
  unless decide (constructor.levelParams = projection.levelParams) do
    throw "source projection and constructor universe telescopes differ"
  let (binders, _) := Kernel.Frontend.stripPisAll constructor.type
  let count := site.owner.numParams + site.ctor.numFields
  unless binders.length == count do
    throw "source constructor telescope disagrees with original field counts"
  let some (fieldType, _) := binders[site.owner.numParams + site.field]?
    | throw "source projection equation field is absent"
  let arguments := (List.range count).map (fun i => Kernel.Expr.bvar (count - 1 - i))
  let parameters := arguments.take site.owner.numParams
  let levels := projection.levelParams.map Kernel.Level.param
  let constructorValue := Kernel.Expr.mkAppN (.const constructor.name levels) arguments
  let lhs := Kernel.Expr.mkAppN (.const projection.name levels) (parameters ++ [constructorValue])
  let rhs := Kernel.Expr.bvar (site.ctor.numFields - 1 - site.field)
  let type := fieldType.liftLooseBVars (site.ctor.numFields - site.field) 0
  let equation := Kernel.Expr.mkAppN (.const Kernel.eqName [level]) [type, lhs, rhs]
  let proof := Kernel.Expr.mkAppN (.const Kernel.eqReflName [level]) [type, rhs]
  let header : Kernel.ConstantVal :=
    ⟨projection.name.str "_source_constructor_equation", projection.levelParams,
      binders.foldr (fun (type, binder) body => .forallE type body binder) equation⟩
  return .thmDecl header (Kernel.Frontend.mkLams binders proof)

/-- Parameters in an open frame containing `extra` more recent binders. -/
def sourceParameterVars (count extra : Nat) : List Kernel.Expr :=
  (List.range count).map (fun i => .bvar (extra + count - 1 - i))

theorem sourceParameterVars_denotes {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ : Nat → V} (arguments : List V) (extra : Nat)
    (frame : ∀ index (inside : index < arguments.length),
      ρ (extra + arguments.length - 1 - index) = arguments[index]) :
    DenotesSpine values env levels ρ (sourceParameterVars arguments.length extra) arguments := by
  apply DenotesSpine.of_get (by simp [sourceParameterVars])
  intro index inside
  have inArgs : index < arguments.length := by simpa [sourceParameterVars] using inside
  simp only [sourceParameterVars, List.getElem_map, List.getElem_range]
  rw [← frame index inArgs]
  exact .bvar

/-- Read parameters below an arbitrary list of more recent binders. This
matches the exact source-owned de Bruijn spine, not a guessed display order. -/
theorem sourceParameterVars_pushed {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} (ρ : Nat → V) (parameters extras : List V) :
    DenotesSpine values env levels (pushArguments (pushArguments ρ parameters) extras)
      (sourceParameterVars parameters.length extras.length) parameters := by
  apply sourceParameterVars_denotes
  intro index inside
  have position : extras.length + parameters.length - 1 - index =
      extras.length + (parameters.length - 1 - index) := by omega
  rw [position, pushArguments_above, pushArguments_get parameters ρ index inside]

/-- Church-encoded constructor presentation at an arbitrary subject:
`∀ P : Prop, (∀ fields, subject = C params fields → P) → P`.
The field domains are the original constructor's dependent telescope.
This avoids importing an unchecked existential-support declaration. -/
def sourceConstructorCoverBody {source : Source} (site : SourceProjectionSite source)
    (owner constructor : Kernel.ConstantVal) (level : Kernel.Level)
    (extra : Nat) (subject : Kernel.Expr) : ExportM Kernel.Expr := do
  let binder : Kernel.BinderMeta := ⟨.never⟩
  let parameters := sourceParameterVars site.owner.numParams (extra + 1)
  let some remaining := Kernel.Frontend.instPisOpen constructor.type parameters
    | throw "source constructor coverage cannot instantiate original parameters"
  let some (fields, _) := remaining.stripPis site.ctor.numFields
    | throw "source constructor coverage cannot read the original field telescope"
  let levels := owner.levelParams.map Kernel.Level.param
  let liftedParams := parameters.map (fun p => p.liftLooseBVars site.ctor.numFields 0)
  let fieldVars := sourceParameterVars site.ctor.numFields 0
  let carrier := Kernel.Expr.mkAppN (.const owner.name levels) liftedParams
  let constructed := Kernel.Expr.mkAppN (.const constructor.name levels) (liftedParams ++ fieldVars)
  let equality := Kernel.Expr.mkAppN (.const Kernel.eqName [level])
    [carrier, subject.liftLooseBVars (site.ctor.numFields + 1) 0, constructed]
  let continuation := fields.foldr
    (fun (type, binder) body => Kernel.Expr.forallE type body binder)
    (.forallE equality (.bvar (site.ctor.numFields + 1)) binder)
  return .forallE (.sort .zero) (.forallE continuation (.bvar 1) binder) binder

/-- Untrusted proposal of a theorem covering arbitrary source carrier
values, not merely constructor applications. The proof eliminates through
the original recursor. Every other motive is the closed true proposition
`∀ P : Prop, P → P`; recursive hypotheses are not assumed as coverage.
Admission plus a semantic reading of this statement is still required. -/
def proposeSourceConstructorCover {source : Source} (site : SourceProjectionSite source) :
    ExportM Kernel.Declaration := do
  let binder : Kernel.BinderMeta := ⟨.never⟩
  let .induct owner _ ← exportSourceEntry (.inductInfo site.owner)
    | throw "source coverage owner export has the wrong kind"
  let .ctor constructor _ _ ← exportSourceEntry (.ctorInfo site.ctor)
    | throw "source coverage constructor export has the wrong kind"
  unless decide (owner.levelParams = constructor.levelParams) do
    throw "source coverage constructor universe telescope differs from its owner"
  let some (parameterBinders, .sort level) := owner.type.stripPis site.owner.numParams
    | throw "source coverage owner is not a zero-index parameter telescope"
  let levels := owner.levelParams.map Kernel.Level.param
  let carrier := Kernel.Expr.mkAppN (.const owner.name levels) (sourceParameterVars site.owner.numParams 0)
  let statementBody ← sourceConstructorCoverBody site owner constructor level 1 (.bvar 0)
  let type := parameterBinders.foldr
    (fun (type, binder) body => Kernel.Expr.forallE type body binder)
    (.forallE carrier statementBody binder)
  let some (.recInfo recursor) := source.find (site.ownerName.str "rec")
    | throw "source coverage has no original recursor"
  unless recursor.numParams == site.owner.numParams && recursor.numIndices == 0 do
    throw "source coverage recursor owner parameters or indices disagree"
  let .recursor recHeader _ _ _ ← exportSourceEntry (.recInfo recursor)
    | throw "source coverage recursor export has the wrong kind"
  unless owner.levelParams.all (fun p => recHeader.levelParams.contains p) &&
      (recHeader.levelParams.filter (fun p => !owner.levelParams.contains p)).length ≤ 1 do
    throw "source coverage recursor universe selection is unsupported"
  let recLevels := recHeader.levelParams.map fun p =>
    if owner.levelParams.contains p then Kernel.Level.param p else .zero
  let recType := recHeader.type.instantiateLevelParams recHeader.levelParams recLevels
  let parameters := sourceParameterVars site.owner.numParams 1
  let some recType := Kernel.Frontend.instPisOpen recType parameters
    | throw "source coverage recursor parameters cannot be instantiated"
  let truth : Kernel.Expr := .forallE (.sort .zero)
    (.forallE (.bvar 0) (.bvar 1) binder) binder
  let truthProof : Kernel.Expr := .lam (.sort .zero)
    (.lam (.bvar 0) (.bvar 0) binder) binder
  let makeMotive := fun domain => do
    let (binders, _) := Kernel.Frontend.stripPisAll domain
    match binders with
    | [(major, _)] =>
      if Kernel.Frontend.headIs owner.name major then
        let body ← (sourceConstructorCoverBody site owner constructor level 2 (.bvar 0)).toOption
        return Kernel.Frontend.mkLams binders body
      else return Kernel.Frontend.mkLams binders truth
    | _ => return Kernel.Frontend.mkLams binders truth
  let some (motives, recType) := Kernel.Frontend.buildBinders makeMotive recursor.numMotives recType
    | throw "source coverage motive construction failed"
  let makeMinor := fun domain => do
    let (binders, result) := Kernel.Frontend.stripPisAll domain
    let some major := result.getAppArgs.getLast? | none
    if Kernel.Frontend.headIs constructor.name major then
      if site.ctor.numFields > binders.length then none else do
        let expected := Kernel.Expr.mkAppN (.const constructor.name levels)
          (sourceParameterVars site.owner.numParams (1 + binders.length) ++
            (List.range site.ctor.numFields).map (fun i => .bvar (binders.length - 1 - i)))
        if !decide (major = expected) then none else do
          let coverage ← (sourceConstructorCoverBody site owner constructor level
            (1 + binders.length) major).toOption
          let some (arguments, _) := coverage.stripPis 2 | none
          let carrier := Kernel.Expr.mkAppN (.const owner.name levels)
            (sourceParameterVars site.owner.numParams (3 + binders.length))
          let reflexive := Kernel.Expr.mkAppN (.const Kernel.eqReflName [level])
            [carrier, major.liftLooseBVars 2 0]
          let fields := (List.range site.ctor.numFields).map
            (fun i => Kernel.Expr.bvar (binders.length + 1 - i))
          return Kernel.Frontend.mkLams binders (Kernel.Frontend.mkLams arguments
            (Kernel.Expr.mkAppN (.bvar 0) (fields ++ [reflexive])))
    else return Kernel.Frontend.mkLams binders truthProof
  let some (minors, recType) := Kernel.Frontend.buildBinders makeMinor recursor.numMinors recType
    | throw "source coverage minor construction failed"
  let .forallE majorDomain _ _ := recType | throw "source coverage recursor has no major premise"
  unless Kernel.Frontend.headIs owner.name majorDomain do
    throw "source coverage recursor major premise has another owner"
  let application := Kernel.Expr.mkAppN (.const recHeader.name recLevels)
    (parameters ++ motives ++ minors ++ [.bvar 0])
  let value := Kernel.Frontend.mkLams parameterBinders (.lam carrier application binder)
  return .thmDecl ⟨owner.name.str "_source_constructor_cover", owner.levelParams, type⟩ value

/-- Source-owned lowering proposal. Original source syntax, constructor and
recursor metadata are authoritative. The generated source model supplies
only a proposed field universe. Neither target data nor reader projRewrite
is consulted. Acceptance below must check both the replacement and its
universal constructor equation; generation itself proves no semantics. -/
def proposeSourceProjection (source : Source) (state : SourceModelState)
    (declaration : Kernel.Declaration) : ExportM (Option (Kernel.Declaration × Kernel.Declaration)) := do
  let .defnDecl header body hint := declaration | return none
  let some ci := source.declarations.find? (fun ci => decide (sourceName ci.name = header.name))
    | return none
  let .defnInfo definition := ci | return none
  let some (owner, field, binders) := sourceProjectionBody definition.value | return none
  let site ← sourceProjectionSite source owner field
  unless binders == site.owner.numParams + 1 do
    throw "source projection binder count differs from original owner parameters"
  let original ← exportSourceEntry ci
  unless decide (original = .defn header body hint) do
    throw "source projection declaration differs from its immutable original export"
  let T := sourceName owner
  let some (_, iotaType) := state.types[Kernel.Frontend.projIotaName T field]?
    | return none
  let some level := Kernel.Frontend.projIotaLevel iotaType
    | throw "source-generated projection equation has no field universe"
  let some (.recInfo recursor) := source.find (owner.str "rec")
    | throw "source projection owner has no original recursor"
  unless recursor.numParams == site.owner.numParams && recursor.numIndices == 0 do
    throw "source projection recursor parameters or indices differ from original owner"
  let .recursor recHeader _ _ _ ← exportSourceEntry (.recInfo recursor)
    | throw "source projection recursor export has the wrong kind"
  let ownerRecipe : Kernel.Frontend.ProjRecOwner := {
    T, lps := site.owner.levelParams.map sourceName, nP := site.owner.numParams,
    ctor := sourceName site.ctorName, nF := site.ctor.numFields,
    recName := recHeader.name, recLps := recHeader.levelParams, recType := recHeader.type,
    numMotives := recursor.numMotives, numMinors := recursor.numMinors }
  let some lowered := Kernel.Frontend.projRecValue ownerRecipe level header.type body field
    | throw "source projection recursor proposal cannot represent the original projection"
  let equation ← sourceProjectionEquation site header level
  return some (.defnDecl header lowered hint, equation)

/-- Independent correspondence check for a proposed source projection.
The replacement may be generated by any algorithm: this receipt binds its
full header and hint to the exact original export and its checked equation
to the exact original constructor/field. It makes no extensional claim. -/
structure SourceProjectionReceipt (source : Source)
    (original replacement equation : Kernel.Declaration) where
  definition : Lean.DefinitionVal
  original_lookup : source.find definition.name = some (.defnInfo definition)
  header : Kernel.ConstantVal
  body : Kernel.Expr
  hint : Kernel.ReducibilityHint
  exported : exportSourceEntry (.defnInfo definition) = .ok (.defn header body hint)
  original_decl : original = .defnDecl header body hint
  ownerName : Lean.Name
  field : Nat
  site : SourceProjectionSite source
  site_checked : sourceProjectionSite source ownerName field = .ok site
  raw_shape : sourceProjectionBody definition.value =
    some (ownerName, field, site.owner.numParams + 1)
  value : Kernel.Expr
  replacement_decl : replacement = .defnDecl header value hint
  level : Kernel.Level
  equation_image : sourceProjectionEquation site header level = .ok equation

def checkSourceProjectionReceipt (source : Source)
    (original replacement equation : Kernel.Declaration) :
    ExportM (SourceProjectionReceipt source original replacement equation) := do
  let .defnDecl originalHeader _ _ := original
    | throw "source projection receipt original is not a definition"
  let some ci := source.declarations.find?
      (fun ci => decide (sourceName ci.name = originalHeader.name))
    | throw "source projection receipt original definition is absent"
  match ho : source.find ci.name with
  | some (.defnInfo definition) =>
    if hn : definition.name = ci.name then
      have originalLookup : source.find definition.name = some (.defnInfo definition) := by
        simpa only [hn] using ho
      match he : exportSourceEntry (.defnInfo definition) with
      | .ok (.defn header body hint) =>
        if hd : original = .defnDecl header body hint then
          let some (owner, field, _) := sourceProjectionBody definition.value
            | throw "source projection receipt original body is not a projection"
          match hm : sourceProjectionSite source owner field with
          | .error why => throw why
          | .ok site =>
            if hs : sourceProjectionBody definition.value =
                some (owner, field, site.owner.numParams + 1) then
              let .defnDecl _ value _ := replacement
                | throw "source projection replacement is not a definition"
              if hr : replacement = .defnDecl header value hint then
                let .thmDecl equationHeader _ := equation
                  | throw "source projection equation is not a theorem"
                let some level := Kernel.Frontend.projIotaLevel equationHeader.type
                  | throw "source projection equation is not a universally quantified equality"
                match hq : sourceProjectionEquation site header level with
                | .error why => throw why
                | .ok expected =>
                  if hsame : expected = equation then
                    return ⟨definition, originalLookup, header, body, hint, he, hd,
                      owner, field, site, hm, hs, value, hr, level,
                      by simpa only [hsame] using hq⟩
                  else throw "source projection equation differs from the original constructor field equation"
              else throw "source projection replacement changed the original header or hint"
            else throw "source projection receipt shape disagrees with original owner metadata"
        else throw "source projection receipt original differs from its exact source export"
      | _ => throw "source projection receipt source definition could not be exported"
    else throw "source projection receipt original identity is inconsistent"
  | _ => throw "source projection receipt does not identify the exact original definition"

theorem SourceProjectionReceipt.constructor_computes {source : Source} {original replacement equation}
    (receipt : SourceProjectionReceipt source original replacement equation)
    (levels : List Lean.Level) (params fields : List Lean.Expr)
    (parameterCount : params.length = receipt.site.owner.numParams)
    (fieldCount : fields.length = receipt.site.ctor.numFields) {value : Lean.Expr}
    (selected : fields[receipt.site.field]? = some value) :
    sourceProjectionCompute source (.proj receipt.ownerName receipt.field
      (sourceApps (.const receipt.site.ctorName levels) (params ++ fields))) = .ok value :=
  sourceProjectionCompute_constructor receipt.site_checked levels params fields
    parameterCount fieldCount selected

theorem SourceProjectionReceipt.original_fields {source : Source} {original replacement equation}
    (receipt : SourceProjectionReceipt source original replacement equation) :
    SourceValImage receipt.definition.toConstantVal receipt.header ∧
      exportSourceExpr receipt.definition.levelParams receipt.definition.value = .ok receipt.body ∧
      receipt.hint = exportHint receipt.definition.hints :=
  exportSourceEntry_defn receipt.exported

/-- A structural receipt, deliberately distinct from Sublist preservation.
Each changed declaration is exactly the source-owned proposal and its
constructor equation occurs immediately afterwards in the checked stream.
This relation records normalization, not semantic equality by definition. -/
inductive SourceProjectionNormalization (source : Source) :
    SourceModelState → List Kernel.Declaration → List Kernel.Declaration → Prop
  | nil (state) : SourceProjectionNormalization source state [] []
  | unchanged {state original rest output}
      (proposal : proposeSourceProjection source state original = .ok none)
      (tail : SourceProjectionNormalization source (state.note original) rest output) :
      SourceProjectionNormalization source state (original :: rest) (original :: output)
  | lowered {state original rest replacement equation output}
      (proposal : proposeSourceProjection source state original = .ok (some (replacement, equation)))
      (association : SourceProjectionReceipt source original replacement equation)
      (fresh : ∀ name ∈ equation.names, state.types[name]? = none ∧
        ∀ declaration ∈ original :: rest, name ∉ declaration.names)
      (tail : SourceProjectionNormalization source
        ((state.note replacement).note equation) rest output) :
      SourceProjectionNormalization source state (original :: rest)
        (replacement :: equation :: output)

def normalizeSourceProjections (source : Source) (state : SourceModelState)
    (input : List Kernel.Declaration) :
    ExportM { output : List Kernel.Declaration // SourceProjectionNormalization source state input output } :=
  match input with
  | [] => .ok ⟨[], .nil state⟩
  | original :: rest =>
    match hp : proposeSourceProjection source state original with
    | .error why => .error why
    | .ok none => do
      let output ← normalizeSourceProjections source (state.note original) rest
      return ⟨original :: output.val, .unchanged hp output.property⟩
    | .ok (some (replacement, equation)) =>
      if hf : ∀ name ∈ equation.names, state.types[name]? = none ∧
          ∀ declaration ∈ original :: rest, name ∉ declaration.names then do
        let association ← checkSourceProjectionReceipt source original replacement equation
        let output ← normalizeSourceProjections source
          ((state.note replacement).note equation) rest
        return ⟨replacement :: equation :: output.val, .lowered hp association hf output.property⟩
      else .error "source projection equation name conflicts with an existing declaration"

structure SourceNormalizedInstallation (source : Source) (roots : List Lean.Name) where
  complete : CompleteSource source roots
  original : Array Kernel.Declaration
  exported : exportSourceDeclarations source = .ok original
  modelProposal : SourceModelProposal source
  proposed : proposeSourceModels source original = .ok modelProposal
  original_preserved : original.toList.Sublist modelProposal.declarations.toList
  original_members : SourceEntryCorrespondence source modelProposal.declarations
  support_checked : ∀ kind ∈ modelProposal.basisSupport,
    Kernel.Declaration.basisDecl kind ∈ modelProposal.declarations.toList ∧
      sourceBasisSupportClosed kind = true
  declarations : List Kernel.Declaration
  normalization : SourceProjectionNormalization source {} modelProposal.declarations.toList declarations
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified [] declarations.toArray = .ok env

def installSourceNormalized (source : Source) (roots : List Lean.Name) :
    Except SourceModelError (SourceNormalizedInstallation source roots) :=
  if hc : CompleteSource source roots then
    match he : exportSourceDeclarations source with
    | .error why => .error (.exportFailure why)
    | .ok original =>
      match hp : proposeSourceModels source original with
      | .error why => .error (.proposalFailure why)
      | .ok proposal =>
        if hs : original.toList.Sublist proposal.declarations.toList then
          if hm : SourceEntryCorrespondence source proposal.declarations then
            if hb : ∀ kind ∈ proposal.basisSupport,
                Kernel.Declaration.basisDecl kind ∈ proposal.declarations.toList ∧
                  sourceBasisSupportClosed kind = true then
              match normalizeSourceProjections source {} proposal.declarations.toList with
              | .error why => .error (.proposalFailure why)
              | .ok output =>
                match hk : Kernel.Cached.checkDecls .verified [] output.val.toArray with
                | .error (error, position) => .error (.checking error position)
                | .ok env => .ok ⟨hc, original, he, proposal, hp, hs, hm, hb,
                    output.val, output.property, env, hk⟩
            else .error .supportMismatch
          else .error .correspondence
        else .error .changedOriginal
  else .error .incomplete

theorem SourceNormalizedInstallation.has_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    Nonempty (Kernel.Model V installed.env) :=
  Kernel.model_exists V [] installed.declarations.toArray installed.env installed.checked

theorem SourceNormalizedInstallation.strong_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    Nonempty (StrongInstalledModel V installed.env) :=
  strongInstalledModel_exists V [] installed.declarations.toArray installed.env installed.checked

/-- In particular, every generated constructor equation is connected to
the actual full annotated statement of its independently installed theorem. -/
theorem SourceNormalizedInstallation.theorem_annotation
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots)
    {header : Kernel.ConstantVal} {value : Kernel.Expr}
    (present : Kernel.Declaration.thmDecl header value ∈ installed.declarations) :
    AnnotationTrace.TheoremInstalled .verified header value installed.env :=
  AnnotationTrace.theorem_checked (by simpa using present) installed.checked

/-- A separate certifier-owned extension of an independently installed
source bundle. The new theorem quantifies every carrier member. This
receipt records its exact proposal and admission, not yet its semantic
constructor-surjectivity interpretation. The original routes are unchanged. -/
structure SourceConstructorCoverChecked {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) (site : SourceProjectionSite source) where
  header : Kernel.ConstantVal
  value : Kernel.Expr
  proposed : proposeSourceConstructorCover site = .ok (.thmDecl header value)
  fresh : ∀ declaration ∈ installed.declarations, header.name ∉ declaration.names
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified []
    (installed.declarations ++ [Kernel.Declaration.thmDecl header value]).toArray = .ok env

def checkSourceConstructorCover {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) (site : SourceProjectionSite source) :
    Except SourceModelError (SourceConstructorCoverChecked installed site) :=
  match hp : proposeSourceConstructorCover site with
  | .error why => .error (.proposalFailure why)
  | .ok (.thmDecl header value) =>
    if hf : ∀ declaration ∈ installed.declarations, header.name ∉ declaration.names then
      match hk : Kernel.Cached.checkDecls .verified []
          (installed.declarations ++ [Kernel.Declaration.thmDecl header value]).toArray with
      | .error (error, position) => .error (.checking error position)
      | .ok env => .ok ⟨header, value, hp, hf, env, hk⟩
    else .error (.proposalFailure "source constructor coverage name is not fresh")
  | .ok _ => .error (.proposalFailure "source constructor coverage proposal is not a theorem")

theorem SourceConstructorCoverChecked.annotation {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) :
    AnnotationTrace.TheoremInstalled .verified coverage.header coverage.value coverage.env :=
  AnnotationTrace.theorem_checked (by simp) coverage.checked

theorem SourceConstructorCoverChecked.strong_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) :
    Nonempty (StrongInstalledModel V coverage.env) :=
  strongInstalledModel_exists V [] _ coverage.env coverage.checked

theorem SourceInstallation.strong_model (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceInstallation source roots) :
    Nonempty (StrongInstalledModel V installed.env) :=
  strongInstalledModel_exists V [] installed.declarations installed.env installed.checked

/-- Pull-back on the independently installed direct source. The exact source
fold remains visible and the semantic image premises are not inferred from
it. This result supplies types/definition values, not the remaining strong
recursor laws or the end-to-end S association. -/
theorem SourceInstallation.target_value_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceInstallation source roots)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv) (map : PullbackMap)
    (types : PullbackTypeEvidence target.public installed.env map)
    (values : PullbackDefinitionEvidence target installed.env map)
    (locality : map.LevelLocality installed.env targetEnv) :
    Kernel.Cached.checkDecls .verified [] installed.declarations = .ok installed.env ∧
      ∃ pulled : PublicValueModel V installed.env,
        pulled.model.cval = map.values target.public.cval :=
  ⟨installed.checked, values.valueModel types locality, rfl⟩

/-- The normalized source route remains a distinct input receipt, retaining
its immutable original stream and checked normalization evidence. This does
not identify that receipt with the direct/Sublist installation route. -/
theorem SourceNormalizedInstallation.target_value_pullback {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots)
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv) (map : PullbackMap)
    (types : PullbackTypeEvidence target.public installed.env map)
    (values : PullbackDefinitionEvidence target installed.env map)
    (locality : map.LevelLocality installed.env targetEnv) :
    Kernel.Cached.checkDecls .verified [] installed.declarations.toArray = .ok installed.env ∧
      ∃ pulled : PublicValueModel V installed.env,
        pulled.model.cval = map.values target.public.cval :=
  ⟨installed.checked, values.valueModel types locality, rfl⟩

/-- Inserting subject and proposition binders must leave references to earlier
fields fixed while moving references to original parameters by two slots. -/
def liftSourceFieldDomains : Nat → List (Kernel.Expr × Kernel.BinderMeta) →
    List (Kernel.Expr × Kernel.BinderMeta)
  | _, [] => []
  | index, (domain, binder) :: rest =>
    (domain.liftLooseBVars 2 index, binder) :: liftSourceFieldDomains (index + 1) rest

theorem liftSourceFieldDomains_length (index : Nat) (fields : List (Kernel.Expr × Kernel.BinderMeta)) :
    (liftSourceFieldDomains index fields).length = fields.length := by
  induction fields generalizing index with
  | nil => rfl
  | cons field rest ih => simp only [liftSourceFieldDomains, List.length_cons, ih]

/-- Data extracted from the *installed* headers, independent of the raw
generator's binder annotations. The checker below binds all three headers to
their actual environment entries before this relation is used. -/
structure SourceCoverShapeData where
  owner : Kernel.ConstantVal
  constructor : Kernel.ConstantVal
  theoremHeader : Kernel.ConstantVal
  parameters : List (Kernel.Expr × Kernel.BinderMeta)
  constructorParameters : List (Kernel.Expr × Kernel.BinderMeta)
  coverageParameters : List (Kernel.Expr × Kernel.BinderMeta)
  fields : List (Kernel.Expr × Kernel.BinderMeta)
  coverageFields : List (Kernel.Expr × Kernel.BinderMeta)
  constructorResult : Kernel.Expr
  subjectType : Kernel.Expr
  equalityType : Kernel.Expr
  level : Kernel.Level
  subjectBinder : Kernel.BinderMeta
  propositionBinder : Kernel.BinderMeta
  continuationBinder : Kernel.BinderMeta
  equalityBinder : Kernel.BinderMeta
  continuation : Kernel.Expr
  propositionIndex : Nat

def sourceForalls (binders : List (Kernel.Expr × Kernel.BinderMeta)) (body : Kernel.Expr) : Kernel.Expr :=
  binders.foldr (fun (domain, binder) rest => .forallE domain rest binder) body

theorem sourceForalls_binders (binders : List (Kernel.Expr × Kernel.BinderMeta))
    (body : Kernel.Expr) : InstalledBinderPrefix binders.length (sourceForalls binders body) := by
  induction binders with
  | nil => exact .zero body
  | cons binder rest ih => exact .succ ih

/-- Typed argument tuples depend on binder domains, not the regime of the
enclosing forall. Each complete telescope is interpreted with its own regime. -/
theorem sourceForalls_transfer {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {sourceBinders targetBinders : List (Kernel.Expr × Kernel.BinderMeta)}
    {sourceBody targetBody result : Kernel.Expr} {arguments : List V}
    (domains : sourceBinders.map Prod.fst = targetBinders.map Prod.fst)
    (length : arguments.length = sourceBinders.length)
    (typed : InstalledTelescope values env levels ρ (sourceForalls sourceBinders sourceBody)
      arguments finalρ result) :
    result = sourceBody ∧
      InstalledTelescope values env levels ρ (sourceForalls targetBinders targetBody)
        arguments finalρ targetBody := by
  induction sourceBinders generalizing targetBinders arguments ρ with
  | nil =>
    have ha : arguments = [] := by simpa using length
    have ht : targetBinders = [] := by simpa using domains.symm
    subst arguments
    subst targetBinders
    cases typed
    exact ⟨rfl, .nil⟩
  | cons sourceBinder rest ih =>
    cases targetBinders with
    | nil => simp at domains
    | cons targetBinder targetRest =>
      simp only [List.map_cons, List.cons.injEq] at domains
      cases arguments with
      | nil => simp at length
      | cons argument arguments =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at length
        cases typed with
        | cons domainDenoted argumentTyped remaining =>
          obtain ⟨resultEq, transferred⟩ := ih domains.2 length remaining
          refine ⟨resultEq, .cons ?_ argumentTyped transferred⟩
          simpa only [← domains.1] using domainDenoted

theorem sourceForalls_lift (binders : List (Kernel.Expr × Kernel.BinderMeta))
    (body : Kernel.Expr) (index : Nat) :
    (sourceForalls binders body).liftLooseBVars 2 index =
      sourceForalls (liftSourceFieldDomains index binders)
        (body.liftLooseBVars 2 (index + binders.length)) := by
  induction binders generalizing index with
  | nil => rfl
  | cons binder rest ih =>
    simp only [sourceForalls, List.foldr_cons, Kernel.Expr.liftLooseBVars,
      liftSourceFieldDomains, List.length_cons]
    congr 1
    simpa only [sourceForalls, Nat.add_assoc, Nat.add_comm 1] using ih (index + 1)

/-- Reflect a typed coverage tuple back to the original constructor telescope.
The original telescope's actual denotation supplies domain existence; this
does not assume raw source annotations denote or infer a source model from a
target model. Earlier dependent arguments are retained in both valuations. -/
theorem sourceForalls_reflect_lift {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat}
    {binders targetBinders : List (Kernel.Expr × Kernel.BinderMeta)}
    {body targetBody result : Kernel.Expr} {arguments : List V}
    {index : Nat} {ρ target finalTarget : Nat → V} {type : V}
    (domains : targetBinders.map Prod.fst = (liftSourceFieldDomains index binders).map Prod.fst)
    (length : arguments.length = binders.length)
    (denoted : Kernel.Denotes values env levels ρ (sourceForalls binders body) type)
    (typed : InstalledTelescope values env levels target (sourceForalls targetBinders targetBody)
      arguments finalTarget result)
    (related : ValuationLift 2 index ρ target) :
    ∃ finalρ, InstalledTelescope values env levels ρ (sourceForalls binders body)
      arguments finalρ body ∧ ValuationLift 2 (index + arguments.length) finalρ finalTarget := by
  induction binders generalizing targetBinders arguments index ρ target type with
  | nil =>
    have ha : arguments = [] := by simpa using length
    have ht : targetBinders = [] := by simpa [liftSourceFieldDomains] using domains
    subst arguments
    subst targetBinders
    cases typed
    exact ⟨ρ, .nil, related⟩
  | cons binder rest ih =>
    cases targetBinders with
    | nil => simp [liftSourceFieldDomains] at domains
    | cons targetBinder targetRest =>
      simp only [liftSourceFieldDomains, List.map_cons, List.cons.injEq] at domains
      cases arguments with
      | nil => simp at length
      | cons argument arguments =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at length
        cases denoted with
        | pi hA hB hP =>
          cases typed with
          | cons targetDomain targetTyped targetRemaining =>
            have shifted := denotes_lift hA related
            rw [← domains.1] at shifted
            obtain rfl := Kernel.Denotes_functional targetDomain shifted
            obtain ⟨finalρ, originalRemaining, finalRelated⟩ :=
              ih domains.2 length (hB argument targetTyped) targetRemaining (related.push argument)
            refine ⟨finalρ, .cons hA targetTyped originalRemaining, ?_⟩
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using finalRelated

/-- Full structural checks, including universe lists, original identities and
dependent domains. Each enclosing telescope retains its own installed binder
regimes: a constructor returns a carrier, whereas the continuation returns Prop.
Only domain expressions are compared across those different telescopes.
Equality is Lean's structural equality, not hash equality. -/
def SourceCoverShape {source : Source} (site : SourceProjectionSite source)
    (coverageHeader : Kernel.ConstantVal) (data : SourceCoverShapeData) : Prop :=
  let levels := data.owner.levelParams.map Kernel.Level.param
  let params := sourceParameterVars site.owner.numParams 0
  let ctorParams := sourceParameterVars site.owner.numParams site.ctor.numFields
  let coverParams := sourceParameterVars site.owner.numParams (site.ctor.numFields + 2)
  data.owner.name = sourceName site.ownerName ∧
  data.constructor.name = sourceName site.ctorName ∧
  data.theoremHeader.name = coverageHeader.name ∧
  data.owner.levelParams = data.constructor.levelParams ∧
  data.owner.levelParams = data.theoremHeader.levelParams ∧
  data.theoremHeader.levelParams = coverageHeader.levelParams ∧
  data.parameters.length = site.owner.numParams ∧
  data.fields.length = site.ctor.numFields ∧
  data.constructorParameters.map Prod.fst = data.parameters.map Prod.fst ∧
  data.coverageParameters.map Prod.fst = data.parameters.map Prod.fst ∧
  data.coverageFields.map Prod.fst = (liftSourceFieldDomains 0 data.fields).map Prod.fst ∧
  data.owner.type = sourceForalls data.parameters (.sort data.level) ∧
  data.constructor.type = sourceForalls data.constructorParameters
    (sourceForalls data.fields data.constructorResult) ∧
  data.constructorResult = Kernel.Expr.mkAppN (.const data.owner.name levels) ctorParams ∧
  data.subjectType = Kernel.Expr.mkAppN (.const data.owner.name levels) params ∧
  data.equalityType = Kernel.Expr.mkAppN (.const Kernel.eqName [data.level])
    [Kernel.Expr.mkAppN (.const data.owner.name levels) coverParams,
      .bvar (site.ctor.numFields + 1),
      Kernel.Expr.mkAppN (.const data.constructor.name levels)
        (coverParams ++ sourceParameterVars site.ctor.numFields 0)] ∧
  data.propositionIndex = site.ctor.numFields + 1 ∧
  data.continuation = sourceForalls data.coverageFields
    (.forallE data.equalityType (.bvar data.propositionIndex) data.equalityBinder) ∧
  data.theoremHeader.type = sourceForalls data.coverageParameters
    (.forallE data.subjectType
      (.forallE (.sort .zero)
        (.forallE data.continuation (.bvar 1) data.continuationBinder)
        data.propositionBinder) data.subjectBinder)

instance {source : Source} (site : SourceProjectionSite source)
    (header : Kernel.ConstantVal) (data : SourceCoverShapeData) :
    Decidable (SourceCoverShape site header data) := by
  unfold SourceCoverShape
  infer_instance

structure SourceCoverInstalledShape {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) where
  data : SourceCoverShapeData
  ownerCaps : Kernel.IndCaps
  ownerLookup : coverage.env.find? (sourceName site.ownerName) = some (.indInfo data.owner ownerCaps)
  constructorLookup : coverage.env.find? (sourceName site.ctorName) =
    some (.ctorInfo data.constructor site.owner.numParams site.ctor.numFields)
  theoremLookup : coverage.env.find? coverage.header.name = some (.thmInfo data.theoremHeader coverage.value)
  shape : SourceCoverShape site coverage.header data

/-- A fail-closed installed annotation/field-domain receipt. Its success for
every source domain member is a separate obligation, not a new definition of Dom. -/
def checkSourceCoverInstalledShape {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) :
    Except String (SourceCoverInstalledShape coverage) := do
  let some (.indInfo owner caps) ← pure (coverage.env.find? (sourceName site.ownerName))
    | throw "installed source coverage owner is missing or has wrong kind"
  let some (.ctorInfo constructor numParams numFields) ← pure (coverage.env.find? (sourceName site.ctorName))
    | throw "installed source coverage constructor is missing or has wrong kind"
  let some (.thmInfo theoremHeader _) ← pure (coverage.env.find? coverage.header.name)
    | throw "installed source coverage theorem is missing or has wrong kind"
  let some (parameters, .sort level) := owner.type.stripPis site.owner.numParams
    | throw "installed source owner telescope is not the original unindexed shape"
  let some (constructorParameters, constructorBody) := constructor.type.stripPis numParams
    | throw "installed source constructor parameter telescope is short"
  let some (fields, constructorResult) := constructorBody.stripPis numFields
    | throw "installed source constructor field telescope is short"
  let some (coverageParameters, .forallE subjectType
      (.forallE (.sort .zero) (.forallE continuation (.bvar 1) continuationBinder)
        propositionBinder) subjectBinder) := theoremHeader.type.stripPis site.owner.numParams
    | throw "installed coverage theorem lacks the exact Church statement"
  let some (coverageFields, .forallE equalityType (.bvar propositionIndex) equalityBinder) :=
      continuation.stripPis site.ctor.numFields
    | throw "installed coverage continuation lacks its exact field/equality telescope"
  let data : SourceCoverShapeData := ⟨owner, constructor, theoremHeader, parameters,
    constructorParameters, coverageParameters, fields, coverageFields, constructorResult,
    subjectType, equalityType, level, subjectBinder, propositionBinder, continuationBinder,
    equalityBinder, continuation, propositionIndex⟩
  if ho : coverage.env.find? (sourceName site.ownerName) = some (.indInfo data.owner caps) then
    if hc : coverage.env.find? (sourceName site.ctorName) =
        some (.ctorInfo data.constructor site.owner.numParams site.ctor.numFields) then
      if ht : coverage.env.find? coverage.header.name = some (.thmInfo data.theoremHeader coverage.value) then
        if hs : SourceCoverShape site coverage.header data then
          return ⟨data, caps, ho, hc, ht, hs⟩
        else throw s!"installed coverage fields or identities do not match the original constructor; fieldDomains={decide (data.coverageFields.map Prod.fst = (liftSourceFieldDomains 0 data.fields).map Prod.fst)}; constructorParams={decide (data.constructorParameters.map Prod.fst = data.parameters.map Prod.fst)}; coverageParams={decide (data.coverageParameters.map Prod.fst = data.parameters.map Prod.fst)}; constructorFieldBinders={reprStr (data.fields.map Prod.snd)}; coverageFieldBinders={reprStr (data.coverageFields.map Prod.snd)}"
      else throw "installed coverage theorem body is not its checked original proposal"
    else throw "installed constructor counts differ from the immutable source"
  else throw "installed coverage owner lookup changed"

theorem SourceCoverInstalledShape.owner_member {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) :
    Kernel.ConstantInfo.indInfo receipt.data.owner receipt.ownerCaps ∈ coverage.env.consts :=
  List.mem_of_find?_eq_some receipt.ownerLookup

open Kernel.SetTheory in
/-- The source carrier's universe membership comes from the actual installed
owner and its typed parameter tuple, not from an assumed shape of arbitrary
set-theoretic application. -/
theorem SourceCoverInstalledShape.owner_apply {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V} {result : Kernel.Expr}
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (typed : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters finalρ result) :
    parameters.foldl app (model.cval (sourceName site.ownerName) levels) ∈ˢ
      univ (Kernel.Level.eval levels receipt.data.level) := by
  rcases receipt.shape with ⟨ownerName, _, _, _, _, _, count, _, _, _, _, ownerType, _⟩
  obtain ⟨type, read, member⟩ := typed.model_apply model receipt.owner_member
  rw [ownerType] at typed
  have ⟨resultType, _⟩ := sourceForalls_transfer (targetBinders := receipt.data.parameters)
    (targetBody := Kernel.Expr.sort receipt.data.level) rfl (parameterCount.trans count.symm) typed
  rw [resultType] at read
  cases read
  simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal, ownerName] using member

theorem SourceCoverInstalledShape.constructor_member {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) :
    Kernel.ConstantInfo.ctorInfo receipt.data.constructor site.owner.numParams site.ctor.numFields
      ∈ coverage.env.consts :=
  List.mem_of_find?_eq_some receipt.constructorLookup

theorem SourceCoverInstalledShape.theorem_member {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) :
    Kernel.ConstantInfo.thmInfo receipt.data.theoremHeader coverage.value ∈ coverage.env.consts :=
  List.mem_of_find?_eq_some receipt.theoremLookup

open Kernel.SetTheory in
/-- Typed original field tuples construct actual carrier members in the same
installed model as the coverage theorem. The immutable source constructor name,
not a reverse content alias or an unrelated model witness, determines the value. -/
theorem SourceCoverInstalledShape.constructor_apply {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V} {result : Kernel.Expr}
    (parameters : List V) (fields : SourceFieldValues site V)
    (typed : InstalledTelescope model.cval coverage.env levels ρ receipt.data.constructor.type
      (parameters ++ fields.val) finalρ result) :
    ∃ carrier, Kernel.Denotes model.cval coverage.env levels finalρ result carrier ∧
      originalConstructorValue site model.cval levels parameters fields ∈ˢ carrier := by
  have applied := typed.model_apply model receipt.constructor_member
  have name : receipt.data.constructor.name = sourceName site.ctorName := receipt.shape.2.1
  simpa only [Kernel.ConstantInfo.toConstantVal, Kernel.ConstantInfo.name,
    originalConstructorValue, name] using applied

open Kernel.SetTheory in
/-- Read the receipt's exact Eq syntax at its exact argument frame. This
connects the independently checked syntax to semantic constructor values;
the Eq constant's own denotation remains explicit until extracted from the
actually denoted continuation leaf. -/
theorem SourceCoverInstalledShape.equality_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (fields : SourceFieldValues site V) (subject proposition E : V)
    (eqRead : Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      (.const Kernel.eqName [receipt.data.level]) E) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      receipt.data.equalityType
      (app (app (app E (parameters.foldl app (model.cval (sourceName site.ownerName) levels))) subject)
        (originalConstructorValue site model.cval levels parameters fields)) := by
  rcases receipt.shape with ⟨ownerName, constructorName, _, levelNames, _, _, _, _, _, _, _,
    _, _, _, _, equation, _, _, _⟩
  let base := pushArguments ρ parameters
  let frame := pushArguments (pushArguments base [subject, proposition]) fields.val
  have parameterSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars site.owner.numParams (site.ctor.numFields + 2)) parameters := by
    have read := sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
      (levels := levels) ρ parameters ([subject, proposition] ++ fields.val)
    simpa only [pushArguments_append, List.length_append, List.length_cons,
      List.length_nil, parameterCount, fields.property, Nat.add_comm 2, Nat.zero_add,
      Nat.reduceAdd, base, frame] using read
  have fieldSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars site.ctor.numFields 0) fields.val := by
    have read := sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
      (levels := levels) (pushArguments base [subject, proposition]) fields.val []
    simpa only [List.length_nil, pushArguments, fields.property, frame] using read
  have ownerRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) receipt.ownerLookup
  have constructorRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) receipt.constructorLookup
  simp only [Kernel.ConstantInfo.toConstantVal] at ownerRead constructorRead
  rw [← ownerName] at ownerRead
  rw [← constructorName, ← levelNames] at constructorRead
  have ownerApp := denotes_mkAppN ownerRead parameterSpine
  have constructorApp := denotes_mkAppN constructorRead (parameterSpine.append fieldSpine)
  have subjectRead : Kernel.Denotes model.cval coverage.env levels frame
      (.bvar (site.ctor.numFields + 1)) subject := by
    have slot : frame (site.ctor.numFields + 1) = subject := by
      have above := pushArguments_above fields.val (pushArguments base [subject, proposition]) 1
      simpa only [frame, fields.property, pushArguments, Kernel.push] using above
    rw [← slot]
    exact .bvar
  rw [equation]
  have read := Kernel.Denotes.app (Kernel.Denotes.app (Kernel.Denotes.app eqRead ownerApp)
    subjectRead) constructorApp
  simpa only [Kernel.Expr.mkAppN, originalConstructorValue, ownerName, constructorName,
    base, frame] using read

open Kernel.SetTheory in
/-- Extract the Eq instance from the actual leaf denotation and identify its
value with the original carrier/subject/constructor equation. No separate
assumption that Eq resolves in the source environment is needed. -/
theorem SourceCoverInstalledShape.equality_value {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (fields : SourceFieldValues site V) (subject proposition value : V)
    (read : Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      receipt.data.equalityType value) :
    ∃ E, Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      (.const Kernel.eqName [receipt.data.level]) E ∧
      value = app (app (app E (parameters.foldl app (model.cval (sourceName site.ownerName) levels))) subject)
        (originalConstructorValue site model.cval levels parameters fields) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, equation, _, _, _⟩
  have expanded := read
  rw [equation] at expanded
  obtain ⟨E, eqRead⟩ := denotes_mkAppN_head _ expanded
  exact ⟨E, eqRead, Kernel.Denotes_functional read
    (receipt.equality_denotes model levels ρ parameters parameterCount fields subject proposition E eqRead)⟩

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.carrier_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams) (extras : List V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) extras)
      (Kernel.Expr.mkAppN (.const receipt.data.owner.name
        (receipt.data.owner.levelParams.map Kernel.Level.param))
        (sourceParameterVars site.owner.numParams extras.length))
      (parameters.foldl app (model.cval (sourceName site.ownerName) levels)) := by
  have head := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := pushArguments (pushArguments ρ parameters) extras) receipt.ownerLookup
  have spine := sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
    (levels := levels) ρ parameters extras
  rw [parameterCount] at spine
  have result := denotes_mkAppN head spine
  have ownerName := receipt.shape.1
  simpa only [Kernel.ConstantInfo.toConstantVal, ownerName] using result

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.constructor_result_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (fields : SourceFieldValues site V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.constructorResult
      (parameters.foldl app (model.cval (sourceName site.ownerName) levels)) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, resultType, _⟩
  rw [resultType]
  simpa only [fields.property] using
    receipt.carrier_denotes model levels ρ parameters parameterCount fields.val

/-- Original constructor field typing, read from the independently installed
source constructor. This predicate does not mention the lowered projection. -/
def SourceCoverValidFields {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) (parameters : List V)
    (fields : SourceFieldValues site V) : Prop :=
    InstalledTelescope model.cval coverage.env levels (pushArguments ρ parameters)
      (sourceForalls receipt.data.fields receipt.data.constructorResult) fields.val
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.constructorResult

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.constructor_fields {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level)) :
    ∃ type, Kernel.Denotes model.cval coverage.env levels (pushArguments ρ parameters)
      (sourceForalls receipt.data.fields receipt.data.constructorResult) type ∧
      parameters.foldl app (model.cval (sourceName site.ctorName) levels) ∈ˢ type := by
  rcases receipt.shape with ⟨_, constructorName, _, _, _, _, count, _, domains, _, _,
    ownerType, constructorType, _⟩
  rw [ownerType] at parameterTyping
  have transferred := (sourceForalls_transfer (targetBody := sourceForalls receipt.data.fields
    receipt.data.constructorResult) domains.symm (parameterCount.trans count.symm) parameterTyping).2
  rw [← constructorType] at transferred
  have result := transferred.model_apply model receipt.constructor_member
  simpa only [Kernel.ConstantInfo.toConstantVal, Kernel.ConstantInfo.name, constructorName] using result

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.constructor_typed {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (fields : SourceFieldValues site V)
    (valid : SourceCoverValidFields receipt model levels ρ parameters fields) :
    originalConstructorValue site model.cval levels parameters fields ∈ˢ
      parameters.foldl app (model.cval (sourceName site.ownerName) levels) := by
  obtain ⟨type, read, member⟩ := receipt.constructor_fields model levels ρ parameters parameterCount parameterTyping
  obtain ⟨result, readResult, memberResult⟩ := valid.apply read member
  obtain rfl := Kernel.Denotes_functional readResult
    (receipt.constructor_result_denotes model levels ρ parameters parameterCount fields)
  simpa only [originalConstructorValue, List.foldl_append] using memberResult

open Kernel.SetTheory in
/-- Specialize the actually admitted coverage theorem to typed original
parameters and an arbitrary member of the original carrier. -/
theorem SourceCoverInstalledShape.church {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName site.ownerName) levels)) :
    ∃ type, Kernel.Denotes model.cval coverage.env levels
      (Kernel.push subject (pushArguments ρ parameters))
      (.forallE (.sort .zero) (.forallE receipt.data.continuation (.bvar 1)
        receipt.data.continuationBinder) receipt.data.propositionBinder) type ∧
      app (parameters.foldl app (model.cval coverage.header.name levels)) subject ∈ˢ type := by
  rcases receipt.shape with ⟨_, _, theoremName, _, _, _, count, _, _, domains, _,
    ownerType, _, _, subjectType, _, _, _, theoremType⟩
  rw [ownerType] at parameterTyping
  have transferred := (sourceForalls_transfer
    (targetBody := .forallE receipt.data.subjectType
      (.forallE (.sort .zero) (.forallE receipt.data.continuation (.bvar 1)
        receipt.data.continuationBinder) receipt.data.propositionBinder) receipt.data.subjectBinder)
    domains.symm (parameterCount.trans count.symm) parameterTyping).2
  rw [← theoremType] at transferred
  obtain ⟨type, read, member⟩ := transferred.model_apply model receipt.theorem_member
  have subjectRead := receipt.carrier_denotes model levels ρ parameters parameterCount []
  simp only [List.length_nil, pushArguments] at subjectRead
  rw [← subjectType] at subjectRead
  have specialized := installed_forall_elim read member subjectRead subjectTyped
  simpa only [Kernel.ConstantInfo.toConstantVal, Kernel.ConstantInfo.name, theoremName] using specialized

open Kernel.SetTheory in
/-- The independently admitted coverage theorem covers every member of the
original source carrier, with fields typed by its actual original constructor.
This discharges the semantic coverage premise for a checked installed receipt;
it does not assert full-domain receipt production or projection computation. -/
theorem SourceCoverInstalledShape.semantic_cover {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName site.ownerName) levels)) :
    SemanticConstructorCover (SourceCoverValidFields receipt model levels ρ parameters)
      (originalConstructorValue site model.cval levels parameters) subject := by
  intro proposition propositionTyped continuation
  obtain ⟨churchType, churchRead, churchMember⟩ :=
    receipt.church model levels ρ parameters parameterCount parameterTyping subject subjectTyped
  apply installed_church_elim churchRead churchMember proposition propositionTyped
  obtain ⟨continuationType, continuationRead⟩ := denotes_church_continuation churchRead propositionTyped
  refine ⟨continuationType, continuationRead, ?_⟩
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, fieldCount, _, _, domains,
    _, _, _, _, _, propositionIndex, continuationShape, _⟩
  have coverageCount : receipt.data.coverageFields.length = site.ctor.numFields := by
    have lengths := congrArg List.length domains
    simpa only [List.length_map, liftSourceFieldDomains_length, fieldCount] using lengths
  have fieldsRead := continuationRead
  rw [continuationShape] at fieldsRead
  apply (sourceForalls_binders receipt.data.coverageFields _).inhabited fieldsRead
  intro arguments finalρ result length typed
  let fields : SourceFieldValues site V := ⟨arguments, length.trans coverageCount⟩
  obtain ⟨constructorType, constructorRead, _⟩ :=
    receipt.constructor_fields model levels ρ parameters parameterCount parameterTyping
  have originalLength : arguments.length = receipt.data.fields.length :=
    (length.trans coverageCount).trans fieldCount.symm
  obtain ⟨originalFinal, originalTyped, _⟩ := sourceForalls_reflect_lift domains originalLength
    constructorRead typed (valuationLift_two (pushArguments ρ parameters) subject proposition)
  have originalFinalEq := originalTyped.final_valuation
  have valid : SourceCoverValidFields receipt model levels ρ parameters fields := by
    rw [originalFinalEq] at originalTyped
    exact originalTyped
  have resultEq := (sourceForalls_transfer (targetBinders := receipt.data.coverageFields)
    (targetBody := Kernel.Expr.forallE receipt.data.equalityType (.bvar receipt.data.propositionIndex)
      receipt.data.equalityBinder) rfl length typed).1
  have finalEq := typed.final_valuation
  obtain ⟨leafType, leafRead⟩ := typed.read fieldsRead
  rw [resultEq, finalEq, propositionIndex] at leafRead
  obtain ⟨equalityType, equalityRead⟩ := denotes_forall_domain leafRead
  obtain ⟨E, eqRead, equalityValue⟩ := receipt.equality_value model levels ρ parameters
    parameterCount fields subject proposition equalityType equalityRead
  rw [equalityValue] at equalityRead
  have carrierTyped := receipt.owner_apply model parameters parameterCount parameterTyping
  have constructorTyped := receipt.constructor_typed model levels ρ parameters parameterCount
    parameterTyping fields valid
  have slot : (pushArguments (Kernel.push proposition (Kernel.push subject (pushArguments ρ parameters)))
      arguments) site.ctor.numFields = proposition := by
    have above := pushArguments_above arguments
      (Kernel.push proposition (Kernel.push subject (pushArguments ρ parameters))) 0
    simpa only [length.trans coverageCount, Nat.add_zero, Kernel.push] using above
  have inhabited := installed_eq_implication_inhabited model eqRead carrierTyped subjectTyped
    constructorTyped equalityRead leafRead slot (fun equal => continuation fields valid equal.symm)
  refine ⟨leafType, ?_, inhabited⟩
  simpa only [resultEq, finalEq, propositionIndex] using leafRead

open Kernel.SetTheory in
/-- Arbitrary carrier values have original-constructor presentations, with
the exact dependent field typing derived above. This is the set-level
coverage conclusion of the admitted Church certificate. -/
theorem SourceCoverInstalledShape.constructor_presentation {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName site.ownerName) levels)) :
    ∃ fields : SourceFieldValues site V,
      SourceCoverValidFields receipt model levels ρ parameters fields ∧
      originalConstructorValue site model.cval levels parameters fields = subject :=
  (semanticConstructorCover_iff _ _ subject).mp
    (receipt.semantic_cover model levels ρ parameters parameterCount parameterTyping subject subjectTyped)

/-- Full installed projection and equation data. Raw source provenance remains
in `SourceProjectionReceipt`; these fields retain the actual annotated types. -/
structure SourceProjectionInstalledData where
  projection : Kernel.ConstantVal
  value : Kernel.Expr
  hint : Kernel.ReducibilityHint
  rawEquation : Kernel.ConstantVal
  equation : Kernel.ConstantVal
  proof : Kernel.Expr
  parameters : List (Kernel.Expr × Kernel.BinderMeta)
  fields : List (Kernel.Expr × Kernel.BinderMeta)
  carrier : Kernel.Expr
  left : Kernel.Expr
  right : Kernel.Expr

def SourceProjectionInstalledShape {source : Source} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    (constructor : SourceCoverShapeData) (data : SourceProjectionInstalledData) : Prop :=
  equation = .thmDecl data.rawEquation data.proof ∧
  data.rawEquation.name = projection.header.name.str "_source_constructor_equation" ∧
  data.equation.name = data.rawEquation.name ∧
  data.equation.levelParams = data.rawEquation.levelParams ∧
  data.rawEquation.levelParams = projection.header.levelParams ∧
  data.projection.name = projection.header.name ∧
  data.projection.levelParams = projection.header.levelParams ∧
  data.hint = projection.hint ∧
  constructor.constructor.levelParams = data.projection.levelParams ∧
  data.parameters.map Prod.fst = constructor.parameters.map Prod.fst ∧
  data.fields.map Prod.fst = constructor.fields.map Prod.fst ∧
  data.equation.type = sourceForalls data.parameters (sourceForalls data.fields
    (.app (.app (.app (.const Kernel.eqName [projection.level]) data.carrier) data.left) data.right)) ∧
  data.left = Kernel.Expr.mkAppN
    (.const data.projection.name (data.projection.levelParams.map Kernel.Level.param))
    (sourceParameterVars projection.site.owner.numParams projection.site.ctor.numFields ++
      [Kernel.Expr.mkAppN
        (.const constructor.constructor.name (data.projection.levelParams.map Kernel.Level.param))
        (sourceParameterVars projection.site.owner.numParams projection.site.ctor.numFields ++
          sourceParameterVars projection.site.ctor.numFields 0)]) ∧
  data.right = .bvar (projection.site.ctor.numFields - 1 - projection.site.field)

instance {source : Source} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    (constructor : SourceCoverShapeData) (data : SourceProjectionInstalledData) :
    Decidable (SourceProjectionInstalledShape projection constructor data) := by
  unfold SourceProjectionInstalledShape
  infer_instance

/-- Links an immutable original projection, its submitted equation and the
actual independently installed annotated entries. No equality between raw and
annotated bodies is assumed. The full constructor/owner receipt stays attached. -/
structure SourceProjectionInstalled {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    {coverage : SourceConstructorCoverChecked installed projection.site}
    (constructor : SourceCoverInstalledShape coverage) where
  data : SourceProjectionInstalledData
  replacement_present : replacement ∈ installed.declarations
  equation_present : equation ∈ installed.declarations
  projectionLookup : coverage.env.find? projection.header.name =
    some (.defnInfo data.projection data.value data.hint)
  equationLookup : coverage.env.find? data.rawEquation.name =
    some (.thmInfo data.equation data.proof)
  shape : SourceProjectionInstalledShape projection constructor.data data

def checkSourceProjectionInstalled {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    {coverage : SourceConstructorCoverChecked installed projection.site}
    (constructor : SourceCoverInstalledShape coverage) :
    Except String (SourceProjectionInstalled projection constructor) := do
  let .thmDecl rawEquation proof := equation
    | throw "source projection equation is not a submitted theorem"
  let some (.defnInfo projectionHeader value hint) ← pure (coverage.env.find? projection.header.name)
    | throw "installed source projection is missing or has wrong kind"
  let some (.thmInfo equationHeader _) ← pure (coverage.env.find? rawEquation.name)
    | throw "installed source projection equation is missing or has wrong kind"
  let some (parameters, body) := equationHeader.type.stripPis projection.site.owner.numParams
    | throw "installed source projection equation parameter telescope is short"
  let some (fields, .app (.app (.app (.const _ _) carrier) left) right) :=
      body.stripPis projection.site.ctor.numFields
    | throw "installed source projection equation lacks its exact field/equality telescope"
  let data : SourceProjectionInstalledData :=
    ⟨projectionHeader, value, hint, rawEquation, equationHeader, proof, parameters, fields, carrier, left, right⟩
  if hr : replacement ∈ installed.declarations then
    if he : equation ∈ installed.declarations then
      if hp : coverage.env.find? projection.header.name =
          some (.defnInfo data.projection data.value data.hint) then
        if hq : coverage.env.find? data.rawEquation.name = some (.thmInfo data.equation data.proof) then
          if hs : SourceProjectionInstalledShape projection constructor.data data then
            return ⟨data, hr, he, hp, hq, hs⟩
          else throw "installed source projection equation differs from its original field/constructor shape"
        else throw "installed source projection equation proof differs from the submitted proof"
      else throw "installed source projection lookup changed"
    else throw "source projection equation is absent from the independently checked stream"
  else throw "source projection replacement is absent from the independently checked stream"

open Kernel.SetTheory in
/-- The checked equation uses exactly the original dependent constructor
domains, while retaining its own actual enclosing binder regimes. -/
theorem SourceProjectionInstalled.typed_equation {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (fields : SourceFieldValues projection.site V)
    (valid : SourceCoverValidFields constructor model levels ρ parameters fields) :
    InstalledTelescope model.cval coverage.env levels ρ receipt.data.equation.type
      (parameters ++ fields.val) (pushArguments (pushArguments ρ parameters) fields.val)
      (.app (.app (.app (.const Kernel.eqName [projection.level]) receipt.data.carrier)
        receipt.data.left) receipt.data.right) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, parameterDomains, fieldDomains, equationType, _, _⟩
  rcases constructor.shape with ⟨_, _, _, _, _, _, parameterLength, fieldLength, _, _, _, ownerType, _⟩
  rw [ownerType] at parameterTyping
  have parameterTuple := (sourceForalls_transfer (targetBody := sourceForalls receipt.data.fields
    (.app (.app (.app (.const Kernel.eqName [projection.level]) receipt.data.carrier)
      receipt.data.left) receipt.data.right)) parameterDomains.symm
      (parameterCount.trans parameterLength.symm) parameterTyping).2
  have fieldTuple := (sourceForalls_transfer (targetBody :=
    .app (.app (.app (.const Kernel.eqName [projection.level]) receipt.data.carrier)
      receipt.data.left) receipt.data.right) fieldDomains.symm
      (fields.property.trans fieldLength.symm) valid).2
  rw [equationType]
  exact parameterTuple.append fieldTuple

open Kernel.SetTheory in
theorem SourceProjectionInstalled.left_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (fields : SourceFieldValues projection.site V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.left
      (app (parameters.foldl app (model.cval projection.header.name levels))
        (originalConstructorValue projection.site model.cval levels parameters fields)) := by
  rcases receipt.shape with ⟨_, _, _, _, _, projectionName, _, _, levelNames, _, _, _, leftShape, _⟩
  let frame := pushArguments (pushArguments ρ parameters) fields.val
  have parameterSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars projection.site.owner.numParams projection.site.ctor.numFields) parameters := by
    simpa only [parameterCount, fields.property, frame] using
      (sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
        (levels := levels) ρ parameters fields.val)
  have fieldSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars projection.site.ctor.numFields 0) fields.val := by
    simpa only [List.length_nil, pushArguments, fields.property, frame] using
      (sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
        (levels := levels) (pushArguments ρ parameters) fields.val [])
  have projectionRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) receipt.projectionLookup
  have constructorRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) constructor.constructorLookup
  simp only [Kernel.ConstantInfo.toConstantVal] at projectionRead constructorRead
  rw [← projectionName] at projectionRead
  have constructorName := constructor.shape.2.1
  rw [← constructorName, levelNames] at constructorRead
  have constructorApp := denotes_mkAppN constructorRead (parameterSpine.append fieldSpine)
  have application := Kernel.Denotes.app (denotes_mkAppN projectionRead parameterSpine) constructorApp
  rw [leftShape]
  simpa only [Kernel.Expr.mkAppN_append_one, List.foldl_append, List.foldl_cons, List.foldl_nil,
    originalConstructorValue, projectionName, constructorName, frame] using application

theorem SourceProjectionInstalled.right_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) (parameters : List V)
    (fields : SourceFieldValues projection.site V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.right
      (originalSelectedField projection.site fields) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rightShape⟩
  rw [rightShape]
  have inside : projection.site.field < fields.val.length := by
    rw [fields.property]
    exact projection.site.shape.2.2.2.2.2
  have slot := pushArguments_get fields.val (pushArguments ρ parameters) projection.site.field inside
  rw [fields.property] at slot
  unfold originalSelectedField
  rw [← slot]
  exact .bvar

open Kernel.SetTheory in
/-- Actual semantic constructor computation, obtained from the independently
admitted equation and its installed grading. The equality is for all typed
original dependent fields, not merely closed fixtures or syntactic reduction. -/
theorem SourceProjectionInstalled.constructor_computation {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (fields : SourceFieldValues projection.site V)
    (valid : SourceCoverValidFields constructor strong.public levels ρ parameters fields) :
    app (parameters.foldl app (strong.public.cval projection.header.name levels))
      (originalConstructorValue projection.site strong.public.cval levels parameters fields) =
        originalSelectedField projection.site fields :=
  strong.theorem_eq receipt.data.equation receipt.data.proof
    (List.mem_of_find?_eq_some receipt.equationLookup)
    (receipt.typed_equation strong.public levels ρ parameters parameterCount parameterTyping fields valid)
    (receipt.left_denotes strong.public levels ρ parameters parameterCount fields)
    (receipt.right_denotes strong.public levels ρ parameters fields)

open Kernel.SetTheory in
/-- Arbitrary original carrier members, with both semantic coverage and
constructor computation discharged by their actual installed certificates. -/
theorem SourceProjectionInstalled.arbitrary_value {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app
      (strong.public.cval (sourceName projection.site.ownerName) levels)) :
    OriginalProjectionValue projection.site strong.public.cval levels parameters
      (SourceCoverValidFields constructor strong.public levels ρ parameters) subject
      (app (parameters.foldl app (strong.public.cval projection.header.name levels)) subject) ∧
    ∀ value, OriginalProjectionValue projection.site strong.public.cval levels parameters
      (SourceCoverValidFields constructor strong.public levels ρ parameters) subject value →
      value = app (parameters.foldl app (strong.public.cval projection.header.name levels)) subject :=
  original_projection_extensional projection.site strong.public.cval levels parameters
    (SourceCoverValidFields constructor strong.public levels ρ parameters)
    (parameters.foldl app (strong.public.cval (sourceName projection.site.ownerName) levels))
    (parameters.foldl app (strong.public.cval projection.header.name levels))
    (constructor.semantic_cover strong.public levels ρ parameters parameterCount parameterTyping)
    (receipt.constructor_computation strong levels ρ parameters parameterCount parameterTyping)
    subject subjectTyped

/-- The semantic value used in `arbitrary_value` is the denotation of the
actual installed annotated definition body. This is a source-owned lowering
pull-back, not an equality between the raw nested Kernel projection fallback
and the normalized term. Original syntax/provenance stays in `projection`. -/
theorem SourceProjectionInstalled.definition_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    Kernel.Denotes strong.public.cval coverage.env levels ρ receipt.data.value
      (strong.public.cval projection.header.name levels) := by
  have projectionName := receipt.shape.2.2.2.2.2.1
  have read := strong.definition_values receipt.data.projection receipt.data.value receipt.data.hint
    (List.mem_of_find?_eq_some receipt.projectionLookup) levels ρ
  simpa only [StrongInstalledModel.public, projectionName] using read

/-- The precise raw replacement-to-installed annotation calls behind the
projection value theorem. This is the source installation, including the
coverage extension, not target `projRewrite` or an unrelated annotation run. -/
theorem SourceProjectionInstalled.annotation
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    (ordinary : (Kernel.natOpNames.contains projection.header.name ||
      Kernel.natDivModNames.contains projection.header.name) = false) :
    receipt.data.projection = { projection.header with type := receipt.data.projection.type } ∧
    receipt.data.hint = projection.hint ∧
    ∃ before : Kernel.FEnv, ∃ initial afterType beforeValue afterValue : Kernel.Cached.CState,
      (Kernel.Cached.coreKnotI .verified before Kernel.checkFuel).annotate 0
        projection.header.type initial.flushed = .ok (receipt.data.projection.type, afterType) ∧
      Kernel.Cached.annotConstantValC .verified before projection.header initial.flushed =
        .ok ((receipt.data.projection, receipt.data.projection.type), beforeValue) ∧
      (Kernel.Cached.coreKnotI .verified before Kernel.checkFuel).annotate 0
        projection.value beforeValue = .ok (receipt.data.value, afterValue) := by
  have present := receipt.replacement_present
  rw [projection.replacement_decl] at present
  have inExtended : Kernel.Declaration.defnDecl projection.header projection.value projection.hint ∈
      (installed.declarations ++ [Kernel.Declaration.thmDecl coverage.header coverage.value]).toArray := by
    simpa using List.mem_append_left [Kernel.Declaration.thmDecl coverage.header coverage.value] present
  exact (AnnotationTrace.definition_checked ordinary inExtended coverage.checked).exact
    (AnnotationTrace.checked_unique_names coverage.checked) receipt.projectionLookup

/-- The unconditional version also records primitive checking paths should
an original source identity select one. No domain exclusion is needed. -/
theorem SourceProjectionInstalled.annotation_all
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) :
    receipt.data.projection = { projection.header with type := receipt.data.projection.type } ∧
    receipt.data.hint = projection.hint ∧
    ∃ before : Kernel.FEnv, ∃ initial : Kernel.Cached.CState,
      AnnotationTrace.ValueAnnotationCalls .verified before projection.header projection.value initial
        receipt.data.projection.type receipt.data.value := by
  have present := receipt.replacement_present
  rw [projection.replacement_decl] at present
  have inExtended : Kernel.Declaration.defnDecl projection.header projection.value projection.hint ∈
      (installed.declarations ++ [Kernel.Declaration.thmDecl coverage.header coverage.value]).toArray := by
    simpa using List.mem_append_left [Kernel.Declaration.thmDecl coverage.header coverage.value] present
  exact (AnnotationTrace.definition_all_checked inExtended coverage.checked).exact
    (AnnotationTrace.checked_unique_names coverage.checked) receipt.projectionLookup

/-- Actual projection function telescope. Its regime is read from the
installed binder; agreement with a separately annotated endpoint is not
silently included in this receipt. -/
structure SourceProjectionFunctionData where
  parameters : List (Kernel.Expr × Kernel.BinderMeta)
  result : Kernel.Expr
  binder : Kernel.BinderMeta

def SourceProjectionFunctionShape {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    (data : SourceProjectionFunctionData) : Prop :=
  data.parameters.map Prod.fst = constructor.data.parameters.map Prod.fst ∧
  receipt.data.projection.type = sourceForalls data.parameters
    (.forallE (Kernel.Expr.mkAppN (.const constructor.data.owner.name
      (constructor.data.owner.levelParams.map Kernel.Level.param))
      (sourceParameterVars projection.site.owner.numParams 0)) data.result data.binder)

instance {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    (data : SourceProjectionFunctionData) : Decidable (SourceProjectionFunctionShape receipt data) := by
  unfold SourceProjectionFunctionShape
  infer_instance

structure SourceProjectionFunction {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) where
  data : SourceProjectionFunctionData
  shape : SourceProjectionFunctionShape receipt data

def checkSourceProjectionFunction {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) :
    Except String (SourceProjectionFunction receipt) := do
  let some (parameters, .forallE _ result binder) :=
      receipt.data.projection.type.stripPis projection.site.owner.numParams
    | throw "installed source projection function has no exact subject telescope"
  let data : SourceProjectionFunctionData := ⟨parameters, result, binder⟩
  if checked : SourceProjectionFunctionShape receipt data then return ⟨data, checked⟩
  else throw "installed source projection function domain differs from original carrier"

open Kernel.SetTheory in
/-- Both the function membership and codomain reading come from the actual
installed type after its typed original parameters are supplied. -/
theorem SourceProjectionFunction.typed {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level)) :
    ∃ codomain : V → V,
      parameters.foldl app (model.cval projection.header.name levels) ∈ˢ
        Kernel.SetModel.piR (Kernel.regime levels function.data.binder.pw)
          (parameters.foldl app (model.cval (sourceName projection.site.ownerName) levels)) codomain ∧
      ∀ subject, subject ∈ˢ parameters.foldl app
        (model.cval (sourceName projection.site.ownerName) levels) →
        Kernel.Denotes model.cval coverage.env levels (Kernel.push subject (pushArguments ρ parameters))
          function.data.result (codomain subject) := by
  rcases constructor.shape with ⟨_, _, _, _, _, _, parameterLength, _, _, _, _, ownerType, _⟩
  rw [ownerType] at parameterTyping
  have transferred := (sourceForalls_transfer (targetBody := .forallE
    (Kernel.Expr.mkAppN (.const constructor.data.owner.name
      (constructor.data.owner.levelParams.map Kernel.Level.param))
      (sourceParameterVars projection.site.owner.numParams 0)) function.data.result function.data.binder)
    function.shape.1.symm
    (parameterCount.trans parameterLength.symm) parameterTyping).2
  rw [← function.shape.2] at transferred
  obtain ⟨type, read, member⟩ := transferred.model_apply model
    (List.mem_of_find?_eq_some receipt.projectionLookup)
  have domainRead := constructor.carrier_denotes model levels ρ parameters parameterCount []
  simp only [List.length_nil, pushArguments] at domainRead
  cases read with
  | pi actualDomain bodyRead regimeTyped =>
    obtain rfl := Kernel.Denotes_functional actualDomain domainRead
    refine ⟨_, ?_, bodyRead⟩
    have projectionName := receipt.shape.2.2.2.2.2.1
    simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal, projectionName] using member

open Kernel.SetTheory in
/-- Full function-value equality with the independent original-field selector.
The exact installed regime is retained. Independent source/target annotation
agreement remains a separate obligation of the wider semantic simulation. -/
theorem SourceProjectionFunction.value_eq {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level)) :
    parameters.foldl app (strong.public.cval projection.header.name levels) =
      Kernel.SetModel.lamR (Kernel.regime levels function.data.binder.pw)
        (parameters.foldl app (strong.public.cval (sourceName projection.site.ownerName) levels))
        (originalProjectionSelection projection.site strong.public.cval levels parameters
          (SourceCoverValidFields constructor strong.public levels ρ parameters)) := by
  obtain ⟨codomain, typed, _⟩ := function.typed strong.public levels ρ parameters parameterCount parameterTyping
  rw [← Kernel.SetModel.lamR_eta typed]
  apply Kernel.SetModel.lamR_congr
  intro subject subjectTyped
  have presented := constructor.constructor_presentation strong.public levels ρ parameters
    parameterCount parameterTyping subject subjectTyped
  have selected := originalProjectionSelection_reading projection.site strong.public.cval levels
    parameters (SourceCoverValidFields constructor strong.public levels ρ parameters) subject presented
  exact ((receipt.arbitrary_value strong levels ρ parameters parameterCount parameterTyping
    subject subjectTyped).2 _ selected).symm

/-- Pull back the actual annotated definition body, including a denoting
parameter application spine, to the source-only function interpretation.
This avoids replacing a body equation with a mere name/type coincidence. -/
theorem SourceProjectionFunction.body_application_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (expressions : List Kernel.Expr)
    (parameterRead : DenotesSpine strong.public.cval coverage.env levels ρ expressions parameters) :
    Kernel.Denotes strong.public.cval coverage.env levels ρ
      (Kernel.Expr.mkAppN receipt.data.value expressions)
      (Kernel.SetModel.lamR (Kernel.regime levels function.data.binder.pw)
        (parameters.foldl Kernel.SetTheory.app (strong.public.cval (sourceName projection.site.ownerName) levels))
        (originalProjectionSelection projection.site strong.public.cval levels parameters
          (SourceCoverValidFields constructor strong.public levels ρ parameters))) := by
  have read := denotes_mkAppN (receipt.definition_denotes strong levels ρ) parameterRead
  rw [function.value_eq strong levels ρ parameters parameterCount parameterTyping] at read
  exact read

/-- Value denotation for the actually installed normalized definitions.
Original-source value correspondence is a separate semantic pull-back. -/
theorem SourceNormalizedInstallation.has_model_values (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    ∃ model : Kernel.Model V installed.env, ∀ header value hint,
      Kernel.ConstantInfo.defnInfo header value hint ∈ installed.env.consts →
        ∀ φ ρ, Kernel.Denotes model.cval installed.env φ ρ value (model.cval header.name φ) :=
  Kernel.Cached.checkDecls_model_defn_values V [] installed.declarations.toArray
    installed.env installed.checked

theorem SourceProjectionNormalization.member {source : Source} {state input output}
    (receipt : SourceProjectionNormalization source state input output)
    {declaration : Kernel.Declaration} (present : declaration ∈ input) :
    declaration ∈ output ∨ ∃ prior replacement equation,
      proposeSourceProjection source prior declaration = .ok (some (replacement, equation)) ∧
      Nonempty (SourceProjectionReceipt source declaration replacement equation) ∧
      replacement ∈ output ∧ equation ∈ output := by
  induction receipt with
  | nil => simp at present
  | @unchanged state original rest output hp tail ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact .inl (by simp)
    · rcases ih present with same | ⟨prior, replacement, equation, hp, association, hr, he⟩
      · exact .inl (List.mem_cons_of_mem _ same)
      · exact .inr ⟨prior, replacement, equation, hp, association,
          List.mem_cons_of_mem _ hr, List.mem_cons_of_mem _ he⟩
  | @lowered state original rest replacement equation output hp association fresh tail ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact .inr ⟨state, replacement, equation, hp, ⟨association⟩, by simp, by simp⟩
    · rcases ih present with same | ⟨prior, next, law, hp, association, hr, he⟩
      · exact .inl (by simp only [List.mem_cons]; exact .inr (.inr same))
      · exact .inr ⟨prior, next, law, hp, association, by simp only [List.mem_cons]; exact .inr (.inr hr),
          by simp only [List.mem_cons]; exact .inr (.inr he)⟩

/-- Every original source entry is retained with its exact raw export,
then associated with either an unchanged checked declaration or the exact
source-owned replacement and checked equation. This does not substitute
the replacement for the original source expression in a semantic theorem. -/
theorem SourceNormalizedInstallation.member {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧ entry ∈ readerEntries declaration ∧
      (declaration ∈ installed.declarations ∨ ∃ prior replacement equation,
        proposeSourceProjection source prior declaration = .ok (some (replacement, equation)) ∧
        Nonempty (SourceProjectionReceipt source declaration replacement equation) ∧
        replacement ∈ installed.declarations ∧ equation ∈ installed.declarations) := by
  have matched := installed.original_members ci present
  cases he : exportSourceEntry ci with
  | error reason => simp [SourceEntryMatches, he] at matched
  | ok entry =>
    have hm : entry ∈ installed.modelProposal.declarations.toList.flatMap readerEntries := by
      simpa only [SourceEntryMatches, he, streamEntries] using matched
    obtain ⟨declaration, hd, hm⟩ := List.mem_flatMap.mp hm
    exact ⟨entry, declaration, rfl, hm, installed.normalization.member hd⟩

structure ArtifactInput where
  limits : Limits
  records : Records
  blobs : Kernel.Ingress.Blobs
  hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint := fun _ => none

structure Input extends ArtifactInput where
  source : Source
  roots : List Lean.Name
  map : SourceMap

/-- Validate host-supplied key widths before admission's hash-table lookups.
This does not assert that a key hashes its payload; admission treats keys as
opaque identities. Wire-embedded references are checked by the decoder. -/
def ArtifactKeysValid (input : ArtifactInput) : Prop :=
  (∀ row ∈ input.records, row.1.hash.size = 32) ∧
  (∀ row ∈ input.blobs, row.1.hash.size = 32)

instance (input : ArtifactInput) : Decidable (ArtifactKeysValid input) :=
  inferInstanceAs (Decidable (
    (∀ row ∈ input.records, row.1.hash.size = 32) ∧
    (∀ row ∈ input.blobs, row.1.hash.size = 32)))

/-- Resolve actual record references and names, rather than comparing a
producer's display label or allowing a fabricated member address. -/
def NameAgrees (cx : ExportContext) (n : Lean.Name) (target : Kernel.Name) : Prop :=
  match cx.name n with
  | .error _ => False
  | .ok actual => actual = target

instance (cx : ExportContext) (n : Lean.Name) (target : Kernel.Name) :
    Decidable (NameAgrees cx n target) :=
  match h : cx.name n with
  | .error _ => by simp only [NameAgrees, h]; infer_instance
  | .ok _ => by simp only [NameAgrees, h]; infer_instance

/-- Recursor K/safety flags are not retained in the reader's installed-rule
placeholder. Check them against the actual source-associated wire member. -/
def sourceRecordFlags (cx : ExportContext) (reader : Ctx) (e : MapEntry) : Bool :=
  match cx.source.find e.source with
  | some (.recInfo rv) =>
    match e.target with
    | .ctor .. => false
    | .member owner index =>
      match reader.store owner with
      | none => false
      | some record =>
        match (recursorMembers record).find? (fun entry => entry.1 == index) with
        | none => false
        | some (_, r) => r.k == rv.k && r.isUnsafe == rv.isUnsafe &&
            r.lvls.toNat == rv.levelParams.length
  | some _ => true
  | none => false

def MapAgrees (cx : ExportContext) (reader : Ctx) : Prop :=
  ∀ e ∈ cx.map,
    resolve reader.store e.record = some e.target ∧
    NameAgrees cx e.source (reader.nameOf e.target) ∧ sourceRecordFlags cx reader e = true

instance (cx : ExportContext) (reader : Ctx) : Decidable (MapAgrees cx reader) :=
  inferInstanceAs (Decidable (∀ e ∈ cx.map,
    resolve reader.store e.record = some e.target ∧
    NameAgrees cx e.source (reader.nameOf e.target) ∧ sourceRecordFlags cx reader e = true))

/-- Precise direct-cone relation. Reader declarations are deliberately kept
separate from the installed `env`: binder annotations/lets may change there. -/
structure AdmittedArtifact (input : ArtifactInput) where
  keys_valid : ArtifactKeysValid input
  env : Kernel.Env
  admitted : checkBytes input.limits input.records input.blobs input.hint = .ok env
  pins : Pins
  pins_valid : defaultPins = .ok pins
  prelude : Prelude
  prelude_valid : builtinPrelude = .ok prelude
  constants : List (Address × Ixon.Constant)
  decoded : decodeRecords input.limits input.records = .ok constants
  declarations : Array Kernel.Declaration
  readerState : State
  detailed_reading : readRecords (streamContext pins prelude constants input.blobs input.hint)
    prelude.state constants.toArray = .ok (readerState, declarations)
  reading : readStream pins prelude constants input.blobs input.hint = .ok declarations

/-- Source correspondence extends one reusable admitted artifact. -/
structure AcceptedAssociation (input : Input) extends AdmittedArtifact input.toArtifactInput where
  domain : DirectDomain input.source input.roots input.map
  map_agrees : MapAgrees ⟨input.source, input.map, pins⟩
    (streamContext pins prelude constants input.blobs input.hint)
  correspondence : SourceCorrespondence ⟨input.source, input.map, pins⟩
    (streamContext pins prelude constants input.blobs input.hint) constants declarations
  block_correspondence : BlockCorrespondence ⟨input.source, input.map, pins⟩ readerState
  definition_groups : DefinitionGroupsCovered ⟨input.source, input.map, pins⟩ constants

inductive Decline where
  | admission (error : Kernel.Admission.Error)
  | unsupported (source : Lean.Name) (feature : String)
  | malformedInput (reason : String)
  | sourceDomain
  | setup (reason : String)
  | decoding (error : ByteError)
  | reading (error : Kernel.Admission.Error)
  | mapMismatch
  | correspondence
  | blockCorrespondence
  | definitionGroupCorrespondence

/-- The runtime checks are the constructors' proof premises, not assumptions
supplied by the caller. Structural equality decisions are kernel-checked. -/
def prepareArtifact (input : ArtifactInput) : Except Decline (AdmittedArtifact input) :=
  if hk : ArtifactKeysValid input then
  match ha : checkBytes input.limits input.records input.blobs input.hint with
  | .error e => .error (.admission e)
  | .ok env =>
      match hp : defaultPins with
      | .error e => .error (.setup e)
      | .ok pins =>
        match hq : builtinPrelude with
        | .error e => .error (.setup e)
        | .ok pre =>
          match hc : decodeRecords input.limits input.records with
          | .error e => .error (.decoding e)
          | .ok constants =>
            match hr : readRecords (streamContext pins pre constants input.blobs input.hint)
                pre.state constants.toArray with
            | .error (e, position) => .error (.reading (.read position e))
            | .ok (state, decls) =>
              have hs : readStream pins pre constants input.blobs input.hint = .ok decls := by
                unfold readStream
                change (match readRecords
                  (streamContext pins pre constants input.blobs input.hint)
                  pre.state constants.toArray with
                  | .ok (_, ds) => Except.ok ds
                  | .error (e, i) => Except.error (Kernel.Admission.Error.read i e)) = .ok decls
                rw [hr]
              .ok ⟨hk, env, ha, pins, hp, pre, hq, constants, hc, decls, state, hr, hs⟩
  else .error (.malformedInput "record and blob keys must be exactly 32 bytes")

def checkAssociation (input : Input) (artifact : AdmittedArtifact input.toArtifactInput) :
    Except Decline (AcceptedAssociation input) :=
  if hd : DirectDomain input.source input.roots input.map then
    match input.source.declarations.findSome? (fun ci =>
        (unsupportedSource ci).map (ci.name, ·)) with
    | some (source, feature) => .error (.unsupported source feature)
    | none =>
    let cx : ExportContext := ⟨input.source, input.map, artifact.pins⟩
    let reader := streamContext artifact.pins artifact.prelude artifact.constants input.blobs input.hint
    if hm : MapAgrees cx reader then
      if hf : SourceCorrespondence cx reader artifact.constants artifact.declarations then
        if hb : BlockCorrespondence cx artifact.readerState then
          if hg : DefinitionGroupsCovered cx artifact.constants then
            .ok ⟨artifact, hd, hm, hf, hb, hg⟩
          else .error .definitionGroupCorrespondence
        else .error .blockCorrespondence
      else .error .correspondence
    else .error .mapMismatch
  else .error .sourceDomain

def checkCompiled (input : Input) : Except Decline (AcceptedAssociation input) := do
  checkAssociation input (← prepareArtifact input.toArtifactInput)

/-- Executable success entails actual admission and every finite source
declaration's independent direct correspondence in the exact reader stream. -/
theorem faithful_sound {input : Input} {accepted : AcceptedAssociation input}
    (_h : checkCompiled input = .ok accepted) :
    checkBytes input.limits input.records input.blobs input.hint = .ok accepted.env ∧
    DirectDomain input.source input.roots input.map ∧
    SourceCorrespondence ⟨input.source, input.map, accepted.pins⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants accepted.declarations ∧
    BlockCorrespondence ⟨input.source, input.map, accepted.pins⟩ accepted.readerState ∧
    DefinitionGroupsCovered ⟨input.source, input.map, accepted.pins⟩ accepted.constants :=
  ⟨accepted.admitted, accepted.domain, accepted.correspondence,
    accepted.block_correspondence, accepted.definition_groups⟩

/-- The existing target model theorem applies to these exact accepted bytes.
This is not yet source semantic pull-back (S). -/
theorem AcceptedAssociation.has_model (V : Type u) [Kernel.SetTheory V]
    {input : Input} (accepted : AcceptedAssociation input) :
    Nonempty (Kernel.Model V accepted.env) :=
  checkBytes_has_model V accepted.admitted

/-- Admission provides installation, independently of source correspondence.
No equality of raw reader types and installed annotated types is asserted. -/
theorem AcceptedAssociation.installed {input : Input} (accepted : AcceptedAssociation input) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      WithinBatch input.limits input.records input.blobs ∧ UniqueKeys input.records input.blobs ∧
      ∃ constants, RecordsRead input.limits input.records constants ∧
        Installed pins pre natPins constants input.blobs input.hint accepted.env :=
  checkBytes_reading accepted.admitted

/-- The installation witness uses these exact decoded constants, pins and
prelude, rather than merely some existentially admitted reading. -/
theorem AdmittedArtifact.installed_exact {input : ArtifactInput} (artifact : AdmittedArtifact input) :
    ∃ natPins, builtinNatOpPins = .ok natPins ∧
      Installed artifact.pins artifact.prelude natPins artifact.constants
        input.blobs input.hint artifact.env := by
  obtain ⟨pins, pre, natPins, hp, hq, hn, hc⟩ := checkBytes_with artifact.admitted
  have hp' : pins = artifact.pins := Except.ok.inj (hp.symm.trans artifact.pins_valid)
  have hq' : pre = artifact.prelude := Except.ok.inj (hq.symm.trans artifact.prelude_valid)
  subst pins
  subst pre
  rw [checkBytesWith_eq] at hc
  cases hf : preflight input.limits input.records input.blobs with
  | error e => simp [hf, bind, Except.bind, Except.mapError] at hc
  | ok u =>
    cases hk : uniqueKeys input.records input.blobs with
    | error e => simp [hf, hk, bind, Except.bind, Except.mapError] at hc
    | ok v =>
      simp only [hf, hk, artifact.decoded, bind, Except.bind, Except.mapError] at hc
      exact ⟨natPins, hn, checkConstantsWith_installed hc⟩

/-- The exact declaration array used by correspondence, behind the actual
prelude, is the array accepted by the certified fold. This binds member-level
reader evidence to admission without replacing it by installation skeletons. -/
theorem AdmittedArtifact.checked_declarations {input : ArtifactInput}
    (artifact : AdmittedArtifact input) :
    ∃ natPins, builtinNatOpPins = .ok natPins ∧
      Kernel.Cached.checkDecls .verified natPins
        (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations) = .ok artifact.env := by
  obtain ⟨pins, pre, natPins, hp, hq, hn, hc⟩ := checkBytes_with artifact.admitted
  have hp' : pins = artifact.pins := Except.ok.inj (hp.symm.trans artifact.pins_valid)
  have hq' : pre = artifact.prelude := Except.ok.inj (hq.symm.trans artifact.prelude_valid)
  subst pins
  subst pre
  rw [checkBytesWith_eq] at hc
  cases hf : preflight input.limits input.records input.blobs with
  | error e => simp [hf, bind, Except.bind, Except.mapError] at hc
  | ok u =>
    cases hk : uniqueKeys input.records input.blobs with
    | error e => simp [hf, hk, bind, Except.bind, Except.mapError] at hc
    | ok v =>
      simp only [hf, hk, artifact.decoded, bind, Except.bind, Except.mapError] at hc
      refine ⟨natPins, hn, ?_⟩
      simp only [checkConstantsWith, artifact.reading, bind, Except.bind] at hc
      cases hcheck : Kernel.Cached.checkDecls .verified natPins
          (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations) with
      | error e => simp [hcheck, Except.mapError] at hc
      | ok result => simpa [hcheck, Except.mapError] using hc

theorem AdmittedArtifact.strong_model (V : Type u) [Kernel.SetTheory V]
    {input : ArtifactInput} (artifact : AdmittedArtifact input) :
    Nonempty (StrongInstalledModel V artifact.env) := by
  obtain ⟨natPins, _, checked⟩ := artifact.checked_declarations
  exact strongInstalledModel_exists V natPins _ artifact.env checked

/-- Direct correspondence identifies a full member of an actual declaration
in the accepted fold. Inductive members retain every rule field via
`readerEntries`; flattened definition-block declarations use the same route.
This is reader membership, not equality to installed annotated fields. -/
theorem AcceptedAssociation.direct_member_reading {input : Input}
    (accepted : AcceptedAssociation input) {ci : Lean.ConstantInfo}
    (direct : DirectMatch ⟨input.source, input.map, accepted.pins⟩
      (streamEntries accepted.declarations) ci) :
    ∃ expected actual decl natPins,
      directExport ⟨input.source, input.map, accepted.pins⟩ ci = .ok expected ∧
      EntryCompatible actual expected ∧ actual ∈ readerEntries decl ∧
      decl ∈ Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations ∧
      builtinNatOpPins = .ok natPins ∧
      Kernel.Cached.checkDecls .verified natPins
        (Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations) = .ok accepted.env := by
  cases he : directExport ⟨input.source, input.map, accepted.pins⟩ ci with
  | error e => simp [DirectMatch, he] at direct
  | ok expected =>
    have hm : expected.withoutHint ∈ compatibleEntries (streamEntries accepted.declarations) := by
      simpa [DirectMatch, he] using direct
    obtain ⟨actual, ha, same⟩ := List.mem_map.mp hm
    obtain ⟨decl, hd, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨natPins, hn, hc⟩ := accepted.toAdmittedArtifact.checked_declarations
    exact ⟨expected, actual, decl, natPins, rfl, same, hm,
      Kernel.Frontend.mem_preparePrelude (by simpa using hd), hn, hc⟩

/-- A raw-source definition is related to an actual declaration in the
admitted fold by the reader's proved normalization specification. Its raw
body remains explicit; no projection denotation theorem is smuggled into W. -/
theorem AcceptedAssociation.raw_definition_reading {input : Input}
    (accepted : AcceptedAssociation input) {ci : Lean.ConstantInfo}
    {owner : Address} {record : Ixon.Constant} {cv : Kernel.ConstantVal}
    {value : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (record_found : rawSourceRecord ⟨input.source, input.map, accepted.pins⟩
      accepted.constants ci = some (owner, record))
    (exported : directExport ⟨input.source, input.map, accepted.pins⟩ ci = .ok (.defn cv value hint))
    (raw : RawSourceMatch ⟨input.source, input.map, accepted.pins⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants ci) :
    ∃ natPins state decl ds, builtinNatOpPins = .ok natPins ∧
      DefinitionDecl cv value (projRewrite state cv value) .defn decl ∧
      decl ∈ ds ∧ Kernel.Cached.checkDecls .verified natPins ds = .ok accepted.env := by
  have hm : RawEntryMatch
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      owner record (.defn cv value hint) := by
    simpa only [RawSourceMatch, exported, record_found] using raw
  cases hi : record.info <;> simp only [RawEntryMatch, hi] at hm
  all_goals try contradiction
  case defn definition =>
    obtain ⟨natPins, hn, installed⟩ := accepted.toAdmittedArtifact.installed_exact
    obtain ⟨state, decl, ds, reading, member, checked, _⟩ :=
      installed.singleton (rawSourceRecord_mem record_found) (by simp [hi, isSingleton])
    exact ⟨natPins, state, decl, ds, hn,
      RawDefinitionAgrees.reader_decl hi hm reading, member, checked⟩

/-- Restrict only source associations. Target bytes remain exact, including
their support/prelude; selecting a source root does not forge a new artifact. -/
def selectedInput (input : Input) (root : Lean.Name)
    (selected : SelectedSource input.source [root]) : Input :=
  { input with
    source := selected.source
    roots := [root]
    map := input.map.filter (fun e => selected.source.names.contains e.source) }

structure RootAssociation (input : Input) (root : Lean.Name) where
  selected : SelectedSource input.source [root]
  association : AcceptedAssociation (selectedInput input root selected)

inductive RootDecline where
  | selection (reason : String)
  | certification (reason : Decline)

/-- One supported cone can certify despite unrelated unsupported ambient
source declarations. Each requested root receives its own explicit outcome. -/
def checkRootWithArtifact (input : Input) (artifact : AdmittedArtifact input.toArtifactInput)
    (root : Lean.Name) :
    Except RootDecline (RootAssociation input root) := do
  let selected ← (selectSource input.source [root]).mapError RootDecline.selection
  let association ← (checkAssociation (selectedInput input root selected) artifact).mapError
    RootDecline.certification
  return ⟨selected, association⟩

def checkRoot (input : Input) (root : Lean.Name) :
    Except RootDecline (RootAssociation input root) := do
  let artifact ← (prepareArtifact input.toArtifactInput).mapError RootDecline.certification
  checkRootWithArtifact input artifact root

structure RootOutcome (input : Input) where
  root : Lean.Name
  result : Except RootDecline (RootAssociation input root)

inductive OutcomeClass where
  | certified | unsupported | blocked | rejected
  deriving BEq, Repr

/-- Classification never turns a decline into an acceptance. Original
diagnostics remain in `RootOutcome.result`. Internal/resource failures are
blocked; only completed malformed/correspondence decisions are rejected. -/
def admissionClass : Kernel.Admission.Error → OutcomeClass
  | .limit _ | .prelude _ | .kernel (.internal _) _ => .blocked
  | .read _ (.declined reason) | .kernel (.notImplemented reason) _ =>
    if (reason.splitOn "fuel").length > 1 then .blocked else .unsupported
  | _ => .rejected

def RootOutcome.classification {input : Input} (outcome : RootOutcome input) : OutcomeClass :=
  match outcome.result with
  | .ok _ => .certified
  | .error (.selection _) => .blocked
  | .error (.certification reason) =>
    match reason with
    | .unsupported .. => .unsupported
    | .admission e | .reading e => admissionClass e
    | .decoding (.limit _) | .setup _ => .blocked
    | _ => .rejected

def checkRoots (input : Input) : List (RootOutcome input) :=
  match prepareArtifact input.toArtifactInput with
  | .error e => input.roots.map (fun root => ⟨root, .error (.certification e)⟩)
  | .ok artifact => input.roots.map (fun root => ⟨root, checkRootWithArtifact input artifact root⟩)

theorem checkRoots_coverage (input : Input) :
    (checkRoots input).map RootOutcome.root = input.roots := by
  unfold checkRoots
  split <;> simp [List.map_map, Function.comp_def]

open Kernel.Semantics Kernel.Model Kernel.Model.Rules in
/-- The value-level telescope required by installed capability laws follows
from the actual application and a stored syntactic Pi prefix. An arbitrary
substitution-created Pi is not treated as evidence of that prefix. -/
theorem AnnotatedApplication.installed_value_fit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (constant : Kernel.ConstantInfo)
    (lookup : env.find? name = some constant) (termEntry : constant.isTowerEntry = false)
    (universes : List Kernel.Level) (arity : universes.length = constant.toConstantVal.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
      expressions annotations residual)
    (piPrefix : (constant.toConstantVal.type.stripPis annotations.length).isSome = true) :
    ∃ typeAnnotation result,
      denoteMeta strong.internal.base2.acval env levels 0
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes) =
          some typeAnnotation ∧
      TeleFit V ρ typeAnnotation (annotations.map (interp V ρ)) result := by
  obtain ⟨typeAnnotation, result, reading, fit, _⟩ :=
    application.installed_fit name constant lookup termEntry universes arity
  exact ⟨typeAnnotation, interp V ρ result, reading,
    teleFit_of_teleFitPA (piChain_of_stripPis annotations.length
      (Kernel.Expr.stripPis_instantiateLevelParams_isSome
        constant.toConstantVal.levelParams universes annotations.length piPrefix) reading) fit⟩

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Fire the actual installed non-basis unit capability using the checked
application. Both the Pi piPrefix and the capability law come from the same
installed model; neither a Boolean claim nor a length equality supplies the
typed telescope. Reserved basis families have separate laws. -/
theorem AnnotatedApplication.installed_unit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (header : Kernel.ConstantVal) (caps : Kernel.IndCaps)
    (lookup : env.find? name = some (.indInfo header caps))
    (enabled : caps.unitlike = true) (nonbasis : Kernel.reservedBasisNames.contains name = false)
    (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (header.type.instantiateLevelParams header.levelParams universes) expressions annotations residual)
    (count : annotations.length = caps.unitParams) (x y : V)
    (left : x ∈ˢ (annotations.map (interp V ρ)).foldl app
      (interp V ρ (strong.internal.base2.acval name (Kernel.Level.substFn levels header.levelParams universes))))
    (right : y ∈ˢ (annotations.map (interp V ρ)).foldl app
      (interp V ρ (strong.internal.base2.acval name (Kernel.Level.substFn levels header.levelParams universes)))) :
    x = y := by
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have piPrefix : (header.type.stripPis annotations.length).isSome = true := by
    rw [count]
    exact (wf.2.2.2.2.2.2.2 header caps rfl).1 enabled
  obtain ⟨typeAnnotation, result, reading, fit⟩ :=
    application.installed_value_fit name (.indInfo header caps) lookup rfl universes arity piPrefix
  obtain ⟨lawAnnotation, lawReading, _, law⟩ :=
    strong.internal.caps_ok.2 name header caps lookup enabled nonbasis levels universes arity
  have same : typeAnnotation = lawAnnotation := Option.some.inj (reading.symm.trans lawReading)
  subst lawAnnotation
  exact law ρ (annotations.map (interp V ρ)) result x y (by simpa using count) fit left right

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- The structural eta equation at the same installed family's actual
parameter application. The stored family/constructor/projection capability
association remains explicit; target content aliases do not establish it. -/
theorem AnnotatedApplication.installed_eta {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (header : Kernel.ConstantVal) (caps : Kernel.IndCaps)
    (lookup : env.find? name = some (.indInfo header caps))
    (enabled : caps.eta = true) (nonbasis : Kernel.reservedBasisNames.contains name = false)
    (stored : Kernel.EtaFamilyStored env name caps)
    (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (header.type.instantiateLevelParams header.levelParams universes) expressions annotations residual)
    (count : annotations.length = caps.etaParams) (x : V)
    (member : x ∈ˢ (annotations.map (interp V ρ)).foldl app
      (interp V ρ (strong.internal.base2.acval name (Kernel.Level.substFn levels header.levelParams universes)))) :
    x = (etaFabArgsV
      (fun n => interp V ρ (strong.internal.base2.acval n
        (Kernel.Level.substFn levels header.levelParams universes)))
      name (annotations.map (interp V ρ)) x caps.etaFields).foldl app
      (interp V ρ (strong.internal.base2.acval caps.etaCtor
        (Kernel.Level.substFn levels header.levelParams universes))) := by
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have piPrefix : (header.type.stripPis annotations.length).isSome = true := by
    rw [count]
    exact (wf.2.2.2.2.2.2.2 header caps rfl).2 enabled
  obtain ⟨typeAnnotation, result, reading, fit⟩ :=
    application.installed_value_fit name (.indInfo header caps) lookup rfl universes arity piPrefix
  obtain ⟨lawAnnotation, lawReading, _, law⟩ :=
    strong.internal.caps_ok.1 name header caps lookup enabled nonbasis stored levels universes arity
  have same : typeAnnotation = lawAnnotation := Option.some.inj (reading.symm.trans lawReading)
  subst lawAnnotation
  exact law ρ (annotations.map (interp V ρ)) result x (by simpa using count) fit member

/-- Check the exact stored constructor/projection presence required by the
eta law. This does not establish cross-environment semantic correspondence. -/
def checkInstalledEtaFamily (env : Kernel.Env) (name : Kernel.Name) (caps : Kernel.IndCaps) : Bool :=
  !Kernel.reservedBasisNames.contains caps.etaCtor &&
  (match env.find? caps.etaCtor with | some (.ctorInfo ..) => true | _ => false) &&
  (List.range caps.etaFields).all fun index =>
    match env.find? (Kernel.projFnName name index) with
    | some (.recInfo ..) => true
    | _ => false

theorem checkInstalledEtaFamily_sound {env : Kernel.Env} {name : Kernel.Name} {caps : Kernel.IndCaps}
    (checked : checkInstalledEtaFamily env name caps = true) : Kernel.EtaFamilyStored env name caps := by
  simp only [checkInstalledEtaFamily, Bool.and_eq_true] at checked
  obtain ⟨⟨nonbasis, constructor⟩, projections⟩ := checked
  refine ⟨by simpa using nonbasis, ?_, ?_⟩
  · cases found : env.find? caps.etaCtor with
    | none => simp [found] at constructor
    | some entry =>
      cases entry <;> simp [found] at constructor
      case ctorInfo header params fields => exact ⟨header, params, fields, rfl⟩
  · intro index bound
    have row := List.all_eq_true.mp projections index (List.mem_range.mpr bound)
    cases found : env.find? (Kernel.projFnName name index) with
    | none => simp [found] at row
    | some entry =>
      cases entry <;> simp [found] at row
      case recInfo header major params rules => exact ⟨header, major, params, rules, rfl⟩

/-- All stored capability fields remain visible. The constructor and indexed
projection-name images are required when eta actually uses them. The sort
datum is compared semantically in the owner's universe telescope below. -/
def InstalledCapsHeader (names : Kernel.Name → Kernel.Name) (owner : Kernel.Name)
    (source target : Kernel.IndCaps) : Prop :=
  source.eta = target.eta ∧ source.unitlike = target.unitlike ∧ source.ruleK = target.ruleK ∧
  source.etaParams = target.etaParams ∧ source.etaFields = target.etaFields ∧
  source.unitParams = target.unitParams ∧
  (source.eta = true → target.etaCtor = names source.etaCtor ∧
    ∀ index ∈ List.range source.etaFields,
      names (Kernel.projFnName owner index) = Kernel.projFnName (names owner) index)

instance (names : Kernel.Name → Kernel.Name) (owner : Kernel.Name)
    (source target : Kernel.IndCaps) : Decidable (InstalledCapsHeader names owner source target) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Reuse the proved binder-regime comparison for the capability's exact
sort datum. This carrier expression is not claimed to be a stored type. -/
def capabilityDatumExpr (caps : Kernel.IndCaps) : Kernel.Expr :=
  .forallE (.sort .zero) (.sort .zero) ⟨caps.sortZ⟩

def checkInstalledCapabilities (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry => match entry with
    | .indInfo header caps =>
      decide (source.find? header.name = some entry) &&
      match target.find? (names header.name) with
      | some (.indInfo _ targetCaps) =>
        decide (InstalledCapsHeader names header.name caps targetCaps) &&
        decide (checkInstalledMemberExpr source target names header.name
          (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps) = some true)
      | _ => false
    | _ => true

theorem checkInstalledCapabilities_member {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledCapabilities source target names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ source.consts) :
    source.find? header.name = some (.indInfo header caps) ∧
    ∃ targetHeader targetCaps,
      target.find? (names header.name) = some (.indInfo targetHeader targetCaps) ∧
      InstalledCapsHeader names header.name caps targetCaps ∧
      checkInstalledMemberExpr source target names header.name
        (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps) = some true := by
  have row := List.all_eq_true.mp checked (.indInfo header caps) present
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  refine ⟨row.1, ?_⟩
  cases lookup : target.find? (names header.name) with
  | none => simp [lookup] at row
  | some entry =>
    cases entry <;> simp only [lookup, Bool.and_eq_true, decide_eq_true_eq] at row
    case indInfo targetHeader targetCaps => exact ⟨targetHeader, targetCaps, rfl, row.2⟩
    all_goals simp at row

theorem checkInstalledCapabilities_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts) :
    ∃ targetHeader targetCaps,
      targetEnv.find? (names header.name) = some (.indInfo targetHeader targetCaps) ∧
      InstalledCapsHeader names header.name caps targetCaps ∧
      ∀ levels, Kernel.regime levels caps.sortZ = Kernel.regime
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels) targetCaps.sortZ := by
  obtain ⟨sourceLookup, targetHeader, targetCaps, targetLookup, headers, compared⟩ :=
    checkInstalledCapabilities_member checked present
  refine ⟨targetHeader, targetCaps, targetLookup, headers, ?_⟩
  intro levels
  have image := checkInstalledMemberExpr_sound target association sourceLookup compared levels
  cases image with
  | forallE _ _ regimes => exact regimes

/-- The reserved unit-capable family is determined by the actual pinned
declaration table, not by an arbitrary name or capability assertion. -/
theorem StrongInstalledModel.reserved_unit_name {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.unitlike = true) : name = Kernel.punitName := by
  have pinned := (strong.internal.base2.basis_pinned name _ lookup reserved).1
  have table : Kernel.reservedBasisNames.all (fun n => match Kernel.pinnedInfo n with
      | .indInfo _ c => !c.unitlike || decide (n = Kernel.punitName)
      | _ => true) = true := by decide
  have member : name ∈ Kernel.reservedBasisNames := by simpa using reserved
  have row := List.all_eq_true.mp table name member
  rw [← pinned] at row
  simpa [enabled] using row

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
theorem StrongInstalledModel.punit_value {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (lookup : env.find? Kernel.punitName = some Kernel.punitA)
    (levels : Kernel.Name → Nat) : strong.public.cval Kernel.punitName levels = (unitSet : V) := by
  have pinned : strong.internal.base2.cvalE Kernel.punitName levels =
      Kernel.Term.punitT (levels Kernel.uN) :=
    (strong.internal.base2.basis_pinned Kernel.punitName _ lookup (by decide)).2 _ levels rfl
  have leaf : strong.internal.base2.acval Kernel.punitName levels = .const .punit [levels Kernel.uN] :=
    erase_eq_const (by rw [strong.internal.base2.acval_erase, pinned]; rfl)
  change interp V (fun _ => empty) (strong.internal.base2.acval Kernel.punitName levels) = unitSet
  rw [leaf, interp_const]
  rfl

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- The reserved branch of the unit law, with its zero parameter count
derived from the pinned installed record. -/
theorem StrongInstalledModel.reserved_unit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.unitlike = true) (levels : Kernel.Name → Nat)
    (values : List V) (count : values.length = caps.unitParams) (x y : V)
    (left : x ∈ˢ values.foldl app (strong.public.cval name levels))
    (right : y ∈ˢ values.foldl app (strong.public.cval name levels)) : x = y := by
  have named := strong.reserved_unit_name lookup reserved enabled
  subst name
  have pinned := (strong.internal.base2.basis_pinned Kernel.punitName _ lookup reserved).1
  have found : env.find? Kernel.punitName = some Kernel.punitA := by
    simpa only [pinned, show Kernel.pinnedInfo Kernel.punitName = Kernel.punitA from rfl] using lookup
  have zero : caps.unitParams = 0 := by
    have h := congrArg (fun entry => match entry with | .indInfo _ c => c.unitParams | _ => 0) pinned
    exact h
  have nil : values = [] := by simpa using count.trans zero
  rw [nil, List.foldl_nil, strong.punit_value found levels] at left right
  exact (mem_unitSet left).trans (mem_unitSet right).symm
open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Source-side unit law for the target-derived interpretation. Installed
type/capability checks and the source typed application assemble the actual
target application; no target telescope or member equality is assumed.
Reserved families use the pinned PUnit law; other families use their stored
unit capability. No reserved-family exclusion is imposed. -/
theorem checked_unit_pullback {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts)
    (enabled : caps.unitlike = true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = header.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    {depth : Nat} {ρ : Nat → V} {targetExpressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations target targetLevels depth ρ targetExpressions annotations)
    {sourceExpressions : List Kernel.Expr} {values : List V} {sourceResidual : Kernel.Expr}
    (application : DenotedApplication
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels ρ (header.type.instantiateLevelParams header.levelParams sourceUs)
      sourceExpressions values sourceResidual)
    (argumentImages : InstalledSpineImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceExpressions (targetExpressions.map (Kernel.Expr.closeN depth)))
    (count : values.length = caps.unitParams) (x y : V)
    (left : x ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs)))
    (right : y ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))) : x = y := by
  obtain ⟨sourceLookup, targetHeader, targetCaps, targetLookup, capHeader, _⟩ :=
    checkInstalledCapabilities_member capabilities present
  obtain ⟨associated, associatedLookup, telescope⟩ := association _ _ sourceLookup
  have same := Option.some.inj (associatedLookup.symm.trans targetLookup)
  subst associated
  have targetArity : targetUs.length = targetHeader.levelParams.length := by
    have equalLengths := congrArg List.length universes
    simp only [List.length_map] at equalLengths
    exact equalLengths.symm.trans (sourceArity.trans telescope.2.2)
  obtain ⟨residual, targetApplication, _⟩ := AnnotatedApplication.from_checked_type target association types
    present targetLookup sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
    readings application argumentImages
  have equalValues := (application.arguments.image argumentImages).functional readings.denotes
  have equalFamily :
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs) =
      target.public.cval (names header.name) (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs) := by
    apply target.value_params targetLookup
    exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
      sourceUs targetUs sourceArity targetArity universes
  have targetEnabled : targetCaps.unitlike = true := capHeader.2.1.symm.trans enabled
  have targetCount : annotations.length = targetCaps.unitParams := by
    rw [equalValues, List.length_map] at count
    exact count.trans capHeader.2.2.2.2.2.1
  rw [equalValues, equalFamily] at left right
  by_cases reserved : Kernel.reservedBasisNames.contains (names header.name) = true
  · exact target.reserved_unit targetLookup reserved targetEnabled
      (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs)
      (annotations.map (interp V ρ)) (by simpa using targetCount) x y left right
  · have nonbasis : Kernel.reservedBasisNames.contains (names header.name) = false := by
      simpa using reserved
    apply targetApplication.installed_unit (names header.name) targetHeader targetCaps targetLookup
      targetEnabled nonbasis targetUs targetArity targetCount x y
    · simpa only [interp_cvalOf target.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using left
    · simpa only [interp_cvalOf target.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using right


/-- Compare a helper's own universe instance inside its family's telescope.
Eta evaluates constructor/projection leaves at that family assignment, not
at an independently chosen helper assignment. Target coverage permits the
proved family-instance locality step; no ambient valuation equality is used. -/
def checkInstalledFamilyMember (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (owner member : Kernel.Name) : Option Bool :=
  match source.find? member, target.find? (names member), target.find? (names owner) with
  | some sourceMember, some targetMember, some targetOwner =>
    if targetMember.toConstantVal.levelParams.all
        (fun parameter => targetOwner.toConstantVal.levelParams.contains parameter) then
      checkInstalledMemberExpr source target names owner
        (.const member (sourceMember.toConstantVal.levelParams.map Kernel.Level.param))
        (.const (names member) (targetMember.toConstantVal.levelParams.map Kernel.Level.param))
    else some false
  | _, _, _ => some false

theorem checkInstalledFamilyMember_lookups {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    {owner member : Kernel.Name} {targetOwner : Kernel.ConstantInfo}
    (ownerLookup : target.find? (names owner) = some targetOwner)
    (checked : checkInstalledFamilyMember source target names owner member = some true) :
    ∃ sourceMember targetMember,
      source.find? member = some sourceMember ∧ target.find? (names member) = some targetMember ∧
      (∀ parameter ∈ targetMember.toConstantVal.levelParams, parameter ∈ targetOwner.toConstantVal.levelParams) ∧
      checkInstalledMemberExpr source target names owner
        (.const member (sourceMember.toConstantVal.levelParams.map Kernel.Level.param))
        (.const (names member) (targetMember.toConstantVal.levelParams.map Kernel.Level.param)) = some true := by
  cases sourceLookup : source.find? member with
  | none => simp [checkInstalledFamilyMember, sourceLookup] at checked
  | some sourceMember =>
    cases targetLookup : target.find? (names member) with
    | none => simp [checkInstalledFamilyMember, sourceLookup, targetLookup] at checked
    | some targetMember =>
      simp only [checkInstalledFamilyMember, sourceLookup, targetLookup, ownerLookup] at checked
      split at checked
      next coverage =>
        refine ⟨sourceMember, targetMember, rfl, rfl, ?_, checked⟩
        intro parameter present
        have row := List.all_eq_true.mp coverage parameter present
        simpa using row
      next => contradiction

/-- Accepted owner-relative helper comparison proves its actual value at
the concrete family universe instance. Helper aliases keep their own source
telescope and are never resolved by choosing a reverse representative. -/
theorem checkInstalledFamilyMember_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {owner member : Kernel.Name} {sourceOwner targetOwner : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? owner = some sourceOwner)
    (targetLookup : targetEnv.find? (names owner) = some targetOwner)
    (checked : checkInstalledFamilyMember sourceEnv targetEnv names owner member = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceOwner.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetOwner.toConstantVal.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval member
      (Kernel.Level.substFn sourceLevels sourceOwner.toConstantVal.levelParams sourceUs) =
    target.public.cval (names member)
      (Kernel.Level.substFn targetLevels targetOwner.toConstantVal.levelParams targetUs) := by
  obtain ⟨sourceMember, targetMember, sourceMemberLookup, targetMemberLookup, coverage, compared⟩ :=
    checkInstalledFamilyMember_lookups targetLookup checked
  let sourceInstance := Kernel.Level.substFn sourceLevels sourceOwner.toConstantVal.levelParams sourceUs
  have image := checkInstalledMemberExpr_sound target association sourceLookup compared sourceInstance
  have direct : (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval member sourceInstance =
      target.public.cval (names member)
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels owner sourceInstance) := by
    have sourceRead := denotes_self_instance (V := V)
      (values := (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      (levels := sourceInstance) (ρ := fun _ => Kernel.SetTheory.empty) sourceMemberLookup
    exact Kernel.Denotes_functional (image.denotes sourceRead) (denotes_self_instance targetMemberLookup)
  apply direct.trans
  apply target.value_params targetMemberLookup
  intro parameter present
  exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
    sourceUs targetUs sourceArity targetArity universes parameter (coverage parameter present)

theorem StrongInstalledModel.reserved_eta_name {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.eta = true) : name = Kernel.punitName := by
  have pinned := (strong.internal.base2.basis_pinned name _ lookup reserved).1
  have table : Kernel.reservedBasisNames.all (fun n => match Kernel.pinnedInfo n with
      | .indInfo _ c => !c.eta || decide (n = Kernel.punitName)
      | _ => true) = true := by decide
  have member : name ∈ Kernel.reservedBasisNames := by simpa using reserved
  have row := List.all_eq_true.mp table name member
  rw [← pinned] at row
  simpa [enabled] using row

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
theorem StrongInstalledModel.punit_unit_value {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (lookup : env.find? Kernel.punitUnitName = some Kernel.punitUnitA)
    (levels : Kernel.Name → Nat) : strong.public.cval Kernel.punitUnitName levels = (pt : V) := by
  have pinned : strong.internal.base2.cvalE Kernel.punitUnitName levels =
      Kernel.Term.punitUnitT (levels Kernel.uN) :=
    (strong.internal.base2.basis_pinned Kernel.punitUnitName _ lookup (by decide)).2 _ levels rfl
  have leaf : strong.internal.base2.acval Kernel.punitUnitName levels = .const .punitUnit [levels Kernel.uN] :=
    erase_eq_const (by rw [strong.internal.base2.acval_erase, pinned]; rfl)
  change interp V (fun _ => empty) (strong.internal.base2.acval Kernel.punitUnitName levels) = pt
  rw [leaf, interp_const]
  rfl

open Kernel.Model Kernel.SetTheory in
/-- Reserved eta uses the actual pinned family and its stored constructor,
including zero parameter/field counts; no general non-basis eta premise is
applied to a reserved family. -/
theorem StrongInstalledModel.reserved_eta {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.eta = true)
    (constructor : ∃ entry, env.find? caps.etaCtor = some entry)
    (levels : Kernel.Name → Nat) (values : List V) (count : values.length = caps.etaParams)
    (x : V) (member : x ∈ˢ values.foldl app (strong.public.cval name levels)) :
    x = (etaFabArgsV (fun n => strong.public.cval n levels) name values x caps.etaFields).foldl app
      (strong.public.cval caps.etaCtor levels) := by
  have named := strong.reserved_eta_name lookup reserved enabled
  subst name
  have pinned := (strong.internal.base2.basis_pinned Kernel.punitName _ lookup reserved).1
  have found : env.find? Kernel.punitName = some Kernel.punitA := by
    simpa only [pinned, show Kernel.pinnedInfo Kernel.punitName = Kernel.punitA from rfl] using lookup
  have zeroParams : caps.etaParams = 0 :=
    congrArg (fun entry => match entry with | .indInfo _ c => c.etaParams | _ => 0) pinned
  have zeroFields : caps.etaFields = 0 :=
    congrArg (fun entry => match entry with | .indInfo _ c => c.etaFields | _ => 0) pinned
  have ctorName : caps.etaCtor = Kernel.punitUnitName :=
    congrArg (fun entry => match entry with | .indInfo _ c => c.etaCtor | _ => .anonymous) pinned
  obtain ⟨entry, constructorLookup⟩ := constructor
  rw [ctorName] at constructorLookup
  have ctorPinned := (strong.internal.base2.basis_pinned Kernel.punitUnitName _ constructorLookup (by decide)).1
  have ctorFound : env.find? Kernel.punitUnitName = some Kernel.punitUnitA := by
    simpa only [ctorPinned, show Kernel.pinnedInfo Kernel.punitUnitName = Kernel.punitUnitA from rfl] using constructorLookup
  have nil : values = [] := by simpa using count.trans zeroParams
  rw [nil, List.foldl_nil, strong.punit_value found levels] at member
  simpa [nil, zeroFields, ctorName, etaFabArgsV, projSpines, strong.punit_unit_value ctorFound levels]
    using (mem_unitSet member)

open Kernel.Model in
theorem etaFabArgsV_image {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Name → V} {sourceOwner targetOwner : Kernel.Name}
    (arguments : List V) (value : V) (fields : Nat)
    (projections : ∀ index ∈ List.range fields,
      source (Kernel.projFnName sourceOwner index) = target (Kernel.projFnName targetOwner index)) :
    etaFabArgsV source sourceOwner arguments value fields = etaFabArgsV target targetOwner arguments value fields := by
  unfold etaFabArgsV projSpines
  congr 1
  apply List.map_congr_left
  intro index present
  rw [projections index present]

/-- Select the actual eta-law branch for one installed family. Reserved
families use their pinned law; ordinary families must have every stored
constructor/projection entry required by the general eta law. -/
def checkInstalledEtaAt (env : Kernel.Env) (name : Kernel.Name) : Bool :=
  match env.find? name with
  | some (.indInfo _ caps) => Kernel.reservedBasisNames.contains name || checkInstalledEtaFamily env name caps
  | _ => false

theorem checkInstalledEtaAt_sound {env : Kernel.Env} {name : Kernel.Name}
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (checked : checkInstalledEtaAt env name = true) :
    Kernel.reservedBasisNames.contains name = true ∨ Kernel.EtaFamilyStored env name caps := by
  simp only [checkInstalledEtaAt, lookup, Bool.or_eq_true] at checked
  exact checked.imp_right checkInstalledEtaFamily_sound

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- The source-side eta reconstruction equation, including the reserved
basis branch. Every constructor/projection value is related at the actual
family universe instance by its executable owner-relative comparison. -/
theorem checked_eta_pullback {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts)
    (enabled : caps.eta = true)
    (family : checkInstalledEtaAt targetEnv (names header.name) = true)
    (constructor : checkInstalledFamilyMember sourceEnv targetEnv names header.name caps.etaCtor = some true)
    (projections : ∀ index ∈ List.range caps.etaFields,
      checkInstalledFamilyMember sourceEnv targetEnv names header.name (Kernel.projFnName header.name index) = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = header.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    {depth : Nat} {ρ : Nat → V} {targetExpressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations target targetLevels depth ρ targetExpressions annotations)
    {sourceExpressions : List Kernel.Expr} {values : List V} {sourceResidual : Kernel.Expr}
    (application : DenotedApplication
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels ρ (header.type.instantiateLevelParams header.levelParams sourceUs)
      sourceExpressions values sourceResidual)
    (argumentImages : InstalledSpineImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceExpressions (targetExpressions.map (Kernel.Expr.closeN depth)))
    (count : values.length = caps.etaParams) (x : V)
    (member : x ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))) :
    x = (etaFabArgsV
      (fun n => (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval n
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))
      header.name values x caps.etaFields).foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval caps.etaCtor
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs)) := by
  obtain ⟨sourceLookup, targetHeader, targetCaps, targetLookup, capHeader, _⟩ :=
    checkInstalledCapabilities_member capabilities present
  obtain ⟨associated, associatedLookup, telescope⟩ := association _ _ sourceLookup
  have same := Option.some.inj (associatedLookup.symm.trans targetLookup)
  subst associated
  have targetArity : targetUs.length = targetHeader.levelParams.length := by
    have equalLengths := congrArg List.length universes
    simp only [List.length_map] at equalLengths
    exact equalLengths.symm.trans (sourceArity.trans telescope.2.2)
  obtain ⟨residual, targetApplication, _⟩ := AnnotatedApplication.from_checked_type target association types
    present targetLookup sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
    readings application argumentImages
  have equalValues := (application.arguments.image argumentImages).functional readings.denotes
  have equalFamily :
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs) =
      target.public.cval (names header.name) (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs) := by
    apply target.value_params targetLookup
    exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
      sourceUs targetUs sourceArity targetArity universes
  have targetEnabled : targetCaps.eta = true := capHeader.1.symm.trans enabled
  have targetCount : annotations.length = targetCaps.etaParams := by
    rw [equalValues, List.length_map] at count
    exact count.trans capHeader.2.2.2.1
  have namedHelpers := capHeader.2.2.2.2.2.2 enabled
  have ctorImage := checkInstalledFamilyMember_sound target association sourceLookup targetLookup
    constructor sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
  rw [← namedHelpers.1] at ctorImage
  simp only [Kernel.ConstantInfo.toConstantVal] at ctorImage
  have spineImage := etaFabArgsV_image (source := fun n =>
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval n
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))
    (target := fun n => target.public.cval n
      (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs))
    (sourceOwner := header.name) (targetOwner := names header.name) values x caps.etaFields
    (fun index bound => by
      have image := checkInstalledFamilyMember_sound target association sourceLookup targetLookup
        (projections index bound) sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
      rwa [namedHelpers.2 index bound] at image)
  rw [spineImage, ctorImage, capHeader.2.2.2.2.1, equalValues]
  rw [equalValues, equalFamily] at member
  by_cases reserved : Kernel.reservedBasisNames.contains (names header.name) = true
  · obtain ⟨_, constructorEntry, _, constructorLookup, _⟩ := checkInstalledFamilyMember_lookups targetLookup constructor
    rw [← namedHelpers.1] at constructorLookup
    exact target.reserved_eta targetLookup reserved targetEnabled ⟨constructorEntry, constructorLookup⟩
      (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs)
      (annotations.map (interp V ρ)) (by simpa using targetCount) x member
  · have stored := (checkInstalledEtaAt_sound targetLookup family).resolve_left reserved
    have nonbasis : Kernel.reservedBasisNames.contains (names header.name) = false := by simpa using reserved
    have targetMember : x ∈ˢ (annotations.map (interp V ρ)).foldl app
        (interp V ρ (target.internal.base2.acval (names header.name)
          (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs))) := by
      simpa only [interp_cvalOf target.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using member
    have reconstructed := targetApplication.installed_eta (names header.name) targetHeader targetCaps targetLookup
      targetEnabled nonbasis stored targetUs targetArity targetCount x targetMember
    simpa only [interp_cvalOf target.internal.base2.cval_closedL,
      StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using reconstructed

end Ix.CompileCert
