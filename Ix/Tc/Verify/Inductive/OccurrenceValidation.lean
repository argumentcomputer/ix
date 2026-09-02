import Ix.Tc.Verify.Decl
import Ix.Tc.Verify.Support
import Ix.Tc.Verify.Totalization
import Ix.Tc.Verify.Trans
import Ix.Tc.Verify.World

/-!
# Recursive-occurrence validation

E2c consumes the successful branch of production positivity checking.  This
module makes that branch proof-visible: a success identifies the active
family, the exact loaded inductive header, every pure arity/universe/index
guard, and the complete state-threaded parameter-definitional-equality loop.
No semantic inductive oracle is used here.
-/

namespace Ix.Tc

/-- Header information read from the actual recursive-family declaration. -/
def KConst.PositiveRecursiveHeader (concrete : KConst m)
    (nParams nIndices levels : Nat) : Prop :=
  match concrete with
  | .indc (params := params) (indices := indices) (lvls := lvls) .. =>
      params.toNat = nParams ∧ indices.toNat = nIndices ∧
        lvls.toNat = levels
  | _ => False

/-- Elementwise form of the recursive-family universe invariant.  Root
families use the canonical symbolic parameter sequence; nested families use
the concrete specialization captured when the auxiliary was discovered. -/
def PositiveUniverseSpecialization (group : PositivityGroup m)
    (us : Array (KUniv m)) : Prop :=
  match group.concreteUs with
  | some expected =>
      expected.size = us.size ∧
        ∀ i, i < us.size → univEq expected[i]! us[i]! = true
  | none =>
      ∀ i, i < us.size →
        univEq us[i]! (.mkParam i.toUInt64 RecM.anonN : KUniv m) = true

/-- Elementwise form of Lean4Lean's root-family-free index condition. -/
def RootIndicesIndependent (args : Array (KExpr m)) (nParams : Nat)
    (rootAddrs : Array Address) : Prop :=
  let indices := args.extract nParams args.size
  ∀ i (h : i < indices.size),
    exprMentionsAnyAddr indices[i] rootAddrs = false

/-- Exact successful executions of the individual parameter comparisons,
in source order and with every intermediate checker state retained. -/
inductive PositiveParameterComparisonTrace
    (args params : Array (KExpr m)) (methods : Methods m) :
    Nat → Nat → TcState m → TcState m → Prop
  | nil (index state) :
      PositiveParameterComparisonTrace args params methods index 0 state state
  | cons {index remaining before afterComparison final} :
      (RecM.isDefEq args[index]! params[index]!).run methods before =
          .ok true afterComparison →
      PositiveParameterComparisonTrace args params methods (index + 1)
        remaining afterComparison final →
      PositiveParameterComparisonTrace args params methods index
        (remaining + 1) before final

/-- Pointwise semantic consequence of a fixed parameter-comparison slice. -/
def PositiveParameterPairs (relation : KExpr m → KExpr m → Prop)
    (args params : Array (KExpr m)) : Nat → Nat → Prop
  | _, 0 => True
  | index, remaining + 1 =>
      relation args[index]! params[index]! ∧
        PositiveParameterPairs relation args params (index + 1) remaining

/-- Translation and finite-support evidence for each concrete parameter pair.
The translated expressions may differ syntactically; successful DefEq will
establish their Theory equality. -/
def PositiveParameterTranslationPlan
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx)
    (args params : Array (KExpr .anon)) : Nat → Nat → Prop
  | _, 0 => True
  | index, remaining + 1 =>
      support args[index]! ∧ support params[index]! ∧
        ∃ argumentV parameterV,
          TrKExprS world.venv uvars world.nameOf trProj Delta args[index]!
              argumentV ∧
            TrKExprS world.venv uvars world.nameOf trProj Delta params[index]!
              parameterV ∧
            PositiveParameterTranslationPlan trProj world support uvars Delta
              args params (index + 1) remaining

/-- Theory meaning of one production parameter-uniformity comparison. -/
def TranslatedParameterDefEq
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (argument parameter : KExpr .anon) : Prop :=
  support argument ∧ support parameter ∧
    ∃ argumentV parameterV,
      TrKExprS world.venv uvars world.nameOf trProj Delta argument argumentV ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta parameter
          parameterV ∧
        world.venv.IsDefEqU uvars Delta.toCtx argumentV parameterV

/-- The exact semantic callback needed by positivity's parameter loop.

This contract intentionally stops at the production `isDefEq` call.  It does
not grant positivity access to the complete DefEq closure, proposition
classification, or inductive authority.  K2 may instantiate it from an
oracle-free recursive-method closure; E2c only consumes the successful-call
meaning and state preservation recorded here. -/
def PositiveParameterDefEqContract
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (methods : Methods .anon)
    (invariant : TcState .anon → Prop) : Prop :=
  ∀ {state : TcState .anon} {argument parameter : KExpr .anon}
      {argumentV parameterV : Lean4Lean.VExpr},
    support argument → support parameter →
    TrKExprS world.venv uvars world.nameOf trProj Delta argument
      argumentV →
    TrKExprS world.venv uvars world.nameOf trProj Delta parameter
      parameterV →
    TcM.WF invariant state ((RecM.isDefEq argument parameter).run methods)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx argumentV parameterV)

/-- Successful branch of the resolved-header validator.  The parameter
comparison keeps its real recursive-method table and threaded checker states
for the later semantic transport theorem. -/
def PositiveRecursiveApplicationHeaderTrace
    (id : KId m) (us : Array (KUniv m)) (args : Array (KExpr m))
    (group : PositivityGroup m) (rootAddrs : Array Address)
    (nParams nIndices levels : Nat) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  args.size = nParams + nIndices ∧
    us.size = levels ∧
    RecM.positiveUniverseArgumentsAgree group us = true ∧
    group.params.size = nParams ∧
    ∃ afterParameters,
      (RecM.checkPositiveParameters id args group.params nParams).run methods
          initial = .ok () afterParameters ∧
      RecM.positiveIndicesIndependent args nParams rootAddrs = true ∧
      final = afterParameters

/-- Logical valid-inductive-application invariant obtained from the concrete
production guards.  The stateful parameter field deliberately retains the
actual `isDefEq` execution: converting it to the normalized Theory parameter
spine is the semantic translation step, not a syntactic assumption. -/
def ValidPositiveRecursiveApplicationHeader
    (id : KId m) (us : Array (KUniv m)) (args : Array (KExpr m))
    (group : PositivityGroup m) (rootAddrs : Array Address)
    (nParams nIndices levels : Nat) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  args.size = nParams + nIndices ∧
    us.size = levels ∧
    PositiveUniverseSpecialization group us ∧
    group.params.size = nParams ∧
    ∃ afterParameters,
      (RecM.checkPositiveParameters id args group.params nParams).run methods
          initial = .ok () afterParameters ∧
      PositiveParameterComparisonTrace args group.params methods 0 nParams
        initial afterParameters ∧
      RootIndicesIndependent args nParams rootAddrs ∧
      final = afterParameters

/-- Exact successful-branch trace of the complete production recursive
application validator, including active-group selection and lazy lookup. -/
def PositiveRecursiveApplicationTrace
    (id : KId m) (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (rootAddrs : Array Address)
    (methods : Methods m) (initial final : TcState m) : Prop :=
  ∃ group concrete nParams nIndices levels afterLookup,
    groups.find? (fun candidate => candidate.addrs.contains id.addr) =
        some group ∧
      TcM.getConst id initial = .ok concrete afterLookup ∧
      concrete.PositiveRecursiveHeader nParams nIndices levels ∧
      PositiveRecursiveApplicationHeaderTrace id us args group rootAddrs
        nParams nIndices levels methods afterLookup final

/-- Complete selected-family form of the valid-inductive-application
invariant.  It contains no `InductiveOracle`: the family and arities come from
the production lookup that occurred in this successful run. -/
def ValidPositiveRecursiveApplication
    (id : KId m) (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (rootAddrs : Array Address)
    (methods : Methods m) (initial final : TcState m) : Prop :=
  ∃ group concrete nParams nIndices levels afterLookup,
    groups.find? (fun candidate => candidate.addrs.contains id.addr) =
        some group ∧
      TcM.getConst id initial = .ok concrete afterLookup ∧
      concrete.PositiveRecursiveHeader nParams nIndices levels ∧
      ValidPositiveRecursiveApplicationHeader id us args group rootAddrs
        nParams nIndices levels methods afterLookup final

namespace RecM

/-- Boolean universe agreement is exactly its elementwise logical form. -/
theorem positiveUniverseArgumentsAgree_eq_true_iff
    (group : PositivityGroup m) (us : Array (KUniv m)) :
    positiveUniverseArgumentsAgree group us = true ↔
      PositiveUniverseSpecialization group us := by
  cases hconcrete : group.concreteUs with
  | none =>
      simp [positiveUniverseArgumentsAgree, PositiveUniverseSpecialization,
        hconcrete, List.all_eq_true]
  | some expected =>
      simp [positiveUniverseArgumentsAgree, PositiveUniverseSpecialization,
        hconcrete, Bool.and_eq_true, List.all_eq_true]

/-- Boolean index independence is exactly root-family non-occurrence for
every argument after the parameter prefix. -/
theorem positiveIndicesIndependent_eq_true_iff
    (args : Array (KExpr m)) (nParams : Nat)
    (rootAddrs : Array Address) :
    positiveIndicesIndependent args nParams rootAddrs = true ↔
      RootIndicesIndependent args nParams rootAddrs := by
  unfold positiveIndicesIndependent RootIndicesIndependent
  rw [Array.all_eq_true]
  simp

/-- The pure validator succeeds exactly when all four header invariants hold.
    This is the bridge from production diagnostics to the logical contract. -/
theorem checkPositiveRecursiveApplicationPreconditions_success_iff
    {us : Array (KUniv m)} {args : Array (KExpr m)}
    {group : PositivityGroup m} {nParams nIndices levels : Nat} :
    checkPositiveRecursiveApplicationPreconditions us args group nParams
        nIndices levels = .ok () ↔
      args.size = nParams + nIndices ∧
      us.size = levels ∧
      positiveUniverseArgumentsAgree group us = true ∧
      group.params.size = nParams := by
  unfold checkPositiveRecursiveApplicationPreconditions
  by_cases hargs : args.size = nParams + nIndices
  · by_cases hus : us.size = levels
    · cases huniverses : positiveUniverseArgumentsAgree group us with
      | false => simp [hargs, hus]
      | true =>
          by_cases hparams : group.params.size = nParams
          · simp [hargs, hus, hparams]
          · simp [hargs, hus, hparams]
    · simp [hargs, hus]
  · simp [hargs]

/-- Expose one concrete `TcM` bind while decomposing the successful
production trace. -/
private theorem runTcBind {α β : Type}
    (x : TcM m α) (k : α → TcM m β) (state : TcState m) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- Success of the structurally recursive loop exposes the exact successful
`isDefEq` execution at every parameter position. -/
theorem checkPositiveParametersFrom_success
    (id : KId m) (args params : Array (KExpr m)) (methods : Methods m) :
    ∀ {index remaining : Nat} {initial final : TcState m},
      (checkPositiveParametersFrom id args params index remaining).run methods
          initial = .ok () final →
      PositiveParameterComparisonTrace args params methods index remaining
        initial final
  | _, 0, initial, final, hrun => by
      simp only [checkPositiveParametersFrom, pure, ReaderT.run] at hrun
      cases hrun
      exact .nil _ _
  | index, remaining + 1, initial, final, hrun => by
      rw [checkPositiveParametersFrom, ReaderT.run_bind, runTcBind] at hrun
      generalize hcomparison :
          (isDefEq args[index]! params[index]!).run methods initial =
            comparisonResult at hrun
      cases comparisonResult with
      | error err afterComparison => contradiction
      | ok answer afterComparison =>
          cases answer with
          | false =>
              simp only [Bool.not_false, if_true] at hrun
              change EStateM.Result.error _ afterComparison = .ok () final
                at hrun
              contradiction
          | true =>
              simp only [Bool.not_true] at hrun
              exact .cons hcomparison
                (checkPositiveParametersFrom_success id args params methods
                  hrun)

/-- Public parameter-loop success trace, starting at the first parameter. -/
theorem checkPositiveParameters_success
    {id : KId m} {args params : Array (KExpr m)} {nParams : Nat}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkPositiveParameters id args params nParams).run methods
      initial = .ok () final) :
    PositiveParameterComparisonTrace args params methods 0 nParams initial
      final := by
  exact checkPositiveParametersFrom_success id args params methods hrun

/-- Any sound interpretation of individual successful `isDefEq` calls lifts
pointwise across the complete parameter trace. -/
theorem PositiveParameterComparisonTrace.sound
    {args params : Array (KExpr m)} {methods : Methods m}
    {relation : KExpr m → KExpr m → Prop}
    {index remaining : Nat} {initial final : TcState m}
    (trace : PositiveParameterComparisonTrace args params methods index
      remaining initial final)
    (soundComparison : ∀ {position : Nat} {before after : TcState m},
      (isDefEq args[position]! params[position]!).run methods before =
          .ok true after →
      relation args[position]! params[position]!) :
    PositiveParameterPairs relation args params index remaining := by
  induction trace with
  | nil => trivial
  | cons hcomparison _ ih =>
      exact ⟨soundComparison hcomparison, ih⟩

/-- Instantiate every comparison with the narrow production DefEq contract.
This is the semantic parameter-uniformity bridge: a successful concrete loop
yields pointwise `VEnv.IsDefEqU` facts for the translated parameter spine, and
the checker invariant reaches the final threaded state. -/
theorem PositiveParameterComparisonTrace.theoryDefEq
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    (defEq : PositiveParameterDefEqContract trProj world support uvars Delta
      methods invariant)
    {args params : Array (KExpr .anon)}
    {index remaining : Nat} {initial final : TcState .anon}
    (trace : PositiveParameterComparisonTrace args params methods index
      remaining initial final)
    (hinitial : invariant initial)
    (plan : PositiveParameterTranslationPlan trProj world support
      uvars Delta args params index remaining) :
    PositiveParameterPairs
        (TranslatedParameterDefEq trProj world support
          uvars Delta)
        args params index remaining ∧
      invariant final := by
  induction trace with
  | nil => exact ⟨trivial, hinitial⟩
  | @cons index remaining before afterComparison final hcomparison _ ih =>
      rcases plan with
        ⟨hargumentSupport, hparameterSupport, argumentV, parameterV,
          hargument, hparameter, htailPlan⟩
      have hverified := defEq
        (state := before)
        hargumentSupport hparameterSupport hargument hparameter
      have hpost := hverified hinitial
      rw [hcomparison] at hpost
      have htail := ih hpost.1 htailPlan
      exact ⟨
        ⟨⟨hargumentSupport, hparameterSupport, argumentV, parameterV,
          hargument, hparameter, hpost.2 rfl⟩, htail.1⟩,
        htail.2⟩

/-- Semantic parameter-uniformity consequence of a valid resolved header.
The operational header retains its exact comparison trace; this theorem
discharges that trace with only the narrow DefEq callback contract. -/
theorem ValidPositiveRecursiveApplicationHeader.theoryParameters
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {invariant : TcState .anon → Prop}
    (defEq : PositiveParameterDefEqContract trProj world support uvars Delta
      methods invariant)
    {id : KId .anon}
    {us : Array (KUniv .anon)} {args : Array (KExpr .anon)}
    {group : PositivityGroup .anon} {rootAddrs : Array Address}
    {nParams nIndices levels : Nat} {initial final : TcState .anon}
    (valid : ValidPositiveRecursiveApplicationHeader id us args group
      rootAddrs nParams nIndices levels methods initial final)
    (hinitial : invariant initial)
    (plan : PositiveParameterTranslationPlan trProj world support
      uvars Delta args group.params 0 nParams) :
    ∃ afterParameters,
      PositiveParameterPairs
          (TranslatedParameterDefEq trProj world support
            uvars Delta)
          args group.params 0 nParams ∧
        invariant afterParameters ∧
        final = afterParameters := by
  rcases valid with
    ⟨_, _, _, _, afterParameters, _, trace, _, hfinal⟩
  have hsemantic :=
    Ix.Tc.RecM.PositiveParameterComparisonTrace.theoryDefEq defEq trace
      hinitial plan
  exact ⟨afterParameters, hsemantic.1, hsemantic.2, hfinal⟩

/-- A successful resolved-header validation exposes every guard and the exact
parameter-comparison execution that justified it. -/
theorem checkPositiveRecursiveApplicationHeader_success
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {group : PositivityGroup m} {rootAddrs : Array Address}
    {nParams nIndices levels : Nat} {methods : Methods m}
    {initial final : TcState m}
    (hrun : (checkPositiveRecursiveApplicationHeader id us args group
      rootAddrs nParams nIndices levels).run methods initial = .ok () final) :
    PositiveRecursiveApplicationHeaderTrace id us args group rootAddrs
      nParams nIndices levels methods initial final := by
  unfold checkPositiveRecursiveApplicationHeader at hrun
  generalize hpreconditions :
      checkPositiveRecursiveApplicationPreconditions us args group nParams
        nIndices levels = preconditionResult at hrun
  cases preconditionResult with
  | error err =>
      simp only at hrun
      change EStateM.Result.error err initial = .ok () final at hrun
      contradiction
  | ok value =>
      cases value
      obtain ⟨hargs, hus, huniverses, hparams⟩ :=
        checkPositiveRecursiveApplicationPreconditions_success_iff.mp
          hpreconditions
      simp only at hrun
      rw [ReaderT.run_bind, runTcBind] at hrun
      generalize hparameterRun :
          (checkPositiveParameters id args group.params nParams).run methods
            initial = parameterResult at hrun
      cases parameterResult with
      | error err afterParameters => contradiction
      | ok value afterParameters =>
          cases value
          cases hindependent :
              positiveIndicesIndependent args nParams rootAddrs with
          | false =>
              simp only [hindependent, Bool.not_false, if_true] at hrun
              change EStateM.Result.error _ afterParameters = .ok () final
                at hrun
              contradiction
          | true =>
              simp only [hindependent, Bool.not_true, pure,
                ReaderT.run] at hrun
              cases hrun
              exact ⟨hargs, hus, huniverses, hparams, final,
                hparameterRun, hindependent, rfl⟩

/-- Strengthen an operational header trace to its elementwise logical
valid-inductive-application invariant. -/
theorem PositiveRecursiveApplicationHeaderTrace.valid
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {group : PositivityGroup m} {rootAddrs : Array Address}
    {nParams nIndices levels : Nat} {methods : Methods m}
    {initial final : TcState m}
    (trace : PositiveRecursiveApplicationHeaderTrace id us args group
      rootAddrs nParams nIndices levels methods initial final) :
    ValidPositiveRecursiveApplicationHeader id us args group rootAddrs
      nParams nIndices levels methods initial final := by
  rcases trace with
    ⟨hargs, hus, huniverses, hparams, afterParameters, hparameterRun,
      hindependent, hfinal⟩
  exact ⟨hargs, hus,
    (positiveUniverseArgumentsAgree_eq_true_iff group us).mp huniverses,
    hparams, afterParameters, hparameterRun,
    checkPositiveParameters_success hparameterRun,
    (positiveIndicesIndependent_eq_true_iff args nParams rootAddrs).mp
      hindependent,
    hfinal⟩

/-- Direct logical contract for a successful resolved-header run. -/
theorem checkPositiveRecursiveApplicationHeader_valid
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {group : PositivityGroup m} {rootAddrs : Array Address}
    {nParams nIndices levels : Nat} {methods : Methods m}
    {initial final : TcState m}
    (hrun : (checkPositiveRecursiveApplicationHeader id us args group
      rootAddrs nParams nIndices levels).run methods initial = .ok () final) :
    ValidPositiveRecursiveApplicationHeader id us args group rootAddrs
      nParams nIndices levels methods initial final :=
  PositiveRecursiveApplicationHeaderTrace.valid
    (checkPositiveRecursiveApplicationHeader_success hrun)

/-- Every successful recursive-application validation exposes the selected
family, exact inductive header, and resolved-header success trace. -/
theorem checkPositiveRecursiveApplication_success
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {groups : Array (PositivityGroup m)} {rootAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkPositiveRecursiveApplication id us args groups rootAddrs).run
      methods initial = .ok () final) :
    PositiveRecursiveApplicationTrace id us args groups rootAddrs methods
      initial final := by
  unfold checkPositiveRecursiveApplication at hrun
  generalize hgroup :
      groups.find? (fun candidate => candidate.addrs.contains id.addr) =
        group? at hrun
  cases group? with
  | none =>
      simp only at hrun
      change EStateM.Result.error _ initial = .ok () final at hrun
      contradiction
  | some group =>
      simp only at hrun
      simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
        at hrun
      rw [runTcBind] at hrun
      generalize hlookup : TcM.getConst id initial = lookupResult at hrun
      cases lookupResult with
      | error err afterLookup => contradiction
      | ok concrete afterLookup =>
          cases concrete with
          | indc name levelParams lvls params indices isUnsafe block memberIdx
              ty ctors leanAll =>
              simp only at hrun
              exact ⟨group,
                .indc name levelParams lvls params indices isUnsafe block
                  memberIdx ty ctors leanAll,
                params.toNat, indices.toNat, lvls.toNat, afterLookup, hgroup,
                hlookup, ⟨rfl, rfl, rfl⟩,
                checkPositiveRecursiveApplicationHeader_success hrun⟩
          | defn name levelParams kind safety hints lvls ty value leanAll block =>
              change EStateM.Result.error _ afterLookup = .ok () final at hrun
              contradiction
          | recr name levelParams k isUnsafe lvls params indices motives minors
              block memberIdx ty rules leanAll =>
              change EStateM.Result.error _ afterLookup = .ok () final at hrun
              contradiction
          | axio name levelParams isUnsafe lvls ty =>
              change EStateM.Result.error _ afterLookup = .ok () final at hrun
              contradiction
          | quot name levelParams kind lvls ty =>
              change EStateM.Result.error _ afterLookup = .ok () final at hrun
              contradiction
          | ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
              change EStateM.Result.error _ afterLookup = .ok () final at hrun
              contradiction

/-- Strengthen the complete operational trace to the selected-family logical
valid-inductive-application invariant. -/
theorem PositiveRecursiveApplicationTrace.valid
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {groups : Array (PositivityGroup m)} {rootAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (trace : PositiveRecursiveApplicationTrace id us args groups rootAddrs
      methods initial final) :
    ValidPositiveRecursiveApplication id us args groups rootAddrs methods
      initial final := by
  rcases trace with
    ⟨group, concrete, nParams, nIndices, levels, afterLookup, hgroup,
      hlookup, hheader, happlication⟩
  exact ⟨group, concrete, nParams, nIndices, levels, afterLookup, hgroup,
    hlookup, hheader,
    PositiveRecursiveApplicationHeaderTrace.valid happlication⟩

/-- Successful production occurrence validation establishes the complete
Ix-side valid-inductive-application invariant without an oracle premise. -/
theorem checkPositiveRecursiveApplication_valid
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {groups : Array (PositivityGroup m)} {rootAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkPositiveRecursiveApplication id us args groups rootAddrs).run
      methods initial = .ok () final) :
    ValidPositiveRecursiveApplication id us args groups rootAddrs methods
      initial final :=
  PositiveRecursiveApplicationTrace.valid
    (checkPositiveRecursiveApplication_success hrun)

/-- The logical resolved-header invariant is execution-complete: its retained
parameter run and pure guards reconstruct the exact production call.  This is
the converse of `checkPositiveRecursiveApplicationHeader_valid`, and is useful
when a larger retained traversal must align its final state with another exact
production execution. -/
theorem ValidPositiveRecursiveApplicationHeader.run
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {group : PositivityGroup m} {rootAddrs : Array Address}
    {nParams nIndices levels : Nat} {methods : Methods m}
    {initial final : TcState m}
    (valid : ValidPositiveRecursiveApplicationHeader id us args group
      rootAddrs nParams nIndices levels methods initial final) :
    (checkPositiveRecursiveApplicationHeader id us args group rootAddrs
      nParams nIndices levels).run methods initial = .ok () final := by
  rcases valid with
    ⟨hargs, hus, huniverses, hparams, afterParameters, hparameterRun,
      _comparisonTrace, hindependent, hfinal⟩
  subst final
  have hpreconditions :
      checkPositiveRecursiveApplicationPreconditions us args group nParams
        nIndices levels = .ok () :=
    checkPositiveRecursiveApplicationPreconditions_success_iff.mpr
      ⟨hargs, hus,
        (positiveUniverseArgumentsAgree_eq_true_iff group us).mpr huniverses,
        hparams⟩
  have hindependent' :
      positiveIndicesIndependent args nParams rootAddrs = true :=
    (positiveIndicesIndependent_eq_true_iff args nParams rootAddrs).mpr
      hindependent
  unfold checkPositiveRecursiveApplicationHeader
  simp only [hpreconditions]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((checkPositiveParameters id args group.params nParams).run methods) _
      initial = _
  unfold EStateM.bind
  rw [hparameterRun]
  simp [hindependent']
  rfl

/-- `ValidPositiveRecursiveApplication` retains enough physical selection and
state-threaded evidence to replay the complete production validator exactly.
In particular, consumers may use determinism to align the final state of a
classified direct positivity branch with a separately named enclosing run. -/
theorem ValidPositiveRecursiveApplication.run
    {id : KId m} {us : Array (KUniv m)} {args : Array (KExpr m)}
    {groups : Array (PositivityGroup m)} {rootAddrs : Array Address}
    {methods : Methods m} {initial final : TcState m}
    (valid : ValidPositiveRecursiveApplication id us args groups rootAddrs
      methods initial final) :
    (checkPositiveRecursiveApplication id us args groups rootAddrs).run
      methods initial = .ok () final := by
  rcases valid with
    ⟨group, concrete, nParams, nIndices, levels, afterLookup, hgroup,
      hlookup, hheader, hvalid⟩
  unfold checkPositiveRecursiveApplication
  simp only [hgroup]
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  rw [runTcBind, hlookup]
  cases concrete with
  | indc name levelParams actualLevels actualParams actualIndices isUnsafe
      block memberIdx ty ctors leanAll =>
      rcases hheader with ⟨rfl, rfl, rfl⟩
      exact ValidPositiveRecursiveApplicationHeader.run hvalid
  | defn => contradiction
  | recr => contradiction
  | axio => contradiction
  | quot => contradiction
  | ctor => contradiction

end RecM
end Ix.Tc
