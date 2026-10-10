import Ix.CompileCert.Opt.O11aFields

/-!
Actual `sizeOfInstanceE` reads and the corresponding local delta/beta steps.
SOURCE-ONLY / UNCOMPILED. The witness retains the exact Boolean guards and
raw universe arrays used by the implementation. In particular, a successful
hash comparison is not promoted to structural Name/Level or erased equality.
The local delta hypotheses are explicit environment-rule obligations; this
leaf does not discharge the SizeOf projection rule, callback faithfulness,
or the original O11aFaithful endpoint.
-/

namespace Ix.CompileCert.Opt.O11aInstanceReads

open Ix (Name Level Expr ConstantInfo DefinitionVal)
open Ix.Compile.Canon (getAppFnArgs)
open Ix.Compile.Pass.Opt
open Ix.CompileCert.Conv
open Ix.CompileCert.Canon (except_bind_ok)
open Ix.CompileCert.Opt.O11aFields (side_ok)
open Ix.CompileCert.Opt.FreshFVarsProof

private theorem need_success {test : Bool} {cause : String} {out : Unit}
    (run : O11aM.need test cause = .ok out) : test = true := by
  cases test <;> cases run <;> rfl

private theorem defn_match_some {info : ConstantInfo} {value : DefinitionVal}
    (read : (match info with | .defnInfo value => some value | _ => none) = some value) :
    info = .defnInfo value := by
  cases info <;> cases read <;> rfl

private theorem defn_lookup_some {info : Option ConstantInfo} {value : DefinitionVal}
    (read : (match info with | some (.defnInfo value) => some value | _ => none) = some value) :
    info = some (.defnInfo value) := by
  cases info with
  | none => cases read
  | some info => exact congrArg some (defn_match_some read)

private theorem need_pair_loop_all {α β : Type} (check : α → β → Bool) (cause : String) :
    ∀ (values : List (α × β)),
      forIn values () (fun (left, right) _ => do
        O11aM.need (check left right) cause
        pure (ForInStep.yield ())) = .ok () →
      ∀ value ∈ values, check value.1 value.2 = true
  | [], _ => by intro value member; cases member
  | first :: rest, run => by
      rcases first with ⟨left, right⟩
      rw [List.forIn_cons] at run
      obtain ⟨step, stepRun, restRun⟩ := except_bind_ok.1 run
      obtain ⟨_, checked, stepRun⟩ := except_bind_ok.1 stepRun
      cases stepRun
      intro value member
      rcases List.mem_cons.1 member with equal | later
      · subst value
        exact need_success checked
      · exact need_pair_loop_all check cause rest restRun value later

/-- Data read by the actual callback, with precisely its existing checks.
No semantic conclusion is hidden in this record. Unchecked universe arrays
are retained, and the recursor/telescope checks remain their actual Booleans. -/
structure InstanceRead (env : OptEnv) (target : Name) (telescope : Array Expr)
    (answer : Name × Level) where
  instanceValue : DefinitionVal
  instanceHead : Expr
  instanceArgs : Array Expr
  constructorName : Name
  constructorLevels : Array Level
  functionName : Name
  functionValue : DefinitionVal
  functionBody : Expr
  recursorHead : Expr
  recursorArgs : Array Expr
  targetRun : sizeOfTargetE env target = .ok ()
  returnedName : answer.1 = Name.mkStr target "_sizeOf_inst"
  instanceRead : env.const? (Name.mkStr target "_sizeOf_inst") = some (.defnInfo instanceValue)
  instanceMonomorphic : instanceValue.cnst.levelParams.isEmpty = true
  instanceSpine : getAppFnArgs instanceValue.value = (instanceHead, instanceArgs)
  constructorRead : (match instanceHead with
    | .const name levels _ => some (name, levels)
    | _ => none) = some (constructorName, constructorLevels)
  constructorCheck : (constructorName == nSizeOfMk) = true
  instanceArity : instanceArgs.size = 2
  returnedLevel : constructorLevels[0]? = some answer.2
  targetCheck : (match instanceArgs[0]! with
    | .const name _ _ => name == target
    | _ => false) = true
  functionRead : (match instanceArgs[1]! with
    | .const name _ _ => some name
    | .lam _ _ (.app (.const name _ _) (.bvar 0 _) _) _ _ => some name
    | _ => none) = some functionName
  functionLookup : env.const? functionName = some (.defnInfo functionValue)
  lambdaRead : (match functionValue.value with
    | .lam _ _ body _ _ => some body
    | _ => none) = some functionBody
  recursorSpine : getAppFnArgs functionBody = (recursorHead, recursorArgs)
  recursorCheck : (match recursorHead with
    | .const name _ _ => name == Name.mkStr target "rec"
    | _ => false) = true
  argumentCheck : (match recursorArgs.back? with
    | some (.bvar 0 _) => true
    | _ => false) = true
  recursorArity : recursorArgs.size = telescope.size + 1
  telescopeChecks : ∀ pair ∈ (recursorArgs.extract 0 telescope.size).zip telescope,
    Ix.Compile.Image.alphaEq pair.1 pair.2 = true

/-- Every witness fact is extracted from the successful actual callback;
there is no alternate callback or strengthened source-side checker. -/
theorem sizeOfInstanceE_success (env : OptEnv) (target : Name) (telescope : Array Expr)
    (answer : Name × Level) (run : sizeOfInstanceE env target telescope = .ok answer) :
    Nonempty (InstanceRead env target telescope answer) := by
  unfold sizeOfInstanceE at run
  obtain ⟨token, targetRun, run⟩ := except_bind_ok.1 run
  cases token
  obtain ⟨info, instanceFound, run⟩ := except_bind_ok.1 run
  obtain ⟨instanceValue, instanceShape, run⟩ := except_bind_ok.1 run
  obtain ⟨_, monomorphic, run⟩ := except_bind_ok.1 run
  generalize instanceSpine : getAppFnArgs instanceValue.value = spine at run
  rcases spine with ⟨instanceHead, instanceArgs⟩
  dsimp only at run
  obtain ⟨headInfo, constructorRead, run⟩ := except_bind_ok.1 run
  rcases headInfo with ⟨constructorName, constructorLevels⟩
  dsimp only at run
  obtain ⟨_, constructorGuard, run⟩ := except_bind_ok.1 run
  obtain ⟨level, levelRead, run⟩ := except_bind_ok.1 run
  obtain ⟨_, targetGuard, run⟩ := except_bind_ok.1 run
  obtain ⟨functionName, functionRead, run⟩ := except_bind_ok.1 run
  obtain ⟨functionValue, functionLookup, run⟩ := except_bind_ok.1 run
  obtain ⟨functionBody, lambdaRead, run⟩ := except_bind_ok.1 run
  generalize recursorSpine : getAppFnArgs functionBody = spine at run
  rcases spine with ⟨recursorHead, recursorArgs⟩
  dsimp only at run
  obtain ⟨_, recursorGuard, run⟩ := except_bind_ok.1 run
  obtain ⟨_, argumentGuard, run⟩ := except_bind_ok.1 run
  obtain ⟨_, arityGuard, run⟩ := except_bind_ok.1 run
  obtain ⟨token, loopRun, run⟩ := except_bind_ok.1 run
  cases token
  have answerEq : answer = (Name.mkStr target "_sizeOf_inst", level) :=
    (Except.ok.inj run).symm
  cases answerEq
  have constructorChecks := Bool.and_eq_true_iff.1 (need_success constructorGuard)
  refine ⟨{
    instanceValue := instanceValue, instanceHead := instanceHead, instanceArgs := instanceArgs,
    constructorName := constructorName, constructorLevels := constructorLevels,
    functionName := functionName, functionValue := functionValue, functionBody := functionBody,
    recursorHead := recursorHead, recursorArgs := recursorArgs,
    targetRun := targetRun, returnedName := rfl,
    instanceRead := (side_ok instanceFound).trans
      (congrArg some (defn_match_some (side_ok instanceShape))),
    instanceMonomorphic := need_success monomorphic,
    instanceSpine := instanceSpine, constructorRead := side_ok constructorRead,
    constructorCheck := constructorChecks.1,
    instanceArity := beq_iff_eq.1 constructorChecks.2,
    returnedLevel := side_ok levelRead, targetCheck := need_success targetGuard,
    functionRead := side_ok functionRead, functionLookup := defn_lookup_some (side_ok functionLookup),
    lambdaRead := side_ok lambdaRead, recursorSpine := recursorSpine,
    recursorCheck := need_success recursorGuard, argumentCheck := need_success argumentGuard,
    recursorArity := beq_iff_eq.1 (need_success arityGuard), telescopeChecks := ?_ }⟩
  rw [← Array.forIn_toList] at loopRun
  intro pair member
  exact need_pair_loop_all Ix.Compile.Image.alphaEq _ _
    loopRun pair (Array.mem_toList_iff.2 member)

theorem sizeOfInstanceE_returnedName (env : OptEnv) (target : Name) (telescope : Array Expr)
    (answer : Name × Level) (run : sizeOfInstanceE env target telescope = .ok answer) :
    answer.1 = Name.mkStr target "_sizeOf_inst" := by
  obtain ⟨read⟩ := sizeOfInstanceE_success env target telescope answer run
  exact read.returnedName

/-- The selected argument may be a constant or the exact single-binder
wrapper accepted by the callback. Its original universe arguments remain. -/
def FunctionSpelling (argument : Expr) (name : Name) (levels : Array Level) : Prop :=
  er argument = .const name levels ∨
    ∃ domain, er argument = .lam domain (.app (.const name levels) (.bvar 0))

theorem functionRead_spelling (argument : Expr) (name : Name)
    (read : (match argument with
      | .const name _ _ => some name
      | .lam _ _ (.app (.const name _ _) (.bvar 0 _) _) _ _ => some name
      | _ => none) = some name) :
    ∃ levels, FunctionSpelling argument name levels := by
  cases argument with
  | const selected levels hash =>
      cases read
      exact ⟨levels, .inl rfl⟩
  | lam binder domain body info hash =>
      cases body with
      | app fn value hash =>
          cases fn with
          | const selected levels hash =>
              cases value with
              | bvar index hash =>
                  cases index with
                  | zero =>
                      cases read
                      exact ⟨levels, .inr ⟨er domain, rfl⟩⟩
                  | succ index => cases read
              | _ => cases read
          | _ => cases read
      | _ => cases read
  | _ => cases read

theorem functionSpelling_apply (Γ : Env) (argument : Expr) (name : Name)
    (levels : Array Level) (spelling : FunctionSpelling argument name levels) (field : Tm) :
    Conv Γ (.app (er argument) field) (.app (.const name levels) field) := by
  rcases spelling with direct | ⟨domain, wrapper⟩
  · rw [direct]
    exact .refl _
  · rw [wrapper]
    have beta := Conv.step (Γ := Γ) (Step.beta domain (.app (.const name levels) (.bvar 0)) field)
    simpa only [Tm.inst, ↓reduceIte, Tm.lift_zero] using beta

/-- A local beta step for the exact lambda read from a source definition.
The explicit delta rule must come from the actual conversion environment. -/
theorem functionBody_beta (Γ : Env) (name : Name) (levels : Array Level)
    (value : DefinitionVal) (body : Expr)
    (read : (match value.value with | .lam _ _ body _ _ => some body | _ => none) = some body)
    (delta : Γ.ax (.const name levels) (er value.value)) (field : Tm) :
    Conv Γ (.app (.const name levels) field) (Tm.inst field 0 (er body)) := by
  have lambda : ∃ domain, er value.value = .lam domain (er body) := by
    generalize value.value = term at read ⊢
    cases term with
    | lam binder domain inner info hash =>
        cases read
        exact ⟨er domain, rfl⟩
    | _ => cases read
  obtain ⟨domain, lambda⟩ := lambda
  rw [lambda] at delta
  exact .trans (.app (.step (.ax delta)) (.refl field))
    (.step (.beta domain (er body) field))

/-- Actual selected function spelling, followed by its actual source lambda.
This derives the exact instantiated body; it does not replace its telescope
using the callback's hash-based comparison. -/
theorem actual_function_application (env : OptEnv) (target : Name) (telescope : Array Expr)
    (answer : Name × Level) (read : InstanceRead env target telescope answer) :
    ∃ levels, FunctionSpelling (read.instanceArgs[1]!) read.functionName levels ∧
      ∀ (Γ : Env) (field : Tm),
        Γ.ax (.const read.functionName levels) (er read.functionValue.value) →
        Conv Γ (.app (er (read.instanceArgs[1]!)) field)
          (Tm.inst field 0 (er read.functionBody)) := by
  obtain ⟨levels, spelling⟩ := functionRead_spelling _ _ read.functionRead
  refine ⟨levels, spelling, ?_⟩
  intro Γ field delta
  exact (functionSpelling_apply Γ _ _ levels spelling field).trans
    (functionBody_beta Γ _ levels _ _ read.lambdaRead delta field)

/-- The exact result after beta uses substitution in every original spine
argument. Open telescope arguments and raw universe arrays are retained. -/
theorem instanceBody_inst_spine (env : OptEnv) (target : Name) (telescope : Array Expr)
    (answer : Name × Level) (read : InstanceRead env target telescope answer) (field : Tm) :
    Tm.inst field 0 (er read.functionBody) =
      Tm.appN (Tm.inst field 0 (er read.recursorHead))
        (read.recursorArgs.toList.map (fun argument => Tm.inst field 0 (er argument))) := by
  rw [er_getAppFnArgs, read.recursorSpine, Tm.inst_appN, List.map_map]

/-- The checked final argument and arity determine the exact source prefix.
This uses the callback's actual array, without identifying its checked prefix
with the caller's telescope. -/
theorem recursorArgs_last (env : OptEnv) (target : Name) (telescope : Array Expr)
    (answer : Name × Level) (read : InstanceRead env target telescope answer) :
    ∃ hash, read.recursorArgs =
      (read.recursorArgs.extract 0 telescope.size).push (.bvar 0 hash) := by
  have checked := read.argumentCheck
  have last : ∃ hash, read.recursorArgs.back? = some (.bvar 0 hash) := by
    generalize read.recursorArgs.back? = value at checked ⊢
    cases value with
    | none => cases checked
    | some argument =>
        cases argument with
        | bvar index hash =>
            cases index with
            | zero => exact ⟨hash, rfl⟩
            | succ index => cases checked
        | _ => cases checked
  obtain ⟨hash, last⟩ := last
  rw [Array.back?_eq_getElem?, read.recursorArity, Nat.add_sub_cancel] at last
  obtain ⟨bound, lastRead⟩ := Array.getElem_of_getElem? last
  refine ⟨hash, ?_⟩
  calc
    read.recursorArgs = read.recursorArgs.extract 0 (telescope.size + 1) :=
      (Array.extract_eq_self_of_le (Nat.le_of_eq read.recursorArity)).symm
    _ = (read.recursorArgs.extract 0 telescope.size).push (.bvar 0 hash) := by
      rw [Array.extract_succ_right (Nat.zero_lt_succ telescope.size) bound, lastRead]

/-- Beta reduces the final `bvar 0` to the caller's field. The exact source
recursor name and universes remain, and substitution still acts on every
source-prefix argument. No equality with the caller's telescope is inferred. -/
theorem instanceBody_inst_last (env : OptEnv) (target : Name) (telescope : Array Expr)
    (answer : Name × Level) (read : InstanceRead env target telescope answer) :
    ∃ name levels, (name == Name.mkStr target "rec") = true ∧
      ∀ field : Tm, Tm.inst field 0 (er read.functionBody) =
        .app (Tm.appN (.const name levels)
          ((read.recursorArgs.extract 0 telescope.size).toList.map
            (fun argument => Tm.inst field 0 (er argument)))) field := by
  have checked := read.recursorCheck
  have head : ∃ name levels, er read.recursorHead = .const name levels ∧
      (name == Name.mkStr target "rec") = true := by
    generalize read.recursorHead = value at checked ⊢
    cases value with
    | const name levels hash => exact ⟨name, levels, rfl, checked⟩
    | _ => cases checked
  obtain ⟨name, levels, head, checked⟩ := head
  obtain ⟨hash, last⟩ := recursorArgs_last env target telescope answer read
  refine ⟨name, levels, checked, ?_⟩
  intro field
  have mapped := congrArg
    (fun args : Array Expr => args.toList.map (fun argument => Tm.inst field 0 (er argument))) last
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
    er, Tm.inst, ↓reduceIte, Tm.lift_zero] at mapped
  rw [instanceBody_inst_spine env target telescope answer read field, head,
    mapped, Tm.appN_concat]

/-- A successful run exposes the exact semantic function application after
its local definition rule and beta steps. The source-prefix substitution is
retained; this is not the callback-to-occurrence conversion endpoint. -/
theorem sizeOfInstanceE_local_function (env : OptEnv) (target : Name)
    (telescope : Array Expr) (answer : Name × Level)
    (run : sizeOfInstanceE env target telescope = .ok answer) :
    ∃ read : InstanceRead env target telescope answer,
      ∃ functionLevels recursorName recursorLevels,
        FunctionSpelling (read.instanceArgs[1]!) read.functionName functionLevels ∧
        (recursorName == Name.mkStr target "rec") = true ∧
        ∀ (Γ : Env) (field : Tm),
          Γ.ax (.const read.functionName functionLevels) (er read.functionValue.value) →
          Conv Γ (.app (er (read.instanceArgs[1]!)) field)
            (.app (Tm.appN (.const recursorName recursorLevels)
              ((read.recursorArgs.extract 0 telescope.size).toList.map
                (fun argument => Tm.inst field 0 (er argument)))) field) := by
  obtain ⟨read⟩ := sizeOfInstanceE_success env target telescope answer run
  obtain ⟨functionLevels, spelling, functionConv⟩ :=
    actual_function_application env target telescope answer read
  obtain ⟨recursorName, recursorLevels, checked, bodyEq⟩ :=
    instanceBody_inst_last env target telescope answer read
  refine ⟨read, functionLevels, recursorName, recursorLevels, spelling, checked, ?_⟩
  intro Γ field delta
  rw [← bodyEq field]
  exact functionConv Γ field delta

/-- The first actual semantic step of the replacement is the instance's
delta rule, under SizeOf.sizeOf and the caller's field. The selected source
value is used exactly as read; no constructor-name or level check is silently
strengthened to structural equality. -/
theorem sizeOfReplacement_instance_delta (env : OptEnv) (target : Name)
    (telescope : Array Expr) (answer : Name × Level)
    (read : InstanceRead env target telescope answer) (Γ : Env)
    (delta : Γ.ax (.const (Name.mkStr target "_sizeOf_inst") #[]) (er read.instanceValue.value))
    (field : Expr) :
    Conv Γ (er (sizeOfReplacement target answer.1 answer.2 field))
      (.app (.app (.app (.const nSizeOf #[answer.2]) (.const target #[]))
        (er read.instanceValue.value)) (er field)) := by
  rw [er_sizeOfReplacement, read.returnedName]
  exact .app (.app (.refl _) (.step (.ax delta))) (.refl _)

end Ix.CompileCert.Opt.O11aInstanceReads
