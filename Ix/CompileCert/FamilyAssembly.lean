import Ix.CompileCert.FamilySourceChecks

/-! Exact declaration assembly and both modeller outcomes of the real family
reader. Generation remains the existing computation, not an assumed total
or source-correct generator. All reader registration fields are retained. -/

namespace Ix.CompileCert.FamilyAssembly

open Ix Kernel.Reader
open FamilyReader (CtorRow RecRow)

structure Assembly where
  declaration : CDecl
  model : Kernel.Frontend.InModel.BlockRec
  owners : List Kernel.Frontend.ProjRecOwner
  memberNames : List Kernel.Name
  diagnosticName : Kernel.Name

def prepare (nPd : Nat) (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive))
    (ctors : Array CtorRow) (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) : Assembly :=
  let typeInfos : List CInfo := types.toList.map (.indInfo · {})
  let ctorInfos : List CInfo := ctors.toList.map fun (cv, nP, nF) => .ctorInfo cv nP nF
  let recInfos : List CInfo := recs.toList.map fun (cv, r, rules) =>
    let nP := r.params.toNat; let nM := r.motives.toNat
    let nm := r.minors.toNat; let nI := r.indices.toNat
    .recInfo cv (nP + nM + nm + nI) (nP + nM + nm) rules
  let block := typeInfos ++ ctorInfos ++ recInfos
  let memberNames := types.toList.map (·.name)
  let fieldDoms := ctors.toList.flatMap fun (cv, _, _) =>
    (Kernel.Frontend.stripPisAll cv.type).1.map (·.1)
  let isRec := fieldDoms.any fun d => memberNames.any (Kernel.Frontend.occursConstFast · d)
  let isReflexive := fieldDoms.any fun d =>
    let (bs, body) := Kernel.Frontend.stripPisAll d
    !bs.isEmpty && memberNames.any (Kernel.Frontend.headIs · body)
  let ownerTypes := (types.zip tyRecs).toList.zip ctorNames.toList |>.map fun ((cv, (_, ind)), cs) =>
    (cv.name, cv.levelParams, cv.type, ind.params.toNat, ind.indices.toNat, cs, isRec)
  let ownerCtors := ctors.toList.map fun (cv, _, fields) => (cv.name, fields, cv.type)
  let ownerRecs := recs.toList.map fun (cv, r, _) =>
    (cv.name, cv.levelParams, cv.type, r.motives.toNat, r.minors.toNat)
  let model : Kernel.Frontend.InModel.BlockRec :=
    ⟨(types.zip tyRecs).toList.zip ctorNames.toList |>.map fun ((cv, (_, ind)), cs) =>
        { cv, nP := ind.params.toNat, nIdx := ind.indices.toNat, ctors := cs, isRec,
          isReflexive, numNested := FamilyConsistency.numNested types recs },
     ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
     recs.toList.map fun (cv, r, rules) =>
       { cv, nP := r.params.toNat, nM := r.motives.toNat, nm := r.minors.toNat,
         nI := r.indices.toNat, rules }⟩
  ⟨.indDecl block nPd, model, Kernel.Frontend.projRecOwners block ownerTypes ownerCtors ownerRecs,
    memberNames, (types[0]?.map (·.name)).getD .anonymous⟩

def Assembly.result (assembly : Assembly) (generated : List CDecl) : Read :=
  { decls := generated.toArray.push assembly.declaration
    generated := generated.length
    owners := assembly.owners
    blocks := assembly.model.types.map (·.cv.name, assembly.model) }

def Assembly.context (assembly : Assembly) (state : State) : Kernel.Frontend.InModel.Ctx :=
  ⟨fun name => state.constTypes[name]?, fun name => state.heights.getD name 0,
    fun name => if assembly.memberNames.contains name then some assembly.model else state.indBlocks[name]?⟩

def Assembly.run (assembly : Assembly) (state : State) : ReadM Read :=
  if Kernel.Frontend.InModel.wants assembly.model then
    match Kernel.Frontend.InModel.generate (assembly.context state) assembly.model with
    | .error why => declined s!"in-process model of {assembly.diagnosticName}: {why}"
    | .ok generated => pure (assembly.result generated)
  else pure (assembly.result [])

theorem assemble_run (state : State) (nPd : Nat) (types : Array CVal)
    (tyRecs : Array (Nat × Ixon.Inductive)) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) :
    FamilyConsistency.assemble state nPd types tyRecs ctors ctorNames recs =
      (prepare nPd types tyRecs ctors ctorNames recs).run state := rfl

theorem result_fields (assembly : Assembly) (generated : List CDecl) :
    (assembly.result generated).decls.toList = generated ++ [assembly.declaration] ∧
      (assembly.result generated).generated = generated.length ∧
      (assembly.result generated).owners = assembly.owners ∧
      (assembly.result generated).blocks = assembly.model.types.map (·.cv.name, assembly.model) ∧
      (assembly.result generated).projRewrites = 0 := by
  simp [Assembly.result]

theorem run_plain (assembly : Assembly) (state : State)
    (plain : Kernel.Frontend.InModel.wants assembly.model = false) :
    assembly.run state = .ok (assembly.result []) := by
  simp [Assembly.run, plain, pure, Except.pure]

theorem run_generated (assembly : Assembly) (state : State) (generated : List CDecl)
    (needed : Kernel.Frontend.InModel.wants assembly.model = true)
    (ran : Kernel.Frontend.InModel.generate (assembly.context state) assembly.model = .ok generated) :
    assembly.run state = .ok (assembly.result generated) := by
  simp [Assembly.run, needed, ran, pure, Except.pure]

theorem run_declined (assembly : Assembly) (state : State) (reason : String)
    (needed : Kernel.Frontend.InModel.wants assembly.model = true)
    (ran : Kernel.Frontend.InModel.generate (assembly.context state) assembly.model = .error reason) :
    assembly.run state = declined s!"in-process model of {assembly.diagnosticName}: {reason}" := by
  simp [Assembly.run, needed, ran]

/-- Every successful result has the complete production reader fields. In
the modelling branch, the generated prefix comes from the actual computation. -/
theorem run_success (assembly : Assembly) (state : State) (output : Read)
    (ran : assembly.run state = .ok output) :
    ∃ generated, output = assembly.result generated ∧
      ((Kernel.Frontend.InModel.wants assembly.model = false ∧ generated = []) ∨
        (Kernel.Frontend.InModel.wants assembly.model = true ∧
          Kernel.Frontend.InModel.generate (assembly.context state) assembly.model = .ok generated)) := by
  unfold Assembly.run at ran
  cases needed : Kernel.Frontend.InModel.wants assembly.model with
  | false =>
    simp only [needed, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at ran
    exact ⟨[], ran.symm, .inl ⟨rfl, rfl⟩⟩
  | true =>
    simp only [needed, ↓reduceIte] at ran
    cases generated : Kernel.Frontend.InModel.generate (assembly.context state) assembly.model with
    | error reason => simp only [generated, declined] at ran; cases ran
    | ok values =>
      simp only [generated, pure, Except.pure, Except.ok.injEq] at ran
      exact ⟨values, ran.symm, .inr ⟨rfl, rfl⟩⟩

theorem model_type_count (nPd : Nat) (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive))
    (ctors : Array CtorRow) (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) :
    (prepare nPd types tyRecs ctors ctorNames recs).model.types.length =
      min (min types.size tyRecs.size) ctorNames.size := by
  simp [prepare]

theorem model_nested (nPd : Nat) (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive))
    (ctors : Array CtorRow) (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) :
    ∀ entry ∈ (prepare nPd types tyRecs ctors ctorNames recs).model.types,
      entry.numNested = FamilyConsistency.numNested types recs := by
  intro entry present
  simp only [prepare, List.mem_map] at present
  obtain ⟨value, _, rfl⟩ := present
  rfl

theorem wants_false (model : Kernel.Frontend.InModel.BlockRec) (small : model.types.length ≤ 1)
    (plain : ∀ entry ∈ model.types, entry.numNested = 0) : Kernel.Frontend.InModel.wants model = false := by
  have noneNested : model.types.any (·.numNested > 0) = false := by
    apply List.any_eq_false.mpr
    intro entry present
    simp [plain entry present]
  simp [Kernel.Frontend.InModel.wants, Nat.not_lt.mpr small, noneNested]

theorem prepare_plain (nPd : Nat) (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive))
    (ctors : Array CtorRow) (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow)
    (small : types.size ≤ 1) (plain : FamilyConsistency.numNested types recs = 0) :
    Kernel.Frontend.InModel.wants (prepare nPd types tyRecs ctors ctorNames recs).model = false := by
  apply wants_false
  · rw [model_type_count]
    omega
  · intro entry present
    exact (model_nested nPd types tyRecs ctors ctorNames recs entry present).trans plain

theorem assemble_plain (state : State) (nPd : Nat) (types : Array CVal)
    (tyRecs : Array (Nat × Ixon.Inductive)) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow)
    (small : types.size ≤ 1) (plain : FamilyConsistency.numNested types recs = 0) :
    FamilyConsistency.assemble state nPd types tyRecs ctors ctorNames recs =
      .ok ((prepare nPd types tyRecs ctors ctorNames recs).result []) := by
  rw [assemble_run]
  exact run_plain _ state (prepare_plain nPd types tyRecs ctors ctorNames recs small plain)

theorem prepare_mutual (nPd : Nat) (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive))
    (ctors : Array CtorRow) (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow)
    (payloadCount : tyRecs.size = types.size) (nameCount : ctorNames.size = types.size)
    (multiple : 1 < types.size) :
    Kernel.Frontend.InModel.wants (prepare nPd types tyRecs ctors ctorNames recs).model = true := by
  have count : 1 < (prepare nPd types tyRecs ctors ctorNames recs).model.types.length := by
    simpa only [model_type_count, payloadCount, nameCount, Nat.min_self] using multiple
  simp only [Kernel.Frontend.InModel.wants, count, decide_true, Bool.true_or]

theorem prepare_nested (nPd : Nat) (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive))
    (ctors : Array CtorRow) (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow)
    (payloadCount : tyRecs.size = types.size) (nameCount : ctorNames.size = types.size)
    (nonempty : 0 < types.size) (nested : 0 < FamilyConsistency.numNested types recs) :
    Kernel.Frontend.InModel.wants (prepare nPd types tyRecs ctors ctorNames recs).model = true := by
  have count : 0 < (prepare nPd types tyRecs ctors ctorNames recs).model.types.length := by
    simpa only [model_type_count, payloadCount, nameCount, Nat.min_self] using nonempty
  have present : ∃ entry, entry ∈ (prepare nPd types tyRecs ctors ctorNames recs).model.types := by
    cases found : (prepare nPd types tyRecs ctors ctorNames recs).model.types with
    | nil => simp [found] at count
    | cons entry rest => exact ⟨entry, by simp⟩
  obtain ⟨entry, present⟩ := present
  have positive := model_nested nPd types tyRecs ctors ctorNames recs entry present
  have anyNested : (prepare nPd types tyRecs ctors ctorNames recs).model.types.any (·.numNested > 0) = true := by
    apply List.any_eq_true.mpr
    exact ⟨entry, present, by simpa only [positive, decide_eq_true_eq] using nested⟩
  simp only [Kernel.Frontend.InModel.wants, anyNested, Bool.or_true]

private theorem paired_length {α β : Type} {related : α → β → Prop}
    {sources : List α} {targets : List β} (pairs : List.Forall₂ related sources targets) :
    sources.length = targets.length := by
  induction pairs with
  | nil => rfl
  | cons head rest ih => exact congrArg Nat.succ ih

/-- The actual collection relations justify both zips used to prepare the
model's type records; no type is silently lost by a short payload/name array. -/
theorem source_alignment (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (member : MemberReader) (sources : Array (Nat × Ind))
    (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive)) (groups : List (List CtorRow))
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (payloadMeanings : List.Forall₂ (FamilyTypes.Paired member names params) sources.toList tyRecs.toList)
    (ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups) :
    tyRecs.size = types.size ∧ (groups.map fun rows => rows.map (·.1.name)).toArray.size = types.size := by
  have typesCount := FamilySourceChecks.type_count reader owner names params sources types typeMeanings
  have payloadCount : sources.size = tyRecs.size := by simpa using paired_length payloadMeanings
  have groupCount : sources.size = groups.length := by simpa using paired_length ctorMeanings
  constructor
  · omega
  · simp only [List.size_toArray, List.length_map]
    omega

/-- The no-modelling branch follows from source cardinality and nestedness,
with both guard discharge and all reader result fields retained. -/
theorem finish_plain_from_source (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (state : State) (nPd : Nat) (sources : Array (Nat × Ind))
    (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive)) (groups : List (List CtorRow))
    (inputs : Array FamilyRecursors.Input) (rows : Array RecRow)
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups)
    (recMeanings : List.Forall₂ (FamilyRecursors.RowMeaning reader params names) inputs.toList rows.toList)
    (small : sources.size ≤ 1) (plain : FamilySourceChecks.sourceNested sources inputs = 0)
    (valid : ∀ input ∈ inputs, FamilySourceChecks.SourceRowOK reader owner nPd sources
      (FamilyConsistency.expectedK types groups.flatten.toArray (groups.map fun rows => rows.map (·.1.name)).toArray) input) :
    FamilyReader.finish state nPd types tyRecs groups.flatten.toArray
      (groups.map fun rows => rows.map (·.1.name)).toArray rows =
      .ok ((prepare nPd types tyRecs groups.flatten.toArray
        (groups.map fun rows => rows.map (·.1.name)).toArray rows).result []) := by
  rw [FamilySourceChecks.finish_from_source reader owner names params state nPd sources types tyRecs groups inputs rows
    typeMeanings ctorMeanings recMeanings (fun _ => valid)]
  exact assemble_plain state nPd types tyRecs groups.flatten.toArray _ rows
    (by rwa [FamilySourceChecks.type_count reader owner names params sources types typeMeanings])
    (by rwa [FamilySourceChecks.nested_eq reader owner names params sources types typeMeanings inputs rows recMeanings])

theorem prepare_required_from_source (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (member : MemberReader) (nPd : Nat) (sources : Array (Nat × Ind))
    (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive)) (groups : List (List CtorRow))
    (inputs : Array FamilyRecursors.Input) (rows : Array RecRow)
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (payloadMeanings : List.Forall₂ (FamilyTypes.Paired member names params) sources.toList tyRecs.toList)
    (ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups)
    (recMeanings : List.Forall₂ (FamilyRecursors.RowMeaning reader params names) inputs.toList rows.toList)
    (needed : 1 < sources.size ∨ (0 < sources.size ∧ 0 < FamilySourceChecks.sourceNested sources inputs)) :
    Kernel.Frontend.InModel.wants
      (prepare nPd types tyRecs groups.flatten.toArray (groups.map fun rows => rows.map (·.1.name)).toArray rows).model = true := by
  have aligned := source_alignment reader owner names params member sources types tyRecs groups typeMeanings payloadMeanings ctorMeanings
  have count := FamilySourceChecks.type_count reader owner names params sources types typeMeanings
  rcases needed with multiple | ⟨nonempty, nested⟩
  · exact prepare_mutual nPd types tyRecs groups.flatten.toArray _ rows aligned.1 aligned.2 (by rwa [count])
  · exact prepare_nested nPd types tyRecs groups.flatten.toArray _ rows aligned.1 aligned.2 (by rwa [count])
      (by rwa [FamilySourceChecks.nested_eq reader owner names params sources types typeMeanings inputs rows recMeanings])

/-- Required source modelling reaches the unchanged generator with its exact
context. Both successful prefixes and declines are retained in the equation;
generation termination and correctness remain separate obligations. -/
theorem finish_model_from_source (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (member : MemberReader) (state : State) (nPd : Nat) (sources : Array (Nat × Ind))
    (types : Array CVal) (tyRecs : Array (Nat × Ixon.Inductive)) (groups : List (List CtorRow))
    (inputs : Array FamilyRecursors.Input) (rows : Array RecRow)
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (payloadMeanings : List.Forall₂ (FamilyTypes.Paired member names params) sources.toList tyRecs.toList)
    (ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups)
    (recMeanings : List.Forall₂ (FamilyRecursors.RowMeaning reader params names) inputs.toList rows.toList)
    (needed : 1 < sources.size ∨ (0 < sources.size ∧ 0 < FamilySourceChecks.sourceNested sources inputs))
    (valid : FamilySourceChecks.sourceNested sources inputs = 0 → ∀ input ∈ inputs,
      FamilySourceChecks.SourceRowOK reader owner nPd sources
        (FamilyConsistency.expectedK types groups.flatten.toArray (groups.map fun rows => rows.map (·.1.name)).toArray) input) :
    let assembly := prepare nPd types tyRecs groups.flatten.toArray (groups.map fun rows => rows.map (·.1.name)).toArray rows
    FamilyReader.finish state nPd types tyRecs groups.flatten.toArray
      (groups.map fun rows => rows.map (·.1.name)).toArray rows =
      match Kernel.Frontend.InModel.generate (assembly.context state) assembly.model with
      | .error reason => declined s!"in-process model of {assembly.diagnosticName}: {reason}"
      | .ok generated => .ok (assembly.result generated) := by
  dsimp only
  rw [FamilySourceChecks.finish_from_source reader owner names params state nPd sources types tyRecs groups inputs rows
    typeMeanings ctorMeanings recMeanings valid, assemble_run]
  have required := prepare_required_from_source reader owner names params member nPd sources types tyRecs groups inputs rows
    typeMeanings payloadMeanings ctorMeanings recMeanings needed
  simp only [Assembly.run, required, ↓reduceIte]
  rfl

end Ix.CompileCert.FamilyAssembly
