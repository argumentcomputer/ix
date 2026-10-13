import Ix.CompileCert.FamilyCollection

/-! The actual family finalizer's consistency conditions. Generation remains
the existing modeller computation; it is not assumed total by these proofs. -/

namespace Ix.CompileCert.FamilyConsistency

open Ix Kernel.Reader
open FamilyReader (CtorRow RecRow)

def numNested (types : Array CVal) (recs : Array RecRow) : Nat :=
  match recs[0]? with
  | some (_, r, _) => r.motives.toNat - types.size
  | none => 0

def expectedK (types : Array CVal) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) : Option Bool :=
  match types.toList, ctorNames.toList, ctors.toList with
  | [ty], [[_]], [(_, _, fields)] =>
    match ty.type.piResult with
    | .sort level => some (fields == 0 && Kernel.Level.isEquiv level .zero == some true)
    | _ => none
  | _, _, _ => some false

theorem expectedK_nonsingleton (types : Array CVal) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (notOne : types.size ≠ 1) :
    expectedK types ctors ctorNames = some false := by
  rcases types with ⟨types⟩
  cases types with
  | nil => rfl
  | cons type rest =>
    cases rest with
    | nil => exact False.elim (notOne rfl)
    | cons other rest => rfl

def checks (nPd : Nat) (types : Array CVal) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) : ReadM Unit := do
  unless numNested types recs != 0 do
    for (cv, r, _) in recs do
      unless r.params.toNat == nPd do
        malformed s!"recursor {cv.name} declares {r.params} parameters; the block declares {nPd}"
      unless r.motives.toNat == types.size do
        malformed s!"recursor {cv.name} declares {r.motives} motives; the block has {types.size} types"
      unless r.minors.toNat == ctors.size do
        malformed s!"recursor {cv.name} declares {r.minors} minor premises; the block has {ctors.size} constructors"
      if let some kE := expectedK types ctors ctorNames then
        unless r.k == kE do
          malformed s!"recursor {cv.name} declares k := {r.k}; the generated recursor is{if kE then "" else " not"} K-like"
      if let .str T "rec" := cv.name then
        for ty in types do
          if ty.name == T then
            if let some n := ty.type.piSortTeleLen? then
              unless nPd + r.indices.toNat == n do
                malformed s!"recursor {cv.name} declares {r.indices} indices; {T} has {n - nPd}"

/-- The unchanged assembly/model computation after consistency checks. -/
def assemble (st : State) (nPd : Nat) (types : Array CVal)
    (tyRecs : Array (Nat × Ixon.Inductive)) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) : ReadM Read := do
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
  let owners := Kernel.Frontend.projRecOwners block ownerTypes ownerCtors ownerRecs
  let b : Kernel.Frontend.InModel.BlockRec :=
    ⟨(types.zip tyRecs).toList.zip ctorNames.toList |>.map fun ((cv, (_, ind)), cs) =>
        { cv, nP := ind.params.toNat, nIdx := ind.indices.toNat, ctors := cs, isRec,
          isReflexive, numNested := numNested types recs },
     ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
     recs.toList.map fun (cv, r, rules) =>
       { cv, nP := r.params.toNat, nM := r.motives.toNat, nm := r.minors.toNat,
         nI := r.indices.toNat, rules }⟩
  let blocks := b.types.map (·.cv.name, b)
  let decl := Kernel.Declaration.indDecl block nPd
  if Kernel.Frontend.InModel.wants b then
    let ctx : Kernel.Frontend.InModel.Ctx :=
      ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0,
       fun n => if memberNames.contains n then some b else st.indBlocks[n]?⟩
    match Kernel.Frontend.InModel.generate ctx b with
    | .error why => declined s!"in-process model of {(types[0]?.map (·.name)).getD .anonymous}: {why}"
    | .ok gen => pure { decls := gen.toArray.push decl, generated := gen.length, owners, blocks }
  else
    pure { decls := #[decl], owners, blocks }

theorem finish_run (st : State) (nPd : Nat) (types : Array CVal)
    (tyRecs : Array (Nat × Ixon.Inductive)) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) :
    FamilyReader.finish st nPd types tyRecs ctors ctorNames recs = (do
      checks nPd types ctors ctorNames recs
      assemble st nPd types tyRecs ctors ctorNames recs) := by
  cases first : recs[0]? with
  | none =>
    simp only [FamilyReader.finish, checks, assemble, numNested, first, show ((0 : Nat) != 0) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, expectedK, bind_assoc, pure_bind]
    rfl
  | some row =>
    rcases row with ⟨cv, recursor, rules⟩
    cases nested : recursor.motives.toNat - types.size != 0 <;>
      simp only [FamilyReader.finish, checks, assemble, numNested, first, nested,
        Bool.false_eq_true, ↓reduceIte, expectedK, bind_assoc, pure_bind]
    all_goals rfl

def indexStep (nPd : Nat) (cv : CVal) (r : Ixon.Recursor) (parent : Kernel.Name)
    (ty : CVal) (state : PUnit) : ReadM (ForInStep PUnit) := do
  if ty.name == parent then
    if let some n := ty.type.piSortTeleLen? then
      unless nPd + r.indices.toNat == n do
        malformed s!"recursor {cv.name} declares {r.indices} indices; {parent} has {n - nPd}"
  pure (.yield state)

def rowStep (nPd : Nat) (types : Array CVal) (nCtors : Nat) (k : Option Bool)
    (row : RecRow) (state : PUnit) : ReadM (ForInStep PUnit) := do
  let (cv, r, _) := row
  unless r.params.toNat == nPd do
    malformed s!"recursor {cv.name} declares {r.params} parameters; the block declares {nPd}"
  unless r.motives.toNat == types.size do
    malformed s!"recursor {cv.name} declares {r.motives} motives; the block has {types.size} types"
  unless r.minors.toNat == nCtors do
    malformed s!"recursor {cv.name} declares {r.minors} minor premises; the block has {nCtors} constructors"
  if let some kE := k then
    unless r.k == kE do
      malformed s!"recursor {cv.name} declares k := {r.k}; the generated recursor is{if kE then "" else " not"} K-like"
  if let .str parent "rec" := cv.name then
    let _ ← forIn types PUnit.unit (indexStep nPd cv r parent)
    pure ()
  pure (.yield state)

theorem checks_run (nPd : Nat) (types : Array CVal) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow) :
    checks nPd types ctors ctorNames recs = (do
      unless numNested types recs != 0 do
        let _ ← forIn recs PUnit.unit (rowStep nPd types ctors.size (expectedK types ctors ctorNames))
        pure ()) := by
  unfold checks
  rfl

structure RowOK (nPd : Nat) (types : Array CVal) (nCtors : Nat) (k : Option Bool) (row : RecRow) : Prop where
  parameters : row.2.1.params.toNat = nPd
  motives : row.2.1.motives.toNat = types.size
  minors : row.2.1.minors.toNat = nCtors
  kValue : ∀ value, k = some value → row.2.1.k = value
  indices : ∀ parent, row.1.name = .str parent "rec" → ∀ ty ∈ types,
    ty.name = parent → ∀ n, ty.type.piSortTeleLen? = some n → nPd + row.2.1.indices.toNat = n

private theorem forIn_skip_list {α : Type} (items : List α) (initial : PUnit)
    (body : α → PUnit → ReadM (ForInStep PUnit))
    (each : ∀ item ∈ items, ∀ state, body item state = .ok (.yield state)) :
    forIn items initial body = .ok initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    rw [List.forIn_cons, each item (by simp) initial]
    exact ih initial (fun item present => each item (by simp [present]))

private theorem forIn_skip {α : Type} (items : Array α) (initial : PUnit)
    (body : α → PUnit → ReadM (ForInStep PUnit))
    (each : ∀ item ∈ items, ∀ state, body item state = .ok (.yield state)) :
    forIn items initial body = .ok initial := by
  rw [← Array.forIn_toList]
  exact forIn_skip_list items.toList initial body (fun item present => each item (by simpa using present))

theorem index_step (nPd : Nat) (cv : CVal) (r : Ixon.Recursor) (parent : Kernel.Name)
    (ty : CVal) (state : PUnit)
    (valid : ty.name = parent → ∀ n, ty.type.piSortTeleLen? = some n → nPd + r.indices.toNat = n) :
    indexStep nPd cv r parent ty state = .ok (.yield state) := by
  unfold indexStep
  by_cases same : ty.name = parent
  · simp only [same, beq_self_eq_true, ↓reduceIte]
    cases found : ty.type.piSortTeleLen? with
    | none => rfl
    | some n => simp [valid same n found, pure, Except.pure]
  · simp [same, pure, Except.pure]

theorem row_step (nPd : Nat) (types : Array CVal) (nCtors : Nat) (k : Option Bool)
    (row : RecRow) (state : PUnit) (valid : RowOK nPd types nCtors k row) :
    rowStep nPd types nCtors k row state = .ok (.yield state) := by
  have loop : ∀ parent, row.1.name = .str parent "rec" →
      forIn types PUnit.unit (indexStep nPd row.1 row.2.1 parent) = .ok PUnit.unit := by
    intro parent named
    exact forIn_skip types PUnit.unit _ (fun ty present state =>
      index_step nPd row.1 row.2.1 parent ty state (valid.indices parent named ty present))
  have tail : (do
      if let .str parent "rec" := row.1.name then
        let _ ← forIn types PUnit.unit (indexStep nPd row.1 row.2.1 parent)
        pure ()
      pure (.yield state)) = (.ok (.yield state) : ReadM (ForInStep PUnit)) := by
    cases named : row.1.name with
    | anonymous => rfl
    | num parent value => rfl
    | str parent suffix =>
      by_cases isRec : suffix = "rec"
      · subst suffix
        change (forIn types PUnit.unit (indexStep nPd row.1 row.2.1 parent) >>= fun _ =>
          pure (ForInStep.yield state)) = .ok (.yield state)
        rw [loop parent named]
        rfl
      · simp [isRec, pure, Except.pure]
  unfold rowStep
  simp only [valid.parameters, valid.motives, valid.minors, beq_self_eq_true, ↓reduceIte]
  cases kFound : k with
  | none => exact tail
  | some value =>
    simp only [valid.kValue value kFound, beq_self_eq_true, ↓reduceIte]
    exact tail

theorem checks_succeed (nPd : Nat) (types : Array CVal) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow)
    (valid : numNested types recs = 0 → ∀ row ∈ recs, RowOK nPd types ctors.size (expectedK types ctors ctorNames) row) :
    checks nPd types ctors ctorNames recs = .ok () := by
  rw [checks_run]
  by_cases nested : numNested types recs = 0
  · have loop := forIn_skip recs PUnit.unit (rowStep nPd types ctors.size (expectedK types ctors ctorNames))
      (fun row present state => row_step nPd types ctors.size (expectedK types ctors ctorNames) row state (valid nested row present))
    simp [nested, loop, bind, Except.bind, pure, Except.pure]
  · simp [nested, pure, Except.pure]

theorem finish_eq_assemble (st : State) (nPd : Nat) (types : Array CVal)
    (tyRecs : Array (Nat × Ixon.Inductive)) (ctors : Array CtorRow)
    (ctorNames : Array (List Kernel.Name)) (recs : Array RecRow)
    (valid : numNested types recs = 0 → ∀ row ∈ recs, RowOK nPd types ctors.size (expectedK types ctors ctorNames) row) :
    FamilyReader.finish st nPd types tyRecs ctors ctorNames recs =
      assemble st nPd types tyRecs ctors ctorNames recs := by
  rw [finish_run, checks_succeed nPd types ctors ctorNames recs valid]
  rfl

end Ix.CompileCert.FamilyConsistency
