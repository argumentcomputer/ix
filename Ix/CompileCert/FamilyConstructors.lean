import Ix.CompileCert.FamilyTypes

/-! Actual constructor-row traversal, deriving the reader's guards from
source positions, safety and syntactic telescope shape. -/

namespace Ix.CompileCert.FamilyConstructors

open Ix Kernel.Reader

def telescope : Expr → Nat
  | .forallE _ _ body _ _ => telescope body + 1
  | .mdata _ body _ => telescope body
  | _ => 0

theorem related_telescope (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Expr) (target : Kernel.Expr)
    (related : ExpressionState.Related names sourceParams params source target) :
    piTeleLen target = telescope source := by
  induction related <;> simp_all [telescope, piTeleLen]

def ctorStep (reader : Ctx) (owner : Address) (index : Nat) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (nPd : Nat) (entry : Ixon.Constructor × Nat)
    (initial : Array FamilyReader.CtorRow × List Kernel.Name) :
    ReadM (ForInStep (Array FamilyReader.CtorRow × List Kernel.Name)) := do
  let (ctor, position) := entry
  unless ctor.cidx.toNat == position do malformed "constructor index differs from its position"
  if ctor.isUnsafe then declined "unsafe inductive declaration"
  let cv : CVal := ⟨reader.nameOf (.ctor owner index position), lpsAt ctor.lvls, ← member.read ctor.typ⟩
  unless nPd + ctor.fields.toNat == piTeleLen cv.type do
    malformed s!"constructor {cv.name} declares {ctor.fields} fields at {nPd} parameters; \
      its type has {piTeleLen cv.type} binders"
  pure (.yield (initial.1.push (cv, ctor.params.toNat, ctor.fields.toNat), initial.2 ++ [cv.name]))

def memberStep (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (nPd : Nat) (entry : Nat × Ixon.Inductive)
    (initial : Array FamilyReader.CtorRow × Array (List Kernel.Name)) :
    ReadM (ForInStep (Array FamilyReader.CtorRow × Array (List Kernel.Name))) := do
  let result ← forIn entry.2.ctors.zipIdx (initial.1, []) (ctorStep reader owner entry.1 member lpsAt nPd)
  pure (.yield (result.1, initial.2.push result.2))

theorem constructors_run (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (nPd : Nat) (indcs : Array (Nat × Ixon.Inductive)) :
    FamilyReader.readConstructors reader owner member lpsAt nPd indcs = (do
      let result ← forIn indcs (#[], #[]) (memberStep reader owner member lpsAt nPd)
      pure (result.1, result.2)) := rfl

structure CtorMeaning (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : ConstructorVal) (target : FamilyReader.CtorRow) : Prop where
  levels : target.1.levelParams.length = source.cnst.levelParams.size
  parameters : target.2.1 = source.numParams
  fields : target.2.2 = source.numFields
  type : ExpressionState.Related names sourceParams params source.cnst.type target.1.type

theorem ctor_step (reader : Ctx) (owner : Address) (index : Nat) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (lengths : ∀ count, (lpsAt count).length = count.toNat)
    (nPd position : Nat) (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : ConstructorVal) (target : Ixon.Constructor)
    (related : ConstructorEmission.Related member names sourceParams params source target)
    (atPosition : source.cidx = position) (safe : source.isUnsafe = false)
    (binders : nPd + source.numFields = telescope source.cnst.type)
    (initial : Array FamilyReader.CtorRow × List Kernel.Name) :
    ∃ row, ctorStep reader owner index member lpsAt nPd (target, position) initial =
        .ok (.yield (initial.1.push row, initial.2 ++ [row.1.name])) ∧
      CtorMeaning names sourceParams params source row ∧ row.1.name = reader.nameOf (.ctor owner index position) := by
  obtain ⟨safety, levels, cidx, parameters, fields, type, meaning, read⟩ := related
  have count : nPd + target.fields.toNat = piTeleLen type := by
    rw [fields, related_telescope names sourceParams params source.cnst.type type meaning]
    exact binders
  let cv : CVal := ⟨reader.nameOf (.ctor owner index position), lpsAt target.lvls, type⟩
  refine ⟨(cv, target.params.toNat, target.fields.toNat), ?_,
    ⟨(lengths target.lvls).trans levels, parameters, fields, meaning⟩, rfl⟩
  simp [ctorStep, cidx.trans atPosition, safety.trans safe, read, count, cv,
    bind, Except.bind, pure, Except.pure]

private theorem push_join (initial : Array α) (head : α) (tail : List α) :
    initial.push head ++ tail.toArray = initial ++ (head :: tail).toArray := by
  rw [Array.push_eq_append, Array.append_assoc]
  exact congrArg (initial ++ ·) (List.toArray_cons head tail).symm

theorem ctor_loop (reader : Ctx) (owner : Address) (index : Nat) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (lengths : ∀ count, (lpsAt count).length = count.toNat)
    (nPd : Nat) (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (sources : List ConstructorVal) (targets : List Ixon.Constructor)
    (related : List.Forall₂ (ConstructorEmission.Related member names sourceParams params) sources targets)
    (start : Nat) (positions : sources.map (·.cidx) = List.range' start sources.length)
    (safe : ∀ source ∈ sources, source.isUnsafe = false)
    (binders : ∀ source ∈ sources, nPd + source.numFields = telescope source.cnst.type)
    (initial : Array FamilyReader.CtorRow × List Kernel.Name) :
    ∃ rows, forIn (targets.zipIdx start) initial (ctorStep reader owner index member lpsAt nPd) =
        .ok (initial.1 ++ rows.toArray, initial.2 ++ rows.map (·.1.name)) ∧
      List.Forall₂ (CtorMeaning names sourceParams params) sources rows ∧
      rows.map (·.1.name) = (List.range' start sources.length).map
        (fun position => reader.nameOf (.ctor owner index position)) := by
  induction related generalizing start initial with
  | nil => exact ⟨[], by simp; rfl, .nil, by simp⟩
  | @cons source target sources targets head rest ih =>
    have pos := List.cons.inj positions
    obtain ⟨row, rowRun, rowMeaning, rowName⟩ := ctor_step reader owner index member lpsAt lengths nPd start
      names sourceParams params source target head pos.1 (safe source (by simp)) (binders source (by simp)) initial
    obtain ⟨rows, tailRun, meanings, rowNames⟩ := ih (start + 1) pos.2
      (fun source present => safe source (by simp [present]))
      (fun source present => binders source (by simp [present]))
      (initial.1.push row, initial.2 ++ [row.1.name])
    refine ⟨row :: rows, ?_, .cons rowMeaning meanings, ?_⟩
    · rw [List.zipIdx_cons, List.forIn_cons, rowRun]
      simpa only [bind, Except.bind, push_join, List.append_assoc, List.singleton_append, List.map_cons] using tailRun
    · simp only [List.map_cons, rowName, rowNames, List.length_cons, List.range'_succ]

structure SourceReady (nPd : Nat) (source : Ind) : Prop where
  positions : source.ctors.toList.map (·.cidx) = List.range' 0 source.ctors.size
  safe : ∀ ctor ∈ source.ctors, ctor.isUnsafe = false
  binders : ∀ ctor ∈ source.ctors, nPd + ctor.numFields = telescope ctor.cnst.type

def GroupMeaning (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (source : Nat × Ind) (rows : List FamilyReader.CtorRow) : Prop :=
  List.Forall₂ (CtorMeaning names source.2.levelParams.toList params) source.2.ctors.toList rows ∧
    rows.map (·.1.name) = (List.range' 0 source.2.ctors.size).map
      (fun position => reader.nameOf (.ctor owner source.1 position))

theorem member_step (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (lengths : ∀ count, (lpsAt count).length = count.toNat)
    (nPd : Nat) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (source : Nat × Ind) (target : Nat × Ixon.Inductive)
    (related : FamilyTypes.Paired member names params source target) (ready : SourceReady nPd source.2)
    (initial : Array FamilyReader.CtorRow × Array (List Kernel.Name)) :
    ∃ rows, memberStep reader owner member lpsAt nPd target initial =
        .ok (.yield (initial.1 ++ rows.toArray, initial.2.push (rows.map (·.1.name)))) ∧
      GroupMeaning reader owner names params source rows := by
  obtain ⟨position, _, _, _, _, _, ctors⟩ := related
  obtain ⟨rows, ran, meanings, identities⟩ := ctor_loop reader owner target.1 member lpsAt lengths nPd
    names source.2.levelParams.toList params source.2.ctors.toList target.2.ctors.toList ctors 0
    (by simpa using ready.positions)
    (fun ctor present => ready.safe ctor (by simpa using present))
    (fun ctor present => ready.binders ctor (by simpa using present)) (initial.1, [])
  refine ⟨rows, ?_, meanings, by simpa only [position, Array.length_toList] using identities⟩
  unfold memberStep
  rw [← Array.forIn_toList]
  have actual : forIn target.2.ctors.zipIdx.toList (initial.1, []) (ctorStep reader owner target.1 member lpsAt nPd) =
      .ok (initial.1 ++ rows.toArray, rows.map (·.1.name)) := by simpa using ran
  rw [actual]
  rfl

private theorem append_join (initial : Array α) (first last : List α) :
    (initial ++ first.toArray) ++ last.toArray = initial ++ (first ++ last).toArray := by
  apply Array.toList_inj.mp
  simpa only [Array.toList_append] using List.append_assoc initial.toList first last

theorem members_loop (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (lengths : ∀ count, (lpsAt count).length = count.toNat)
    (nPd : Nat) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : List (Nat × Ind)) (targets : List (Nat × Ixon.Inductive))
    (related : List.Forall₂ (FamilyTypes.Paired member names params) sources targets)
    (ready : ∀ source ∈ sources, SourceReady nPd source.2)
    (initial : Array FamilyReader.CtorRow × Array (List Kernel.Name)) :
    ∃ groups, forIn targets initial (memberStep reader owner member lpsAt nPd) =
        .ok (initial.1 ++ groups.flatten.toArray, initial.2 ++ (groups.map fun rows => rows.map (·.1.name)).toArray) ∧
      List.Forall₂ (GroupMeaning reader owner names params) sources groups := by
  induction related generalizing initial with
  | nil => exact ⟨[], by simp; rfl, .nil⟩
  | @cons source target sources targets head rest ih =>
    obtain ⟨rows, rowRun, rowMeaning⟩ := member_step reader owner member lpsAt lengths nPd names params
      source target head (ready source (by simp)) initial
    obtain ⟨groups, tailRun, meanings⟩ := ih (fun source present => ready source (by simp [present]))
      (initial.1 ++ rows.toArray, initial.2.push (rows.map (·.1.name)))
    refine ⟨rows :: groups, ?_, .cons rowMeaning meanings⟩
    rw [List.forIn_cons, rowRun]
    simpa only [bind, Except.bind, append_join, push_join, List.flatten_cons, List.map_cons] using tailRun

/-- Exact constructor order, counts, types and grouped identities through both
actual family loops. Guard conditions mention source syntax and declarations. -/
theorem constructors_read (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (lengths : ∀ count, (lpsAt count).length = count.toNat)
    (nPd : Nat) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : Array (Nat × Ind)) (targets : Array (Nat × Ixon.Inductive))
    (related : List.Forall₂ (FamilyTypes.Paired member names params) sources.toList targets.toList)
    (ready : ∀ source ∈ sources, SourceReady nPd source.2) :
    ∃ groups, FamilyReader.readConstructors reader owner member lpsAt nPd targets =
        .ok (groups.flatten.toArray, (groups.map fun rows => rows.map (·.1.name)).toArray) ∧
      List.Forall₂ (GroupMeaning reader owner names params) sources.toList groups := by
  obtain ⟨groups, ran, meanings⟩ := members_loop reader owner member lpsAt lengths nPd names params sources.toList targets.toList
    related (fun source present => ready source (by simpa using present)) (#[], #[])
  refine ⟨groups, ?_, meanings⟩
  rw [constructors_run, ← Array.forIn_toList]
  have actual : forIn targets.toList (#[], #[]) (memberStep reader owner member lpsAt nPd) =
      .ok (groups.flatten.toArray, (groups.map fun rows => rows.map (·.1.name)).toArray) := by simpa using ran
  rw [actual]
  rfl

end Ix.CompileCert.FamilyConstructors
