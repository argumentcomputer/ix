import Ix.CompileCert.InductiveReading

/-! # The reader on an inductive block of several types

`readInductive` reads an inductive block's types in the block shape's motive order
(`BlockShape.order`), each under its member key, its constructors under their keys, and its
recursors from their own records (`InductiveReading.readRecursors`), then lowers the block
(`lowerInductive`). For a block laid out in Lean's order the motive order is the identity
(`shape.order = [0, …, n)`), and `readRecord_family` states the record's reading, given every
type's and constructor's key, reading and checks (`TypeFacts`): `lowerInductive` of the block
the reads describe, after the recursors' reading. -/

namespace Ix.Cert.InductiveBlocks

open Ix.Kernel (Mode LevelParam ConstRef)
open Ix.Kernel.Reader
open Ix.CompileCert.InductiveReading (blockSelf indcAt typeStep ctorStep ctorClassStep readRecursors)

variable {md : Mode}

/-! ## Constructors -/

/-- What the reader reads of type `i`'s constructors, from position `j`. -/
def ctorReadsAt (ctorKey : Nat → Nat → CName md) (i : Nat) : Nat → List Ixon.Constructor →
    List (CExpr md) → List (CVal md × Nat × Nat)
  | j, ctor :: ctors, type :: types =>
    (⟨ctorKey i j, List.range ctor.lvls.toNat, type⟩, ctor.params.toNat, ctor.fields.toNat) ::
      ctorReadsAt ctorKey i (j + 1) ctors types
  | _, _, _ => []

/-- The constructor loop of type `i` passes its checks and reads, from position `j`. -/
def CtorFactsAt (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd : Nat)
    (ctorKey : Nat → Nat → CName md) (i : Nat) : Nat → List Ixon.Constructor → List (CExpr md) → Prop
  | _, [], [] => True
  | j, ctor :: ctors, type :: types =>
    ctor.cidx.toNat = j ∧ ctor.isUnsafe = false ∧ cx.memberKey (.ctor owner i j) = .ok (ctorKey i j) ∧
      mr.read ctor.typ = .ok type ∧ nPd + ctor.fields.toNat = piTeleLen type ∧
      CtorFactsAt cx owner mr nPd ctorKey i (j + 1) ctors types
  | _, _, _ => False

theorem ctorStep_at (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd i : Nat)
    (ctor : Ixon.Constructor) (j : Nat) (state : Array (CVal md × Nat × Nat) × List (CName md))
    {key : CName md} {type : CExpr md} (index : ctor.cidx.toNat = j) (safe : ctor.isUnsafe = false)
    (keyed : cx.memberKey (.ctor owner i j) = .ok key) (read : mr.read ctor.typ = .ok type)
    (arity : nPd + ctor.fields.toNat = piTeleLen type) :
    ctorStep cx owner mr nPd i (ctor, j) state =
      .ok (.yield (state.1.push (⟨key, List.range ctor.lvls.toNat, type⟩, ctor.params.toNat, ctor.fields.toNat),
        state.2 ++ [key])) := by
  simp only [ctorStep, index, safe, keyed, read, arity, beq_self_eq_true, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind, pure, Except.pure]

theorem ctorLoop_at (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd : Nat)
    (ctorKey : Nat → Nat → CName md) (i : Nat) :
    ∀ (targets : List Ixon.Constructor) (j : Nat) (types : List (CExpr md))
      (state : Array (CVal md × Nat × Nat) × List (CName md)),
      CtorFactsAt cx owner mr nPd ctorKey i j targets types →
      forIn (targets.zipIdx j) state (ctorStep cx owner mr nPd i) =
        .ok ((state.1.toList ++ ctorReadsAt ctorKey i j targets types).toArray,
          state.2 ++ (ctorReadsAt ctorKey i j targets types).map (·.1.name)) := by
  intro targets
  induction targets with
  | nil =>
    intro j types state facts
    cases types with
    | nil => simp [ctorReadsAt]; rfl
    | cons _ _ => exact False.elim facts
  | cons ctor rest ih =>
    intro j types state facts
    cases types with
    | nil => exact False.elim facts
    | cons type types =>
      obtain ⟨index, safe, keyed, read, arity, tail⟩ := facts
      rw [List.zipIdx_cons, List.forIn_cons, ctorStep_at cx owner mr nPd i ctor j state index safe keyed read arity]
      simp only [bind, Except.bind]
      rw [ih (j + 1) types _ tail]
      simp [ctorReadsAt]

/-! ## Types -/

/-- What the reader reads of the block's types, at their keys and type readings. -/
def typeReads (keyOf : Nat → CName md) (typeOf : Nat → CExpr md) (l : List (Nat × Ixon.Inductive)) :
    List (CVal md × Nat × Nat) :=
  l.map fun x => (⟨keyOf x.1, List.range x.2.lvls.toNat, typeOf x.1⟩, x.2.params.toNat, x.2.indices.toNat)

theorem typeLoop_family (cx : Ctx md) (owner : Address) (mr : MemberReader md) (keyOf : Nat → CName md)
    (typeOf : Nat → CExpr md) :
    ∀ (l : List (Nat × Ixon.Inductive)) (acc : Array (CVal md × Nat × Nat)),
      (∀ x ∈ l, cx.memberKey (.member owner x.1) = .ok (keyOf x.1) ∧ mr.read x.2.typ = .ok (typeOf x.1)) →
      forIn l acc (typeStep cx owner mr) = .ok (acc.toList ++ typeReads keyOf typeOf l).toArray
  | [], acc, _ => by simp [typeReads]; rfl
  | x :: l, acc, h => by
    obtain ⟨keyed, read⟩ := h x List.mem_cons_self
    rw [List.forIn_cons]
    obtain ⟨i, t⟩ := x
    simp only [typeStep, keyed, read, bind, Except.bind, pure, Except.pure]
    rw [typeLoop_family cx owner mr keyOf typeOf l _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp [typeReads]

/-- The constructors the reader reads of the block's types, in order. -/
def ctorsReads (ctorKey : Nat → Nat → CName md) (ctorTypesOf : Nat → List (CExpr md))
    (l : List (Nat × Ixon.Inductive)) : List (CVal md × Nat × Nat) :=
  l.flatMap fun x => ctorReadsAt ctorKey x.1 0 x.2.ctors.toList (ctorTypesOf x.1)

theorem ctorClassLoop_family (cx : Ctx md) (owner : Address) (mr : MemberReader md) (nPd : Nat)
    (ctorKey : Nat → Nat → CName md) (ctorTypesOf : Nat → List (CExpr md)) :
    ∀ (l : List (Nat × Ixon.Inductive)) (acc : Array (CVal md × Nat × Nat) × Array (List (CName md))),
      (∀ x ∈ l, CtorFactsAt cx owner mr nPd ctorKey x.1 0 x.2.ctors.toList (ctorTypesOf x.1)) →
      forIn l acc (ctorClassStep cx owner mr nPd) =
        .ok ((acc.1.toList ++ ctorsReads ctorKey ctorTypesOf l).toArray,
          (acc.2.toList ++ l.map fun x =>
            (ctorReadsAt ctorKey x.1 0 x.2.ctors.toList (ctorTypesOf x.1)).map (·.1.name)).toArray)
  | [], acc, _ => by simp [ctorsReads]; rfl
  | x :: l, acc, h => by
    rw [List.forIn_cons]
    obtain ⟨i, t⟩ := x
    simp only [ctorClassStep]
    rw [← Array.forIn_toList, Array.toList_zipIdx,
      ctorLoop_at cx owner mr nPd ctorKey i t.ctors.toList 0 (ctorTypesOf i) (acc.1, [])
        (h (i, t) List.mem_cons_self)]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [ctorClassLoop_family cx owner mr nPd ctorKey ctorTypesOf l _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp [ctorsReads]

/-! ## The block -/

theorem filterMap_eq_map {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons,
      filterMap_eq_map (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- A block's types, by position. -/
def indexed (targets : List Ixon.Inductive) : List (Nat × Ixon.Inductive) :=
  (List.range targets.length).map fun i => (i, targets[i]!)

theorem indcs_family (targets : List Ixon.Inductive) :
    (List.range targets.length).toArray.filterMap (indcAt (targets.map Ixon.MutConst.indc).toArray) =
      (indexed targets).toArray := by
  rw [List.filterMap_toArray]
  congr 1
  unfold indexed
  apply filterMap_eq_map
  intro i hi
  rw [List.mem_range] at hi
  simp [indcAt, hi]

theorem readRecord_muts_indc (cx : Ctx md) (st : State md) (owner : Address) (c : Ixon.Constant)
    (targets : List Ixon.Inductive) (hne : targets ≠ [])
    (info : c.info = .muts (targets.map Ixon.MutConst.indc).toArray) :
    readRecord cx st owner c = readInductive cx st owner c (targets.map Ixon.MutConst.indc).toArray := by
  unfold readRecord
  rw [info]
  obtain ⟨t, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp

/-- **The reader on an inductive block laid out in Lean's order**: given every type's key,
type reading, safety and parameter count and its constructors' checks and readings, the
record reads as `lowerInductive` of the block they describe, after the recursors' reading. -/
theorem readRecord_family (cx : Ctx md) (st : State md) (owner : Address) (c : Ixon.Constant)
    (targets : List Ixon.Inductive) (hne : targets ≠ [])
    (info : c.info = .muts (targets.map Ixon.MutConst.indc).toArray) {shape : BlockShape}
    (hindexed : cx.index.blocks[owner]? = some shape)
    (order : shape.order = (List.range targets.length).toArray) (nPd : Nat)
    (keyOf typeOf : Nat → _) (ctorKey : Nat → Nat → CName md) (ctorTypesOf : Nat → List (CExpr md))
    (facts : ∀ x ∈ indexed targets,
      cx.memberKey (.member owner x.1) = .ok (keyOf x.1) ∧
      (MemberReader.mk' cx c id (blockSelf cx owner (targets.map Ixon.MutConst.indc).toArray)).read x.2.typ =
        .ok (typeOf x.1) ∧
      x.2.isUnsafe = false ∧ x.2.params.toNat = nPd ∧
      CtorFactsAt cx owner (MemberReader.mk' cx c id (blockSelf cx owner (targets.map Ixon.MutConst.indc).toArray))
        nPd ctorKey x.1 0 x.2.ctors.toList (ctorTypesOf x.1)) :
    readRecord cx st owner c =
      readRecursors cx (List.range (targets.head hne).lvls.toNat) shape.recs >>= fun recs =>
        lowerInductive st ⟨nPd, (typeReads keyOf typeOf (indexed targets)).toArray,
          (ctorsReads ctorKey ctorTypesOf (indexed targets)).toArray,
          ((indexed targets).map fun x =>
            (ctorReadsAt ctorKey x.1 0 x.2.ctors.toList (ctorTypesOf x.1)).map (·.1.name)).toArray, recs⟩ := by
  rw [readRecord_muts_indc cx st owner c targets hne info, Ix.CompileCert.InductiveReading.readInductive_eq]
  unfold Ix.CompileCert.InductiveReading.readInductiveSpec
  rw [hindexed]
  dsimp only
  rw [order, indcs_family]
  obtain ⟨t, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hsize : (indexed (t :: rest)).toArray.size == (List.range (t :: rest).length).toArray.size := by
    simp [indexed]
  have hfirst : (indexed (t :: rest)).toArray[0]? = some (0, t) := by
    simp [indexed, List.range_succ_eq_map]
  have hunsafe : (indexed (t :: rest)).toArray.any (·.2.isUnsafe) = false := by
    rw [Bool.eq_false_iff]
    intro hany
    simp only [List.any_toArray', List.any_eq_true] at hany
    obtain ⟨x, hx, hu⟩ := hany
    rw [(facts x hx).2.2.1] at hu
    cases hu
  have hparams : (indexed (t :: rest)).toArray.all (·.2.params.toNat == t.params.toNat) = true := by
    simp only [List.all_toArray', List.all_eq_true, beq_iff_eq]
    intro x hx
    rw [(facts x hx).2.2.2.1, ← (facts (0, t) (by simp [indexed, List.range_succ_eq_map])).2.2.2.1]
  have hnPd : t.params.toNat = nPd := (facts (0, t) (by simp [indexed, List.range_succ_eq_map])).2.2.2.1
  simp only [hsize, Bool.false_eq_true, ↓reduceIte, hfirst, hunsafe, hparams]
  rw [hnPd, ← Array.forIn_toList, List.toList_toArray,
    typeLoop_family cx owner _ keyOf typeOf _ #[] (fun x hx => ⟨(facts x hx).1, (facts x hx).2.1⟩),
    ← Array.forIn_toList, List.toList_toArray,
    ctorClassLoop_family cx owner _ nPd ctorKey ctorTypesOf _ (#[], #[]) (fun x hx => (facts x hx).2.2.2.2)]
  simp [bind, Except.bind]

/--
info: 'Ix.Cert.InductiveBlocks.readRecord_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms readRecord_family

end Ix.Cert.InductiveBlocks
