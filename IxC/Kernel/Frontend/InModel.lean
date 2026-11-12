module

public import IxC.Kernel.Frontend.InModel.Nested

@[expose] public section

/-!
# The in-process modeller (task #200)

Entry point of the in-process construction of `_model` families for the
inductive blocks the direct routes do not install and the modeled
install expects a model for: **mutual** and **nested** blocks.  The
frontend calls `generate` at the block's record, before the block is
pushed, when the stream carries no model for it; the records it returns
are pushed ahead of the block and checked by the fold like any stream
declaration (the "certification tax"), and the block itself installs
through the modeled route.

Since task #207 this is the **only** model source: there is no
external preprocessor and no dependency, and every input is a raw
`lean4export` stream.  Soundness needs nothing from this module: a
wrong record is rejected or declined by the fold, never accepted.  Its
correctness decides only *coverage* — which blocks accept — and every
decline names its class, so the residual is exact and positive.

Rungs: `genMutual` (B1: index-free mutual; B2 adds indices), nested
(B3/B4) to follow.
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

/-- Is the block one this modeller is for: mutual (several types) or
nested (`numNested > 0`)? -/
def wants (b : BlockRec md) : Bool :=
  b.types.length > 1 || b.types.any (·.numNested > 0)

/-- A member's former as the rungs read it: its type at `nP + nIdx` Π binders and
a sort (`formerTele`, at the definitions' values), which is the declared type
itself when that is already such a telescope; a member declared at a
definition (`T : MyType`, `MyType := Type`) gets the unfolding. Its parameters are
syntactic binders, as Lean counts a block's parameters on the declared type. -/
def readFormer (ctx : Ctx md) (t : IndTypeRec md) : Except String (IndTypeRec md) :=
  if (t.cv.type.stripPis t.nP).isSome then
    match formerTele ctx.values (t.nP + t.nIdx) t.cv.type with
    | some ty => .ok { t with cv := { t.cv with type := ty } }
    | none => .error s!"former {t.cv.name} is not a telescope ending in a sort"
  else .error s!"former {t.cv.name}: its parameters are not syntactic binders"

/-- The block with every former read at its telescope (`readFormer`). -/
def readFormers (ctx : Ctx md) (b : BlockRec md) : Except String (BlockRec md) := do
  let types ← b.types.mapM (readFormer ctx)
  pure { b with types }

/-- The record at position `i` of a rung's output, a member model's type put back
(`restoreModelTypes`). -/
def restoreAt (b : BlockRec md) (i : Nat) : Declaration md → Declaration md
  | .defnDecl cv v h =>
    match b.types[i - 2]? with
    | some t => if 2 ≤ i then .defnDecl { cv with type := t.cv.type } v h else .defnDecl cv v h
    | none => .defnDecl cv v h
  | d => d

/-- `restoreAt` along a rung's output from position `i`. -/
def restoreFrom (b : BlockRec md) : Nat → List (Declaration md) → List (Declaration md)
  | _, [] => []
  | i, d :: ds => restoreAt b i d :: restoreFrom b (i + 1) ds

/-- **The member models at their members' declared types.** Both rungs emit the
tag block, the auxiliary block, then member `m`'s model `T_m._model` at position
`2 + m`, typed at the former the rung read (`readFormers`). The modeled install
compares a model's type with its member's declared type syntactically, so each
member model takes its member's declared type back (definitionally equal: one
unfolds to the other). Where no former was unfolded this changes nothing. -/
def restoreModelTypes (b : BlockRec md) (ds : List (Declaration md)) : List (Declaration md) :=
  restoreFrom b 0 ds

/-- Generate the model records of a block, in stream order, or the
reason the block is declined. The rungs read each former at its telescope
(`readFormers`). -/
def generate (ctx : Ctx md) (b : BlockRec md) : Except String (List (Declaration md)) := do
  let b' ← readFormers ctx b
  let ds ← (if b.types.any (·.numNested > 0) then genNested ctx b' else genMutual ctx b')
  pure (restoreModelTypes b ds)

theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {y : β}
    (h : (x >>= g) = .ok y) : ∃ a, x = .ok a ∧ g a = .ok y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- **A successful generation** is a rung's run at the block with its formers read
(`readFormers`), its member models' types put back (`restoreModelTypes`). -/
theorem generate_eq_ok {ctx : Ctx md} {b : BlockRec md} {ds : List (Declaration md)}
    (h : generate ctx b = .ok ds) :
    ∃ b' ds0, readFormers ctx b = .ok b' ∧
      (genNested ctx b' = .ok ds0 ∨ genMutual ctx b' = .ok ds0) ∧ ds = restoreModelTypes b ds0 := by
  unfold generate at h
  obtain ⟨b', h1, h⟩ := except_bind_eq_ok h
  obtain ⟨ds0, h2, h⟩ := except_bind_eq_ok h
  refine ⟨b', ds0, h1, ?_, (Except.ok.inj h).symm⟩
  split at h2
  · exact .inl h2
  · exact .inr h2

/-- A record of a restored output is a restored record of the rung's output. -/
theorem restoreFrom_mem {b : BlockRec md} :
    ∀ {i : Nat} {ds : List (Declaration md)} {d : Declaration md},
      d ∈ restoreFrom b i ds → ∃ j, ∃ d0 ∈ ds, d = restoreAt b j d0
  | _, [], _, h => by simp [restoreFrom] at h
  | i, d0 :: ds, d, h => by
    simp only [restoreFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨i, d0, List.mem_cons_self, rfl⟩
    · obtain ⟨j, d1, hd1, rfl⟩ := restoreFrom_mem h
      exact ⟨j, d1, List.mem_cons_of_mem _ hd1, rfl⟩

/-- A restored record is a basis declaration only if the record was. -/
theorem restoreAt_basis {b : BlockRec md} {i : Nat} {d : Declaration md} {k : BasisKind}
    (h : restoreAt b i d = .basisDecl k) : d = .basisDecl k := by
  cases d with
  | defnDecl cv v hh =>
    simp only [restoreAt] at h
    split at h
    · split at h <;> exact nomatch h
    · exact nomatch h
  | _ => exact h

end Ix.Kernel.Frontend.InModel
