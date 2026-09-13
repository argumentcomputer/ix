/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Expr
import Ix.Theory.Model.LevelCongruence

/-!
# Reading opened binders

The production binder paths use free variables for their active locals.
`readScopedExpr?` maps those identifiers to model de Bruijn indices, keeping
syntactically bound variables distinct from active locals. Unknown free
variables and loose legacy variables fail. This binder fragment also excludes
lets and strings; the original closed reader remains available independently.

The local identifier list is newest first, matching `Model.Context.push`.
No local declaration's type or semantic validity is assumed by this reader.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u} {m : Mode}

def localIndex? (locals : List FVarId) (id : FVarId) : Option Nat :=
  match locals with
  | [] => none
  | head :: rest => if id = head then some 0 else (localIndex? rest id).map Nat.succ

theorem localIndex?_mem {locals : List FVarId} {id : FVarId} {index : Nat}
    (found : localIndex? locals id = some index) : id ∈ locals := by
  induction locals generalizing index with
  | nil => contradiction
  | cons head rest ih =>
      by_cases equal : id = head
      · simp [equal]
      · simp only [localIndex?, equal, if_false] at found
        obtain ⟨previous, found, _⟩ := Option.map_eq_some_iff.mp found
        exact List.mem_cons_of_mem _ (ih found)

theorem localIndex?_getElem {locals : List FVarId} {id : FVarId} {index : Nat}
    (found : localIndex? locals id = some index) : locals[index]? = some id := by
  induction locals generalizing index with
  | nil => contradiction
  | cons head rest ih =>
      by_cases equal : id = head
      · simp only [localIndex?, equal, if_true, Option.some.injEq] at found
        subst index
        simp [equal]
      · simp only [localIndex?, equal, if_false] at found
        obtain ⟨previous, hit, rfl⟩ := Option.map_eq_some_iff.mp found
        exact ih hit

theorem localIndex?_fresh {locals : List FVarId} {id fresh : FVarId} {index : Nat}
    (absent : fresh ∉ locals) (found : localIndex? locals id = some index) :
    localIndex? (fresh :: locals) id = some (index + 1) := by
  have different : id ≠ fresh := fun equal => absent (equal ▸ localIndex?_mem found)
  simp [localIndex?, different, found]

/-- Structural reading in the currently opened local context. `depth` counts
only syntactic binders still present inside the expression. -/
def readScopedExpr? (resolve : Address → Option (ConstRef β)) (locals : List FVarId) :
    KExpr m → (depth : Nat := 0) → Option (VExpr β)
  | .var index _ _, depth =>
      if index.toNat < depth then some (.bvar index.toNat) else none
  | .fvar id _ _, depth =>
      (localIndex? locals id).map (fun index => .bvar (depth + index))
  | .sort level _, _ => some (.sort (readLevel level))
  | .const id levels _, _ => do
      return .const (← resolve id.addr) (levels.toList.map readLevel)
  | .app fn arg _, depth => do
      return .app (← readScopedExpr? resolve locals fn depth)
        (← readScopedExpr? resolve locals arg depth)
  | .lam _ _ domain body _, depth => do
      return .lam (← readScopedExpr? resolve locals domain depth)
        (← readScopedExpr? resolve locals body (depth + 1))
  | .all _ _ domain body _, depth => do
      return .forallE (← readScopedExpr? resolve locals domain depth)
        (← readScopedExpr? resolve locals body (depth + 1))
  | .prj id index value _, depth => do
      return .proj (← resolve id.addr) index.toNat
        (← readScopedExpr? resolve locals value depth)
  | .nat value _ _, _ => some (.natLit value)
  | .letE .., _ | .str .., _ => none

@[simp] theorem readScopedExpr?_mkVar (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (index : UInt64) (name : m.F Name) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkVar index name) depth =
      if index.toNat < depth then some (.bvar index.toNat) else none := rfl

@[simp] theorem readScopedExpr?_mkFVar (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (id : FVarId) (name : m.F Name) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkFVar id name) depth =
      (localIndex? locals id).map (fun index => .bvar (depth + index)) := rfl

@[simp] theorem readScopedExpr?_mkSort (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (level : KUniv m) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkSort level) depth = some (.sort (readLevel level)) := rfl

@[simp] theorem readScopedExpr?_mkApp (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (fn arg : KExpr m) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkApp fn arg) depth = do
      return .app (← readScopedExpr? resolve locals fn depth)
        (← readScopedExpr? resolve locals arg depth) := rfl

@[simp] theorem readScopedExpr?_mkLam (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (domain body : KExpr m) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkLam name bi domain body) depth = do
      return .lam (← readScopedExpr? resolve locals domain depth)
        (← readScopedExpr? resolve locals body (depth + 1)) := rfl

@[simp] theorem readScopedExpr?_mkAll (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (domain body : KExpr m) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkAll name bi domain body) depth = do
      return .forallE (← readScopedExpr? resolve locals domain depth)
        (← readScopedExpr? resolve locals body (depth + 1)) := rfl

@[simp] theorem readScopedExpr?_mkPrj (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (id : KId m) (index : UInt64) (value : KExpr m) (depth : Nat) :
    readScopedExpr? resolve locals (KExpr.mkPrj id index value) depth = do
      return .proj (← resolve id.addr) index.toNat
        (← readScopedExpr? resolve locals value depth) := rfl

private theorem option_bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

theorem readScopedExpr?_lam_parts {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {name : m.F Name} {bi : m.F Lean.BinderInfo}
    {domain body : KExpr m} {info : ExprInfo m} {A b : VExpr β} {depth : Nat}
    (reading : readScopedExpr? resolve locals (.lam name bi domain body info) depth =
      some (.lam A b)) :
    readScopedExpr? resolve locals domain depth = some A ∧
      readScopedExpr? resolve locals body (depth + 1) = some b := by
  rw [readScopedExpr?] at reading
  obtain ⟨A', domainReads, reading⟩ := option_bind_success reading
  obtain ⟨b', bodyReads, reading⟩ := option_bind_success reading
  cases reading
  exact ⟨domainReads, bodyReads⟩

theorem readScopedExpr?_all_parts {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {name : m.F Name} {bi : m.F Lean.BinderInfo}
    {domain body : KExpr m} {info : ExprInfo m} {A B : VExpr β} {depth : Nat}
    (reading : readScopedExpr? resolve locals (.all name bi domain body info) depth =
      some (.forallE A B)) :
    readScopedExpr? resolve locals domain depth = some A ∧
      readScopedExpr? resolve locals body (depth + 1) = some B := by
  rw [readScopedExpr?] at reading
  obtain ⟨A', domainReads, reading⟩ := option_bind_success reading
  obtain ⟨B', bodyReads, reading⟩ := option_bind_success reading
  cases reading
  exact ⟨domainReads, bodyReads⟩

/-- Closing the local context recovers the original reader exactly. -/
theorem readScopedExpr?_closed {resolve : Address → Option (ConstRef β)}
    {term : KExpr m} {source : VExpr β} {depth : Nat}
    (reading : readScopedExpr? resolve [] term depth = some source) :
    readExpr? resolve term = some source := by
  induction term generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at reading
      split at reading
      · exact reading
      · contradiction
  | fvar _ _ _ | letE _ _ _ _ _ _ _ _ _ | str _ _ _ => contradiction
  | sort _ _ | const _ _ _ | nat _ _ _ => exact reading
  | app fn arg info hf ha | lam _ _ fn arg info hf ha | all _ _ fn arg info hf ha =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readExpr?, hf fReads, ha aReads]
  | prj id index value info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readExpr?, resolved, ih valueReads]

@[simp] theorem readScopedExpr?_eraseMeta
    (resolve : Address → Option (ConstRef β)) (locals : List FVarId)
    (term : KExpr m) (depth : Nat) :
    readScopedExpr? resolve locals term.eraseMeta depth =
      readScopedExpr? resolve locals term depth := by
  induction term generalizing depth <;>
    simp_all [readScopedExpr?, KExpr.eraseMeta, KId.eraseMeta,
      Array.toList_map, List.map_map, Function.comp_def]

theorem beq_readScopedExpr? {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {left right : KExpr m} {depth : Nat}
    (faithful : left.AddrFaithful right) (equal : (left == right) = true) :
    readScopedExpr? resolve locals left depth = readScopedExpr? resolve locals right depth := by
  have erased := faithful (KExpr.beq_def left right ▸ equal)
  simpa only [readScopedExpr?_eraseMeta] using
    congrArg (fun term => readScopedExpr? resolve locals term depth) erased

theorem internExpr_readScopedExpr? {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {table : InternTable m} {term : KExpr m} {depth : Nat}
    (coherent : table.WF)
    (faithful : KExpr.KeyCollisionFree fun value => table.ExprSupport value ∨ value = term) :
    readScopedExpr? resolve locals (table.internExpr term).1 depth =
      readScopedExpr? resolve locals term depth := by
  simpa only [readScopedExpr?_eraseMeta] using
    congrArg (fun term => readScopedExpr? resolve locals term depth)
      (table.internExpr_eraseMeta coherent faithful)

/-- A fresh local shifts every existing local occurrence by one, below the
syntactic binders. Reading success excludes a hidden occurrence of the new id. -/
theorem readScopedExpr?_push {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {term : KExpr m} {source : VExpr β} {depth : Nat}
    {fresh : FVarId} (absent : fresh ∉ locals)
    (reading : readScopedExpr? resolve locals term depth = some source) :
    readScopedExpr? resolve (fresh :: locals) term depth = some (source.liftN 1 depth) := by
  induction term generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at reading ⊢
      split at reading
      next bound =>
        cases reading
        simp [bound, VExpr.liftN, liftVar]
      · contradiction
  | fvar id name info =>
      rw [readScopedExpr?] at reading
      obtain ⟨index, found, reading⟩ := Option.map_eq_some_iff.mp reading
      cases reading
      simp [readScopedExpr?, localIndex?_fresh absent found, VExpr.liftN, liftVar,
        Nat.not_lt.mpr (Nat.le_add_right depth index), Nat.add_assoc, Nat.add_comm 1]
  | letE _ _ _ _ _ _ _ _ _ | str _ _ _ => contradiction
  | sort level info => cases reading; rfl
  | nat value name info => cases reading; rfl
  | const id levels info =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      cases reading
      simp [readScopedExpr?, resolved, VExpr.liftN]
  | app fn arg info hf ha | lam _ _ fn arg info hf ha | all _ _ fn arg info hf ha =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readScopedExpr?, hf fReads, ha aReads, VExpr.liftN]
  | prj id index value info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, reading⟩ := option_bind_success reading
      cases reading
      simp [readScopedExpr?, resolved, ih valueReads, VExpr.liftN]

end Ix.Kernel.Consistency
