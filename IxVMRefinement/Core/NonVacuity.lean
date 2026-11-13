import IxVMRefinement.Core.Seams

/-! # The context seam is satisfiable

A context the core's specs are stated under exists: the records are empty, the environment is
empty, the role table binds nothing, and the role context assumes it (`Assumed`, no group
limit). Its environment invariant holds (`envFacts₀`), and a heap holding the role context and
an empty context list relates them (`rcRep₀`, `typesRep₀`), so `S0.ctx` holds of it apart from
the loads (`ctx₀`: given `LoadFacts`, which only the record conversion can discharge). The
specs' hypotheses on the context are therefore not contradictory. -/

namespace IxVM.Refinement.Core.NonVacuity

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List

/-- The role table that binds nothing. -/
def t₀ : Ix.Kernel.RoleTable := { version := Ix.Kernel.specVersion, bound := #[], evidence := #[] }

/-- The empty environment. -/
def env₀ : Ix.Kernel.Env .anon := Ix.Kernel.Env.empty

/-- The context: no records, the empty environment, the empty table, no group limit. -/
def c₀ : Ctx := ⟨{}, env₀, t₀, none⟩

theorem t₀_wf : t₀.wf = true := by decide

theorem env₀_find (k : KKey) : env₀.find? k = none := rfl

theorem env₀_findProj (T : KKey) (i : Nat) : env₀.findProj? T i = none := by
  simp [Ix.Kernel.Env.findProj?, env₀_find]

theorem t₀_addressOf (r : Ix.Kernel.Role) : t₀.addressOf? r = none := rfl

theorem not_inForce (r : Ix.Kernel.Role) : ¬ c₀.inForce r := by
  intro h
  have hb := h.1
  simp [Ctx.binds, c₀, t₀_addressOf] at hb

/-- **The environment invariant holds of the empty context.** -/
theorem envFacts₀ : EnvFacts c₀ where
  tableWf := t₀_wf
  storeClosed :=
    { type := by intro k c h; simp [c₀, env₀_find] at h
      defn := by intro k cv v hn h; simp [c₀, env₀_find] at h
      rhs := by intro k cv mI rP rules h; simp [c₀, env₀_find] at h
      proj := by intro sn i entry h; simp [c₀, env₀_findProj] at h }
  thmTyped := by intro n cv value h; simp [c₀, env₀_find] at h
  natLit := fun h => absurd h (not_inForce _)
  strLit := fun h => absurd h (not_inForce _)
  natOps := fun _ h => absurd h (not_inForce _)
  natAdd := fun h => absurd h (not_inForce _)
  eqStored := fun h => absurd h (not_inForce _)
  evidence := fun _ _ _ _ h => absurd h (not_inForce _)
  recRules := by intro k cv mI rP rls h; simp [c₀, env₀_find] at h
  recPlain := by intro k cv mI rP rls rl cvj nP nF h; simp [c₀, env₀_find] at h
  recArity := by intro k cv mI rP rls h; simp [c₀, env₀_find] at h
  ruleCtorArity := by intro k cv mI rP rls h; simp [c₀, env₀_find] at h
  tableCtorArity := by intro sn i entry h; simp [c₀, env₀_findProj] at h
  familyArity := by intro T cvT caps h; simp [c₀, env₀_find] at h
  store := Ix.Kernel.Open.StoreInv.empty
  recMajorRecord := by intro k cv mI rP rls p us h; simp [c₀, env₀_find] at h
  ruleCtorHead := by intro k cv mI rP rls rl cvj nP nF T us h; simp [c₀, env₀_find] at h
  quotBasis := fun h => absurd h (not_inForce _)

/-- The table cell: an empty binding section and three empty maps. -/
def tableCell : SourceValue F :=
  .construct rtEnum "Mk" [.field 0, .construct roleAddrMapEnum "Nil" [],
    .construct addrMapEnum "Nil" [], .construct roleEvMapEnum "Nil" []]

/-- The role context cell: assuming the table at address `0`. -/
def rcCell : SourceValue F := .construct rcEnum "Assumed" [.ptr (.enum rtEnum) 0, .field 0]

/-- A heap holding the table, the role context and an empty context list. -/
def h₀ : Heap F := [tableCell, rcCell, .construct kexprListEnum "Nil" []]

def rc₀ : SourceValue F := .ptr (.enum rcEnum) 1
def types₀ : SourceValue F := .ptr (.enum kexprListEnum) 2

theorem tableRep₀ : TableRep t₀ h₀ (.ptr (.enum rtEnum) 0) :=
  ⟨.field 0, _, _, _, loadValue_enum_cell (heap := h₀) (addr := 0) rfl, .nil, .nil, .nil⟩

/-- **The role context relates to the empty table**, assuming it. -/
theorem rcRep₀ : RCRep t₀ none h₀ rc₀ :=
  ⟨.ptr (.enum rtEnum) 0, .field 0, rcCell, loadValue_enum_cell (heap := h₀) (addr := 1) rfl,
    Or.inr ⟨rfl, rfl⟩, tableRep₀⟩

/-- **The empty context list is a context list at depth `0`.** -/
theorem typesRep₀ (κ : _root_.Address → KKey) (Γ : Nat → KExpr) : TypesRep κ Γ h₀ 0 types₀ :=
  .nil (addr := 2) rfl

theorem ghostScoped₀ (Γ : Nat → KExpr) : GhostScoped Γ 0 := fun _ hj => absurd hj (Nat.not_lt_zero _)

/-- **The context seam holds of the empty context**, given its loads: the role context, the
empty context list, the scoped ghost context and the environment invariant are all met. -/
theorem ctx₀ (Γ : Nat → KExpr) (hl : LoadFacts c₀) :
    S0.ctx c₀.E c₀.env ⟨keyOf t₀, Γ⟩ 0 h₀ rc₀ types₀ :=
  ⟨t₀, none, rfl, rcRep₀, typesRep₀ _ Γ, ghostScoped₀ Γ, envFacts₀, hl⟩

end IxVM.Refinement.Core.NonVacuity
