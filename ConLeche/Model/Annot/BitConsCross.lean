module

public import ConLeche.Model.Annot.BitExtendTower
import ConLeche.Model.Annot.BitInstall
public import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.InferLemmas
import ConLeche.Semantics.EnvFacts

public section

/-!
# The P cons crossing at a tower head (task #175 W4c, P3 module 4)

Consing a tower-backed entry `(T, i)` changes the reading of exactly
one node shape, `.proj T i _` with no entry (`BitExtendTower`), so the
readings the install kit and its law transports move across a cons
survive whenever the moved subject has no such node.  This module
packages that side condition at the granularity the transports
consume:

* `NoProjEnv env T i` — no stored piece of `env` (a type, a definition
  or theorem value, a recursor rule's right-hand side or nested pin)
  has a `.proj T i` node;
* `ConsCrossEnv env c₀` — the head, if a tower entry, has that
  property at its own slot (vacuous at every other head:
  `ConsCrossEnv.ofNtc`);
* `ConsCrossAt c₀ e` — the per-subject condition the crossing itself
  (`denoteMeta_cons_mono`, `InstallP.lean`) consumes, with the helpers
  that discharge it from `ConsCrossEnv` for the stored pieces and
  their level instantiations and openings.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule)

/-- No stored piece of the environment mentions the slot `(T, i)`. -/
structure NoProjEnv (env : Env) (T : Name) (i : Nat) : Prop where
  type : ∀ c ∈ env.consts, Expr.NoProjAt T i c.toConstantVal.type
  defn : ∀ (cv : ConstantVal) (v : Expr) (hint : ConLeche.ReducibilityHint),
    ConstantInfo.defnInfo cv v hint ∈ env.consts → Expr.NoProjAt T i v
  rule : ∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    ConstantInfo.recInfo cv mI rP rules ∈ env.consts →
    ∀ r ∈ rules, Expr.NoProjAt T i (RecRule.rhs r) ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        ∀ pin ∈ pins, Expr.NoProjAt T i pin
  /-- a stored projection table's bodies (task #175 S1: the tower laws
  read them) -/
  table : ∀ (tbl : ConLeche.ProjTable), ConstantInfo.projInfo tbl ∈ env.consts →
    ∀ j, j < tbl.numFields → Expr.NoProjAt T i (tbl.bodies.getD j default)

/-- The head's crossing condition: a table head's slots (every field
of the structure, task #175 S1) are mentioned by no stored piece. -/
@[expose] def ConsCrossEnv (env : Env) (c₀ : ConstantInfo) : Prop :=
  ∀ tbl : ConLeche.ProjTable, c₀ = .projInfo tbl →
    ∀ i : Nat, NoProjEnv env tbl.structName i

/-- A non-table head crosses vacuously. -/
theorem ConsCrossEnv.ofNtc {env : Env} {c₀ : ConstantInfo}
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl) :
    ConsCrossEnv env c₀ := fun tbl heq => absurd heq (hntc tbl)

/-- The per-subject condition: the head's slots, if a table's, are not
mentioned. -/
@[expose] def ConsCrossAt (c₀ : ConstantInfo) (e : Expr) : Prop :=
  ∀ tbl : ConLeche.ProjTable, c₀ = .projInfo tbl →
    ∀ i : Nat, Expr.NoProjAt tbl.structName i e

theorem ConsCrossAt.ofNtc {c₀ : ConstantInfo} {e : Expr}
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl) :
    ConsCrossAt c₀ e := fun tbl heq => absurd heq (hntc tbl)

theorem ConsCrossAt.instantiateLevelParams {c₀ : ConstantInfo} {e : Expr}
    (h : ConsCrossAt c₀ e) (ks : List Name) (us : List Level) :
    ConsCrossAt c₀ (e.instantiateLevelParams ks us) := fun tbl heq i =>
  Expr.NoProjAt.instantiateLevelParams ks us e (h tbl heq i)

theorem ConsCrossAt.instantiate1 {c₀ : ConstantInfo} {e v : Expr}
    (h : ConsCrossAt c₀ e) (hv : ConsCrossAt c₀ v) (d : Nat) :
    ConsCrossAt c₀ (e.instantiate1 v d) := fun tbl heq i =>
  Expr.NoProjAt.instantiate1 (hv tbl heq i) e d (h tbl heq i)

theorem ConsCrossAt.sort {c₀ : ConstantInfo} (u : Level) :
    ConsCrossAt c₀ (.sort u) := fun _ _ _ => by simp

theorem ConsCrossAt.fvar_sort {c₀ : ConstantInfo} (idx : Nat)
    (u : Level) : ConsCrossAt c₀ (.fvar idx (.sort u)) :=
  fun _ _ _ => by simp

theorem ConsCrossAt.openRev {c₀ : ConstantInfo} {e : Expr}
    (h : ConsCrossAt c₀ e) (d : Nat) :
    ∀ n : Nat, ConsCrossAt c₀ (ConLeche.Verify.openRev d n e)
  | 0 => h
  | n + 1 =>
    ConsCrossAt.instantiate1 (ConsCrossAt.openRev h d n)
      (ConsCrossAt.fvar_sort _ _) 0

/-! ## The stored pieces -/

theorem ConsCrossEnv.type {env : Env} {c₀ : ConstantInfo}
    (h : ConsCrossEnv env c₀) {c : ConstantInfo} (hc : c ∈ env.consts) :
    ConsCrossAt c₀ c.toConstantVal.type := fun tbl heq i =>
  (h tbl heq i).type c hc

theorem ConsCrossEnv.typeOf {env : Env} {c₀ : ConstantInfo}
    (h : ConsCrossEnv env c₀) {n : Name} {c : ConstantInfo}
    (hf : env.find? n = some c) : ConsCrossAt c₀ c.toConstantVal.type :=
  h.type (ConLeche.Semantics.Env.find?_mem hf)

theorem ConsCrossEnv.defn {env : Env} {c₀ : ConstantInfo}
    (h : ConsCrossEnv env c₀) {cv : ConstantVal} {v : Expr}
    {hint : ConLeche.ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv v hint ∈ env.consts) :
    ConsCrossAt c₀ v := fun tbl heq i =>
  (h tbl heq i).defn cv v hint hc

/-- A stored table's body at a field (task #175 S1). -/
theorem ConsCrossEnv.body {env : Env} {c₀ : ConstantInfo}
    (h : ConsCrossEnv env c₀) {n : Name} {tbl : ConLeche.ProjTable}
    (hf : env.find? n = some (.projInfo tbl)) {j : Nat} (hj : j < tbl.numFields) :
    ConsCrossAt c₀ (tbl.entry j).body := fun tbl' heq i =>
  (h tbl' heq i).table tbl (ConLeche.Semantics.Env.find?_mem hf) j hj

theorem ConsCrossEnv.ruleRhs {env : Env} {c₀ : ConstantInfo}
    (h : ConsCrossEnv env c₀) {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule}
    (hc : ConstantInfo.recInfo cv mI rP rules ∈ env.consts)
    {r : RecRule} (hr : r ∈ rules) : ConsCrossAt c₀ (RecRule.rhs r) :=
  fun tbl heq i => ((h tbl heq i).rule cv mI rP rules hc r hr).1

theorem ConsCrossEnv.rulePin {env : Env} {c₀ : ConstantInfo}
    (h : ConsCrossEnv env c₀) {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule}
    (hc : ConstantInfo.recInfo cv mI rP rules ∈ env.consts)
    {r : RecRule} (hr : r ∈ rules) {lvls : List Level} {pins : List Expr}
    (hn : RecRule.fire r = .nested lvls pins) {pin : Expr}
    (hp : pin ∈ pins) : ConsCrossAt c₀ pin :=
  fun tbl heq i =>
    ((h tbl heq i).rule cv mI rP rules hc r hr).2 lvls pins hn pin hp

/-- The pin at an index (`getD`), whether in range or the default. -/
theorem ConsCrossEnv.rulePinD {env : Env} {c₀ : ConstantInfo}
    (h : ConsCrossEnv env c₀) {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule}
    (hc : ConstantInfo.recInfo cv mI rP rules ∈ env.consts)
    {r : RecRule} (hr : r ∈ rules) {lvls : List Level} {pins : List Expr}
    (hn : RecRule.fire r = .nested lvls pins) (i : Nat) :
    ConsCrossAt c₀ (pins.getD i default) := by
  by_cases hi : i < pins.length
  · exact h.rulePin hc hr hn (ConLeche.getD_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    intro _ _ _
    show Expr.NoProjAt _ _ (Expr.bvar 0)
    simp

end ConLeche.Model
