module

public import IxC.Kernel.Model.Open.Certs
public import IxC.Kernel.Model.Open.Irrel

@[expose] public section

/-!
# The rules' soundness over the public `Model`: the stored environment

The rules read these facts about the stored environment that `Model` does not state, each
checked by the kernel when it stores a declaration and held by the fold's invariant:

* `StoredClosed`: the stored terms are closed (`Open/Core.lean`);
* `StoredArities`: the telescopes the laws read have their binders (`Open/Certs.lean`);
* `StoredTables`: a stored projection table is its structure's. The table names its
  structure, its guard level is bounded by the structure's sort where the structure is not
  a proposition (`TowerO5`), the structure is stored as an inductive whose η record names
  the table, and the constructor as a constructor of the structure at the table's arities.
  Each clause is stated of the constant the environment stores at the key, if any, so a
  sub-environment whose lookups are the environment's keeps it.
* `StoredEtaRules`: an η-flagged recursor rule's constructor carries its family's level
  parameters.
* `StoredBodies`: a stored projection table's field types have no free variable and are
  scoped at the parameters and the subject.
* `StoredRules`: a firing recursor rule's constructor has its binders, and the recursor's
  major premise's domain has the rule's shape.

`StoredEnv` bundles them (`StoredEnv.of_find`, `EnvModelM.storedEnv`).
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules

universe w

/-- **A stored projection table is its structure's**: at every field `i` of the table of `T`,
the entry names `T`, its guard level is bounded where `T` is not a proposition (`TowerO5`),
`T` is stored as an inductive whose η record (if `T` claims η) names the entry's
constructor and arities, and the constructor is stored as a constructor of `T` at the
entry's arities and level parameters: its type is `∀ (params) (fields), T.{lps} params`. -/
def StoredTables (env : Env md) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md), env.findProj? T i = some entry →
    entry.structName = T ∧ Ix.Kernel.Model.TowerO5 entry ∧
    (∀ ci, env.find? T = some ci → ∃ (cvT : ConstantVal md) (capsT : IndCaps md),
      ci = .indInfo cvT capsT ∧
      (capsT.eta = true → capsT.etaCtor = some entry.ctor ∧
        capsT.etaParams = entry.numParams ∧ capsT.etaFields = entry.numFields)) ∧
    ∀ (cvC : ConstantVal md) (nP nF : Nat),
      env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
      nP = entry.numParams ∧ nF = entry.numFields ∧ cvC.levelParams = entry.levelParams ∧
      ∃ bs, cvC.type.stripPis (entry.numParams + entry.numFields) = some (bs,
        Expr.mkAppN (.const T (entry.levelParams.map .param))
          ((List.range entry.numParams).map fun k =>
            .bvar (entry.numFields + entry.numParams - 1 - k)))

/-- An environment whose lookups and tables are the environment's keeps its tables'
facts. -/
theorem StoredTables.of_find {env env' : Env md} (h : StoredTables env)
    (hf : ∀ n ci, env'.find? n = some ci → env.find? n = some ci)
    (hp : ∀ T i, env'.findProj? T i = env.findProj? T i) : StoredTables env' := by
  intro T i entry hP
  obtain ⟨hsn, hO5, hT, hC⟩ := h T i entry (by rw [← hp]; exact hP)
  exact ⟨hsn, hO5, fun ci hci => hT ci (hf _ _ hci),
    fun cvC nP nF hci => hC cvC nP nF (hf _ _ hci)⟩

/-- **An η-flagged recursor rule's constructor carries its family's level parameters**: at a
stored recursor's rule with the η flag, whose stored constructor's result is the stored family
`T`, the constructor's level parameters are `T`'s. The kernel records the flag only at the
family's own constructor. -/
def StoredEtaRules (env : Env md) : Prop :=
  ∀ (recName : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md))
    (rl : RecRule md), env.find? recName = some (.recInfo cv mI rP rules) → rl ∈ rules →
    rl.eta = true → ∀ (cvj : ConstantVal md) (cnP cnF : Nat),
    env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
    ∀ (T : Key md) (us₀ : List Level) (cvT : ConstantVal md) (caps : IndCaps md),
      (cvj.type.piResult).getAppFn = .const T us₀ → env.find? T = some (.indInfo cvT caps) →
      cvj.levelParams = cvT.levelParams

theorem StoredEtaRules.of_find {env env' : Env md} (h : StoredEtaRules env)
    (hf : ∀ n ci, env'.find? n = some ci → env.find? n = some ci) : StoredEtaRules env' :=
  fun recName cv mI rP rules rl hr hrl he cvj cnP cnF hc T us₀ cvT caps hp hT =>
    h recName cv mI rP rules rl (hf _ _ hr) hrl he cvj cnP cnF (hf _ _ hc) T us₀ cvT caps hp
      (hf _ _ hT)

/-- **A stored projection table's field types are scoped**: at every field, the stored type
body has no free variable, and its loose bound variables are the parameters and the subject. -/
def StoredBodies (env : Env md) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md), env.findProj? T i = some entry →
    entry.body.hasFvar = false ∧ entry.body.looseBVarsBounded (entry.numParams + 1) = true

theorem StoredBodies.of_find {env env' : Env md} (h : StoredBodies env)
    (hp : ∀ T i, env'.findProj? T i = env.findProj? T i) : StoredBodies env' :=
  fun T i entry hP => h T i entry (by rw [← hp]; exact hP)

/-- **The environment's well-formedness scopes the tables' field types.** -/
theorem EnvWF.storedBodies {env : Env md} (h : EnvWF env) : StoredBodies env :=
  fun _ _ _ hP => ⟨(Ix.Kernel.projEntry_body_wf h hP).1, (Ix.Kernel.projEntry_body_wf h hP).2.2.2⟩

/-- **A firing recursor rule's shape**: at a stored recursor's rule that fires, the rule
prefix is within the major premise's position; the rule's constructor, if stored, is stored
at the rule's counts, with a binder for each of its parameters and fields, and a canonical
rule has the shape its install tested (`Expr.recRulePlain`); a certified nested rule has
one stored instantiation per constructor parameter, closed and scoped in the rule prefix,
and the recursor's major premise's domain is the family at the rule's levels applied to
those instantiations lifted past the indices, then to the indices. -/
def StoredRules (env : Env md) : Prop :=
  ∀ (r : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
    env.find? r = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules, rl.fire ≠ .inert →
    rP ≤ mI ∧
    (∀ (cvC : ConstantVal md) (nP nF : Nat), env.find? rl.ctor = some (.ctorInfo cvC nP nF) →
      nP = rl.ctorParams ∧ nF = rl.nfields ∧ (cvC.type.stripPis (nP + nF)).isSome = true ∧
      (rl.fire = .plain → Expr.recRulePlain cv.type mI rP nP cvC.levelParams = true)) ∧
    ∀ (lvls : List Level) (pins : List (Expr md)), rl.fire = .nested lvls pins →
      pins.length = rl.ctorParams ∧
      (∀ pin ∈ pins, pin.hasFvar = false ∧ pin.looseBVarsBounded rP = true) ∧
      ∃ pre dom body bm D,
        cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
        dom.getAppFn = .const D lvls ∧
        dom.getAppArgs =
          pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
            (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i))

theorem StoredRules.of_find {env env' : Env md} (h : StoredRules env)
    (hf : ∀ n ci, env'.find? n = some ci → env.find? n = some ci) : StoredRules env' := by
  intro r cv mI rP rules hr rl hrl hfire
  obtain ⟨h1, h2, h3⟩ := h r cv mI rP rules (hf _ _ hr) rl hrl hfire
  exact ⟨h1, fun cvC nP nF hc => h2 cvC nP nF (hf _ _ hc), h3⟩

variable {V : Type w} [SetTheory V]

/-- **The fold's invariant holds the rules' shapes**: the recursor's constructor records
(`RecCtorsStored`), the fired law's prefix bound, and the nested shape (`EnvWF`). -/
theorem EnvModelM.storedRules {μ : CheckMode} {env : Env md}
    (m : Ix.Kernel.Model.EnvModelM V μ env) : StoredRules env := by
  intro r cv mI rP rules hr rl hrl hfire
  obtain ⟨⟨cvj, hfj, hplain, hnestLen, -, hstrip⟩, -, -⟩ :=
    m.base2.rec_ctors r cv mI rP rules hr rl hrl
  have hrPmI := (m.rec_rules (fun _ => 0) r cv mI rP rules hr rl hrl hfire).1
  obtain ⟨-, -, -, -, -, h6, -⟩ := m.base2.wf _ (List.mem_of_find?_eq_some hr)
  refine ⟨hrPmI, fun cvC nP nF hc => ?_, fun lvls pins hn => ?_⟩
  · rw [hfj] at hc
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc)
    exact ⟨rfl, rfl, hstrip, hplain⟩
  · obtain ⟨-, -, hpins, hshape⟩ := (h6 cv mI rP rules rfl rl hrl).2.2.2.2 lvls pins hn
    exact ⟨hnestLen lvls pins hn, fun pin hp => ⟨(hpins pin hp).1, (hpins pin hp).2.2.2⟩, hshape⟩

/-- **The fold's invariant holds the tables' facts**: the tower law's head data
(`TowerEntryLaw`) and the table discipline's (`TowerHead`). -/
theorem EnvModelM.storedTables {μ : CheckMode} {env : Env md}
    (m : Ix.Kernel.Model.EnvModelM V μ env) : StoredTables env := by
  intro T i entry hP
  obtain ⟨hsn, -, -, ⟨cvT, capsT, hfT, -, heta⟩, hO5, -⟩ := m.tower_ok (fun _ => 0) T i entry hP
  obtain ⟨-, -, -, -, ⟨cvC, hfC, hlpsC, bs, hs⟩⟩ := m.base2.proj_ok.towerHead hP
  refine ⟨hsn, hO5, fun ci hci => ?_, fun cvC' nP nF hci => ?_⟩
  · rw [hfT] at hci
    cases hci
    exact ⟨cvT, capsT, rfl, fun he => (heta he).2⟩
  · rw [hfC] at hci
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hci)
    rw [hsn] at hs
    exact ⟨rfl, rfl, hlpsC, bs, hs⟩

/-- **The fold's invariant holds the η rules' level parameters** (the recursor's constructor
records, `RecCtorsStored`). -/
theorem EnvModelM.storedEtaRules {μ : CheckMode} {env : Env md}
    (m : Ix.Kernel.Model.EnvModelM V μ env) : StoredEtaRules env :=
  fun _ _ _ _ _ _ hr hrl he _ _ _ hc _ _ _ _ hp hT =>
    ((Ix.Kernel.recCtors_bits m.base2.rec_ctors hr hrl hc hp hT).2 he).2.2

/-- **The stored environment's facts the rules read**, in one bundle. -/
structure StoredEnv (env : Env md) : Prop where
  closed : StoredClosed env
  arities : StoredArities env
  tables : StoredTables env
  etaRules : StoredEtaRules env
  bodies : StoredBodies env
  rules : StoredRules env

/-- **A sub-environment keeps the bundle**: its constants are the environment's, and its
lookups and tables are too. -/
theorem StoredEnv.of_find {env env' : Env md} (h : StoredEnv env)
    (hsub : ∀ c ∈ env'.consts, c ∈ env.consts)
    (hf : ∀ n ci, env'.find? n = some ci → env.find? n = some ci)
    (hp : ∀ T i, env'.findProj? T i = env.findProj? T i) : StoredEnv env' :=
  ⟨h.closed.of_sub hsub, h.arities.of_find hf, h.tables.of_find hf hp, h.etaRules.of_find hf,
    h.bodies.of_find hp, h.rules.of_find hf⟩

/-- **The fold's invariant holds the bundle.** -/
theorem EnvModelM.storedEnv {μ : CheckMode} {env : Env md}
    (m : Ix.Kernel.Model.EnvModelM V μ env) : StoredEnv env :=
  ⟨EnvWF.storedClosed m.base2.wf, EnvModel.storedArities m.base2, EnvModelM.storedTables m,
    EnvModelM.storedEtaRules m, EnvWF.storedBodies m.base2.wf, EnvModelM.storedRules m⟩

end Ix.Kernel.Open
