import IxVMRefinement.RoleOps.Interface

/-! # What the checker's native arithmetic reads of a stored operation

Once an operation is stored, later declarations are checked with it in force: the checker folds
its applications to literals (`Red.natOp`, which reads `natOpStored`), and for `Nat.add` rewrites
offsets (`Red.natAddSucc`, `Red.natAddZero`, `DefEq.natOffset`, which read `natAddTyOk`). The
scoped core reads both through the role fields of `CoreCompanions`, at the roles in force.

* `opCompanion_installed`: the two stored shapes hold of an operation just installed. For
  `Nat.add` the outer binder's datum `never` is read off the typing of the pinned type.
* `coreCompanions_installed`: the companions at an unchanged group limit are kept by the install.
* `coreCompanions_withOps`: the companions at a group limit that puts stored operations in
  force.
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KExpr KKey Ctx)
open IxVM.Refinement.Decl (isBaseKey ne_projTableName_of_isBaseKey CoreCompanions)
open Ix.Kernel (Env Expr ConstantInfo ConstantVal BinderMeta ReducibilityHint EnvExt
  natOpStored natLitSupported natName natPredName natAddName)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The outer binder of a typed `Nat → Nat → Nat` carries the datum `never`: its codomain
`Nat → Nat` is not a proposition. -/
theorem outer_pw_never {env : Env .anon} {mb₁ mb₂ : BinderMeta} {s : KExpr}
    (hnat : natLitSupported env = true)
    (hinf : Infer env .full 0
      (.forallE (.const natName []) (.forallE (.const natName []) (.const natName []) mb₂) mb₁)
      s) :
    mb₁.pw = .never := by
  unfold Ix.Kernel.natLitSupported at hnat
  simp only [Bool.and_eq_true] at hnat
  have hnatInd := hnat.1.1
  cases hfN : env.find? natName with
  | none => rw [hfN] at hnatInd; cases hnatInd
  | some ciN =>
    rw [hfN] at hnatInd
    cases ciN with
    | indInfo cvN capsN =>
      simp only [Ix.Kernel.natIndOk, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hnatInd
      cases hinf with
      | forallE _ _ hbs hv hz =>
        simp only [Ix.Kernel.Expr.instantiate1] at hbs
        cases hbs with
        | forallE _ _ hbs2 hv2 _ =>
          simp only [Ix.Kernel.Expr.instantiate1] at hbs2
          cases hbs2 with
          | const hfN' _ _ =>
            rw [hfN] at hfN'
            injection hfN' with hciN_eq
            subst hciN_eq
            simp only [Ix.Kernel.ConstantInfo.toConstantVal, hnatInd.1, hnatInd.2,
              Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst] at hv2
            have hv2_eq := IxVM.Refinement.Assembly.red_sort_inv hv2
            injection hv2_eq with hv2_s
            subst hv2_s
            have hv_eq := IxVM.Refinement.Assembly.red_sort_inv hv
            injection hv_eq with hv_s
            subst hv_s
            rw [← hz]
            rfl
    | _ => simp [Ix.Kernel.natIndOk] at hnatInd

/-- `natAddTyOk` once `Nat.add` is stored: the pinned type, with the outer binder's datum read
off the typing of the type. -/
theorem natAddTyOk_installed {env : Env .anon} {ty₀ val₀ ty val : KExpr}
    (hnat : natLitSupported env = true) (hfront : OpFront env ty₀ val₀ ty val)
    (hsh : OpTyShape natAddName ty) (hint : ReducibilityHint) :
    Ix.Kernel.Rules.natAddTyOk ((installed env natAddName ty val hint).find? natAddName)
      = true := by
  unfold OpTyShape at hsh
  rw [ite_eq_right (by decide : ¬ ((natAddName : KKey) = natPredName))] at hsh
  obtain ⟨mb₁, mb₂, rfl⟩ := hsh
  have hcod : opCod (natAddName : KKey) = natName := ite_eq_right (by decide)
  obtain ⟨s, u, hinf, -⟩ := hfront.tySort
  rw [hcod] at hinf
  have hpw := outer_pw_never hnat hinf
  rw [installed_find_self]
  simp [Ix.Kernel.Rules.natAddTyOk, hcod, hpw]

/-- **What the core's companions read of an operation role stored in `env`**: the operation is
stored as a definition, and `Nat.add` at its pinned type with the outer binder's datum
`never`. -/
def OpCompanion (env : Env .anon) (r : Ix.Kernel.Role) : Prop :=
  (Ix.Kernel.Key.role r : KKey) ∈ opNames ∧ natOpStored env (.role r) = true ∧
    (r = .natAdd → Ix.Kernel.Rules.natAddTyOk (env.find? natAddName) = true)

theorem OpCompanion.mono {env env' : Env .anon} {r : Ix.Kernel.Role} (h : EnvExt env env')
    (hc : OpCompanion env r) : OpCompanion env' r :=
  ⟨hc.1, h.natOpStored_mono hc.2.1,
    fun hr => h.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (hc.2.2 hr) rfl⟩

/-- The companion facts of an operation hold once it is stored. -/
theorem opCompanion_installed {env : Env .anon} {r : Ix.Kernel.Role} {ty₀ val₀ ty val : KExpr}
    (hc : (Ix.Kernel.Key.role r : KKey) ∈ opNames) (hp : OpPrefix env (.role r))
    (hfront : OpFront env ty₀ val₀ ty val) (hsh : OpTyShape (.role r) ty)
    (hint : ReducibilityHint) :
    OpCompanion (installed env (.role r) ty val hint) r := by
  have hbase := isBaseKey_of_mem_opNames hc
  refine ⟨hc, natOpStored_of_storedOk (natOpStoredOk_installed hp hbase hsh val hint), ?_⟩
  intro hr
  subst hr
  exact natAddTyOk_installed hp.natLit hfront hsh hint

/-- The record companions and the role companions of the roles already in force are kept by an
operation's install. -/
theorem coreCompanions_installed {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Env .anon} {c : KKey} (hc : c ∈ opNames) (hfresh : env.find? c = none)
    (h : CoreCompanions ⟨E, env, t, lim⟩) (ty val : KExpr) (hint : ReducibilityHint) :
    CoreCompanions ⟨E, installed env c ty val hint, t, lim⟩ :=
  h.cons_value (ci := .defnInfo ⟨c, [], ty⟩ val hint) hfresh
    (fun _ => ne_projTableName_of_isBaseKey (isBaseKey_of_mem_opNames hc))
    (fun _ _ _ _ e => nomatch e) (fun _ _ _ e => nomatch e)

private theorem basisRoles_not_ops :
    ([Ix.Kernel.Role.nat, .natZero, .natSucc, .string, .eq, .quot].all
      (fun r => !opNames.contains (Ix.Kernel.Key.role r : KKey))) = true := by decide

/-- **The companions at a group limit that puts stored operations in force.** If every role in
force at `lim'` is in force at `lim` or is an operation with its companion facts in `env`, the
companions at `lim` give those at `lim'`. An operation's group holds that operation alone, so
this raises the limit past the group of an operation just installed. -/
theorem coreCompanions_withOps {E : Ixon.Env} {env : Env .anon} {t : Ix.Kernel.RoleTable}
    {lim lim' : Option Nat} (h : CoreCompanions ⟨E, env, t, lim⟩)
    (hnew : ∀ r, Ctx.inForce ⟨E, env, t, lim'⟩ r →
      Ctx.inForce ⟨E, env, t, lim⟩ r ∨ OpCompanion env r) :
    CoreCompanions ⟨E, env, t, lim'⟩ := by
  have hold : ∀ r, r ∈ [Ix.Kernel.Role.nat, .natZero, .natSucc, .string, .eq, .quot] →
      Ctx.inForce ⟨E, env, t, lim'⟩ r → Ctx.inForce ⟨E, env, t, lim⟩ r := by
    intro r hr hf
    rcases hnew r hf with h1 | ⟨hop, -, -⟩
    · exact h1
    · have hb : (!opNames.contains (Ix.Kernel.Key.role r : KKey)) = true :=
        List.all_eq_true.mp basisRoles_not_ops r hr
      rw [List.contains_iff_mem.mpr hop] at hb
      exact absurd hb (by decide)
  exact
    { natLit := fun h1 h2 h3 =>
        h.natLit (hold _ (by simp) h1) (hold _ (by simp) h2) (hold _ (by simp) h3)
      strLit := fun h1 => h.strLit (hold _ (by simp) h1)
      natOps := fun r hr hm => by
        rcases hnew r hr with h1 | ⟨-, hs, -⟩
        · exact h.natOps r h1 hm
        · exact hs
      natAdd := fun h1 => by
        rcases hnew _ h1 with h2 | ⟨-, -, ha⟩
        · exact h.natAdd h2
        · exact ha rfl
      eqStored := fun h1 => h.eqStored (hold _ (by simp) h1)
      primEqn := fun ⟨r, hge, hf⟩ => by
        rcases hnew r hf with h1 | ⟨hop, -, -⟩
        · exact h.primEqn ⟨r, hge, h1⟩
        · exfalso
          have hlt : ∀ r', (Ix.Kernel.Key.role r' : KKey) ∈ opNames → Ix.SpecDigest.groupOf r' < 46 := by
            intro r' hr'
            cases r' <;> first | exact absurd hr' (by decide) | decide
          exact Nat.not_lt.mpr hge (hlt r hop)
      quotBasis := fun h1 => h.quotBasis (hold _ (by simp) h1)
      recMajorRecord := h.recMajorRecord
      recRulesNodupAndProj := h.recRulesNodupAndProj
      recPlain := h.recPlain
      ruleCtorHead := h.ruleCtorHead }

end IxVM.Refinement.RoleOps
