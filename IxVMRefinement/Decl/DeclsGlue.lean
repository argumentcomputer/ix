import IxVMRefinement.Core.Ctx
import IxVMRefinement.Assembly.ClaimsL1L6
import Ix.IxVM.Consistency.Restrict
import IxC.Kernel.Model.JudgeRules
import IxC.Kernel.Model.StoreCompanions
import IxC.Kernel.Model.StoreRecShape
import IxC.Kernel.Model.StoreFold

/-! # Unified declaration fold invariant, `claimedEnv` restriction, and per-route refinement glue

Unifies the model-tier and store-tier declaration invariants into the single Wave-5 fold invariant
`FoldInv V env` (`EnvModelT V .verified env` paired with `FoldStoreInv env`), proving:

* **Structural non-aux invariants, `StrongEnvProps`, `DeclsStrong`, and `claimedEnv` model
  existence**: `NonAuxKey`, `ConstantInfoNonAux`, `DeclNonAux`, `StrongEnvProps` (`TableBodies` plus
  non-auxiliary projection-table constructor keys on kept structures), `DeclsStrong`, and
  `claimedEnv_models_of_installs` (`∀ V [SetTheory V], Nonempty (Model V (claimedEnv env))`).
* **Structure η shape (`EtaShape`)**: maintained across every `DeclRunJ rulesJ` step (including the
  pinned `PUnit` basis block and native one-constructor index-free blocks), discharging
  `EnvFacts.etaSort` unconditionally and `etaType` on closed parameter spines (`etaType_of_closed`).
* **`FoldStoreInv` and `FoldInv`**: empty-environment initialization (`foldStoreInv_empty`,
  `foldInv_empty`), `EnvModelOk` and `StrongEnvProps` projections (`foldInv_envModelOk`,
  `foldInv_strongEnvProps`, `foldInv_etaFamiliesClosed`, `foldInv_tableBodies`), declaration-owned
  `Core.EnvFacts` projections (`FoldStoreInv.toEnvFacts`), and uniform step preservation along
  `DeclRunJ rulesJ (IndRoutesJ rulesJ env)` (`foldStoreInv_step_declRunJ`, `foldInv_step_declRunJ`).
* **Per-route `FoldInv` preservation and `InstallStep` bridges**: explicit step and `InstallStep`
  theorems for `DeclAxiomRunJ` (standard axioms, inert axioms, `quotSound`, and `sorryAx`),
  `DeclDefnRunJ`, `DeclThmRunJ`, `DeclOpaqueRunJ`, `DeclQuotRunJ`, `DeclBasisRun` (`.basisDecl` and
  pinned `.indDecl`), `DeclIndRunJ`, `DeclNativeRunJ`, `DeclNativeNoRecRunJ`, and
  `DeclRecTwinRunJ`, together with constructor prefix parameter-domain canonicalization helpers
  (`copyPrefixPis`). -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Mode Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule
  BasisKind QuotKind IndCaps NativeParts InductiveShape ProjTable EnvExt)
open Ix.Kernel.Rules (Annot Red DefEq Infer Grade)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ ValueFrontRunJ
  DeclDefnRunJ DeclThmRunJ DeclOpaqueRunJ DeclAxiomRunJ DeclBasisRun DeclRunJ DeclsRunJ
  IndRoutesJ DeclIndRunJ IndMembersRunJ ProvisionRecsRunJ IndRecsFoldRunJ IndRecsRunJ
  DeclNativeRunJ DeclNativeNoRecRunJ DeclRecTwinRunJ TwinRecPart twinModels twinProv twinRecs
  SumIndRunJ SumCtorsRunJ SumCtorRunJ FormerStoredJ nativePartsNoRec? letFree)
open Ix.Kernel.Model (rulesJ EnvModel EnvModelM EnvModelT EnvModelOk JudgeFrames NewSat NotProj
  TableBodies ThmTyped RecK EtaTowers RecShape)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Section 1: `NonAuxKey`, `DeclNonAux`, `StrongEnvProps`, `DeclsStrong`, and `claimedEnv` -/

/-- A key that is not derived (`Key.aux`), i.e., `.id` or `.role`. -/
def NonAuxKey {md : Mode} (k : Ix.Kernel.Key md) : Prop :=
  ∀ b s, k ≠ .aux b s

theorem isAux_eq_false_iff {md : Mode} {k : Ix.Kernel.Key md} :
    k.isAux = false ↔ NonAuxKey k := by
  cases k <;> simp [Ix.Kernel.Key.isAux, NonAuxKey]

/-- Structural non-aux property of a `ConstantInfo`. -/
def ConstantInfoNonAux {md : Mode} (ci : Ix.Kernel.ConstantInfo md) : Prop :=
  NonAuxKey ci.name ∧
  ci.toConstantVal.type.RefsIn NonAuxKey ∧
  (match ci with
    | .defnInfo _ v _ => v.RefsIn NonAuxKey
    | .thmInfo _ v => v.RefsIn NonAuxKey
    | .recInfo _ _ _ rules => ∀ rl ∈ rules, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey
    | _ => True)

/-- Every constant in `IxVM.Consistency.installs d` is `ConstantInfoNonAux`, and the names of
`IxVM.Consistency.installs d` are pairwise distinct. -/
def DeclNonAux (d : Ix.Kernel.Declaration .anon) : Prop :=
  (∀ ci₀ ∈ IxVM.Consistency.installs d, ConstantInfoNonAux ci₀) ∧
  ((IxVM.Consistency.installs d).map (·.name)).Nodup

/-- Boolean mirror of `Expr.RefsIn NonAuxKey`. -/
def exprNonAuxB {md : Mode} : Ix.Kernel.Expr md → Bool
  | .bvar _ => true
  | .fvar _ _ => true
  | .sort _ => true
  | .const n _ => !n.isAux
  | .app f a => exprNonAuxB f && exprNonAuxB a
  | .lam ty b _ => exprNonAuxB ty && exprNonAuxB b
  | .forallE ty b _ => exprNonAuxB ty && exprNonAuxB b
  | .letE ty v b _ => exprNonAuxB ty && exprNonAuxB v && exprNonAuxB b
  | .lit _ => true
  | .proj _ _ e => exprNonAuxB e

theorem exprNonAuxB_eq_true_iff {md : Mode} :
    ∀ e : Ix.Kernel.Expr md, exprNonAuxB e = true ↔ e.RefsIn NonAuxKey
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ => by simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn]
  | .const n _ => by simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, isAux_eq_false_iff]
  | .app f a => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true,
      exprNonAuxB_eq_true_iff f, exprNonAuxB_eq_true_iff a]
  | .lam ty b _ => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true,
      exprNonAuxB_eq_true_iff ty, exprNonAuxB_eq_true_iff b]
  | .forallE ty b _ => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true,
      exprNonAuxB_eq_true_iff ty, exprNonAuxB_eq_true_iff b]
  | .letE ty v b _ => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true, and_assoc,
      exprNonAuxB_eq_true_iff ty, exprNonAuxB_eq_true_iff v, exprNonAuxB_eq_true_iff b]
  | .proj _ _ e => by simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, exprNonAuxB_eq_true_iff e]

/-- Boolean mirror of `ConstantInfoNonAux`. -/
def cinfoNonAuxB {md : Mode} (ci : Ix.Kernel.ConstantInfo md) : Bool :=
  !ci.name.isAux &&
  exprNonAuxB ci.toConstantVal.type &&
  match ci with
  | .defnInfo _ v _ => exprNonAuxB v
  | .thmInfo _ v => exprNonAuxB v
  | .recInfo _ _ _ rules => rules.all fun rl => !rl.ctor.isAux && exprNonAuxB rl.rhs
  | _ => true

theorem cinfoNonAuxB_eq_true_iff {md : Mode} (ci : Ix.Kernel.ConstantInfo md) :
    cinfoNonAuxB ci = true ↔ ConstantInfoNonAux ci := by
  cases ci <;>
    simp [cinfoNonAuxB, ConstantInfoNonAux, Bool.and_eq_true,
      isAux_eq_false_iff, exprNonAuxB_eq_true_iff, List.all_eq_true, and_assoc]

theorem basisDeclsA_nonAux (kind : Ix.Kernel.BasisKind) :
    ∀ ci₀ ∈ (kind.declsA : List (Ix.Kernel.ConstantInfo .anon)), ConstantInfoNonAux ci₀ := by
  have hb : ((kind.declsA : List (Ix.Kernel.ConstantInfo .anon)).all cinfoNonAuxB) = true := by
    cases kind <;> decide
  intro ci₀ hmem
  exact (cinfoNonAuxB_eq_true_iff ci₀).mp (List.all_eq_true.mp hb ci₀ hmem)

theorem basisDeclsA_nodup (kind : Ix.Kernel.BasisKind) :
    (((kind.declsA : List (Ix.Kernel.ConstantInfo .anon)).map (·.name))).Nodup := by
  have hroles :
      ∃ rs : List Ix.Kernel.Role,
        ((kind.declsA : List (Ix.Kernel.ConstantInfo .anon)).map (·.name)) =
          rs.map Ix.Kernel.Key.role ∧ rs.Nodup := by
    cases kind with
    | eqK => exact ⟨[.eq, .eqRefl, .eqRec], rfl, by decide⟩
    | natK => exact ⟨[.nat, .natZero, .natSucc, .natRec], rfl, by decide⟩
    | punitK => exact ⟨[.punit, .punitUnit, .punitRec], rfl, by decide⟩
    | emptyK => exact ⟨[.empty, .emptyRec], rfl, by decide⟩
    | falseK => exact ⟨[.false, .falseRec], rfl, by decide⟩
    | quotK => exact ⟨[.quot, .quotMk, .quotLift, .quotInd, .quotSound], rfl, by decide⟩
  obtain ⟨rs, heq, hnd⟩ := hroles
  rw [heq]
  exact hnd.map fun _ _ h => by injection h

private theorem glue_refsIn_mono {md : Mode} {K₁ K₂ : Ix.Kernel.Key md → Prop}
    (h : ∀ k, K₁ k → K₂ k) : ∀ {e : Ix.Kernel.Expr md}, e.RefsIn K₁ → e.RefsIn K₂ := by
  intro e
  induction e with
  | bvar _ | fvar _ _ | sort _ | lit _ => intro _; trivial
  | const n _ => exact h n
  | app _ _ ihf iha => intro ⟨hf, ha⟩; exact ⟨ihf hf, iha ha⟩
  | lam _ _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | forallE _ _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | letE _ _ _ _ iht ihv ihb => intro ⟨ht, hv, hb⟩; exact ⟨iht ht, ihv hv, ihb hb⟩
  | proj _ _ _ ihe => exact ihe

private theorem glue_refsIn_liftLooseBVars {md : Mode} {K : Ix.Kernel.Key md → Prop} (amt : Nat) :
    ∀ (e : Ix.Kernel.Expr md) (cut : Nat), e.RefsIn K →
      (Ix.Kernel.Expr.liftLooseBVars amt cut e).RefsIn K
  | .bvar _, cut, _ => by rw [Ix.Kernel.Expr.liftLooseBVars]; split <;> trivial
  | .fvar _ _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, hk => hk
  | .app f a, cut, ⟨hf, ha⟩ =>
    ⟨glue_refsIn_liftLooseBVars amt f cut hf, glue_refsIn_liftLooseBVars amt a cut ha⟩
  | .lam ty b _, cut, ⟨ht, hb⟩ =>
    ⟨glue_refsIn_liftLooseBVars amt ty cut ht, glue_refsIn_liftLooseBVars amt b (cut + 1) hb⟩
  | .forallE ty b _, cut, ⟨ht, hb⟩ =>
    ⟨glue_refsIn_liftLooseBVars amt ty cut ht, glue_refsIn_liftLooseBVars amt b (cut + 1) hb⟩
  | .letE ty v b _, cut, ⟨ht, hv, hb⟩ =>
    ⟨glue_refsIn_liftLooseBVars amt ty cut ht, glue_refsIn_liftLooseBVars amt v cut hv,
      glue_refsIn_liftLooseBVars amt b (cut + 1) hb⟩
  | .proj _ _ e, cut, he => glue_refsIn_liftLooseBVars amt e cut he

private theorem glue_refsIn_instantiate1Lift {md : Mode} {K : Ix.Kernel.Key md → Prop}
    {v : Ix.Kernel.Expr md} (hv : v.RefsIn K) :
    ∀ (e : Ix.Kernel.Expr md) (d : Nat), e.RefsIn K → (e.instantiate1Lift v d).RefsIn K
  | .bvar _, d, _ => by
    rw [Ix.Kernel.Expr.instantiate1Lift]
    split
    · exact glue_refsIn_liftLooseBVars d v 0 hv
    · split <;> trivial
  | .fvar _ _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, hk => hk
  | .app f a, d, ⟨hf, ha⟩ =>
    ⟨glue_refsIn_instantiate1Lift hv f d hf, glue_refsIn_instantiate1Lift hv a d ha⟩
  | .lam ty b _, d, ⟨ht, hb⟩ =>
    ⟨glue_refsIn_instantiate1Lift hv ty d ht, glue_refsIn_instantiate1Lift hv b (d + 1) hb⟩
  | .forallE ty b _, d, ⟨ht, hb⟩ =>
    ⟨glue_refsIn_instantiate1Lift hv ty d ht, glue_refsIn_instantiate1Lift hv b (d + 1) hb⟩
  | .letE ty val b _, d, ⟨ht, hval, hb⟩ =>
    ⟨glue_refsIn_instantiate1Lift hv ty d ht, glue_refsIn_instantiate1Lift hv val d hval,
      glue_refsIn_instantiate1Lift hv b (d + 1) hb⟩
  | .proj _ _ e, d, he => glue_refsIn_instantiate1Lift hv e d he

private theorem glue_annotates_refsIn {K : Ix.Kernel.Key .anon → Prop}
    {e' e : Ix.Kernel.Expr .anon} (h : IxVM.Consistency.Annotates e' e) :
    e.RefsIn K → e'.RefsIn K := by
  induction h with
  | bvar | fvar _ _ | sort | lit => intro _; trivial
  | const => intro hk; exact hk
  | app _ _ ihf iha => intro ⟨hf, ha⟩; exact ⟨ihf hf, iha ha⟩
  | lam _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | forallE _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | proj _ ihe => intro he; exact ihe he
  | letE _ ih => intro ⟨_, hv, hb⟩; exact ih (glue_refsIn_instantiate1Lift hv _ 0 hb)

private theorem glue_refsIn_instPisAtLift {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (as : List (Ix.Kernel.Expr md)) :
    ∀ {e r : Ix.Kernel.Expr md},
      (∀ a ∈ as, a.RefsIn K) → e.RefsIn K →
      Ix.Kernel.Expr.instPisAtLift as e = some r → r.RefsIn K := by
  induction as with
  | nil =>
    intro e r _ he h
    simp only [Ix.Kernel.Expr.instPisAtLift, Option.some.injEq] at h
    rwa [← h]
  | cons a as ih =>
    intro e r has he h
    cases e with
    | forallE _ body _ =>
      exact ih (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (glue_refsIn_instantiate1Lift (has a List.mem_cons_self) body 0 he.2) h
    | _ => cases h

private theorem glue_structProjBodiesGo_spec {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (T : Ix.Kernel.Key md) (k : Nat) :
    ∀ (i : Nat) {r : Ix.Kernel.Expr md} {bs : List (Ix.Kernel.Expr md)},
      r.RefsIn K → Ix.Kernel.structProjBodiesGo T k i r = some bs →
      bs.length = k ∧ ∀ b ∈ bs, b.RefsIn K := by
  induction k with
  | zero =>
    intro _ _ bs _ h
    simp only [Ix.Kernel.structProjBodiesGo, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hm => nomatch hm⟩
  | succ k ih =>
    intro i r bs hr h
    cases r with
    | forallE fdom body _ =>
      obtain ⟨hfdom, hbody⟩ := hr
      simp only [Ix.Kernel.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨bs₀, hgo, rfl⟩ := h
      have harg : (Ix.Kernel.structProjArgP T i).RefsIn K := trivial
      obtain ⟨hlen, hall⟩ := ih (i + 1) (glue_refsIn_instantiate1Lift harg body 0 hbody) hgo
      refine ⟨by simp [hlen], fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | htl
      · exact hfdom
      · exact hall b htl
    | _ => cases h

private theorem glue_structProjBodies_spec {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (T : Ix.Kernel.Key md) (nP nF : Nat) {cty : Ix.Kernel.Expr md}
    {bodies : Array (Ix.Kernel.Expr md)}
    (hcty : cty.RefsIn K)
    (hbodies : Ix.Kernel.structProjBodies T nP nF cty = some bodies) :
    bodies.size = nF ∧ ∀ b ∈ bodies.toList, b.RefsIn K := by
  unfold Ix.Kernel.structProjBodies at hbodies
  cases hinst : Ix.Kernel.Expr.instPisAtLift (Ix.Kernel.structProjPs nP) cty with
  | none => rw [hinst] at hbodies; cases hbodies
  | some r =>
    rw [hinst, Option.map_eq_some_iff] at hbodies
    obtain ⟨bs, hgo, rfl⟩ := hbodies
    have hps : ∀ a ∈ Ix.Kernel.structProjPs (md := md) nP, a.RefsIn K := by
      intro a ha
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
      trivial
    have hr := glue_refsIn_instPisAtLift (Ix.Kernel.structProjPs nP) hps hcty hinst
    obtain ⟨hlen, hall⟩ := glue_structProjBodiesGo_spec T nF 0 hr hgo
    simpa using ⟨hlen, hall⟩

private theorem glue_installs_consts_origin :
    ∀ {ds : List (Ix.Kernel.Declaration .anon)} {env : Ix.Kernel.Env .anon},
      IxVM.Consistency.Installs ds env →
      ∀ c ∈ env.consts,
        (∃ d ∈ ds, ∃ ci₀ ∈ IxVM.Consistency.installs d, ci₀.name = c.name) ∨
        (∃ b s, c.name = .aux b s)
  | _, _, .nil, _, hc => nomatch hc
  | _, _, @IxVM.Consistency.Installs.snoc ds₀ d env₀ env₂ hprev hstep, c, hc => by
    obtain ⟨new, henv₂, -, -, -, horig⟩ := hstep
    rw [henv₂] at hc
    rcases List.mem_append.mp hc with hnew | hold
    · rcases horig c hnew with ⟨ci₀, hci₀, hname⟩ | haux
      · exact Or.inl ⟨d, List.mem_append_right _ List.mem_cons_self, ci₀, hci₀, hname⟩
      · exact Or.inr haux
    · rcases glue_installs_consts_origin hprev c hold with ⟨d₀, hd₀, ci₀, hci₀, hname⟩ | haux
      · exact Or.inl ⟨d₀, List.mem_append_left _ hd₀, ci₀, hci₀, hname⟩
      · exact Or.inr haux

private theorem glue_forall₂_mem_left {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hm => nomatch hm
  | _, _, .cons hr htl, x, hm => by
    rcases List.mem_cons.mp hm with rfl | hmem
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hry⟩ := glue_forall₂_mem_left htl x hmem
      exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

private theorem glue_installs_claimed_stored {ds : List (Ix.Kernel.Declaration .anon)}
    {env : Ix.Kernel.Env .anon}
    (h : IxVM.Consistency.Installs ds env)
    (hna : ∀ d ∈ ds, DeclNonAux d)
    {c : Ix.Kernel.ConstantInfo .anon}
    (hc : c ∈ (IxVM.Consistency.claimedEnv env).consts) :
    (∃ tbl, c = .projInfo tbl) ∨
      ∃ d ∈ ds, ∃ ci₀ ∈ IxVM.Consistency.installs d,
        IxVM.Consistency.StoredAs c ci₀ ∧ ConstantInfoNonAux ci₀ := by
  by_cases hproj : ∃ tbl, c = .projInfo tbl
  · exact Or.inl hproj
  · have hnproj : ∀ tbl, c ≠ .projInfo tbl := fun tbl heq => hproj ⟨tbl, heq⟩
    obtain ⟨hc_mem, hc_keep⟩ := List.mem_filter.mp hc
    have hc_not_aux : IxVM.Consistency.isModelAux c = false := by simpa using hc_keep
    rcases glue_installs_consts_origin h c hc_mem with ⟨d, hd, ci₀, hci₀, hname⟩ | ⟨b, s, haux⟩
    · obtain ⟨ci', hfind, hst⟩ := h.stored hd hci₀
      have hci_eq : c = ci' :=
        IxVM.Consistency.eq_of_name_eq h.nodup hc_mem
          (Ix.Kernel.Semantics.Env.find?_mem hfind)
          (hname.symm.trans (Ix.Kernel.Semantics.Env.find?_name hfind).symm)
      subst hci_eq
      exact Or.inr ⟨d, hd, ci₀, hci₀, hst, (hna d hd).1 ci₀ hci₀⟩
    · have haux_true : IxVM.Consistency.isModelAux c = true := by
        unfold IxVM.Consistency.isModelAux
        rw [haux]
        cases c with
        | projInfo tbl => exact absurd rfl (hnproj tbl)
        | _ => rfl
      rw [hc_not_aux] at haux_true
      cases haux_true

private theorem glue_findProj?_some_inv {env : Ix.Kernel.Env .anon} {T : Ix.Kernel.Key .anon}
    {i : Nat} {entry : Ix.Kernel.ProjEntry .anon}
    (h : env.findProj? T i = some entry) :
    ∃ tbl : Ix.Kernel.ProjTable .anon,
      env.find? (Ix.Kernel.projTableName T) = some (.projInfo tbl) ∧
      tbl.structName = T ∧
      i < tbl.numFields ∧
      entry = tbl.entry i ∧
      entry.ctor = tbl.ctor := by
  unfold Ix.Kernel.Env.findProj? at h
  cases hfind : env.find? (Ix.Kernel.projTableName T) with
  | none => rw [hfind] at h; cases h
  | some ci =>
    rw [hfind] at h
    cases ci with
    | projInfo tbl =>
      dsimp only at h
      split at h
      · next hlt =>
        injection h with hent
        have hname := Ix.Kernel.Semantics.Env.find?_name hfind
        change Ix.Kernel.Key.aux tbl.structName .projTable =
          Ix.Kernel.Key.aux T .projTable at hname
        injection hname with hT
        exact ⟨tbl, rfl, hT, hlt, hent.symm, by rw [← hent]; rfl⟩
      · cases h
    | _ => cases h

/-- Store-level projection-table companion properties required to restrict a model to `claimedEnv`:
`Ix.Kernel.Model.TableBodies env` together with non-auxiliary constructor keys on projection tables
of kept structures. -/
def StrongEnvProps (env : Ix.Kernel.Env .anon) : Prop :=
  Ix.Kernel.Model.TableBodies env ∧
  ∀ n tbl, env.find? n = some (.projInfo tbl) →
    NonAuxKey tbl.ctor ∨ ¬ IxVM.Consistency.KeptKey env tbl.structName

theorem strongEnvProps_empty : StrongEnvProps Ix.Kernel.Env.empty :=
  ⟨Ix.Kernel.Model.TableBodies.empty,
    fun _ _ h => by simp [Ix.Kernel.Env.find?, Ix.Kernel.Env.empty] at h⟩

/-- Step combinator for `StrongEnvProps` along any lookup-preserving extension `env → env₂`. -/
theorem strongEnvProps_step {env env₂ : Ix.Kernel.Env .anon}
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {x : Ix.Kernel.ConstantInfo .anon},
      env.find? k = some x → env₂.find? k = some x)
    (h : StrongEnvProps env)
    (htb : Ix.Kernel.Model.TableBodies env₂)
    (hnew : ∀ n tbl, env₂.find? n = some (.projInfo tbl) → env.find? n = none →
      NonAuxKey tbl.ctor ∨ ¬ IxVM.Consistency.KeptKey env₂ tbl.structName) :
    StrongEnvProps env₂ := by
  refine ⟨htb, fun n tbl hf => ?_⟩
  cases hold : env.find? n with
  | none => exact hnew n tbl hf hold
  | some c =>
    have h2 := hfind hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    rcases h.2 n tbl hold with hna | hnk
    · exact Or.inl hna
    · exact Or.inr fun hk₂ => hnk fun ci hf₁ => hk₂ ci (hfind hf₁)

/-- Step combinator for `StrongEnvProps` when no `.projInfo` entry is added. -/
theorem strongEnvProps_step_noProj {env env₂ : Ix.Kernel.Env .anon}
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {x : Ix.Kernel.ConstantInfo .anon},
      env.find? k = some x → env₂.find? k = some x)
    (h : StrongEnvProps env)
    (hno : Ix.Kernel.Model.NewSat env env₂ Ix.Kernel.Model.NotProj) :
    StrongEnvProps env₂ :=
  strongEnvProps_step hfind h
    (Ix.Kernel.Model.tableBodies_step_noProj hfind h.1 hno)
    fun n tbl hf hn => by
      rcases hno n (.projInfo tbl) hf with hold | hnp
      · rw [hold] at hn; cases hn
      · exact absurd rfl (hnp tbl)

/-- Strengthened `L5` fold obligation carrying `StrongEnvProps` alongside `EnvModelOk`. -/
def DeclsStrong
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) : Prop :=
  ∃ Inv : (V : Type u) → [Ix.Kernel.SetTheory V] → Ix.Kernel.Env .anon → Prop,
    (∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V Ix.Kernel.Env.empty) ∧
    (∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      Inv V env → Ix.Kernel.Model.EnvModelOk V .verified env ∧ StrongEnvProps env) ∧
    ∀ (calls : List (Call F)) (env : Ix.Kernel.Env .anon) (d : Ix.Kernel.Declaration .anon),
      IxVM.Consistency.Bounded calls → Checked calls env d →
        ∃ env₂, IxVM.Consistency.InstallStep env d env₂ ∧
          ∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V env → Inv V env₂

/-- `DeclsStrong S.Checked` directly implies `IxVM.Consistency.Decls S` for any `Seams` package. -/
theorem DeclsStrong.toDeclsOfSeams {S : IxVM.Consistency.Seams}
    (h : DeclsStrong.{u} S.Checked) :
    IxVM.Consistency.Decls.{u} S := by
  obtain ⟨Inv, hemp, hok, hstep⟩ := h
  exact ⟨Inv, hemp, fun V _ env hinv => (hok V env hinv).1, hstep⟩

/-- **Model existence for `claimedEnv env`** in every set theory from `Installs ds env`,
`DeclNonAux` on `ds`, `EnvModelOk`, and `StrongEnvProps`. -/
theorem claimedEnv_models_of_installs {ds : List (Ix.Kernel.Declaration .anon)}
    {env : Ix.Kernel.Env .anon}
    (hinst : IxVM.Consistency.Installs ds env)
    (hna : ∀ d ∈ ds, DeclNonAux d)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      Ix.Kernel.Model.EnvModelOk V .verified env ∧ StrongEnvProps env) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      Nonempty (Ix.Kernel.Model V (IxVM.Consistency.claimedEnv env)) := by
  intro V _
  obtain ⟨hok, htables, hprojCtor⟩ := hmodel V
  obtain ⟨M⟩ := IxVM.Consistency.model_of_envModelOk hok
  have hnd := hinst.nodup
  have hmono : ∀ {e : Ix.Kernel.Expr .anon},
      e.RefsIn NonAuxKey → e.RefsIn (IxVM.Consistency.KeptKey env) :=
    fun hr => glue_refsIn_mono (fun _ hk => IxVM.Consistency.keptKey_of_not_aux hk) hr
  have htype : ∀ c ∈ (IxVM.Consistency.claimedEnv env).consts,
      c.toConstantVal.type.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro c hc
    rcases glue_installs_claimed_stored hinst hna hc with ⟨tbl, rfl⟩ | ⟨_, _, ci₀, _, hst, hci₀⟩
    · trivial
    · exact hmono (glue_annotates_refsIn hst.1.2.2 hci₀.2.1)
  have hvalue : ∀ cv value hint,
      Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ (IxVM.Consistency.claimedEnv env).consts →
      value.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro cv value hint hc
    rcases glue_installs_claimed_stored hinst hna hc with ⟨_, heq⟩ | ⟨_, _, ci₀, _, hst, hci₀⟩
    · cases heq
    · cases ci₀ with
      | defnInfo _ v₀ _ => exact hmono (glue_annotates_refsIn hst.2.1 hci₀.2.2)
      | _ => exact hst.2.elim
  have hrhs : ∀ cv mI rP rules,
      Ix.Kernel.ConstantInfo.recInfo cv mI rP rules ∈ (IxVM.Consistency.claimedEnv env).consts →
      ∀ rl ∈ rules, rl.rhs.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro cv mI rP rules hc rl hrl
    rcases glue_installs_claimed_stored hinst hna hc with ⟨_, heq⟩ | ⟨_, _, ci₀, _, hst, hci₀⟩
    · cases heq
    · cases ci₀ with
      | recInfo _ _ _ rules₀ =>
        obtain ⟨rl₀, hrl₀_mem, hrl_st⟩ := glue_forall₂_mem_left hst.2.2.2 rl hrl
        exact hmono (glue_annotates_refsIn hrl_st.2.2 (hci₀.2.2 rl₀ hrl₀_mem).2)
      | _ => exact hst.2.elim
  have hctor : ∀ T i entry, (IxVM.Consistency.claimedEnv env).findProj? T i = some entry →
      IxVM.Consistency.KeptKey env T → IxVM.Consistency.KeptKey env entry.ctor := by
    intro T i entry hfp hKT
    rw [IxVM.Consistency.claimedEnv_findProj? hnd T i] at hfp
    obtain ⟨tbl, hfind_tbl, hT_eq, -, -, hctor_eq⟩ := glue_findProj?_some_inv hfp
    rw [hctor_eq]
    rcases hprojCtor (Ix.Kernel.projTableName T) tbl hfind_tbl with hna_ctor | hnk
    · exact IxVM.Consistency.keptKey_of_not_aux hna_ctor
    · rw [hT_eq] at hnk
      exact (hnk hKT).elim
  have hbody : ∀ T i entry, (IxVM.Consistency.claimedEnv env).findProj? T i = some entry →
      IxVM.Consistency.KeptKey env T → entry.body.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro T i entry hfp hKT
    have hK_ctor := hctor T i entry hfp hKT
    rw [IxVM.Consistency.claimedEnv_findProj? hnd T i] at hfp
    obtain ⟨tbl, hfind_tbl, -, hi_lt, rfl, hctor_eq⟩ := glue_findProj?_some_inv hfp
    rw [hctor_eq] at hK_ctor
    obtain ⟨cvC, hfind_ctor, hbodies, -⟩ := htables (Ix.Kernel.projTableName T) tbl hfind_tbl
    have hfind_claimed :
        (IxVM.Consistency.claimedEnv env).find? tbl.ctor =
          some (.ctorInfo cvC tbl.numParams tbl.numFields) := by
      rwa [IxVM.Consistency.claimedEnv_find? hK_ctor]
    have hcty_refs : cvC.type.RefsIn (IxVM.Consistency.KeptKey env) :=
      htype (.ctorInfo cvC tbl.numParams tbl.numFields)
        (Ix.Kernel.Semantics.Env.find?_mem hfind_claimed)
    obtain ⟨hsz, hall⟩ :=
      glue_structProjBodies_spec tbl.structName tbl.numParams tbl.numFields hcty_refs hbodies
    have hi_sz : i < tbl.bodies.size := by omega
    change (tbl.bodies.getD i default).RefsIn (IxVM.Consistency.KeptKey env)
    have hgetD_eq : tbl.bodies.getD i default = tbl.bodies[i] := by
      unfold Array.getD
      simp only [hi_sz, ↓reduceDIte]
      rfl
    rw [hgetD_eq]
    refine hall tbl.bodies[i] ?_
    rw [← Array.getElem_toList]
    exact List.getElem_mem _
  exact ⟨IxVM.Consistency.claimedModel M hnd htype hvalue hrhs hctor hbody⟩

/-! ### `StrongEnvProps` preservation across native inductive blocks and `DeclRunJ` -/

private theorem sumSplit_eq {rest : List (ConstantInfo .anon)}
    {cs : List (ConstantVal .anon × Nat × Nat)} {cvR : ConstantVal .anon} {mI rP : Nat}
    {rules : List (RecRule .anon)}
    (h : Ix.Kernel.sumSplit rest = some (cs, cvR, mI, rP, rules)) :
    rest = (cs.map fun c => .ctorInfo c.1 c.2.1 c.2.2) ++ [.recInfo cvR mI rP rules] := by
  induction rest generalizing cs with
  | nil => simp [Ix.Kernel.sumSplit] at h
  | cons hd tl ih =>
    cases hd with
    | recInfo cvR' mI' rP' rules' =>
      cases tl with
      | nil =>
        simp only [Ix.Kernel.sumSplit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        rfl
      | cons _ _ => simp [Ix.Kernel.sumSplit] at h
    | ctorInfo cvC nP nF =>
      simp only [Ix.Kernel.sumSplit, Option.map_eq_some_iff] at h
      obtain ⟨⟨cs₀, cvR₀, mI₀, rP₀, rules₀⟩, hs₀, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
      simp [ih hs₀]
    | _ => simp [Ix.Kernel.sumSplit] at h

/-- Exact member decomposition of a block accepted by `nativeShape?`. -/
theorem nativeShape?_block_eq {nPd : Nat} {block : List (ConstantInfo .anon)}
    {p : InductiveShape .anon}
    (h : Ix.Kernel.nativeShape? nPd block = some p) :
    ∃ (caps : IndCaps .anon) (cs : List (ConstantVal .anon × Nat × Nat))
      (mI rP : Nat) (rules : List (RecRule .anon)),
      block = .indInfo p.cvT caps ::
        ((cs.map fun c => .ctorInfo c.1 c.2.1 c.2.2) ++ [.recInfo p.cvR mI rP rules]) ∧
      p.ctors = cs.map (fun c => (c.1, c.2.2)) := by
  unfold Ix.Kernel.nativeShape? at h
  cases block with
  | nil => simp at h
  | cons hd rest =>
    cases hd with
    | indInfo cvT caps =>
      dsimp only at h
      cases hsp : Ix.Kernel.sumSplit rest with
      | none => rw [hsp] at h; simp at h
      | some q =>
        obtain ⟨cs, cvR, mI, rP, rules⟩ := q
        rw [hsp] at h
        dsimp only at h
        cases hcnt : Ix.Kernel.nativeCounts? nPd cvT cs mI rP with
        | none => rw [hcnt] at h; simp at h
        | some npni =>
          obtain ⟨nP, nIdx⟩ := npni
          rw [hcnt] at h
          dsimp only at h
          split at h
          · split at h <;>
              (simp only [Option.some.injEq] at h; subst h;
               exact ⟨caps, cs, mI, rP, rules, by rw [sumSplit_eq hsp], rfl⟩)
          · simp at h
    | _ => simp at h

/-- Exact member decomposition of a block accepted by `nativeParts?`. -/
theorem nativeParts?_block_eq {nPd : Nat} {block : List (ConstantInfo .anon)}
    {p₀ : NativeParts .anon}
    (h : Ix.Kernel.nativeParts? nPd block = some p₀) :
    ∃ (caps : IndCaps .anon) (cs : List (ConstantVal .anon × Nat × Nat))
      (mI rP : Nat) (rules : List (RecRule .anon)),
      block = .indInfo p₀.cvT caps ::
        ((cs.map fun c => .ctorInfo c.1 c.2.1 c.2.2) ++ [.recInfo p₀.cvR mI rP rules]) ∧
      p₀.ctors = cs.map (fun c => (c.1, c.2.2)) :=
  nativeShape?_block_eq (Ix.Kernel.nativeParts?_inv h).1

/-- Exact member decomposition of a block accepted by `nativePartsNoRec?`. -/
theorem nativePartsNoRec?_block_eq {nPd : Nat} {block : List (ConstantInfo .anon)}
    {p₀ : NativeParts .anon}
    (h : nativePartsNoRec? nPd block = some p₀) :
    ∃ (caps : IndCaps .anon) (cs : List (ConstantVal .anon × Nat × Nat)),
      block = .indInfo p₀.cvT caps :: (cs.map fun c => .ctorInfo c.1 c.2.1 c.2.2) ∧
      p₀.ctors = cs.map (fun c => (c.1, c.2.2)) := by
  unfold nativePartsNoRec? at h
  cases block with
  | nil => simp at h
  | cons hd rest =>
    cases hd with
    | indInfo cvT caps =>
      dsimp only at h
      split at h
      · obtain ⟨caps', cs, mI, rP, rules, hblk', hctors⟩ := nativeParts?_block_eq h
        injection hblk' with hhd htl
        obtain ⟨hcvT, rfl⟩ := ConstantInfo.indInfo.inj hhd
        have hrest_eq : rest = cs.map fun c => .ctorInfo c.1 c.2.1 c.2.2 :=
          (List.append_inj' htl (by simp)).1
        exact ⟨caps, cs, by rw [hcvT, hrest_eq], hctors⟩
      · simp at h
    | _ => simp at h

/-- Extract constructor-key `NonAuxKey` from `nativeParts?` on a block of `NonAuxKey` members. -/
theorem nonAuxKey_ctors_of_nativeParts {nPd : Nat} {block : List (ConstantInfo .anon)}
    {p₀ : NativeParts .anon}
    (hblk : ∀ ci ∈ block, NonAuxKey ci.name)
    (hparts : Ix.Kernel.nativeParts? nPd block = some p₀) :
    ∀ c ∈ p₀.ctors, NonAuxKey c.1.name := by
  obtain ⟨caps, cs, mI, rP, rules, hblk_eq, hctors_eq⟩ := nativeParts?_block_eq hparts
  intro c hc
  rw [hctors_eq] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  refine hblk (.ctorInfo c'.1 c'.2.1 c'.2.2) ?_
  rw [hblk_eq]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨c', hc', rfl⟩))

/-- Extract constructor-key `NonAuxKey` from `nativePartsNoRec?` on a block of `NonAuxKey` members. -/
theorem nonAuxKey_ctors_of_nativePartsNoRec {nPd : Nat} {block : List (ConstantInfo .anon)}
    {p₀ : NativeParts .anon}
    (hblk : ∀ ci ∈ block, NonAuxKey ci.name)
    (hparts : nativePartsNoRec? nPd block = some p₀) :
    ∀ c ∈ p₀.ctors, NonAuxKey c.1.name := by
  obtain ⟨caps, cs, hblk_eq, hctors_eq⟩ := nativePartsNoRec?_block_eq hparts
  intro c hc
  rw [hctors_eq] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  refine hblk (.ctorInfo c'.1 c'.2.1 c'.2.2) ?_
  rw [hblk_eq]
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', rfl⟩)

private theorem nativeTable_newProj_ctor_nonAux {J : Judgements .anon}
    {envO env₁ X env₂ : Ix.Kernel.Env .anon} {p : NativeParts .anon}
    {cvTa : ConstantVal .anon} {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hCtors : SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss)
    (hCna : ∀ c ∈ p.ctors, NonAuxKey c.1.name)
    (hX : NewSat envO X NotProj)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    ∀ n tbl, env₂.find? n = some (.projInfo tbl) → envO.find? n = none →
      NonAuxKey tbl.ctor := by
  intro n tbl hf hn
  have hold : ∀ {t : ProjTable .anon}, X.find? n = some (.projInfo t) → False := by
    intro t hx
    rcases hX _ _ hx with h1 | h1
    · rw [h1] at hn; exact nomatch hn
    · exact h1 t rfl
  rcases Ix.Kernel.Model.nativeTable_cases hTbl with rfl | ⟨cA, sorts, bodies, rfl, rfl, -, -, rfl⟩
  · exact (hold hf).elim
  · rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · obtain rfl := ConstantInfo.projInfo.inj (Option.some.inj hf)
      obtain ⟨hlA, -, hall⟩ := id hCtors
      cases hpc : p.ctors with
      | nil => rw [hpc] at hlA; simp at hlA
      | cons c rest =>
        obtain ⟨_, _, _, hCtor⟩ := hall 0 c cA (by rw [hpc]; rfl) rfl
        have hc_mem : c ∈ p.ctors := by rw [hpc]; exact List.mem_cons_self
        have hname_eq : cA.1.name = c.1.name := by
          obtain ⟨cvCa₀, hchk₀, hcases⟩ := hCtor.1
          rcases hcases with rfl | ⟨ty', hchk'⟩
          · exact hchk₀.name_eq
          · exact hchk'.name_eq
        show NonAuxKey cA.1.name
        rw [hname_eq]
        exact hCna c hc_mem
    · exact (hold hf).elim

/-- `StrongEnvProps` preservation across any `DeclRunJ rulesJ (IndRoutesJ rulesJ env)` step when
any unpinned `.indDecl` block has `NonAuxKey` member names (in particular under `DeclNonAux d`). -/
theorem strongEnvProps_declRunJ {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hS : Ix.Kernel.Open.StoreInv env) (h : StrongEnvProps env)
    (hna : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∀ ci ∈ block, NonAuxKey ci.name)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    StrongEnvProps env₂ := by
  have hext := Ix.Kernel.Model.declRunJ_envExt_routes hrun
  have htb := Ix.Kernel.Model.tableBodies_declRunJ hS h.1 hrun
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact strongEnvProps_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact strongEnvProps_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact strongEnvProps_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact h
    · exact strongEnvProps_step_noProj hext.find h (NewSat.cons (fun _ heq => nomatch heq))
    · exact h
  | basisDecl kind =>
    exact strongEnvProps_step_noProj hext.find h (Ix.Kernel.Model.basis_newSat_noProj hrun)
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact strongEnvProps_step_noProj hext.find h (Ix.Kernel.Model.basis_newSat_noProj hrun)
    · subst hrun; exact h
  | indDecl block nP =>
    cases hpin : Ix.Kernel.basisPinHit block with
    | some kind =>
      have hrun' : DeclBasisRun env kind env₂ := by simpa [DeclRunJ, hpin] using hrun
      exact strongEnvProps_step_noProj hext.find h (Ix.Kernel.Model.basis_newSat_noProj hrun')
    | none =>
      have hblk_na := hna block nP rfl hpin
      have hroutes : IndRoutesJ rulesJ env block nP env₂ := by simpa [DeclRunJ, hpin] using hrun
      rcases hroutes with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩ | hT
      · refine strongEnvProps_step hext.find h htb fun n tbl hf hn => Or.inl ?_
        obtain ⟨_, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, _, _, _, hInd,
          hp, hCtors, _, _, _, _, _, _, _, hTbl, _⟩ := hN
        obtain ⟨_, _, _, _, _, _, _, _, hp₁, henv₁⟩ := hInd
        have h1 : NewSat env env₁ NotProj := by
          rw [henv₁]; exact NewSat.cons (fun _ heq => nomatch heq)
        have hXno : NewSat env ⟨.recInfo cvRa p.majorIdx p.rulePrefix
            (Ix.Kernel.sumRules (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP
              p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
            :: (Ix.Kernel.consSumCtors p.nP ctorsA env₁).consts⟩ NotProj :=
          h1.trans
            ((Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq)).trans
              (NewSat.cons (fun _ heq => nomatch heq)))
        have hp_ctors : p.ctors = p₀.ctors := by
          rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
        exact nativeTable_newProj_ctor_nonAux hCtors
          (by rw [hp_ctors]; exact nonAuxKey_ctors_of_nativeParts hblk_na hdp) hXno hTbl n tbl hf hn
      · exact strongEnvProps_step_noProj hext.find h
          (Ix.Kernel.Model.modeled_newSat (fun _ _ heq => nomatch heq)
            (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hM)
      · refine strongEnvProps_step hext.find h htb fun n tbl hf hn => Or.inl ?_
        obtain ⟨_, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd, hp, hCtors,
          _, _, _, _, _, hTbl, _⟩ := hN
        obtain ⟨_, _, _, _, _, _, _, _, hp₁, henv₁⟩ := hInd
        have h1 : NewSat env env₁ NotProj := by
          rw [henv₁]; exact NewSat.cons (fun _ heq => nomatch heq)
        have hXno : NewSat env (Ix.Kernel.consSumCtors p.nP ctorsA env₁) NotProj :=
          h1.trans (Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq))
        have hp_ctors : p.ctors = p₀.ctors := by
          rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
        exact nativeTable_newProj_ctor_nonAux hCtors
          (by rw [hp_ctors]; exact nonAuxKey_ctors_of_nativePartsNoRec hblk_na hdp)
          hXno hTbl n tbl hf hn
      · exact strongEnvProps_step_noProj hext.find h
          (Ix.Kernel.Model.twin_newSat (fun _ _ _ _ heq => nomatch heq)
            (fun _ _ _ _ _ heq => nomatch heq) hT)

/-! ## Section 2: `EtaShape` (`etaSort` unconditional + `etaType` on closed parameter spines) -/

/-- Structural shape invariant of every stored η-capable inductive family and its η constructor:
the stored former peels `caps.etaParams` binders to a sort matching `caps.sortZ`, and its stored
η-constructor has duplicate-free `levelParams` matching `cvT.levelParams`, counts
`(caps.etaParams, caps.etaFields)`, and residual
`mkAppN (.const T (lps.map .param)) (structPsAt nF nP)`. -/
def EtaShape (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ T cvT caps, env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    (∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
      caps.sortZ = Ix.Kernel.Level.zeronessOf l) ∧
    ∀ kc cvc nP nF, caps.etaCtor = some kc →
      env.find? kc = some (.ctorInfo cvc nP nF) →
      cvc.levelParams.Nodup ∧
      cvc.levelParams = cvT.levelParams ∧
      nP = caps.etaParams ∧
      nF = caps.etaFields ∧
      ∃ cbs, cvc.type.stripPis (nP + nF) = some (cbs,
        Ix.Kernel.Expr.mkAppN (.const T (cvc.levelParams.map .param))
          (Ix.Kernel.structPsAt nF nP))

theorem EtaShape.empty : EtaShape Ix.Kernel.Env.empty := by
  intro T cvT caps h
  simp [Ix.Kernel.Env.find?, Ix.Kernel.Env.empty] at h

/-- Constant predicate asserting no η-capable `.indInfo` is introduced. -/
def NoEtaInd (x : ConstantInfo .anon) : Prop :=
  ∀ cv caps, x = .indInfo cv caps → caps.eta = false

theorem etaShape_step {env env₂ : Ix.Kernel.Env .anon}
    (hext : EnvExt env env₂)
    (h : EtaShape env)
    (hnoNewCtorOnOld : ∀ T cvT caps kc cvc nP nF,
      env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
      env₂.find? kc = some (.ctorInfo cvc nP nF) → env.find? kc = some (.ctorInfo cvc nP nF))
    (hnew : ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → env.find? T = none →
      caps.eta = true →
      (∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
        caps.sortZ = Ix.Kernel.Level.zeronessOf l) ∧
      ∀ kc cvc nP nF, caps.etaCtor = some kc →
        env₂.find? kc = some (.ctorInfo cvc nP nF) →
        cvc.levelParams.Nodup ∧
        cvc.levelParams = cvT.levelParams ∧
        nP = caps.etaParams ∧
        nF = caps.etaFields ∧
        ∃ cbs, cvc.type.stripPis (nP + nF) = some (cbs,
          Ix.Kernel.Expr.mkAppN (.const T (cvc.levelParams.map .param))
            (Ix.Kernel.structPsAt nF nP))) :
    EtaShape env₂ := by
  intro T cvT caps hf he
  cases hold : env.find? T with
  | none => exact hnew T cvT caps hf hold he
  | some c =>
    have h2 := hext.find hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    obtain ⟨hsort, hctor⟩ := h T cvT caps hold he
    refine ⟨hsort, fun kc cvc nP nF hkc hfc₂ => ?_⟩
    exact hctor kc cvc nP nF hkc (hnoNewCtorOnOld T cvT caps kc cvc nP nF hold he hkc hfc₂)

/-- Every η-capable family in `env` already has its `etaCtor` stored in `env`, so `EnvExt.find`
locks `env₂.find? kc` across all future extensions. -/
def EtaCtorStored (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ T cvT caps kc, env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    caps.etaCtor = some kc → (env.find? kc).isSome = true

theorem EtaCtorStored.empty : EtaCtorStored Ix.Kernel.Env.empty := by
  intro T cvT caps kc h
  simp [Ix.Kernel.Env.find?, Ix.Kernel.Env.empty] at h

theorem etaCtorStored_step_noEta {env env₂ : Ix.Kernel.Env .anon}
    (hext : EnvExt env env₂) (h : EtaCtorStored env) (hno : NewSat env env₂ NoEtaInd) :
    EtaCtorStored env₂ := by
  intro T cvT caps kc hf he hkc
  cases hold : env.find? T with
  | none =>
    rcases hno T (.indInfo cvT caps) hf with h1 | h1
    · rw [h1] at hold; cases hold
    · rw [h1 cvT caps rfl] at he; cases he
  | some c =>
    have h2 := hext.find hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (h T cvT caps kc hold he hkc)
    rw [hext.find hci]
    rfl

theorem etaShape_step_noEta {env env₂ : Ix.Kernel.Env .anon}
    (hext : EnvExt env env₂) (hcs : EtaCtorStored env) (h : EtaShape env)
    (hno : NewSat env env₂ NoEtaInd) :
    EtaCtorStored env₂ ∧ EtaShape env₂ := by
  refine ⟨etaCtorStored_step_noEta hext hcs hno, etaShape_step hext h ?_ ?_⟩
  · intro T cvT caps kc cvc nP nF hold he hkc hfc₂
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
    have hci₂ := hext.find hci
    rw [hfc₂] at hci₂
    obtain rfl := Option.some.inj hci₂
    exact hci
  · intro T cvT caps hf hn he
    rcases hno T (.indInfo cvT caps) hf with h1 | h1
    · rw [h1] at hn; cases hn
    · rw [h1 cvT caps rfl] at he; cases he

private theorem levelParam_nodup_iff :
    ∀ (lps : List LevelParam), LevelParam.nodup lps = true ↔ lps.Nodup
  | [] => by simp [LevelParam.nodup]
  | p :: ps => by
    simp [LevelParam.nodup, Bool.and_eq_true, List.nodup_cons, levelParam_nodup_iff ps]

private theorem basis_etaShape_new {env env₂ : Ix.Kernel.Env .anon} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) :
    ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → env.find? T = none →
      caps.eta = true →
      (∀ kc, caps.etaCtor = some kc → (env₂.find? kc).isSome = true) ∧
      (∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
        caps.sortZ = Ix.Kernel.Level.zeronessOf l) ∧
      ∀ kc cvc nP nF, caps.etaCtor = some kc →
        env₂.find? kc = some (.ctorInfo cvc nP nF) →
        cvc.levelParams.Nodup ∧
        cvc.levelParams = cvT.levelParams ∧
        nP = caps.etaParams ∧
        nF = caps.etaFields ∧
        ∃ cbs, cvc.type.stripPis (nP + nF) = some (cbs,
          Ix.Kernel.Expr.mkAppN (.const T (cvc.levelParams.map .param))
            (Ix.Kernel.structPsAt nF nP)) := by
  intro T cvT caps hf hn he
  have hmem : .indInfo cvT caps ∈ (kind.declsA : List (ConstantInfo .anon)) := by
    rcases Ix.Kernel.Model.basis_newSat (Q := fun c => c ∈ kind.declsA) (fun _ hc => hc) hrun
        T (.indInfo cvT caps) hf with hold | hmem
    · rw [hold] at hn; cases hn
    · exact hmem
  have hT_eq : cvT.name = T := Ix.Kernel.Semantics.Env.find?_name hf
  cases kind with
  | eqK | natK | emptyK | falseK | quotK =>
    simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with heq | heq | heq | heq | heq <;>
      (first | cases heq; cases he | exact nomatch heq)
  | punitK =>
    simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with heq | heq | heq
    · injection heq with hcv hcaps
      subst hcv hcaps
      subst hT_eq
      have hunit_stored : env₂.find? Ix.Kernel.punitUnitName = some Ix.Kernel.punitUnitA := by
        obtain ⟨henv₂, _⟩ := Ix.Kernel.Model.basisInstallRun_eq hrun.2
        have hpre : Ix.Kernel.Env.find? ⟨(BasisKind.punitK.declsA (md := .anon)).reverse⟩
            Ix.Kernel.punitUnitName = some Ix.Kernel.punitUnitA := by decide
        rw [henv₂, Ix.Kernel.Model.find?_prefix, hpre]
        rfl
      refine ⟨fun kc hkc => ?_, ⟨[], .param Ix.Kernel.BasisDSL.uN, rfl, rfl⟩,
        fun kc cvc nP nF hkc hfc => ?_⟩
      · injection hkc with hkc_eq
        subst hkc_eq
        rw [hunit_stored]; rfl
      · injection hkc with hkc_eq
        subst hkc_eq
        rw [hunit_stored] at hfc
        injection hfc with hci
        injection hci with hcvc hnP hnF
        subst hcvc hnP hnF
        exact ⟨List.nodup_singleton _, rfl, rfl, rfl, [], rfl⟩
    · cases heq
    · cases heq

private theorem nativeCapsAt_eta_full {p : InductiveShape .anon} {isRec : Bool}
    (h : (Ix.Kernel.nativeCapsAt p isRec).eta = true) :
    ∃ c, p.ctors = [c] ∧ p.nIdx = 0 ∧
      (Ix.Kernel.nativeCapsAt p isRec).etaCtor = some c.1.name ∧
      (Ix.Kernel.nativeCapsAt p isRec).etaParams = p.nP ∧
      (Ix.Kernel.nativeCapsAt p isRec).etaFields = c.2 ∧
      (Ix.Kernel.nativeCapsAt p isRec).sortZ = Ix.Kernel.Level.zeronessOf p.resSort := by
  unfold Ix.Kernel.nativeCapsAt at h ⊢
  split at h
  · next c hc =>
    rw [hc]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨c, rfl, h.1.1, rfl, rfl, rfl, rfl⟩
  · exact nomatch h

private theorem native_etaShape_new {env env₁ X env₂ : Ix.Kernel.Env .anon}
    {p₀ p : NativeParts .anon} {isRec : Bool} {cvTa : ConstantVal .anon} {p₁ : InductiveShape .anon}
    {kinds : List (List Ix.Kernel.RecFieldKind)} {ctorsA : List (ConstantVal .anon × Nat)}
    {sortss : List (List KLevel)}
    (hS : Ix.Kernel.Open.StoreInv env)
    (hrc : Ix.Kernel.Model.NativeRecog p₀)
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    (hInd : SumIndRunJ rulesJ env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      env₁ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ rulesJ env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss)
    (hX : NewSat env₁ X (fun x => ∀ cv caps, x ≠ .indInfo cv caps))
    (hCkeep : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
      env₂.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2))
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → env.find? T = none →
      caps.eta = true →
      (∀ kc, caps.etaCtor = some kc → (env₂.find? kc).isSome = true) ∧
      (∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
        caps.sortZ = Ix.Kernel.Level.zeronessOf l) ∧
      ∀ kc cvc nP nF, caps.etaCtor = some kc →
        env₂.find? kc = some (.ctorInfo cvc nP nF) →
        cvc.levelParams.Nodup ∧
        cvc.levelParams = cvT.levelParams ∧
        nP = caps.etaParams ∧
        nF = caps.etaFields ∧
        ∃ cbs, cvc.type.stripPis (nP + nF) = some (cbs,
          Ix.Kernel.Expr.mkAppN (.const T (cvc.levelParams.map .param))
            (Ix.Kernel.structPsAt nF nP)) := by
  have hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames rulesJ e :=
    fun e => Ix.Kernel.Model.judgeFrames_rulesJ e
  have _hF := Ix.Kernel.Model.nativeFront hfr hS hrc hnd hInd hp hCtors
  obtain ⟨cvTa₀, s, bs, cvS, hchk₀, hTa_cases, hstripT, hFS, hp₁, henv₁⟩ := hInd
  intro T cvT caps hf hn he
  have hT₁ : env₁.find? T = some (.indInfo cvT caps) := by
    rcases (hX.trans (Ix.Kernel.Model.nativeTable_newSat
        (Q := fun x => ∀ cv caps, x ≠ .indInfo cv caps)
        (fun _ _ _ heq => nomatch heq) hTbl)) _ _ hf with h1 | h1
    · exact h1
    · exact absurd rfl (h1 cvT caps)
  rw [henv₁, Ix.Kernel.Env.find?_cons] at hT₁
  split at hT₁
  · next hname =>
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hT₁)
    obtain ⟨c, hc, hI, hCtorOpt, hParams, hFields, hSortZ⟩ := nativeCapsAt_eta_full he
    have hI₀ : p₀.nIdx = 0 := by subst hp₁; simpa [InductiveShape.withSort] using hI
    have hcvS_eq : cvS = cvTa := by
      rcases hFS with rfl | ⟨_, _, hne⟩
      · rfl
      · exact absurd hI₀ hne
    have hp_nP : p₀.nP = (Ix.Kernel.nativeCapsAt p₁ isRec).etaParams := by
      rw [hParams]; subst hp₁; rfl
    have hp_sort : s = p₁.resSort := by subst hp₁; rfl
    have hsort_part :
        ∃ bs' l, cvS.type.stripPis (Ix.Kernel.nativeCapsAt p₁ isRec).etaParams =
          some (bs', Expr.sort l) ∧
          (Ix.Kernel.nativeCapsAt p₁ isRec).sortZ = Ix.Kernel.Level.zeronessOf l := by
      refine ⟨bs, s, ?_, ?_⟩
      · rw [hcvS_eq, ← hp_nP]
        simpa [hI₀] using hstripT
      · rw [hSortZ, hp_sort]
    have hc₀ : p₀.ctors = [c] := by subst hp₁; simpa [InductiveShape.withSort] using hc
    have hpc : p.ctors = [c] := by
      rw [hp, hp₁]; simpa [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort] using hc₀
    obtain ⟨hlA, -, hall⟩ := id hCtors
    rw [hpc] at hlA
    obtain ⟨cA, rfl⟩ : ∃ cA, ctorsA = [cA] := by
      match ctorsA, hlA with
      | [cA], _ => exact ⟨cA, rfl⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    obtain ⟨hnF, sorts, _, hCtorRun⟩ := hall 0 c cA (by rw [hpc]; rfl) rfl
    have hcA_name : cA.1.name = c.1.name := by
      obtain ⟨cvCa₀, hcc₀, hcc⟩ := hCtorRun.1
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.name_eq
      · exact hcc'.name_eq
    have hcA_c_lps : cA.1.levelParams = c.1.levelParams := by
      obtain ⟨cvCa₀, hcc₀, hcc⟩ := hCtorRun.1
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.levelParams_eq
      · exact hcc'.levelParams_eq
    have hcA_nd : cA.1.levelParams.Nodup := by
      obtain ⟨cvCa₀, ⟨_, hrunC, _⟩, _⟩ := hCtorRun.1
      rw [hcA_c_lps]
      exact (levelParam_nodup_iff c.1.levelParams).mp hrunC.2.2.2.1
    have hcA_find : env₂.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) := hCkeep 0 cA rfl
    have hT_eq : T = p.cvT.name := by
      have hTa_name : cvTa.name = p₀.cvT.name := by
        rcases hTa_cases with rfl | ⟨_, hTa'⟩
        · exact hchk₀.name_eq
        · exact hTa'.name_eq
      have hp_name : p.cvT.name = p₀.cvT.name := by
        rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
      have hcvS_name : cvS.name = T := hname
      rw [← hcvS_name, hcvS_eq, hTa_name, hp_name]
    have h1_lps : cvTa.levelParams = p₀.cvT.levelParams := by
      rcases hTa_cases with rfl | ⟨_, hTa'⟩
      · exact hchk₀.levelParams_eq
      · exact hTa'.levelParams_eq
    have hTa_lps : cvTa.levelParams = p.cvT.levelParams := by
      have h2 : p.cvT.levelParams = p₀.cvT.levelParams := by
        rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
      rw [h1_lps, h2]
    have hcA_lps : cA.1.levelParams = cvS.levelParams := by
      have hc_lps : c.1.levelParams = p₀.cvT.levelParams :=
        (hrc.1 c (by rw [hc₀]; exact List.mem_cons_self)).1
      rw [hcA_c_lps, hc_lps, hcvS_eq, h1_lps]
    refine ⟨fun kc hkc => ?_, hsort_part, fun kc cvc nP nF hkc hfc => ?_⟩
    · rw [hCtorOpt] at hkc
      injection hkc with hkc_eq
      rw [← hkc_eq, ← hcA_name, hcA_find]
      rfl
    · rw [hCtorOpt] at hkc
      injection hkc with hkc_eq
      rw [← hkc_eq, ← hcA_name, hcA_find] at hfc
      obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfc)
      obtain ⟨cbs, es, hstripC, hes_len⟩ := hCtorRun.2.1
      have hp_I : p.nIdx = 0 := by
        rw [hp, hp₁]; simpa [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort] using hI₀
      have hes_nil : es = [] := List.eq_nil_of_length_eq_zero (hes_len.trans hp_I)
      rw [hes_nil, List.append_nil] at hstripC
      have hp_nP' : p.nP = (Ix.Kernel.nativeCapsAt p₁ isRec).etaParams := by
        rw [← hp_nP, hp, hp₁]
        simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
      refine ⟨hcA_nd, hcA_lps, hp_nP', hnF.trans hFields.symm, cbs, ?_⟩
      rw [hnF, hT_eq, hcA_lps, hcvS_eq, hTa_lps]
      exact hstripC
  · rw [hT₁] at hn; cases hn

/-- Every `DeclRunJ rulesJ (IndRoutesJ rulesJ env)` step preserves `EtaCtorStored` and `EtaShape`. -/
theorem etaShape_declRunJ {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hS : Ix.Kernel.Open.StoreInv env)
    (hcs : EtaCtorStored env) (h : EtaShape env)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    EtaCtorStored env₂ ∧ EtaShape env₂ := by
  have hext := Ix.Kernel.Model.declRunJ_envExt_routes hrun
  have hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames rulesJ e :=
    fun e => Ix.Kernel.Model.judgeFrames_rulesJ e
  have hbasis_step : ∀ {kind : BasisKind}, DeclBasisRun env kind env₂ →
      EtaCtorStored env₂ ∧ EtaShape env₂ := by
    intro kind hb
    refine ⟨?_, etaShape_step hext h ?_ (fun T cvT caps hf hn he =>
      (basis_etaShape_new hb T cvT caps hf hn he).2)⟩
    · intro T cvT caps kc hf he hkc
      cases hold : env.find? T with
      | none => exact (basis_etaShape_new hb T cvT caps hf hold he).1 kc hkc
      | some c =>
        have h2 := hext.find hold
        rw [hf] at h2
        obtain rfl := Option.some.inj h2
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
        rw [hext.find hci]; rfl
    · intro T cvT caps kc cvc nP nF hold he hkc hfc₂
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
      have hci₂ := hext.find hci
      rw [hfc₂] at hci₂
      obtain rfl := Option.some.inj hci₂
      exact hci
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact etaShape_step_noEta hext hcs h (NewSat.cons (fun _ _ heq => nomatch heq))
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact etaShape_step_noEta hext hcs h (NewSat.cons (fun _ _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact etaShape_step_noEta hext hcs h (NewSat.cons (fun _ _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact ⟨hcs, h⟩
    · exact etaShape_step_noEta hext hcs h (NewSat.cons (fun _ _ heq => nomatch heq))
    · exact ⟨hcs, h⟩
  | basisDecl kind => exact hbasis_step hrun
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact hbasis_step hrun
    · subst hrun; exact ⟨hcs, h⟩
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact hbasis_step hrun
    · rcases hrun with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩ | hT
      · obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, _, _, _, hInd,
          hp, hCtors, _, _, _, _, _, _, hRec, hTbl, _⟩ := hN
        have hF := Ix.Kernel.Model.nativeFront hfr hS (Ix.Kernel.Model.nativeRecog_of hdp)
          hnd hInd hp hCtors
        obtain ⟨hnR, _, hfR, _⟩ := hRec.recursor
        have hfreshR : (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name = none := by
          rw [hnR]; exact hfR
        have hX : NewSat env₁
            ⟨.recInfo cvRa p.majorIdx p.rulePrefix
              (Ix.Kernel.sumRules (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP
                p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
              :: (Ix.Kernel.consSumCtors p.nP ctorsA env₁).consts⟩
            (fun x => ∀ cv caps, x ≠ .indInfo cv caps) :=
          (Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ _ heq => nomatch heq)).trans
            (NewSat.cons (fun _ _ heq => nomatch heq))
        have hCkeep : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
            env₂.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) :=
          fun j cA hj => Ix.Kernel.Model.nativeTable_keep hTbl
            (Ix.Kernel.Env.find?_cons_of_fresh hfreshR (hF.ctor j cA hj).1)
        have hnew := native_etaShape_new hS (Ix.Kernel.Model.nativeRecog_of hdp)
          hnd hInd hp hCtors hX hCkeep hTbl
        refine ⟨?_, etaShape_step hext h ?_ (fun T cvT caps hf hn he =>
          (hnew T cvT caps hf hn he).2)⟩
        · intro T cvT caps kc hf he hkc
          cases hold : env.find? T with
          | none => exact (hnew T cvT caps hf hold he).1 kc hkc
          | some c =>
            have h2 := hext.find hold
            rw [hf] at h2
            obtain rfl := Option.some.inj h2
            obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
            rw [hext.find hci]; rfl
        · intro T cvT caps kc cvc nP' nF' hold he hkc hfc₂
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
          have hci₂ := hext.find hci
          rw [hfc₂] at hci₂
          obtain rfl := Option.some.inj hci₂
          exact hci
      · exact etaShape_step_noEta hext hcs h
          (Ix.Kernel.Model.modeled_newSat
            (fun _ _ _ heq => by obtain ⟨_, rfl⟩ := ConstantInfo.indInfo.inj heq; rfl)
            (fun _ _ _ _ _ heq => nomatch heq)
            (fun _ _ _ _ _ _ heq => nomatch heq) hM)
      · obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd, hp, hCtors,
          _, _, _, _, _, hTbl, _⟩ := hN
        have hF := Ix.Kernel.Model.nativeFront hfr hS (Ix.Kernel.Model.nativeRecog_noRec hdp)
          hnd hInd hp hCtors
        have hX : NewSat env₁ (Ix.Kernel.consSumCtors p.nP ctorsA env₁)
            (fun x => ∀ cv caps, x ≠ .indInfo cv caps) :=
          Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ _ heq => nomatch heq)
        have hCkeep : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
            env₂.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) :=
          fun j cA hj => Ix.Kernel.Model.nativeTable_keep hTbl (hF.ctor j cA hj).1
        have hnew := native_etaShape_new hS (Ix.Kernel.Model.nativeRecog_noRec hdp)
          hnd hInd hp hCtors hX hCkeep hTbl
        refine ⟨?_, etaShape_step hext h ?_ (fun T cvT caps hf hn he =>
          (hnew T cvT caps hf hn he).2)⟩
        · intro T cvT caps kc hf he hkc
          cases hold : env.find? T with
          | none => exact (hnew T cvT caps hf hold he).1 kc hkc
          | some c =>
            have h2 := hext.find hold
            rw [hf] at h2
            obtain rfl := Option.some.inj h2
            obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
            rw [hext.find hci]; rfl
        · intro T cvT caps kc cvc nP' nF' hold he hkc hfc₂
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
          have hci₂ := hext.find hci
          rw [hfc₂] at hci₂
          obtain rfl := Option.some.inj hci₂
          exact hci
      · exact etaShape_step_noEta hext hcs h
          (Ix.Kernel.Model.twin_newSat (fun _ _ _ _ _ heq => nomatch heq)
            (fun _ _ _ _ _ _ heq => nomatch heq) hT)

/-! ### `.io`-grade `Infer` spine inversion for `etaType` on closed parameter arguments -/

private theorem infer_io_app_inv {env : Ix.Kernel.Env .anon} {d : Nat} {f a t : KExpr}
    (h : Infer env .io d (.app f a) t) :
    ∃ tf ty body mt, Infer env .io d f tf ∧ Red env d tf (.forallE ty body mt) ∧
      t = body.instantiate1 a := by
  cases h with
  | app hfn hred _ _ => exact ⟨_, _, _, _, hfn, hred, rfl⟩
  | appSkip hfn hred _ => exact ⟨_, _, _, _, hfn, hred, rfl⟩

private theorem instantiateLevelParams_mkAppN (lps : List LevelParam) (us : List KLevel)
    (f : KExpr) (args : List KExpr) :
    (Expr.mkAppN f args).instantiateLevelParams lps us =
      Expr.mkAppN (f.instantiateLevelParams lps us)
        (args.map (·.instantiateLevelParams lps us)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih =>
    simp only [Expr.mkAppN, List.map_cons, ih (.app f a), Expr.instantiateLevelParams]

private theorem instantiate1_mkAppN (v : KExpr) (k : Nat) (f : KExpr) (args : List KExpr) :
    (Expr.mkAppN f args).instantiate1 v k =
      Expr.mkAppN (f.instantiate1 v k) (args.map (·.instantiate1 v k)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih =>
    simp only [Expr.mkAppN, List.map_cons, ih (.app f a), Expr.instantiate1]

private theorem subst_go_getElem {lps : List LevelParam} {us : List KLevel}
    (hnd : lps.Nodup) (hlen : us.length = lps.length) :
    ∀ {i : Nat} (hi : i < lps.length),
      Level.subst.go lps us lps[i] = us[i]'(by omega) := by
  induction lps generalizing us with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons p ps ih =>
    intro i hi
    cases us with
    | nil => simp at hlen
    | cons u us' =>
      obtain ⟨hp_notin, hnd'⟩ := List.nodup_cons.mp hnd
      cases i with
      | zero =>
        show (if p = p then u else Level.subst.go ps us' p) = u
        simp
      | succ j =>
        have hj : j < ps.length := Nat.lt_of_succ_lt_succ hi
        have hj_us : j < us'.length := by simp at hlen; omega
        have hne : p ≠ ps[j] := fun heq => hp_notin (by rw [heq]; exact List.getElem_mem hj)
        show (if p = ps[j] then u else Level.subst.go ps us' ps[j]) = us'[j]'hj_us
        simp only [hne, ↓reduceIte]
        exact ih hnd' (Nat.succ.inj hlen) hj

private theorem map_subst_self_params {lps : List LevelParam} {us : List KLevel}
    (hnd : lps.Nodup) (hlen : us.length = lps.length) :
    (lps.map Level.param).map (Level.subst lps us) = us := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.length_map] at h1
    simp only [List.getElem_map, Level.subst]
    exact subst_go_getElem hnd hlen h1

private theorem stripPis_instantiateLevelParams (lps : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {res : KExpr},
      e.stripPis n = some (bs, res) →
      ∃ bs', (e.instantiateLevelParams lps us).stripPis n =
        some (bs', res.instantiateLevelParams lps us)
  | 0, e, bs, res, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl⟩
  | n + 1, .forallE dom bo mb, bs, res, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, res₀⟩, hst₀, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨bs', hst'⟩ := stripPis_instantiateLevelParams lps us n hst₀
    exact ⟨(dom.instantiateLevelParams lps us, { mb with pw := Level.substPW lps us mb.pw }) :: bs',
      by simp [Expr.instantiateLevelParams, Expr.stripPis, hst']⟩
  | n + 1, .bvar _, _, _, h | n + 1, .fvar _ _, _, _, h | n + 1, .sort _, _, _, h
  | n + 1, .const _ _, _, _, h | n + 1, .app _ _, _, _, h | n + 1, .lam _ _ _, _, _, h
  | n + 1, .letE _ _ _ _, _, _, h | n + 1, .lit _, _, _, h | n + 1, .proj _ _ _, _, _, h => by
    simp [Expr.stripPis] at h

private theorem instantiate1_of_looseBVarsBounded_zero (v : KExpr) :
    ∀ {e : KExpr} (k : Nat), e.looseBVarsBounded k = true → e.instantiate1 v k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    have h1 : i ≠ k := by omega
    have h2 : ¬ (i > k) := by omega
    show (if i = k then v else if i > k then Expr.bvar (i - 1) else Expr.bvar i) = Expr.bvar i
    simp only [h1, h2, ↓reduceIte]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, ihf k hb.1, iha k hb.2]
  | lam ty bo mb iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, iht k hb.1, ihb (k + 1) hb.2]
  | forallE ty bo mb iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, iht k hb.1, ihb (k + 1) hb.2]
  | letE ty val bo mb iht ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, iht k hb.1.1, ihv k hb.1.2, ihb (k + 1) hb.2]
  | proj s i e ih =>
    intro k hb
    simp only [Expr.looseBVarsBounded] at hb
    simp [Expr.instantiate1, ih k hb]

private theorem looseBVarsBounded_mono_glue :
    ∀ {e : KExpr} {k₁ k₂ : Nat}, k₁ ≤ k₂ →
      e.looseBVarsBounded k₁ = true → e.looseBVarsBounded k₂ = true := by
  intro e
  induction e with
  | bvar i =>
    intro k₁ k₂ hle hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _; rfl
  | app f a ihf iha =>
    intro k₁ k₂ hle hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf hle hb.1, iha hle hb.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro k₁ k₂ hle hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨iht hle hb.1, ihb (by omega) hb.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro k₁ k₂ hle hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨⟨iht hle hb.1.1, ihv hle hb.1.2⟩, ihb (by omega) hb.2⟩
  | proj _ _ _ ih =>
    intro k₁ k₂ hle hb
    simp only [Expr.looseBVarsBounded] at hb ⊢
    exact ih hle hb

private def spineInst : List KExpr → Nat → KExpr → KExpr
  | [], _, e => e
  | a :: rest, depth, e => spineInst rest (depth - 1) (e.instantiate1 a (depth - 1))

private theorem infer_io_spine_inst {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (Ss : List KExpr) {f ty : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {res ta : KExpr},
      (∀ t', Infer env .io d f t' → t' = ty) →
      ty.stripPis Ss.length = some (bs, res) →
      Infer env .io d (Expr.mkAppN f Ss) ta →
      ta = spineInst Ss Ss.length res
  | [], f, ty, bs, res, ta, huniq, hst, hinf => by
    obtain rfl := huniq ta hinf
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    exact hst.2
  | a :: Ss, f, ty, bs, res, ta, huniq, hst, hinf => by
    obtain ⟨dom, body, mb, rfl⟩ : ∃ dom body mb, ty = .forallE dom body mb := by
      cases ty <;> first | exact ⟨_, _, _, rfl⟩ | simp [Expr.stripPis] at hst
    simp only [List.length_cons, Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs₀, res₀⟩, hst₀, heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hsome := Expr.stripPis_instantiate1_isSome (v := a) Ss.length (e := body) 0
      (by rw [hst₀]; rfl)
    obtain ⟨⟨bs₁, res₁⟩, hst₁⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hres₁, -⟩ := Expr.stripPis_instantiate1_eq (v := a) Ss.length 0 hst₀ hst₁
    have huniq' : ∀ t', Infer env .io d (.app f a) t' → t' = body.instantiate1 a := by
      intro t' h'
      obtain ⟨tf, ty', body', mt', htf, hred, rfl⟩ := infer_io_app_inv h'
      obtain rfl := huniq tf htf
      injection Ix.Kernel.Rules.Red.rigid hred rfl with _ hbody _
      rw [← hbody]
    have hta := infer_io_spine_inst Ss (f := .app f a) (ty := body.instantiate1 a)
      huniq' hst₁ hinf
    simpa [spineInst, hres₁] using hta

private theorem spineInst_mkAppN_const (T : KKey) (us : List KLevel) :
    ∀ (Ss : List KExpr) (depth : Nat) (args : List KExpr),
      spineInst Ss depth (Expr.mkAppN (.const T us) args) =
        Expr.mkAppN (.const T us) (args.map (spineInst Ss depth))
  | [], _, _ => by simp [spineInst]
  | a :: rest, depth, args => by
    simp only [spineInst, instantiate1_mkAppN, Expr.instantiate1,
      spineInst_mkAppN_const T us rest (depth - 1), List.map_map]
    rfl

private theorem spineInst_closed_arg :
    ∀ (Ss : List KExpr) (depth : Nat) {v : KExpr},
      v.looseBVarsBounded 0 = true → spineInst Ss depth v = v
  | [], _, _, _ => rfl
  | a :: rest, depth, v, hv => by
    simp only [spineInst]
    rw [instantiate1_of_looseBVarsBounded_zero a (depth - 1)
      (looseBVarsBounded_mono_glue (Nat.zero_le _) hv)]
    exact spineInst_closed_arg rest (depth - 1) hv

private theorem spineInst_bvar_param :
    ∀ (P F : List KExpr) (i : Nat) (hi : i < P.length),
      (∀ s ∈ P, s.looseBVarsBounded 0 = true) →
      spineInst (P ++ F) (P.length + F.length) (.bvar (F.length + P.length - 1 - i)) = P[i]
  | [], _, i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | p :: ps, F, 0, _, hclosed => by
    simp only [List.cons_append, List.length_cons, spineInst]
    have hidx : F.length + (ps.length + 1) - 1 - 0 = ps.length + 1 + F.length - 1 := by omega
    rw [hidx]
    have hb : (Expr.bvar (ps.length + 1 + F.length - 1) : KExpr).instantiate1 p
        (ps.length + 1 + F.length - 1) = p := by
      simp [Expr.instantiate1]
    rw [hb]
    exact spineInst_closed_arg (ps ++ F) (ps.length + 1 + F.length - 1)
      (hclosed p List.mem_cons_self)
  | p :: ps, F, i + 1, hi, hclosed => by
    simp only [List.cons_append, List.length_cons, spineInst]
    have hi' : i < ps.length := Nat.lt_of_succ_lt_succ hi
    have hb : (Expr.bvar (F.length + (ps.length + 1) - 1 - (i + 1)) : KExpr).instantiate1 p
        (ps.length + 1 + F.length - 1) =
        .bvar (F.length + ps.length - 1 - i) := by
      have h1 : F.length + (ps.length + 1) - 1 - (i + 1) ≠ ps.length + 1 + F.length - 1 := by omega
      have h2 : ¬ (F.length + (ps.length + 1) - 1 - (i + 1) > ps.length + 1 + F.length - 1) := by omega
      show (if _ then _ else if _ then _ else _) = _
      simp only [h1, h2, ↓reduceIte]
      congr 1; omega
    rw [hb]
    have hsub : ps.length + 1 + F.length - 1 = ps.length + F.length := by omega
    rw [hsub]
    exact spineInst_bvar_param ps F i hi' (fun s hs => hclosed s (List.mem_cons_of_mem _ hs))

private theorem infer_io_mkAppN_head {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (args : List KExpr) {f t : KExpr},
      Infer env .io d (Expr.mkAppN f args) t → ∃ tf, Infer env .io d f tf
  | [], _, _, h => ⟨_, h⟩
  | _ :: as, _, _, h => by
    obtain ⟨_, hfn⟩ := infer_io_mkAppN_head as h
    obtain ⟨tf₀, _, _, _, h0, _, _⟩ := infer_io_app_inv hfn
    exact ⟨tf₀, h0⟩

/-- **`etaType` on closed parameter arguments** from `EtaShape`: for any stored η-capable family `T`
and its η-constructor `kc`, any `.io`-grade `Infer` on a full application `mkAppN (.const kc us) Ss`
(`Ss.length = nP + nF`) whose first `nP` arguments have no loose bound variables yields
`ta = mkAppN (.const T us) (Ss.take nP)` (hence `Red.refl`). -/
theorem etaType_of_closed {env : Ix.Kernel.Env .anon}
    (heta : EtaShape env)
    {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon} {nP nF : Nat}
    (hT : env.find? T = some (.indInfo cvT caps))
    (hcap : caps.eta = true) (hctorOpt : caps.etaCtor = some kc)
    (hkc : env.find? kc = some (.ctorInfo cvc nP nF))
    {d : Nat} {us : List KLevel} {Ss : List KExpr} {ta : KExpr}
    (hlen : Ss.length = nP + nF)
    (hclosed : ∀ s ∈ Ss.take nP, s.looseBVarsBounded 0 = true)
    (hinf : Infer env .io d (Expr.mkAppN (.const kc us) Ss) ta) :
    Red env d ta (Expr.mkAppN (.const T us) (Ss.take nP)) := by
  obtain ⟨_, hctorShape⟩ := heta T cvT caps hT hcap
  obtain ⟨hnd, _, _, _, cbs, hstrip⟩ := hctorShape kc cvc nP nF hctorOpt hkc
  have huniq : ∀ t', Infer env .io d (.const kc us) t' →
      t' = cvc.type.instantiateLevelParams cvc.levelParams us := by
    intro t' h'
    obtain ⟨ci, hf', _, _, rfl⟩ := Ix.Kernel.Rules.Infer.const_inv h'
    rw [hkc] at hf'
    obtain rfl := Option.some.inj hf'
    rfl
  have hus_len : us.length = cvc.levelParams.length := by
    obtain ⟨tf, hconst⟩ := infer_io_mkAppN_head Ss hinf
    obtain ⟨ci, hf', _, hus, _⟩ := Ix.Kernel.Rules.Infer.const_inv hconst
    rw [hkc] at hf'
    obtain rfl := Option.some.inj hf'
    exact hus
  obtain ⟨bs', hst_inst⟩ := stripPis_instantiateLevelParams cvc.levelParams us (nP + nF) hstrip
  have hps_inst :
      (Ix.Kernel.structPsAt (md := .anon) nF nP).map (·.instantiateLevelParams cvc.levelParams us) =
        Ix.Kernel.structPsAt (md := .anon) nF nP := by
    unfold Ix.Kernel.structPsAt
    simp [List.map_map, Expr.instantiateLevelParams]
  rw [instantiateLevelParams_mkAppN, Expr.instantiateLevelParams,
    map_subst_self_params hnd hus_len, hps_inst, ← hlen] at hst_inst
  have hta := infer_io_spine_inst Ss huniq hst_inst hinf
  have hsplit : Ss = Ss.take nP ++ Ss.drop nP := (List.take_append_drop nP Ss).symm
  have hlenP : (Ss.take nP).length = nP := by simp [hlen]
  have hlenF : (Ss.drop nP).length = nF := by simp [hlen]
  rw [hlen, spineInst_mkAppN_const] at hta
  have hargs_eq :
      (Ix.Kernel.structPsAt nF nP).map (spineInst Ss (nP + nF)) = Ss.take nP := by
    apply List.ext_getElem
    · simp [Ix.Kernel.structPsAt, hlenP]
    · intro i h1 h2
      simp only [Ix.Kernel.structPsAt, List.length_map, List.length_range] at h1
      simp only [Ix.Kernel.structPsAt, List.getElem_map, List.getElem_range]
      have hcall := spineInst_bvar_param (Ss.take nP) (Ss.drop nP) i
        (by rw [hlenP]; exact h1) hclosed
      rw [← hsplit] at hcall
      have hlhs :
          spineInst Ss ((Ss.take nP).length + (Ss.drop nP).length)
            (.bvar ((Ss.drop nP).length + (Ss.take nP).length - 1 - i)) =
          spineInst Ss (nP + nF) (.bvar (nF + nP - 1 - i)) := by
        rw [hlenP, hlenF]
      exact hlhs.symm.trans hcall
  rw [hta, hargs_eq]
  exact .refl

/-! ## Section 3: Unified store and fold invariants (`FoldStoreInv`, `FoldInv`) -/

/-- Unified store-level declaration invariant bundle carried alongside `EnvModelT` across all
declaration routes: combines `StoreInv`, `ThmTyped`, `RecK`, `EtaTowers`, `StrongEnvProps`
(extending `TableBodies` with non-auxiliary projection-table constructor keys), `RecShape`,
`EtaCtorStored`, and `EtaShape`. -/
structure FoldStoreInv (env : Ix.Kernel.Env .anon) : Prop where
  store : Ix.Kernel.Open.StoreInv env
  thmTyped : ThmTyped env
  recK : RecK env
  etaTowers : EtaTowers env
  strongProps : StrongEnvProps env
  recShape : RecShape env
  etaCtorStored : EtaCtorStored env
  etaShape : EtaShape env

/-- `TableBodies` projection of `FoldStoreInv`. -/
theorem FoldStoreInv.tableBodies {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    TableBodies env :=
  h.strongProps.1

/-- `FoldStoreInv` holds of the empty environment. -/
theorem foldStoreInv_empty : FoldStoreInv Ix.Kernel.Env.empty :=
  ⟨.empty, .empty, .empty, .empty, strongEnvProps_empty, .empty, .empty, .empty⟩

/-- One-step preservation of `FoldStoreInv` along any `DeclRunJ rulesJ (IndRoutesJ rulesJ env)`
step when any unpinned `.indDecl` block has `NonAuxKey` member names. -/
theorem foldStoreInv_step_declRunJ {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (h : FoldStoreInv env)
    (hna : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    FoldStoreInv env₂ := by
  have heta := etaShape_declRunJ h.store h.etaCtorStored h.etaShape hd
  refine
    { store :=
        Ix.Kernel.Model.storeInv_declRunJ
          (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e)
          (fun hI => Ix.Kernel.Model.storeInv_indRoutesJ
            (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e) h.store hI)
          h.store hd
      thmTyped := Ix.Kernel.Model.thmTyped_declRunJ h.thmTyped hd
      recK := Ix.Kernel.Model.recK_declRunJ h.store h.recK hd
      etaTowers := Ix.Kernel.Model.etaTowers_declRunJ h.etaTowers hd
      strongProps := strongEnvProps_declRunJ h.store h.strongProps hna hd
      recShape := Ix.Kernel.Model.recShape_declRunJ h.store h.recShape hd
      etaCtorStored := heta.1
      etaShape := heta.2 }

/-! ### Declaration-owned `Core.EnvFacts` projections from `FoldStoreInv` -/

theorem FoldStoreInv.storeClosed {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    Ix.Kernel.StoreClosed env :=
  h.store.storeClosed

theorem FoldStoreInv.recArity {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    ∀ k cv mI rP rls, env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
      (cv.type.stripPis (mI + 1)).isSome = true :=
  fun _ _ _ _ _ hf _ hrl => h.store.recArity hf hrl

theorem FoldStoreInv.ruleCtorArity {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    ∀ k cv mI rP rls, env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
      ∀ cvj nP nF, env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
        nP = rl.ctorParams ∧ nF = rl.nfields ∧ (cvj.type.stripPis (nP + nF)).isSome = true :=
  fun _ _ _ _ _ hf _ hrl _ _ _ hc => h.store.ruleCtor_arity hf hrl hc

theorem FoldStoreInv.tableCtorArity {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    ∀ sn i entry, env.findProj? sn i = some entry →
      ∀ cvC nP nF, env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
        nP = entry.numParams ∧ nF = entry.numFields ∧
          (cvC.type.stripPis (nP + nF)).isSome = true :=
  fun _ _ _ hp _ _ _ hc => h.store.tableCtor_arity hp hc

theorem FoldStoreInv.familyArity {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    ∀ T cvT caps, env.find? T = some (.indInfo cvT caps) →
      (caps.unitlike = true → (cvT.type.stripPis caps.unitParams).isSome = true) ∧
        (caps.eta = true → (cvT.type.stripPis caps.etaParams).isSome = true) :=
  fun _ _ _ hf => h.store.familyArity hf

theorem FoldStoreInv.recEta {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    ∀ k cv mI rP rl, env.find? k = some (.recInfo cv mI rP [rl]) →
      rl.eta = Ix.Kernel.recRuleEtaOf env.find? k rl.ctor :=
  fun k cv mI rP rl hf => (h.recShape k cv mI rP [rl] hf).eta rl List.mem_cons_self

theorem FoldStoreInv.etaSort {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env) :
    ∀ T cvT caps, env.find? T = some (.indInfo cvT caps) → caps.eta = true →
      ∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
        caps.sortZ = Ix.Kernel.Level.zeronessOf l :=
  fun T cvT caps hf he => (h.etaShape T cvT caps hf he).1

theorem FoldStoreInv.etaType_closed {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env)
    {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon} {nP nF : Nat}
    (hT : env.find? T = some (.indInfo cvT caps))
    (hcap : caps.eta = true) (hctorOpt : caps.etaCtor = some kc)
    (hkc : env.find? kc = some (.ctorInfo cvc nP nF))
    {d : Nat} {us : List KLevel} {Ss : List KExpr} {ta : KExpr}
    (hlen : Ss.length = nP + nF)
    (hclosed : ∀ s ∈ Ss.take nP, s.looseBVarsBounded 0 = true)
    (hinf : Infer env .io d (Expr.mkAppN (.const kc us) Ss) ta) :
    Red env d ta (Expr.mkAppN (.const T us) (Ss.take nP)) :=
  etaType_of_closed h.etaShape hT hcap hctorOpt hkc hlen hclosed hinf

theorem piDomAt_eq_some_iff :
    ∀ (n : Nat) (e D : KExpr),
      piDomAt n e = some D ↔
        ∃ pre body bm, e.stripPis n = some (pre, .forallE D body bm)
  | 0, .forallE ty b m, D => by
    simp only [piDomAt, Expr.stripPis, Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h; subst h; exact ⟨[], b, m, rfl, rfl⟩
    · rintro ⟨_, body, bm, _, heq⟩
      cases heq
      rfl
  | 0, .bvar _, _ | 0, .fvar _ _, _ | 0, .sort _, _ | 0, .const _ _, _
  | 0, .app _ _, _ | 0, .lam _ _ _, _ | 0, .letE _ _ _ _, _ | 0, .lit _, _
  | 0, .proj _ _ _, _ => by
    simp [piDomAt, Expr.stripPis]
  | n + 1, .forallE ty b m, D => by
    simp only [piDomAt, Expr.stripPis, Option.map_eq_some_iff, piDomAt_eq_some_iff n b D]
    constructor
    · rintro ⟨pre, body, bm, hst⟩
      exact ⟨(ty, m) :: pre, body, bm, ⟨(pre, .forallE D body bm), hst, rfl⟩⟩
    · rintro ⟨_, body, bm, ⟨⟨pre₀, res₀⟩, hst₀, heq⟩⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      exact ⟨pre₀, body, bm, hst₀⟩
  | n + 1, .bvar _, _ | n + 1, .fvar _ _, _ | n + 1, .sort _, _ | n + 1, .const _ _, _
  | n + 1, .app _ _, _ | n + 1, .lam _ _ _, _ | n + 1, .letE _ _ _ _, _ | n + 1, .lit _, _
  | n + 1, .proj _ _ _, _ => by
    simp [piDomAt, Expr.stripPis]

/-- `EnvFacts.recPlain` for every stored recursor without a model companion (`¬ HasModel env k`). -/
theorem FoldStoreInv.recPlain_of_not_hasModel {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env)
    {k : KKey} {cv cvj : ConstantVal .anon} {mI rP nP nF : Nat} {rls : List (RecRule .anon)}
    {rl : RecRule .anon}
    (hf : env.find? k = some (.recInfo cv mI rP rls))
    (hnm : ¬ Ix.Kernel.Model.HasModel env k)
    (hrl : rl ∈ rls) (hfire : rl.fire = .plain)
    (hc : env.find? rl.ctor = some (.ctorInfo cvj nP nF)) :
    ∃ D T, piDomAt mI cv.type = some D ∧
      D.getAppFn = .const T (cvj.levelParams.map .param) ∧
      D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
      D.getAppArgs.drop nP = (List.range (mI - rP)).map (fun i => .bvar (mI - rP - 1 - i)) := by
  have hnP_eq : nP = rl.ctorParams := (h.store.ruleCtor_arity hf hrl hc).1
  obtain ⟨pre, D, body, bm, T, hst, hfn, htake⟩ := h.store.recPlain hf hrl hfire hc
  obtain ⟨bs', D', B', m', hst', hdrop⟩ := (h.recShape k cv mI rP rls hf).plainIdx hnm rl hrl hfire
  rw [hst] at hst'
  injection Option.some.inj hst' with _ heq
  injection heq with hD_eq _ _
  subst hD_eq
  rw [← hnP_eq] at hdrop
  exact ⟨D, T, (piDomAt_eq_some_iff mI cv.type D).mpr ⟨pre, body, bm, hst⟩, hfn, htake, hdrop⟩

/-- `EnvFacts.ruleCtorHead` for every stored recursor without a model companion (`¬ HasModel env k`). -/
theorem FoldStoreInv.ruleCtorHead_of_not_hasModel {env : Ix.Kernel.Env .anon} (h : FoldStoreInv env)
    {k T : KKey} {cv cvj : ConstantVal .anon} {mI rP nP nF : Nat} {rls : List (RecRule .anon)}
    {rl : RecRule .anon} {us : List KLevel}
    (hf : env.find? k = some (.recInfo cv mI rP rls))
    (hnm : ¬ Ix.Kernel.Model.HasModel env k)
    (hrl : rl ∈ rls)
    (hc : env.find? rl.ctor = some (.ctorInfo cvj nP nF))
    (hdom : (piDomAt mI cv.type).map (·.getAppFn) = some (.const T us)) :
    ∃ tus, (cvj.type.piResult).getAppFn = .const T tus := by
  obtain ⟨D, hpD, hfn⟩ := Option.map_eq_some_iff.mp hdom
  obtain ⟨pre, body, bm, hst⟩ := (piDomAt_eq_some_iff mI cv.type D).mp hpD
  exact (h.recShape k cv mI rP rls hf).ctorHead hnm rl hrl cvj nP nF hc pre D body bm hst T us hfn

/-- Role-table and record-correspondence companions complementing `FoldStoreInv c.env` to assemble
`Core.EnvFacts c` (`etaSort` is already discharged unconditionally by `FoldStoreInv`). -/
structure FoldEnvCompanions (c : Ctx) : Prop where
  natLit : c.inForce .nat → c.inForce .natZero → c.inForce .natSucc →
    Ix.Kernel.natLitSupported c.env = true
  strLit : c.inForce .string → Ix.Kernel.strLitSupported c.env = true
  natOps : ∀ r, c.inForce r → (.role r : KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
    Ix.Kernel.natOpStored c.env (.role r) = true
  natAdd : c.inForce .natAdd → Ix.Kernel.Rules.natAddTyOk (c.env.find? Ix.Kernel.natAddName) = true
  eqStored : c.inForce .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci
  quotBasis : c.inForce .quot → ∀ ci ∈ BasisKind.declsA (md := .anon) .quotK,
    c.env.find? ci.name = some ci
  recMajorRecord : ∀ k cv mI rP rls (p : _root_.Address) us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rls ≠ [] →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
    ∃ cm, Ix.Cert.recordAt c.E p = some cm
  recRulesNodupAndProj : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) →
    (rls.map (·.ctor)).Nodup ∧
    ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (us : List KLevel),
      (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
      Ix.Cert.recordAt c.E p = some cm → cm.info = .iPrj ip →
      ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (cprjAddr ip.block ip.idx.toNat j)
  recPlain : ∀ k cv mI rP rls rl cvj nP nF, c.env.find? k = some (.recInfo cv mI rP rls) →
    rl ∈ rls → rl.fire = .plain → c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    ∃ D T, piDomAt mI cv.type = some D ∧
      D.getAppFn = .const T (cvj.levelParams.map .param) ∧
      D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
      D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)
  ruleCtorHead : ∀ k cv mI rP rls rl cvj nP nF T us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
    c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const T us) →
    ∃ tus, (Expr.piResult cvj.type).getAppFn = .const T tus
  etaType : ∀ (T kc : KKey) (cvT cvc : ConstantVal .anon)
      (caps : IndCaps .anon) (nP nF : Nat),
    c.env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    c.env.find? kc = some (.ctorInfo cvc nP nF) →
    ∀ (d : Nat) (us : List KLevel) (Ss : List KExpr) (ta : KExpr), Ss.length = nP + nF →
      Infer c.env .io d (Expr.mkAppN (.const kc us) Ss) ta →
      Red c.env d ta (Expr.mkAppN (.const T us) (Ss.take nP))

/-- Assemble `Core.EnvFacts c` from `FoldStoreInv c.env`, `c.t.wf = true`, and `FoldEnvCompanions c`. -/
theorem FoldStoreInv.toEnvFacts {c : Ctx} (hS : FoldStoreInv c.env) (htwf : c.t.wf = true)
    (hR : FoldEnvCompanions c) : EnvFacts c where
  tableWf := htwf
  storeClosed := hS.storeClosed
  thmTyped := hS.thmTyped
  natLit := hR.natLit
  strLit := hR.strLit
  natOps := hR.natOps
  natAdd := hR.natAdd
  eqStored := hR.eqStored
  recRules := fun k cv mI rP rls hf =>
    let ⟨hnodup, hprj⟩ := hR.recRulesNodupAndProj k cv mI rP rls hf
    ⟨hnodup, fun rl hrl => hS.store.recRules_fire hf hrl, hprj⟩
  recPlain := hR.recPlain
  store := hS.store
  recMajorRecord := hR.recMajorRecord
  ruleCtorHead := hR.ruleCtorHead
  quotBasis := hR.quotBasis
  etaTowers := hS.etaTowers
  etaType := hR.etaType
  recEta := hS.recEta
  etaSort := hS.etaSort
  recArity := hS.recArity
  ruleCtorArity := hS.ruleCtorArity
  tableCtorArity := hS.tableCtorArity
  familyArity := hS.familyArity

/-! ### Unified set-theoretic fold invariant (`FoldInv`) -/

/-- Unified Wave-5 fold invariant combining `EnvModelT V .verified env` with `FoldStoreInv env`. -/
structure FoldInv (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon) : Prop where
  model : EnvModelT V .verified env
  store : FoldStoreInv env

/-- `FoldInv` holds of the empty environment in every set theory. -/
theorem foldInv_empty : ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V Ix.Kernel.Env.empty :=
  fun _ _ => ⟨EnvModelT.empty, foldStoreInv_empty⟩

/-- `FoldInv` projects to `EnvModelOk V .verified env`. -/
theorem foldInv_envModelOk :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      FoldInv V env → EnvModelOk V .verified env := by
  intro V _ env h
  obtain ⟨⟨mp, _⟩, hE⟩ := h.model
  exact ⟨⟨mp⟩, hE⟩

/-- `FoldInv` projects to `StrongEnvProps env`. -/
theorem foldInv_strongEnvProps :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      FoldInv V env → StrongEnvProps env :=
  fun _ _ _ h => h.store.strongProps

/-- `FoldInv` projects simultaneously to `EnvModelOk V .verified env ∧ StrongEnvProps env`
(the exact pair required by `DeclsStrong`). -/
theorem foldInv_envModelOk_and_strong :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      FoldInv V env → EnvModelOk V .verified env ∧ StrongEnvProps env :=
  fun V _ env h => ⟨foldInv_envModelOk V env h, h.store.strongProps⟩

/-- `FoldInv` projects to `EtaFamiliesClosed env`. -/
theorem foldInv_etaFamiliesClosed :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      FoldInv V env → Ix.Kernel.EtaFamiliesClosed env :=
  fun _ _ _ h => h.model.2

/-- `FoldInv` projects to `TableBodies env`. -/
theorem foldInv_tableBodies :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      FoldInv V env → TableBodies env :=
  fun _ _ _ h => h.store.tableBodies

/-- `FoldInv` supplies `EnvModelM` together with `ThmValOk` and `RulesInputs` at every assignment. -/
theorem foldInv_rulesInputs {V : Type u} [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env .anon}
    (h : FoldInv V env) :
    ∃ mp : EnvModelM V .verified env,
      Ix.Kernel.Model.ThmValOk mp ∧
        ∀ φ, Ix.Kernel.Model.Rules.RulesInputs V mp.base2 φ := by
  obtain ⟨⟨mp, hT⟩, _⟩ := h.model
  exact ⟨mp, hT, fun φ => Ix.Kernel.Model.Rules.RulesInputs.ofSem mp φ⟩

/-- Uniform one-step preservation of `FoldInv` along `DeclRunJ rulesJ (IndRoutesJ rulesJ env)`. -/
theorem foldInv_step_declRunJ {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hna : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  fun _ _ h => ⟨Ix.Kernel.Model.foldRulesRoutes (.cons hd .nil) h.model,
    foldStoreInv_step_declRunJ h.store hna hd⟩

/-! ## Section 4: `FreshChain`, `InstallStep`, and per-route `FoldInv` preservation -/

/-- Named relation for `.quotDecl` in `DeclRunJ`: `.type` installs `BasisKind.quotK`, and the
remaining quotient records (`mk`, `lift`, `ind`) are no-ops. -/
def DeclQuotRunJ (env : Ix.Kernel.Env .anon) (k : QuotKind) (_cv : ConstantVal .anon)
    (env₂ : Ix.Kernel.Env .anon) : Prop :=
  match k with
  | .type => DeclBasisRun env .quotK env₂
  | _ => env₂ = env

/-- Boolean check for expressions free of both `letE` and `fvar`, ensuring reflexive `Annotates`. -/
def noLetNoFvar : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ _ | .letE _ _ _ _ => false
  | .app f a => noLetNoFvar f && noLetNoFvar a
  | .lam ty b _ | .forallE ty b _ => noLetNoFvar ty && noLetNoFvar b
  | .proj _ _ e => noLetNoFvar e

/-- Every expression satisfying `noLetNoFvar e = true` annotates itself. -/
theorem annotates_refl_of_noLetNoFvar :
    ∀ {e : KExpr}, noLetNoFvar e = true → IxVM.Consistency.Annotates e e
  | .bvar _, _ => .bvar
  | .sort _, _ => .sort
  | .const _ _, _ => .const
  | .lit _, _ => .lit
  | .fvar _ _, h | .letE _ _ _ _, h => nomatch h
  | .app f a, h => by
    simp only [noLetNoFvar, Bool.and_eq_true] at h
    exact .app (annotates_refl_of_noLetNoFvar h.1) (annotates_refl_of_noLetNoFvar h.2)
  | .lam ty b _, h => by
    simp only [noLetNoFvar, Bool.and_eq_true] at h
    exact .lam (annotates_refl_of_noLetNoFvar h.1) (annotates_refl_of_noLetNoFvar h.2)
  | .forallE ty b _, h => by
    simp only [noLetNoFvar, Bool.and_eq_true] at h
    exact .forallE (annotates_refl_of_noLetNoFvar h.1) (annotates_refl_of_noLetNoFvar h.2)
  | .proj _ _ e, h => .proj (annotates_refl_of_noLetNoFvar h)

/-- Boolean check for `ConstantInfo` entries that satisfy `StoredAs ci ci` reflexively. -/
def cinfoReflStoredB : ConstantInfo .anon → Bool
  | .axiomInfo cv => noLetNoFvar cv.type
  | .defnInfo cv v _ => noLetNoFvar cv.type && noLetNoFvar v
  | .thmInfo cv v => noLetNoFvar cv.type && noLetNoFvar v
  | .indInfo cv _ => noLetNoFvar cv.type
  | .ctorInfo cv _ _ => noLetNoFvar cv.type
  | .recInfo cv _ _ rules => noLetNoFvar cv.type && rules.all (fun rl => noLetNoFvar rl.rhs)
  | .projInfo _ => false

private theorem rules_refl_of_noLetNoFvar :
    ∀ (rls : List (RecRule .anon)),
      (∀ rl ∈ rls, noLetNoFvar rl.rhs = true) →
      List.Forall₂ IxVM.Consistency.RuleStored rls rls
  | [], _ => .nil
  | rl :: rls, hr =>
    .cons ⟨rfl, rfl, annotates_refl_of_noLetNoFvar (hr rl List.mem_cons_self)⟩
      (rules_refl_of_noLetNoFvar rls fun r hm => hr r (List.mem_cons_of_mem _ hm))

theorem storedAs_refl_of_bool {ci : ConstantInfo .anon} (h : cinfoReflStoredB ci = true) :
    IxVM.Consistency.StoredAs ci ci := by
  cases ci with
  | axiomInfo cv | indInfo cv _ =>
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLetNoFvar h⟩, trivial⟩
  | ctorInfo cv nP nF =>
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLetNoFvar h⟩, rfl, rfl⟩
  | defnInfo cv v hint =>
    simp only [cinfoReflStoredB, Bool.and_eq_true] at h
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLetNoFvar h.1⟩, annotates_refl_of_noLetNoFvar h.2, rfl⟩
  | thmInfo cv v =>
    simp only [cinfoReflStoredB, Bool.and_eq_true] at h
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLetNoFvar h.1⟩, annotates_refl_of_noLetNoFvar h.2⟩
  | recInfo cv mI rP rules =>
    simp only [cinfoReflStoredB, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLetNoFvar h.1⟩, rfl, rfl,
      rules_refl_of_noLetNoFvar rules h.2⟩
  | projInfo _ => exact nomatch h

theorem basisDeclsA_reflStored (kind : BasisKind) :
    ∀ ci ∈ BasisKind.declsA (md := .anon) kind, IxVM.Consistency.StoredAs ci ci := by
  have hall : (BasisKind.declsA (md := .anon) kind).all cinfoReflStoredB = true := by
    cases kind <;> decide
  intro ci hci
  exact storedAs_refl_of_bool (List.all_eq_true.mp hall ci hci)

/-! ### `FreshChain` and generic `InstallStep` constructors -/

/-- Prefix extension certificate from `env` to `acc = ⟨new ++ env.consts⟩` with distinct, fresh
keys in `new`. -/
structure FreshChain (env : Ix.Kernel.Env .anon) (new : List (ConstantInfo .anon))
    (acc : Ix.Kernel.Env .anon) : Prop where
  eq : acc = ⟨new ++ env.consts⟩
  nodup : (new.map (·.name)).Nodup
  fresh : ∀ c ∈ new, env.find? c.name = none

theorem freshChain_nil (env : Ix.Kernel.Env .anon) : FreshChain env [] env :=
  ⟨rfl, List.nodup_nil, fun _ h => nomatch h⟩

theorem freshChain_prepend {env acc : Ix.Kernel.Env .anon} {new xs : List (ConstantInfo .anon)}
    (hc : FreshChain env new acc)
    (hnd : (xs.map (·.name)).Nodup)
    (hfr : ∀ x ∈ xs, acc.find? x.name = none) :
    FreshChain env (xs ++ new) ⟨xs ++ acc.consts⟩ := by
  refine ⟨by rw [hc.eq, List.append_assoc], ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hnd, hc.nodup, ?_⟩
    intro k₁ hk_xs k₂ hk_new heq
    subst heq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk_xs
    obtain ⟨y, hy, hy_eq⟩ := List.mem_map.mp hk_new
    have hnone := hfr x hx
    rw [hc.eq] at hnone
    have hy_mem : y ∈ new ++ env.consts := List.mem_append_left _ hy
    have hneq := List.find?_eq_none.mp hnone y hy_mem
    simp [hy_eq] at hneq
  · intro c hc_mem
    rcases List.mem_append.mp hc_mem with hxs | hnew
    · have hnone := hfr c hxs
      rw [hc.eq] at hnone
      exact List.find?_eq_none.mpr fun y hy =>
        List.find?_eq_none.mp hnone y (List.mem_append_right _ hy)
    · exact hc.fresh c hnew

theorem freshChain_cons {env acc : Ix.Kernel.Env .anon} {new : List (ConstantInfo .anon)}
    {x : ConstantInfo .anon}
    (hc : FreshChain env new acc) (hfr : acc.find? x.name = none) :
    FreshChain env (x :: new) ⟨x :: acc.consts⟩ :=
  freshChain_prepend (xs := [x]) hc (List.nodup_singleton _)
    (fun y hy => by obtain rfl := List.mem_singleton.mp hy; exact hfr)

theorem FreshChain.fresh_of_mem_names {env acc : Ix.Kernel.Env .anon} {new : List (ConstantInfo .anon)}
    (hc : FreshChain env new acc) {k : KKey} (hk : k ∈ new.map (·.name)) :
    env.find? k = none := by
  obtain ⟨c, hc_mem, rfl⟩ := List.mem_map.mp hk
  exact hc.fresh c hc_mem

/-- Generic `InstallStep` constructor for any `FreshChain` whose new names cover `installs d`
(modulo `Key.aux`) and look up to `StoredAs` entries in `env₂`. -/
theorem installStep_glue_of_freshChain {env env₂ : Ix.Kernel.Env .anon}
    {d : Declaration .anon} {new : List (ConstantInfo .anon)}
    (hc : FreshChain env new env₂)
    (hcov : ∀ c ∈ new,
      (∃ ci₀ ∈ IxVM.Consistency.installs d, ci₀.name = c.name) ∨ ∃ k t, c.name = .aux k t)
    (hnames : ∀ ci₀ ∈ IxVM.Consistency.installs d, ci₀.name ∈ new.map (·.name))
    (hstored : ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env d env₂ := by
  refine ⟨new, hc.eq, hc.nodup, hc.fresh, ?_, hcov⟩
  intro ci₀ hci₀
  obtain ⟨ci, hf₂, hst⟩ := hstored ci₀ hci₀
  have hfr₀ : env.find? ci₀.name = none := hc.fresh_of_mem_names (hnames ci₀ hci₀)
  have hmem₂ : ci ∈ env₂.consts := Ix.Kernel.Semantics.Env.find?_mem hf₂
  rw [hc.eq] at hmem₂
  rcases List.mem_append.mp hmem₂ with hnew | hold
  · exact ⟨ci, hnew, hst⟩
  · have hneq := List.find?_eq_none.mp hfr₀ ci hold
    simp [hst.name_eq] at hneq

/-- `InstallStep` for declarations whose `installs d` is empty (`env₂ = env`). -/
theorem installStep_glue_empty (env : Ix.Kernel.Env .anon) {d : Declaration .anon}
    (hempty : IxVM.Consistency.installs d = []) :
    IxVM.Consistency.InstallStep env d env := by
  refine ⟨[], rfl, List.nodup_nil, ?_, ?_, ?_⟩
  · intro _ h; exact nomatch h
  · intro _ h; rw [hempty] at h; exact nomatch h
  · intro _ h; exact nomatch h

/-- `InstallStep` for declarations installing a single fresh constant `ci` matching `ci₀`. -/
theorem installStep_glue_single {env : Ix.Kernel.Env .anon} {d : Declaration .anon}
    {ci ci₀ : ConstantInfo .anon}
    (hinst : IxVM.Consistency.installs d = [ci₀])
    (hfresh : env.find? ci.name = none)
    (hst : IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env d ⟨ci :: env.consts⟩ := by
  refine ⟨[ci], rfl, List.nodup_singleton _,
    fun x hx => by obtain rfl := List.mem_singleton.mp hx; exact hfresh,
    fun x hx => ?_,
    fun x hx => ?_⟩
  · rw [hinst] at hx
    obtain rfl := List.mem_singleton.mp hx
    exact ⟨ci, List.mem_singleton.mpr rfl, hst⟩
  · obtain rfl := List.mem_singleton.mp hx
    exact Or.inl ⟨ci₀, by rw [hinst]; exact List.mem_singleton.mpr rfl, hst.name_eq.symm⟩

/-! ### Route 1: Axioms (`DeclAxiomRunJ`, inert axioms, and `quotSound`) -/

theorem foldInv_step_axiom {env env₂ : Ix.Kernel.Env .anon} {cv : ConstantVal .anon}
    (hrun : DeclAxiomRunJ rulesJ env cv env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  foldInv_step_declRunJ (d := .axiomDecl cv) (fun _ _ heq => nomatch heq) hrun

theorem foldInv_step_axiom_inert {env env₂ : Ix.Kernel.Env .anon}
    (heq : env₂ = env) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  fun _ _ h => by subst heq; exact h

theorem foldInv_step_axiom_quotSound {env env₂ : Ix.Kernel.Env .anon} {cv : ConstantVal .anon}
    (hqs : cv.name = Ix.Kernel.quotSoundName) (heq : env₂ = env) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  foldInv_step_axiom (Or.inl ⟨hqs, heq⟩)

theorem installStep_glue_axiom_inert {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon}
    (hinert : IxVM.Consistency.inertKey cv.name = true) :
    IxVM.Consistency.InstallStep env (.axiomDecl cv) env :=
  installStep_glue_empty env (by simp [IxVM.Consistency.installs, hinert])

theorem installStep_glue_axiom_quotSound {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon}
    (hqs : cv.name = Ix.Kernel.quotSoundName) :
    IxVM.Consistency.InstallStep env (.axiomDecl cv) env :=
  installStep_glue_empty env (by simp [IxVM.Consistency.installs, hqs])

private theorem stdAxiomOk_names {env : Ix.Kernel.Env .anon} {cvA : ConstantVal .anon}
    (hok : Ix.Kernel.stdAxiomOk env cvA = true) :
    cvA.name = Ix.Kernel.propextName ∨ cvA.name = Ix.Kernel.choiceName := by
  unfold Ix.Kernel.stdAxiomOk at hok
  split at hok
  · exact Or.inl ‹_›
  · split at hok
    · exact Or.inr ‹_›
    · cases hok

private theorem env_find?_head_eq {cs : List (ConstantInfo .anon)} {c ci : ConstantInfo .anon}
    {k : KKey} (hk : c.name = k) (hf : (⟨c :: cs⟩ : Ix.Kernel.Env .anon).find? k = some ci) :
    ci = c := by
  rw [Ix.Kernel.Env.find?_cons] at hf
  simp only [hk, ↓reduceIte, Option.some.injEq] at hf
  exact hf.symm

theorem installStep_glue_axiom {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon}
    (hrun : DeclAxiomRunJ J env cv env₂)
    (hstored : env₂ ≠ env →
      ∃ ci, env₂.find? cv.name = some ci ∧ IxVM.Consistency.StoredAs ci (.axiomInfo cv)) :
    IxVM.Consistency.InstallStep env (.axiomDecl cv) env₂ := by
  rcases hrun with ⟨hqs, rfl⟩ | ⟨type', hcv, ⟨hok, henv₂⟩ | ⟨-, -, -, hsorry, rfl⟩⟩
  · exact installStep_glue_axiom_quotSound hqs
  · have hne : env₂ ≠ env := by
      intro heq
      have hlen := congrArg (fun e : Ix.Kernel.Env .anon => e.consts.length) (henv₂.symm.trans heq)
      simp at hlen
    obtain ⟨ci, hf₂, hst⟩ := hstored hne
    have hnot_qs_inert : ¬ (cv.name = Ix.Kernel.quotSoundName ∨
        IxVM.Consistency.inertKey cv.name = true) := by
      rcases stdAxiomOk_names hok with hp | hc
      · change cv.name = Ix.Kernel.propextName at hp
        rw [hp]; decide
      · change cv.name = Ix.Kernel.choiceName at hc
        rw [hc]; decide
    have hinst : IxVM.Consistency.installs (.axiomDecl cv) = [.axiomInfo cv] := by
      simp [IxVM.Consistency.installs, hnot_qs_inert]
    rw [henv₂] at hf₂ ⊢
    obtain rfl := env_find?_head_eq rfl hf₂
    exact installStep_glue_single hinst (Option.isNone_iff_eq_none.mp hcv.1) hst
  · change cv.name = Ix.Kernel.sorryAxName at hsorry
    exact installStep_glue_axiom_inert (by rw [hsorry]; decide)

/-! ### Route 2: Definitions (`DeclDefnRunJ`) -/

theorem foldInv_step_defn {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (hrun : DeclDefnRunJ rulesJ env cv value hint env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  foldInv_step_declRunJ (d := .defnDecl cv value hint) (fun _ _ heq => nomatch heq) hrun

theorem installStep_glue_defn {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (hrun : DeclDefnRunJ J env cv value hint env₂)
    (hstored : ∃ ci, env₂.find? cv.name = some ci ∧
      IxVM.Consistency.StoredAs ci (.defnInfo cv value hint)) :
    IxVM.Consistency.InstallStep env (.defnDecl cv value hint) env₂ := by
  obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
  obtain ⟨ci, hf₂, hst⟩ := hstored
  obtain rfl := env_find?_head_eq rfl hf₂
  exact installStep_glue_single rfl (Option.isNone_iff_eq_none.mp hcv.1) hst

/-! ### Route 3: Theorems (`DeclThmRunJ`) -/

theorem foldInv_step_thm {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hrun : DeclThmRunJ rulesJ env cv value env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  foldInv_step_declRunJ (d := .thmDecl cv value) (fun _ _ heq => nomatch heq) hrun

theorem installStep_glue_thm {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hrun : DeclThmRunJ J env cv value env₂)
    (hstored : ∃ ci, env₂.find? cv.name = some ci ∧
      IxVM.Consistency.StoredAs ci (.thmInfo cv value)) :
    IxVM.Consistency.InstallStep env (.thmDecl cv value) env₂ := by
  obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
  obtain ⟨ci, hf₂, hst⟩ := hstored
  obtain rfl := env_find?_head_eq rfl hf₂
  exact installStep_glue_single rfl (Option.isNone_iff_eq_none.mp hcv.1) hst

/-! ### Route 4: Opaque constants (`DeclOpaqueRunJ`) -/

theorem foldInv_step_opaque {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hrun : DeclOpaqueRunJ rulesJ env cv value env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  foldInv_step_declRunJ (d := .opaqueDecl cv value) (fun _ _ heq => nomatch heq) hrun

theorem installStep_glue_opaque {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hrun : DeclOpaqueRunJ J env cv value env₂)
    (hstored : ∃ ci, env₂.find? cv.name = some ci ∧
      IxVM.Consistency.StoredAs ci (.axiomInfo cv)) :
    IxVM.Consistency.InstallStep env (.opaqueDecl cv value) env₂ := by
  obtain ⟨type', value', hcv, -, rfl⟩ := hrun
  obtain ⟨ci, hf₂, hst⟩ := hstored
  obtain rfl := env_find?_head_eq rfl hf₂
  exact installStep_glue_single rfl (Option.isNone_iff_eq_none.mp hcv.1) hst

/-! ### Routes 5 & 6: Basis (`DeclBasisRun`), pinned `.indDecl`, and Quotient (`DeclQuotRunJ`) -/

private theorem basisInstallRun_freshChain
    (ds : List (ConstantInfo .anon)) {env env₂ : Ix.Kernel.Env .anon}
    (h : Ix.Kernel.Semantics.BasisInstallRun env ds env₂) :
    FreshChain env ds.reverse env₂ := by
  induction ds generalizing env env₂ with
  | nil =>
    change env₂ = env at h
    rw [h]
    exact freshChain_nil env
  | cons ci rest ih =>
    obtain ⟨hfr, hrest⟩ := h
    have hc_rest := ih hrest
    refine ⟨by rw [hc_rest.eq]; simp [List.reverse_cons, List.append_assoc], ?_, ?_⟩
    · rw [List.reverse_cons, List.map_append, List.nodup_append]
      refine ⟨hc_rest.nodup, List.nodup_singleton _, ?_⟩
      intro k₁ hk₁ k₂ hk₂ heq
      subst heq
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk₂
      subst hk₂
      obtain ⟨c, hc, hname⟩ := List.mem_map.mp hk₁
      have hnone := hc_rest.fresh c hc
      rw [Ix.Kernel.Env.find?_cons] at hnone
      simp [hname] at hnone
    · intro c hc
      rw [List.reverse_cons, List.mem_append] at hc
      rcases hc with hmem | hsingle
      · have hnone := hc_rest.fresh c hmem
        rw [Ix.Kernel.Env.find?_cons] at hnone
        split at hnone
        · cases hnone
        · exact hnone
      · obtain rfl := List.mem_singleton.mp hsingle
        exact Option.isNone_iff_eq_none.mp hfr

private theorem installStep_of_declBasisRun {env env₂ : Ix.Kernel.Env .anon}
    {d : Declaration .anon} {kind : BasisKind}
    (hinst : IxVM.Consistency.installs d = kind.declsA)
    (hrun : DeclBasisRun env kind env₂) :
    IxVM.Consistency.InstallStep env d env₂ := by
  have hc := basisInstallRun_freshChain kind.declsA hrun.2
  refine ⟨kind.declsA.reverse, hc.eq, hc.nodup, hc.fresh, ?_, ?_⟩
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    exact ⟨ci₀, List.mem_reverse.mpr hci₀, basisDeclsA_reflStored kind ci₀ hci₀⟩
  · intro ci hci
    exact Or.inl ⟨ci, by rw [hinst]; exact List.mem_reverse.mp hci, rfl⟩

theorem foldInv_step_basis {env env₂ : Ix.Kernel.Env .anon} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  foldInv_step_declRunJ (d := .basisDecl kind) (fun _ _ heq => nomatch heq) hrun

theorem installStep_glue_basis {env env₂ : Ix.Kernel.Env .anon} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) :
    IxVM.Consistency.InstallStep env (.basisDecl kind) env₂ :=
  installStep_of_declBasisRun rfl hrun

theorem foldInv_step_pinnedInd {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {kind : BasisKind}
    (hpin : Ix.Kernel.basisPinHit block = some kind)
    (hrun : DeclBasisRun env kind env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ := by
  have hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
    simpa [DeclRunJ, hpin] using hrun
  exact foldInv_step_declRunJ
    (fun blk _ heq hp => by
      injection heq with hblk _
      subst hblk
      rw [hpin] at hp; cases hp)
    hd

theorem installStep_glue_pinnedInd {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {kind : BasisKind}
    (hpin : Ix.Kernel.basisPinHit block = some kind)
    (hrun : DeclBasisRun env kind env₂) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ :=
  installStep_of_declBasisRun (by simp [IxVM.Consistency.installs, hpin]) hrun

theorem foldInv_step_quot {env env₂ : Ix.Kernel.Env .anon} {k : QuotKind} {cv : ConstantVal .anon}
    (hrun : DeclQuotRunJ env k cv env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  foldInv_step_declRunJ (d := .quotDecl k cv) (fun _ _ heq => nomatch heq) hrun

theorem installStep_glue_quot {env env₂ : Ix.Kernel.Env .anon} {k : QuotKind} {cv : ConstantVal .anon}
    (hrun : DeclQuotRunJ env k cv env₂) :
    IxVM.Consistency.InstallStep env (.quotDecl k cv) env₂ := by
  cases k with
  | type => exact installStep_of_declBasisRun rfl hrun
  | ctor | lift | ind | sound =>
    change env₂ = env at hrun
    rw [hrun]
    exact installStep_glue_empty env rfl

/-! ### Route 7: Modeled inductives (`DeclIndRunJ`) -/

theorem indMembersRunJ_freshChain {J : Judgements .anon} {blockNames : List KKey}
    {caps : IndCaps .anon} {env : Ix.Kernel.Env .anon} :
    ∀ (ms : List (ConstantInfo .anon)) {acc envM : Ix.Kernel.Env .anon} {new₀ : List (ConstantInfo .anon)},
      FreshChain env new₀ acc →
      IndMembersRunJ J blockNames caps acc ms envM →
      ∃ newM, FreshChain env newM envM ∧
        newM.map (·.name) = ms.reverse.map (·.name) ++ new₀.map (·.name)
  | [], acc, envM, new₀, hc, h => by
    subst h
    exact ⟨new₀, hc, rfl⟩
  | ci :: rest, acc, envM, new₀, hc, ⟨cvA, hmv, hrest⟩ => by
    obtain ⟨type', hcv, rfl, -⟩ := hmv
    have hfr : acc.find? ci.toConstantVal.name = none := Option.isNone_iff_eq_none.mp hcv.1
    cases ci with
    | indInfo cvI _ =>
      have hc' := freshChain_cons (x := .indInfo ⟨cvI.name, cvI.levelParams, type'⟩ caps) hc hfr
      obtain ⟨newM, hcM, hnames⟩ := indMembersRunJ_freshChain rest hc' hrest
      exact ⟨newM, hcM, by
        simpa [List.reverse_cons, List.map_append, List.append_assoc,
          ConstantInfo.name, ConstantInfo.toConstantVal] using hnames⟩
    | ctorInfo cvC nP nF =>
      have hc' := freshChain_cons (x := .ctorInfo ⟨cvC.name, cvC.levelParams, type'⟩ nP nF) hc hfr
      obtain ⟨newM, hcM, hnames⟩ := indMembersRunJ_freshChain rest hc' hrest
      exact ⟨newM, hcM, by
        simpa [List.reverse_cons, List.map_append, List.append_assoc,
          ConstantInfo.name, ConstantInfo.toConstantVal] using hnames⟩
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ =>
      exact hrest.elim

theorem provisionRecsRunJ_fresh {J : Judgements .anon} {blockNames : List KKey} :
    ∀ (recs : List (ConstantInfo .anon)) {acc envSelf : Ix.Kernel.Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ J blockNames acc recs envSelf checked →
      checked.map (·.1.name) = recs.map (·.name) ∧
        (checked.map (·.1.name)).Nodup ∧
        ∀ c ∈ checked, acc.find? c.1.name = none
  | [], acc, envSelf, checked, ⟨_, hchk⟩ => by
    subst hchk
    exact ⟨rfl, List.nodup_nil, fun _ h => nomatch h⟩
  | ci :: rest, acc, envSelf, checked, ⟨cvA, mI, rP, rules, rest', hci, hmv, hprov, hchk⟩ => by
    subst hchk
    obtain ⟨type', hcv, rfl, -⟩ := hmv
    have hfr0 : acc.find? ci.toConstantVal.name = none := Option.isNone_iff_eq_none.mp hcv.1
    have hci_name : ci.name = ci.toConstantVal.name := by cases ci <;> rfl
    obtain ⟨hnames, hnd, hfr_rest⟩ := provisionRecsRunJ_fresh rest hprov
    refine ⟨by simp [hnames, hci_name], ?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hmem
      obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
      have hnone := hfr_rest c hc
      rw [Ix.Kernel.Env.find?_cons] at hnone
      simp [hceq, ConstantInfo.name, ConstantInfo.toConstantVal] at hnone
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hfr0
      · have hnone := hfr_rest c hc'
        rw [Ix.Kernel.Env.find?_cons] at hnone
        split at hnone
        · cases hnone
        · exact hnone

theorem indRecsFoldRunJ_prefix {J : Judgements .anon} {blockNames : List KKey}
    {envBase envSelf : Ix.Kernel.Env .anon} :
    ∀ (checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon)))
      {acc out : Ix.Kernel.Env .anon} {done : List (ConstantInfo .anon)},
      IndRecsFoldRunJ J blockNames envBase envSelf ⟨done ++ acc.consts⟩ checked out →
      ∃ newR, out = ⟨(newR ++ done) ++ acc.consts⟩ ∧
        newR.map (·.name) = checked.reverse.map (·.1.name)
  | [], acc, out, done, h => by
    subst h
    exact ⟨[], rfl, rfl⟩
  | c :: rest, acc, out, done, ⟨rules', _, hfold⟩ => by
    have hstep : (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: (done ++ acc.consts)⟩ :
        Ix.Kernel.Env .anon) =
        ⟨(.recInfo c.1 c.2.1 c.2.2.1 rules' :: done) ++ acc.consts⟩ := rfl
    rw [hstep] at hfold
    obtain ⟨newR, hout, hnames⟩ := indRecsFoldRunJ_prefix rest hfold
    refine ⟨newR ++ [.recInfo c.1 c.2.1 c.2.2.1 rules'], ?_, ?_⟩
    · simpa [List.append_assoc] using hout
    · rw [List.map_append, List.reverse_cons, List.map_append, hnames]
      rfl

theorem foldInv_step_indModeled {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hM : DeclIndRunJ rulesJ env block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ := by
  have hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
    simp only [DeclRunJ, hpin]
    exact Or.inr (Or.inl hM)
  exact foldInv_step_declRunJ
    (fun blk _ heq _ => by injection heq with hblk _; subst hblk; exact hna) hd

/-- The checked member and recursor phases install the declared block at arbitrary capabilities. -/
theorem installStep_glue_indPhases {J : Judgements .anon} {env envM env₂ : Ix.Kernel.Env .anon}
    {block members recs : List (ConstantInfo .anon)} {nP : Nat} {caps : IndCaps .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hblk_split : block = members ++ recs)
    (hmem : IndMembersRunJ J (block.map (·.name)) caps env members envM)
    (hrecs : IndRecsRunJ J (block.map (·.name)) envM recs env₂)
    (hstored : ∀ ci₀ ∈ block,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂
 := by
  obtain ⟨newM, hcM, hnamesM⟩ := indMembersRunJ_freshChain _ (freshChain_nil env) hmem
  simp only [List.map_nil, List.append_nil] at hnamesM
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hpin]
  rcases hrecs with ⟨hrecs_nil, rfl⟩ | ⟨_, _, envSelf, checked, hprov, hfold⟩
  · have hblk_eq := hblk_split
    rw [hrecs_nil, List.append_nil] at hblk_eq
    refine installStep_glue_of_freshChain hcM ?_ ?_ ?_
    · intro c hc_mem
      left
      have hk : c.name ∈ newM.map (·.name) := List.mem_map_of_mem hc_mem
      rw [hnamesM] at hk
      obtain ⟨ci₀, hci₀, hnm⟩ := List.mem_map.mp hk
      have hci₀_blk : ci₀ ∈ block := by
        rw [hblk_eq]; exact List.mem_reverse.mp hci₀
      exact ⟨ci₀, by rw [hinst]; exact hci₀_blk, hnm⟩
    · intro ci₀ hci₀
      rw [hinst] at hci₀
      have hci₀_ms := Eq.mp (congrArg (ci₀ ∈ ·) hblk_eq) hci₀
      rw [hnamesM]
      exact List.mem_map_of_mem (List.mem_reverse.mpr hci₀_ms)
    · intro ci₀ hci₀
      rw [hinst] at hci₀
      exact hstored ci₀ hci₀
  · obtain ⟨hchk_names, hchk_nd, hchk_fr⟩ := provisionRecsRunJ_fresh _ hprov
    have hfold' : IndRecsFoldRunJ J (block.map (·.name)) envM envSelf ⟨[] ++ envM.consts⟩
        checked env₂ := hfold
    obtain ⟨newR, hout, hnamesR⟩ := indRecsFoldRunJ_prefix checked hfold'
    simp only [List.append_nil] at hout
    have hndR : (newR.map (·.name)).Nodup := by
      rw [hnamesR, List.map_reverse]
      exact List.nodup_reverse.mpr hchk_nd
    have hfrR : ∀ x ∈ newR, envM.find? x.name = none := by
      intro x hx
      have hk : x.name ∈ checked.map (·.1.name) := by
        have hk' : x.name ∈ checked.reverse.map (·.1.name) := by
          rw [← hnamesR]; exact List.mem_map_of_mem hx
        rw [List.map_reverse] at hk'
        exact List.mem_reverse.mp hk'
      obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hk
      rw [← hceq]
      exact hchk_fr c hc
    have hc₂ : FreshChain env (newR ++ newM) env₂ := by
      rw [hout]
      exact freshChain_prepend hcM hndR hfrR
    have hnamesAll : (newR ++ newM).map (·.name) = block.reverse.map (·.name) := by
      have h1 : newR.map (·.name) = (checked.map (·.1.name)).reverse :=
        hnamesR.trans (List.map_reverse ..)
      have h2 := hnamesM.trans (List.map_reverse ..)
      rw [List.map_append, h1, hchk_names, h2, ← List.reverse_append, ← List.map_append,
        ← hblk_split, List.map_reverse]
    refine installStep_glue_of_freshChain hc₂ ?_ ?_ ?_
    · intro c hc_mem
      left
      have hk : c.name ∈ block.reverse.map (·.name) := by
        rw [← hnamesAll]
        exact List.mem_map_of_mem hc_mem
      obtain ⟨ci₀, hci₀, hnm⟩ := List.mem_map.mp hk
      exact ⟨ci₀, by rw [hinst]; exact List.mem_reverse.mp hci₀, hnm⟩
    · intro ci₀ hci₀
      rw [hinst] at hci₀
      rw [hnamesAll]
      exact List.mem_map_of_mem (List.mem_reverse.mpr hci₀)
    · intro ci₀ hci₀
      rw [hinst] at hci₀
      exact hstored ci₀ hci₀

/-- The empty-capability modeled relation is a specialization of the checked phase installation. -/
theorem installStep_glue_indModeled {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hM : DeclIndRunJ J env block env₂)
    (hstored : ∀ ci₀ ∈ block,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ := by
  obtain ⟨split, envM, members, recs⟩ := hM
  exact installStep_glue_indPhases hpin split members recs hstored

/-! ### Routes 8 & 9: Native inductives (`DeclNativeRunJ`, `DeclNativeNoRecRunJ`) -/

private theorem consSumCtors_consts_eq (nP : Nat) :
    ∀ (ctorsA : List (ConstantVal .anon × Nat)) (e : Ix.Kernel.Env .anon),
      (Ix.Kernel.consSumCtors nP ctorsA e).consts =
        (ctorsA.reverse.map fun c => .ctorInfo c.1 nP c.2) ++ e.consts
  | [], e => rfl
  | c :: cs, e => by
    simp [Ix.Kernel.consSumCtors, consSumCtors_consts_eq nP cs, List.reverse_cons,
      List.map_append, List.append_assoc]

private theorem sumCtorsRunJ_names_fresh {J : Judgements .anon}
    {env env₁ : Ix.Kernel.Env .anon} {T : KKey} {lps : List LevelParam} {nP nIdx : Nat}
    {resSort : KLevel} {isProp large : Bool} {cvTa : ConstantVal .anon}
    {ctors ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hCtors : SumCtorsRunJ J env env₁ T lps nP nIdx resSort isProp large cvTa ctors ctorsA sortss) :
    ctorsA.map (·.1.name) = ctors.map (·.1.name) ∧
      ∀ cA ∈ ctorsA, env₁.find? cA.1.name = none := by
  obtain ⟨hlA, -, hall⟩ := id hCtors
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem
    · simp [hlA]
    · intro j h1 h2
      simp only [List.length_map] at h1 h2
      obtain ⟨_, _, _, hC⟩ := hall j ctors[j] ctorsA[j] (List.getElem?_eq_getElem h2)
        (List.getElem?_eq_getElem h1)
      obtain ⟨cvCa₀, hcc₀, hcc⟩ := hC.1
      simp only [List.getElem_map]
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.name_eq
      · exact hcc'.name_eq
  · intro cA hcA
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcA
    have hj_c : j < ctors.length := by omega
    obtain ⟨_, _, _, hC⟩ := hall j ctors[j] ctorsA[j] (List.getElem?_eq_getElem hj_c)
      (List.getElem?_eq_getElem hj)
    obtain ⟨cvCa₀, hcc₀, hcc⟩ := hC.1
    have hname : ctorsA[j].1.name = ctors[j].1.name := by
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.name_eq
      · exact hcc'.name_eq
    rw [hname]
    exact hcc₀.fresh

private theorem checkNativeTable_freshChain {env X env₂ : Ix.Kernel.Env .anon}
    {newX : List (ConstantInfo .anon)} {p : NativeParts .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hcX : FreshChain env newX X)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    ∃ new₂, FreshChain env new₂ env₂ ∧
      (new₂ = newX ∨ ∃ tbl : ProjTable .anon, new₂ = .projInfo tbl :: newX ∧
        (.projInfo tbl : ConstantInfo .anon).name = .aux p.cvT.name .projTable) := by
  unfold Ix.Kernel.checkNativeTable at hTbl
  split at hTbl
  · next cA sorts =>
    split at hTbl
    · obtain ⟨bodies, -, -, -, hfrT, rfl⟩ := Ix.Kernel.checkStructProjTable_inv hTbl
      let tbl : ProjTable .anon :=
        ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
          Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩
      have hc₂ := freshChain_cons (x := .projInfo tbl) hcX hfrT
      exact ⟨.projInfo tbl :: newX, hc₂, Or.inr ⟨tbl, rfl, rfl⟩⟩
    · injection hTbl with hX_eq
      subst hX_eq
      exact ⟨newX, hcX, Or.inl rfl⟩
  · injection hTbl with hX_eq
    subst hX_eq
    exact ⟨newX, hcX, Or.inl rfl⟩

theorem foldInv_step_indNative {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {p₀ : NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hdp : Ix.Kernel.nativeParts? nP block = some p₀)
    (hN : DeclNativeRunJ rulesJ env p₀ env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ := by
  have hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
    simp only [DeclRunJ, hpin]
    exact Or.inl ⟨p₀, hdp, hN⟩
  exact foldInv_step_declRunJ
    (fun blk _ heq _ => by injection heq with hblk _; subst hblk; exact hna) hd

theorem installStep_glue_indNative {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {p₀ : NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hdp : Ix.Kernel.nativeParts? nP block = some p₀)
    (hN : DeclNativeRunJ J env p₀ env₂)
    (hstored : ∀ ci₀ ∈ block,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ := by
  obtain ⟨caps₀, cs, mI₀, rP₀, rules₀, hblk_eq, hctors₀⟩ := nativeParts?_block_eq hdp
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, _, _, _, hInd,
    hp, hCtors, _, _, _, _, _, _, hRec, hTbl, _⟩ := hN
  obtain ⟨cvTa₀, s, bs, cvS, hchkT, hTa_cases, _, hFS, hp₁, henv₁⟩ := hInd
  have hcvS_name : cvS.name = p₀.cvT.name := by
    have hTa_name : cvTa.name = p₀.cvT.name := by
      rcases hTa_cases with rfl | ⟨_, hTa'⟩
      · exact hchkT.name_eq
      · exact hTa'.name_eq
    rcases hFS with rfl | ⟨rfl, -⟩
    · exact hTa_name
    · exact hchkT.name_eq
  have hc₁ : FreshChain env [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)] env₁ := by
    rw [henv₁]
    exact freshChain_cons (freshChain_nil env) (by show env.find? cvS.name = none; rw [hcvS_name]; exact hchkT.fresh)
  obtain ⟨hctorsA_names, hctorsA_fr⟩ := sumCtorsRunJ_names_fresh hCtors
  have hp_ctors : p.ctors = p₀.ctors := by
    rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
  have hp_cvR : p.cvR = p₀.cvR := by
    rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
  let newCtors : List (ConstantInfo .anon) := ctorsA.reverse.map fun c => .ctorInfo c.1 p.nP c.2
  have hnewCtors_names : newCtors.map (·.name) = (p₀.ctors.map (·.1.name)).reverse := by
    simp [newCtors, List.map_map, Function.comp_def, ConstantInfo.name, ConstantInfo.toConstantVal,
      hctorsA_names, hp_ctors]
  have hcCtors : FreshChain env (newCtors ++ [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)])
      (Ix.Kernel.consSumCtors p.nP ctorsA env₁) := by
    have heqC : Ix.Kernel.consSumCtors p.nP ctorsA env₁ = ⟨newCtors ++ env₁.consts⟩ := by
      cases env₁; exact congrArg Ix.Kernel.Env.mk (consSumCtors_consts_eq p.nP ctorsA _)
    rw [heqC]
    refine freshChain_prepend hc₁ (by rw [hnewCtors_names]; exact List.nodup_reverse.mpr hnd) ?_
    intro x hx
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp hx
    exact hctorsA_fr cA (List.mem_reverse.mp hcA)
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  let recCI : ConstantInfo .anon :=
    .recInfo cvRa p.majorIdx p.rulePrefix
      (Ix.Kernel.sumRules (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP
        p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
  have hrec_name : recCI.name = p₀.cvR.name := by show cvRa.name = p₀.cvR.name; rw [hnR, hp_cvR]
  have hcRec : FreshChain env (recCI :: newCtors ++ [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)])
      ⟨recCI :: (Ix.Kernel.consSumCtors p.nP ctorsA env₁).consts⟩ :=
    freshChain_cons hcCtors (by show _ = none; rw [hrec_name, ← hp_cvR]; exact hfR)
  obtain ⟨new₂, hc₂, htbl_cases⟩ := checkNativeTable_freshChain hcRec hTbl
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hpin]
  have hcore_cov : ∀ c ∈ (recCI :: newCtors ++ [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)]),
      ∃ ci₀ ∈ block, ci₀.name = c.name := by
    intro c hc_mem
    rcases List.mem_cons.mp hc_mem with rfl | hc_rest
    · refine ⟨.recInfo p₀.cvR mI₀ rP₀ rules₀, ?_, hrec_name.symm⟩
      rw [hblk_eq]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
    · rcases List.mem_append.mp hc_rest with hct | hind
      · have hk : c.name ∈ p₀.ctors.map (·.1.name) := by
          have hk' : c.name ∈ (p₀.ctors.map (·.1.name)).reverse := by
            rw [← hnewCtors_names]; exact List.mem_map_of_mem hct
          exact List.mem_reverse.mp hk'
        rw [hctors₀] at hk
        obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hk
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
        refine ⟨.ctorInfo c'.1 c'.2.1 c'.2.2, ?_, hxeq⟩
        rw [hblk_eq]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨c', hc', rfl⟩))
      · obtain rfl := List.mem_singleton.mp hind
        exact ⟨.indInfo p₀.cvT caps₀, by rw [hblk_eq]; exact List.mem_cons_self, hcvS_name.symm⟩
  have hcore_names : ∀ ci₀ ∈ block,
      ci₀.name ∈ (recCI :: newCtors ++
        [ConstantInfo.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)]).map (·.name) := by
    intro ci₀ hci₀
    rw [hblk_eq] at hci₀
    rcases List.mem_cons.mp hci₀ with rfl | hrest
    · simp [ConstantInfo.name, ConstantInfo.toConstantVal, hcvS_name]
    · rcases List.mem_append.mp hrest with hcs | hrec_mem
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hcs
        have hk : c'.1.name ∈ newCtors.map (·.name) := by
          rw [hnewCtors_names, List.mem_reverse, hctors₀]
          exact List.mem_map.mpr ⟨(c'.1, c'.2.2), List.mem_map.mpr ⟨c', hc', rfl⟩, rfl⟩
        rw [List.map_append, List.map_cons]
        exact List.mem_append_left _ (List.mem_cons_of_mem _ hk)
      · obtain rfl := List.mem_singleton.mp hrec_mem
        rw [List.map_append, List.map_cons, List.cons_append, hrec_name]
        exact List.mem_cons_self
  refine installStep_glue_of_freshChain hc₂ ?_ ?_ ?_
  · intro c hc_mem
    rcases htbl_cases with rfl | ⟨tbl, rfl, htbl_name⟩
    · obtain ⟨ci₀, hci₀, hnm⟩ := hcore_cov c hc_mem
      exact Or.inl ⟨ci₀, by rw [hinst]; exact hci₀, hnm⟩
    · rcases List.mem_cons.mp hc_mem with rfl | hc_old
      · exact Or.inr ⟨_, _, htbl_name⟩
      · obtain ⟨ci₀, hci₀, hnm⟩ := hcore_cov c hc_old
        exact Or.inl ⟨ci₀, by rw [hinst]; exact hci₀, hnm⟩
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    rcases htbl_cases with rfl | ⟨tbl, rfl, -⟩
    · exact hcore_names ci₀ hci₀
    · exact List.mem_cons_of_mem _ (hcore_names ci₀ hci₀)
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    exact hstored ci₀ hci₀

theorem foldInv_step_indNativeNoRec {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {p₀ : NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hdp : nativePartsNoRec? nP block = some p₀)
    (hN : DeclNativeNoRecRunJ rulesJ env p₀ env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ := by
  have hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
    simp only [DeclRunJ, hpin]
    exact Or.inr (Or.inr (Or.inl ⟨p₀, hdp, hN⟩))
  exact foldInv_step_declRunJ
    (fun blk _ heq _ => by injection heq with hblk _; subst hblk; exact hna) hd

theorem installStep_glue_indNativeNoRec {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {p₀ : NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hdp : nativePartsNoRec? nP block = some p₀)
    (hN : DeclNativeNoRecRunJ J env p₀ env₂)
    (hstored : ∀ ci₀ ∈ block,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ := by
  obtain ⟨caps₀, cs, hblk_eq, hctors₀⟩ := nativePartsNoRec?_block_eq hdp
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd, hp, hCtors,
    _, _, _, _, _, hTbl, _⟩ := hN
  obtain ⟨cvTa₀, s, bs, cvS, hchkT, hTa_cases, _, hFS, hp₁, henv₁⟩ := hInd
  have hcvS_name : cvS.name = p₀.cvT.name := by
    have hTa_name : cvTa.name = p₀.cvT.name := by
      rcases hTa_cases with rfl | ⟨_, hTa'⟩
      · exact hchkT.name_eq
      · exact hTa'.name_eq
    rcases hFS with rfl | ⟨rfl, -⟩
    · exact hTa_name
    · exact hchkT.name_eq
  have hc₁ : FreshChain env [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)] env₁ := by
    rw [henv₁]
    exact freshChain_cons (freshChain_nil env) (by show env.find? cvS.name = none; rw [hcvS_name]; exact hchkT.fresh)
  obtain ⟨hctorsA_names, hctorsA_fr⟩ := sumCtorsRunJ_names_fresh hCtors
  have hp_ctors : p.ctors = p₀.ctors := by
    rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
  let newCtors : List (ConstantInfo .anon) := ctorsA.reverse.map fun c => .ctorInfo c.1 p.nP c.2
  have hnewCtors_names : newCtors.map (·.name) = (p₀.ctors.map (·.1.name)).reverse := by
    simp [newCtors, List.map_map, Function.comp_def, ConstantInfo.name, ConstantInfo.toConstantVal,
      hctorsA_names, hp_ctors]
  have hcCtors : FreshChain env (newCtors ++ [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)])
      (Ix.Kernel.consSumCtors p.nP ctorsA env₁) := by
    have heqC : Ix.Kernel.consSumCtors p.nP ctorsA env₁ = ⟨newCtors ++ env₁.consts⟩ := by
      cases env₁; exact congrArg Ix.Kernel.Env.mk (consSumCtors_consts_eq p.nP ctorsA _)
    rw [heqC]
    refine freshChain_prepend hc₁ (by rw [hnewCtors_names]; exact List.nodup_reverse.mpr hnd) ?_
    intro x hx
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp hx
    exact hctorsA_fr cA (List.mem_reverse.mp hcA)
  obtain ⟨new₂, hc₂, htbl_cases⟩ := checkNativeTable_freshChain hcCtors hTbl
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hpin]
  have hcore_cov : ∀ c ∈ (newCtors ++ [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)]),
      ∃ ci₀ ∈ block, ci₀.name = c.name := by
    intro c hc_mem
    rcases List.mem_append.mp hc_mem with hct | hind
    · have hk : c.name ∈ p₀.ctors.map (·.1.name) := by
        have hk' : c.name ∈ (p₀.ctors.map (·.1.name)).reverse := by
          rw [← hnewCtors_names]; exact List.mem_map_of_mem hct
        exact List.mem_reverse.mp hk'
      rw [hctors₀] at hk
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hk
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
      refine ⟨.ctorInfo c'.1 c'.2.1 c'.2.2, ?_, hxeq⟩
      rw [hblk_eq]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', rfl⟩)
    · obtain rfl := List.mem_singleton.mp hind
      exact ⟨.indInfo p₀.cvT caps₀, by rw [hblk_eq]; exact List.mem_cons_self, hcvS_name.symm⟩
  have hcore_names : ∀ ci₀ ∈ block,
      ci₀.name ∈ (newCtors ++
        [ConstantInfo.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)]).map (·.name) := by
    intro ci₀ hci₀
    rw [hblk_eq] at hci₀
    rcases List.mem_cons.mp hci₀ with rfl | hcs
    · simp [ConstantInfo.name, ConstantInfo.toConstantVal, hcvS_name]
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hcs
      have hk : c'.1.name ∈ newCtors.map (·.name) := by
        rw [hnewCtors_names, List.mem_reverse, hctors₀]
        exact List.mem_map.mpr ⟨(c'.1, c'.2.2), List.mem_map.mpr ⟨c', hc', rfl⟩, rfl⟩
      rw [List.map_append]
      exact List.mem_append_left _ hk
  refine installStep_glue_of_freshChain hc₂ ?_ ?_ ?_
  · intro c hc_mem
    rcases htbl_cases with rfl | ⟨tbl, rfl, htbl_name⟩
    · obtain ⟨ci₀, hci₀, hnm⟩ := hcore_cov c hc_mem
      exact Or.inl ⟨ci₀, by rw [hinst]; exact hci₀, hnm⟩
    · rcases List.mem_cons.mp hc_mem with rfl | hc_old
      · exact Or.inr ⟨_, _, htbl_name⟩
      · obtain ⟨ci₀, hci₀, hnm⟩ := hcore_cov c hc_old
        exact Or.inl ⟨ci₀, by rw [hinst]; exact hci₀, hnm⟩
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    rcases htbl_cases with rfl | ⟨tbl, rfl, -⟩
    · exact hcore_names ci₀ hci₀
    · exact List.mem_cons_of_mem _ (hcore_names ci₀ hci₀)
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    exact hstored ci₀ hci₀

/-! ### Route 10: Twin recursors (`DeclRecTwinRunJ`) -/

theorem foldInv_step_recTwin {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hT : DeclRecTwinRunJ rulesJ env block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ := by
  have hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
    simp only [DeclRunJ, hpin]
    exact Or.inr (Or.inr (Or.inr hT))
  exact foldInv_step_declRunJ
    (fun blk _ heq _ => by injection heq with hblk _; subst hblk; exact hna) hd

theorem installStep_glue_recTwin {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hT : DeclRecTwinRunJ J env block env₂)
    (hstored : ∀ ci₀ ∈ block,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ := by
  obtain ⟨ws, f, _, hblk_ws, henv₂, hnd_all, hfr_all, _, hmembers⟩ := hT
  have hc : FreshChain env (twinRecs ws ++ twinModels ws) env₂ :=
    ⟨by simpa [List.append_assoc] using henv₂, hnd_all, hfr_all⟩
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hpin]
  refine installStep_glue_of_freshChain hc ?_ ?_ ?_
  · intro c hc_mem
    rcases List.mem_append.mp hc_mem with hrec | hmod
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
      have hw_name : w.cvW'.name = w.cvW.name := (hmembers w hw).1.name_eq
      refine Or.inl ⟨.recInfo w.cvW w.mI w.rP w.rulesW, ?_, hw_name.symm⟩
      rw [hinst, hblk_ws]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    · obtain ⟨w, _, hmi⟩ := List.mem_filterMap.mp hmod
      unfold TwinRecPart.modelInfo? at hmi
      obtain ⟨⟨cvm, mval, hint⟩, _, rfl⟩ := Option.map_eq_some_iff.mp hmi
      exact Or.inr ⟨w.cvW.name, .model, rfl⟩
  · intro ci₀ hci₀
    rw [hinst, hblk_ws] at hci₀
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci₀
    have hw_name : w.cvW'.name = w.cvW.name := (hmembers w hw).1.name_eq
    rw [List.map_append]
    refine List.mem_append_left _ ?_
    change w.cvW.name ∈ (ws.map fun w => ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW').map (·.name)
    rw [List.map_map]
    exact List.mem_map.mpr ⟨w, hw, hw_name⟩
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    exact hstored ci₀ hci₀

/-! ## Section 5: Constructor prefix parameter-domain canonicalization (`copyPrefixPis`) -/

/-- Replace the first `n` `∀`-binder domains of `cty` with the first `n` `∀`-binder domains of
`indTy`, preserving `cty`'s binder metadata and residual body. -/
def copyPrefixPis : Nat → KExpr → KExpr → Option KExpr
  | 0, _, cty => some cty
  | n + 1, .forallE idom ibody _, .forallE _ cbody cm =>
    (copyPrefixPis n ibody cbody).map fun r => .forallE idom r cm
  | _ + 1, _, _ => none

theorem copyPrefixPis_instantiate1Lift (v : KExpr) :
    ∀ (n k : Nat) {indTy cty cty' : KExpr},
      copyPrefixPis n indTy cty = some cty' →
      copyPrefixPis n (indTy.instantiate1Lift v k) (cty.instantiate1Lift v k) =
        some (cty'.instantiate1Lift v k) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ h
    simp only [copyPrefixPis, Option.some.injEq] at h
    subst h; rfl
  | succ n ih =>
    intro k indTy cty _ h
    cases indTy with
    | forallE idom ibody im =>
      cases cty with
      | forallE cdom cbody cm =>
        simp only [copyPrefixPis, Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        simp [Expr.instantiate1Lift, copyPrefixPis, ih (k + 1) hr]
      | _ => simp [copyPrefixPis] at h
    | _ => simp [copyPrefixPis] at h

/-- `Expr.instPisAtLift` along any spine of length `n` ignores the first `n` binder domains, so
`copyPrefixPis n indTy cty` produces the exact same post-parameter body as `cty`. -/
theorem instPisAtLift_copyPrefixPis :
    ∀ (args : List KExpr) {indTy cty cty' : KExpr},
      copyPrefixPis args.length indTy cty = some cty' →
      Expr.instPisAtLift args cty' = Expr.instPisAtLift args cty := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ h
    simp only [List.length_nil, copyPrefixPis, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro indTy cty _ h
    cases indTy with
    | forallE idom ibody im =>
      cases cty with
      | forallE cdom cbody cm =>
        simp only [List.length_cons, copyPrefixPis, Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        simp only [Expr.instPisAtLift]
        exact ih (copyPrefixPis_instantiate1Lift a as.length 0 hr)
      | _ => simp [copyPrefixPis] at h
    | _ => simp [copyPrefixPis] at h

/-- `structProjBodies T nP nF` is invariant under replacing the first `nP` `∀`-binder domains via
`copyPrefixPis nP`. -/
theorem structProjBodies_copyPrefixPis (T : KKey) (nP nF : Nat)
    {indTy cty cty' : KExpr}
    (hcopy : copyPrefixPis nP indTy cty = some cty') :
    Ix.Kernel.structProjBodies T nP nF cty' = Ix.Kernel.structProjBodies T nP nF cty := by
  unfold Ix.Kernel.structProjBodies
  rw [instPisAtLift_copyPrefixPis (Ix.Kernel.structProjPs (md := .anon) nP)
    (by simp only [Ix.Kernel.structProjPs, List.length_map, List.length_range]; exact hcopy)]

/-- Stripping `n + m` `∀`-binders after `copyPrefixPis n` yields the exact same residual body. -/
theorem stripPis_snd_copyPrefixPis :
    ∀ (n m : Nat) {indTy cty cty' : KExpr},
      copyPrefixPis n indTy cty = some cty' →
      (cty'.stripPis (n + m)).map Prod.snd = (cty.stripPis (n + m)).map Prod.snd := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ h
    simp only [copyPrefixPis, Option.some.injEq, Nat.zero_add] at h
    subst h; rfl
  | succ n ih =>
    intro m indTy cty _ h
    cases indTy with
    | forallE idom ibody im =>
      cases cty with
      | forallE cdom cbody cm =>
        simp only [copyPrefixPis, Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        have hadd : n + 1 + m = (n + m) + 1 := by omega
        rw [hadd]
        have hrec := ih m hr
        cases hs1 : r.stripPis (n + m) <;> cases hs2 : cbody.stripPis (n + m) <;>
          simp [Expr.stripPis, hs1, hs2] at hrec ⊢
        exact hrec
      | _ => simp [copyPrefixPis] at h
    | _ => simp [copyPrefixPis] at h

/-- Relational witness that `indTy` annotates the first `n` prefix `∀`-binder domains of `rawCty`
(allowing ζ-reduction of outer `letE` binders on `rawCty` just as `Annotates` does). -/
inductive PrefixDomsAnnot : Nat → KExpr → KExpr → Prop
  | zero {indTy rawCty : KExpr} : PrefixDomsAnnot 0 indTy rawCty
  | forallE {n : Nat} {idom ibody rawDom rawBody : KExpr} {im rm : Ix.Kernel.BinderMeta} :
      IxVM.Consistency.Annotates idom rawDom →
      PrefixDomsAnnot n ibody rawBody →
      PrefixDomsAnnot (n + 1) (.forallE idom ibody im) (.forallE rawDom rawBody rm)
  | letE {n : Nat} {indTy ty v b : KExpr} {lm : Ix.Kernel.LetMeta} :
      PrefixDomsAnnot n indTy (b.instantiate1Lift v) →
      PrefixDomsAnnot n indTy (.letE ty v b lm)

/-- If `cty` annotates `rawCty` and `indTy` annotates the first `n` prefix `∀`-domains of `rawCty`,
then `copyPrefixPis n indTy cty` still annotates `rawCty`. -/
theorem annotates_copyPrefixPis {n : Nat} {indTy cty cty' rawCty : KExpr}
    (hpfx : PrefixDomsAnnot n indTy rawCty)
    (hann : IxVM.Consistency.Annotates cty rawCty)
    (hcopy : copyPrefixPis n indTy cty = some cty') :
    IxVM.Consistency.Annotates cty' rawCty := by
  induction hpfx generalizing cty cty' with
  | zero =>
    simp only [copyPrefixPis, Option.some.injEq] at hcopy
    subst hcopy
    exact hann
  | @forallE n idom ibody rawDom rawBody im rm hdom _ ih =>
    cases hann with
    | forallE _ hbody =>
      simp only [copyPrefixPis, Option.map_eq_some_iff] at hcopy
      obtain ⟨r, hr, rfl⟩ := hcopy
      exact .forallE hdom (ih hbody hr)
  | letE _ ih =>
    cases hann with
    | letE hred => exact .letE (ih hred hcopy)

end IxVM.Refinement.Decl


