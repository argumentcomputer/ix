import IxVMRefinement.FamilyAlias.ProjTablePrep
import IxVMRefinement.FamilyAlias.ProjCoherenceTop
import IxVMRefinement.FamilyAlias.StoreAr
import IxVMRefinement.FamilyAlias.EqPin
import IxCK.Kernel.Model.Inductives.StructBodyFrames
import IxCK.Kernel.Model.Inductives.StructEntryKit
import IxCK.Kernel.Model.Inductives.TowerCons
import IxCK.Kernel.Model.IndCons
import IxCK.Kernel.Model.IndUnitLaw
import IxCK.Kernel.Model.Caps
import IxCK.Kernel.Model.RecRulesCons
import IxCK.Kernel.Model.Annot.BitLevels

/-! # Chain-axiom installation and `TowerEntryLaw` for modeled structure projections

Proves the two semantic building blocks consumed by `FamilyAlias/ProjTableInstall.lean`:

* **Section 1**: General telescope, `ExprLvEq`, `renameAll`, `instSeq`, `TeleFit`, `mkAppN`,
  `basisEnv`, and `denoteMeta` monotonicity helpers.
* **Section 2**: `chainAxiom_step`: installs one `chainAxiom T j` (`[0] : Sort 1`) with leaf
  `A_chain` from `field_chain_coherence` via `declStep_preserves_of_ind_cons`, preserving
  `ModelExt`, `EtaFamiliesClosed`, `StoreInv`, `StoreArR`, and `NoProjEnv`.
* **Section 3**: `modeled_towerEntryLaw`: establishes `TowerEntryLaw m₂ φ T i (tbl.entry i)`
  (`off = 2`, `structSort.isNeverZero = true`, `capsT.eta = false`):
  - Clause (A) equates the opened table body (`structProjBody_open` + `Rules.denoteMeta_instPisAt_peel`
    + `peelPis_of_piTeleAV`) to `fp.rdom` (`projFieldTeleAt` + `denoteMeta_exprSemEq`) at
    `ρ' = consList (vs_v ++ [x_v]) ρ` via `field_chain_coherence` and `wellDenotedV_instSeq_iff`;
  - Clause (B) combines `TeleFit`, `m₂.mem_type`, `field_chain_coherence`, `fp.hfindIota`,
    `mp₀.eq_law`, and `mem_eqv` to show `proj_i (C ys) = ys[nP + i]`;
  - Clause (C), `TowerO5`, and `capsT.eta` are vacuous.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Refinement.Core
open IxVM.Refinement.Decl (ExprSemEq)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule ProjEntry ProjTable LevelParam
  BinderMeta Key Env EnvExt SetTheory)
open Ix.Kernel.Semantics
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open Ix.Kernel.Model

/-! ## Section 1: Telescope, `ExprLvEq`, `instSeq`, `TeleFit`, and `denoteMeta` helpers -/

/-- `Core.ExprLvEq` implies `Decl.ExprSemEq`. -/
theorem exprSemEq_of_exprLvEq {e₁ e₂ : KExpr} (h : Core.ExprLvEq e₁ e₂) :
    ExprSemEq e₁ e₂ := by
  induction h with
  | bvar => exact .bvar _
  | fvar _ ih => exact .fvar ih
  | sort hl => exact .sort hl
  | const hl => exact .const hl
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam rfl iht ihb
  | forallE _ _ iht ihb => exact .forallE rfl iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | lit => exact .lit _
  | proj _ ihe => exact .proj ihe

/-- Symmetry of `Decl.ExprSemEq`. -/
theorem exprSemEq_symm {e₁ e₂ : KExpr} (h : ExprSemEq e₁ e₂) : ExprSemEq e₂ e₁ := by
  induction h with
  | bvar => exact .bvar _
  | fvar _ ih => exact .fvar ih
  | sort hl => exact .sort (fun φ => (hl φ).symm)
  | const hl => exact .const (IxVM.Refinement.Decl.LvEqList.symm hl)
  | lit => exact .lit _
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw _ _ iht ihb => exact .lam hpw.symm iht ihb
  | forallE hpw _ _ iht ihb => exact .forallE hpw.symm iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

/-- On an fvar-free expression with no `.proj s _ _` where `g s ≠ s`, `Decl.renameAll g` equals
`Expr.renameConsts g`. -/
theorem renameAll_eq_renameConsts_of_noProj {g : KKey → KKey} {bn : List KKey}
    (hout : ∀ k, k ∉ bn → g k = k) :
    ∀ {e : KExpr}, e.hasFvar = false → (∀ k ∈ bn, ∀ i, Expr.NoProjAt k i e) →
      Decl.renameAll g e = e.renameConsts g
  | .bvar _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .lit _, _, _ => rfl
  | .fvar _ _, hfv, _ => by simp [Expr.hasFvar] at hfv
  | .app f a, hfv, hnp => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Decl.renameAll, Expr.renameConsts]
    congr 1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.1 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_app.mp (hnp k hk i)).1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.2 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_app.mp (hnp k hk i)).2
  | .lam t b _, hfv, hnp => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Decl.renameAll, Expr.renameConsts]
    congr 1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.1 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_lam.mp (hnp k hk i)).1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.2 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_lam.mp (hnp k hk i)).2
  | .forallE t b _, hfv, hnp => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Decl.renameAll, Expr.renameConsts]
    congr 1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.1 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp k hk i)).1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.2 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp k hk i)).2
  | .letE t v b _, hfv, hnp => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Decl.renameAll, Expr.renameConsts]
    congr 1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.1.1 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_letE.mp (hnp k hk i)).1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.1.2 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_letE.mp (hnp k hk i)).2.1
    · exact renameAll_eq_renameConsts_of_noProj hout hfv.2 fun k hk i =>
        (Ix.Kernel.Expr.noProjAt_letE.mp (hnp k hk i)).2.2
  | .proj s j sub, hfv, hnp => by
    have hs : s ∉ bn := fun hmem =>
      (Ix.Kernel.Expr.noProjAt_proj.mp (hnp s hmem j)).1 ⟨rfl, rfl⟩
    simp only [Decl.renameAll, Expr.renameConsts, hout s hs]
    congr 1
    exact renameAll_eq_renameConsts_of_noProj hout hfv fun k hk i =>
      (Ix.Kernel.Expr.noProjAt_proj.mp (hnp k hk i)).2

/-- Bidirectional grading across `AnnotTerm.instSeq`: when every substituted argument is
`WellDenotedV`, `instSeq` is `WellDenotedV` at `ρ` iff the body is `WellDenotedV` at
`chain V ρ ws`. -/
theorem wellDenotedV_instSeq_iff {V : Type u} [SetTheory V] {ρ : Nat → V} :
    ∀ (ws : List AnnotTerm) (X : AnnotTerm),
      (∀ w ∈ ws, WellDenotedV V ρ w) →
      (WellDenotedV V ρ (Ix.Kernel.Model.AnnotTerm.instSeq ws (ws.length - 1) X) ↔
        WellDenotedV V (chain V ρ ws) X)
  | [], X, _ => Iff.rfl
  | w :: ws, X, hoks => by
    have hokw : WellDenotedV V ρ w := hoks w List.mem_cons_self
    have hshift : shiftE ws.length 0 (chain V ρ ws) = ρ := shiftE_chain ρ ws
    have hstep : WellDenotedV V (chain V ρ ws) (X.inst w ws.length) ↔
        WellDenotedV V (chain V ρ (w :: ws)) X := by
      refine and_congr ?_ ?_
      · rw [WellDenoted_inst V X w ws.length (chain V ρ ws) (by rw [hshift]; exact hokw.1),
          hshift, ← chain_cons_eq_instE]
      · rw [AnnotValid_inst V X w ws.length (chain V ρ ws) (by rw [hshift]; exact hokw.2),
          hshift, ← chain_cons_eq_instE]
    have hcons : (w :: ws).length - 1 = ws.length := by simp
    rw [hcons, AnnotTerm.instSeq_cons,
      wellDenotedV_instSeq_iff ws (X.inst w ws.length) (fun u hu => hoks u (List.mem_cons_of_mem _ hu)),
      hstep]

/-- `chain V ρ ws` depends only on `ws.map (interp V ρ)` (it is `consList (ws.map (interp V ρ)) ρ`). -/
theorem chain_eq_consList_map {V : Type u} [SetTheory V] (ρ : Nat → V) (ws : List AnnotTerm) :
    chain V ρ ws = consList (ws.map (interp V ρ)) ρ := by
  funext i
  by_cases hi : i < ws.length
  · rw [chain_lt hi]
    have hlen : (ws.map (interp V ρ)).length = ws.length := by simp
    rw [consList_getElem (ws.map (interp V ρ)) ρ i (by omega)]
    have hlt : ws.length - 1 - i < ws.length := by omega
    simp only [hlen, List.getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_map]
  · have hge : ws.length ≤ i := Nat.not_lt.mp hi
    rw [chain_ge hge]
    have hi_eq : i = (ws.map (interp V ρ)).length + (i - ws.length) := by simp; omega
    conv_rhs => rw [hi_eq]
    rw [consList_ge]

/-- Equal `interp` lists give identical `chain` environments. -/
theorem chain_eq_of_map_interp_eq {V : Type u} [SetTheory V] {ρ : Nat → V}
    {ws₁ ws₂ : List AnnotTerm} (h : ws₁.map (interp V ρ) = ws₂.map (interp V ρ)) :
    chain V ρ ws₁ = chain V ρ ws₂ := by
  rw [chain_eq_consList_map, chain_eq_consList_map, h]

/-- Decompose `WellDenotedV V ρ (AnnotTerm.mkAppN f vs)` into `WellDenotedV` of `f`, every
element of `vs`, and `AppChainOk` along `vs.map (interp V ρ)`. -/
theorem wellDenotedV_mkAppN_inv {V : Type u} [SetTheory V] {ρ : Nat → V} :
    ∀ (f : AnnotTerm) (vs : List AnnotTerm),
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs) →
      WellDenotedV V ρ f ∧ (∀ v ∈ vs, WellDenotedV V ρ v) ∧
        AppChainOk (interp V ρ f) (vs.map (interp V ρ))
  | f, [], h => ⟨h, (fun _ hm => nomatch hm), trivial⟩
  | f, v :: vs, h => by
    simp only [AnnotTerm.mkAppN] at h
    obtain ⟨hfa, hvs, hch⟩ := wellDenotedV_mkAppN_inv (.app f v) vs h
    rw [WellDenotedV, WellDenoted_app, AnnotValid_app] at hfa
    refine ⟨⟨hfa.1.1, hfa.2.1⟩, fun u hu => ?_, ?_⟩
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨hfa.1.2.1, hfa.2.2⟩
      · exact hvs u hu
    · simp only [List.map_cons, AppChainOk]
      exact ⟨hfa.1.2.2, by simpa [interp_app] using hch⟩

/-- Build `WellDenotedV V ρ (AnnotTerm.mkAppN f vs)` from `WellDenotedV` of `f`, every `v ∈ vs`,
and `AppChainOk`. -/
theorem wellDenotedV_mkAppN_of {V : Type u} [SetTheory V] {ρ : Nat → V} :
    ∀ (f : AnnotTerm) (vs : List AnnotTerm),
      WellDenotedV V ρ f →
      (∀ v ∈ vs, WellDenotedV V ρ v) →
      AppChainOk (interp V ρ f) (vs.map (interp V ρ)) →
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs)
  | f, [], hf, _, _ => hf
  | f, v :: vs, hf, hvs, hch => by
    simp only [List.map_cons, AppChainOk] at hch
    have hv : WellDenotedV V ρ v := hvs v List.mem_cons_self
    have hfa : WellDenotedV V ρ (.app f v) :=
      ⟨by rw [WellDenoted_app]; exact ⟨hf.1, hv.1, hch.1⟩,
        by rw [AnnotValid_app]; exact ⟨hf.2, hv.2⟩⟩
    exact wellDenotedV_mkAppN_of (.app f v) vs hfa
      (fun u hu => hvs u (List.mem_cons_of_mem _ hu))
      (by simpa [interp_app] using hch.2)

/-- `TeleFit` along `mkPisAV ds body` decomposes into `SpineFit` on `ds.map (·.2.2)` and
`rest = interp V (consList ys ρ) body`. -/
theorem teleFit_mkPisAV_iff {V : Type u} [SetTheory V] :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (body : AnnotTerm) (ρ : Nat → V)
      (ys : List V) (rest : V),
      ys.length = ds.length →
      (TeleFit V ρ (mkPisAV ds body) ys rest ↔
        SpineFit ρ (ds.map (·.2.2)) ys ∧ rest = interp V (consList ys ρ) body)
  | [], body, ρ, [], rest, _ => by
    simp only [mkPisAV, List.map_nil, SpineFit, consList, true_and]
    exact ⟨fun h => teleFit_nil_inv h, fun h => h ▸ TeleFit.nil⟩
  | d :: ds, body, ρ, y :: ys, rest, hlen => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [mkPisAV, List.map_cons, SpineFit, consList]
    constructor
    · intro h
      cases h with
      | cons hy hrest =>
        have ih := (teleFit_mkPisAV_iff ds body (cons y ρ) ys rest hlen).mp hrest
        exact ⟨⟨hy, ih.1⟩, ih.2⟩
    · rintro ⟨⟨hy, hsp⟩, rfl⟩
      exact TeleFit.cons hy ((teleFit_mkPisAV_iff ds body (cons y ρ) ys _ hlen).mpr ⟨hsp, rfl⟩)
  | [], _, _, _ :: _, _, hlen => by simp at hlen
  | _ :: _, _, _, [], _, hlen => by simp at hlen

/-- The `k` projection-application arguments used by `projFieldTeleAt`. -/
def projAppsD (nP bnl : Nat) (projKeyAt : Nat → KKey) (k : Nat) : List KExpr :=
  (List.range k).map fun j =>
    Expr.mkAppN (.const (projKeyAt j) ((List.range bnl).map .param))
      (Ix.Kernel.fvsD nP ++ [Ix.Kernel.tfvD nP])

theorem projAppsD_length (nP bnl : Nat) (projKeyAt : Nat → KKey) (k : Nat) :
    (projAppsD nP bnl projKeyAt k).length = k := by
  simp [projAppsD]

private theorem instPisAt_append (as bs : List KExpr) :
    ∀ (e : KExpr),
      Expr.instPisAt (as ++ bs) e =
        (Expr.instPisAt as e).bind fun ⟨ds₁, r₁⟩ =>
          (Expr.instPisAt bs r₁).map fun ⟨ds₂, r₂⟩ => (ds₁ ++ ds₂, r₂) := by
  induction as with
  | nil =>
    intro e
    simp [Expr.instPisAt]
  | cons a as ih =>
    intro e
    cases e with
    | forallE d b m =>
      simp only [List.cons_append, Expr.instPisAt, ih (b.instantiate1 a 0)]
      cases Expr.instPisAt as (b.instantiate1 a 0) with
      | none => rfl
      | some p =>
        simp only [Option.map_some, Option.bind_some]
        cases Expr.instPisAt bs p.2 <;> simp
    | _ => simp [Expr.instPisAt]

/-- `projFieldTeleAt` is the residual of `Expr.instPisAt` along `fvsD nP ++ projAppsD nP bnl projKeyAt k`. -/
theorem projFieldTeleAt_eq_instPisAt (cty : KExpr) (nP bnl : Nat) (projKeyAt : Nat → KKey) :
    ∀ (k : Nat),
      projFieldTeleAt cty nP bnl projKeyAt k =
        (Expr.instPisAt (Ix.Kernel.fvsD nP ++ projAppsD nP bnl projKeyAt k) cty).map Prod.snd
  | 0 => by
    simp [projFieldTeleAt, projAppsD, Ix.Kernel.fvsD]
  | k + 1 => by
    have h1 : projAppsD nP bnl projKeyAt (k + 1) =
        projAppsD nP bnl projKeyAt k ++
          [Expr.mkAppN (.const (projKeyAt k) ((List.range bnl).map .param))
            (Ix.Kernel.fvsD nP ++ [Ix.Kernel.tfvD nP])] := by
      simp [projAppsD, List.range_succ]
    rw [h1, ← List.append_assoc, instPisAt_append, projFieldTeleAt,
      projFieldTeleAt_eq_instPisAt cty nP bnl projKeyAt k]
    cases Expr.instPisAt (Ix.Kernel.fvsD nP ++ projAppsD nP bnl projKeyAt k) cty with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.bind_some]
      cases p.2 with
      | forallE d b m =>
        simp [Expr.instPisAt, Ix.Kernel.fvsD, Ix.Kernel.tfvD]
      | _ => simp [Expr.instPisAt]

/-- Every constant of `TableInhabit.basisEnv` is stored at its name in any nodup extension of a
valid table's environment `envT`. -/
theorem basisPins_of_shape {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env}
    {envT env : Env .anon} (hshape : IxVM.Consistency.TableShape.{u} t G R envT)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup) :
    ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci := by
  intro ci hci
  have hmem : ci ∈ env.consts := by
    simp only [IxVM.Refinement.TableInhabit.basisEnv, List.mem_cons, List.not_mem_nil,
      or_false] at hci
    rcases hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
    · exact hext _ (hshape.pins .quotK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .quotK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .quotK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .quotK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .quotK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .falseK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .falseK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .emptyK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .emptyK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .punitK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .punitK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .punitK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .natK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .natK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .natK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .natK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .eqK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .eqK _ (by simp [Ix.Kernel.BasisKind.declsA]))
    · exact hext _ (hshape.pins .eqK _ (by simp [Ix.Kernel.BasisKind.declsA]))
  exact find_of_mem_nodup hnd hmem

/-- `denoteMeta` is preserved along a `ModelExt` when every `.proj s j _` in `e` has
`env₂.findProj? s j = env₁.findProj? s j` (in particular when new projection tables are for
structures that `e` has `NoProjAt` for). -/
theorem denoteMeta_ext_of_findProj_eq {V : Type u} [SetTheory V] {env₁ env₂ : Env .anon}
    {mp₁ : EnvModelM V .verified env₁} {mp₂ : EnvModelM V .verified env₂}
    (hext : ModelExt mp₁ mp₂)
    (hfind : ∀ {k : KKey} {ci : ConstantInfo .anon}, env₁.find? k = some ci → env₂.find? k = some ci)
    (φ : LevelParam → Nat) (d : Nat) (e : KExpr)
    (hres : e.constsResolve env₁ = true)
    (hnp : ∀ s j, env₂.findProj? s j ≠ env₁.findProj? s j → Expr.NoProjAt s j e) :
    denoteMeta mp₂.base2.acval env₂ φ d e = denoteMeta mp₁.base2.acval env₁ φ d e := by
  have hfind_eq : ∀ k, (env₁.find? k).isSome = true → env₂.find? k = env₁.find? k := fun k hk => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
    rw [hfind hci, hci]
  match e with
  | .bvar _ | .fvar _ _ | .sort _ | .letE _ _ _ _ => simp [denoteMeta]
  | .lit (.natVal n) =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    have hnat : Ix.Kernel.natLitSupported env₂ = Ix.Kernel.natLitSupported env₁ := by
      simp only [Ix.Kernel.natLitSupported, hfind_eq _ hres.1.1, hfind_eq _ hres.1.2,
        hfind_eq _ hres.2]
    simp only [denoteMeta, hnat,
      modelExt_acval_eq_of_isSome hext hres.1.2,
      modelExt_acval_eq_of_isSome hext hres.2]
  | .lit (.strVal s) =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hres
    have hstr : Ix.Kernel.strLitSupported env₂ = Ix.Kernel.strLitSupported env₁ := by
      simp only [Ix.Kernel.strLitSupported, Ix.Kernel.natLitSupported,
        hfind_eq _ h1, hfind_eq _ h2, hfind_eq _ h3, hfind_eq _ h4, hfind_eq _ h5,
        hfind_eq _ h6, hfind_eq _ h7, hfind_eq _ h8, hfind_eq _ h9, hfind_eq _ h10]
    have hlpNil : Ix.Kernel.Verify.levelParamsAt env₂ Ix.Kernel.listNilName =
        Ix.Kernel.Verify.levelParamsAt env₁ Ix.Kernel.listNilName := by
      simp only [Ix.Kernel.Verify.levelParamsAt, hfind_eq _ h7]
    have hlpCons : Ix.Kernel.Verify.levelParamsAt env₂ Ix.Kernel.listConsName =
        Ix.Kernel.Verify.levelParamsAt env₁ Ix.Kernel.listConsName := by
      simp only [Ix.Kernel.Verify.levelParamsAt, hfind_eq _ h8]
    simp only [denoteMeta, hstr, hlpNil, hlpCons,
      modelExt_acval_eq_of_isSome hext h2,
      modelExt_acval_eq_of_isSome hext h3,
      modelExt_acval_eq_of_isSome hext h5,
      modelExt_acval_eq_of_isSome hext h7,
      modelExt_acval_eq_of_isSome hext h8,
      modelExt_acval_eq_of_isSome hext h9,
      modelExt_acval_eq_of_isSome hext h10]
  | .const k us =>
    simp only [Expr.constsResolve] at hres
    simp only [denoteMeta, hfind_eq k hres]
    cases hf : env₁.find? k with
    | none => simp [hf] at hres
    | some ci =>
      dsimp only
      split
      · rw [modelExt_acval_eq_of_isSome hext hres]
      · rfl
  | .app f a =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    simp only [denoteMeta,
      denoteMeta_ext_of_findProj_eq hext hfind φ d f hres.1
        (fun s j hne => (Ix.Kernel.Expr.noProjAt_app.mp (hnp s j hne)).1),
      denoteMeta_ext_of_findProj_eq hext hfind φ d a hres.2
        (fun s j hne => (Ix.Kernel.Expr.noProjAt_app.mp (hnp s j hne)).2)]
  | .lam dom body bm =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    simp only [denoteMeta,
      denoteMeta_ext_of_findProj_eq hext hfind φ d dom hres.1
        (fun s j hne => (Ix.Kernel.Expr.noProjAt_lam.mp (hnp s j hne)).1),
      denoteMeta_ext_of_findProj_eq hext hfind φ (d + 1) (body.instantiate1 (.fvar d dom) 0)
        (Expr.constsResolve_instantiate1 hres.1 0 hres.2)
        (fun s j hne => noProjAt_instantiate1_prop (T := s) (i := j) (v := .fvar d dom)
          (by simpa using (Ix.Kernel.Expr.noProjAt_lam.mp (hnp s j hne)).1)
          body 0 (Ix.Kernel.Expr.noProjAt_lam.mp (hnp s j hne)).2)]
  | .forallE dom body bm =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    simp only [denoteMeta,
      denoteMeta_ext_of_findProj_eq hext hfind φ d dom hres.1
        (fun s j hne => (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp s j hne)).1),
      denoteMeta_ext_of_findProj_eq hext hfind φ (d + 1) (body.instantiate1 (.fvar d dom) 0)
        (Expr.constsResolve_instantiate1 hres.1 0 hres.2)
        (fun s j hne => noProjAt_instantiate1_prop (T := s) (i := j) (v := .fvar d dom)
          (by simpa using (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp s j hne)).1)
          body 0 (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp s j hne)).2)]
  | .proj s j sub =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    have hpeq : env₂.findProj? s j = env₁.findProj? s j := by
      by_contra hne
      exact (Ix.Kernel.Expr.noProjAt_proj.mp (hnp s j hne)).1 ⟨rfl, rfl⟩
    have ihs := denoteMeta_ext_of_findProj_eq hext hfind φ d sub hres.2
      (fun s' j' hne => (Ix.Kernel.Expr.noProjAt_proj.mp (hnp s' j' hne)).2)
    simp only [denoteMeta, ihs, hpeq]
    cases hfp : env₁.findProj? s j with
    | none => rfl
    | some entry =>
      cases hsub : denoteMeta mp₁.base2.acval env₁ φ d sub with
      | none => rfl
      | some ea =>
        change (if entry.off ≤ 1 then some (projAV (j + entry.off) ea)
            else if (env₂.find? (Ix.Kernel.projChainKey s j)).isSome = true then
              some (AnnotTerm.chain (fun n => mp₂.base2.acval (Ix.Kernel.projChainKey s j) (fun _ => n)) ea)
            else none) =
          (if entry.off ≤ 1 then some (projAV (j + entry.off) ea)
            else if (env₁.find? (Ix.Kernel.projChainKey s j)).isSome = true then
              some (AnnotTerm.chain (fun n => mp₁.base2.acval (Ix.Kernel.projChainKey s j) (fun _ => n)) ea)
            else none)
        by_cases hle : entry.off ≤ 1
        · simp only [hle, ↓reduceIte]
        · obtain ⟨tbl, hftbl, hlt, rfl⟩ := Ix.Kernel.Env.findProj?_some hfp
          have hsn : tbl.structName = s :=
            projTableName_inj (Ix.Kernel.Semantics.Env.find?_name hftbl)
          have hch : (env₁.find? (Ix.Kernel.projChainKey s j)).isSome = true := by
            have h1 := (mp₁.base2.proj_ok _ tbl hftbl j hlt).chain_isSome hle
            simpa [ProjTable.entry, hsn] using h1
          have hch₂ : (env₂.find? (Ix.Kernel.projChainKey s j)).isSome = true :=
            modelExt_isSome_mono hext hch
          simp only [hle, hch₂, hch, ↓reduceIte]
          exact congrArg some (congrArg (fun f => AnnotTerm.chain f ea)
            (funext fun n => modelExt_acval_eq_of_isSome hext hch (fun _ => n)))
termination_by Expr.sizeB e
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; done)
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB])

private theorem denoteMetaSpine_to_getElem {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} {d : Nat} :
    ∀ {args : List KExpr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d args vs →
      ∃ hlen : vs.length = args.length,
        ∀ k (hk : k < args.length),
          denoteMeta acval env φ d args[k] = some (vs[k]'(hlen ▸ hk))
  | [], [], .nil => ⟨rfl, fun _ hk => nomatch hk⟩
  | a :: as, v :: vs, .cons ha hsp => by
    obtain ⟨hlen, hget⟩ := denoteMetaSpine_to_getElem hsp
    refine ⟨by simp [hlen], fun k hk => ?_⟩
    cases k with
    | zero => exact ha
    | succ k => exact hget k (Nat.lt_of_succ_lt_succ hk)

private theorem denoteMeta_mkAppN_some {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {φ : LevelParam → Nat} {d : Nat} {f : KExpr} {args : List KExpr}
    {res : AnnotTerm}
    (h : denoteMeta acval env φ d (Expr.mkAppN f args) = some res) :
    ∃ (fa : AnnotTerm) (vs : List AnnotTerm) (hlen : vs.length = args.length),
      denoteMeta acval env φ d f = some fa ∧
      (∀ k (hk : k < args.length),
        denoteMeta acval env φ d args[k] = some (vs[k]'(hlen ▸ hk))) ∧
      res = AnnotTerm.mkAppN fa vs := by
  obtain ⟨fa, vs, hfa, hsp, hres⟩ := denoteMeta_mkAppN_inv h
  obtain ⟨hlen, hget⟩ := denoteMetaSpine_to_getElem hsp
  exact ⟨fa, vs, hlen, hfa, hget, hres⟩

/-! ## Section 2: Single `chainAxiom` installation step -/

/-- `ConstWF` for `chainAxiom T j` in any environment. -/
theorem constWF_chainAxiom (env : Env .anon) (T : KKey) (j : Nat) :
    Ix.Kernel.ConstWF env (chainAxiom T j) := by
  refine Ix.Kernel.structConstWF (c := chainAxiom T j)
    (by rfl) (by show Expr.allLevelParamsDefined [0] (.sort (.succ (.param 0))) = true; decide)
    (by rfl) (by rfl)
    (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ h => nomatch h)

/-- `StoreInv` across cons-ing a fresh `chainAxiom T j`. -/
theorem storeInv_cons_chainAxiom {env : Env .anon} {T : KKey} {j : Nat}
    (hS : Ix.Kernel.Open.StoreInv env)
    (hfresh : env.find? (Ix.Kernel.projChainKey T j) = none) :
    Ix.Kernel.Open.StoreInv ⟨chainAxiom T j :: env.consts⟩ :=
  Ix.Kernel.Model.storeInv_consTyped hS hfresh
    ⟨by rfl, (by show Expr.allLevelParamsDefined [0] (.sort (.succ (.param 0))) = true; decide),
      by rfl, by rfl⟩
    (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ h => nomatch h)

/-- `StoreArR` across cons-ing a fresh `chainAxiom T j`. -/
theorem storeArR_cons_chainAxiom {env : Env .anon} {T : KKey} {j : Nat}
    (hAr : Ix.Kernel.Model.StoreArR env)
    (hfresh : env.find? (Ix.Kernel.projChainKey T j) = none) :
    Ix.Kernel.Model.StoreArR ⟨chainAxiom T j :: env.consts⟩ :=
  Ix.Kernel.Model.storeArR_cons (ci := chainAxiom T j) hAr hfresh
    (Ix.Kernel.Model.ConstArR.of_axiom (cv := ⟨Ix.Kernel.projChainKey T j, [0], .sort (.succ (.param 0))⟩) ⟨rfl, rfl⟩)
    (fun ⟨_, _, _, h⟩ _ => nomatch h)

/-- **One chain-axiom model step**: installs `chainAxiom T j` with leaf `A_chain`, extending the
model (`ModelExt`) and preserving `EtaFamiliesClosed`. -/
theorem chainAxiom_step {V : Type u} [SetTheory V] {env : Env .anon} {T : KKey} {j : Nat}
    (mp : EnvModelM V .verified env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (hfresh : env.find? (Ix.Kernel.projChainKey T j) = none)
    (A_chain : (LevelParam → Nat) → AnnotTerm)
    (hAclosed : ∀ ψ k, (A_chain ψ).liftN 1 k = A_chain ψ)
    (hAparams : ∀ ψ₁ ψ₂, ψ₁ 0 = ψ₂ 0 → A_chain ψ₁ = A_chain ψ₂)
    (hAok : ∀ ψ ρ, WellDenotedV V ρ (A_chain ψ))
    (hAmem : ∀ ψ ρ, interp V ρ (A_chain ψ) ∈ˢ (univ (ψ 0 + 1) : V)) :
    Ix.Kernel.EtaFamiliesClosed ⟨chainAxiom T j :: env.consts⟩ ∧
    ∃ mp' : EnvModelM V .verified ⟨chainAxiom T j :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval (Ix.Kernel.projChainKey T j) A_chain ∧
      ModelExt mp mp' := by
  have hwf' : Ix.Kernel.EnvWF ⟨chainAxiom T j :: env.consts⟩ :=
    Ix.Kernel.EnvWF.cons mp.base2.wf (constWF_chainAxiom _ T j)
  have hnres : Ix.Kernel.reservedBasisNames.contains (chainAxiom T j).name = false :=
    projChainKey_not_reserved T j
  have hntc : ConsCrossEnv env (chainAxiom T j) :=
    ConsCrossEnv.ofNtc (fun _ h => nomatch h)
  have hh : ConsHead env (chainAxiom T j) A_chain :=
    { wf := hwf'
      vclosed := fun ψ => bvarsBelow_of_liftN_eq (A_chain ψ) 0 (fun k _ => hAclosed ψ k)
      pin := fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h)
      projTower := hntc
      projTowerHead := fun _ h => nomatch h
      ctorsHead := fun _ _ _ _ h => nomatch h }
  have hreads : ∀ ψ : LevelParam → Nat,
      denoteMeta (acvalWith mp.base2.acval (Ix.Kernel.projChainKey T j) A_chain)
        ⟨chainAxiom T j :: env.consts⟩ ψ 0 (chainAxiom T j).toConstantVal.type =
      some (.sort (ψ 0 + 1)) := by
    intro ψ
    show denoteMeta _ _ ψ 0 (.sort (.succ (.param 0))) = _
    rw [denoteMeta_sort]
    rfl
  obtain ⟨mp', hac'⟩ := Ix.Kernel.Model.declStep_preserves_of_ind_cons mp
    (c₀ := chainAxiom T j) (A := A_chain) hfresh hnres
    (fun _ _ _ h => nomatch h) hh hAclosed
    (fun ψ₁ ψ₂ h0 => hAparams ψ₁ ψ₂ (h0 0 List.mem_cons_self))
    (fun ψ ρ => (hAok ψ ρ).1) (fun ψ ρ => (hAok ψ ρ).2)
    (fun ψ => ⟨.sort (ψ 0 + 1), hreads ψ⟩)
    (fun ψ ta hta ρ => by
      obtain rfl := Option.some.inj ((hreads ψ).symm.trans hta)
      exact ⟨by rw [WellDenoted_sort]; trivial, by rw [AnnotValid_sort]; trivial⟩)
    (fun ψ ta hta ρ => by
      obtain rfl := Option.some.inj ((hreads ψ).symm.trans hta)
      simpa [interp_sort] using hAmem ψ ρ)
    (fun m₂ hac => capsOk_cons_fresh mp mp.caps_ok (c₀ := chainAxiom T j) hfresh hntc
      (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) m₂ hac)
    (fun m₂ hac φ => recRules_cons_fresh mp (c₀ := chainAxiom T j) hfresh hntc
      (fun _ _ _ _ h => nomatch h) m₂ hac φ)
    (fun _ h => nomatch h)
  refine ⟨Ix.Kernel.EtaFamiliesClosed.cons_nonind hE hfresh (fun _ _ h => nomatch h),
    mp', hac', ModelExt.plain ModelExt.refl hac' hfresh⟩

/-! ## Section 3: `TowerEntryLaw` for a modeled structure projection table (`off = 2`) -/

private theorem denoteMetaSpine_projArgsD_chain
    {env : Env .anon} {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {T : KKey} {tbl : ProjTable .anon} {nP : Nat}
    (hoff : tbl.off = 2)
    (hfindTbl : env.find? (Ix.Kernel.projTableName T) = some (.projInfo tbl))
    (hsn : tbl.structName = T)
    (hchain : ∀ j, j < tbl.numFields → (env.find? (Ix.Kernel.projChainKey T j)).isSome = true)
    (φ : LevelParam → Nat) :
    ∀ (i : Nat), i ≤ tbl.numFields →
      DenoteMetaSpine acval env φ (nP + 1) (Ix.Kernel.projArgsD T i nP)
        ((List.range i).map fun j =>
          AnnotTerm.chain (fun n => acval (Ix.Kernel.projChainKey T j) (fun _ => n)) (.bvar 0)) := by
  intro i hi
  have hgo : ∀ (xs : List Nat), (∀ j ∈ xs, j < tbl.numFields) →
      DenoteMetaSpine acval env φ (nP + 1)
        (xs.map fun j => Expr.proj T j (Ix.Kernel.tfvD nP))
        (xs.map fun j =>
          AnnotTerm.chain (fun n => acval (Ix.Kernel.projChainKey T j) (fun _ => n)) (.bvar 0)) := by
    intro xs hxs
    induction xs with
    | nil => exact .nil
    | cons j xs ih =>
      refine .cons ?_ (ih fun j' hj' => hxs j' (List.mem_cons_of_mem _ hj'))
      have hj : j < tbl.numFields := hxs j List.mem_cons_self
      have hfp : env.findProj? T j = some (tbl.entry j) := by
        rw [← hsn]
        exact Ix.Kernel.Env.findProj?_of_table (by rw [hsn]; exact hfindTbl) hj
      have hch := hchain j hj
      simp only [denoteMeta, Ix.Kernel.tfvD, Nat.add_sub_cancel, Nat.sub_self, hfp,
        Ix.Kernel.Semantics.projNodeAV?, ProjTable.entry, hoff,
        show ¬ (2 ≤ 1) by omega, ↓reduceIte, hch]
      rfl
  exact hgo (List.range i) fun j hj => by have := List.mem_range.mp hj; omega

private theorem denoteMetaSpine_projAppsD
    {env : Env .anon} {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {nP bnl : Nat} {projKeyAt : Nat → KKey}
    (hfind : ∀ j, j < bnl → True)
    (hproj : ∀ j, j < nP + bnl → True)
    (φ : LevelParam → Nat) :
    ∀ (k : Nat)
      (hP : ∀ j, j < k → ∃ cv v hint,
        env.find? (projKeyAt j) = some (.defnInfo cv v hint) ∧
        cv.levelParams.length = bnl),
      DenoteMetaSpine acval env φ (nP + 1) (projAppsD nP bnl projKeyAt k)
        ((List.range k).map fun j =>
          AnnotTerm.mkAppN
            (acval (projKeyAt j) (Level.substFn φ (Ix.Kernel.Verify.levelParamsAt env (projKeyAt j))
              ((List.range bnl).map .param)))
            (entryParamBvars nP ++ [.bvar 0])) := by
  intro k hP
  have hmk : ∀ (f : KExpr) (fa : AnnotTerm) (args : List KExpr) (va : List AnnotTerm),
      denoteMeta acval env φ (nP + 1) f = some fa →
      DenoteMetaSpine acval env φ (nP + 1) args va →
      denoteMeta acval env φ (nP + 1) (Expr.mkAppN f args) = some (AnnotTerm.mkAppN fa va) := by
    intro f fa args
    induction args generalizing f fa with
    | nil =>
      intro va hf hsp
      cases hsp
      exact hf
    | cons a as ih =>
      intro va hf hsp
      cases hsp with
      | cons ha hsp' =>
        simp only [Expr.mkAppN, AnnotTerm.mkAppN]
        exact ih (.app f a) (.app fa _) _ (by rw [denoteMeta, hf, ha]; rfl) hsp'
  have hfvs : DenoteMetaSpine acval env φ (nP + 1) (Ix.Kernel.fvsD nP ++ [Ix.Kernel.tfvD nP])
      (entryParamBvars nP ++ [.bvar 0]) := by
    refine DenoteMetaSpine.append (denoteMetaSpine_entryParams (nP := nP) ?_ (Ix.Kernel.fvsD_length nP))
      (.cons (by simp [denoteMeta, Ix.Kernel.tfvD]) .nil)
    intro m x hx
    have hm : m < nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rwa [Ix.Kernel.fvsD_length] at this
    rw [Ix.Kernel.fvsD_getElem? nP m hm] at hx
    exact ⟨.sort .zero, (Option.some.inj hx).symm⟩
  have hgo : ∀ (xs : List Nat), (∀ j ∈ xs, j < k) →
      DenoteMetaSpine acval env φ (nP + 1)
        (xs.map fun j => Expr.mkAppN (.const (projKeyAt j) ((List.range bnl).map .param))
          (Ix.Kernel.fvsD nP ++ [Ix.Kernel.tfvD nP]))
        (xs.map fun j =>
          AnnotTerm.mkAppN
            (acval (projKeyAt j) (Level.substFn φ (Ix.Kernel.Verify.levelParamsAt env (projKeyAt j))
              ((List.range bnl).map .param)))
            (entryParamBvars nP ++ [.bvar 0])) := by
    intro xs hxs
    induction xs with
    | nil => exact .nil
    | cons j xs ih =>
      refine .cons ?_ (ih fun j' hj' => hxs j' (List.mem_cons_of_mem _ hj'))
      obtain ⟨cv, v, hint, hfj, hlenj⟩ := hP j (hxs j List.mem_cons_self)
      refine hmk _ _ _ _ ?_ hfvs
      simp only [denoteMeta, hfj, ConstantInfo.toConstantVal, List.length_map, List.length_range,
        hlenj, ↓reduceIte, Ix.Kernel.Verify.levelParamsAt]
  exact hgo (List.range k) fun j hj => List.mem_range.mp hj

private theorem origVal_eq_substFn_range (φ : LevelParam → Nat) (lps : List LevelParam)
    (hlen : lps.length = bnl) (_hperm : lps.Perm (List.range bnl)) :
    ∀ p ∈ lps,
      origVal lps φ p = Level.substFn φ lps ((List.range bnl).map .param) p := by
  intro p _
  unfold origVal Core.posLevels
  rw [hlen]

private theorem map_interp_entryParamBvars {V : Type u} [SetTheory V]
    (vs_v : List V) (x_v : V) (ρ : Nat → V) :
    (entryParamBvars vs_v.length).map (interp V (consList (vs_v ++ [x_v]) ρ)) = vs_v := by
  refine List.ext_getElem (by simp [entryParamBvars]) fun k hk1 hk2 => ?_
  simp only [List.getElem_map, entryParamBvars, List.getElem_range, interp_bvar]
  have hlt : vs_v.length - k < (vs_v ++ [x_v]).length := by simp
  rw [consList_getElem (vs_v ++ [x_v]) ρ (vs_v.length - k) hlt]
  simp only [List.length_append, List.length_singleton,
    show vs_v.length + 1 - 1 - (vs_v.length - k) = k by omega,
    List.getElem_append_left hk2]

private theorem stripPis_split_law {n1 n2 : Nat} {e rem : KExpr}
    {bs : List (KExpr × BinderMeta)}
    (hs : e.stripPis (n1 + n2) = some (bs, rem)) :
    ∃ bs1 rem1 bs2, e.stripPis n1 = some (bs1, rem1) ∧ rem1.stripPis n2 = some (bs2, rem) ∧
      bs = bs1 ++ bs2 := by
  induction n1 generalizing e bs with
  | zero =>
    simp only [Nat.zero_add] at hs
    exact ⟨[], e, bs, by simp [Expr.stripPis], hs, rfl⟩
  | succ n1 ih =>
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega] at hs
    cases e with
    | forallE ty b bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs₀, rem₀⟩, hsb, hp⟩ := hs
      obtain ⟨hbs, hrem⟩ := Prod.mk.inj hp
      subst hrem
      obtain ⟨bs1, rem1, bs2, h1, h2, hcat⟩ := ih hsb
      refine ⟨(ty, bm) :: bs1, rem1, bs2, by simp [Expr.stripPis, h1], h2, ?_⟩
      rw [← hbs, hcat]; rfl
    | _ => simp [Expr.stripPis] at hs

private theorem openDummiesP_forallE (m d c : Nat) (t b : KExpr) (bm : BinderMeta) :
    openDummiesP m d c (.forallE t b bm) =
      .forallE (openDummiesP m d c t) (openDummiesP m d (c + 1) b) bm := by
  induction m generalizing d c t b with
  | zero => rfl
  | succ m ih =>
    simp only [openDummiesP, Expr.instantiate1]
    rw [show c + m + 1 = c + 1 + m by omega]
    exact ih (d + 1) c _ _

private theorem openDummiesP_sort (m d c : Nat) (l : KLevel) :
    openDummiesP m d c (.sort l) = .sort l := by
  induction m generalizing d c with
  | zero => rfl
  | succ m ih => exact ih (d + 1) c

private theorem get_dom_denoteMeta_stripPis {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {env : Env .anon} {ψ : LevelParam → Nat} :
    ∀ {n : Nat} {e rem : KExpr} {bs : List (KExpr × BinderMeta)} {a : AnnotTerm}
      {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
      (hs : e.stripPis n = some (bs, rem)),
      denoteMeta acval env ψ 0 e = some a →
      a = mkPisAV ds b → (hlen : ds.length = n) →
      ∀ i (hi : i < n),
        denoteMeta acval env ψ i
          (openDummiesP i 0 0 (bs[i]'(by rw [stripPis_length_p hs]; exact hi)).1) =
          some (ds[i]'(by omega)).2.2
  | 0, _, _, _, _, _, _, _, _, _, _, i, hi => nomatch hi
  | n + 1, e, rem, bs, a, ds, b, hs, hden, hmk, hlen, i, hi => by
    obtain ⟨bs1, rem1, bs2, h1, h2, hcat⟩ := stripPis_split_law
      (show e.stripPis (i + (n + 1 - i)) = some (bs, rem) by
        rwa [show i + (n + 1 - i) = n + 1 by omega])
    have hsub : n + 1 - i = (n - i) + 1 := by omega
    rw [hsub] at h2
    cases hrm : rem1 with
    | forallE d_i b_i bm_i =>
      rw [hrm] at h2 h1
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h2
      obtain ⟨⟨bs2', _⟩, _, hp⟩ := h2
      injection hp with hbs2 _
      obtain ⟨ds1, remA1, hmk1, hds1_len, -, hremA1_den⟩ := denoteMeta_stripPis i 0 h1 hden
      simp only [Nat.zero_add] at hremA1_den
      rw [openDummiesP_forallE] at hremA1_den
      obtain ⟨dA_i, _, hdA_i, -, hremA1_eq⟩ := denoteMeta_forallE_some hremA1_den
      have hbi_eq : (bs[i]'(by rw [stripPis_length_p hs]; exact hi)).1 = d_i := by
        have hlen1 : bs1.length = i := stripPis_length_p h1
        simp only [hcat, ← hbs2, List.getElem_append_right (by omega : bs1.length ≤ i), hlen1,
          Nat.sub_self, List.getElem_cons_zero]
      rw [hbi_eq, hdA_i]
      congr 1
      have hds_split : ds = ds.take i ++ ds[i]'(by omega) :: ds.drop (i + 1) := by
        rw [← List.drop_eq_getElem_cons, List.take_append_drop]
      rw [hds_split, mkPisAV_append, mkPisAV] at hmk
      have hgo : ∀ (l1 l2 : List (Nat × Nat × AnnotTerm)) (b1 b2 : AnnotTerm),
          l1.length = l2.length → mkPisAV l1 b1 = mkPisAV l2 b2 → b1 = b2 := by
        intro l1; induction l1 with
        | nil => intro l2 _ _ hl h; cases l2 with | nil => exact h | cons _ _ => simp at hl
        | cons _ l1 ih =>
          intro l2 b1 b2 hl h; cases l2 with
          | nil => simp at hl
          | cons _ l2 =>
            simp only [mkPisAV] at h
            exact ih l2 b1 b2 (by simpa using hl) (AnnotTerm.pi.inj h).2.2.2
      have hb_eq := hgo ds1 (ds.take i) remA1 _ (by rw [hds1_len, List.length_take]; omega)
        (hmk1.symm.trans hmk)
      rw [← hremA1_eq] at hb_eq
      exact (AnnotTerm.pi.inj hb_eq).2.2.1
    | _ => rw [hrm] at h2; simp [Expr.stripPis] at h2

private theorem map_getElem_eq_law {α β : Type _} {f : α → Nat} {g : β → Nat}
    {l1 : List α} {l2 : List β} (h : l1.map f = l2.map g) (i : Nat)
    (hi1 : i < l1.length) (hi2 : i < l2.length) : f l1[i] = g l2[i] := by
  have hget := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
    Option.map_some, Option.some.injEq] at hget
  exact hget

set_option maxHeartbeats 1600000 in
/-- **`TowerEntryLaw` for a modeled structure projection table (`off = 2`).** -/
theorem modeled_towerEntryLaw {V : Type u} [SetTheory V]
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env₀ env₃ : Env .anon} {B : _root_.Address} {ms : Array Ixon.MutConst}
    {g : KKey → KKey} {bn : List KKey} {pos : Nat} {tyA_T tyA_C : KExpr}
    (mp₀ : EnvModelM V .verified env₀)
    (m₃ : EnvModel V env₃)
    (heqPin : env₀.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (mpf : MemberProjFacts t E env₀ B ms g pos tyA_T tyA_C)
    (tbl : ProjTable .anon)
    (cvT cvC : ConstantVal .anon) (capsT : Ix.Kernel.IndCaps .anon)
    (htbl_sn : tbl.structName = Core.keyOf t (Core.iprjAddr B pos))
    (htbl_ctor : tbl.ctor = Core.keyOf t (Core.cprjAddr B pos 0))
    (htbl_nP : tbl.numParams = mpf.ind.params.toNat)
    (htbl_nF : tbl.numFields = mpf.ct.fields.toNat)
    (htbl_lps : tbl.levelParams = List.range mpf.ind.lvls.toNat)
    (htbl_sort : tbl.structSort = mpf.structSort)
    (htbl_off : tbl.off = 2)
    (hbodies : Ix.Kernel.structProjBodies tbl.structName tbl.numParams tbl.numFields cvC.type =
      some tbl.bodies)
    (hfindT₃ : env₃.find? tbl.structName = some (.indInfo cvT capsT))
    (hcapsT : capsT.eta = false)
    (hcvT_lps : cvT.levelParams = List.range mpf.ind.lvls.toNat)
    (hcvT_ty : cvT.type = tyA_T)
    (hfindC₃ : env₃.find? tbl.ctor = some (.ctorInfo cvC tbl.numParams tbl.numFields))
    (hcvC_lps : cvC.levelParams = List.range mpf.ind.lvls.toNat)
    (hcvC_ty : cvC.type = tyA_C)
    (hfindTbl₃ : env₃.find? (Ix.Kernel.projTableName tbl.structName) = some (.projInfo tbl))
    (hchain₃ : ∀ j, j < tbl.numFields →
      (env₃.find? (Ix.Kernel.projChainKey tbl.structName j)).isSome = true)
    (hC_mem : ConstantInfo.ctorInfo cvC tbl.numParams tbl.numFields ∈ env₃.consts)
    (hC_def : tyA_C.allLevelParamsDefined (List.range mpf.ind.lvls.toNat) = true)
    (hT_def : tyA_T.allLevelParamsDefined (List.range mpf.ind.lvls.toNat) = true)
    (hT_pw : ∀ bm ∈ mpf.bsT, bm.2.pw = .never)
    (hC_ren_eq : Decl.renameAll g (Core.posOf (List.range mpf.ct.lvls.toNat) tyA_C) =
      tyA_C.renameConsts g)
    -- Agreement between `m₃` and `mp₀` on `cvC.type`, `T`, `C`, and `projChainKey T j`
    (hC_denote : ∀ ψ,
      denoteMeta m₃.acval env₃ ψ 0 cvC.type =
        denoteMeta mp₀.base2.acval env₀ ψ 0 (tyA_C.renameConsts g))
    (hC_reads : ∀ ψ, ∃ TCa,
      denoteMeta m₃.acval env₃ ψ 0 cvC.type = some TCa ∧
      (∀ ρ, WellDenotedV V ρ TCa) ∧
      (∀ ρ, interp V ρ (m₃.acval tbl.ctor ψ) ∈ˢ interp V ρ TCa))
    (hTM_find : ∃ cvTM mvalTM hintTM,
      env₀.find? (g tbl.structName) = some (.defnInfo cvTM mvalTM hintTM) ∧
      cvTM.levelParams.length = mpf.ind.lvls.toNat ∧
      cvTM.levelParams.Perm (List.range mpf.ind.lvls.toNat) ∧
      ExprSemEq (Core.posOf cvTM.levelParams cvTM.type) (Core.posOf (List.range mpf.ind.lvls.toNat) tyA_T) ∧
      ∀ ψ, m₃.acval tbl.structName ψ =
        mp₀.base2.acval (g tbl.structName) (origVal cvTM.levelParams ψ))
    (hCM_find : ∃ cvCM mvalCM hintCM,
      env₀.find? (g tbl.ctor) = some (.defnInfo cvCM mvalCM hintCM) ∧
      cvCM.levelParams.length = mpf.ind.lvls.toNat ∧
      cvCM.levelParams.Perm (List.range mpf.ind.lvls.toNat) ∧
      ∀ ψ, m₃.acval tbl.ctor ψ =
        mp₀.base2.acval (g tbl.ctor) (origVal cvCM.levelParams ψ))
    -- Chain coherence at every field `j < nF`
    (hA_ok : ∀ j, j < tbl.numFields → ∀ ψ ρ,
      WellDenotedV V ρ (m₃.acval (Ix.Kernel.projChainKey tbl.structName j) ψ))
    (hA_coh : ∀ j (hj : j < tbl.numFields),
      ∀ (fdom frest rawDom : KExpr) (fbm : BinderMeta)
        (bsRaw : List (KExpr × BinderMeta)) (remRaw : KExpr)
        (fp : FieldProjFacts t E env₀ (g tbl.structName) (g tbl.ctor)
          (Core.posOf (List.range mpf.ind.lvls.toNat) tyA_T)
          (Decl.renameAll g (Core.posOf (List.range mpf.ct.lvls.toNat) tyA_C))
          tbl.numParams mpf.ind.lvls.toNat tbl.numFields j fdom rawDom),
        fp.projKey = mpf.projKeyAt j →
        ∀ (ψ_P : LevelParam → Nat) (ρ₀ : Nat → V) (vs_v : List V) (x_v : V),
          vs_v.length = tbl.numParams →
          (∀ cvTM mvalTM hintTM,
            env₀.find? (g tbl.structName) = some (.defnInfo cvTM mvalTM hintTM) →
            AppChainOk (interp V ρ₀ (mp₀.base2.acval (g tbl.structName) (origVal cvTM.levelParams ψ_P))) vs_v ∧
            x_v ∈ˢ vs_v.foldl SetTheory.app
              (interp V ρ₀ (mp₀.base2.acval (g tbl.structName) (origVal cvTM.levelParams ψ_P)))) →
          Ix.Kernel.chainApp
              (fun n => interp V ρ₀ (m₃.acval (Ix.Kernel.projChainKey tbl.structName j) (fun _ => n)))
              x_v =
            (vs_v ++ [x_v]).foldl SetTheory.app
              (interp V ρ₀ (mp₀.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∧
          ∀ rdomA,
            denoteMeta mp₀.base2.acval env₀ ψ_P (tbl.numParams + 1)
              (openDummiesP (tbl.numParams + 1) 0 0 fp.rdom) = some rdomA →
            (vs_v ++ [x_v]).foldl SetTheory.app
              (interp V ρ₀ (mp₀.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∈ˢ
              interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA)
    (φ : LevelParam → Nat) (i : Nat) (hi : i < tbl.numFields) :
    TowerEntryLaw m₃ φ tbl.structName i (tbl.entry i) := by
  cases tbl with
  | mk sn ctor nP nF lps sSort bodies guards off =>
  dsimp only at *
  subst htbl_sn htbl_ctor htbl_nP htbl_nF htbl_lps htbl_sort htbl_off
  let T := Core.keyOf t (Core.iprjAddr B pos)
  let C := Core.keyOf t (Core.cprjAddr B pos 0)
  let nP := mpf.ind.params.toNat
  let nF := mpf.ct.fields.toNat
  let bnl := mpf.ind.lvls.toNat
  let ps := List.range bnl
  let tbl : ProjTable .anon := ⟨T, ps, nP, C, nF, mpf.structSort, bodies, guards, 2⟩
  obtain ⟨cvTM, mvalTM, hintTM, hfindTM, hTM_lvls, hTM_perm, hTM_ty, hacT_eq⟩ := hTM_find
  obtain ⟨cvCM, mvalCM, hintCM, hfindCM, hCM_lvls, hCM_perm, hacC_eq⟩ := hCM_find
  have hwfC := m₃.wf _ hC_mem
  have hCf : cvC.type.hasFvar = false := hwfC.1
  have hCb : cvC.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hposC_eq : Core.posOf (List.range mpf.ct.lvls.toNat) tyA_C = tyA_C := by
    rw [mpf.hcnl]
    exact posOf_range_eq_prep bnl tyA_C
  have hposT_eq : Core.posOf ps tyA_T = tyA_T := posOf_range_eq_prep bnl tyA_T
  have hstripC_tyA : tyA_C.stripPis (nP + nF) = some (mpf.bsC, mpf.cret) := by
    have h1 := mpf.hC_ret
    rwa [hposC_eq] at h1
  have hstripC : cvC.type.stripPis (nP + nF) = some (mpf.bsC, mpf.cret) := by
    rw [hcvC_ty]; exact hstripC_tyA
  have hstripC_ren : (tyA_C.renameConsts g).stripPis (nP + nF) =
      some (mpf.bsC.map (fun p => (p.1.renameConsts g, p.2)), mpf.cret.renameConsts g) :=
    stripPis_renameConsts g (nP + nF) hstripC_tyA
  have hO5 : TowerO5 (tbl.entry i) := by
    intro _ ψ h0
    have hpos : 0 < Level.eval ψ mpf.structSort := eval_pos_of_isNeverZero mpf.hT_sort_nz ψ
    simp only [ProjTable.entry, tbl] at h0
    omega
  refine ⟨rfl, rfl, hi, ⟨cvT, capsT, hfindT₃, hcvT_lps, fun he => by
      rw [hcapsT] at he; exact nomatch he⟩, hO5, cvC, hfindC₃, hcvC_lps, ?_, ?_⟩
  · -- Per-instantiation laws (A) and (B)
    intro us hus
    let ψ := Level.substFn φ ps us
    -- Read `cvC.type` at `ψ` in `m₃` (and in `mp₀` on `tyA_C.renameConsts g`)
    obtain ⟨TCa, hTCa_m₃, hTCa_wd_all, hTCa_mem_all⟩ := hC_reads ψ
    have hTCa_mp₀ : denoteMeta mp₀.base2.acval env₀ ψ 0 (tyA_C.renameConsts g) = some TCa := by
      rw [← hC_denote ψ]; exact hTCa_m₃
    have hTCa_ilp : denoteMeta m₃.acval env₃ φ 0 (cvC.type.instantiateLevelParams cvC.levelParams us) =
        some TCa := by
      rw [denotePInstLevels m₃ φ cvC.levelParams us 0 cvC.type, hcvC_lps]
      exact hTCa_m₃
    -- Decompose `TCa = mkPisAV dsC bodyC`
    obtain ⟨dsC, bodyC, hTCa_mk, hdsC_len, -, hbodyC_den⟩ :=
      denoteMeta_stripPis (nP + nF) 0 hstripC hTCa_m₃
    -- Helper: `mp₀` setup from `AppChainOk (acval T ψ) vs_v` + `x_v ∈ˢ ...`
    have hproj_setup : ∀ (ρ : Nat → V) (vs_v : List V) (x_v : V),
        vs_v.length = nP →
        AppChainOk (interp V ρ (m₃.acval T ψ)) vs_v →
        x_v ∈ˢ vs_v.foldl SetTheory.app (interp V ρ (m₃.acval T ψ)) →
        (∀ cvTM' mvalTM' hintTM',
          env₀.find? (g T) = some (.defnInfo cvTM' mvalTM' hintTM') →
          AppChainOk (interp V ρ (mp₀.base2.acval (g T) (origVal cvTM'.levelParams ψ))) vs_v ∧
          x_v ∈ˢ vs_v.foldl SetTheory.app
            (interp V ρ (mp₀.base2.acval (g T) (origVal cvTM'.levelParams ψ)))) := by
      intro ρ vs_v x_v hvs_len hAppT hxT cvTM' mvalTM' hintTM' hfTM'
      have hcv_eq : cvTM' = cvTM :=
        (ConstantInfo.defnInfo.inj (Option.some.inj (hfTM'.symm.trans hfindTM))).1
      subst hcv_eq
      rw [← hacT_eq ψ]
      exact ⟨hAppT, hxT⟩
    -- Helper: for any field `j < nF`, `mpf.hfields j` yields `fp_j`, `AppChainOk`, and `WellDenotedV`
    -- of `rdomA` at `consList (vs_v ++ [x_v]) ρ`.
    have hproj_app_wd : ∀ (j : Nat) (hj : j < nF) (fdom_j frest_j rawDom_j : KExpr)
        (fbm_j : BinderMeta) (bsRaw_j : List (KExpr × BinderMeta)) (remRaw_j : KExpr)
        (fp_j : FieldProjFacts t E env₀ (g T) (g C)
          (Core.posOf ps tyA_T) (Decl.renameAll g (Core.posOf (List.range mpf.ct.lvls.toNat) tyA_C))
          nP bnl nF j fdom_j rawDom_j)
        (ρ : Nat → V) (vs_v : List V) (x_v : V),
        vs_v.length = nP →
        AppChainOk (interp V ρ (m₃.acval T ψ)) vs_v →
        x_v ∈ˢ vs_v.foldl SetTheory.app (interp V ρ (m₃.acval T ψ)) →
        AppChainOk
          (interp V ρ (mp₀.base2.acval fp_j.projKey (origVal fp_j.cvProj.levelParams ψ)))
          (vs_v ++ [x_v]) ∧
        ∀ rdomA,
          denoteMeta mp₀.base2.acval env₀ ψ (nP + 1) (openDummiesP (nP + 1) 0 0 fp_j.rdom) =
            some rdomA →
          WellDenotedV V (consList (vs_v ++ [x_v]) ρ) rdomA := by
      intro j hj fdom_j frest_j rawDom_j fbm_j bsRaw_j remRaw_j fp_j ρ vs_v x_v hvs_len hAppT hxT
      -- Strip `cvTM.type` to get `SpineFit` for `vs_v`
      have hmemTM := Ix.Kernel.Semantics.Env.find?_mem hfindTM
      obtain ⟨TTM_a, hTTM_a⟩ := mp₀.type_reads _ hmemTM (origVal cvTM.levelParams ψ)
      have hTTM_mem := mp₀.mem_type _ hmemTM (origVal cvTM.levelParams ψ) TTM_a hTTM_a ρ
      rw [Ix.Kernel.Semantics.Env.find?_name hfindTM] at hTTM_mem
      have hTTM_pos : denoteMeta mp₀.base2.acval env₀ ψ 0 (Core.posOf ps tyA_T) = some TTM_a := by
        rw [← denoteMeta_exprSemEq hTM_ty, posOf_denoteMeta]; exact hTTM_a
      rw [hposT_eq] at hTTM_pos
      obtain ⟨dsT, bodyT, hTTM_mk, hdsT_len, hdsT_bits, hbodyT_den⟩ :=
        denoteMeta_stripPis nP 0 mpf.hT_sort hTTM_pos
      simp only [Nat.zero_add] at hbodyT_den
      have hbodyT_eq : bodyT = .sort (mpf.structSort.eval ψ) := by
        rw [openDummiesP_sort, denoteMeta_sort] at hbodyT_den
        exact (Option.some.inj hbodyT_den).symm
      have hpos_dsT : ∀ d ∈ dsT, d.2.1 ≠ 0 := by
        intro d hd
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
        have hbi := map_getElem_eq_law hdsT_bits k hk (by rw [stripPis_length_p mpf.hT_sort]; omega)
        have hnev := hT_pw (mpf.bsT[k]'(by rw [stripPis_length_p mpf.hT_sort]; omega))
          (List.getElem_mem _)
        rw [hbi, hnev]; simp [pwBit]
      rw [hTTM_mk, hbodyT_eq] at hTTM_mem
      have hAppTM : AppChainOk
          (interp V ρ (mp₀.base2.acval (g T) (origVal cvTM.levelParams ψ))) vs_v := by
        rw [← hacT_eq ψ]; exact hAppT
      have hsp_T : SpineFit ρ (dsT.map (·.2.2)) vs_v :=
        spineFit_of_mkPisAV_appChainOk_pos dsT (.sort (mpf.structSort.eval ψ)) vs_v ρ hpos_dsT
          (by rw [hdsT_len, hvs_len]) hTTM_mem hAppTM
      -- Strip `fp_j.cvProj.type`
      have hmemP := Ix.Kernel.Semantics.Env.find?_mem fp_j.hfindProj
      obtain ⟨TPa, hTPa⟩ := mp₀.type_reads _ hmemP (origVal fp_j.cvProj.levelParams ψ)
      have hTPa_mem := mp₀.mem_type _ hmemP (origVal fp_j.cvProj.levelParams ψ) TPa hTPa ρ
      rw [Ix.Kernel.Semantics.Env.find?_name fp_j.hfindProj] at hTPa_mem
      have hTPa_wd := mp₀.type_wellDenotedV _ hmemP (origVal fp_j.cvProj.levelParams ψ) TPa hTPa ρ
      have hTPa_pos : denoteMeta mp₀.base2.acval env₀ ψ 0
          (Core.posOf fp_j.cvProj.levelParams fp_j.cvProj.type) = some TPa := by
        rw [posOf_denoteMeta]; exact hTPa
      obtain ⟨dsP, remP, hTPa_mk, hdsP_len, -, hremP_den⟩ :=
        denoteMeta_stripPis nP 0 fp_j.hProj_strip hTPa_pos
      simp only [Nat.zero_add] at hremP_den
      rw [openDummiesP_forallE] at hremP_den
      obtain ⟨sdomA, rdomA₀, hsdomA_den, hrdomA₀_den, hremP_eq⟩ := denoteMeta_forallE_some hremP_den
      have hrdom_open_eq : openDummiesP (nP + 1) 0 0 fp_j.rdom =
          (openDummiesP nP 0 1 fp_j.rdom).instantiate1 (.fvar nP (.sort .zero)) 0 := by
        simpa [openDummiesP, Nat.zero_add] using openDummiesP_add nP 1 0 fp_j.rdom
      rw [← hrdom_open_eq] at hrdomA₀_den
      -- Show `dsP.map (·.2.2) = dsT.map (·.2.2)`
      have hdsPT_eq : dsP.map (·.2.2) = dsT.map (·.2.2) := by
        have hT_st : tyA_T.stripPis nP = some (fp_j.tbsP, fp_j.tremP) := by
          simpa [hposT_eq] using fp_j.hT_strip
        have hlen_tb : fp_j.tbsP = mpf.bsT :=
          (Prod.mk.inj (Option.some.inj (hT_st.symm.trans mpf.hT_sort))).1
        refine List.ext_getElem (by simp [hdsP_len, hdsT_len]) fun k hk1 hk2 => ?_
        simp only [List.getElem_map]
        have hk : k < nP := by simp [hdsP_len] at hk1; exact hk1
        have h1 := get_dom_denoteMeta_stripPis fp_j.hProj_strip hTPa_pos hTPa_mk hdsP_len k hk
        have h2 := get_dom_denoteMeta_stripPis mpf.hT_sort hTTM_pos hTTM_mk hdsT_len k hk
        have heq_k : ExprSemEq
            (fp_j.pbsP[k]'(by rw [stripPis_length_p fp_j.hProj_strip]; exact hk)).1
            (mpf.bsT[k]'(by rw [stripPis_length_p mpf.hT_sort]; exact hk)).1 := by
          have h := forall₂_getElem fp_j.hProj_pdoms k
            (by rw [List.length_map, stripPis_length_p fp_j.hProj_strip]; exact hk)
            (by rw [List.length_map, hlen_tb, stripPis_length_p mpf.hT_sort]; exact hk)
          simpa [hlen_tb] using h
        have hsame := denoteMeta_exprSemEq (acval := mp₀.base2.acval) (env := env₀) (φ := ψ)
          (d := k) (exprSemEq_openDummiesP heq_k k 0 0)
        rw [h1, h2] at hsame
        exact Option.some.inj hsame
      -- Show `interp V (consList vs_v ρ) sdomA = vs_v.foldl app (acval T ψ)`
      have hsdom_val : interp V (consList vs_v ρ) sdomA =
          vs_v.foldl SetTheory.app (interp V ρ (m₃.acval T ψ)) := by
        have hsame := denoteMeta_exprSemEq (acval := mp₀.base2.acval) (env := env₀) (φ := ψ)
          (d := nP) (exprSemEq_openDummiesP fp_j.hProj_sdom nP 0 0)
        rw [hsdomA_den, openDummiesP_mkAppN, openDummiesP_const] at hsame
        have hargs_open :
            ((List.range nP).map fun m => Expr.bvar (nP - 1 - m)).map (openDummiesP nP 0 0) =
              (List.range nP).map fun m => Expr.fvar m (.sort .zero) := by
          rw [List.map_map]
          refine List.map_congr_left fun m hm => ?_
          have hm' := List.mem_range.mp hm
          have h := openDummiesP_bvar_lt nP 0 0 (nP - 1 - m) (Nat.zero_le _) (by omega)
          simpa [show nP - 1 - (nP - 1 - m) = m by omega] using h
        rw [hargs_open] at hsame
        obtain ⟨ftmA, sargsA, hsargsA_len, hftmA, hsargsA_at, hsdomA_eq⟩ :=
          denoteMeta_mkAppN_some hsame.symm
        have hftmA_eq : ftmA = mp₀.base2.acval (g T) (origVal cvTM.levelParams ψ) := by
          simp only [denoteMeta, T] at hftmA
          rw [hfindTM] at hftmA
          simp only [ConstantInfo.toConstantVal, List.length_map, List.length_range, hTM_lvls, bnl,
            ↓reduceIte] at hftmA
          have h1 := Option.some.inj hftmA
          rw [← h1]
          exact mp₀.base2.acval_params (g T) _ hfindTM _ _
            (fun p hp => (origVal_eq_substFn_range ψ cvTM.levelParams hTM_lvls hTM_perm p hp).symm)
        have hsargsV_eq : sargsA.map (interp V (consList vs_v ρ)) = vs_v := by
          have hlen_s : sargsA.length = nP := by rw [hsargsA_len]; simp
          refine List.ext_getElem (by rw [List.length_map, hlen_s, hvs_len]) fun k hk1 hk2 => ?_
          have hk : k < nP := by rw [← hvs_len]; exact hk2
          have hdk := hsargsA_at k (by rw [List.length_map, List.length_range]; exact hk)
          simp only [List.getElem_map, List.getElem_range, denoteMeta] at hdk
          have hsk : sargsA[k]'(by omega) = .bvar (nP - 1 - k) := (Option.some.inj hdk).symm
          rw [List.getElem_map, hsk, interp_bvar,
            consList_getElem vs_v ρ (nP - 1 - k) (by omega)]
          congr 1; omega
        rw [hsdomA_eq, hftmA_eq, interp_mkAppN_foldl, hsargsV_eq, hacT_eq ψ,
          closed_interp_env (mp₀.base2.acval_closed (g T) _) _ ρ]
      have hTPa_all : TPa = mkPisAV (dsP ++ [(0, pwBit ψ fp_j.sbm.pw, sdomA)]) rdomA₀ := by
        simp only [hTPa_mk, mkPisAV_append, mkPisAV, ← hremP_eq]
      have hsp_all : SpineFit ρ
          ((dsP ++ [(0, pwBit ψ fp_j.sbm.pw, sdomA)]).map fun d : Nat × Nat × AnnotTerm => d.2.2)
          (vs_v ++ [x_v]) := by
        rw [List.map_append]
        refine (spineFit_append_iff (by simp [hdsP_len, hvs_len])).mpr ⟨?_, ?_⟩
        · rw [hdsPT_eq]; exact hsp_T
        · simp only [List.map_cons, List.map_nil, SpineFit]
          exact ⟨by rwa [hsdom_val], trivial⟩
      rw [hTPa_all] at hTPa_mem hTPa_wd
      obtain ⟨hApp_P, -, hval_r0⟩ := appChainOk_and_mem_of_mkPisAV_spineFit
        (dsP ++ [(0, pwBit ψ fp_j.sbm.pw, sdomA)]) rdomA₀ (vs_v ++ [x_v]) ρ
        (by simp [hdsP_len, hvs_len]) hTPa_wd.2 hTPa_mem hsp_all
      -- Also extract `WellDenoted V (consList (vs_v ++ [x_v]) ρ) rdomA₀` from `hTPa_wd.1`!
      have hwd_r0 : WellDenoted V (consList (vs_v ++ [x_v]) ρ) rdomA₀ := by
        have hgo : ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) (as : List V) (σ : Nat → V),
            as.length = ds.length →
            WellDenoted V σ (mkPisAV ds b) →
            SpineFit σ (ds.map (·.2.2)) as →
            WellDenoted V (consList as σ) b := by
          intro ds
          induction ds with
          | nil =>
            intro b as σ hl hwd _
            cases as with
            | nil => exact hwd
            | cons _ _ => simp at hl
          | cons d ds ih =>
            intro b as σ hl hwd hsp
            cases as with
            | nil => simp at hl
            | cons a as =>
              simp only [mkPisAV, WellDenoted_pi] at hwd
              simp only [List.map_cons, SpineFit] at hsp
              exact ih b as (cons a σ) (by simpa using hl) (hwd.2 a hsp.1) hsp.2
        exact hgo _ rdomA₀ (vs_v ++ [x_v]) ρ (by simp [hdsP_len, hvs_len]) hTPa_wd.1 hsp_all
      refine ⟨hApp_P, fun rdomA hrdomA => ?_⟩
      have heq : rdomA = rdomA₀ := Option.some.inj (hrdomA.symm.trans hrdomA₀_den)
      subst heq
      exact ⟨hwd_r0, hval_r0⟩
    constructor
    · -- **Clause (A): Typing law**
      -- 1. Open body `i` of `tbl.bodies` via `structProjBody_open`
      obtain ⟨cds, bodyB, mbB, hcf⟩ :=
        Ix.Kernel.structProjBody_open hbodies (by rw [hstripC]; rfl) hCb hi
      -- 2. Peel `TCa` along `fvsD nP ++ projArgsD T i nP` via `Rules.denoteMeta_instPisAt_peel`
      have hTCa_d : denoteMeta m₃.acval env₃ ψ (nP + 1) cvC.type = some TCa :=
        denoteMeta_depth_of_closed m₃.acval_closed hCf
          (fun k => denoteMeta_closed m₃.acval_erase m₃.cval_closed hCf hCb hTCa_m₃ 1 k)
          hTCa_m₃ (nP + 1)
      have hargs_chain : ∀ a ∈ Ix.Kernel.fvsD nP ++ Ix.Kernel.projArgsD T i nP,
          Expr.WScoped (nP + 1) a ∧ a.looseBVarsBounded 0 = true := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          have := List.mem_range.mp hk
          exact ⟨by simp only [Expr.WScoped, and_true]; omega, rfl⟩
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
          exact ⟨by simp only [Expr.WScoped, Ix.Kernel.tfvD, and_true]; omega, rfl⟩
      let chainArgsA : List AnnotTerm :=
        (List.range i).map fun j =>
          AnnotTerm.chain (fun n => m₃.acval (Ix.Kernel.projChainKey T j) (fun _ => n)) (.bvar 0)
      have hsp_chain : DenoteMetaSpine m₃.acval env₃ ψ (nP + 1)
          (Ix.Kernel.fvsD nP ++ Ix.Kernel.projArgsD T i nP) (entryParamBvars nP ++ chainArgsA) := by
        refine DenoteMetaSpine.append
          (denoteMetaSpine_entryParams (nP := nP) (fun k x hx => ?_) (Ix.Kernel.fvsD_length nP))
          (denoteMetaSpine_projArgsD_chain (tbl := tbl) rfl hfindTbl₃ rfl hchain₃ ψ i (Nat.le_of_lt hi))
        have hk : k < nP := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          rwa [Ix.Kernel.fvsD_length] at this
        rw [Ix.Kernel.fvsD_getElem? nP k hk] at hx
        exact ⟨.sort .zero, (Option.some.inj hx).symm⟩
      obtain ⟨restA, hrestA, hpeel_chain⟩ := Rules.denoteMeta_instPisAt_peel m₃.acval_closed
        (acval_inst_self m₃) _ hcf (Expr.WScoped.of_not_hasFvar hCf) hargs_chain hTCa_d hsp_chain
      obtain ⟨fdomA, baA, hfdomA, -, rfl⟩ := denoteMeta_forallE_inv hrestA
      -- 3. `projTele (nP + 1) (body.instantiateLevelParams ... us)` reads to `mkPisAV (replicate (nP + 1) ...) fdomA`
      have hTa_ψ : denoteMeta m₃.acval env₃ ψ 0
          (Ix.Kernel.projTele (nP + 1) (tbl.entry i).body) =
          some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) fdomA) :=
        denoteMeta_projTele_zero hfdomA
      have hTa_φ : denoteMeta m₃.acval env₃ φ 0
          (Ix.Kernel.projTele (nP + 1) ((tbl.entry i).body.instantiateLevelParams tbl.levelParams us)) =
          some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) fdomA) := by
        rw [← Ix.Kernel.projTele_instantiateLevelParams,
          denotePInstLevels m₃ φ tbl.levelParams us 0]
        exact hTa_ψ
      refine ⟨mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) fdomA, hTa_φ, ?_⟩
      intro _ ρ vs x rest hvs_len hTvs_wd hx_wd hx_mem hpeel_Ta
      -- Extract `rest = fdomA.instSeq (vs ++ [x]) nP`
      have hrest_eq : rest = Ix.Kernel.Model.AnnotTerm.instSeq (vs ++ [x]) nP fdomA := by
        have hlen_vx : (vs ++ [x]).length = nP + 1 := by simp [hvs_len, nP]
        have hpt := piTeleAV_mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) fdomA
        simp only [List.length_replicate] at hpt
        have hp := peelPis_of_piTeleAV (nP + 1) hpt hlen_vx
        rw [hpeel_Ta] at hp
        simpa using Option.some.inj hp
      obtain ⟨-, hvs_wd, hAppT⟩ := wellDenotedV_mkAppN_inv _ vs hTvs_wd
      have hvx_wd : ∀ w ∈ vs ++ [x], WellDenotedV V ρ w := fun w hw => by
        rcases List.mem_append.mp hw with hw | hw
        · exact hvs_wd w hw
        · rw [List.mem_singleton.mp hw]; exact hx_wd
      let vs_v := vs.map (interp V ρ)
      let x_v := interp V ρ x
      let ρ' := consList (vs_v ++ [x_v]) ρ
      have hvs_v_len : vs_v.length = nP := by simp [vs_v, hvs_len, nP]
      have hx_mem' : x_v ∈ˢ vs_v.foldl SetTheory.app (interp V ρ (m₃.acval T ψ)) := by
        simpa [vs_v, x_v, interp_mkAppN_foldl] using hx_mem
      -- 4. Compute `fdomA = Fi.instSeq (entryParamBvars nP ++ chainArgsA) (nP + i - 1)`
      have hsplitDs : dsC = dsC.take (nP + i) ++ dsC.drop (nP + i) :=
        (List.take_append_drop _ _).symm
      have hteleC : PiTeleAV (nP + i) TCa
          (((dsC.take (nP + i)).map (·.2.2)).reverse)
          (mkPisAV (dsC.drop (nP + i)) bodyC) := by
        rw [hTCa_mk]
        have h := piTeleAV_mkPisAV (dsC.take (nP + i)) (mkPisAV (dsC.drop (nP + i)) bodyC)
        rw [← mkPisAV_append, ← hsplitDs, List.length_take, hdsC_len,
          show min (nP + i) (nP + nF) = nP + i from by omega] at h
        exact h
      have hdropDs : dsC.drop (nP + i) = dsC.getD (nP + i) default :: dsC.drop (nP + i + 1) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]
        rfl
      let Fi : AnnotTerm := (dsC.getD (nP + i) default).2.2
      have hlen_ws1 : (entryParamBvars nP ++ chainArgsA).length = nP + i := by
        simp [entryParamBvars_length, chainArgsA]
      have hfdomA_inst : fdomA =
          Ix.Kernel.Model.AnnotTerm.instSeq (entryParamBvars nP ++ chainArgsA) (nP + i - 1) Fi := by
        have hp := peelPis_of_piTeleAV (nP + i) hteleC hlen_ws1
        rw [hpeel_chain, hdropDs, mkPisAV] at hp
        obtain ⟨B', hB'⟩ := instSeq_pi_dom (entryParamBvars nP ++ chainArgsA) (nP + i - 1)
          (dsC.getD (nP + i) default).1 (dsC.getD (nP + i) default).2.1 Fi
          (mkPisAV (dsC.drop (nP + i + 1)) bodyC)
        rw [hB'] at hp
        exact (AnnotTerm.pi.inj (Option.some.inj hp)).2.2.1
      -- 5. Now peel `TCa` along `entryParamBvars nP ++ projArgsA` using `mpf.hfields i hi`!
      obtain ⟨fdom_i, frest_i, rawDom_i, fbm_i, bsRaw_i, remRaw_i, htele_i, -, -, fp_i, hfp_i_key⟩ :=
        mpf.hfields i hi
      have htele_i' : (Expr.instPisAt (Ix.Kernel.fvsD nP ++ projAppsD nP bnl mpf.projKeyAt i)
          (tyA_C.renameConsts g)).map Prod.snd = some (.forallE fdom_i frest_i fbm_i) := by
        rw [← projFieldTeleAt_eq_instPisAt, ← hC_ren_eq]; exact htele_i
      obtain ⟨⟨cds_p, r_p⟩, hinst_p, hr_p⟩ := Option.map_eq_some_iff.mp htele_i'
      dsimp only at hr_p; subst hr_p
      have hC_ren_fvar : (tyA_C.renameConsts g).hasFvar = false := by
        have hgo : ∀ (e : KExpr), e.hasFvar = false → (e.renameConsts g).hasFvar = false := by
          intro e; induction e with
          | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
          | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
          | app _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
            intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
            simp [Expr.renameConsts, Expr.hasFvar, ih1 h.1, ih2 h.2]
          | letE _ _ _ _ ih1 ih2 ih3 =>
            intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
            simp [Expr.renameConsts, Expr.hasFvar, ih1 h.1.1, ih2 h.1.2, ih3 h.2]
          | proj _ _ _ ih1 => intro h; exact ih1 h
        rw [← hcvC_ty]; exact hgo cvC.type hCf
      have hC_ren_lbb : (tyA_C.renameConsts g).looseBVarsBounded 0 = true := by
        have hgo : ∀ (e : KExpr) (k : Nat),
            e.looseBVarsBounded k = true → (e.renameConsts g).looseBVarsBounded k = true := by
          intro e; induction e with
          | bvar _ | sort _ | const _ _ | lit _ => intro _ h; exact h
          | fvar _ _ _ => intro _ h; exact h
          | app _ _ ih1 ih2 =>
            intro k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
            simp [Expr.renameConsts, Expr.looseBVarsBounded, ih1 k h.1, ih2 k h.2]
          | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
            intro k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
            simp [Expr.renameConsts, Expr.looseBVarsBounded, ih1 k h.1, ih2 (k + 1) h.2]
          | letE _ _ _ _ ih1 ih2 ih3 =>
            intro k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
            simp [Expr.renameConsts, Expr.looseBVarsBounded, ih1 k h.1.1, ih2 k h.1.2, ih3 (k + 1) h.2]
          | proj _ _ _ ih1 => intro k h; exact ih1 k h
        rw [← hcvC_ty]; exact hgo cvC.type 0 hCb
      have hTCa_mp₀_d : denoteMeta mp₀.base2.acval env₀ ψ (nP + 1) (tyA_C.renameConsts g) =
          some TCa :=
        denoteMeta_depth_of_closed mp₀.base2.acval_closed hC_ren_fvar
          (fun k => denoteMeta_closed mp₀.base2.acval_erase mp₀.base2.cval_closed
            hC_ren_fvar hC_ren_lbb hTCa_mp₀ 1 k)
          hTCa_mp₀ (nP + 1)
      have hargs_proj : ∀ a ∈ Ix.Kernel.fvsD nP ++ projAppsD nP bnl mpf.projKeyAt i,
          Expr.WScoped (nP + 1) a ∧ a.looseBVarsBounded 0 = true := by
        have hmk_w : ∀ (f : KExpr) (xs : List KExpr),
            Expr.WScoped (nP + 1) f → f.looseBVarsBounded 0 = true →
            (∀ x ∈ xs, Expr.WScoped (nP + 1) x ∧ x.looseBVarsBounded 0 = true) →
            Expr.WScoped (nP + 1) (Expr.mkAppN f xs) ∧ (Expr.mkAppN f xs).looseBVarsBounded 0 = true := by
          intro f xs
          induction xs generalizing f with
          | nil => intro hf1 hf2 _; exact ⟨hf1, hf2⟩
          | cons x xs ih =>
            intro hf1 hf2 hxs
            have hx := hxs x List.mem_cons_self
            exact ih (.app f x) (by simp [Expr.WScoped, hf1, hx.1])
              (by simp [Expr.looseBVarsBounded, hf2, hx.2])
              (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          have := List.mem_range.mp hk
          exact ⟨by simp only [Expr.WScoped, and_true]; omega, rfl⟩
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
          refine hmk_w _ _ (by simp [Expr.WScoped]) rfl fun y hy => ?_
          rcases List.mem_append.mp hy with hy | hy
          · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
            have := List.mem_range.mp hk
            exact ⟨by simp only [Expr.WScoped, and_true]; omega, rfl⟩
          · rw [List.mem_singleton.mp hy]
            exact ⟨by simp only [Expr.WScoped, Ix.Kernel.tfvD, and_true]; omega, rfl⟩
      let projArgsA : List AnnotTerm :=
        (List.range i).map fun j =>
          AnnotTerm.mkAppN
            (mp₀.base2.acval (mpf.projKeyAt j)
              (Level.substFn ψ (Ix.Kernel.Verify.levelParamsAt env₀ (mpf.projKeyAt j))
                ((List.range bnl).map .param)))
            (entryParamBvars nP ++ [.bvar 0])
      have hsp_proj : DenoteMetaSpine mp₀.base2.acval env₀ ψ (nP + 1)
          (Ix.Kernel.fvsD nP ++ projAppsD nP bnl mpf.projKeyAt i)
          (entryParamBvars nP ++ projArgsA) := by
        refine DenoteMetaSpine.append
          (denoteMetaSpine_entryParams (nP := nP) (fun k x hx => ?_) (Ix.Kernel.fvsD_length nP))
          (denoteMetaSpine_projAppsD (fun _ _ => trivial) (fun _ _ => trivial) ψ i fun j hj => ?_)
        · have hk : k < nP := by
            have := (List.getElem?_eq_some_iff.mp hx).1
            rwa [Ix.Kernel.fvsD_length] at this
          rw [Ix.Kernel.fvsD_getElem? nP k hk] at hx
          exact ⟨.sort .zero, (Option.some.inj hx).symm⟩
        · obtain ⟨_, _, _, _, _, _, -, -, -, fp_j, hfp_j_key⟩ := mpf.hfields j (by omega)
          rw [← hfp_j_key]
          exact ⟨fp_j.cvProj, fp_j.projVal, fp_j.projHint, fp_j.hfindProj, fp_j.hProj_lvls⟩
      obtain ⟨restA_p, hrestA_p, hpeel_proj⟩ := Rules.denoteMeta_instPisAt_peel
        mp₀.base2.acval_closed (acval_inst_self mp₀.base2) _ hinst_p
        (Expr.WScoped.of_not_hasFvar hC_ren_fvar) hargs_proj hTCa_mp₀_d hsp_proj
      obtain ⟨fdomA_p, ba_p, hfdomA_p, -, rfl⟩ := denoteMeta_forallE_inv hrestA_p
      have hlen_ws2 : (entryParamBvars nP ++ projArgsA).length = nP + i := by
        simp [entryParamBvars_length, projArgsA]
      have hfdomA_p_inst : fdomA_p =
          Ix.Kernel.Model.AnnotTerm.instSeq (entryParamBvars nP ++ projArgsA) (nP + i - 1) Fi := by
        have hp := peelPis_of_piTeleAV (nP + i) hteleC hlen_ws2
        rw [hpeel_proj, hdropDs, mkPisAV] at hp
        obtain ⟨B', hB'⟩ := instSeq_pi_dom (entryParamBvars nP ++ projArgsA) (nP + i - 1)
          (dsC.getD (nP + i) default).1 (dsC.getD (nP + i) default).2.1 Fi
          (mkPisAV (dsC.drop (nP + i + 1)) bodyC)
        rw [hB'] at hp
        exact (AnnotTerm.pi.inj (Option.some.inj hp)).2.2.1
      -- 6. Show `rdomA = fdomA_p` literally via `fp_i.hProj_rdom` + `denoteMeta_exprSemEq`!
      have hrdom_eq : denoteMeta mp₀.base2.acval env₀ ψ (nP + 1)
          (openDummiesP (nP + 1) 0 0 fp_i.rdom) = some fdomA_p := by
        rw [denoteMeta_exprSemEq fp_i.hProj_rdom]
        exact hfdomA_p
      -- 7. Show `ws1` and `ws2` are both `WellDenotedV V ρ'` and have equal `interp V ρ'`!
      have hws1_wd : ∀ w ∈ entryParamBvars nP ++ chainArgsA, WellDenotedV V ρ' w := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw
          exact ⟨trivial, trivial⟩
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
          have hj' : j < nF := by have := List.mem_range.mp hj; omega
          exact ⟨by rw [WellDenoted_chain]; exact ⟨fun m => (hA_ok j hj' (fun _ => m) ρ').1, trivial⟩,
            by rw [AnnotValid_chain]; exact ⟨fun m => (hA_ok j hj' (fun _ => m) ρ').2, trivial⟩⟩
      have hws2_wd : ∀ w ∈ entryParamBvars nP ++ projArgsA, WellDenotedV V ρ' w := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw
          exact ⟨trivial, trivial⟩
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
          have hj' : j < nF := by have := List.mem_range.mp hj; omega
          obtain ⟨fdom_j, frest_j, rawDom_j, fbm_j, bsRaw_j, remRaw_j, -, -, -, fp_j, hfp_j_key⟩ :=
            mpf.hfields j hj'
          have hAppP_j := (hproj_app_wd j hj' fdom_j frest_j rawDom_j fbm_j bsRaw_j remRaw_j fp_j
            ρ vs_v x_v hvs_v_len hAppT hx_mem').1
          have hac_eq_j : mp₀.base2.acval (mpf.projKeyAt j)
              (Level.substFn ψ (Ix.Kernel.Verify.levelParamsAt env₀ (mpf.projKeyAt j))
                ((List.range bnl).map .param)) =
              mp₀.base2.acval fp_j.projKey (origVal fp_j.cvProj.levelParams ψ) := by
            rw [← hfp_j_key]
            simp only [Ix.Kernel.Verify.levelParamsAt, fp_j.hfindProj]
            exact mp₀.base2.acval_params fp_j.projKey _ fp_j.hfindProj _ _
              (fun p hp => (origVal_eq_substFn_range ψ fp_j.cvProj.levelParams fp_j.hProj_lvls
                fp_j.hProj_perm p hp).symm)
          rw [hac_eq_j]
          refine wellDenotedV_mkAppN_of _ _
            ⟨mp₀.base2.acval_wellDenoted _ _ _, mp₀.acval_validV _ _ _⟩
            (fun u hu => by
              rcases List.mem_append.mp hu with hu | hu
              · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hu; exact ⟨trivial, trivial⟩
              · rw [List.mem_singleton.mp hu]; exact ⟨trivial, trivial⟩) ?_
          have hargs_v : (entryParamBvars nP ++ [AnnotTerm.bvar 0]).map (interp V ρ') = vs_v ++ [x_v] := by
            rw [List.map_append, show nP = vs_v.length from hvs_v_len.symm,
              map_interp_entryParamBvars vs_v x_v ρ]
            simp only [List.map_singleton, interp_bvar, ρ']
            rw [← consList_snoc']; rfl
          rw [hargs_v, closed_interp_env (mp₀.base2.acval_closed _ _) ρ' ρ]
          exact hAppP_j
      have hws_map_eq : (entryParamBvars nP ++ chainArgsA).map (interp V ρ') =
          (entryParamBvars nP ++ projArgsA).map (interp V ρ') := by
        rw [List.map_append, List.map_append]
        congr 1
        refine List.ext_getElem (by simp [chainArgsA, projArgsA]) fun j hj1 hj2 => ?_
        have hj : j < i := by simp [chainArgsA] at hj1; exact hj1
        have hj' : j < nF := by omega
        obtain ⟨fdom_j, frest_j, rawDom_j, fbm_j, bsRaw_j, remRaw_j, -, -, -, fp_j, hfp_j_key⟩ :=
          mpf.hfields j hj'
        simp only [chainArgsA, projArgsA, List.getElem_map, List.getElem_range]
        have hac_eq_j : mp₀.base2.acval (mpf.projKeyAt j)
            (Level.substFn ψ (Ix.Kernel.Verify.levelParamsAt env₀ (mpf.projKeyAt j))
              ((List.range bnl).map .param)) =
            mp₀.base2.acval fp_j.projKey (origVal fp_j.cvProj.levelParams ψ) := by
          rw [← hfp_j_key]
          simp only [Ix.Kernel.Verify.levelParamsAt, fp_j.hfindProj]
          exact mp₀.base2.acval_params fp_j.projKey _ fp_j.hfindProj _ _
            (fun p hp => (origVal_eq_substFn_range ψ fp_j.cvProj.levelParams fp_j.hProj_lvls
              fp_j.hProj_perm p hp).symm)
        rw [hac_eq_j, interp_chain, interp_mkAppN_foldl]
        have hargs_v : (entryParamBvars nP ++ [AnnotTerm.bvar 0]).map (interp V ρ') = vs_v ++ [x_v] := by
          rw [List.map_append, show nP = vs_v.length from hvs_v_len.symm,
            map_interp_entryParamBvars vs_v x_v ρ]
          simp only [List.map_singleton, interp_bvar, ρ']
          rw [← consList_snoc']; rfl
        have hbv0 : interp V ρ' (.bvar 0) = x_v := by
          simp only [interp_bvar, ρ']
          rw [← consList_snoc']; rfl
        rw [hargs_v, hbv0]
        have hcoh_j := (hA_coh j hj' fdom_j frest_j rawDom_j fbm_j bsRaw_j remRaw_j fp_j hfp_j_key
          ψ ρ vs_v x_v hvs_v_len (hproj_setup ρ vs_v x_v hvs_v_len hAppT hx_mem')).1
        rw [closed_interp_env (mp₀.base2.acval_closed _ _) ρ' ρ]
        have hcl_ch : (fun n => interp V ρ' (m₃.acval (Ix.Kernel.projChainKey T j) (fun _ => n))) =
            (fun n => interp V ρ (m₃.acval (Ix.Kernel.projChainKey T j) (fun _ => n))) := by
          funext n
          exact closed_interp_env (m₃.acval_closed _ _) ρ' ρ
        rw [hcl_ch]
        exact hcoh_j
      -- 8. Conclude `interp V ρ rest = interp V ρ' fdomA_p` and `WellDenotedV V ρ rest`!
      have hchain_eq : chain V ρ' (entryParamBvars nP ++ chainArgsA) =
          chain V ρ' (entryParamBvars nP ++ projArgsA) :=
        chain_eq_of_map_interp_eq hws_map_eq
      have hrest_interp : interp V ρ rest = interp V ρ' fdomA_p := by
        rw [hrest_eq, show nP = (vs ++ [x]).length - 1 by simp [hvs_len, nP], interp_instSeq,
          chain_eq_consList_map, List.map_append, List.map_singleton]
        change interp V ρ' fdomA = interp V ρ' fdomA_p
        rw [hfdomA_inst, hfdomA_p_inst, ← hlen_ws1, interp_instSeq, hlen_ws1, ← hlen_ws2,
          interp_instSeq, hchain_eq]
      have hfdomA_p_wd : WellDenotedV V ρ' fdomA_p :=
        (hproj_app_wd i hi fdom_i frest_i rawDom_i fbm_i bsRaw_i remRaw_i fp_i
          ρ vs_v x_v hvs_v_len hAppT hx_mem').2 fdomA_p hrdom_eq
      have hrest_wd : WellDenotedV V ρ rest := by
        rw [hrest_eq, show nP = (vs ++ [x]).length - 1 by simp [hvs_len, nP]]
        refine (wellDenotedV_instSeq_iff (vs ++ [x]) fdomA hvx_wd).mpr ?_
        rw [chain_eq_consList_map, List.map_append, List.map_singleton]
        change WellDenotedV V ρ' fdomA
        rw [hfdomA_inst, ← hlen_ws1, wellDenotedV_instSeq_iff _ Fi hws1_wd, hchain_eq,
          ← wellDenotedV_instSeq_iff _ Fi hws2_wd, hlen_ws2, ← hfdomA_p_inst]
        exact hfdomA_p_wd
      -- 9. Conclude `WellDenotedV` and membership for `projNodeAV m₃.acval T i (tbl.entry i) x`!
      have hnode_eq : projNodeAV m₃.acval T i (tbl.entry i) x =
          AnnotTerm.chain (fun n => m₃.acval (Ix.Kernel.projChainKey T i) (fun _ => n)) x := by
        unfold projNodeAV
        simp [ProjTable.entry, tbl]
      have hnode_wd : WellDenotedV V ρ (projNodeAV m₃.acval T i (tbl.entry i) x) := by
        rw [hnode_eq]
        exact ⟨by rw [WellDenoted_chain]; exact ⟨fun m => (hA_ok i hi (fun _ => m) ρ).1, hx_wd.1⟩,
          by rw [AnnotValid_chain]; exact ⟨fun m => (hA_ok i hi (fun _ => m) ρ).2, hx_wd.2⟩⟩
      have hcoh_i := hA_coh i hi fdom_i frest_i rawDom_i fbm_i bsRaw_i remRaw_i fp_i hfp_i_key
        ψ ρ vs_v x_v hvs_v_len (hproj_setup ρ vs_v x_v hvs_v_len hAppT hx_mem')
      have hnode_mem : interp V ρ (projNodeAV m₃.acval T i (tbl.entry i) x) ∈ˢ interp V ρ rest := by
        rw [hnode_eq, interp_chain, hcoh_i.1, hrest_interp]
        exact hcoh_i.2 fdomA_p hrdom_eq
      exact ⟨hnode_wd, hrest_wd, hnode_mem⟩
    · -- **Clause (B): Iota law**
      refine ⟨TCa, hTCa_ilp, ?_⟩
      intro _ ρ ys rest hys_len hCys_wd hfit
      let ys_v := ys.map (interp V ρ)
      let vs_v := ys_v.take nP
      let c_v := ys_v.foldl SetTheory.app (interp V ρ (m₃.acval C ψ))
      have hys_v_len : ys_v.length = nP + nF := by simp [ys_v, hys_len, nP, nF]
      have hvs_v_len : vs_v.length = nP := by simp [vs_v, hys_v_len]
      -- 1. From `hfit : TeleFit V ρ TCa ys_v rest`, extract `SpineFit` on `dsC` and `rest`
      rw [hTCa_mk] at hfit
      obtain ⟨hsp_C, hrest_eq⟩ := (teleFit_mkPisAV_iff dsC bodyC ρ ys_v rest
        (by omega : ys_v.length = dsC.length)).mp hfit
      -- 2. Show `c_v ∈ˢ vs_v.foldl app (acval T ψ)` and `AppChainOk (acval T ψ) vs_v`
      have hC_mem_TCa := hTCa_mem_all ρ
      rw [hTCa_mk] at hC_mem_TCa
      have hC_wd_TCa := hTCa_wd_all ρ
      rw [hTCa_mk] at hC_wd_TCa
      obtain ⟨-, hc_mem_body, hbody_val⟩ :=
        appChainOk_and_mem_of_mkPisAV_spineFit dsC bodyC ys_v ρ (by omega) hC_wd_TCa.2 hC_mem_TCa hsp_C
      have hbody_wd : WellDenoted V (consList ys_v ρ) bodyC := by
        have hgo : ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) (as : List V) (σ : Nat → V),
            as.length = ds.length →
            WellDenoted V σ (mkPisAV ds b) →
            SpineFit σ (ds.map (·.2.2)) as →
            WellDenoted V (consList as σ) b := by
          intro ds; induction ds with
          | nil => intro b as σ hl hwd _; cases as with | nil => exact hwd | cons _ _ => simp at hl
          | cons d ds ih =>
            intro b as σ hl hwd hsp
            cases as with
            | nil => simp at hl
            | cons a as =>
              simp only [mkPisAV, WellDenoted_pi] at hwd
              simp only [List.map_cons, SpineFit] at hsp
              exact ih b as (cons a σ) (by simpa using hl) (hwd.2 a hsp.1) hsp.2
        exact hgo dsC bodyC ys_v ρ (by omega) hC_wd_TCa.1 hsp_C
      -- Identify `bodyC` with `mkAppN (m₃.acval T ψ) paramBvars` from `mpf.hC_ret_eq`!
      simp only [Nat.zero_add] at hbodyC_den
      rw [mpf.hC_ret_eq, openDummiesP_mkAppN, openDummiesP_const] at hbodyC_den
      have hret_args :
          ((List.range nP).map fun m => Expr.bvar (nP + nF - 1 - m)).map
              (openDummiesP (nP + nF) 0 0) =
            (List.range nP).map fun m => Expr.fvar m (.sort .zero) := by
        rw [List.map_map]
        refine List.map_congr_left fun m hm => ?_
        have hm' := List.mem_range.mp hm
        have h := openDummiesP_bvar_lt (nP + nF) 0 0 (nP + nF - 1 - m) (Nat.zero_le _) (by omega)
        simpa [show nP + nF - 1 - (nP + nF - 1 - m) = m by omega] using h
      rw [hret_args] at hbodyC_den
      obtain ⟨ftA, rargsA, hrargsA_len, hftA, hrargsA_at, hbodyC_eq⟩ :=
        denoteMeta_mkAppN_some hbodyC_den
      have hftA_eq : ftA = m₃.acval T ψ := by
        simp only [denoteMeta, hfindT₃, ConstantInfo.toConstantVal, hcvT_lps, List.length_map,
          List.length_range, ↓reduceIte] at hftA
        have h1 := Option.some.inj hftA
        rw [← h1]
        exact m₃.acval_params T _ hfindT₃ _ _ fun p hp => by
          have hp_lt : p < bnl := by
            simp only [ConstantInfo.toConstantVal, hcvT_lps, List.mem_range] at hp; exact hp
          have hr : (List.range bnl)[p]? = some p := by simp [hp_lt]
          have hm : ((List.range bnl).map Level.param)[p]? = some (.param p) := by simp [hp_lt]
          exact substFn_getElem?_eq_aux ψ List.nodup_range hr hm
      have hrargsV_eq : rargsA.map (interp V (consList ys_v ρ)) = vs_v := by
        have hlen_r : rargsA.length = nP := by rw [hrargsA_len]; simp
        refine List.ext_getElem (by rw [List.length_map, hlen_r, hvs_v_len]) fun k hk1 hk2 => ?_
        have hk : k < nP := by rw [← hvs_v_len]; exact hk2
        have hdk := hrargsA_at k (by rw [List.length_map, List.length_range]; exact hk)
        simp only [List.getElem_map, List.getElem_range, denoteMeta] at hdk
        have hsk : rargsA[k]'(by omega) = .bvar (nP + nF - 1 - k) := (Option.some.inj hdk).symm
        rw [List.getElem_map, hsk, interp_bvar,
          consList_getElem ys_v ρ (nP + nF - 1 - k) (by omega)]
        simp only [vs_v, List.getElem_take]
        congr 1; omega
      rw [hbodyC_eq, hftA_eq] at hc_mem_body hbody_wd hbody_val
      have hAppT_ys : AppChainOk (interp V ρ (m₃.acval T ψ)) vs_v := by
        have hwd_all := wellDenotedV_mkAppN_inv (m₃.acval T ψ) rargsA ⟨hbody_wd, hbody_val⟩
        have h1 := hwd_all.2.2
        rw [hrargsV_eq, closed_interp_env (m₃.acval_closed T ψ) (consList ys_v ρ) ρ] at h1
        exact h1
      have hc_mem_T : c_v ∈ˢ vs_v.foldl SetTheory.app (interp V ρ (m₃.acval T ψ)) := by
        rw [interp_mkAppN_foldl, hrargsV_eq,
          closed_interp_env (m₃.acval_closed T ψ) (consList ys_v ρ) ρ] at hc_mem_body
        exact hc_mem_body
      -- 3. Apply `hA_coh i` to rewrite `projNodeAV ... (C ys)` to `proj_i vs_v (C ys)`!
      obtain ⟨fdom_i, frest_i, rawDom_i, fbm_i, bsRaw_i, remRaw_i, -, -, -, fp_i, hfp_i_key⟩ :=
        mpf.hfields i hi
      have hnode_eq : projNodeAV m₃.acval T i (tbl.entry i)
          (AnnotTerm.mkAppN (m₃.acval C ψ) ys) =
          AnnotTerm.chain (fun n => m₃.acval (Ix.Kernel.projChainKey T i) (fun _ => n))
            (AnnotTerm.mkAppN (m₃.acval C ψ) ys) := by
        unfold projNodeAV; simp [ProjTable.entry, tbl]
      have hcoh_i := (hA_coh i hi fdom_i frest_i rawDom_i fbm_i bsRaw_i remRaw_i fp_i hfp_i_key
        ψ ρ vs_v c_v hvs_v_len (hproj_setup ρ vs_v c_v hvs_v_len hAppT_ys hc_mem_T)).1
      change interp V ρ (projNodeAV m₃.acval T i (tbl.entry i)
        (AnnotTerm.mkAppN (m₃.acval C ψ) ys)) =
        interp V ρ (ys.getD (nP + i) default)
      rw [hnode_eq, interp_chain]
      have hcl_c : interp V ρ (AnnotTerm.mkAppN (m₃.acval C ψ) ys) = c_v := by
        simp [c_v, ys_v, interp_mkAppN_foldl]
      rw [hcl_c, hcoh_i]
      -- 4. Now fire `fp_i.hfindIota` at `ys_v` to prove `proj_i vs_v c_v = ys_v[nP + i]`!
      have hmemI := Ix.Kernel.Semantics.Env.find?_mem fp_i.hfindIota
      obtain ⟨TIa, hTIa⟩ := mp₀.type_reads _ hmemI (origVal fp_i.cvIota.levelParams ψ)
      have hTIa_mem := mp₀.mem_type _ hmemI (origVal fp_i.cvIota.levelParams ψ) TIa hTIa ρ
      rw [Ix.Kernel.Semantics.Env.find?_name fp_i.hfindIota] at hTIa_mem
      have hTIa_wd := mp₀.type_wellDenotedV _ hmemI (origVal fp_i.cvIota.levelParams ψ) TIa hTIa ρ
      have hTIa_pos : denoteMeta mp₀.base2.acval env₀ ψ 0
          (Core.posOf fp_i.cvIota.levelParams fp_i.cvIota.type) = some TIa := by
        rw [posOf_denoteMeta]; exact hTIa
      obtain ⟨dsI, eqBodyA, hTIa_mk, hdsI_len, -, heqBody_den⟩ :=
        denoteMeta_stripPis (nP + nF) 0 fp_i.hIota_strip hTIa_pos
      -- Equate `dsI.map (·.2.2)` to `dsC.map (·.2.2)` via `fp_i.hIota_doms` + `hTCa_mp₀`!
      have hdsIC_eq : dsI.map (·.2.2) = dsC.map (·.2.2) := by
        have hC_st : (tyA_C.renameConsts g).stripPis (nP + nF) = some (fp_i.cbsI, fp_i.cremI) := by
          rw [← hC_ren_eq]; exact fp_i.hC_strip
        have hcbsI_eq : fp_i.cbsI = mpf.bsC.map (fun p => (p.1.renameConsts g, p.2)) :=
          (Prod.mk.inj (Option.some.inj (hC_st.symm.trans hstripC_ren))).1
        refine List.ext_getElem (by simp [hdsI_len, hdsC_len]) fun k hk1 hk2 => ?_
        simp only [List.getElem_map]
        have hk : k < nP + nF := by simp [hdsI_len] at hk1; exact hk1
        have h1 := get_dom_denoteMeta_stripPis fp_i.hIota_strip hTIa_pos hTIa_mk hdsI_len k hk
        have h2 := get_dom_denoteMeta_stripPis hstripC_ren hTCa_mp₀ hTCa_mk hdsC_len k hk
        have heq_k : ExprSemEq
            (fp_i.ibsI[k]'(by rw [stripPis_length_p fp_i.hIota_strip]; exact hk)).1
            ((mpf.bsC.map (fun p => (p.1.renameConsts g, p.2)))[k]'(by
              rw [List.length_map, stripPis_length_p hstripC]; exact hk)).1 := by
          have h := forall₂_getElem fp_i.hIota_doms k
            (by rw [List.length_map, stripPis_length_p fp_i.hIota_strip]; exact hk)
            (by rw [List.length_map, hcbsI_eq, List.length_map, stripPis_length_p hstripC]; exact hk)
          simpa [hcbsI_eq] using h
        have hsame := denoteMeta_exprSemEq (acval := mp₀.base2.acval) (env := env₀) (φ := ψ)
          (d := k) (exprSemEq_openDummiesP heq_k k 0 0)
        rw [h1, h2] at hsame
        exact Option.some.inj hsame
      rw [hTIa_mk] at hTIa_mem hTIa_wd
      obtain ⟨-, hiota_mem, -⟩ := appChainOk_and_mem_of_mkPisAV_spineFit dsI eqBodyA ys_v ρ
        (by omega) hTIa_wd.2 hTIa_mem (by rw [hdsIC_eq]; exact hsp_C)
      -- Identify `eqBodyA = .app (.app (.app (acval eqName ψ_eq) alphaA) lhsA) (.bvar (nF - 1 - i))`
      simp only [Nat.zero_add] at heqBody_den
      rw [openDummiesP_mkAppN, openDummiesP_const] at heqBody_den
      simp only [List.map_cons, List.map_nil] at heqBody_den
      obtain ⟨eqFnA, eqArgsA, heqArgs_len, heqFnA, heqArgs_at, heqBody_eq⟩ :=
        denoteMeta_mkAppN_some heqBody_den
      simp only [List.length_cons, List.length_nil] at heqArgs_len
      obtain ⟨alphaA, lhsA, rhsA, rfl⟩ : ∃ a l r, eqArgsA = [a, l, r] := by
        cases eqArgsA with
        | nil => simp at heqArgs_len
        | cons a t1 =>
          cases t1 with
          | nil => simp at heqArgs_len
          | cons l t2 =>
            cases t2 with
            | nil => simp at heqArgs_len
            | cons r t3 =>
              cases t3 with
              | nil => exact ⟨a, l, r, rfl⟩
              | cons _ _ => simp at heqArgs_len
      have hα_den := heqArgs_at 0 (by simp)
      have hlhs_den := heqArgs_at 1 (by simp)
      have hrhs_den := heqArgs_at 2 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hα_den hlhs_den hrhs_den
      -- Evaluate `eqFnA`: `acval eqName (substFn ψ [uN] [fp_i.uEq])`
      have heqA_lps : (Ix.Kernel.eqA : ConstantInfo .anon).toConstantVal.levelParams = [Ix.Kernel.uN] := by
        decide +kernel
      have heqFn_eq : eqFnA = mp₀.base2.acval Ix.Kernel.eqName
          (Level.substFn ψ [Ix.Kernel.uN] [fp_i.uEq]) := by
        simp only [denoteMeta, heqPin, heqA_lps, List.length_singleton, ↓reduceIte] at heqFnA
        exact (Option.some.inj heqFnA).symm
      -- Evaluate `rhsA`: `.bvar (nF - 1 - i)`, whose interp at `consList ys_v ρ` is `ys_v[nP + i]`!
      have hrhs_val : interp V (consList ys_v ρ) rhsA = interp V ρ (ys.getD (nP + i) default) := by
        have hopen_bv : openDummiesP (nP + nF) 0 0 (.bvar (nF - 1 - i)) =
            .fvar (nP + i) (.sort .zero) := by
          have h := openDummiesP_bvar_lt (nP + nF) 0 0 (nF - 1 - i) (Nat.zero_le _) (by omega)
          simpa [show nP + nF - 1 - (nF - 1 - i) = nP + i by omega] using h
        rw [hopen_bv, denoteMeta] at hrhs_den
        have hreq : rhsA = .bvar (nP + nF - 1 - (nP + i)) := (Option.some.inj hrhs_den).symm
        rw [hreq, interp_bvar,
          consList_getElem ys_v ρ (nP + nF - 1 - (nP + i)) (by omega)]
        have hidx_eq : ys_v.length - 1 - (nP + nF - 1 - (nP + i)) = nP + i := by omega
        have hys_lt : nP + i < ys.length := by
          have : ys.length = nP + nF := hys_len
          omega
        simp only [hidx_eq, ys_v, List.getElem_map, List.getD,
          List.getElem?_eq_getElem hys_lt, Option.getD_some]
      -- Evaluate `lhsA`: `proj_i vs_v c_v`!
      have hlhs_val : interp V (consList ys_v ρ) lhsA =
          (vs_v ++ [c_v]).foldl SetTheory.app
            (interp V ρ (mp₀.base2.acval fp_i.projKey (origVal fp_i.cvProj.levelParams ψ))) := by
        have hsame := denoteMeta_exprSemEq (acval := mp₀.base2.acval) (env := env₀) (φ := ψ)
          (d := nP + nF) (exprSemEq_openDummiesP fp_i.hIota_lhs (nP + nF) 0 0)
        rw [hlhs_den, openDummiesP_mkAppN, openDummiesP_const, List.map_append,
          List.map_singleton] at hsame
        have hargsP :
            ((List.range nP).map fun m => Expr.bvar (nP + nF - 1 - m)).map
                (openDummiesP (nP + nF) 0 0) =
              (List.range nP).map fun m => Expr.fvar m (.sort .zero) := by
          rw [List.map_map]
          refine List.map_congr_left fun m hm => by
            have hm' := List.mem_range.mp hm
            have h := openDummiesP_bvar_lt (nP + nF) 0 0 (nP + nF - 1 - m) (Nat.zero_le _) (by omega)
            simpa [show nP + nF - 1 - (nP + nF - 1 - m) = m by omega] using h
        have hargsF :
            ((List.range nF).map fun m => Expr.bvar (nF - 1 - m)).map
                (openDummiesP (nP + nF) 0 0) =
              (List.range nF).map fun m => Expr.fvar (nP + m) (.sort .zero) := by
          rw [List.map_map]
          refine List.map_congr_left fun m hm => by
            have hm' := List.mem_range.mp hm
            have h := openDummiesP_bvar_lt (nP + nF) 0 0 (nF - 1 - m) (Nat.zero_le _) (by omega)
            simpa [show nP + nF - 1 - (nF - 1 - m) = nP + m by omega] using h
        rw [hargsP, openDummiesP_mkAppN, openDummiesP_const, List.map_append, hargsP,
          hargsF] at hsame
        obtain ⟨fpA, pargsA, hpargs_len, hfpA, hpargs_at, hlhs_eq⟩ :=
          denoteMeta_mkAppN_some hsame.symm
        have hfpA_eq : fpA = mp₀.base2.acval fp_i.projKey (origVal fp_i.cvProj.levelParams ψ) := by
          simp only [denoteMeta, fp_i.hfindProj, ConstantInfo.toConstantVal, List.length_map,
            List.length_range, fp_i.hProj_lvls, ↓reduceIte] at hfpA
          have h1 := Option.some.inj hfpA
          rw [← h1]
          exact mp₀.base2.acval_params fp_i.projKey _ fp_i.hfindProj _ _
            (fun p hp => (origVal_eq_substFn_range ψ fp_i.cvProj.levelParams fp_i.hProj_lvls
              fp_i.hProj_perm p hp).symm)
        have hpargs_v : pargsA.map (interp V (consList ys_v ρ)) = vs_v ++ [c_v] := by
          have hlen_p : pargsA.length = nP + 1 := by
            rw [hpargs_len]; simp
          refine List.ext_getElem (by simp [hlen_p, hvs_v_len]) fun k hk1 hk2 => ?_
          by_cases hkn : k < nP
          · have hdk := hpargs_at k (by simp; omega)
            rw [List.getElem_append_left (by simp; exact hkn)] at hdk
            simp only [List.getElem_map, List.getElem_range, denoteMeta] at hdk
            have hsk : pargsA[k]'(by omega) = .bvar (nP + nF - 1 - k) := (Option.some.inj hdk).symm
            rw [List.getElem_map, hsk, interp_bvar,
              consList_getElem ys_v ρ (nP + nF - 1 - k) (by omega),
              List.getElem_append_left (by omega)]
            simp only [vs_v, List.getElem_take]
            congr 1; omega
          · have hk2' : k < nP + 1 := by simpa [hvs_v_len] using hk2
            have hk_eq : k = nP := by omega
            subst hk_eq
            have hdk := hpargs_at nP (by simp)
            rw [List.getElem_append_right (by simp)] at hdk
            simp only [List.length_map, List.length_range, Nat.sub_self,
              List.getElem_cons_zero] at hdk
            obtain ⟨fcA, cargsA, hcargs_len, hfcA, hcargs_at, hc_eq⟩ :=
              denoteMeta_mkAppN_some hdk
            have hfcA_eq : fcA = m₃.acval C ψ := by
              simp only [denoteMeta, hfindCM, ConstantInfo.toConstantVal, List.length_map,
                List.length_range, hCM_lvls, ↓reduceIte] at hfcA
              have h1 := Option.some.inj hfcA
              rw [← h1, hacC_eq ψ]
              exact mp₀.base2.acval_params (g C) _ hfindCM _ _
                (fun p hp => (origVal_eq_substFn_range ψ cvCM.levelParams hCM_lvls hCM_perm p hp).symm)
            have hcargs_v : cargsA.map (interp V (consList ys_v ρ)) = ys_v := by
              have hlen_c : cargsA.length = nP + nF := by rw [hcargs_len]; simp
              refine List.ext_getElem (by simp [hlen_c, hys_v_len]) fun m hm1 hm2 => ?_
              have hm : m < nP + nF := by omega
              have hdm := hcargs_at m (by simp; exact hm)
              by_cases hmn : m < nP
              · rw [List.getElem_append_left (by simp; exact hmn)] at hdm
                simp only [List.getElem_map, List.getElem_range, denoteMeta] at hdm
                have hsm : cargsA[m]'(by omega) = .bvar (nP + nF - 1 - m) := (Option.some.inj hdm).symm
                rw [List.getElem_map, hsm, interp_bvar,
                  consList_getElem ys_v ρ (nP + nF - 1 - m) (by omega)]
                congr 1; omega
              · rw [List.getElem_append_right (by simp; omega)] at hdm
                simp only [List.length_map, List.length_range, List.getElem_map,
                  List.getElem_range, denoteMeta] at hdm
                have hsm : cargsA[m]'(by omega) = .bvar (nP + nF - 1 - (nP + (m - nP))) :=
                  (Option.some.inj hdm).symm
                rw [List.getElem_map, hsm, interp_bvar,
                  consList_getElem ys_v ρ (nP + nF - 1 - (nP + (m - nP))) (by omega)]
                congr 1; omega
            rw [List.getElem_map, hc_eq, hfcA_eq, interp_mkAppN_foldl, hcargs_v,
              closed_interp_env (m₃.acval_closed C ψ) (consList ys_v ρ) ρ,
              List.getElem_append_right (by omega)]
            simp only [hvs_v_len, Nat.sub_self, List.getElem_cons_zero]
            rfl
        rw [hlhs_eq, hfpA_eq, interp_mkAppN_foldl, hpargs_v,
          closed_interp_env (mp₀.base2.acval_closed _ _) (consList ys_v ρ) ρ]
      -- 5. Apply `mp₀.eq_law` + `mem_eqv` using `WellDenoted` of `eqBodyA`!
      have heq_wd : WellDenoted V (consList ys_v ρ) eqBodyA := by
        have hgo : ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) (as : List V) (σ : Nat → V),
            as.length = ds.length →
            WellDenoted V σ (mkPisAV ds b) →
            SpineFit σ (ds.map (·.2.2)) as →
            WellDenoted V (consList as σ) b := by
          intro ds; induction ds with
          | nil => intro b as σ hl hwd _; cases as with | nil => exact hwd | cons _ _ => simp at hl
          | cons d ds ih =>
            intro b as σ hl hwd hsp
            cases as with
            | nil => simp at hl
            | cons a as =>
              simp only [mkPisAV, WellDenoted_pi] at hwd
              simp only [List.map_cons, SpineFit] at hsp
              exact ih b as (cons a σ) (by simpa using hl) (hwd.2 a hsp.1) hsp.2
        exact hgo dsI eqBodyA ys_v ρ (by omega) hTIa_wd.1 (by rw [hdsIC_eq]; exact hsp_C)
      rw [heqBody_eq, heqFn_eq] at hiota_mem heq_wd
      simp only [AnnotTerm.mkAppN] at hiota_mem heq_wd
      -- From `WellDenoted V σ (.app (.app (.app eqFn alphaA) lhsA) rhsA)` + `mp₀.acval_memType` on `eqA`,
      -- extract `α ∈ˢ univ (ψ_eq uN)`, `lhs ∈ˢ α`, `rhs ∈ˢ α` by graph rigidity (`piR_dom_unique`).
      let ψ_eq := Level.substFn ψ [Ix.Kernel.uN] [fp_i.uEq]
      have hα_u : interp V (consList ys_v ρ) alphaA ∈ˢ (univ (ψ_eq Ix.Kernel.uN) : V) ∧
          interp V (consList ys_v ρ) lhsA ∈ˢ interp V (consList ys_v ρ) alphaA ∧
          interp V (consList ys_v ρ) rhsA ∈ˢ interp V (consList ys_v ρ) alphaA := by
        obtain ⟨ea, hea, -, hmem⟩ := mp₀.acval_memType heqPin ψ_eq
        rw [show (Ix.Kernel.eqA : ConstantInfo .anon).toConstantVal.type =
            (Ix.Kernel.eqA (md := .anon)).toConstantVal.type from rfl,
          Ix.Kernel.Model.denoteMeta_eqA_type_gen] at hea
        obtain rfl : ea = Ix.Kernel.Model.eqTy ψ_eq := (Option.some.inj hea).symm
        have hpin : interp V (consList ys_v ρ) (mp₀.base2.acval Ix.Kernel.eqName ψ_eq) ∈ˢ
            piR 1 (univ (ψ_eq Ix.Kernel.uN) : V)
              (fun A => piR 1 A fun _ => piR 1 A fun _ => (univ 0 : V)) := by
          have := hmem (consList ys_v ρ)
          rw [show interp V (consList ys_v ρ) (Ix.Kernel.Model.eqTy ψ_eq) =
              piR 1 (univ (ψ_eq Ix.Kernel.uN) : V)
                (fun A => piR 1 A fun _ => piR 1 A fun _ => (univ 0 : V)) from rfl] at this
          exact this
        have hwd2 : WellDenoted V (consList ys_v ρ)
            (.app (.app (mp₀.base2.acval Ix.Kernel.eqName ψ_eq) alphaA) lhsA) := by
          have h := heq_wd; rw [WellDenoted_app] at h; exact h.1
        have hwd1 : WellDenoted V (consList ys_v ρ)
            (.app (mp₀.base2.acval Ix.Kernel.eqName ψ_eq) alphaA) := by
          have h := hwd2; rw [WellDenoted_app] at h; exact h.1
        obtain ⟨-, -, v1, A1, B1, hIn1, hα1, -⟩ := by
          have h := hwd1; rw [WellDenoted_app] at h; exact h
        have hv1 : v1 ≠ 0 := fun hv =>
          not_pt_mem_piR_pos (V := V) Nat.one_ne_zero (eq_pt_of_mem_piR_zero (hv ▸ hIn1) ▸ hpin)
        have hα : interp V (consList ys_v ρ) alphaA ∈ˢ (univ (ψ_eq Ix.Kernel.uN) : V) := by
          rwa [← piR_dom_unique hv1 Nat.one_ne_zero hIn1 hpin]
        have hpin1 := app_mem_piR_pos (V := V) Nat.one_ne_zero hpin hα
        obtain ⟨-, -, v2, A2, B2, hIn2, hlhs2, -⟩ := by
          have h := hwd2; rw [WellDenoted_app] at h; exact h
        rw [interp_app] at hIn2
        have hv2 : v2 ≠ 0 := fun hv =>
          not_pt_mem_piR_pos (V := V) Nat.one_ne_zero (eq_pt_of_mem_piR_zero (hv ▸ hIn2) ▸ hpin1)
        have hlhs : interp V (consList ys_v ρ) lhsA ∈ˢ interp V (consList ys_v ρ) alphaA := by
          rwa [← piR_dom_unique hv2 Nat.one_ne_zero hIn2 hpin1]
        have hpin2 := app_mem_piR_pos (V := V) Nat.one_ne_zero hpin1 hlhs
        obtain ⟨-, -, v3, A3, B3, hIn3, hrhs3, -⟩ := by
          have h := heq_wd; rw [WellDenoted_app] at h; exact h
        rw [interp_app, interp_app] at hIn3
        have hv3 : v3 ≠ 0 := fun hv =>
          not_pt_mem_piR_pos (V := V) Nat.one_ne_zero (eq_pt_of_mem_piR_zero (hv ▸ hIn3) ▸ hpin2)
        have hrhs : interp V (consList ys_v ρ) rhsA ∈ˢ interp V (consList ys_v ρ) alphaA := by
          rwa [← piR_dom_unique hv3 Nat.one_ne_zero hIn3 hpin2]
        exact ⟨hα, hlhs, hrhs⟩
      have heq_val := (mp₀.eq_law heqPin ψ_eq).1 (consList ys_v ρ)
        (interp V (consList ys_v ρ) alphaA)
        (interp V (consList ys_v ρ) lhsA)
        (interp V (consList ys_v ρ) rhsA)
        hα_u.1 hα_u.2.1 hα_u.2.2
      simp only [interp_app] at hiota_mem
      rw [heq_val] at hiota_mem
      have hlr := eq_of_mem_eqv hiota_mem
      rw [← hlhs_val, hlr, hrhs_val]
  · -- **Clause (C): Structural η** — vacuous since `tbl.off = 2`
    intro hle
    simp only [ProjTable.entry] at hle
    omega

end IxVM.Refinement.Typing.FamilyAlias
