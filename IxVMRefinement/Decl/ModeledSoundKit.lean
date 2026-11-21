import IxVMRefinement.Decl.ModeledLevels
import IxVMRefinement.Decl.ModeledTele
import IxC.Kernel.Model.IndOpenerGrade
import IxC.Kernel.Model.DeclIndJ
import IxC.Kernel.Model.Annot.BitRename
import IxC.Kernel.Model.Annot.BitInst
import IxC.Kernel.Verify.InferLemmas
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.InstSpine
import IxC.Kernel.Verify.BridgeWfImp
import IxC.Kernel.Verify.Extend.Iota
import IxC.Kernel.Verify.Extend.Recs
import IxC.Kernel.Verify.Denote.VClosed
import IxC.Kernel.Verify.Denote.IndFrame

/-!
# Soundness Kit for VM Modeled-Inductive `defeq_lam_tele` Walks

In `KernelModeled::check_iota_rule`, the rule's right-hand side `rhsA` has its `rP + cnF`
`λ`-binders opened in `rhsA`'s own domain context `lfvs` (`openLamsAtFvars (rP + cnF) rhsA 0`),
while the recursor prefix `tyA` and constructor field domains `crestL` are instantiated at `lfvs`
and compared pairwise via `defeq_lam_tele` (`LamTeleWalkJ`).

Because `denoteMeta` ignores `.fvar` type annotations (`denoteMeta_erasedEq`), instantiating the
recursor and constructor telescopes at `lfvs` produces domains `pdoms` that are `Expr.ErasedEq` to
the public-frame opener domains `(fvsP ++ xFvsP).map Expr.fvarTypeD`, while having all free-variable
leaves inside `lfvs`. Strong induction on the position `k < rP + cnF` (`annotMem_lamWalk`) grades
each `λ`-slot and equates its reading with the statement tower's slot, firing `DefEqClaimJ` on
`lfvs`'s own prefix context via `ctxOk_of_walked_openers_lt`.

This module also defines the VM-shaped modeled-inductive judgement records (`IotaRunsVmJ`,
`IotaThmVmRunJ`, `IotaThmNVmRunJ`, `IotaRuleVmRunJ`, `IotaRulesVmRunJ`, `IndRecsFoldVmRunJ`,
`IndRecsVmRunJ`, `DeclIndVmRunJ`) and proves their projection `.toTrivDefEq` onto `DeclIndRunJ`
at `{ J with defeq := fun _ _ _ _ => True }`, giving `DeclStoreInv` preservation and `EtaFamiliesClosed`
for free without duplicating syntactic store folds.
-/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule IndCaps
  CheckMode LevelParam EnvExt SwapShList openPisAtFvars eqName eqA auxKey nestedRuleShape recRuleBits
  isEqHead fvarLeaves_instSpine hasFvar_renameConsts instPisAt_WScoped instPisAt_index_WScoped
  instSpine_WScoped instSpine_closed openPisAtFvars_index recRuleKOf_mono recRuleEtaOf_mono)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Scoping, Leaf-Closure, Bounds, and Erasure Lemmas for `openLamsAtFvars` -/

theorem openLamsAtFvars_WScoped :
    ∀ (n : Nat) (e : KExpr) (i : Nat) {fvs : List KExpr} {body : KExpr},
      openLamsAtFvars n e i = some (fvs, body) → Expr.WScoped i e →
      (∀ x ∈ fvs, Expr.WScoped (i + n) x) ∧ Expr.WScoped (i + n) body := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h hw
    dsimp only [openLamsAtFvars] at h
    rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
    exact ⟨fun _ hx => (nomatch hx), hw⟩
  | succ n ih =>
    intro e i fvs body h hw
    cases e with
    | lam dom bodyE mb =>
      simp only [openLamsAtFvars] at h
      cases hrec : openLamsAtFvars n (bodyE.instantiate1 (.fvar i dom)) (i + 1) with
      | none => rw [hrec] at h; exact nomatch h
      | some p =>
        rw [hrec] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Expr.WScoped] at hw
        obtain ⟨hdom, hbody⟩ := hw
        have hinst : Expr.WScoped (i + 1) (bodyE.instantiate1 (.fvar i dom)) :=
          Expr.WScoped.instantiate1 hdom 0 hbody
        obtain ⟨hfvs', hbody'⟩ := ih _ _ hrec hinst
        rw [show i + 1 + n = i + (n + 1) by omega] at hfvs' hbody'
        refine ⟨?_, hbody'⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [Expr.WScoped]
          exact ⟨by omega, hdom⟩
        · exact hfvs' x hx
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | forallE _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ => exact nomatch h

theorem openLamsAtFvars_leaves :
    ∀ (k : Nat) {e : KExpr} {d : Nat} {fvs : List KExpr} {body : KExpr},
      openLamsAtFvars k e d = some (fvs, body) →
      ∀ l, (l ∈ body.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
        l ∈ e.fvarLeaves ∨ Expr.fvar l.1 l.2 ∈ fvs := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h l hl
    simp only [openLamsAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hl with hl | ⟨_, hx, -⟩
    · exact Or.inl hl
    · exact nomatch hx
  | succ k ih =>
    intro e d fvs body h l hl
    match e, h with
    | .lam dom bodyE mb, h =>
      simp only [openLamsAtFvars] at h
      cases hop : openLamsAtFvars k (bodyE.instantiate1 (.fvar d dom)) (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have head : l ∈ (Expr.fvar d dom).fvarLeaves →
            l ∈ (Expr.lam dom bodyE mb).fvarLeaves ∨
              Expr.fvar l.1 l.2 ∈ Expr.fvar d dom :: p.1 := by
          intro hl'
          rw [Expr.fvarLeaves] at hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact Or.inr List.mem_cons_self
          · refine Or.inl ?_
            rw [Expr.fvarLeaves]
            exact List.mem_append_left _ hl'
        rcases hl with hl | ⟨x, hx, hlx⟩
        · rcases ih hop l (Or.inl hl) with hl' | hl'
          · rcases Expr.fvarLeaves_instantiate1 bodyE 0 hl' with h1 | h1
            · refine Or.inl ?_
              rw [Expr.fvarLeaves]
              exact List.mem_append_right _ h1
            · exact head h1
          · exact Or.inr (List.mem_cons_of_mem _ hl')
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact head hlx
          · rcases ih hop l (Or.inr ⟨x, hx', hlx⟩) with hl' | hl'
            · rcases Expr.fvarLeaves_instantiate1 bodyE 0 hl' with h1 | h1
              · refine Or.inl ?_
                rw [Expr.fvarLeaves]
                exact List.mem_append_right _ h1
              · exact head h1
            · exact Or.inr (List.mem_cons_of_mem _ hl')

theorem openLamsAtFvars_bounded :
    ∀ (k : Nat) {e : KExpr} {d : Nat} {fvs : List KExpr} {body : KExpr},
      openLamsAtFvars k e d = some (fvs, body) →
      e.looseBVarsBounded 0 = true →
      body.looseBVarsBounded 0 = true ∧
        ∀ x ∈ fvs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body h hb
    simp only [openLamsAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hb, fun _ hx => nomatch hx⟩
  | succ k ih =>
    intro e d fvs body h hb
    match e, h with
    | .lam dom bodyE mb, h =>
      simp only [openLamsAtFvars] at h
      cases hop : openLamsAtFvars k (bodyE.instantiate1 (.fvar d dom)) (d + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb' : dom.looseBVarsBounded 0 = true ∧ bodyE.looseBVarsBounded 1 = true := by
          revert hb; simp [Expr.looseBVarsBounded]
        obtain ⟨hbody, hanns⟩ := ih hop
          (Expr.looseBVarsBounded_instantiate1_gen (a := .fvar d dom) rfl hb'.2)
        refine ⟨hbody, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb'.1
        · exact hanns x hx'

theorem stripLams_isSome_instantiate1 {a : KExpr} :
    ∀ (k : Nat) {e : KExpr} (j : Nat),
      (e.stripLams k).isSome = true → ((e.instantiate1 a j).stripLams k).isSome = true
  | 0, _, _, _ => rfl
  | k + 1, .lam dom body mb, j, h => by
    simp only [Expr.stripLams, Option.isSome_map] at h
    simp only [Expr.instantiate1, Expr.stripLams, Option.isSome_map]
    exact stripLams_isSome_instantiate1 k (j + 1) h
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .forallE _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => nomatch h

theorem instLamsAt_of_stripLams_len :
    ∀ (sp : List KExpr) {e : KExpr},
      (e.stripLams sp.length).isSome = true →
      ∃ ldoms lrest, Expr.instLamsAt sp e = some (ldoms, lrest) ∧ ldoms.length = sp.length
  | [], e, _ => ⟨[], e, rfl, rfl⟩
  | a :: as, .lam dom body mb, h => by
    simp only [List.length_cons, Expr.stripLams, Option.isSome_map] at h
    obtain ⟨ds, rs, hinst, hlen⟩ :=
      instLamsAt_of_stripLams_len as (stripLams_isSome_instantiate1 (a := a) as.length 0 h)
    exact ⟨dom :: ds, rs, by simp [Expr.instLamsAt, hinst], by simp [hlen]⟩
  | _ :: _, .bvar _, h | _ :: _, .fvar _ _, h | _ :: _, .sort _, h
  | _ :: _, .const _ _, h | _ :: _, .app _ _, h | _ :: _, .forallE _ _ _, h
  | _ :: _, .letE _ _ _ _, h | _ :: _, .lit _, h | _ :: _, .proj _ _ _, h => nomatch h

theorem instSpine_erasedEq :
    ∀ (as as' : List KExpr) (t : Nat) {e e' : KExpr},
      Expr.ErasedEq e e' →
      as.length = as'.length →
      (∀ (i : Nat) (a a' : KExpr), as[i]? = some a → as'[i]? = some a' → Expr.ErasedEq a a') →
      Expr.ErasedEq (Expr.instSpine as t e) (Expr.instSpine as' t e')
  | [], [], _, _, _, he, _, _ => he
  | [], _ :: _, _, _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, _, _, hlen, _ => nomatch hlen
  | a :: as, a' :: as', t, _, _, he, hlen, hargs =>
    instSpine_erasedEq as as' (t - 1)
      (Expr.ErasedEq.instantiate1 he (hargs 0 a a' rfl rfl))
      (by simpa using hlen)
      (fun i x x' hx hx' => hargs (i + 1) x x' (by simpa using hx) (by simpa using hx'))

theorem instPisAt_erasedEq :
    ∀ (as as' : List KExpr) {ty ty' : KExpr} {ds ds' : List KExpr} {rs rs' : KExpr},
      Expr.instPisAt as ty = some (ds, rs) →
      Expr.instPisAt as' ty' = some (ds', rs') →
      Expr.ErasedEq ty ty' →
      (∀ (i : Nat) (a a' : KExpr), as[i]? = some a → as'[i]? = some a' → Expr.ErasedEq a a') →
      as.length = as'.length →
      (∀ (i : Nat) (x x' : KExpr), ds[i]? = some x → ds'[i]? = some x' → Expr.ErasedEq x x') ∧
        Expr.ErasedEq rs rs' := by
  intro as
  induction as with
  | nil =>
    intro as' ty ty' ds ds' rs rs' h h' hty _ hlen
    cases as' with
    | nil =>
      dsimp only [Expr.instPisAt] at h h'
      rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
      rcases Prod.mk.inj (Option.some.inj h') with ⟨rfl, rfl⟩
      exact ⟨fun _ _ _ hx _ => (nomatch hx), hty⟩
    | cons _ _ => exact nomatch hlen
  | cons a as ih =>
    intro as' ty ty' ds ds' rs rs' h h' hty hargs hlen
    cases as' with
    | nil => exact nomatch hlen
    | cons a' as'' =>
      match ty, h with
      | .forallE d₁ b₁ m₁, h =>
        match ty', h' with
        | .forallE d₂ b₂ m₂, h' =>
          obtain ⟨-, hdom, hbody⟩ : m₁ = m₂ ∧ Expr.ErasedEq d₁ d₂ ∧ Expr.ErasedEq b₁ b₂ :=
            hty
          simp only [Expr.instPisAt] at h h'
          cases h1 : Expr.instPisAt as (b₁.instantiate1 a) with
          | none => rw [h1] at h; exact nomatch h
          | some p1 =>
            cases h2 : Expr.instPisAt as'' (b₂.instantiate1 a') with
            | none => rw [h2] at h'; exact nomatch h'
            | some p2 =>
              rw [h1] at h
              rw [h2] at h'
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h h'
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨rfl, rfl⟩ := h'
              obtain ⟨hds, hrs⟩ := ih as'' h1 h2
                (Expr.ErasedEq.instantiate1 hbody (hargs 0 a a' rfl rfl))
                (fun i x x' hx hx' =>
                  hargs (i + 1) x x' (by simpa using hx) (by simpa using hx'))
                (by simpa using hlen)
              refine ⟨?_, hrs⟩
              intro i x x' hx hx'
              cases i with
              | zero =>
                obtain rfl : d₁ = x := by simpa using hx
                obtain rfl : d₂ = x' := by simpa using hx'
                exact hdom
              | succ i =>
                exact hds i x x' (by simpa using hx) (by simpa using hx')

/-! ## Parameter-Spine Adapter `PinsWalkOk` and `LamTeleWalkJ` Unpacking -/

/-- Structural invariants of the constructor-parameter spine functor `pinsOf` passed to
`LamTeleWalkJ` (satisfied by both `fun pre => pre.take cnP` in the plain case and
`fun pre => pins.map (Expr.instSpine pre (rP - 1))` in the nested case). -/
structure PinsWalkOk (rP cnP : Nat) (pinsOf : List KExpr → List KExpr) : Prop where
  len : ∀ pre : List KExpr, pre.length = rP → (pinsOf pre).length = cnP
  erased : ∀ pre₁ pre₂ : List KExpr,
    pre₁.length = rP → pre₂.length = rP →
    (∀ (i : Nat) (a₁ a₂ : KExpr), pre₁[i]? = some a₁ → pre₂[i]? = some a₂ → Expr.ErasedEq a₁ a₂) →
    ∀ (j : Nat) (x₁ x₂ : KExpr),
      (pinsOf pre₁)[j]? = some x₁ → (pinsOf pre₂)[j]? = some x₂ → Expr.ErasedEq x₁ x₂
  wscoped : ∀ pre : List KExpr, pre.length = rP →
    (∀ a ∈ pre, Expr.WScoped rP a) →
    ∀ x ∈ pinsOf pre, Expr.WScoped rP x
  bounded : ∀ pre : List KExpr, pre.length = rP →
    (∀ a ∈ pre, a.looseBVarsBounded 0 = true) →
    ∀ x ∈ pinsOf pre, x.looseBVarsBounded 0 = true
  leaves : ∀ pre : List KExpr, pre.length = rP →
    ∀ x ∈ pinsOf pre, ∀ l ∈ x.fvarLeaves, ∃ a ∈ pre, l ∈ a.fvarLeaves

theorem pinsWalkOk_plain {rP cnP : Nat} (hcnP : cnP ≤ rP) :
    PinsWalkOk rP cnP (fun pre => pre.take cnP) where
  len pre hpre := by simp [hpre, hcnP]
  erased pre₁ pre₂ _ _ hpre j x₁ x₂ hx₁ hx₂ := by
    by_cases hj : j < cnP
    · rw [List.getElem?_take_of_lt hj] at hx₁ hx₂
      exact hpre j x₁ x₂ hx₁ hx₂
    · simp [List.getElem?_take, hj] at hx₁
  wscoped _ _ hws _ hx := hws _ (List.mem_of_mem_take hx)
  bounded _ _ hbnd _ hx := hbnd _ (List.mem_of_mem_take hx)
  leaves _ _ x hx l hl := ⟨x, List.mem_of_mem_take hx, hl⟩

theorem pinsWalkOk_nested {rP cnP : Nat} {pins : List KExpr}
    (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧ p.looseBVarsBounded rP = true) :
    PinsWalkOk rP cnP (fun pre => pins.map fun p => Expr.instSpine pre (rP - 1) p) where
  len _ _ := by simp [hpinsLen]
  erased pre₁ pre₂ hlen₁ hlen₂ hpre j x₁ x₂ hx₁ hx₂ := by
    rw [List.getElem?_map] at hx₁ hx₂
    rcases hp : pins[j]? with _ | p
    · simp [hp] at hx₁
    · simp only [hp, Option.map_some, Option.some.injEq] at hx₁ hx₂
      subst hx₁ hx₂
      exact instSpine_erasedEq pre₁ pre₂ (rP - 1) (Expr.ErasedEq.rfl p)
        (hlen₁.trans hlen₂.symm) hpre
  wscoped pre _ hws x hx := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact instSpine_WScoped (rP - 1) (Expr.WScoped.of_not_hasFvar (hpinsWf p hp).1) hws
  bounded pre hpre hbnd x hx := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have h := instSpine_closed (args := pre) (e := p) hbnd (by rw [hpre]; exact (hpinsWf p hp).2)
    rwa [hpre] at h
  leaves pre _ x hx l hl := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinsWf p hp).1] at hl'
      exact nomatch hl'
    · exact ⟨a, ha, hla⟩

/-- Unpack `LamTeleWalkJ` against the public frame `(fvsP ++ xFvsP)` into `openLamsAtFvars` plus
the `pdoms` scoping, leaf-closure, bound, and `ErasedEq` package consumed by `annotMem_lamWalk`. -/
theorem lamTeleWalk_unpack {J : Judgements .anon} {env : Env .anon}
    {rP cnP cnF : Nat} {tyA ctyInst rhsA : KExpr} {pinsOf : List KExpr → List KExpr}
    (hpinsOk : PinsWalkOk rP cnP pinsOf)
    (htyw : tyA.hasFvar = false) (htyb : tyA.looseBVarsBounded 0 = true)
    (hctyw : ctyInst.hasFvar = false) (hctyb : ctyInst.looseBVarsBounded 0 = true)
    (hrhsw : rhsA.hasFvar = false)
    {fvsP xFvsP cdomsP : List KExpr} {crest2 crestP ldoms : KExpr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, crest2))
    (hcinstP : Expr.instPisAt (pinsOf (fvsP.take rP)) ctyInst = some (cdomsP, crestP))
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    (hwalk : LamTeleWalkJ J env rP cnF tyA ctyInst pinsOf rhsA) :
    ∃ lfvs lrest pdoms,
      openLamsAtFvars (rP + cnF) rhsA 0 = some (lfvs, lrest) ∧
      pdoms.length = rP + cnF ∧
      (∀ (i : Nat) (x : KExpr), pdoms[i]? = some x → Expr.WScoped i x) ∧
      (∀ x ∈ pdoms, x.looseBVarsBounded 0 = true) ∧
      (∀ x ∈ pdoms, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ lfvs) ∧
      (∀ i, i < rP + cnF →
        Expr.ErasedEq (pdoms.getD i default)
          (Expr.fvarTypeD ((fvsP ++ xFvsP).getD i default))) ∧
      DefEqListJ J env (rP + cnF) (lfvs.map Expr.fvarTypeD) pdoms := by
  obtain ⟨lfvs, lrest, pdoms1, tyRest, cdomsL, crestL, pdoms2, crestEnd,
    hopLam, hinst1, hcinstL, hinst2, hdeLam⟩ := hwalk
  obtain ⟨hlfvsLen, -, hlfvsIdx⟩ := openLamsAtFvars_spec (rP + cnF) rhsA 0 hopLam
  obtain ⟨hLws, -⟩ := openLamsAtFvars_WScoped (rP + cnF) rhsA 0 hopLam
    (Expr.WScoped.of_not_hasFvar hrhsw)
  have hLleafClosed : ∀ l, (∃ x ∈ lfvs, l ∈ x.fvarLeaves) → Expr.fvar l.1 l.2 ∈ lfvs := by
    intro l ⟨x, hx, hlx⟩
    rcases openLamsAtFvars_leaves (rP + cnF) hopLam l (Or.inr ⟨x, hx, hlx⟩) with h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at h0
      exact nomatch h0
    · exact h0
  have hLshape : ∀ (i : Nat) (x : KExpr), lfvs[i]? = some x → ∃ ty, x = .fvar i ty := by
    intro i x hx
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx
    exact ⟨lfvs[i].fvarTypeD, by simpa using hlfvsIdx i hi⟩
  have hLbnd : ∀ a ∈ lfvs, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hLshape q a hq
    rfl
  have htkLlen : (lfvs.take rP).length = rP := by simp [hlfvsLen]
  have hdrLlen : (lfvs.drop rP).length = cnF := by simp [hlfvsLen]
  have hp1len : pdoms1.length = rP := by rw [instPisAt_length hinst1, htkLlen]
  have hp2len : pdoms2.length = cnF := by rw [instPisAt_length hinst2, hdrLlen]
  have htkLws_step : ∀ (i : Nat) (a : KExpr), (lfvs.take rP)[i]? = some a →
      Expr.WScoped (0 + i + 1) a := by
    intro i a ha
    have hi : i < rP := by
      have h := (List.getElem?_eq_some_iff.mp ha).1
      rwa [htkLlen] at h
    rw [List.getElem?_take_of_lt hi] at ha
    obtain ⟨ty, rfl⟩ := hLshape i a ha
    have hw := hLws _ (List.mem_of_getElem? ha)
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨by omega, hw.2⟩
  have htkLws_rP : ∀ a ∈ lfvs.take rP, Expr.WScoped rP a := by
    intro a ha
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
    have hi_lt : i < rP := by
      have h := (List.getElem?_eq_some_iff.mp hi).1
      rwa [htkLlen] at h
    exact (htkLws_step i a hi).mono (by omega)
  have hcrestL_ws : Expr.WScoped rP crestL :=
    (instPisAt_WScoped (d := rP) (pinsOf (lfvs.take rP)) ctyInst hcinstL
      (Expr.WScoped.of_not_hasFvar hctyw)
      (hpinsOk.wscoped (lfvs.take rP) htkLlen htkLws_rP)).2
  have hdrLws_step : ∀ (j : Nat) (a : KExpr), (lfvs.drop rP)[j]? = some a →
      Expr.WScoped (rP + j + 1) a := by
    intro j a ha
    rw [List.getElem?_drop] at ha
    obtain ⟨ty, rfl⟩ := hLshape (rP + j) a ha
    have hw := hLws _ (List.mem_of_getElem? ha)
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨by omega, hw.2⟩
  have hpdomsWS : ∀ (i : Nat) (x : KExpr), (pdoms1 ++ pdoms2)[i]? = some x → Expr.WScoped i x := by
    intro i x hx
    rcases Nat.lt_or_ge i rP with hi | hi
    · rw [List.getElem?_append_left (by omega)] at hx
      simpa using instPisAt_index_WScoped (lfvs.take rP) (d := 0) hinst1
        (Expr.WScoped.of_not_hasFvar htyw) htkLws_step i x hx
    · rw [List.getElem?_append_right (by omega), hp1len] at hx
      have h2 := instPisAt_index_WScoped (lfvs.drop rP) (d := rP) hinst2
        hcrestL_ws hdrLws_step (i - rP) x hx
      rwa [show rP + (i - rP) = i by omega] at h2
  have hp1bnd := (instPisAt_bounded (lfvs.take rP) hinst1 htyb
    (fun a ha => hLbnd a (List.mem_of_mem_take ha))).1
  have hcrestLbnd := (instPisAt_bounded (pinsOf (lfvs.take rP)) hcinstL hctyb
    (hpinsOk.bounded (lfvs.take rP) htkLlen
      (fun a ha => hLbnd a (List.mem_of_mem_take ha)))).2
  have hp2bnd := (instPisAt_bounded (lfvs.drop rP) hinst2 hcrestLbnd
    (fun a ha => hLbnd a (List.mem_of_mem_drop ha))).1
  have hpdomsBnd : ∀ x ∈ pdoms1 ++ pdoms2, x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hp1bnd x hx
    · exact hp2bnd x hx
  have hpdomsLeaves : ∀ x ∈ pdoms1 ++ pdoms2, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ lfvs := by
    intro x hx l hl
    rcases List.mem_append.mp hx with hx | hx
    · rcases instPisAt_leaves (lfvs.take rP) hinst1 l (Or.inl ⟨x, hx, hl⟩) with h0 | ⟨a, ha, hla⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h0
        exact nomatch h0
      · exact hLleafClosed l ⟨a, List.mem_of_mem_take ha, hla⟩
    · rcases instPisAt_leaves (lfvs.drop rP) hinst2 l (Or.inl ⟨x, hx, hl⟩) with h0 | ⟨a, ha, hla⟩
      · rcases instPisAt_leaves (pinsOf (lfvs.take rP)) hcinstL l (Or.inr h0) with
          h1 | ⟨pin, hpin, hlpin⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hctyw] at h1
          exact nomatch h1
        · obtain ⟨a, ha, hla⟩ := hpinsOk.leaves (lfvs.take rP) htkLlen pin hpin l hlpin
          exact hLleafClosed l ⟨a, List.mem_of_mem_take ha, hla⟩
      · exact hLleafClosed l ⟨a, List.mem_of_mem_drop ha, hla⟩
  -- Pointwise `ErasedEq` between `pdoms1 ++ pdoms2` and `(fvsP ++ xFvsP).map Expr.fvarTypeD`
  have hfvsPlen : fvsP.length = rP := Ix.Kernel.Model.openPisAtFvars_length _ hopenP
  have hxlen : xFvsP.length = cnF := Ix.Kernel.Model.openPisAtFvars_length _ hopenXP
  have hinstP1 : Expr.instPisAt fvsP tyA = some (fvsP.map Expr.fvarTypeD, crest2) :=
    openPisAtFvars_instPisAt _ hopenP
  have hinstP2 : Expr.instPisAt xFvsP crestP = some (xFvsP.map Expr.fvarTypeD, ldoms) :=
    openPisAtFvars_instPisAt _ hopenXP
  have hpre_erased : ∀ (i : Nat) (a₁ a₂ : KExpr),
      (lfvs.take rP)[i]? = some a₁ → fvsP[i]? = some a₂ → Expr.ErasedEq a₁ a₂ := by
    intro i a₁ a₂ ha₁ ha₂
    have hi : i < rP := by
      have h := (List.getElem?_eq_some_iff.mp ha₂).1
      rwa [hfvsPlen] at h
    rw [List.getElem?_take_of_lt hi] at ha₁
    obtain ⟨ty₁, rfl⟩ := hLshape i a₁ ha₁
    obtain ⟨ty₂, hp₂⟩ := openPisAtFvars_index _ _ _ hopenP i a₂ ha₂
    rw [Nat.zero_add] at hp₂; subst hp₂
    rfl
  obtain ⟨hds1, -⟩ := instPisAt_erasedEq (lfvs.take rP) fvsP hinst1 hinstP1
    (Expr.ErasedEq.rfl tyA) hpre_erased (htkLlen.trans hfvsPlen.symm)
  have htkPlen : (fvsP.take rP).length = rP := by simp [hfvsPlen]
  have hpre_take_erased : ∀ (i : Nat) (a₁ a₂ : KExpr),
      (lfvs.take rP)[i]? = some a₁ → (fvsP.take rP)[i]? = some a₂ → Expr.ErasedEq a₁ a₂ := by
    intro i a₁ a₂ ha₁ ha₂
    have hi : i < rP := by
      have h := (List.getElem?_eq_some_iff.mp ha₂).1
      rwa [htkPlen] at h
    rw [List.getElem?_take_of_lt hi] at ha₂
    exact hpre_erased i a₁ a₂ ha₁ ha₂
  obtain ⟨-, hcrest_erased⟩ := instPisAt_erasedEq
    (pinsOf (lfvs.take rP)) (pinsOf (fvsP.take rP)) hcinstL hcinstP
    (Expr.ErasedEq.rfl ctyInst)
    (hpinsOk.erased (lfvs.take rP) (fvsP.take rP) htkLlen htkPlen hpre_take_erased)
    ((hpinsOk.len (lfvs.take rP) htkLlen).trans (hpinsOk.len (fvsP.take rP) htkPlen).symm)
  have hflds_erased : ∀ (j : Nat) (a₁ a₂ : KExpr),
      (lfvs.drop rP)[j]? = some a₁ → xFvsP[j]? = some a₂ → Expr.ErasedEq a₁ a₂ := by
    intro j a₁ a₂ ha₁ ha₂
    rw [List.getElem?_drop] at ha₁
    obtain ⟨ty₁, rfl⟩ := hLshape (rP + j) a₁ ha₁
    obtain ⟨ty₂, rfl⟩ := openPisAtFvars_index _ _ _ hopenXP j a₂ ha₂
    rfl
  obtain ⟨hds2, -⟩ := instPisAt_erasedEq (lfvs.drop rP) xFvsP hinst2 hinstP2
    hcrest_erased hflds_erased (hdrLlen.trans hxlen.symm)
  refine ⟨lfvs, lrest, pdoms1 ++ pdoms2, hopLam, by rw [List.length_append, hp1len, hp2len],
    hpdomsWS, hpdomsBnd, hpdomsLeaves, ?_, hdeLam⟩
  intro i hi
  rcases Nat.lt_or_ge i rP with hi_rP | hi_rP
  · rcases hx₁ : pdoms1[i]? with _ | x₁
    · rw [List.getElem?_eq_none_iff, hp1len] at hx₁; omega
    rcases hx₂ : fvsP[i]? with _ | x₂
    · rw [List.getElem?_eq_none_iff, hfvsPlen] at hx₂; omega
    have hg1 : (pdoms1 ++ pdoms2).getD i default = x₁ := by
      rw [List.getD, List.getElem?_append_left (by omega), hx₁]; rfl
    have hg2 : (fvsP ++ xFvsP).getD i default = x₂ := by
      rw [List.getD, List.getElem?_append_left (by omega), hx₂]; rfl
    rw [hg1, hg2]
    exact hds1 i x₁ x₂.fvarTypeD hx₁ (by simp [List.getElem?_map, hx₂])
  · obtain ⟨j, rfl⟩ : ∃ j, i = rP + j := ⟨i - rP, by omega⟩
    have hj : j < cnF := by omega
    rcases hx₁ : pdoms2[j]? with _ | x₁
    · rw [List.getElem?_eq_none_iff, hp2len] at hx₁; omega
    rcases hx₂ : xFvsP[j]? with _ | x₂
    · rw [List.getElem?_eq_none_iff, hxlen] at hx₂; omega
    have hg1 : (pdoms1 ++ pdoms2).getD (rP + j) default = x₁ := by
      rw [List.getD, List.getElem?_append_right (by omega), hp1len, Nat.add_sub_cancel_left, hx₁]
      rfl
    have hg2 : (fvsP ++ xFvsP).getD (rP + j) default = x₂ := by
      rw [List.getD, List.getElem?_append_right (by omega), hfvsPlen, Nat.add_sub_cancel_left, hx₂]
      rfl
    rw [hg1, hg2]
    exact hds2 j x₁ x₂.fvarTypeD hx₁ (by simp [List.getElem?_map, hx₂])

/-! ## Prefix-Bounded `CtxOk` and `annotMem` / `annotTransport` / `annotOpeners` for `LamTeleWalkJ` -/

/-- Prefix-bounded variant of `ctxOk_of_walked_openers`: `hwalk` only needs to hold below `n`,
since every reachable leaf of `e` has index `< n`. -/
theorem ctxOk_of_walked_openers_lt {V : Type w} [Ix.Kernel.SetTheory V]
    {env : Env .anon} {m : EnvModel V env} {φ : LevelParam → Nat}
    {k n : Nat} {fvs : List KExpr} {Aa : Nat → AnnotTerm} {Δa : List AnnotTerm}
    (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : KExpr), fvs[i]? = some x → ∃ ty, x = .fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hwalk : ∀ (i : Nat) (x : KExpr), i < n → fvs[i]? = some x →
      ∃ tya, denoteMeta m.acval env φ k (Expr.fvarTypeD x) = some tya ∧
        (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ tya = interp V (fun j => ρ (j + (k - 1 - i) + 1)) (Aa i)) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ tya))
    {e : KExpr}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltE : ∀ l ∈ e.fvarLeaves, l.1 < n)
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i)) :
    CtxOk m φ k Δa e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  have hmem := hleaf l hl
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
  obtain ⟨ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2⟩ : l.1 = pos ∧ l.2 = ty := by
    injection hx with a b
    exact ⟨a, b⟩
  subst h1 h2
  have hlt : l.1 < n := hltE l hl
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2 := by
    simpa [Expr.WScoped] using hw
  obtain ⟨tya, htya, heq, hok⟩ := hwalk l.1 _ hlt hpos
  rw [show Expr.fvarTypeD (.fvar l.1 l.2) = l.2 from rfl] at htya
  exact ⟨hwty.1, hwty.2.fvarsBelow, tya, Aa l.1, htya, hent l.1 hlt, heq, hok⟩

set_option maxHeartbeats 6400000 in
/-- Layer-membership identification along a `defeq_lam_tele` walk (`annotMem`'s VM counterpart). -/
theorem annotMem_lamWalk {V : Type w} [Ix.Kernel.SetTheory V]
    {env : Env .anon} {φ : LevelParam → Nat} {m : EnvModel V env} {J : Judgements .anon}
    (hclaims : DefEqClaimJ J m φ)
    {K : Nat}
    {pfvs : List KExpr}
    {Γs : List AnnotTerm} {Δa : List AnnotTerm} (hΔalen : Δa.length = K)
    (hΔaent : ∀ i, i < K → Δa[K - 1 - i]? = some (Γs.getD (K - 1 - i) default))
    (hIdent : ∀ i, i < K → ∃ Bi : AnnotTerm,
      denoteMeta m.acval env φ K (Expr.fvarTypeD (pfvs.getD i default)) = some Bi ∧
      ∀ ρ' : Nat → V, Sat V Δa ρ' →
        WellDenotedV V ρ' Bi ∧
          interp V (fun j => ρ' (j + (K - i))) (Γs.getD (K - 1 - i) default) = interp V ρ' Bi)
    {rhsA : KExpr} (hrhsw : rhsA.hasFvar = false) (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {Ra : AnnotTerm} (hokRa : ∀ σ : Nat → V, WellDenotedV V σ Ra)
    {lfvs : List KExpr} {lrest : KExpr}
    (hopLam : openLamsAtFvars K rhsA 0 = some (lfvs, lrest))
    {Γlam : List AnnotTerm} {C : AnnotTerm} (htowerLam : LamTele K Ra Γlam C)
    (hdomsLam : ∀ (i : Nat) (x : KExpr), (lfvs.map Expr.fvarTypeD)[i]? = some x →
      denoteMeta m.acval env φ i x = some (Γlam.getD (K - 1 - i) default))
    {pdoms : List KExpr}
    (hpdomsLen : pdoms.length = K)
    (hpdomsWS : ∀ (i : Nat) (x : KExpr), pdoms[i]? = some x → Expr.WScoped i x)
    (hpdomsBnd : ∀ x ∈ pdoms, x.looseBVarsBounded 0 = true)
    (hpdomsLeaves : ∀ x ∈ pdoms, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ lfvs)
    (hpdomsErased : ∀ i, i < K →
      Expr.ErasedEq (pdoms.getD i default) (Expr.fvarTypeD (pfvs.getD i default)))
    (hdeLam : DefEqListJ J env K (lfvs.map Expr.fvarTypeD) pdoms) :
    ∀ k, k < K → ∀ ρ' : Nat → V, Sat V Δa ρ' →
      WellDenotedV V (fun j => ρ' (j + (K - k))) (Γlam.getD (K - 1 - k) default) ∧
        interp V (fun j => ρ' (j + (K - k))) (Γs.getD (K - 1 - k) default)
          = interp V (fun j => ρ' (j + (K - k))) (Γlam.getD (K - 1 - k) default) := by
  obtain ⟨hlfvsLen, -, hlfvsIdx⟩ := openLamsAtFvars_spec K rhsA 0 hopLam
  obtain ⟨hLws, -⟩ := openLamsAtFvars_WScoped K rhsA 0 hopLam (Expr.WScoped.of_not_hasFvar hrhsw)
  rw [Nat.zero_add] at hLws
  have hLshape : ∀ (i : Nat) (x : KExpr), lfvs[i]? = some x → ∃ ty, x = .fvar i ty := by
    intro i x hx
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx
    exact ⟨lfvs[i].fvarTypeD, by simpa using hlfvsIdx i hi⟩
  have hLleafClosed : ∀ l, (∃ x ∈ lfvs, l ∈ x.fvarLeaves) → Expr.fvar l.1 l.2 ∈ lfvs := by
    intro l ⟨x, hx, hlx⟩
    rcases openLamsAtFvars_leaves K hopLam l (Or.inr ⟨x, hx, hlx⟩) with h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at h0
      exact nomatch h0
    · exact h0
  have hlbL : ∀ (i : Nat) (ty : KExpr), Expr.fvar i ty ∈ lfvs →
      ty.looseBVarsBounded 0 = true := by
    intro i ty hmem
    exact (openLamsAtFvars_bounded K hopLam hrhsb).2 (.fvar i ty) hmem
  have hshiftEnv : ∀ (d : Nat) (ρ0 : Nat → V),
      shiftE d 0 ρ0 = (fun j => ρ0 (j + d)) := by
    intro d ρ0
    funext j
    show (if j < 0 then ρ0 j else ρ0 (j + d)) = _
    simp only [Nat.not_lt_zero, ↓reduceIte]
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
    intro hkK
    have hgrall : ∀ ρ0 : Nat → V, Sat V Δa ρ0 →
        WellDenotedV V (fun j => ρ0 (j + (K - k))) (Γlam.getD (K - 1 - k) default) := by
      intro ρ0 hρ0
      refine cast ?_ (wellDenotedV_lamTower_slot K htowerLam (ρ' := ρ0)
        (hokRa _) (K - 1 - k) (by omega) (fun q hq1 hq2 => ?_))
      · congr 1; funext j; congr 1; omega
      · obtain ⟨-, heq⟩ := ihk (K - 1 - q) (by omega) (by omega) ρ0 hρ0
        have hsatm := hρ0 q (Γs.getD q default) (by
          have h := hΔaent (K - 1 - q) (by omega)
          rw [show K - 1 - (K - 1 - q) = q from by omega] at h
          exact h)
        show ρ0 q ∈ˢ interp V (fun j => ρ0 (j + q + 1)) (Γlam.getD q default)
        rw [show Γlam.getD q default = Γlam.getD (K - 1 - (K - 1 - q)) default from by
              congr 1; omega,
          show (fun j => ρ0 (j + q + 1)) = (fun j => ρ0 (j + (K - (K - 1 - q)))) from by
            funext j; congr 1; omega,
          ← heq,
          show Γs.getD (K - 1 - (K - 1 - q)) default = Γs.getD q default from by
            congr 1; omega,
          show (fun j => ρ0 (j + (K - (K - 1 - q)))) = (fun j => ρ0 (j + q + 1)) from by
            funext j; congr 1; omega]
        exact hsatm
    intro ρ' hρ'
    refine ⟨hgrall ρ' hρ', ?_⟩
    -- Prefix walk on `lfvs` for positions `i < k`, supplied by `ihk`
    have hwalk_lt : ∀ (i : Nat) (x : KExpr), i < k → lfvs[i]? = some x →
        ∃ tya, denoteMeta m.acval env φ K (Expr.fvarTypeD x) = some tya ∧
          (∀ ρ : Nat → V, Sat V Δa ρ →
            interp V ρ tya
              = interp V (fun j => ρ (j + (K - 1 - i) + 1)) (Γs.getD (K - 1 - i) default)) ∧
          (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ tya) := by
      intro i x hi hx
      obtain ⟨ty_i, rfl⟩ := hLshape i x hx
      have hw_i : Expr.WScoped i ty_i := by
        have hw := hLws _ (List.mem_of_getElem? hx)
        simp only [Expr.WScoped] at hw
        exact hw.2
      have hden_i : denoteMeta m.acval env φ i ty_i = some (Γlam.getD (K - 1 - i) default) :=
        hdomsLam i ty_i (by simp [List.getElem?_map, hx, Expr.fvarTypeD])
      have hlift_i : denoteMeta m.acval env φ K ty_i
          = some ((Γlam.getD (K - 1 - i) default).liftN (K - i) 0) := by
        rw [denoteMeta_lift m.acval_closed hw_i K (by omega), hden_i]
        rfl
      refine ⟨(Γlam.getD (K - 1 - i) default).liftN (K - i) 0, hlift_i, ?_, ?_⟩
      · intro ρ hρ
        obtain ⟨-, heq_i⟩ := ihk i hi (by omega) ρ hρ
        rw [interp_liftN, hshiftEnv (K - i) ρ, ← heq_i]
        congr 1; funext j; congr 1; omega
      · intro ρ hρ
        obtain ⟨hok_i, -⟩ := ihk i hi (by omega) ρ hρ
        exact (WellDenotedV_liftN V (K - i) _ 0 ρ).mpr (by rw [hshiftEnv (K - i) ρ]; exact hok_i)
    -- Comparands at position `k`: `lk = ty_k` (from `lfvs[k]`) and `pk` (from `pdoms[k]`)
    obtain ⟨Bk, hBk, hBkP⟩ := hIdent k hkK
    rcases hlk : lfvs[k]? with _ | lfv_k
    · rw [List.getElem?_eq_none_iff, hlfvsLen] at hlk; omega
    obtain ⟨lk, rfl⟩ := hLshape k lfv_k hlk
    rcases hpk : pdoms[k]? with _ | pk
    · rw [List.getElem?_eq_none_iff, hpdomsLen] at hpk; omega
    have hrun : J.defeq env K lk pk :=
      hdeLam.pointwise k (by simp [List.getElem?_map, hlk, Expr.fvarTypeD]) hpk
    have hmemLk : Expr.fvar k lk ∈ lfvs := List.mem_of_getElem? hlk
    have hwsLk : Expr.WScoped k lk := by
      have hw := hLws _ hmemLk
      simp only [Expr.WScoped] at hw
      exact hw.2
    have hwsPk : Expr.WScoped k pk := hpdomsWS k pk hpk
    have hleafLk : ∀ l ∈ lk.fvarLeaves, Expr.fvar l.1 l.2 ∈ lfvs := fun l hl =>
      hLleafClosed l ⟨.fvar k lk, hmemLk, by rw [Expr.fvarLeaves]; exact List.mem_cons_of_mem _ hl⟩
    have hleafPk : ∀ l ∈ pk.fvarLeaves, Expr.fvar l.1 l.2 ∈ lfvs :=
      hpdomsLeaves pk (List.mem_of_getElem? hpk)
    have hbLk : lk.looseBVarsBounded 0 = true := hlbL k lk hmemLk
    have hbPk : pk.looseBVarsBounded 0 = true := hpdomsBnd pk (List.mem_of_getElem? hpk)
    have hctxLk : CtxOk m φ K Δa lk :=
      ctxOk_of_walked_openers_lt (m := m) (n := k) hΔalen hLshape hLws hwalk_lt
        hleafLk (Expr.fvarLeaves_lt_of_wscoped hwsLk) (fun i hi => hΔaent i (by omega))
    have hctxPk : CtxOk m φ K Δa pk :=
      ctxOk_of_walked_openers_lt (m := m) (n := k) hΔalen hLshape hLws hwalk_lt
        hleafPk (Expr.fvarLeaves_lt_of_wscoped hwsPk) (fun i hi => hΔaent i (by omega))
    have hLkden : denoteMeta m.acval env φ K lk
        = some ((Γlam.getD (K - 1 - k) default).liftN (K - k) 0) := by
      rw [denoteMeta_lift m.acval_closed hwsLk K (by omega),
        hdomsLam k lk (by simp [List.getElem?_map, hlk, Expr.fvarTypeD])]
      rfl
    have hPkden : denoteMeta m.acval env φ K pk = some Bk := by
      have her := hpdomsErased k hkK
      rw [List.getD, hpk] at her
      exact (denoteMeta_erasedEq her K).trans hBk
    have hfire := hclaims hrun
      (hwsLk.mono (by omega)) hbLk (fun l hl => hlbL l.1 l.2 (hleafLk l hl))
      (hwsPk.mono (by omega)) hbPk (fun l hl => hlbL l.1 l.2 (hleafPk l hl))
      hctxLk hctxPk hLkden hPkden
      (fun ρ0 hρ0 => (WellDenotedV_liftN V (K - k) _ 0 ρ0).mpr (by
        rw [hshiftEnv (K - k) ρ0]; exact hgrall ρ0 hρ0))
      (fun ρ0 hρ0 => (hBkP ρ0 hρ0).1)
      ρ' hρ'
    rw [interp_liftN, hshiftEnv (K - k) ρ'] at hfire
    rw [(hBkP ρ' hρ').2, ← hfire]

set_option maxHeartbeats 3200000 in
/-- Truthfulness transport along a `LamTeleWalkJ` (`annotTransport`'s VM counterpart). -/
theorem annotTransport_lamWalk {V : Type w} [Ix.Kernel.SetTheory V]
    {env : Env .anon} {φ : LevelParam → Nat} {m : EnvModel V env} {J : Judgements .anon}
    (hclaims : DefEqClaimJ J m φ)
    {rP cnP cnF : Nat}
    {tyA ctyInst : KExpr} {pinsOf : List KExpr → List KExpr}
    (hpinsOk : PinsWalkOk rP cnP pinsOf)
    (htyw : tyA.hasFvar = false) (htyb : tyA.looseBVarsBounded 0 = true)
    (hctyw : ctyInst.hasFvar = false) (hctyb : ctyInst.looseBVarsBounded 0 = true)
    {fvsP xFvsP cdomsP : List KExpr} {crest2 crestP ldoms : KExpr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, crest2))
    (hcinstP : Expr.instPisAt (pinsOf (fvsP.take rP)) ctyInst = some (cdomsP, crestP))
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    {Γs : List AnnotTerm} {Δa : List AnnotTerm} (hΔalen : Δa.length = rP + cnF)
    (hΔaent : ∀ i, i < rP + cnF →
      Δa[rP + cnF - 1 - i]? = some (Γs.getD (rP + cnF - 1 - i) default))
    (hIdent : ∀ i, i < rP + cnF → ∃ Bi : AnnotTerm,
      denoteMeta m.acval env φ (rP + cnF)
        (Expr.fvarTypeD ((fvsP ++ xFvsP).getD i default)) = some Bi ∧
      ∀ ρ' : Nat → V, Sat V Δa ρ' →
        WellDenotedV V ρ' Bi ∧
          interp V (fun j => ρ' (j + (rP + cnF - i)))
              (Γs.getD (rP + cnF - 1 - i) default) = interp V ρ' Bi)
    {rhsA : KExpr} (hrhsw : rhsA.hasFvar = false) (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {Ra : AnnotTerm} (hRa : denoteMeta m.acval env φ 0 rhsA = some Ra)
    (hokRa : ∀ σ : Nat → V, WellDenotedV V σ Ra)
    (hwalk : LamTeleWalkJ J env rP cnF tyA ctyInst pinsOf rhsA)
    {zs : List AnnotTerm} {ρ : Nat → V} (hzslen : zs.length = rP + cnF)
    (hsat : Sat V Δa (chain V ρ zs))
    (hmemZ : ∀ k, k < rP + cnF →
      interp V ρ (zs.getD k default)
        ∈ˢ interp V (chain V ρ (zs.take k)) (Γs.getD (rP + cnF - 1 - k) default))
    (hzsAnnot : ∀ w ∈ zs, WellDenotedV V ρ w) :
    WellDenotedV V ρ (AnnotTerm.mkAppN Ra zs) := by
  let K := rP + cnF
  obtain ⟨lfvs, lrest, pdoms, hopLam, hpdomsLen, hpdomsWS, hpdomsBnd,
    hpdomsLeaves, hpdomsErased, hdeLam⟩ :=
    lamTeleWalk_unpack hpinsOk htyw htyb hctyw hctyb hrhsw hopenP hcinstP hopenXP hwalk
  obtain ⟨hlfvsLen, hinstLamLfvs, hlfvsIdx⟩ := openLamsAtFvars_spec K rhsA 0 hopLam
  obtain ⟨Γlam, C, htowerLam, hΓlamLen, -, hdoms⟩ :=
    instLamsAt_denotePTele (acval := m.acval) (env := env) (φ := φ)
      lfvs hinstLamLfvs
      (fun i x hx => by
        obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx
        exact ⟨lfvs[i].fvarTypeD, by simpa using hlfvsIdx i hi⟩) hRa
  rw [hlfvsLen] at htowerLam hΓlamLen
  have hdomsLam : ∀ (i : Nat) (x : KExpr), (lfvs.map Expr.fvarTypeD)[i]? = some x →
      denoteMeta m.acval env φ i x = some (Γlam.getD (K - 1 - i) default) := by
    intro i x hx
    have h := hdoms i x hx
    rwa [Nat.zero_add, hlfvsLen] at h
  have hmemLam : ∀ k, k < K →
      interp V ρ (zs.getD k default)
        ∈ˢ interp V (chain V ρ (zs.take k)) (Γlam.getD (K - 1 - k) default) := by
    intro k hk
    have henvk : (fun j => (chain V ρ zs) (j + (K - k))) = chain V ρ (zs.take k) := by
      have h := chain_tail (V := V) (ρ := ρ) (ws := zs) (i := K - 1 - k)
        (by rw [hzslen]; omega)
      rw [hzslen] at h
      rw [show K - 1 - (K - 1 - k) = k from by omega] at h
      rw [← h]
      funext j; congr 1; omega
    obtain ⟨-, heq⟩ := annotMem_lamWalk hclaims hΔalen hΔaent hIdent hrhsw hrhsb hokRa
      hopLam htowerLam hdomsLam hpdomsLen hpdomsWS hpdomsBnd hpdomsLeaves hpdomsErased hdeLam
      k hk (chain V ρ zs) hsat
    rw [henvk] at heq
    rw [← heq]
    exact hmemZ k hk
  obtain ⟨-, -, -, -, hok⟩ := lamTowerStep (V := V) (C := C) K
    (Nat.le_refl _) htowerLam hzslen hmemLam (hokRa ρ)
  have hok' := hok hzsAnnot
  rwa [show zs.take K = zs from List.take_of_length_le (Nat.le_of_eq hzslen)] at hok'

set_option maxHeartbeats 3200000 in
/-- Applied reduct graded at the statement frame's own openers along `LamTeleWalkJ`
(`annotOpeners`'s VM counterpart). -/
theorem annotOpeners_lamWalk {V : Type w} [Ix.Kernel.SetTheory V]
    {env : Env .anon} {φ : LevelParam → Nat} {m : EnvModel V env} {J : Judgements .anon}
    (hclaims : DefEqClaimJ J m φ)
    {f : Key .anon → Key .anon} (hroT : RenameOk m.acval env f)
    {rP cnP cnF : Nat}
    -- statement frame and its tower
    {fvs : List KExpr} (hfvslen : fvs.length = rP + cnF)
    (hshapeS : ∀ (i : Nat) (x : KExpr), fvs[i]? = some x → ∃ ty, x = .fvar i ty)
    (hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x)
    (hlbFvs : ∀ (i : Nat) (ty : KExpr), Expr.fvar i ty ∈ fvs → ty.looseBVarsBounded 0 = true)
    {Γs : List AnnotTerm} (hΓslen : Γs.length = rP + cnF)
    (hdomsS0 : ∀ (i : Nat) (x : KExpr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x) = some (Γs.getD (rP + cnF - 1 - i) default))
    (hΔaent : ∀ i, i < rP + cnF →
      Γs[rP + cnF - 1 - i]? = some (Γs.getD (rP + cnF - 1 - i) default))
    -- public frame and `LamTeleWalkJ`
    {tyA ctyInst : KExpr} {pinsOf : List KExpr → List KExpr}
    (hpinsOk : PinsWalkOk rP cnP pinsOf)
    (htyw : tyA.hasFvar = false) (htyb : tyA.looseBVarsBounded 0 = true)
    (hctyw : ctyInst.hasFvar = false) (hctyb : ctyInst.looseBVarsBounded 0 = true)
    {fvsP xFvsP cdomsP : List KExpr} {crest2 crestP ldoms : KExpr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, crest2))
    (hcinstP : Expr.instPisAt (pinsOf (fvsP.take rP)) ctyInst = some (cdomsP, crestP))
    (hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    (hIdent : ∀ i, i < rP + cnF → ∃ Bi : AnnotTerm,
      denoteMeta m.acval env φ (rP + cnF)
        (Expr.fvarTypeD ((fvsP ++ xFvsP).getD i default)) = some Bi ∧
      ∀ ρ' : Nat → V, Sat V Γs ρ' →
        WellDenotedV V ρ' Bi ∧
          interp V (fun j => ρ' (j + (rP + cnF - i)))
              (Γs.getD (rP + cnF - 1 - i) default) = interp V ρ' Bi)
    {rhsA : KExpr} (hrhsw : rhsA.hasFvar = false) (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {Ra : AnnotTerm} (hRa : denoteMeta m.acval env φ 0 rhsA = some Ra)
    (hokRa : ∀ σ : Nat → V, WellDenotedV V σ Ra)
    (hwalk : LamTeleWalkJ J env rP cnF tyA ctyInst pinsOf rhsA) :
    ∀ σ : Nat → V, Sat V Γs σ → ∀ ba : AnnotTerm,
      denoteMeta m.acval env φ (rP + cnF) (Expr.mkAppN (rhsA.renameConsts f) fvs) = some ba →
      WellDenotedV V σ ba := by
  let K := rP + cnF
  have hΓsBnd : ∀ mIdx, mIdx < K →
      Term.bvarsBelow mIdx (Γs.getD (K - 1 - mIdx) default).erase := by
    intro mIdx hmIdx
    rcases hx : fvs[mIdx]? with _ | x
    · rw [List.getElem?_eq_none_iff, hfvslen] at hx; omega
    obtain ⟨ty, rfl⟩ := hshapeS mIdx x hx
    have hmem := List.mem_of_getElem? hx
    have hws : Expr.WScoped mIdx ty := by
      have h := hwsFvs _ hmem
      simp only [Expr.WScoped] at h
      exact h.2
    exact denote_bvarsBelow m.cval_closed mIdx ty hws (hlbFvs mIdx ty hmem)
      (denoteMeta_erase m.acval_erase mIdx ty (hdomsS0 mIdx _ hx))
  obtain ⟨bvs, hbvslen, hbvsel⟩ : ∃ bvs : List AnnotTerm,
      bvs.length = K ∧ ∀ k, k < K → bvs[k]? = some (AnnotTerm.bvar (K - 1 - k)) := by
    refine ⟨(List.range K).map (fun j => AnnotTerm.bvar (K - 1 - j)),
      by rw [List.length_map, List.length_range], fun k hk => ?_⟩
    rw [List.getElem?_map, List.getElem?_range hk]; rfl
  have hbvsgetD : ∀ k, k < K → bvs.getD k default = AnnotTerm.bvar (K - 1 - k) := by
    intro k hk; rw [List.getD, hbvsel k hk]; rfl
  have hspBvs : DenoteMetaSpine m.acval env φ K fvs bvs := by
    refine DenoteMetaSpine.of_getD fvs bvs (by rw [hfvslen, hbvslen]) ?_
    intro q hq
    rw [hfvslen] at hq
    rcases hx : fvs[q]? with _ | x
    · rw [List.getElem?_eq_none_iff, hfvslen] at hx; omega
    obtain ⟨ty, rfl⟩ := hshapeS q x hx
    rw [show fvs.getD q default = .fvar q ty from by rw [List.getD, hx]; rfl, hbvsgetD q hq]
    exact denoteMeta_fvar m.acval K q ty
  have hchainbvs : ∀ (τ : Nat → V) (i : Nat), i < K → chain V τ bvs i = τ i := by
    intro τ i hi
    rw [chain_lt (by rw [hbvslen]; exact hi), hbvslen,
      hbvsgetD (K - 1 - i) (by omega), show K - 1 - (K - 1 - i) = i from by omega]
    rfl
  have hRacl : ∀ k : Nat, Ra.liftN 1 k = Ra := fun k =>
    denoteMeta_closed m.acval_erase m.cval_closed hrhsw hrhsb hRa 1 k
  have hrhsRw : (rhsA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]; exact hrhsw
  have hRaK : denoteMeta m.acval env φ K (rhsA.renameConsts f) = some Ra := by
    refine denoteMeta_depth_of_closed m.acval_closed hrhsRw hRacl ?_ K
    rw [denoteMeta_renameConsts hroT]
    exact hRa
  have hbaEq : denoteMeta m.acval env φ K (Expr.mkAppN (rhsA.renameConsts f) fvs)
      = some (AnnotTerm.mkAppN Ra bvs) := denoteMeta_mkAppN_of fvs hRaK hspBvs
  intro σ hσ ba hba
  obtain rfl : ba = AnnotTerm.mkAppN Ra bvs := Option.some.inj (hba.symm.trans hbaEq)
  have hsatB : Sat V Γs (chain V σ bvs) := by
    intro i Aa hi
    have hiK : i < K := by
      rcases Nat.lt_or_ge i K with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hΓslen]; omega)] at hi
        exact nomatch hi
    obtain rfl : Aa = Γs.getD i default := by rw [List.getD, hi]; rfl
    have hbnd : Term.bvarsBelow (K - 1 - i) (Γs.getD i default).erase := by
      have h := hΓsBnd (K - 1 - i) (by omega)
      rwa [show K - 1 - (K - 1 - i) = i from by omega] at h
    rw [hchainbvs σ i hiK,
      interp_congr_below V (Γs.getD i default) (K - 1 - i)
        (fun j => chain V σ bvs (j + i + 1)) (fun j => σ (j + i + 1))
        hbnd (fun j hj => hchainbvs σ (j + i + 1) (by omega))]
    exact hσ i _ hi
  have hmemZB : ∀ k, k < K →
      interp V σ (bvs.getD k default)
        ∈ˢ interp V (chain V σ (bvs.take k)) (Γs.getD (K - 1 - k) default) := by
    intro k hk
    have htklen : (bvs.take k).length = k := by rw [List.length_take, hbvslen]; omega
    rw [hbvsgetD k hk]
    show σ (K - 1 - k) ∈ˢ _
    rw [interp_congr_below V (Γs.getD (K - 1 - k) default) k
      (chain V σ (bvs.take k)) (fun j => σ (j + (K - 1 - k) + 1)) (hΓsBnd k hk)
      (fun j hj => by
        rw [chain_lt (by rw [htklen]; omega), htklen,
          show (bvs.take k).getD (k - 1 - j) default
            = AnnotTerm.bvar (K - 1 - (k - 1 - j)) from by
            rw [List.getD, List.getElem?_take_of_lt (by omega),
              hbvsel (k - 1 - j) (by omega)]
            rfl]
        show σ (K - 1 - (k - 1 - j)) = σ (j + (K - 1 - k) + 1)
        congr 1; omega)]
    exact hσ (K - 1 - k) _ (hΔaent k hk)
  exact annotTransport_lamWalk hclaims hpinsOk htyw htyb hctyw hctyb hopenP hcinstP hopenXP
    hΓslen hΔaent hIdent hrhsw hrhsb hRa hokRa hwalk hbvslen hsatB hmemZB
    (fun w hw => by
      obtain ⟨q, hq⟩ := List.getElem?_of_mem hw
      have hqlt : q < K := by
        have := (List.getElem?_eq_some_iff.mp hq).1
        rwa [hbvslen] at this
      rw [hbvsel q hqlt] at hq
      obtain rfl : w = AnnotTerm.bvar (K - 1 - q) := (Option.some.inj hq).symm
      exact ⟨by simp, by simp⟩)

/-! ## VM Modeled-Inductive Judgement Records and `.toTrivDefEq` Projection -/

/-- `IotaRunsJ` without the redundant `lamL`/`lamR` field (carried by `LamTeleWalkJ` instead). -/
def IotaRunsVmJ (J : Judgements .anon) (envSelf : Env .anon) (depth : Nat)
    (idxL idxR domL domR preL preR : List KExpr)
    (rhsS rhsApplied alphaS lhsS : KExpr) : Prop :=
  DefEqListJ J envSelf depth idxL idxR ∧
  DefEqListJ J envSelf depth domL domR ∧
  DefEqListJ J envSelf depth preL preR ∧
  J.defeq envSelf depth rhsS rhsApplied ∧
  (∃ tl, J.infer envSelf depth lhsS tl ∧ J.defeq envSelf depth tl alphaS) ∧
  (∃ tr, J.infer envSelf depth rhsS tr ∧ J.defeq envSelf depth tr alphaS)

/-- Canonical `iota` theorem run record using `LamTeleWalkJ`. -/
def IotaThmVmRunJ (J : Judgements .anon) (env' envSelf : Env .anon)
    (f : Key .anon → Key .anon) (cvName : Key .anon)
    (lps : List LevelParam) (tyA : KExpr) (mI rP j : Nat) (r : RecRule .anon)
    (cvj : ConstantVal .anon) (cnP cnF : Nat) (rhsA : KExpr) : Prop :=
  ∃ cvt fvs tbody,
    env'.findCV? (auxKey (auxKey cvName .model) (.iota j)) = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     (largs.getLastD (.bvar 0) == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs)) = true ∧
     Expr.ctorTeleOk cvj.type (cnP + cnF) = true ∧
     ∃ cdoms cres rdoms fvsP cdomsP crestP xFvsP crest2 ldoms lrest,
       Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f)
         = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       Expr.instPisAt (fvsP.take cnP) cvj.type = some (cdomsP, crestP) ∧
       openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
       LamTeleWalkJ J envSelf rP cnF tyA cvj.type (fun pre => pre.take cnP) rhsA ∧
       DefEqListJ J envSelf depth ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP ∧
       IotaRunsVmJ J envSelf depth
         ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
         (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
         ((fvs.take rP).map Expr.fvarTypeD) rdoms
         rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
         (targs.getD 0 (.bvar 0)) lhsS)

/-- Nested `iota` theorem run record using `LamTeleWalkJ`. -/
def IotaThmNVmRunJ (J : Judgements .anon) (env' envSelf : Env .anon)
    (f : Key .anon → Key .anon) (cvName : Key .anon)
    (lps : List LevelParam) (tyA : KExpr) (mI rP j : Nat) (r : RecRule .anon)
    (cvj : ConstantVal .anon) (cnP cnF : Nat) (rhsA : KExpr)
    (lvls : List Level) (pins : List KExpr) : Prop :=
  nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j = some (lvls, pins) ∧
  ∃ cvt fvs tbody,
    env'.findCV? (auxKey (auxKey cvName .model) (.iota j)) = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let pinsF := pins.map fun p =>
       Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     Expr.ErasedEq (largs.getLastD (.bvar 0))
       (Expr.mkAppN (.const (f r.ctor) lvls) (pinsF ++ xFvs)) ∧
     (∃ cbinders cbody0 Dc usc, cvj.type.stripPis (cnP + cnF) = some (cbinders, cbody0) ∧
       cbody0.getAppFn = .const Dc usc) ∧
     ∃ cdoms cres rdoms lrest fvsP crest2 cdomsP crestP xFvsP ldoms,
       Expr.instPisAt (pinsF ++ xFvs)
         ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts f)
         = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       (let pinsP := pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p
        Expr.instPisAt pinsP (cvj.type.instantiateLevelParams cvj.levelParams lvls)
          = some (cdomsP, crestP) ∧
        openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
        (ldoms.getAppArgs.length == cnP + (mI - rP)) = true) ∧
       LamTeleWalkJ J envSelf rP cnF tyA
         (cvj.type.instantiateLevelParams cvj.levelParams lvls)
         (fun pre => pins.map fun p => Expr.instSpine pre (rP - 1) p) rhsA ∧
       TypedListJ J envSelf depth
         (pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP ∧
       IotaRunsVmJ J envSelf depth
         ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
         (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
         ((fvs.take rP).map Expr.fvarTypeD) rdoms
         rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
         (targs.getD 0 (.bvar 0)) lhsS)

/-- Single `iota` rule run record using `IotaThmVmRunJ` / `IotaThmNVmRunJ`. -/
def IotaRuleVmRunJ (J : Judgements .anon) (env' envSelf : Env .anon)
    (f : Key .anon → Key .anon) (cvName : Key .anon)
    (lps : List LevelParam) (tyA : KExpr) (mI rP j : Nat) (r r' : RecRule .anon) : Prop :=
  ∃ cvj cnP cnF rhsA,
    env'.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
    r.nfields = cnF ∧
    r.rhs.looseBVarsBounded 0 = true ∧
    r.rhs.hasFvar = false ∧
    J.annot envSelf 0 r.rhs rhsA ∧
    rhsA.allLevelParamsDefined lps = true ∧
    rhsA.constsResolve envSelf = true ∧
    (rhsA.stripLams (rP + cnF)).isSome = true ∧
    (∃ t', J.infer envSelf 0 rhsA t') ∧
    ∃ fire,
      r' = recRuleBits env'.find? cvName
        { r with rhs := rhsA, ctorParams := cnP, fire := fire, paramsBlind := false } ∧
      ((Expr.recRulePlain tyA mI rP cnP cvj.levelParams = true ∧ fire = .plain ∧
          IotaThmVmRunJ J env' envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA) ∨
       (Expr.recRulePlain tyA mI rP cnP cvj.levelParams = false ∧
          ∃ lvls pins, fire = .nested lvls pins ∧
            IotaThmNVmRunJ J env' envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA lvls pins))

/-- Rule list run record over `IotaRuleVmRunJ`. -/
def IotaRulesVmRunJ (J : Judgements .anon) (env' envSelf : Env .anon)
    (f : Key .anon → Key .anon) (cvName : Key .anon)
    (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat) :
    Nat → List (RecRule .anon) → List (RecRule .anon) → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleVmRunJ J env' envSelf f cvName lps tyA mI rP j r r' ∧
      IotaRulesVmRunJ J env' envSelf f cvName lps tyA mI rP (j + 1) rest rest' ∧
      out = r' :: rest'

/-- Recursor-group install fold over `IotaRulesVmRunJ`. -/
def IndRecsFoldVmRunJ (J : Judgements .anon) (blockNames : List KKey)
    (envBase envSelf : Env .anon) :
    Env .anon → List (ConstantVal .anon × Nat × Nat × List (RecRule .anon)) → Env .anon → Prop
  | acc, [], out => out = acc
  | acc, c :: rest, out =>
    ∃ rules',
      IotaRulesVmRunJ J envBase envSelf
        (fun n => if blockNames.contains n then auxKey n .model else n)
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2 rules' ∧
      IndRecsFoldVmRunJ J blockNames envBase envSelf
        ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-- Recursor-group phase over `IndRecsFoldVmRunJ`. -/
def IndRecsVmRunJ (J : Judgements .anon)
    (blockNames : List KKey) (env₂ : Env .anon)
    (recs : List (ConstantInfo .anon)) (env₃ : Env .anon) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf checked,
     ProvisionRecsRunJ J blockNames env₂ recs envSelf checked ∧
     IndRecsFoldVmRunJ J blockNames env₂ envSelf env₂ checked env₃)

/-- Whether a `ConstantInfo` entry is a `.recInfo` recursor. -/
def isRecInfo : ConstantInfo .anon → Bool
  | .recInfo _ _ _ _ => true
  | _ => false

/-- Whether a `ConstantInfo` entry is not a `.recInfo` recursor. -/
def isNonRecInfo : ConstantInfo .anon → Bool
  | .recInfo _ _ _ _ => false
  | _ => true

/-- Modeled-inductive block run record using `IndRecsVmRunJ`. -/
def DeclIndVmRunJ (J : Judgements .anon) (env : Env .anon)
    (block : List (ConstantInfo .anon)) (env₂ : Env .anon) : Prop :=
  let recs := block.filter isRecInfo
  let nonrecs := block.filter isNonRecInfo
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  ∃ envM,
    IndMembersRunJ J blockNames {} env nonrecs envM ∧
    IndRecsVmRunJ J blockNames envM recs env₂

/-- Judgement package replacing `J.defeq` by `True` while keeping `J.infer`, `J.sort`, `J.annot`. -/
def trivDefEqOf (J : Judgements .anon) : Judgements .anon :=
  { J with defeq := fun _ _ _ _ => True }

theorem defEqListJ_trivDefEqOf_of_length {J : Judgements .anon} {env : Env .anon} {d : Nat} :
    ∀ {as bs : List KExpr}, as.length = bs.length → DefEqListJ (trivDefEqOf J) env d as bs
  | [], [], _ => trivial
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: as, _ :: bs, h => ⟨trivial, defEqListJ_trivDefEqOf_of_length (by simpa using h)⟩

theorem defEqListJ_to_trivDefEqOf {J : Judgements .anon} {env : Env .anon} {d : Nat}
    {as bs : List KExpr} (h : DefEqListJ J env d as bs) :
    DefEqListJ (trivDefEqOf J) env d as bs :=
  defEqListJ_trivDefEqOf_of_length h.length

theorem typedListJ_to_trivDefEqOf {J : Judgements .anon} {env : Env .anon} {d : Nat} :
    ∀ {as bs : List KExpr}, TypedListJ J env d as bs → TypedListJ (trivDefEqOf J) env d as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨⟨ty, hinf, _⟩, htl⟩ => ⟨⟨ty, hinf, trivial⟩, typedListJ_to_trivDefEqOf htl⟩

theorem IotaRuleVmRunJ.toTrivDefEq {J : Judgements .anon} {env' envSelf : Env .anon}
    {f : Key .anon → Key .anon} {cvName : Key .anon} {lps : List LevelParam} {tyA : KExpr}
    {mI rP j : Nat} {r r' : RecRule .anon}
    (h : IotaRuleVmRunJ J env' envSelf f cvName lps tyA mI rP j r r') :
    IotaRuleRunJ (trivDefEqOf J) env' envSelf f cvName lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, hfc, hnf, hrb, hrf, hann, hrlp, hrres, hstrip, hinf,
    fire, hr'eq, hbranch⟩ := h
  refine ⟨cvj, cnP, cnF, rhsA, hfc, hnf, hrb, hrf, hann, hrlp, hrres, hstrip, hinf,
    fire, hr'eq, ?_⟩
  rcases hbranch with ⟨hpl, hfire, hthm⟩ | ⟨hnpl, lvls, pins, hfire, hthmN⟩
  · refine Or.inl ⟨hpl, hfire, ?_⟩
    obtain ⟨cvt, fvs, tbody, hcvt, hlps, hop, heqH, hlen3, hlh, hlar, hlp, hmaj, hct,
      cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP, crest2, ldoms, lrest,
      hcinst, hclen, hrinst, hopenP, hcinstP, hopenXP, _, hdePars,
      hdeIdx, hdeDom, hdePre, _, ⟨tl, htl, _⟩, ⟨tr, htr, _⟩⟩ := hthm
    have hPlen : (fvsP ++ xFvsP).length = rP + cnF := by
      rw [List.length_append, Ix.Kernel.Model.openPisAtFvars_length _ hopenP,
        Ix.Kernel.Model.openPisAtFvars_length _ hopenXP]
    obtain ⟨ldomsL, lrest2, hinstLam, hldlen⟩ :=
      instLamsAt_of_stripLams_len (fvsP ++ xFvsP) (by rw [hPlen]; exact hstrip)
    exact ⟨cvt, fvs, tbody, hcvt, hlps, hop, heqH, hlen3, hlh, hlar, hlp, hmaj, hct,
      cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP, crest2, ldoms, lrest,
      hcinst, hclen, hrinst, hopenP, hcinstP, hopenXP,
      ldomsL, lrest2, hinstLam, defEqListJ_to_trivDefEqOf hdePars,
      defEqListJ_to_trivDefEqOf hdeIdx, defEqListJ_to_trivDefEqOf hdeDom,
      defEqListJ_to_trivDefEqOf hdePre,
      defEqListJ_trivDefEqOf_of_length (by simp [hldlen]),
      trivial, ⟨tl, htl, trivial⟩, ⟨tr, htr, trivial⟩⟩
  · refine Or.inr ⟨hnpl, lvls, pins, hfire, ?_⟩
    obtain ⟨hshape, cvt, fvs, tbody, hcvt, hlps, hop, heqH, hlen3, hlh, hlar, hlp, hmaj,
      ⟨cbinders, cbody0, Dc, usc, hstrip0, hfn0⟩,
      cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP, crestP, xFvsP, ldoms,
      hcinst, hclen, hrinst, hopenP, ⟨hcinstP, hopenXP, hldlen0⟩, _, hTypedP,
      hdeIdx, hdeDom, hdePre, _, ⟨tl, htl, _⟩, ⟨tr, htr, _⟩⟩ := hthmN
    have hPlen : (fvsP ++ xFvsP).length = rP + cnF := by
      rw [List.length_append, Ix.Kernel.Model.openPisAtFvars_length _ hopenP,
        Ix.Kernel.Model.openPisAtFvars_length _ hopenXP]
    obtain ⟨ldomsL, lrest2, hinstLam, hldlen⟩ :=
      instLamsAt_of_stripLams_len (fvsP ++ xFvsP) (by rw [hPlen]; exact hstrip)
    exact ⟨hshape, cvt, fvs, tbody, hcvt, hlps, hop, heqH, hlen3, hlh, hlar, hlp, hmaj,
      ⟨cbinders, cbody0, hstrip0, by rw [hfn0]⟩,
      cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP, crestP, xFvsP, ldoms,
      hcinst, hclen, hrinst, hopenP, ⟨hcinstP, hopenXP, hldlen0⟩,
      ldomsL, lrest2, hinstLam, typedListJ_to_trivDefEqOf hTypedP,
      defEqListJ_to_trivDefEqOf hdeIdx, defEqListJ_to_trivDefEqOf hdeDom,
      defEqListJ_to_trivDefEqOf hdePre,
      defEqListJ_trivDefEqOf_of_length (by simp [hldlen]),
      trivial, ⟨tl, htl, trivial⟩, ⟨tr, htr, trivial⟩⟩

theorem IotaRulesVmRunJ.toTrivDefEq {J : Judgements .anon} {env' envSelf : Env .anon}
    {f : Key .anon → Key .anon} {cvName : Key .anon} {lps : List LevelParam} {tyA : KExpr}
    {mI rP : Nat} :
    ∀ {j : Nat} {rs out : List (RecRule .anon)},
      IotaRulesVmRunJ J env' envSelf f cvName lps tyA mI rP j rs out →
      IotaRulesRunJ (trivDefEqOf J) env' envSelf f cvName lps tyA mI rP j rs out
  | _, [], _, h => h
  | _, _ :: _, _, ⟨r', rest', hr, hrest, hout⟩ =>
    ⟨r', rest', hr.toTrivDefEq, hrest.toTrivDefEq, hout⟩

theorem IndRecsFoldVmRunJ.toTrivDefEq {J : Judgements .anon} {blockNames : List KKey}
    {envBase envSelf : Env .anon} :
    ∀ {acc : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
      {out : Env .anon},
      IndRecsFoldVmRunJ J blockNames envBase envSelf acc checked out →
      IndRecsFoldRunJ (trivDefEqOf J) blockNames envBase envSelf acc checked out
  | _, [], _, h => h
  | _, _ :: _, _, ⟨rules', hiot, hfold⟩ =>
    ⟨rules', hiot.toTrivDefEq, hfold.toTrivDefEq⟩

theorem JudgeFrames.toTrivDefEq {J : Judgements .anon} {env : Env .anon}
    (h : JudgeFrames J env) : JudgeFrames (trivDefEqOf J) env :=
  ⟨h.annot_syntax, h.annot_wscoped, h.annot_bounded, h.annot_leaves⟩

theorem MemberValRunJ.toTrivDefEq {J : Judgements .anon} {env' : Env .anon}
    {blockNames : List KKey} {cv cvA : ConstantVal .anon}
    (h : MemberValRunJ J env' blockNames cv cvA) :
    MemberValRunJ (trivDefEqOf J) env' blockNames cv cvA := by
  obtain ⟨type', hcv, hrest⟩ := h
  exact ⟨type', hcv, hrest⟩

theorem IndMembersRunJ.toTrivDefEq {J : Judgements .anon} {blockNames : List KKey}
    {caps : IndCaps .anon} :
    ∀ {env' : Env .anon} {members : List (ConstantInfo .anon)} {env₂ : Env .anon},
      IndMembersRunJ J blockNames caps env' members env₂ →
      IndMembersRunJ (trivDefEqOf J) blockNames caps env' members env₂
  | _, [], _, h => h
  | _, .indInfo _ _ :: _, _, ⟨cvA, hmv, hrec⟩ =>
    ⟨cvA, MemberValRunJ.toTrivDefEq hmv, IndMembersRunJ.toTrivDefEq hrec⟩
  | _, .ctorInfo _ _ _ :: _, _, ⟨cvA, hmv, hrec⟩ =>
    ⟨cvA, MemberValRunJ.toTrivDefEq hmv, IndMembersRunJ.toTrivDefEq hrec⟩
  | _, .axiomInfo _ :: _, _, ⟨_, _, h⟩ => nomatch h
  | _, .defnInfo _ _ _ :: _, _, ⟨_, _, h⟩ => nomatch h
  | _, .thmInfo _ _ :: _, _, ⟨_, _, h⟩ => nomatch h
  | _, .recInfo _ _ _ _ :: _, _, ⟨_, _, h⟩ => nomatch h
  | _, .projInfo _ :: _, _, ⟨_, _, h⟩ => nomatch h

theorem ProvisionRecsRunJ.toTrivDefEq {J : Judgements .anon} {blockNames : List KKey} :
    ∀ {envAcc : Env .anon} {recs : List (ConstantInfo .anon)} {envSelf : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ J blockNames envAcc recs envSelf checked →
      ProvisionRecsRunJ (trivDefEqOf J) blockNames envAcc recs envSelf checked
  | _, [], _, _, h => h
  | _, _ :: _, _, _, ⟨cvA, mI, rP, rules, rest', hci, hmv, hrec, hchk⟩ =>
    ⟨cvA, mI, rP, rules, rest', hci, MemberValRunJ.toTrivDefEq hmv,
      ProvisionRecsRunJ.toTrivDefEq hrec, hchk⟩

theorem IndRecsVmRunJ.toTrivDefEq {J : Judgements .anon} {blockNames : List KKey}
    {env₂ : Env .anon} {recs : List (ConstantInfo .anon)} {env₃ : Env .anon}
    (h : IndRecsVmRunJ J blockNames env₂ recs env₃) :
    IndRecsRunJ (trivDefEqOf J) blockNames env₂ recs env₃ := by
  rcases h with ⟨h1, h2⟩ | ⟨hne, heqf, envSelf, checked, hprov, hfold⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨hne, heqf, envSelf, checked, ProvisionRecsRunJ.toTrivDefEq hprov,
      hfold.toTrivDefEq⟩

private theorem filter_eq_of_forall {α : Type _} {p : α → Bool} (q : α → Bool) (xs : List α)
    (h : ∀ x, p x = q x) : xs.filter p = xs.filter q := by
  have hpq : p = q := funext h
  rw [hpq]

theorem DeclIndVmRunJ.toTrivDefEq {J : Judgements .anon} {env : Env .anon}
    {block : List (ConstantInfo .anon)} {env₂ : Env .anon}
    (h : DeclIndVmRunJ J env block env₂) :
    DeclIndRunJ (trivDefEqOf J) env block env₂ := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  refine ⟨?_, envM, ?_, ?_⟩
  · exact hsplit.trans (congrArg₂ List.append
      (filter_eq_of_forall _ block fun ci => by cases ci <;> rfl)
      (filter_eq_of_forall _ block fun ci => by cases ci <;> rfl))
  · rw [filter_eq_of_forall isNonRecInfo block (fun ci => by cases ci <;> rfl)]
    exact IndMembersRunJ.toTrivDefEq hmem
  · rw [filter_eq_of_forall isRecInfo block (fun ci => by cases ci <;> rfl)]
    exact hrecs.toTrivDefEq

/-- `DeclIndVmRunJ posRulesJ` preserves `DeclStoreInv` via its `.toTrivDefEq` projection. -/
theorem DeclStoreInv.declInd_vm {env env₂ : Env .anon} {block : List (ConstantInfo .anon)}
    (h : DeclStoreInv env)
    (hrun : DeclIndVmRunJ posRulesJ env block env₂) :
    DeclStoreInv env₂ := by
  have htriv : DeclIndRunJ (trivDefEqOf posRulesJ) env block env₂ := hrun.toTrivDefEq
  have hfr : ∀ e : Env .anon, JudgeFrames (trivDefEqOf posRulesJ) e :=
    fun e => JudgeFrames.toTrivDefEq (judgeFrames_posRulesJ e)
  have hext : EnvExt env env₂ := Ix.Kernel.Semantics.declIndRunJ_envExt htriv
  refine
    { store := Ix.Kernel.Model.storeInv_declIndRunJ hfr h.store htriv
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (Ix.Kernel.Model.modeled_newSat (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) htriv)
      recK := Ix.Kernel.Model.recK_step h.store h.recK hext.find
        (Ix.Kernel.Model.modeled_recK_new htriv)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (Ix.Kernel.Model.modeled_newSat
          (fun _ _ _ heq he => by
            obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
            simp at he)
          (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) htriv)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find h.tableBodies
        (Ix.Kernel.Model.modeled_newSat (fun _ _ heq => nomatch heq)
          (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) htriv)
      recShape := Ix.Kernel.Model.recShape_step h.store h.recShape hext.find
        (Ix.Kernel.Model.modeled_recShape_new htriv) }

/-! ## `f`-parametric modeled-inductive records for advice model aliases -/

theorem modelExt_isSome_mono {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {env₁ env₂ : Env .anon} {mp₁ : EnvModelM V μ env₁} {mp₂ : EnvModelM V μ env₂}
    (h : ModelExt mp₁ mp₂) {n : KKey} (hs : (env₁.find? n).isSome = true) :
    (env₂.find? n).isSome = true := by
  induction h with
  | refl => exact hs
  | step _ hfresh _ _ _ ih =>
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp ih
    rw [Env.find?_cons_of_fresh hfresh hci]
    rfl
  | swap _ hsome _ _ _ ih => exact hsome n ih

theorem modelExt_acval_eq_of_isSome {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {env₁ env₂ : Env .anon} {mp₁ : EnvModelM V μ env₁} {mp₂ : EnvModelM V μ env₂}
    (h : ModelExt mp₁ mp₂) {n : KKey} (hs : (env₁.find? n).isSome = true) :
    mp₂.base2.acval n = mp₁.base2.acval n := by
  induction h with
  | refl => rfl
  | @step e₂ m₂ c₀ A m₃ hext hfresh _ _ hac ih =>
    have hs₂ : (e₂.find? n).isSome = true := modelExt_isSome_mono hext hs
    have hne : n ≠ c₀.name := fun heq => by
      rw [heq, hfresh] at hs₂
      exact nomatch hs₂
    rw [hac, acvalWith_ne hne, ih]
  | swap _ _ _ _ hac ih => rw [hac, ih]

/-- Compatibility between a block's `.model` auxiliary companions in `env` and an advice renaming `f`:
outside `blockNames`, `f` is the identity; inside `blockNames`, `f n` is stored in `env` with the
same level parameters and leaf as `auxKey n .model`. -/
def ModelAliasOk (blockNames : List KKey) (env : Env .anon)
    (acval : KKey → (LevelParam → Nat) → AnnotTerm) (f : KKey → KKey) : Prop :=
  (∀ n, blockNames.contains n = false → f n = n) ∧
  (∀ n, blockNames.contains n = true →
    ∃ cvm mval hm ciF,
      env.find? (auxKey n .model) = some (.defnInfo cvm mval hm) ∧
      env.find? (f n) = some ciF ∧
      ciF.toConstantVal.levelParams = cvm.levelParams ∧
      acval (f n) = acval (auxKey n .model))

/-- Establish `RenameOk` for an advice renaming `f` at the provisioned environment `envSelf`. -/
theorem modelRenameOk_of_alias {V : Type w} [Ix.Kernel.SetTheory V] {μ : CheckMode}
    {blockNames : List KKey} {env envSelf : Env .anon}
    {mp : EnvModelM V μ env} {mS : EnvModelM V μ envSelf} {f : KKey → KKey}
    (hAlias : ModelAliasOk blockNames env mp.base2.acval f)
    (hext : ModelExt mp mS)
    (hmono : ∀ n ci, env.find? n = some ci → envSelf.find? n = some ci)
    (hIS : BlockInstalledTT blockNames envSelf mS.base2.cvalE)
    (hIAS : BlockAcvalInstalled blockNames envSelf mS.base2.acval)
    (hnames : ∀ n, blockNames.contains n = true → (envSelf.find? n).isSome = true) :
    RenameOk mS.base2.acval envSelf f := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ciS hfS
    cases hc : blockNames.contains n with
    | false =>
      rw [hAlias.1 n hc]
      exact ⟨ciS, hfS, rfl⟩
    | true =>
      obtain ⟨cvm, mval, hm, ciF, hfmE, hfFE, hflp, _⟩ := hAlias.2 n hc
      obtain ⟨cvmS, mvalS, hmS, hfmS, hlpsS, _, _⟩ := hIS n hc ciS hfS
      have hfmEq := (hmono _ _ hfmE).symm.trans hfmS
      obtain ⟨rfl, _, _⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfmEq)
      exact ⟨ciF, hmono _ _ hfFE, hflp.trans hlpsS⟩
  · intro n hfS
    cases hc : blockNames.contains n with
    | false =>
      rw [hAlias.1 n hc]
      exact hfS
    | true =>
      have hs := hnames n hc
      rw [hfS] at hs
      exact nomatch hs
  · intro n ψ
    cases hc : blockNames.contains n with
    | false =>
      rw [hAlias.1 n hc]
    | true =>
      obtain ⟨ciS, hfS⟩ := Option.isSome_iff_exists.mp (hnames n hc)
      obtain ⟨cvm, mval, hm, ciF, hfmE, hfFE, _, hacEq⟩ := hAlias.2 n hc
      have hsF : (env.find? (f n)).isSome = true := by rw [hfFE]; rfl
      have hsM : (env.find? (auxKey n .model)).isSome = true := by rw [hfmE]; rfl
      have h1 := congrFun (modelExt_acval_eq_of_isSome hext hsF) ψ
      have h2 := congrFun hacEq ψ
      have h3 := (congrFun (modelExt_acval_eq_of_isSome hext hsM) ψ).symm
      have h4 := hIAS n hc ciS hfS ψ
      exact h1.trans (h2.trans (h3.trans h4))

/-- Uniform `.nested`-fire `iota` rule run record over `IotaThmNVmRunJ` (covering both canonical
and nested rules uniformly without a `recRulePlain = false` guard). -/
def IotaRuleNVmRunJ (J : Judgements .anon) (env' envSelf : Env .anon)
    (f : Key .anon → Key .anon) (cvName : Key .anon)
    (lps : List LevelParam) (tyA : KExpr) (mI rP j : Nat) (r r' : RecRule .anon) : Prop :=
  ∃ cvj cnP cnF rhsA lvls pins,
    env'.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
    r.nfields = cnF ∧
    r.rhs.looseBVarsBounded 0 = true ∧
    r.rhs.hasFvar = false ∧
    J.annot envSelf 0 r.rhs rhsA ∧
    rhsA.allLevelParamsDefined lps = true ∧
    rhsA.constsResolve envSelf = true ∧
    (rhsA.stripLams (rP + cnF)).isSome = true ∧
    (∃ t', J.infer envSelf 0 rhsA t') ∧
    r' = recRuleBits env'.find? cvName
      { r with rhs := rhsA, ctorParams := cnP, fire := .nested lvls pins, paramsBlind := false } ∧
    IotaThmNVmRunJ J env' envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA lvls pins

theorem IotaRuleVmRunJ.toNVm {J : Judgements .anon} {env' envSelf : Env .anon}
    {f : Key .anon → Key .anon} {cvName : Key .anon} {lps : List LevelParam} {tyA : KExpr}
    {mI rP j : Nat} {r r' : RecRule .anon} {lvls : List Level} {pins : List KExpr}
    (h : IotaRuleVmRunJ J env' envSelf f cvName lps tyA mI rP j r r')
    (hfire : RecRule.fire r' = .nested lvls pins) :
    IotaRuleNVmRunJ J env' envSelf f cvName lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, hfc, hnf, hrb, hrf, hann, hrlp, hrres, hstrip, hinf,
    fire, hr'eq, hbranch⟩ := h
  have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]; rfl
  rcases hbranch with ⟨_, hfireP, _⟩ | ⟨_, lvls₀, pins₀, hfireN, hthmN⟩
  · rw [hr'fire, hfireP] at hfire
    exact nomatch hfire
  · rw [hr'fire, hfireN] at hfire
    obtain ⟨rfl, rfl⟩ := Ix.Kernel.RecRuleFire.nested.inj hfire
    subst hfireN
    exact ⟨cvj, cnP, cnF, rhsA, lvls₀, pins₀, hfc, hnf, hrb, hrf, hann, hrlp, hrres,
      hstrip, hinf, hr'eq, hthmN⟩

/-- Rule list run record over `IotaRuleNVmRunJ`. -/
def IotaRulesNVmRunJ (J : Judgements .anon) (env' envSelf : Env .anon)
    (f : Key .anon → Key .anon) (cvName : Key .anon)
    (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat) :
    Nat → List (RecRule .anon) → List (RecRule .anon) → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleNVmRunJ J env' envSelf f cvName lps tyA mI rP j r r' ∧
      IotaRulesNVmRunJ J env' envSelf f cvName lps tyA mI rP (j + 1) rest rest' ∧
      out = r' :: rest'

/-- Recursor-group install fold over `IotaRulesNVmRunJ` parameterized by `f`. -/
def IndRecsFoldNVmRunJF (J : Judgements .anon) (f : KKey → KKey)
    (envBase envSelf : Env .anon) :
    Env .anon → List (ConstantVal .anon × Nat × Nat × List (RecRule .anon)) → Env .anon → Prop
  | acc, [], out => out = acc
  | acc, c :: rest, out =>
    ∃ rules',
      IotaRulesNVmRunJ J envBase envSelf f
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2 rules' ∧
      IndRecsFoldNVmRunJF J f envBase envSelf
        ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-- Recursor-group phase over `IndRecsFoldNVmRunJF`. -/
def IndRecsNVmRunJF (J : Judgements .anon)
    (blockNames : List KKey) (f : KKey → KKey) (env₂ : Env .anon)
    (recs : List (ConstantInfo .anon)) (env₃ : Env .anon) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   ∃ envSelf checked,
     ((∃ c ∈ checked, c.2.2.2 ≠ []) → env₂.find? eqName = some eqA) ∧
     ProvisionRecsRunJ J blockNames env₂ recs envSelf checked ∧
     IndRecsFoldNVmRunJF J f env₂ envSelf env₂ checked env₃)

/-- Modeled-inductive block run record parameterized by advice renaming `f` for rule checks. -/
def DeclIndNVmRunJF (J : Judgements .anon) (f : KKey → KKey) (env : Env .anon)
    (block : List (ConstantInfo .anon)) (env₂ : Env .anon) : Prop :=
  let recs := block.filter isRecInfo
  let nonrecs := block.filter isNonRecInfo
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  ∃ envM,
    IndMembersRunJ J blockNames {} env nonrecs envM ∧
    IndRecsNVmRunJF J blockNames f envM recs env₂

/-- Model-free rule facts for every rule produced by `IotaRulesNVmRunJ`. -/
theorem iotaRulesNVmFactsRun {J : Judgements .anon}
    {env₂ envSelf : Env .anon} {cvalSelf : TConstVal .anon} {f : Key .anon → Key .anon}
    (hup : FoldUpS env₂ envSelf)
    (hden : ∀ e : KExpr, e.hasFvar = false →
      e.looseBVarsBounded 0 = true →
      (∃ t', J.infer envSelf 0 e t') →
      ∀ φ : LevelParam → Nat,
        ∃ Rv, denoteClosed cvalSelf envSelf φ e = some Rv)
    (hsyn : ∀ {e e' : KExpr}, J.annot envSelf 0 e e' → e.hasFvar = false →
      e.looseBVarsBounded 0 = true → e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true)
    {cvA : ConstantVal .anon} {mI rP : Nat} :
    ∀ (j : Nat) (rules rules' : List (RecRule .anon)),
      IotaRulesNVmRunJ J env₂ envSelf f cvA.name cvA.levelParams
        cvA.type mI rP j rules rules' →
      ∀ rl ∈ rules', RuleFacts envSelf cvalSelf cvA mI rP rl := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h rl hrl
    rw [h] at hrl
    exact nomatch hrl
  | cons r rest ih =>
    intro rules' h rl hrl
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · rw [heqrl]
      obtain ⟨cvjK, cnPK, cnFK, rhsA, lvls₀, pins₀, hfcK, hnfK, hrb, hrf, hann, hrlp,
        hrres, _, hityK, hr'eq, hthmN⟩ := hkit
      have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]; rfl
      have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]; rfl
      have hr'fire : RecRule.fire r' = .nested lvls₀ pins₀ := by rw [hr'eq]; rfl
      have hr'cp : RecRule.ctorParams r' = cnPK := by rw [hr'eq]; rfl
      have hr'nf : RecRule.nfields r' = cnFK := by rw [hr'eq]; exact hnfK
      obtain ⟨hrhsAw, hrhsAb⟩ := hsyn hann hrf hrb
      have hfcS : envSelf.find? (RecRule.ctor r') = some (.ctorInfo cvjK cnPK cnFK) := by
        rw [hr'ctor]
        rcases hup _ _ hfcK with h' | ⟨_, _, _, _, _, heq, -⟩
        · exact h'
        · exact nomatch heq
      have hkeep : ∀ (n : Key .anon) (ci : ConstantInfo .anon),
          (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
          env₂.find? n = some ci → envSelf.find? n = some ci := by
        intro n ci hnr hf
        rcases hup _ _ hf with h' | ⟨_, _, _, _, _, heq, -⟩
        · exact h'
        · exact absurd heq (hnr _ _ _ _)
      refine ⟨by rw [hr'rhs]; exact hrhsAw, by rw [hr'rhs]; exact hrlp,
        by rw [hr'rhs]; exact hrres, by rw [hr'rhs]; exact hrhsAb, ?_, ?_, ?_, ?_, ?_⟩
      · intro lvls pins hfireN
        rw [hr'fire] at hfireN
        obtain ⟨rfl, rfl⟩ := Ix.Kernel.RecRuleFire.nested.inj hfireN
        obtain ⟨hrPmI, hlvls, hpins, pre, dom, body, bm, D, hstrip, hfn, hargs, -⟩ :=
          Ix.Kernel.nestedRuleShape_inv hthmN.1
        exact ⟨hrPmI, hlvls, hpins, pre, dom, body, bm, D, hstrip, hfn, hargs⟩
      · refine ⟨cvjK, by rw [hr'cp, hr'nf]; exact hfcS,
          fun hp => ?_, fun lvls pins hfireN => ?_, ?_, ?_⟩
        · rw [hr'fire] at hp
          exact nomatch hp
        · rw [hr'cp]; rw [hr'fire] at hfireN
          obtain ⟨rfl, rfl⟩ := Ix.Kernel.RecRuleFire.nested.inj hfireN
          obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hlen⟩ :=
            Ix.Kernel.nestedRuleShape_inv hthmN.1
          exact hlen
        · rw [hr'fire]
          exact fun h => nomatch h
        · rw [hr'cp, hr'nf]
          obtain ⟨-, _, _, _, _, _, _, _, _, _, _, _, _, ⟨cb, cb0, Dc, usc, hsC, hh⟩, -⟩ := hthmN
          exact Expr.ctorTeleOk_of hsC hh
      · intro _
        refine ⟨(Ix.Kernel.nestedRuleShape_inv hthmN.1).1, fun φ => ?_⟩
        obtain ⟨t', hty'⟩ := hityK
        obtain ⟨Rv, hRv⟩ := hden rhsA hrhsAw hrhsAb ⟨t', hty'⟩ φ
        exact ⟨Rv, by rw [hr'rhs]; exact hRv⟩
      · intro hb
        refine recRuleKOf_mono hkeep ?_
        rw [hr'eq] at hb ⊢
        exact hb
      · intro hb
        refine recRuleEtaOf_mono hkeep ?_
        rw [hr'eq] at hb ⊢
        exact hb
    · exact ih (j + 1) rest' hrec rl hrl'

set_option maxHeartbeats 1600000 in
/-- Provisioning and install swap facts over `IndRecsFoldNVmRunJF`. -/
theorem indRecsFoldNVmFactsRunF {J : Judgements .anon}
    {blockNames : List KKey} {f : KKey → KKey}
    {envSelf envBase : Env .anon}
    (RF : ConstantVal .anon → Nat → Nat → RecRule .anon → Prop)
    (hfire : ∀ (cvA : ConstantVal .anon) (mI rP : Nat)
      (rules rules' : List (RecRule .anon)),
      blockNames.contains cvA.name = true →
      envSelf.find? cvA.name = some (.recInfo cvA mI rP []) →
      IotaRulesNVmRunJ J envBase envSelf f
        cvA.name cvA.levelParams cvA.type mI rP 0 rules rules' →
      ∀ rl ∈ rules', RF cvA mI rP rl) :
    ∀ (recs : List (ConstantInfo .anon)) {envP envF env₃ : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      SwapShList envP.consts envF.consts →
      SwapNResS envP envF →
      FoldUpS envF envSelf →
      (∀ (n : KKey) (ci : ConstantInfo .anon),
        envP.find? n = some ci → envSelf.find? n = some ci) →
      (∀ c ∈ envF.consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RF cv mI rP rl) →
      (∀ (n : KKey) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        ∀ rl ∈ rules, RF cv mI rP rl) →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsRunJ J blockNames envP recs envSelf checked →
      IndRecsFoldNVmRunJF J f envBase envSelf envF checked env₃ →
      SwapShList envSelf.consts env₃.consts ∧
      SwapNResS envSelf env₃ ∧
      (∀ c ∈ env₃.consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RF cv mI rP rl) ∧
      ∀ (n : KKey) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (RecRule .anon)),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        ∀ rl ∈ rules, RF cv mI rP rl := by
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ checked hsw hnres _ _ hents hentF _ hprov hfold
    obtain ⟨rfl, rfl⟩ := hprov
    subst hfold
    exact ⟨hsw, hnres, hents, hentF⟩
  | cons ci₀ rest ih =>
    intro envP envF env₃ checked hsw hnres hupF hupP hents hentF hbn hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', ⟨hfresh0, hres0, -, -, -, -, -, -, -, -⟩, hcvAdef, -⟩ := hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvAdef]
    have hfreshP : envP.find? cvA.name = none := by
      rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfresh0
    have hres : Ix.Kernel.reservedBasisNames.contains cvA.name = false := by
      rw [hnameA]; exact hres0
    have hselfA : envSelf.find? cvA.name = some (.recInfo cvA mI rP []) :=
      provisionRecsRunS_mono rest hprov' _ _
        (Ix.Kernel.Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    have hfacts := hfire cvA mI rP rules rules' hbnA hselfA hiot
    have hsw' : SwapShList
        (Env.consts ⟨.recInfo cvA mI rP [] :: envP.consts⟩)
        (Env.consts ⟨.recInfo cvA mI rP rules' :: envF.consts⟩) :=
      SwapShList.cons (Or.inr ⟨cvA, mI, rP, rules', rfl, rfl⟩) hsw
    have hnres' : SwapNResS ⟨.recInfo cvA mI rP [] :: envP.consts⟩
        ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ := by
      intro n cv mI₀ rP₀ rules₀ h₀ h₃
      rw [Ix.Kernel.Env.find?_cons] at h₀ h₃
      split at h₀
      · next hn =>
        obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj (Option.some.inj h₀)
        exact Or.inr (by rw [← hn]; exact hres)
      · next hn =>
        have hn' : ¬(ConstantInfo.recInfo cvA mI rP rules').name = n := hn
        simp only [hn', ↓reduceIte] at h₃
        exact hnres n cv mI₀ rP₀ rules₀ h₀ h₃
    have hupF' : FoldUpS ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ envSelf := by
      intro n ci hfx
      rw [Ix.Kernel.Env.find?_cons] at hfx
      split at hfx
      · next hn =>
        obtain rfl := Option.some.inj hfx
        exact Or.inr ⟨cvA, mI, rP, rules', [], rfl, by rw [← hn]; exact hselfA⟩
      · exact hupF n ci hfx
    have hupP' : ∀ (n : KKey) (ci : ConstantInfo .anon),
        (Env.find? ⟨.recInfo cvA mI rP [] :: envP.consts⟩ n) = some ci →
        envSelf.find? n = some ci := by
      intro n ci hfx
      rw [Ix.Kernel.Env.find?_cons] at hfx
      split at hfx
      · next hn =>
        obtain rfl := Option.some.inj hfx
        rw [← hn]; exact hselfA
      · exact hupP n ci hfx
    have hents' : ∀ c ∈ (Env.consts ⟨.recInfo cvA mI rP rules' :: envF.consts⟩),
        c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RF cv mI rP rl := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inr ⟨cvA, mI, rP, rules', rfl, hfacts⟩
      · exact hents c hc'
    have hentF' : ∀ (n : KKey) (cv : ConstantVal .anon) (mI₀ rP₀ : Nat)
        (rules₀ : List (RecRule .anon)),
        Env.find? ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ n
          = some (.recInfo cv mI₀ rP₀ rules₀) →
        envSelf.find? n = some (.recInfo cv mI₀ rP₀ rules₀) ∨
        ∀ rl ∈ rules₀, RF cv mI₀ rP₀ rl := by
      intro n cv mI₀ rP₀ rules₀ hfx
      rw [Ix.Kernel.Env.find?_cons] at hfx
      split at hfx
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hfx)
        exact Or.inr hfacts
      · exact hentF n cv mI₀ rP₀ rules₀ hfx
    exact ih hsw' hnres' hupF' hupP' hents' hentF'
      (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci)) hprov' hfold'

end IxVM.Refinement.Decl
