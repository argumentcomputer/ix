import IxVMRefinement.FamilyAlias.RuleAliasGroup
import IxVMRefinement.FamilyAlias.Enter

/-! # A rule's record from its facts and its alias

IxC's renamed rule record `IotaRuleRenRunJ` (`IxC/Kernel/Model/IndRenRecord.lean`) over the family
package `famJ h`, at the environment `envM` after the family's types and constructors and the
environment `envSelf` after its recursors without rules, from a rule's facts with its alias
found (`RuleAliased`, `FamilyAlias/RuleAliasGroup.lean`): `iotaRuleRenRunJ_of_aliased`.

The facts are judgements at the prefix `env` on terms renamed to the advice by `g`; the record
asks judgements of `renameJ f (famJ h)` at `envSelf`, with `f` the block renaming and `h` the
renaming of the aliases to their targets. Three kinds of term meet:

* the advice statement's side (its variables, the arguments of its equation): it resolves in
  the prefix, which `h` fixes, so it is its own renaming (`openPisAtFvars_fixed`);
* the record's terms already renamed by `f` (the constructor's and the recursor's telescopes
  instantiated): `h` takes them to the facts' terms (`instPisAt_pullback`);
* the record's raw terms (the variables of the recursor's and the constructor's telescopes, the
  right-hand side's λ-domains, the pins): `f` then `h` is `g` on them. This is carried from the
  recursor's type, the constructor's type, the right-hand side and the pins through each
  opening (`openPisAtFvars_agree`, `instPisAt_agree`, `instLamsAt_agree`, `instSpine_agree`).

The copy's left side, which names the recursor's model key and the constructor under `f`, is
taken to the statement's by `h` (`ruleCopy_spec`). A nested rule's pins are typed renamed by `f`;
their leaf annotations are parameter domains, which the facts' `LeavesFixed g` conjunct shows
name no member, so `f` and `h` fix them. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam BinderMeta EnvWF
  EnvExt Derived auxKey openPisAtFvars isEqHead nestedRuleShape recRuleBits eqName)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false

/-! ## Lists -/

theorem map_eq_self_mem {α : Type} {φ : α → α} :
    ∀ {l : List α}, l.map φ = l → ∀ x ∈ l, φ x = x
  | [], _, _, hx => nomatch hx
  | a :: l, h, x, hx => by
    rw [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact map_eq_self_mem h.2 x hx

theorem getLastD_append_single {α : Type} (a : α) :
    ∀ (l : List α) (d : α), (l ++ [a]).getLastD d = a := by
  intro l d
  simp

theorem take_dropLast_of_lt {α : Type} :
    ∀ {l : List α} {n : Nat}, n < l.length → l.dropLast.take n = l.take n
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | [_], 0, _ => rfl
  | [_], _ + 1, h => absurd h (by simp)
  | _ :: _ :: _, 0, _ => rfl
  | a :: b :: l, n + 1, h => by
    rw [List.dropLast_cons₂, List.take_succ_cons, List.take_succ_cons,
      take_dropLast_of_lt (l := b :: l) (n := n) (by simp only [List.length_cons] at h ⊢; omega)]

theorem take_drop_dropLast_append {α : Type} (m : α) (l : List α) (n k : Nat)
    (hk : n + k < l.length) :
    ((l.dropLast ++ [m]).drop n).take k = (l.drop n).take k := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_append, List.length_dropLast,
      List.length_cons, List.length_nil]
    omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop]
    have hi : n + i < l.dropLast.length := by
      simp only [List.length_take, List.length_drop] at h2
      rw [List.length_dropLast]
      omega
    rw [List.getElem_append_left hi, List.getElem_dropLast]

/-! ## Leaves -/

theorem LeavesFixed.of_renameConsts_eq {h : KKey → KKey} {e : KExpr}
    (he : e.renameConsts h = e) : LeavesFixed h e := by
  have h1 := Ix.Kernel.Verify.fvarLeaves_renameConstsE (f := h) e
  rw [he] at h1
  intro l hl
  exact congrArg Prod.snd (map_eq_self_mem h1.symm l hl)

theorem LeavesFixed.mkAppN' {h : KKey → KKey} {xs : List KExpr} {f : KExpr}
    (hf : LeavesFixed h f) (hxs : ∀ x ∈ xs, LeavesFixed h x) :
    LeavesFixed h (Expr.mkAppN f xs) := by
  intro l hl
  rcases Ix.Kernel.fvarLeaves_mkAppN hl with hl | ⟨x, hx, hl⟩
  · exact hf l hl
  · exact hxs x hx l hl

theorem LeavesFixed.instSpine' {h : KKey → KKey} {args : List KExpr} {t : Nat} {e : KExpr}
    (he : LeavesFixed h e) (hargs : ∀ a ∈ args, LeavesFixed h a) :
    LeavesFixed h (Expr.instSpine args t e) := by
  intro l hl
  rcases Ix.Kernel.fvarLeaves_instSpine t hl with hl | ⟨a, ha, hl⟩
  · exact he l hl
  · exact hargs a ha l hl

/-- Two renamings that agree on a term agree on its leaf annotations. -/
theorem leaves_agree {π₁ π₂ : KKey → KKey} {x : KExpr}
    (hx : x.renameConsts π₁ = x.renameConsts π₂) :
    ∀ l ∈ x.fvarLeaves, l.2.renameConsts π₁ = l.2.renameConsts π₂ := by
  have h1 := Ix.Kernel.Verify.fvarLeaves_renameConstsE (f := π₁) x
  rw [hx, Ix.Kernel.Verify.fvarLeaves_renameConstsE] at h1
  intro l hl
  exact (congrArg Prod.snd (List.map_inj_left.mp h1 l hl)).symm

/-- A term `g` fixes is fixed by a renaming that fixes every key `g` fixes. (A projection's
structure name is not renamed, so only the constants count.) -/
theorem renameConsts_eq_self_of_fixed {g f : KKey → KKey} (hfg : ∀ k, g k = k → f k = k) :
    ∀ e : KExpr, e.renameConsts g = e → e.renameConsts f = e := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ => intro _; rfl
  | const n ls =>
    intro he
    injection he with hn
    show Expr.const (f n) ls = Expr.const n ls
    rw [hfg n hn]
  | fvar i ty ih =>
    intro he
    injection he with _ hty
    show Expr.fvar i (ty.renameConsts f) = Expr.fvar i ty
    rw [ih hty]
  | app a b iha ihb =>
    intro he
    injection he with h1 h2
    show Expr.app (a.renameConsts f) (b.renameConsts f) = Expr.app a b
    rw [iha h1, ihb h2]
  | lam ty b m iht ihb =>
    intro he
    injection he with h1 h2
    show Expr.lam (ty.renameConsts f) (b.renameConsts f) m = Expr.lam ty b m
    rw [iht h1, ihb h2]
  | forallE ty b m iht ihb =>
    intro he
    injection he with h1 h2
    show Expr.forallE (ty.renameConsts f) (b.renameConsts f) m = Expr.forallE ty b m
    rw [iht h1, ihb h2]
  | letE ty v b m iht ihv ihb =>
    intro he
    injection he with h1 h2 h3
    show Expr.letE (ty.renameConsts f) (v.renameConsts f) (b.renameConsts f) m =
      Expr.letE ty v b m
    rw [iht h1, ihv h2, ihb h3]
  | proj s i e ih =>
    intro he
    injection he with _ _ h3
    show Expr.proj s i (e.renameConsts f) = Expr.proj s i e
    rw [ih h3]

/-! ## Two renamings that agree on a term agree on what is read off it -/

theorem instLamsAt_renameConsts (π : KKey → KKey) :
    ∀ (xs : List KExpr) (e : KExpr),
      Expr.instLamsAt (xs.map (·.renameConsts π)) (e.renameConsts π) =
        (Expr.instLamsAt xs e).map (fun p => (p.1.map (·.renameConsts π), p.2.renameConsts π))
  | [], _ => rfl
  | x :: xs, .lam ty body _ => by
    simp only [List.map_cons, Expr.renameConsts, Expr.instLamsAt]
    have hinst : (body.renameConsts π).instantiate1 (x.renameConsts π) =
        (body.instantiate1 x).renameConsts π :=
      (Ix.Kernel.Expr.renameConsts_instantiate1_gen π body 0).symm
    rw [hinst, instLamsAt_renameConsts π xs (body.instantiate1 x)]
    cases Expr.instLamsAt xs (body.instantiate1 x) <;> rfl
  | _ :: _, .bvar _ | _ :: _, .fvar _ _ | _ :: _, .sort _ | _ :: _, .const _ _
  | _ :: _, .app _ _ | _ :: _, .forallE _ _ _ | _ :: _, .letE _ _ _ _
  | _ :: _, .lit _ | _ :: _, .proj _ _ _ => rfl

theorem openPisAtFvars_agree {π₁ π₂ : KKey → KKey} {m i : Nat} {e rem : KExpr}
    {fvs : List KExpr} (hop : openPisAtFvars m e i = some (fvs, rem))
    (he : e.renameConsts π₁ = e.renameConsts π₂) :
    fvs.map (·.renameConsts π₁) = fvs.map (·.renameConsts π₂) ∧
      rem.renameConsts π₁ = rem.renameConsts π₂ := by
  have h1 := IxVM.Refinement.Decl.openPisAtFvars_renameConsts π₁ m e i
  have h2 := IxVM.Refinement.Decl.openPisAtFvars_renameConsts π₂ m e i
  rw [he, h2, hop] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

theorem openPisAtFvars_fixed {h : KKey → KKey} {m i : Nat} {e rem : KExpr} {fvs : List KExpr}
    (hop : openPisAtFvars m e i = some (fvs, rem)) (he : e.renameConsts h = e) :
    fvs.map (·.renameConsts h) = fvs ∧ rem.renameConsts h = rem := by
  have h1 := IxVM.Refinement.Decl.openPisAtFvars_renameConsts h m e i
  rw [he, hop] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

theorem instPisAt_agree {π₁ π₂ : KKey → KKey} {xs doms : List KExpr} {e rem : KExpr}
    (hi : Expr.instPisAt xs e = some (doms, rem))
    (hxs : xs.map (·.renameConsts π₁) = xs.map (·.renameConsts π₂))
    (he : e.renameConsts π₁ = e.renameConsts π₂) :
    doms.map (·.renameConsts π₁) = doms.map (·.renameConsts π₂) ∧
      rem.renameConsts π₁ = rem.renameConsts π₂ := by
  have h1 := IxVM.Refinement.Decl.instPisAt_renameConsts π₁ xs e
  have h2 := IxVM.Refinement.Decl.instPisAt_renameConsts π₂ xs e
  rw [hxs, he, h2, hi] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

theorem instLamsAt_agree {π₁ π₂ : KKey → KKey} {xs doms : List KExpr} {e rem : KExpr}
    (hi : Expr.instLamsAt xs e = some (doms, rem))
    (hxs : xs.map (·.renameConsts π₁) = xs.map (·.renameConsts π₂))
    (he : e.renameConsts π₁ = e.renameConsts π₂) :
    doms.map (·.renameConsts π₁) = doms.map (·.renameConsts π₂) ∧
      rem.renameConsts π₁ = rem.renameConsts π₂ := by
  have h1 := instLamsAt_renameConsts π₁ xs e
  have h2 := instLamsAt_renameConsts π₂ xs e
  rw [hxs, he, h2, hi] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- **Pulling an instantiation back along a renaming**: if the renamed arguments instantiate
the renamed telescope, the arguments instantiate the telescope, to the preimages. -/
theorem instPisAt_pullback {h : KKey → KKey} {xs ys doms : List KExpr} {e e' rem : KExpr}
    (hxs : xs.map (·.renameConsts h) = ys) (he : e.renameConsts h = e')
    (hi : Expr.instPisAt ys e' = some (doms, rem)) :
    ∃ doms₀ rem₀, Expr.instPisAt xs e = some (doms₀, rem₀) ∧
      doms₀.map (·.renameConsts h) = doms ∧ rem₀.renameConsts h = rem := by
  have h1 := IxVM.Refinement.Decl.instPisAt_renameConsts h xs e
  rw [hxs, he, hi] at h1
  cases hx : Expr.instPisAt xs e with
  | none => rw [hx] at h1; simp at h1
  | some p =>
    rw [hx] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact ⟨p.1, p.2, rfl, h1.1.symm, h1.2.symm⟩

theorem instSpine_agree {π₁ π₂ : KKey → KKey} {xs : List KExpr} {t : Nat} {e : KExpr}
    (hxs : xs.map (·.renameConsts π₁) = xs.map (·.renameConsts π₂))
    (he : e.renameConsts π₁ = e.renameConsts π₂) :
    (Expr.instSpine xs t e).renameConsts π₁ = (Expr.instSpine xs t e).renameConsts π₂ := by
  rw [← IxVM.Refinement.Decl.instSpine_renameConsts π₁,
    ← IxVM.Refinement.Decl.instSpine_renameConsts π₂, hxs, he]

theorem map_take_agree {π₁ π₂ : KKey → KKey} {xs : List KExpr} (n : Nat)
    (h : xs.map (·.renameConsts π₁) = xs.map (·.renameConsts π₂)) :
    (xs.take n).map (·.renameConsts π₁) = (xs.take n).map (·.renameConsts π₂) := by
  rw [List.map_take, List.map_take, h]

theorem map_fvarTypeD_renameConsts' (π : KKey → KKey) (xs : List KExpr) :
    (xs.map Expr.fvarTypeD).map (·.renameConsts π) =
      (xs.map (·.renameConsts π)).map Expr.fvarTypeD := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun x _ =>
    (IxVM.Refinement.Decl.fvarTypeD_renameConsts π x).symm)

theorem map_fvarTypeD_agree {π₁ π₂ : KKey → KKey} {xs : List KExpr}
    (h : xs.map (·.renameConsts π₁) = xs.map (·.renameConsts π₂)) :
    (xs.map Expr.fvarTypeD).map (·.renameConsts π₁) =
      (xs.map Expr.fvarTypeD).map (·.renameConsts π₂) := by
  rw [map_fvarTypeD_renameConsts', map_fvarTypeD_renameConsts', h]

theorem instantiateLevelParams_agree {π₁ π₂ : KKey → KKey} (ks : List LevelParam)
    (us : List KLevel) {e : KExpr} (h : e.renameConsts π₁ = e.renameConsts π₂) :
    (e.instantiateLevelParams ks us).renameConsts π₁ =
      (e.instantiateLevelParams ks us).renameConsts π₂ := by
  rw [← IxVM.Refinement.Decl.instantiateLevelParams_renameConsts,
    ← IxVM.Refinement.Decl.instantiateLevelParams_renameConsts, h]

/-! ## Lifting -/

theorem noLooseIn_liftLooseBVars_self (n : Nat) :
    ∀ (v : KExpr) (c : Nat), noLooseIn c n (v.liftLooseBVars n c) = true := by
  intro v
  induction v with
  | bvar i =>
    intro c
    show noLooseIn c n (if i ≥ c then Expr.bvar (i + n) else Expr.bvar i) = true
    by_cases hic : i ≥ c
    · rw [ite_eq_left hic]
      simp only [noLooseIn, decide_eq_true_eq]
      omega
    · rw [ite_eq_right hic]
      simp only [noLooseIn, decide_eq_true_eq]
      omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha =>
    intro c
    simp only [Expr.liftLooseBVars, noLooseIn, ihf c, iha c, Bool.and_self]
  | lam ty b _ iht ihb | forallE ty b _ iht ihb =>
    intro c
    simp only [Expr.liftLooseBVars, noLooseIn, iht c, ihb (c + 1), Bool.and_self]
  | letE ty v b _ iht ihv ihb =>
    intro c
    simp only [Expr.liftLooseBVars, noLooseIn, iht c, ihv c, ihb (c + 1), Bool.and_self]
  | proj _ _ e ih =>
    intro c
    simp only [Expr.liftLooseBVars, noLooseIn, ih c]

/-! ## Entering the record's package from the facts' judgements -/

/-- A conversion list of the facts whose terms are the record's renamed by `h`. -/
theorem defEqListJ_renameJ_of_pos {env E : Env .anon} {h f : KKey → KKey} {d : Nat}
    (hext : EnvExt env E) (hA : AliasEnv E h) :
    ∀ {as bs : List KExpr},
      DefEqListJ posRulesJ env d (as.map (·.renameConsts h)) (bs.map (·.renameConsts h)) →
      DefEqListJ (renameJ f (famJ h)) E d as bs
  | [], [], _ => trivial
  | [], _ :: _, hd => nomatch hd
  | _ :: _, [], hd => nomatch hd
  | a :: as, b :: bs, hd => by
    obtain ⟨h0, h1⟩ := hd
    exact ⟨Or.inl ⟨hA, Or.inl (posRulesJ_defeq_weaken hext h0)⟩,
      defEqListJ_renameJ_of_pos hext hA h1⟩

/-- A conversion list of the facts whose terms are the record's renamed by `g`, where `f` then
`h` is `g` on them. -/
theorem defEqListJ_renameJ_of_renamed {env E : Env .anon} {h f g : KKey → KKey} {d : Nat}
    (hext : EnvExt env E) (hA : AliasEnv E h) :
    ∀ {as bs : List KExpr},
      DefEqListJ posRulesJ env d (as.map (·.renameConsts g)) (bs.map (·.renameConsts g)) →
      as.map (·.renameConsts (fun k => h (f k))) = as.map (·.renameConsts g) →
      bs.map (·.renameConsts (fun k => h (f k))) = bs.map (·.renameConsts g) →
      DefEqListJ (renameJ f (famJ h)) E d as bs
  | [], [], _, _, _ => trivial
  | [], _ :: _, hd, _, _ => nomatch hd
  | _ :: _, [], hd, _, _ => nomatch hd
  | a :: as, b :: bs, hd, ha, hb => by
    obtain ⟨h0, h1⟩ := hd
    rw [List.map_cons, List.map_cons, List.cons.injEq] at ha hb
    have h0' : posRulesJ.defeq E d ((a.renameConsts f).renameConsts h)
        ((b.renameConsts f).renameConsts h) := by
      rw [renameConsts_comp, renameConsts_comp, ha.1, hb.1]
      exact posRulesJ_defeq_weaken hext h0
    exact ⟨Or.inr ⟨hA, Or.inl h0'⟩, defEqListJ_renameJ_of_renamed hext hA h1 ha.2 hb.2⟩

/-- A typed list of the facts whose terms are the record's renamed by `g`, where `f` then `h`
is `g` on them and `h` fixes the leaf annotations of the subjects renamed by `f`. -/
theorem typedListJ_famJ_of_renamed {env E : Env .anon} {h f g : KKey → KKey} {d : Nat}
    (hext : EnvExt env E) (hA : AliasEnv E h) :
    ∀ {as bs : List KExpr},
      TypedListJ posRulesJ env d (as.map (·.renameConsts g)) (bs.map (·.renameConsts g)) →
      as.map (·.renameConsts (fun k => h (f k))) = as.map (·.renameConsts g) →
      bs.map (·.renameConsts (fun k => h (f k))) = bs.map (·.renameConsts g) →
      (∀ a ∈ as, LeavesFixed h (a.renameConsts f)) →
      TypedListJ (famJ h) E d (as.map (·.renameConsts f)) (bs.map (·.renameConsts f))
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, hd, _, _, _ => nomatch hd
  | _ :: _, [], hd, _, _, _ => nomatch hd
  | a :: as, b :: bs, hd, ha, hb, hL => by
    obtain ⟨⟨ty, hi, hde⟩, h1⟩ := hd
    rw [List.map_cons, List.map_cons, List.cons.injEq] at ha hb
    have hi' : posRulesJ.infer E d ((a.renameConsts f).renameConsts h) ty := by
      rw [renameConsts_comp, ha.1]
      exact posRulesJ_infer_weaken hext hi
    have hde' : posRulesJ.defeq E d ty ((b.renameConsts f).renameConsts h) := by
      rw [renameConsts_comp, hb.1]
      exact posRulesJ_defeq_weaken hext hde
    exact ⟨⟨ty, ⟨hA, hL a List.mem_cons_self, hi'⟩, ⟨hA, Or.inr hde'⟩⟩,
      typedListJ_famJ_of_renamed hext hA h1 ha.2 hb.2
        (fun x hx => hL x (List.mem_cons_of_mem _ hx))⟩

end IxVM.Refinement.Decl.FamilyAlias
