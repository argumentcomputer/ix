import IxVMRefinement.Decl.NativeRecRules
import IxCK.Kernel.Semantics.Inductives.DeclNativeRecLateJ
import IxCK.Kernel.Ixon.Reader

/-! # The recursor's stage at a late recursor of a stored native family

A recursor installed for a native family that is already stored is compared, field by field,
with the recursor the family generates. This module assembles the native recursor relation
(`NativeRecJ`) at such a recursor from what the comparison establishes:

* the generated type `recTy` is scoped at the environment (`GenScoped.structRecTyR`), and the
  declared type, the generated one with type-annotation wrappers consumed at binder domains,
  is convertible with it (`WrapRelSem.defeq`);
* the generated rules exist and are scoped at the environment holding the generated recursor
  (`checkNativeRules_ok_go`); the recursor's name is fresh, so that environment keeps every
  lookup of the current one;
* the stored rules are the generated ones with wrappers consumed, index by index, and annotate
  the declared rules; their level parameters are the recursor's.

The stored recursor is the declared one (`RecStoredJ`, second arm).
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored NativeRecJ)
open Ix.Kernel.Model (rulesJ)

/-! ## Lists -/

/-- Lists of one length related at every position are related position by position. -/
private theorem semForall₂_of_getElem {α β : Type} {Rel : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ (i : Nat) (h₁ : i < xs.length) (h₂ : i < ys.length), Rel xs[i] ys[i]) →
      Ix.Kernel.Semantics.Forall₂ Rel xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp only [List.length_nil, List.length_cons] at hl; omega
  | _ :: _, [], hl, _ => by simp only [List.length_nil, List.length_cons] at hl; omega
  | x :: xs, y :: ys, hl, h =>
    .cons (h 0 (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega))
      (semForall₂_of_getElem (by simp only [List.length_cons] at hl; omega)
        (fun i h₁ h₂ => h (i + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega)))

/-- Every element on the left of a positionwise relation is related to one on the right. -/
private theorem forall₂_left_mem {α β : Type} {Rel : α → β → Prop} {xs : List α}
    {ys : List β} (h : List.Forall₂ Rel xs ys) : ∀ x ∈ xs, ∃ y ∈ ys, Rel x y := by
  induction h with
  | nil => intro x hx; simp at hx
  | cons hr _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, by simp, hr⟩
    · obtain ⟨y, hy, hxy⟩ := ih x hx
      exact ⟨y, by simp [hy], hxy⟩

/-- A generated rule exists only at a constructor's position. -/
private theorem lt_of_structRecRhsR_some {T lps elim large nP nIdx tty ctors recC rlvls j rhs}
    (h : Ix.Kernel.structRecRhsR (md := .anon) T lps elim large nP nIdx tty ctors recC rlvls j =
      some rhs) :
    j < ctors.length := by
  rcases Nat.lt_or_ge j ctors.length with hj | hj
  · exact hj
  · have hn : ctors[j]? = none := List.getElem?_eq_none_iff.mpr hj
    simp [Ix.Kernel.structRecRhsR, hn] at h

/-- **The stored rules annotate the declared rules**: each stored rule's right-hand side
annotates the declared one's, which is closed. -/
private theorem annot_rules_of_stored (envA : Ix.Kernel.Env .anon)
    {rlsC rules : List (Ix.Kernel.RecRule .anon)}
    (h : List.Forall₂ RuleStored rlsC rules)
    (hrd : ∀ rl ∈ rules, rl.rhs.hasFvar = false ∧ rl.rhs.looseBVarsBounded 0 = true) :
    Ix.Kernel.Semantics.Forall₂ (rulesJ.annot envA 0)
      (rules.map (·.rhs)) (rlsC.map (·.rhs)) := by
  revert hrd
  induction h with
  | nil => intro _; exact .nil
  | @cons c r cs rs hr _ ih =>
    intro hrd
    rw [List.map_cons, List.map_cons]
    have hr0 := hrd r (by simp)
    exact .cons (Decl.annot_of_annotates hr.2.2 hr0.1 hr0.2 0)
      (ih (fun rl hrl => hrd rl (by simp [hrl])))

/-- The record's level-parameter pin at the recursor's level parameters: the block's, with the
elimination parameter (the block's level count) in front at a large eliminator. -/
private theorem nativeRecLpsOk_recParts (fam : NativeFam .anon) (R : Ix.Kernel.Key .anon)
    (ty : Ix.Kernel.Expr .anon) {k : Nat} (hL1 : fam.p.cvT.levelParams = List.range k)
    (large : Bool) (rhs : List (Ix.Kernel.Expr .anon)) :
    Ix.Kernel.nativeRecLpsOk
      (fam.recParts ⟨R, Ix.Kernel.Reader.recLps large (List.range k), ty⟩
        (if large then k else 0) large rhs).toInductiveShape = true := by
  cases large <;>
    simp [Ix.Kernel.nativeRecLpsOk, NativeFam.recParts, Ix.Kernel.Reader.recLps, hL1]

/-! ## The native recursor relation -/

/-- **The recursor's stage and the stored recursor at a late recursor of a stored native
family.** The recursor `R` is fresh, its level parameters are the block's (with the
elimination parameter in front at a large eliminator); the declared recursor is checked
(`hcv`), the generated type `recTy` is the declared stored type `tyC` with wrappers consumed
(`hwrap`), and `tyC` annotates the declared type; the stored rules are the declared ones
annotated, one per stored constructor, each the generated rule with wrappers consumed
(`hrules`); the level parameters of a stored rule are the recursor's when the generated rule's
are (`hlpd`); the major premise of `tyC` is headed by the family at the block's level
parameters (`hmaj`). -/
theorem nativeRecJ_of_parts {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    {cvS : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hT : env.find? fam.p.cvT.name = some (.indInfo cvS caps))
    (hctorsFind : ∀ c4 ∈ Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds,
      (env.find? c4.1).isSome = true ∧ (∀ cv v hn, env.find? c4.1 ≠ some (.defnInfo cv v hn)))
    {k : Nat} (hL1 : fam.p.cvT.levelParams = List.range k) (large : Bool)
    (htty : Decl.GenScoped env (Ix.Kernel.Reader.recLps large (List.range k)) 0 fam.cvTa.type)
    (htst : ∃ tbs tsort, fam.cvTa.type.stripPis (fam.p.nP + fam.p.nIdx) = some (tbs, tsort))
    (hcs : ∀ c4 ∈ Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds,
      Decl.GenScoped env (Ix.Kernel.Reader.recLps large (List.range k)) 0 c4.2.2.1 ∧
      (∀ i ∈ c4.2.2.2, i < c4.2.1) ∧
      ∃ cbs cbody, c4.2.2.1.stripPis (fam.p.nP + c4.2.1) = some (cbs, cbody))
    {R : Ix.Kernel.Key .anon} (hRfresh : env.find? R = none)
    {ty tyC recTy : Ix.Kernel.Expr .anon} {rules rlsC : List (Ix.Kernel.RecRule .anon)}
    (hcv : Ix.Kernel.Semantics.ConstantValCheckJ rulesJ env
      ⟨R, Ix.Kernel.Reader.recLps large (List.range k), ty⟩
      ⟨R, Ix.Kernel.Reader.recLps large (List.range k), tyC⟩)
    (hrec : Ix.Kernel.structRecTyR fam.p.cvT.name fam.p.cvT.levelParams
      (if large then k else 0) large fam.p.nP fam.p.nIdx fam.cvTa.type
      (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) = some recTy)
    (hwrap : Decl.WrapRelSem env.find? recTy tyC)
    (hannT : IxVM.Consistency.Annotates tyC ty)
    (hstored : List.Forall₂ IxVM.Consistency.RuleStored rlsC rules)
    (hlen : rlsC.length = fam.ctorsA.length)
    (hrules : ∀ (j : Nat) (hlt : j < rlsC.length), ∃ rhsG,
      Ix.Kernel.structRecRhsR fam.p.cvT.name (List.range k) (if large then k else 0) large
        fam.p.nP fam.p.nIdx fam.cvTa.type (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) R
        ((Ix.Kernel.Reader.recLps large (List.range k)).map .param) j = some rhsG ∧
      Decl.WrapRelSem env.find? rhsG (rlsC[j]'hlt).rhs)
    (hrd : ∀ rl ∈ rules, rl.rhs.hasFvar = false ∧ rl.rhs.looseBVarsBounded 0 = true)
    (hlpd : ∀ (j : Nat) (hlt : j < rlsC.length) (rhsG : Ix.Kernel.Expr .anon),
      Ix.Kernel.structRecRhsR fam.p.cvT.name (List.range k) (if large then k else 0) large
        fam.p.nP fam.p.nIdx fam.cvTa.type (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) R
        ((Ix.Kernel.Reader.recLps large (List.range k)).map .param) j = some rhsG →
      rhsG.allLevelParamsDefined (Ix.Kernel.Reader.recLps large (List.range k)) = true →
      (rlsC[j]'hlt).rhs.allLevelParamsDefined
        (Ix.Kernel.Reader.recLps large (List.range k)) = true)
    (hmaj : ∀ bs dom B m, tyC.stripPis (fam.p.nP + 1 + fam.p.ctors.length + fam.p.nIdx) =
      some (bs, .forallE dom B m) → ∃ K, dom.getAppFn = .const K (fam.p.cvT.levelParams.map .param)) :
    NativeRecJ rulesJ env
      (fam.recParts ⟨R, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ (if large then k else 0)
        large (rules.map (·.rhs)))
      fam.cvTa fam.ctorsA ⟨R, Ix.Kernel.Reader.recLps large (List.range k), tyC⟩
      (rlsC.map (·.rhs)) := by
  -- the block's level parameters, and the elimination parameter, are the recursor's
  have hlps_sub : ∀ x ∈ fam.p.cvT.levelParams,
      x ∈ Ix.Kernel.Reader.recLps large (List.range k) := by
    intro x hx
    rw [hL1, List.mem_range] at hx
    rcases Bool.eq_false_or_eq_true large with hl | hl <;>
      simp [hl, Ix.Kernel.Reader.recLps, List.mem_range, hx]
  have helim_mem : large = true →
      (if large then k else 0) ∈ Ix.Kernel.Reader.recLps large (List.range k) := by
    intro hl
    simp [hl, Ix.Kernel.Reader.recLps]
  -- the generated type is scoped, and the declared type is convertible with it
  have hT_res : (env.find? fam.p.cvT.name).isSome = true := by rw [hT]; rfl
  have hT_nd : ∀ cv v hn, env.find? fam.p.cvT.name ≠ some (.defnInfo cv v hn) := by
    intro cv v hn hf
    rw [hT] at hf
    exact nomatch hf
  have hsc_recTy : Decl.GenScoped env (Ix.Kernel.Reader.recLps large (List.range k)) 0 recTy :=
    Decl.GenScoped.structRecTyR hlps_sub helim_mem hT_res hT_nd htty
      (fun c4 hc4 => ⟨(hctorsFind c4 hc4).1, (hctorsFind c4 hc4).2, (hcs c4 hc4).1,
        (hcs c4 hc4).2.1⟩) hrec
  have hlf_ty : Ix.Kernel.Semantics.letFree tyC = true := Decl.annotates_letFree hannT
  have hdefeq : Ix.Kernel.Rules.DefEq env 0 tyC recTy :=
    Decl.WrapRelSem.defeq hwrap hlf_ty hsc_recTy.2.2.2.2 hsc_recTy.1
  -- the environment holding the generated recursor keeps every lookup of `env`
  let P : Ix.Kernel.NativeParts .anon :=
    fam.recParts ⟨R, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ (if large then k else 0)
      large (rules.map (·.rhs))
  let cvRg : Ix.Kernel.ConstantVal .anon :=
    ⟨R, Ix.Kernel.Reader.recLps large (List.range k), recTy⟩
  let envR : Ix.Kernel.Env .anon := ⟨.recInfo cvRg P.majorIdx P.rulePrefix [] :: env.consts⟩
  have hsub : ∀ m ci, env.find? m = some ci → envR.find? m = some ci :=
    fun m ci hci => Ix.Kernel.Env.find?_cons_of_fresh hRfresh hci
  have hno_defn : ∀ n cv v hn, envR.find? n = some (.defnInfo cv v hn) →
      env.find? n = some (.defnInfo cv v hn) := by
    intro n cv v hn hf
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · exact nomatch hf
    · exact hf
  have hsome : ∀ m, (env.find? m).isSome = true → (envR.find? m).isSome = true := by
    intro m hm
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hm
    rw [hsub m ci hci]
    rfl
  have hnd : ∀ m, (∀ cv v hn, env.find? m ≠ some (.defnInfo cv v hn)) →
      ∀ cv v hn, envR.find? m ≠ some (.defnInfo cv v hn) :=
    fun m h cv v hn hf => h cv v hn (hno_defn m cv v hn hf)
  have hgs : ∀ e, Decl.GenScoped env (Ix.Kernel.Reader.recLps large (List.range k)) 0 e →
      Decl.GenScoped envR (Ix.Kernel.Reader.recLps large (List.range k)) 0 e :=
    fun e h => ⟨h.1, h.2.1, Decl.constsResolve_mono_env hsub h.2.2.1, h.2.2.2.1,
      Decl.defnAritiesOk_congr_defn hno_defn e h.2.2.2.2⟩
  have hR_find : envR.find? R = some (.recInfo cvRg P.majorIdx P.rulePrefix []) :=
    Ix.Kernel.Env.find?_cons_self _ env
  -- the generated rules, scoped at the environment holding the generated recursor
  obtain ⟨rhsG, hchk, hrhsG_len, hrhsG_get⟩ :=
    Decl.checkNativeRules_ok_go (envR := envR)
      (rlps := Ix.Kernel.Reader.recLps large (List.range k))
      (lps := fam.p.cvT.levelParams) (T := fam.p.cvT.name) (recC := R)
      (elim := if large then k else 0) (large := large) (nP := fam.p.nP) (nIdx := fam.p.nIdx)
      (tty := fam.cvTa.type) (ctors := Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds)
      hlps_sub helim_mem (hsome _ hT_res) (hnd _ hT_nd)
      (by rw [hR_find]; rfl)
      (fun cv v hn hf => by rw [hR_find] at hf; exact nomatch hf)
      (hgs _ htty) htst
      (fun c4 hc4 => ⟨hsome _ (hctorsFind c4 hc4).1, hnd _ (hctorsFind c4 hc4).2,
        hgs _ (hcs c4 hc4).1, (hcs c4 hc4).2.1, (hcs c4 hc4).2.2⟩)
      (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds).length 0 (Nat.zero_add _)
  -- one generated rule per stored rule
  have hle4 : (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds).length ≤ fam.ctorsA.length := by
    unfold Ix.Kernel.nativeCtors4
    rw [List.length_zipWith]
    exact Nat.min_le_left _ _
  have hlen4 : (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds).length = rlsC.length := by
    rcases Nat.eq_zero_or_pos rlsC.length with h0 | hpos
    · omega
    · obtain ⟨g, hg, _⟩ := hrules (rlsC.length - 1) (by omega)
      have := lt_of_structRecRhsR_some hg
      omega
  have hlenG : rhsG.length = rlsC.length := by rw [hrhsG_len, hlen4]
  have hidx : ∀ (j : Nat) (hj : j < rlsC.length), ∃ g, rhsG[j]? = some g ∧
      Ix.Kernel.structRecRhsR fam.p.cvT.name (List.range k) (if large then k else 0) large
        fam.p.nP fam.p.nIdx fam.cvTa.type (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) R
        ((Ix.Kernel.Reader.recLps large (List.range k)).map .param) j = some g ∧
      Decl.GenScoped envR (Ix.Kernel.Reader.recLps large (List.range k)) 0 g := by
    intro j hj
    obtain ⟨g, hget, hR, hsc⟩ := hrhsG_get j (by omega)
    rw [hL1, Nat.zero_add] at hR
    exact ⟨g, hget, hR, hsc⟩
  -- the stored rules are the generated ones with wrappers consumed
  have hwrap_rules : Ix.Kernel.Semantics.Forall₂ (Ix.Kernel.Semantics.WrapRel env.find?) rhsG
      (rlsC.map (·.rhs)) := by
    refine semForall₂_of_getElem (by rw [List.length_map]; exact hlenG) fun j h₁ h₂ => ?_
    have hj : j < rlsC.length := by rwa [List.length_map] at h₂
    obtain ⟨g, hget, hR, _⟩ := hidx j hj
    obtain ⟨g', hR', hw⟩ := hrules j hj
    have hgg : g = g' := Option.some.inj (hR.symm.trans hR')
    subst hgg
    rw [List.getElem?_eq_getElem h₁, Option.some.injEq] at hget
    rw [hget]
    simp only [List.getElem_map]
    exact Decl.WrapRelSem.toWrapRel hw
  -- the stored rules carry no `let`, and their level parameters are the recursor's
  have hlf_rules : ∀ r ∈ rlsC.map (·.rhs), Ix.Kernel.Semantics.letFree r = true := by
    intro r hr
    obtain ⟨rl, hrl, rfl⟩ := List.mem_map.mp hr
    obtain ⟨rl₀, _, hst⟩ := forall₂_left_mem hstored rl hrl
    exact Decl.annotates_letFree hst.2.2
  have hlpd_rules : ∀ r ∈ rlsC.map (·.rhs),
      r.allLevelParamsDefined (Ix.Kernel.Reader.recLps large (List.range k)) = true := by
    intro r hr
    obtain ⟨rl, hrl, rfl⟩ := List.mem_map.mp hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrl
    obtain ⟨g, _, hR, hsc⟩ := hidx j hj
    exact hlpd j hj g hR hsc.2.1
  -- the stage and the stored recursor
  exact ⟨cvRg, rhsG,
    ⟨nativeRecLpsOk_recParts fam R ty hL1 large _, rfl,
      ⟨R, Ix.Kernel.Reader.recLps large (List.range k), tyC⟩, recTy, hcv, hrec,
      hsc_recTy.2.1, hsc_recTy.2.2.1, hsc_recTy.1, hsc_recTy.2.2.2.1, hdefeq, hchk, rfl⟩,
    Or.inr ⟨⟨R, Ix.Kernel.Reader.recLps large (List.range k), tyC⟩, hcv, rfl,
      Decl.WrapRelSem.toWrapRel hwrap, hwrap_rules, hlf_rules,
      annot_rules_of_stored _ hstored hrd, hlf_ty, hlpd_rules, hmaj⟩⟩

end IxVM.Refinement.Typing
