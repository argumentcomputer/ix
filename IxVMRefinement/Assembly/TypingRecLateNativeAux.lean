import IxVMRefinement.Assembly.TypingRecLateStep
import IxVMRefinement.Assembly.FoldClause
import IxVMRefinement.Decl.LateNatRecCheckT

/-! # The registry entry's data for the native recursor comparison at the arm

The native recursor comparison (`Decl.late_nat_rec_check_spec_traced`) reads the matched family's
stored constructors as a list of entries `(C, nF, R₀, C₀, recIdx)` (`lateCtorsInfo`: the stored
constructor's key, field count and type, and the recursive field indices of its kinds), and
asks, of each entry, the well-formedness facts `Decl.NatCtorInfoWfT`. This module states:

* `FamCtorNoProj`: no constructor type of the family projects out of the family, a fact of the
  registry entry (the constructor stage of the native block's step) that the store does not
  carry;
* `lateCtorsInfo` and its facts: the entries are the family's `nativeCtors4`, and each entry
  meets `NatCtorInfoWfT` at the family; the former's and the constructors' stored types are
  `GenScoped` at the environment.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantVal LevelParam)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-- **No stored constructor type of the family projects out of the family**
(`Decl.NatCtorInfoWfT.noProj_C`, read by `nat_rec_idx`'s specification through
`natT_ctor_spec`). The constructor stage of the native block's step gives it at admission
(`Decl.noProjAt_of_infer_full`, where the family has no projection yet); neither the store nor
the registry entry carries it, and the recursor's run does not check it. -/
def FamCtorNoProj (fam : NativeFam .anon) : Prop :=
  ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
    Decl.noProjAt fam.p.cvT.name cA.1.type = true

/-- **The comparison's constructor entries at a family**: per stored constructor, its key, its
field count, its stored type (twice: the raw slot is not read by the stored-type
specifications) and the recursive field indices of its kinds. -/
def lateCtorsInfo (fam : NativeFam .anon) :
    List (Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat) :=
  List.zipWith (fun cA ks => (cA.1.name, cA.2, cA.1.type, cA.1.type, Ix.Kernel.recIdxOf ks))
    fam.ctorsA fam.p.kinds

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Level parameters and arities of the stored types -/

private theorem lateAux_level_alpd_mono {ps qs : List LevelParam}
    (hsub : ∀ x ∈ ps, x ∈ qs) {u : Ix.Kernel.Level}
    (h : u.allParamsDefined ps = true) : u.allParamsDefined qs = true := by
  induction u with
  | zero => rfl
  | succ l ih => exact ih h
  | max l r ihl ihr | imax l r ihl ihr =>
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h ⊢
    exact ⟨ihl h.1, ihr h.2⟩
  | param n =>
    simp only [Ix.Kernel.Level.allParamsDefined, List.contains_iff_mem] at h ⊢
    exact hsub n h

private theorem lateAux_pw_paramsDefined_mono {ps qs : List LevelParam}
    (hsub : ∀ x ∈ ps, x ∈ qs) {pw : Ix.Kernel.PropWhen}
    (h : pw.paramsDefined ps = true) : pw.paramsDefined qs = true := by
  unfold Ix.Kernel.PropWhen.paramsDefined at h ⊢
  split at h
  · rfl
  · rfl
  · simp only [List.contains_iff_mem] at h ⊢
    exact hsub _ h
  · simp only [Bool.and_eq_true, List.contains_iff_mem] at h ⊢
    exact ⟨hsub _ h.1, hsub _ h.2⟩
  · simp only [List.all_eq_true, List.contains_iff_mem] at h ⊢
    exact fun x hx => hsub x (h x hx)

/-- Level-parameter coverage is monotone in the parameter list. -/
private theorem lateAux_alpd_mono {ps qs : List LevelParam}
    (hsub : ∀ x ∈ ps, x ∈ qs) {e : Core.KExpr}
    (he : e.allLevelParamsDefined ps = true) :
    e.allLevelParamsDefined qs = true := by
  induction e with
  | bvar _ | lit _ => rfl
  | sort u => exact lateAux_level_alpd_mono hsub he
  | const _ us =>
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, List.all_eq_true] at he ⊢
    exact fun v hv => lateAux_level_alpd_mono hsub (he v hv)
  | fvar _ ty iht =>
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at he ⊢
    exact iht he
  | app f a ihf iha =>
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at he ⊢
    exact ⟨ihf he.1, iha he.2⟩
  | lam ty body m iht ihb | forallE ty body m iht ihb =>
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at he ⊢
    exact ⟨⟨iht he.1.1, ihb he.1.2⟩, lateAux_pw_paramsDefined_mono hsub he.2⟩
  | letE ty val body _ iht ihv ihb =>
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at he ⊢
    exact ⟨⟨iht he.1.1, ihv he.1.2⟩, ihb he.2⟩
  | proj _ _ sub ih =>
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at he ⊢
    exact ih he

/-- **An arity-correct term is arity-correct at the stored definitions**: `arOk` asks the level
count of every stored constant the term names, `defnAritiesOk` only of the stored definitions
(and reads no `fvar`'s type). -/
theorem defnAritiesOk_of_arOk {env : Ix.Kernel.Env .anon} :
    ∀ {e : Core.KExpr}, Ix.Kernel.Expr.arOk env e = true →
      Decl.defnAritiesOk env.find? e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ => intro _; rfl
  | fvar _ _ _ => intro _; rfl
  | const n us =>
    intro h
    simp only [Ix.Kernel.Expr.arOk] at h
    simp only [Decl.defnAritiesOk]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      rw [hf] at h
      cases ci <;> first | rfl | exact h
  | app f a ihf iha =>
    intro h
    simp only [Ix.Kernel.Expr.arOk, Bool.and_eq_true] at h
    simp only [Decl.defnAritiesOk, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b _ iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.arOk, Bool.and_eq_true] at h
    simp only [Decl.defnAritiesOk, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b _ iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.arOk, Bool.and_eq_true] at h
    simp only [Decl.defnAritiesOk, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | letE t v b _ iht ihv ihb =>
    intro h
    simp only [Ix.Kernel.Expr.arOk, Bool.and_eq_true] at h
    simp only [Decl.defnAritiesOk, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj _ _ e ih =>
    intro h
    simp only [Ix.Kernel.Expr.arOk] at h
    simp only [Decl.defnAritiesOk]
    exact ih h

/-! ## The entries -/

/-- The entries without the raw slot are the family's `nativeCtors4`. -/
theorem lateCtorsInfo_map (fam : NativeFam .anon) :
    (lateCtorsInfo fam).map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2)) =
      Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds := by
  unfold lateCtorsInfo Ix.Kernel.nativeCtors4
  exact List.map_zipWith.trans rfl

/-- One entry per stored constructor. -/
theorem lateCtorsInfo_length {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    (hfam : NativeFamStored env fam) : (lateCtorsInfo fam).length = fam.ctorsA.length := by
  unfold lateCtorsInfo
  rw [List.length_zipWith]
  have := hfam.lenK
  omega

/-- The entry at a stored constructor: its key, field count, stored type (twice) and the
recursive field indices of its kinds. -/
theorem lateCtorsInfo_getElem? {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    (hfam : NativeFamStored env fam) {j : Nat} {cA : ConstantVal .anon × Nat}
    (hcA : fam.ctorsA[j]? = some cA) :
    ∃ ks, fam.p.kinds[j]? = some ks ∧
      (lateCtorsInfo fam)[j]? =
        some (cA.1.name, cA.2, cA.1.type, cA.1.type, Ix.Kernel.recIdxOf ks) := by
  obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hcA
  have hjK : j < fam.p.kinds.length := by have := hfam.lenK; omega
  refine ⟨fam.p.kinds[j]'hjK, List.getElem?_eq_getElem hjK, ?_⟩
  unfold lateCtorsInfo
  exact List.getElem?_zipWith_eq_some.mpr ⟨cA, _, hcA, List.getElem?_eq_getElem hjK, rfl⟩

/-- A successful `mapM` in `Option` relates the inputs and the outputs position by position. -/
private theorem lateAux_mapM_option_getElem? {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r →
      ∀ {j : Nat} {a : α}, l[j]? = some a → ∃ b, r[j]? = some b ∧ f a = some b
  | [], _, _, _, _, ha => by simp at ha
  | x :: l, r, h, j, a, ha => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst ha
      exact ⟨b, rfl, hb⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at ha ⊢
      exact lateAux_mapM_option_getElem? hbs ha

/-- **The kinds of a registered family's constructor**: the recogniser's reading of the stored
constructor, with no non-positive and no unmodeled field. -/
private theorem lateAux_kinds_at {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hat : FamRead L t E env fam)
    {j : Nat} {cA : ConstantVal .anon × Nat} {ks : List Ix.Kernel.RecFieldKind}
    (hcA : fam.ctorsA[j]? = some cA) (hks : fam.p.kinds[j]? = some ks) :
    Ix.Kernel.recCtorKinds fam.p.cvT.name fam.p.cvT.levelParams fam.p.nP fam.p.nIdx cA =
        some ks ∧
      ∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported := by
  obtain ⟨hmapM, hneg, huns, _⟩ := Ix.Kernel.classifyFixKinds_inv hat.kinds
  obtain ⟨ks', hks', hrck⟩ := lateAux_mapM_option_getElem? hmapM hcA
  rw [hks] at hks'
  have hks_eq : ks = ks' := Option.some.inj hks'
  subst hks_eq
  refine ⟨hrck, fun k hk => ?_⟩
  have hmem : ks ∈ fam.p.kinds := List.mem_of_getElem? hks
  have h1 := List.any_eq_false.mp hneg ks hmem
  have h2 := List.any_eq_false.mp huns ks hmem
  refine ⟨fun he => h1 ?_, fun he => h2 ?_⟩
  · exact List.any_eq_true.mpr ⟨k, hk, by simp [he]⟩
  · exact List.any_eq_true.mpr ⟨k, hk, by simp [he]⟩

/-- **Every entry is well formed at the family** (`Decl.NatCtorInfoWfT`): the stored type's
level parameters from the environment's well-formedness, its freedom from projections of the
family from `FamCtorNoProj`, its return position from the store, and the recursive field
indices from the kinds. No count bound is among the facts: the comparison reads each
constructor's field count with its load. -/
theorem lateCtorsInfo_wf {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {fam : NativeFam .anon} {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hat : FamRead L t E env fam) (henv : Ix.Kernel.EnvWF env) {k : Nat}
    (hk : fam.p.cvT.levelParams = List.range k) (hnoProj : FamCtorNoProj fam) (large : Bool) :
    ∀ info ∈ lateCtorsInfo fam,
      Decl.NatCtorInfoWfT fam.p.cvT.name k large fam.p.nP fam.p.nIdx (lateCtorsInfo fam).length
        info := by
  intro info hinfo
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hinfo
  have hj' := hj
  unfold lateCtorsInfo at hj'
  obtain ⟨cA, ks, hcA, hks, hf⟩ := List.getElem?_zipWith_eq_some.mp hj'
  have hinfo_eq : info = (cA.1.name, cA.2, cA.1.type, cA.1.type, Ix.Kernel.recIdxOf ks) :=
    hf.symm
  subst hinfo_eq
  obtain ⟨hfind, hlpsC, cbs, es, hsC, hes⟩ := hat.stored.ctor j cA hcA
  obtain ⟨hrck, hok⟩ := lateAux_kinds_at hat hcA hks
  -- the stored type's level parameters
  have hwfC := henv _ (Ix.Kernel.Semantics.Env.find?_mem hfind)
  have hlpC0 : cA.1.type.allLevelParamsDefined cA.1.levelParams = true := hwfC.2.1
  have hlpC : cA.1.type.allLevelParamsDefined (List.range k) = true := by
    rw [hlpsC, hk] at hlpC0
    exact hlpC0
  exact
    { lps_C := hlpC
      noProj_C := hnoProj j cA hcA
      strip_C := ⟨cbs, _, _, hsC⟩
      recIdx_eq := fun ecbs ebody hsE => Decl.recIdxOf_eq_recIdxFrom hrck hok hsC hsE }

/-! ## The stored types are scoped at the environment -/

/-- **The telescope constant's type is `GenScoped`** at the environment, at every
level-parameter list covering the family's: what the recursor generators read of it, from the
facts the former's stage checked (`TeleChecked`). The telescope constant need not be the stored
former. -/
theorem late_former_genScoped {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hat : FamRead L t E env fam)
    {rlps : List LevelParam} (hsub : ∀ x ∈ fam.p.cvT.levelParams, x ∈ rlps) :
    Decl.GenScoped env rlps 0 fam.cvTa.type :=
  ⟨hat.tele.bounded, lateAux_alpd_mono hsub hat.tele.levels, hat.tele.arRes.res,
    hat.tele.closed, defnAritiesOk_of_arOk hat.tele.arRes.ar⟩

/-- **Each constructor of the family, as the generators read it**: stored, not a definition, its
type `GenScoped` at the environment, its recursive field indices field indices, and its type
with the parameter and field binders. -/
theorem late_ctors_genScoped {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hat : FamRead L t E env fam)
    (henv : Ix.Kernel.EnvWF env) (hlv : LvClauses env) {rlps : List LevelParam}
    (hsub : ∀ x ∈ fam.p.cvT.levelParams, x ∈ rlps) :
    ∀ c4 ∈ Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds,
      (env.find? c4.1).isSome = true ∧
      (∀ cv v hn, env.find? c4.1 ≠ some (.defnInfo cv v hn)) ∧
      Decl.GenScoped env rlps 0 c4.2.2.1 ∧
      (∀ i ∈ c4.2.2.2, i < c4.2.1) ∧
      ∃ cbs cbody, c4.2.2.1.stripPis (fam.p.nP + c4.2.1) = some (cbs, cbody) := by
  intro c4 hc4
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc4
  unfold Ix.Kernel.nativeCtors4 at hj
  obtain ⟨cA, ks, hcA, hks, hf⟩ := List.getElem?_zipWith_eq_some.mp hj
  have hc4_eq : c4 = (cA.1.name, cA.2, cA.1.type, Ix.Kernel.recIdxOf ks) := hf.symm
  subst hc4_eq
  obtain ⟨hfind, hlpsC, cbs, es, hsC, hes⟩ := hat.stored.ctor j cA hcA
  obtain ⟨hrck, hok⟩ := lateAux_kinds_at hat hcA hks
  have hwf := henv _ (Ix.Kernel.Semantics.Env.find?_mem hfind)
  have hfv : cA.1.type.hasFvar = false := hwf.1
  have hlp : cA.1.type.allLevelParamsDefined cA.1.levelParams = true := hwf.2.1
  have hcr : cA.1.type.constsResolve env = true := hwf.2.2.1
  have hlb : cA.1.type.looseBVarsBounded 0 = true := hwf.2.2.2.1
  have har : Ix.Kernel.Expr.arOk env cA.1.type = true := (hlv.2.const hfind).type.ar
  rw [hlpsC] at hlp
  refine ⟨?_, ?_, ?_, ?_, cbs, _, hsC⟩
  · show (env.find? cA.1.name).isSome = true
    simp only [hfind, Option.isSome_some]
  · intro cv v hn h
    have h' : env.find? cA.1.name = some (.defnInfo cv v hn) := h
    rw [hfind] at h'
    exact nomatch h'
  · exact ⟨hlb, lateAux_alpd_mono hsub hlp, hcr, hfv, defnAritiesOk_of_arOk har⟩
  · intro i hi
    exact (Decl.recIdxOf_mem_mentionsConst hrck hok hsC hi).1

end IxVM.Refinement.Typing
