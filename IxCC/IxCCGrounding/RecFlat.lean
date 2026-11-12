import IxCCGrounding.CaseFire

/-!
# F2 at a flat recursor, model side (`IxCCGrounding.RecFlat`; G3, part D)

**Statement** (`flatIota`). In every model with the laws, at every level assignment: a recursor
stored with major index and rule prefix `mI` (no index), whose rules' λ-domains are its type's
(`RecTele`), applied at its own level parameters to `mI + 1` sets that fit its stored type, where
the major premise's set is the image `K` of rule `j`'s constructor (no parameter, no field, a
codomain without arguments) at the levels its major domain names, is the set of the argument the
rule's body `.bvar i` names. That is what SrcEval's F2 returns at a flat recursor: the rule's
right-hand side peeled of its `mI` λs is a variable, evaluated in the slots of the first `mI`
arguments.

**Proof.** ι (`Laws.iota_rule`) at rule `j`, with no field and no parameter (so the premises on
the major's parameters and the constructor's indices are about empty lists), gives the recursor
applied to the arguments as the rule's right-hand side applied to the first `mI`; β through its
`mI` λs (their domains the type's, so the arguments lie in them by `Fits`; no regime is read,
`app_den_lam`) gives the variable's set.

**What it assumes of the model.** `Laws.iota_rule` at a stored rule of a recursor whose inductive
is never a proposition (the class asks it), at the recursor's own level parameters. How the
major's set is shown to be `K` (the constructor's image at the major domain's levels, while the
relation gives the image at the constructor value's own assignment) is the open point of part D
and is not in this lemma.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Term CId)

universe w

theorem getAppArgs_inst (ks : List LevelParam) (us : List Level) : ∀ e : KExpr,
    (e.instantiateLevelParams ks us).getAppArgs =
      e.getAppArgs.map (·.instantiateLevelParams ks us)
  | .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs, List.map_append, List.map_cons,
      List.map_nil]
    rw [getAppArgs_inst ks us f]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => rfl

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **β through a `λ`-telescope whose domains are a `∀`-telescope's** (the binder data may
differ: β does not read them). -/
theorem lamTele_app_doms {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ (bsL bsP : List (KExpr × BinderMeta)) (b C : KExpr) {ρ σ : BVarIdx → V} {F : V} {R : KExpr}
    {xs : List V}, bsL.map (·.1) = bsP.map (·.1) → Denotes cval env φ ρ (lamTele bsL b) F →
    Fits cval env φ ρ (piTele bsP C) xs σ R → xs.length = bsL.length →
      ∃ Y, Denotes cval env φ (pushAll xs ρ) b Y ∧ xs.foldl app F = Y
  | [], _, b, _, ρ, _, F, _, [], _, hF, _, _ => ⟨F, by rwa [pushAll_nil], rfl⟩
  | [], _, _, _, _, _, _, _, _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, _, _, _, _, _, _, _, [], _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, _, _, _, _ :: _, hm, _, _, _ => by simp at hm
  | (A, m) :: bsL, (A', m') :: bsP, b, C, ρ, σ, F, R, x :: xs, hm, hF, h, hl => by
    simp only [List.map_cons, List.cons.injEq] at hm
    obtain ⟨rfl, hm⟩ := hm
    have h0 : Fits cval env φ ρ (.forallE A (piTele bsP C) m') (x :: xs) σ R := h
    cases h0 with
    | cons hA hx h' =>
      have hF' : Denotes cval env φ ρ (.lam A (lamTele bsL b) m) F := hF
      obtain ⟨Y1, hY1, e1⟩ := app_den_lam hF' hA hx
      obtain ⟨Y, hY, e⟩ := lamTele_app_doms bsL bsP b C hm hY1 h' (by simpa using hl)
      exact ⟨Y, by rwa [pushAll_cons], by rw [List.foldl_cons, e1, e]⟩

/-- **F2 at a flat recursor, model side** (ι, then β through the rule's right-hand side), given
the major premise's set as the rule constructor's image at the levels the major domain names. -/
theorem flatIota (M : Model V env) (hL : Laws M) {kr : KKey} {cvr : ConstantVal .anon} {mI : Nat}
    {krules : List (RecRule .anon)} (hf : env.find? kr = some (.recInfo cvr mI mI krules))
    {tbs : List (KExpr × BinderMeta)} {C : KExpr} (hty : cvr.type = piTele tbs C)
    (htbs : tbs.length = mI) {krl : RecRule .anon} (hkrl : krl ∈ krules)
    {cvC : ConstantVal .anon} (hcC : env.find? krl.ctor = some (.ctorInfo cvC 0 0))
    (hcod : cvC.type.getAppArgs = []) {i : Nat} {bs : List (KExpr × BinderMeta)}
    (hrhs : krl.rhs = lamTele bs (.bvar i)) (hbs : bs.map (·.1) = tbs.map (·.1))
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hfit : Fits M.cval env φ ρ cvr.type As σ R) (hlen : As.length = mI + 1)
    {dom body : KExpr} {m : BinderMeta} {D : KKey} {ls : List Level}
    (hpb : piBody mI cvr.type = .forallE dom body m) (hdom : dom.getAppFn = .const D ls)
    {K : V} (hK : Denotes M.cval env φ ρ (.const krl.ctor ls) K) (hmaj : As[mI]? = some K) :
    ∃ X, (As.take mI).reverse[i]? = some X ∧ As.foldl app (M.cval kr φ) = X := by
  have hbsl : bs.length = mI := by
    have := congrArg List.length hbs
    simp only [List.length_map] at this
    omega
  -- the arguments: the prefix and the major
  have hsplit : As = As.take mI ++ [K] := by
    rw [← List.take_append_drop mI As]
    congr 1
    · simp
    · rw [List.drop_append_of_le_length (by simp; omega)]
      have hd : As.drop mI = [K] := by
        rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
        rw [List.getElem?_eq_getElem (by omega)] at hmaj
        rw [Option.some.inj hmaj]
      simp [hd]
  have hxl : (As.take mI).length = mI := by simp; omega
  have hfit' := hfit
  rw [hsplit] at hfit'
  obtain ⟨σ1, R1, hf1, hf2⟩ := fits_append hfit'
  have hR1 : R1 = .forallE dom body m := by rw [fits_piBody hf1, hxl, hpb]
  subst hR1
  obtain ⟨X, hX, hKX⟩ : ∃ X, Denotes M.cval env φ σ1 dom X ∧ K ∈ˢ X := by
    cases hf2 with
    | cons hA hx _ => exact ⟨_, hA, hx⟩
  -- ι at rule `krl`, at the recursor's own level parameters
  have hRden : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param)) (M.cval kr φ) := by
    have h1 : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param))
        (M.cval kr (Level.substFn φ cvr.levelParams (cvr.levelParams.map .param))) :=
      Denotes.const (ci := .recInfo cvr mI mI krules) hf (by simp [ConstantInfo.toConstantVal])
    rwa [substFn_self] at h1
  have hidx : DenotesList M.cval env φ ρ
      ((cvC.type.instantiateLevelParams cvC.levelParams ls).getAppArgs.drop 0)
      ((As.take mI).drop mI) := by
    rw [getAppArgs_inst, hcod, List.drop_eq_nil_of_le (by omega)]
    exact .nil
  obtain ⟨H, hH, heq⟩ := hL.iota_rule kr cvr mI mI krules krl hf hkrl cvC 0 0 hcC
    (cvr.levelParams.map .param) φ ρ σ1 ρ (As.take mI) [] dom body
    (cvC.type.instantiateLevelParams cvC.levelParams ls) m D ls (M.cval kr φ) K X (by simp) hxl
    rfl hRden (by rw [inst_self]; exact hf1) hdom hX hK .nil (by simpa using hKX)
    (by simp; exact .nil) hidx
  -- β through the rule's right-hand side
  rw [inst_self, hrhs] at hH
  have hfitP : Fits M.cval env φ ρ (piTele tbs C) (As.take mI) σ1 (.forallE dom body m) := by
    rw [← hty]; exact hf1
  obtain ⟨Y, hY, hYe⟩ := lamTele_app_doms bs tbs (.bvar i) C hbs hH hfitP (by rw [hxl, hbsl])
  refine ⟨Y, ?_, ?_⟩
  · have hy := den_bvar.mp hY
    rw [hy]
    simp only [pushAll, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    rfl
  · rw [hsplit]
    simp only [List.take_append_drop, List.drop_nil, List.append_nil] at heq ⊢
    have e1 : (As.take mI ++ [K]).foldl app (M.cval kr φ) =
        (As.take mI ++ [([] : List V).foldl app K]).foldl app (M.cval kr φ) := rfl
    rw [e1, heq]
    simpa using hYe

section Rel

variable {M : Model V env} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
  {Ok : CId → IxCC.Src.Levels → Prop}

theorem relSlots_append : ∀ {a b : List IxCC.Src.Slot} {A B : List V},
    RelSlots M κ lpsOf S Ok a A → RelSlots M κ lpsOf S Ok b B →
      RelSlots M κ lpsOf S Ok (a ++ b) (A ++ B)
  | [], _, _, _, ha, hb => by cases ha; exact hb
  | _ :: _, _, _, _, ha, hb => by
    cases ha with
    | cons hs h' => exact .cons hs (relSlots_append h' hb)

theorem relSlots_reverse : ∀ {ss : List IxCC.Src.Slot} {Xs : List V},
    RelSlots M κ lpsOf S Ok ss Xs → RelSlots M κ lpsOf S Ok ss.reverse Xs.reverse
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
    cases h with
    | cons hs h' =>
      rw [List.reverse_cons, List.reverse_cons]
      exact relSlots_append (relSlots_reverse h') (.cons hs .nil)

end Rel

end Sem

end IxCC.Grounding
