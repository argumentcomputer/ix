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

**The major's set at the major domain's levels.** The relation gives the major's set as the
constructor's image at the assignment the constructor value was built at; ι names the image at
the levels the major domain names. Where the constructor has no level parameters (every flat
recursor of the measured closures: `Bool.rec`), its image is the same set at every assignment
(`ctorImage_noLevels`, by `Laws.cval_params`): no canonicity. Where it has some, canonicity at the
inductive, which the class asks to be never a proposition (`ctorImage_canon`, by the restricted
`Laws.ctor_canon`), reading the constructor's codomain as `RecCtorsRaw` checks it.

**What it assumes of the model, and why each holds in a proof-irrelevant set model.**

* `Laws.iota_rule` (ι) at a stored rule of a recursor whose inductive is never a proposition, at
  the recursor's own level parameters: proved on the side that owes the laws for every stored rule;
  in this repository the kernel's own model proves the rule law for canonical (`.plain`) rules
  (`iotaRulePlain`, `IxCK/Kernel/Model/IotaRulePlain.lean`). Tested against the kernel on the
  measured recursors (`Bool.rec` in seven closures, the enumeration recursors of `tags16` and
  `tags17`, `Nat.rec`, `List.rec`: each rule at its constructor reduces to its minor premise and
  not to another; probes `GR-3f-q1`, `q3`, `k1`, not in the suite).
* `Laws.cval_params` (a constant depends on the level assignment only through its own parameters):
  proved on that side; here only at constructors without level parameters, where it says that
  their image is one set.
* `Laws.ctor_canon`, restricted to families that are never propositions, only where a flat
  recursor's constructor has level parameters (no measured closure has one): the same kind of
  instance the generic `case` lemma uses (`caseFires_of_shape`), with no parameter and no field.
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
the major premise's set as the rule constructor's image at the levels the major domain names.
Of the laws it takes ι alone (`Laws.iota_rule`). -/
theorem flatIota (M : Model V env) (hι : IotaLaw M.cval env) {kr : KKey}
    {cvr : ConstantVal .anon} {mI : Nat}
    {krules : List (RecRule .anon)} (hf : env.find? kr = some (.recInfo cvr mI mI krules))
    {tbs : List (KExpr × BinderMeta)} {C : KExpr} (hty : cvr.type = piTele tbs C)
    (htbs : tbs.length = mI) {krl : RecRule .anon} (hkrl : krl ∈ krules)
    {cvC : ConstantVal .anon} (hcC : env.find? krl.ctor = some (.ctorInfo cvC 0 0))
    (hcod : cvC.type.getAppArgs = []) {i : Nat} {bs : List (KExpr × BinderMeta)}
    (hrhs : krl.rhs = lamTele bs (.bvar i)) (hbs : bs.map (·.1) = tbs.map (·.1)) (hi : i < mI)
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hfit : Fits M.cval env φ ρ cvr.type As σ R) (hlen : As.length = mI + 1)
    {dom body : KExpr} {m : BinderMeta} {D : KKey} {ls : List Level}
    (hpb : piBody mI cvr.type = .forallE dom body m) (hdom : dom.getAppFn = .const D ls)
    {K : V}
    (hK : ∀ τ X, Denotes M.cval env φ τ dom X → K ∈ˢ X → Denotes M.cval env φ ρ (.const krl.ctor ls) K)
    (hmaj : As[mI]? = some K) :
    ∃ X, (As.take mI).reverse[i]? = some X ∧ As.foldl app (M.cval kr φ) = X := by
  have hbsl : bs.length = mI := by
    have := congrArg List.length hbs
    simp only [List.length_map] at this
    omega
  -- the arguments: the prefix and the major
  have hdrop : As.drop mI = [K] := by
    rw [List.getElem?_eq_getElem (by omega)] at hmaj
    rw [List.drop_eq_getElem_cons (by omega), Option.some.inj hmaj,
      List.drop_eq_nil_of_le (by omega)]
  have hsplit : As = As.take mI ++ [K] := by rw [← hdrop, List.take_append_drop]
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
    rw [getAppArgs_inst, hcod, List.drop_eq_nil_of_le (as := As.take mI) (by omega)]
    exact .nil
  obtain ⟨H, hH, heq⟩ := hι kr cvr mI mI krules krl hf hkrl cvC 0 0 hcC
    (cvr.levelParams.map .param) φ ρ σ1 ρ (As.take mI) [] dom body
    (cvC.type.instantiateLevelParams cvC.levelParams ls) m D ls (M.cval kr φ) K X (by simp) hxl
    rfl hRden (by rw [inst_self]; exact hf1) hdom hX (hK σ1 X hX hKX) .nil (by simpa using hKX)
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
    rw [List.getElem?_eq_getElem (by rw [List.length_reverse, hxl]; omega)]
    rfl
  · have e2 : (As.take mI).take mI ++ ([] : List V).drop 0 = As.take mI := by
      rw [List.take_take, Nat.min_self, List.drop_zero, List.append_nil]
    rw [e2] at heq
    have e1 : As.foldl app (M.cval kr φ) =
        (As.take mI ++ [([] : List V).foldl app K]).foldl app (M.cval kr φ) := by
      rw [List.foldl_nil, ← hsplit]
    rw [e1, heq, hYe]

/-- **A constructor without level parameters, used at none, denotes its image at any assignment**
(`Laws.cval_params`; no canonicity): so the major's set, built at the constructor value's own
assignment, is the image ι names. -/
theorem ctorImage_noLevels (M : Model V env) (hcv : CvalParams M) {c : KKey}
    {cvC : ConstantVal .anon}
    {nP nF : Nat} (hcC : env.find? c = some (.ctorInfo cvC nP nF)) (hlp : cvC.levelParams = [])
    (φ ψ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ (.const c []) (M.cval c ψ) := by
  have h1 : Denotes M.cval env φ ρ (.const c [])
      (M.cval c (Level.substFn φ cvC.levelParams [])) :=
    Denotes.const (ci := .ctorInfo cvC nP nF) hcC (by simp [ConstantInfo.toConstantVal, hlp])
  rwa [hcv c _ hcC (Level.substFn φ cvC.levelParams []) ψ
    (fun q hq => by simp [ConstantInfo.toConstantVal, hlp] at hq)] at h1

/-- **F2 at a flat recursor whose rule's constructor has no level parameters, from ι and
level-parameter irrelevance alone** (no canonicity: its hypotheses name the two laws it uses,
`Laws.iota_rule` and `Laws.cval_params`, both proved on the side that owes them). Every flat
recursor of the measured closures is of this kind (`Bool.rec`). -/
theorem flatIota_noLevels (M : Model V env) (hι : IotaLaw M.cval env) (hcv : CvalParams M)
    {kr : KKey} {cvr : ConstantVal .anon} {mI : Nat} {krules : List (RecRule .anon)}
    (hf : env.find? kr = some (.recInfo cvr mI mI krules))
    {tbs : List (KExpr × BinderMeta)} {C : KExpr} (hty : cvr.type = piTele tbs C)
    (htbs : tbs.length = mI) {krl : RecRule .anon} (hkrl : krl ∈ krules)
    {cvC : ConstantVal .anon} (hcC : env.find? krl.ctor = some (.ctorInfo cvC 0 0))
    (hlp : cvC.levelParams = []) (hcod : cvC.type.getAppArgs = []) {i : Nat}
    {bs : List (KExpr × BinderMeta)} (hrhs : krl.rhs = lamTele bs (.bvar i))
    (hbs : bs.map (·.1) = tbs.map (·.1)) (hi : i < mI)
    {φ ψ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hfit : Fits M.cval env φ ρ cvr.type As σ R) (hlen : As.length = mI + 1)
    {dom body : KExpr} {m : BinderMeta} {D : KKey} {ls : List Level}
    (hpb : piBody mI cvr.type = .forallE dom body m) (hdom : dom.getAppFn = .const D ls)
    (hls : cvC.levelParams.length = ls.length) (hmaj : As[mI]? = some (M.cval krl.ctor ψ)) :
    ∃ X, (As.take mI).reverse[i]? = some X ∧ As.foldl app (M.cval kr φ) = X := by
  have hls0 : ls = [] := List.eq_nil_of_length_eq_zero (by rw [← hls, hlp]; rfl)
  subst hls0
  exact flatIota M hι hf hty htbs hkrl hcC hcod hrhs hbs hi hfit hlen hpb hdom
    (fun _ _ _ _ => ctorImage_noLevels M hcv hcC hlp φ ψ ρ) hmaj

/-- **A field-less constructor without parameters, built at any assignment, is its image at the
levels a member's family names, by canonicity** (`Laws.ctor_canon`, at a family never a
proposition): what ι needs where the constructor has level parameters. -/
theorem ctorImage_canon (M : Model V env) (hL : Laws M) {c D : KKey} {cvC : ConstantVal .anon}
    (hcC : env.find? c = some (.ctorInfo cvC 0 0)) (hnd : cvC.levelParams.Nodup)
    (hhead : cvC.type.getAppFn = .const D (cvC.levelParams.map .param)) (hN : NeverProp env D)
    {ls : List Level} (hls : cvC.levelParams.length = ls.length)
    {φ ψ : LevelParam → Nat} {ρ τ : BVarIdx → V} {dom : KExpr} {X : V}
    (hdom : dom.getAppFn = .const D ls) (hX : Denotes M.cval env φ τ dom X)
    (hm : M.cval c ψ ∈ˢ X) :
    Denotes M.cval env φ ρ (.const c ls) (M.cval c ψ) := by
  obtain ⟨ls'', hls''⟩ : ∃ ls'' : List Level,
      ls'' = cvC.levelParams.map fun q => lvlOf (ψ q) := ⟨_, rfl⟩
  have hψ : ∀ q ∈ cvC.levelParams, Level.substFn φ cvC.levelParams ls'' q = ψ q := by
    intro q hq
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    rw [substFn_at φ cvC.levelParams ls'' i q (lvlOf (ψ q)) hnd hi
      (by rw [hls'', List.getElem?_map, hi]; rfl), eval_lvlOf]
  have hK' : Denotes M.cval env φ ρ (.const c ls'') (M.cval c ψ) := by
    have h1 : Denotes M.cval env φ ρ (.const c ls'')
        (M.cval c (Level.substFn φ cvC.levelParams ls'')) :=
      Denotes.const (ci := .ctorInfo cvC 0 0) hcC (by rw [hls'', List.length_map]; rfl)
    rwa [hL.cval_params _ _ hcC (Level.substFn φ cvC.levelParams ls'') ψ
      fun q hq => hψ q hq] at h1
  have hK : Denotes M.cval env φ ρ (.const c ls)
      (M.cval c (Level.substFn φ cvC.levelParams ls)) :=
    Denotes.const (ci := .ctorInfo cvC 0 0) hcC (by rw [← hls]; rfl)
  have hR'head : (cvC.type.instantiateLevelParams cvC.levelParams ls'').getAppFn =
      .const D ls'' := by
    rw [getAppFn_inst, hhead]
    simp only [Expr.instantiateLevelParams]
    rw [subst_params hnd (by rw [hls'', List.length_map])]
  -- canonicity at `D`, which is never a proposition: in a proof-irrelevant set model its
  -- constructors are read in the graph regime, and an image lying in the family at other levels
  -- is the image there
  obtain ⟨cvD, capsD, sD, hfD, hsD, hnvD⟩ := hN
  obtain ⟨heqK, -⟩ := hL.ctor_canon c cvC 0 0 hcC D cvD capsD sD ls ls'' φ ρ τ ρ dom
    (cvC.type.instantiateLevelParams cvC.levelParams ls'') [] [] [] _ _ X hfD hsD
    (eval_ne_zero_of_never hnvD _) (eval_ne_zero_of_never hnvD _) rfl rfl rfl hK hK' .nil
    hR'head hdom hX (by simp; exact .nil) (by simpa using hm)
  simp only [List.append_nil, List.foldl_nil] at heqK
  rw [heqK]
  exact hK

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
