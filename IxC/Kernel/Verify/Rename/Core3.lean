module

public import IxC.Kernel.Verify.Rename.Core2

@[expose] public section

/-!
# The renaming walk through the core, part 3: ι reduction

The stuck-major rescues (`majorToCtor`), the literal majors
(`litMajorToCtor`, `projLitToCtor`), the major's preparation
(`prepareMajor`), the ι step (`iotaRec`) and the projection certificate
(`projCert`, `projCertAt`), at renamed arguments over related core records
and environments.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {env : Env md} {env' : Env md'}
variable {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}

/-! ## Free-variable leaves -/

/-- A leaf, renamed. -/
abbrev leafMap (f : md.Id → md'.Id) (l : Nat × Expr md) : Nat × Expr md' := (l.1, l.2.mapKeys f)

theorem Expr.fvarLeaves_good {e : Expr md} (he : e.Good P) : ∀ l ∈ e.fvarLeaves, l.2.Good P := by
  induction e with
  | fvar i t ih =>
    intro l hl
    rw [Expr.fvarLeaves] at hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact he
    · exact ih he l hl
  | app a b iha ihb =>
    intro l hl; rw [Expr.fvarLeaves] at hl; simp only [List.mem_append] at hl
    rcases hl with hl | hl
    · exact iha he.1 l hl
    · exact ihb he.2 l hl
  | lam t b m iht ihb =>
    intro l hl; rw [Expr.fvarLeaves] at hl; simp only [List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht he.1 l hl
    · exact ihb he.2 l hl
  | forallE t b m iht ihb =>
    intro l hl; rw [Expr.fvarLeaves] at hl; simp only [List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht he.1 l hl
    · exact ihb he.2 l hl
  | letE t v b m iht ihv ihb =>
    intro l hl; rw [Expr.fvarLeaves] at hl; simp only [List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht he.1 l hl
    · exact ihv he.2.1 l hl
    · exact ihb he.2.2 l hl
  | proj s i x ih => intro l hl; rw [Expr.fvarLeaves] at hl; exact ih he.2 l hl
  | bvar i => intro l hl; simp [Expr.fvarLeaves] at hl
  | sort u => intro l hl; simp [Expr.fvarLeaves] at hl
  | const n us => intro l hl; simp [Expr.fvarLeaves] at hl
  | lit l' => intro l hl; simp [Expr.fvarLeaves] at hl

/-- The leaf-containment guard of the rescues, renamed. -/
theorem fvarLeaves_all_contains_ren (hf : InjOn f P) {fab major : Expr md} (hfab : fab.Good P)
    (hmaj : major.Good P) :
    ((fab.mapKeys f).fvarLeaves.all fun l => (major.mapKeys f).fvarLeaves.contains l) =
      (fab.fvarLeaves.all fun l => major.fvarLeaves.contains l) := by
  rw [Expr.fvarLeaves_mapKeys, Expr.fvarLeaves_mapKeys, List.all_map]
  apply List.all_congr_mem
  intro l hl
  have hlg := Expr.fvarLeaves_good hfab l hl
  simp only [Function.comp_apply, List.contains_eq_mem, decide_eq_decide, List.mem_map]
  constructor
  · rintro ⟨l', hl', he⟩
    have hl'g := Expr.fvarLeaves_good hmaj l' hl'
    obtain ⟨l'1, l'2⟩ := l'
    obtain ⟨l1, l2⟩ := l
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, h2⟩ := he
    have h3 := Expr.mapKeys_inj hf hl'g hlg h2
    simp only at h3
    subst h3
    exact hl'
  · intro h; exact ⟨l, h, rfl⟩

/-! ## The stuck-major rescues -/

theorem majorToCtor_sim (mode : CheckMode) (hE : EnvRel P f env env') (hr : CoreSim P f r r')
    (d : Nat) (recName : Key md) {rules : List (RecRule md)} (hrules : ∀ rl ∈ rules, rl.Good P)
    {major : Expr md} (hmaj : major.Good P) :
    SimX P f (majorToCtor mode r env d recName rules major)
      (majorToCtor mode r' env' d (recName.map f) (rules.map (RecRule.mapKeys f))
        (major.mapKeys f)) := by
  unfold majorToCtor
  rw [isCtorApp_ren hE hmaj]
  refine SimE.ite Iff.rfl (fun _ => SimE.pure' hmaj rfl) (fun _ => ?_)
  rcases rules with _ | ⟨rl, _ | _⟩
  · exact SimE.pure' hmaj rfl
  case cons.nil =>
    have hrl : rl.Good P := hrules rl (List.mem_singleton_self rl)
    simp only [List.map_cons, List.map_nil, RecRule.mapKeys]
    rw [hE.find rl.ctor hrl.1]
    cases hcj : env.find? rl.ctor with
    | none => exact SimE.pure' hmaj rfl
    | some cj =>
      have hgj := hE.good rl.ctor cj hrl.1 hcj
      cases cj with
      | ctorInfo cvj cnP cnF =>
        simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_type,
          ConstantVal.mapKeys_levelParams, ← Expr.mapKeys_piResult, ← Expr.mapKeys_getAppFn]
        have hgT := Expr.Good.getAppFn (Expr.Good.piResult hgj.2)
        generalize cvj.type.piResult.getAppFn = gT at hgT ⊢
        cases gT with
        | const T _ =>
          simp only [Expr.mapKeys]
          rw [hE.find T hgT]
          cases hcT : env.find? T with
          | none => exact SimE.pure' hmaj rfl
          | some cT =>
            have hgcT := hE.good T cT hgT hcT
            cases cT with
            | indInfo cvT caps =>
              simp only [Option.map_some, ConstantInfo.mapKeys]
              refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
              · -- the K rescue
                refine SimE.bind (hr.inferIO d major hmaj) (fun tm htm => ?_)
                refine SimE.bind (hr.whnf d tm htm) (fun tmaj htmaj => ?_)
                rw [← Expr.mapKeys_getAppFn]
                have hgM := Expr.Good.getAppFn htmaj
                have hma := Expr.Good.getAppArgs htmaj
                generalize tmaj.getAppFn = gM at hgM ⊢
                cases gM with
                | const T' ust =>
                  simp only [Expr.mapKeys, Key.map_eq_map_iff hE.inj hgM hgT,
                    Expr.getAppArgs_mapKeys, List.length_map]
                  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                  have hfab : (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).Good P :=
                    Expr.Good.mkAppN hrl.1 (hma.take cnP)
                  have hF : Expr.mkAppN (.const (Key.map f rl.ctor) ust)
                      (List.take cnP (List.map (Expr.mapKeys f) tmaj.getAppArgs)) =
                      (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).mapKeys f := by
                    simp
                  simp only [hF]
                  generalize Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP) = fab at hfab ⊢
                  rw [Expr.wscopedB_mapKeys, Expr.looseBVarsBounded_mapKeys,
                    fvarLeaves_all_contains_ren hE.inj hfab hmaj]
                  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                  refine SimE.bind (iotaCerts_sim' hr d false
                    (Expr.Good.instantiateLevelParams hgj.2 _ _) (hma.take cnP) (by simp) (by simp))
                    (fun ok₁ _ => ?_)
                  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                  refine SimE.bind (hr.inferIO d fab hfab) (fun tf htf => ?_)
                  refine SimE.bind (hr.defeq d tmaj tf htmaj htf) (fun ok₂ _ => ?_)
                  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                  refine SimE.bind (proofIrrel_sim hE hr d hfab hmaj) (fun ok₃ _ => ?_)
                  exact SimE.ite Iff.rfl (fun _ => SimE.pure' hfab rfl) (fun _ => SimE.pure' hmaj rfl)
                | _ => exact SimE.pure' hmaj rfl
              · refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
                · -- the structure-η rescue
                  refine SimE.bind (hr.inferIO d major hmaj) (fun tm htm => ?_)
                  refine SimE.bind (hr.whnf d tm htm) (fun tmaj htmaj => ?_)
                  rw [← Expr.mapKeys_getAppFn]
                  have hgM := Expr.Good.getAppFn htmaj
                  have hma := Expr.Good.getAppArgs htmaj
                  generalize tmaj.getAppFn = gM at hgM ⊢
                  cases gM with
                  | const T' ust =>
                    simp only [Expr.mapKeys, Key.map_eq_map_iff hE.inj hgM hgT,
                      Expr.getAppArgs_mapKeys, List.length_map, IndCaps.mapKeys]
                    refine SimE.ite (by simp [capsNeverZero, IndCaps.mapKeys]) (fun _ => ?_)
                      (fun _ => SimE.pure' hmaj rfl)
                    have hargs := etaFabArgsE_ren hE hgT ust tmaj.getAppArgs major caps.etaFields
                    have hgargs : Expr.GoodList P
                        (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields) := by
                      simp only [etaFabArgsE, Expr.goodList_append]
                      exact ⟨hma, etaProjs_good hgT hma hmaj _⟩
                    have hfab : (Expr.mkAppN (.const rl.ctor ust)
                        (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)).Good P :=
                      Expr.Good.mkAppN hrl.1 hgargs
                    have hF : Expr.mkAppN (.const (Key.map f rl.ctor) ust)
                        ((etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields).map
                          (Expr.mapKeys f)) =
                        (Expr.mkAppN (.const rl.ctor ust)
                          (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)).mapKeys f := by
                      simp
                    rw [hargs]
                    simp only [hF]
                    generalize Expr.mkAppN (.const rl.ctor ust)
                      (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields) = fab at hfab ⊢
                    rw [Expr.wscopedB_mapKeys, Expr.looseBVarsBounded_mapKeys,
                      fvarLeaves_all_contains_ren hE.inj hfab hmaj]
                    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                    refine SimE.bind (iotaCerts_sim' hr d false
                      (Expr.Good.instantiateLevelParams hgj.2 _ _) hgargs (by simp) rfl)
                      (fun ok₁ _ => ?_)
                    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                    refine SimE.bind (structEtaCertWith_sim mode hE hr d hfab hmaj htmaj)
                      (fun ok₂ _ => ?_)
                    refine SimE.ite Iff.rfl (fun _ => SimE.pure' hfab rfl) (fun _ => ?_)
                    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                    refine SimE.bind (proofIrrel_sim hE hr d hfab hmaj) (fun ok₃ _ => ?_)
                    exact SimE.ite Iff.rfl (fun _ => SimE.pure' hfab rfl)
                      (fun _ => SimE.pure' hmaj rfl)
                  | _ => exact SimE.pure' hmaj rfl
                · refine SimE.ite (by simp) (fun hT => ?_) (fun _ => SimE.pure' hmaj rfl)
                  -- the `And` rescue
                  refine SimE.bind (hr.inferIO d major hmaj) (fun tm htm => ?_)
                  refine SimE.bind (hr.whnf d tm htm) (fun tmaj htmaj => ?_)
                  rw [← Expr.mapKeys_getAppFn]
                  have hgM := Expr.Good.getAppFn htmaj
                  have hma := Expr.Good.getAppArgs htmaj
                  generalize tmaj.getAppFn = gM at hgM ⊢
                  cases gM with
                  | const T' ust =>
                    simp only [Expr.mapKeys, Key.map_eq_map_iff hE.inj hgM hgT,
                      Expr.getAppArgs_mapKeys, List.length_map, andRescueSlots_ren hE hrl.1]
                    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                    have hgargs : Expr.GoodList P
                        (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major]) := by
                      simp only [Expr.goodList_append, Expr.goodList_cons, Expr.goodList_nil,
                        and_true]
                      exact ⟨hma, ⟨hgT, hmaj⟩, ⟨hgT, hmaj⟩⟩
                    have hfab : (Expr.mkAppN (.const rl.ctor ust)
                        (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])).Good P :=
                      Expr.Good.mkAppN hrl.1 hgargs
                    have hF : Expr.mkAppN (.const (Key.map f rl.ctor) ust)
                        (List.map (Expr.mapKeys f) tmaj.getAppArgs ++
                          [.proj (T.map f) 0 (major.mapKeys f), .proj (T.map f) 1 (major.mapKeys f)]) =
                        (Expr.mkAppN (.const rl.ctor ust)
                          (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])).mapKeys f := by
                      simp
                    simp only [hF]
                    generalize Expr.mkAppN (.const rl.ctor ust)
                      (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major]) = fab at hfab ⊢
                    rw [Expr.wscopedB_mapKeys, Expr.looseBVarsBounded_mapKeys,
                      fvarLeaves_all_contains_ren hE.inj hfab hmaj]
                    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                    refine SimE.bind (iotaCerts_sim' hr d false
                      (Expr.Good.instantiateLevelParams hgj.2 _ _) hgargs (by simp) (by simp))
                      (fun ok₁ _ => ?_)
                    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                    refine SimE.bind (hr.inferIO d fab hfab) (fun tf htf => ?_)
                    refine SimE.bind (hr.defeq d tmaj tf htmaj htf) (fun ok₂ _ => ?_)
                    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hmaj rfl)
                    refine SimE.bind (proofIrrel_sim hE hr d hfab hmaj) (fun ok₃ _ => ?_)
                    exact SimE.ite Iff.rfl (fun _ => SimE.pure' hfab rfl)
                      (fun _ => SimE.pure' hmaj rfl)
                  | _ => exact SimE.pure' hmaj rfl
            | _ => exact SimE.pure' hmaj rfl
        | _ => exact SimE.pure' hmaj rfl
      | _ => exact SimE.pure' hmaj rfl
  · exact SimE.pure' hmaj rfl

/-! ## Literal majors and the major's preparation -/

theorem strLitToConstructor_good (s : String) : (strLitToConstructor s : Expr md).Good P := by
  unfold strLitToConstructor
  refine ⟨trivial, ?_⟩
  generalize s.toList = cs
  induction cs with
  | nil => exact ⟨trivial, trivial⟩
  | cons c cs ih => exact ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, ih⟩

theorem natLitToConstructor_good (n : Nat) : (natLitToConstructor n : Expr md).Good P := by
  cases n <;> simp [natLitToConstructor]

theorem litToCtorIfNat_good {e : Expr md} (he : e.Good P) : (litToCtorIfNat env e).Good P := by
  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | ⟨n | _⟩ | _ <;> simp only [litToCtorIfNat] <;>
    first | exact he | (split <;> first | exact natLitToConstructor_good n | trivial)

theorem litMajorToCtor_of_ne {e : Expr md} (h : ∀ s, e ≠ .lit (.strVal s)) :
    litMajorToCtor r env d e = pure (litToCtorIfNat env e) := by
  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | s⟩ | _ <;> first | rfl | exact absurd rfl (h _)

theorem projLitToCtor_of_ne {e : Expr md} (h : ∀ s, e ≠ .lit (.strVal s)) :
    projLitToCtor r env d e = pure e := by
  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | s⟩ | _ <;> first | rfl | exact absurd rfl (h _)

theorem litMajorToCtor_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat)
    {e : Expr md} (he : e.Good P) :
    SimX P f (litMajorToCtor r env d e) (litMajorToCtor r' env' d (e.mapKeys f)) := by
  by_cases hs : ∃ s, e = .lit (.strVal s)
  · obtain ⟨s, rfl⟩ := hs
    simp only [Expr.mapKeys, litMajorToCtor, strLitSupported_ren hE]
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' trivial rfl)
    exact SimE.congr (by simp) (hr.whnf d (strLitToConstructor s) (strLitToConstructor_good s))
  · have h₁ : ∀ s, e ≠ .lit (.strVal s) := fun s h => hs ⟨s, h⟩
    have h₂ : ∀ s, e.mapKeys f ≠ .lit (.strVal s) :=
      fun s h => h₁ s (Expr.mapKeys_eq_lit_iff.mp h)
    rw [litMajorToCtor_of_ne h₁, litMajorToCtor_of_ne h₂]
    exact SimE.pure' (litToCtorIfNat_good he) (litToCtorIfNat_ren hE e)

theorem projLitToCtor_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat)
    {e : Expr md} (he : e.Good P) :
    SimX P f (projLitToCtor r env d e) (projLitToCtor r' env' d (e.mapKeys f)) := by
  by_cases hs : ∃ s, e = .lit (.strVal s)
  · obtain ⟨s, rfl⟩ := hs
    simp only [Expr.mapKeys, projLitToCtor, strLitSupported_ren hE]
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' trivial rfl)
    exact SimE.congr (by simp) (hr.whnf d (strLitToConstructor s) (strLitToConstructor_good s))
  · have h₁ : ∀ s, e ≠ .lit (.strVal s) := fun s h => hs ⟨s, h⟩
    have h₂ : ∀ s, e.mapKeys f ≠ .lit (.strVal s) :=
      fun s h => h₁ s (Expr.mapKeys_eq_lit_iff.mp h)
    rw [projLitToCtor_of_ne h₁, projLitToCtor_of_ne h₂]
    exact SimE.pure' he rfl

theorem prepareMajor_sim (mode : CheckMode) (hE : EnvRel P f env env') (hr : CoreSim P f r r')
    (d : Nat) (recName : Key md) {rules : List (RecRule md)} (hrules : ∀ rl ∈ rules, rl.Good P)
    {major : Expr md} (hmaj : major.Good P) :
    SimX P f (prepareMajor mode r env d recName rules major)
      (prepareMajor mode r' env' d (recName.map f) (rules.map (RecRule.mapKeys f))
        (major.mapKeys f)) := by
  unfold prepareMajor
  rw [recRuleK_map]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
  · refine SimE.bind (majorToCtor_sim mode hE hr d recName hrules hmaj) (fun mk hmk => ?_)
    refine SimE.bind (hr.whnf d mk hmk) (fun m₀ hm₀ => ?_)
    exact litMajorToCtor_sim hE hr d hm₀
  · refine SimE.bind (hr.whnf d major hmaj) (fun m₀ hm₀ => ?_)
    refine SimE.bind (litMajorToCtor_sim hE hr d hm₀) (fun m₁ hm₁ => ?_)
    exact majorToCtor_sim mode hE hr d recName hrules hm₁

theorem Expr.Good.instSpine {as : List (Expr md)} (has : Expr.GoodList P as) {t : Nat}
    {e : Expr md} (he : e.Good P) : (Expr.instSpine as t e).Good P := by
  induction as generalizing t e with
  | nil => exact he
  | cons a as ih =>
    simp only [Expr.goodList_cons] at has
    exact ih has.2 (Expr.Good.instantiate1 he has.1 t)

/-! ## The ι step -/

/-- The rule lookup of the ι step, renamed. -/
theorem rules_find?_ren (hf : InjOn f P) {rules : List (RecRule md)}
    (hrules : ∀ rl ∈ rules, rl.Good P) {cj : Key md} (hcj : cj.Good P) :
    (rules.map (RecRule.mapKeys f)).find? (fun r' => r'.ctor == cj.map f) =
      (rules.find? (fun r' => r'.ctor == cj)).map (RecRule.mapKeys f) := by
  induction rules with
  | nil => rfl
  | cons rl rules ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hrules
    simp only [List.map_cons, List.find?_cons, RecRule.mapKeys]
    rw [Key.map_beq hf hrules.1.1 hcj]
    cases (rl.ctor == cj) with
    | true => rfl
    | false => exact ih hrules.2

@[simp] theorem RecRule.mapKeys_fire_eq_inert (rl : RecRule md) :
    (rl.mapKeys f).fire = .inert ↔ rl.fire = .inert := by
  simp only [RecRule.mapKeys]
  cases rl.fire <;> simp

@[simp] theorem RecRule.mapKeys_compareParams (rl : RecRule md) :
    (rl.mapKeys f).compareParams = rl.compareParams := by
  simp only [RecRule.compareParams, RecRule.mapKeys]
  cases rl.fire <;> rfl

@[simp] theorem RecRule.mapKeys_ctorParams (rl : RecRule md) :
    (rl.mapKeys f).ctorParams = rl.ctorParams := rfl
@[simp] theorem RecRule.mapKeys_nfields (rl : RecRule md) :
    (rl.mapKeys f).nfields = rl.nfields := rfl
@[simp] theorem RecRule.mapKeys_rhs (rl : RecRule md) :
    (rl.mapKeys f).rhs = rl.rhs.mapKeys f := rfl
@[simp] theorem RecRule.mapKeys_ctor (rl : RecRule md) :
    (rl.mapKeys f).ctor = rl.ctor.map f := rfl

theorem List.getD_map_bvar (l : List (Expr md)) (n : Nat) :
    (l.map (Expr.mapKeys f)).getD n (.bvar 0) = (l.getD n (.bvar 0)).mapKeys f := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

theorem Expr.GoodList.getD {l : List (Expr md)} (h : Expr.GoodList P l) (n : Nat) :
    (l.getD n (.bvar 0)).Good P := by
  simp only [List.getD_eq_getElem?_getD]
  cases hn : l[n]? with
  | none => trivial
  | some x => exact h x (List.mem_of_getElem? hn)

theorem iotaRec_sim (mode : CheckMode) (hE : EnvRel P f env env') (hr : CoreSim P f r r')
    (d : Nat) {e : Expr md} (he : e.Good P) :
    SimO P f (iotaRec mode r env d e) (iotaRec mode r' env' d (e.mapKeys f)) := by
  unfold iotaRec
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
  have hg := Expr.Good.getAppFn he
  have hargs := Expr.Good.getAppArgs he
  generalize e.getAppFn = g at hg ⊢
  generalize e.getAppArgs = args at hargs ⊢
  cases g with
  | const c us =>
    simp only [Expr.mapKeys]
    rw [hE.find c hg]
    cases hcc : env.find? c with
    | none => exact SimE.pure' (fun _ h => nomatch h) rfl
    | some cc =>
      have hgc := hE.good c cc hg hcc
      cases cc with
      | recInfo cv mI rP rules =>
        simp only [Option.map_some, ConstantInfo.mapKeys, List.length_map,
          ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
        refine SimE.bind (SimE.congr (by rw [List.getD_map_bvar])
          (prepareMajor_sim mode hE hr d c hgc.2 (hargs.getD mI))) (fun major hmaj => ?_)
        rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
        have hgm := Expr.Good.getAppFn hmaj
        have hmargs := Expr.Good.getAppArgs hmaj
        generalize major.getAppFn = gm at hgm ⊢
        cases gm with
        | const cj usj =>
          simp only [Expr.mapKeys]
          rw [hE.find cj hgm]
          cases hcj : env.find? cj with
          | none => exact SimE.pure' (fun _ h => nomatch h) rfl
          | some ccj =>
            have hgcj := hE.good cj ccj hgm hcj
            cases ccj with
            | ctorInfo cvj nP nF =>
              simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams,
                ConstantVal.mapKeys_type]
              rw [rules_find?_ren hE.inj hgc.2 hgm]
              cases hrl : rules.find? (fun r' => r'.ctor == cj) with
              | none => exact SimE.pure' (fun _ h => nomatch h) rfl
              | some rl =>
                have hgrl : rl.Good P := hgc.2 rl (List.mem_of_find?_eq_some hrl)
                simp only [Option.map_some, List.length_map, RecRule.mapKeys_ctorParams,
                  RecRule.mapKeys_nfields, RecRule.mapKeys_fire_eq_inert,
                  RecRule.mapKeys_compareParams]
                refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
                refine SimE.ite Iff.rfl (fun _ => SimE.throw') (fun _ => ?_)
                rw [recFireComparands_mapKeys]
                refine SimE.bind (SimE.liftFueled _ _) (fun okL _ => ?_)
                refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
                refine SimE.bind (?_ : SimV _ _) (fun ok₁ _ => ?_)
                · refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT true)
                  refine defEqList_sim' hr d (hmargs.take _) ?_ (by simp) rfl
                  unfold recFireComparands
                  cases hfire : rl.fire with
                  | nested lvls pins =>
                    have hp : Expr.GoodList P pins := by
                      have := hgrl.2.1; rw [hfire] at this; exact this
                    intro x hx
                    simp only [List.mem_map] at hx
                    obtain ⟨p, hp', rfl⟩ := hx
                    exact Expr.Good.instSpine (hargs.take rP) (Expr.Good.instantiateLevelParams (hp p hp') _ _)
                  | inert => exact hargs.take _
                  | plain => exact hargs.take _
                refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
                refine SimE.bind (iotaCerts_sim' hr d mode.betaGate
                  (Expr.Good.instantiateLevelParams hgc.1.2 _ _)
                  (by simp only [Expr.goodList_append, Expr.goodList_cons, Expr.goodList_nil,
                    and_true]; exact ⟨hargs.take _, hmaj⟩) (by simp) (by simp)) (fun ok₂ _ => ?_)
                refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
                refine SimE.bind (iotaCerts_sim' hr d mode.betaGate
                  (Expr.Good.instantiateLevelParams hgcj.2 _ _) hmargs (by simp) rfl)
                  (fun ok₃ _ => ?_)
                refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
                refine SimE.bind (SimE.congr (by simp)
                  (iotaIndexOk_sim (env := env) (env' := env') hr d mI rP rl.ctorParams
                    (Expr.Good.instantiateLevelParams hgcj.2 _ _) hmargs
                    ((hargs.take mI).drop rP))) (fun ok₄ _ => ?_)
                refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
                refine SimE.pure' ?_ (by simp)
                intro x hx
                simp only [Option.mem_def, Option.some.injEq] at hx
                subst hx
                exact Expr.Good.mkAppN (Expr.Good.instantiateLevelParams hgrl.2.2 _ _)
                  (by simp only [Expr.goodList_append]; exact ⟨hargs.take _, hmargs.drop _⟩)
            | _ => exact SimE.pure' (fun _ h => nomatch h) rfl
        | _ => exact SimE.pure' (fun _ h => nomatch h) rfl
      | _ => exact SimE.pure' (fun _ h => nomatch h) rfl
  | _ => exact SimE.pure' (fun _ h => nomatch h) rfl

end Ix.Kernel
