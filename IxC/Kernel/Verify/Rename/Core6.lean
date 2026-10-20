module

public import IxC.Kernel.Verify.Rename.Core5

@[expose] public section

/-!
# The renaming walk through the core, part 6: definitional equality

`boolTrueShortcut`, the same-head short-circuit `defeqSpine`, one step of
the lazy-delta loop `defeqStep` (with its continuation abstracted, as the
body itself abstracts it), the loop `defeqLoop` and `defeqBody`, at renamed
arguments over related core records and environments. Here the
injectivity of the renaming on good keys is what keeps every equality test
answering alike.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {env : Env md} {env' : Env md'}
variable {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}

theorem boolTrueShortcut_sim (hr : CoreSim P f r r') (d : Nat) {a : Expr md} (ha : a.Good P) :
    SimV (boolTrueShortcut r d a) (boolTrueShortcut r' d (a.mapKeys f)) := by
  unfold boolTrueShortcut
  refine SimE.bind (hr.whnf d a ha) (fun w _ => ?_)
  exact SimE.pure' trivial (by simp)

theorem defeqSpine_sim (hE : EnvRelG P f L env env') (hr : CoreSim P f r r') (d : Nat)
    {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (defeqSpine r env d a b) (defeqSpine r' env' d (a.mapKeys f) (b.mapKeys f)) := by
  unfold defeqSpine
  rw [← Expr.mapKeys_getAppFn, ← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys,
    Expr.getAppArgs_mapKeys]
  have hga := Expr.Good.getAppFn ha
  have hgb := Expr.Good.getAppFn hb
  have haa := Expr.Good.getAppArgs ha
  have hba := Expr.Good.getAppArgs hb
  generalize a.getAppFn = ga at hga ⊢
  generalize b.getAppFn = gb at hgb ⊢
  cases ga with
  | const n us =>
    cases gb with
    | const n' us' =>
      simp only [Expr.mapKeys, List.length_map, Key.map_eq_map_iff hE.inj hga hgb]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
      cases Level.isEquivList us us' with
      | none => exact SimV.pureT false
      | some v =>
        cases v with
        | false => exact SimV.pureT false
        | true => exact defEqList_sim hr d _ _ haa hba
    | _ => exact SimV.pureT false
  | _ => exact SimV.pureT false

theorem defeqStep_sim (mode : CheckMode) (hE : EnvRelG P f L env env') (hr : CoreSim P f r r')
    (d : Nat) {k : Bool → Expr md → Expr md → CheckM md Bool}
    {k' : Bool → Expr md' → Expr md' → CheckM md' Bool}
    (hk : ∀ pi (a b : Expr md), a.Good P → b.Good P → SimV (k pi a b) (k' pi (a.mapKeys f) (b.mapKeys f)))
    (pi : Bool) {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (defeqStep mode r env d k pi a b)
      (defeqStep mode r' env' d k' pi (a.mapKeys f) (b.mapKeys f)) := by
  unfold defeqStep
  rw [Expr.mapKeys_beq hE.inj ha hb]
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  simp only [isBoolTrue_mapKeys, Expr.hasFvar_mapKeys]
  refine SimE.bind (?_ : SimV _ _) (fun ok₀ _ => ?_)
  · exact SimE.ite Iff.rfl (fun _ => boolTrueShortcut_sim hr d ha) (fun _ => SimV.pureT false)
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  refine SimE.bind (hr.whnfCore d a ha) (fun a' ha' => ?_)
  refine SimE.bind (hr.whnfCore d b hb) (fun b' hb' => ?_)
  rw [Expr.mapKeys_beq hE.inj ha' hb']
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  simp only [quickPair_mapKeys, Expr.hasFvar_mapKeys]
  refine SimE.bind (?_ : SimV _ _) (fun ok₁ _ => ?_)
  · exact SimE.ite Iff.rfl (fun _ => propIrrel_sim hE hr d ha' hb') (fun _ => SimV.pureT false)
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  refine SimE.bind (?_ : SimO P f _ _) (fun o₁ ho₁ => ?_)
  · exact SimE.ite Iff.rfl (fun _ => reduceNat_sim hE hr d ha')
      (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
  cases o₁ with
  | some a₂ => exact hk true a₂ b' (ho₁ a₂ rfl) hb'
  | none =>
  simp only [Option.map_none]
  refine SimE.bind (?_ : SimO P f _ _) (fun o₂ ho₂ => ?_)
  · exact SimE.ite Iff.rfl (fun _ => reduceNat_sim hE hr d hb')
      (fun _ => SimE.pure' (fun _ h => nomatch h) rfl)
  cases o₂ with
  | some b₂ => exact hk true a' b₂ ha' (ho₂ b₂ rfl)
  | none =>
  simp only [Option.map_none, unfoldableHead_ren hE ha', unfoldableHead_ren hE hb',
    headHint_ren hE ha', headHint_ren hE hb', sameConstHeads_ren hE.inj ha' hb',
    unfoldDefinition_ren hE ha', unfoldDefinition_ren hE hb']
  cases hu₁ : unfoldableHead env a' <;> cases hu₂ : unfoldableHead env b' <;> simp only
  · -- neither head unfolds: the structural comparison
    rcases a' with _ | _ | _ | ⟨ca, usa⟩ | ⟨fa, xa⟩ | _ | _ | _ | ⟨n | s⟩ | _ <;>
      rcases b' with _ | _ | _ | ⟨cb, usb⟩ | ⟨fb, xb⟩ | _ | _ | _ | ⟨n' | s'⟩ | _ <;>
      simp only [Expr.mapKeys] <;>
      first
        | exact stuckIrrel_sim mode hE hr d ha' hb'
        | exact SimE.liftFueled _ _
        | exact SimV.pureT _
        | -- one-sided λ on the left: η, else the stuck fallbacks
          (refine SimE.bind (etaCert_sim mode hr d _ ha'.1 ha'.2 hb') (fun _ _ => ?_)
           exact SimE.ite Iff.rfl (fun _ => SimV.pureT true)
             (fun _ => stuckIrrel_sim mode hE hr d ha' hb'))
        | -- one-sided λ on the right
          (refine SimE.bind (etaCert_sim mode hr d _ hb'.1 hb'.2 ha') (fun _ _ => ?_)
           exact SimE.ite Iff.rfl (fun _ => SimV.pureT true)
             (fun _ => stuckIrrel_sim mode hE hr d ha' hb'))
        | -- two free variables
          exact SimE.ite Iff.rfl (fun _ => SimV.pureT true)
            (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
        | -- a literal against `Nat.zero`
          exact SimE.ite (by simp) (fun _ => SimV.pureT _)
            (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
        | -- two projections
          (rw [Key.map_beq hE.inj ha'.1 hb'.1]
           refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
           refine SimE.bind (hr.defeq d _ _ ha'.2 hb'.2) (fun _ _ => ?_)
           exact SimE.ite Iff.rfl (fun _ => SimV.pureT true)
             (fun _ => stuckIrrel_sim mode hE hr d ha' hb'))
        | -- two binders
          (refine SimE.bind (hr.defeq d _ _ ha'.1 hb'.1) (fun _ _ => ?_)
           refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
           refine SimE.bind (SimE.congr (by simp)
             (hr.defeq (d + 1) _ _ (Expr.Good.instantiate1 (v := .fvar d _) ha'.2 hb'.1 0)
               (Expr.Good.instantiate1 (v := .fvar d _) hb'.2 hb'.1 0))) (fun _ _ => ?_)
           refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
           refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
           exact SimE.ite Iff.rfl (fun _ => SimE.throw') (fun _ => SimV.pureT true))
        | -- two applications: spine congruence
          (simp only [Expr.app_mapKeys_fold, Expr.getAppArgs_mapKeys, List.length_map,
             ← Expr.mapKeys_getAppFn]
           refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
           refine SimE.bind (hr.defeq d _ _ (Expr.Good.getAppFn ha') (Expr.Good.getAppFn hb'))
             (fun _ _ => ?_)
           refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
           refine SimE.bind (defEqList_sim hr d _ _ (Expr.Good.getAppArgs ha')
             (Expr.Good.getAppArgs hb')) (fun _ _ => ?_)
           exact SimE.ite Iff.rfl (fun _ => SimV.pureT true)
             (fun _ => stuckIrrel_sim mode hE hr d ha' hb'))
        | skip
    case lit.natVal.app =>
      rcases n with _ | n <;> rcases fb with _ | _ | _ | ⟨c, _ | _⟩ | _ | _ | _ | _ | _ | _ <;>
        simp only [Expr.mapKeys] <;>
        first
          | exact stuckIrrel_sim mode hE hr d ha' hb'
          | exact SimE.ite (by simp) (fun _ => hr.defeq d _ _ trivial hb'.2)
              (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
    case app.lit.natVal =>
      rcases n' with _ | n' <;> rcases fa with _ | _ | _ | ⟨c, _ | _⟩ | _ | _ | _ | _ | _ | _ <;>
        simp only [Expr.mapKeys] <;>
        first
          | exact stuckIrrel_sim mode hE hr d ha' hb'
          | exact SimE.ite (by simp) (fun _ => hr.defeq d _ _ ha'.2 trivial)
              (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
    case lit.strVal.app =>
      rcases fb with _ | _ | _ | ⟨c, us⟩ | _ | _ | _ | _ | _ | _ <;>
        simp only [Expr.mapKeys] <;>
        first
          | exact stuckIrrel_sim mode hE hr d ha' hb'
          | exact SimE.ite (by simp [strLitSupported_ren hE ha'])
              (fun _ => SimE.congr (by simp) (hr.defeq d _ _ (strLitToConstructor_good hE.pre ha' s) hb'))
              (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
    case app.lit.strVal =>
      rcases fa with _ | _ | _ | ⟨c, us⟩ | _ | _ | _ | _ | _ | _ <;>
        simp only [Expr.mapKeys] <;>
        first
          | exact stuckIrrel_sim mode hE hr d ha' hb'
          | exact SimE.ite (by simp [strLitSupported_ren hE hb'])
              (fun _ => SimE.congr (by simp) (hr.defeq d _ _ ha' (strLitToConstructor_good hE.pre hb' s')))
              (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
    case const.const =>
      have hca : ca.Good P := ha'
      have hcb : cb.Good P := hb'
      refine SimE.ite (Key.map_eq_map_iff hE.inj hca hcb).symm (fun _ => ?_)
        (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
      refine SimE.bind (SimE.liftFueled _ _) (fun _ _ => ?_)
      exact SimE.ite Iff.rfl (fun _ => SimV.pureT true)
        (fun _ => stuckIrrel_sim mode hE hr d ha' hb')
    all_goals done
  · -- only the right head unfolds
    cases hd : unfoldDefinition env b' with
    | none => exact SimV.pureT false
    | some b₂ => exact hk false a' b₂ ha' (unfoldDefinition_good hE hb' hd)
  · -- only the left head unfolds
    cases hd : unfoldDefinition env a' with
    | none => exact SimV.pureT false
    | some a₂ => exact hk false a₂ b' (unfoldDefinition_good hE ha' hd) hb'
  · -- both heads unfold: lazy delta by the hints
    have hboth : SimV
        (match unfoldDefinition env a', unfoldDefinition env b' with
          | some a₂, some b₂ => k false a₂ b₂
          | _, _ => pure false)
        (match (unfoldDefinition env a').map (Expr.mapKeys f),
            (unfoldDefinition env b').map (Expr.mapKeys f) with
          | some a₂, some b₂ => k' false a₂ b₂
          | _, _ => pure false) := by
      cases hd₁ : unfoldDefinition env a' <;> cases hd₂ : unfoldDefinition env b' <;>
        try exact SimV.pureT false
      exact hk false _ _ (unfoldDefinition_good hE ha' hd₁) (unfoldDefinition_good hE hb' hd₂)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · cases hd : unfoldDefinition env a' with
      | none => exact SimV.pureT false
      | some a₂ => exact hk false a₂ b' (unfoldDefinition_good hE ha' hd) hb'
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · cases hd : unfoldDefinition env b' with
      | none => exact SimV.pureT false
      | some b₂ => exact hk false a' b₂ ha' (unfoldDefinition_good hE hb' hd)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => hboth)
    refine SimE.bind (defeqSpine_sim hE hr d ha' hb') (fun ok _ => ?_)
    exact SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => hboth)

theorem defeqLoop_sim (mode : CheckMode) (hE : EnvRelG P f L env env') (hr : CoreSim P f r r')
    (d : Nat) :
    ∀ (n : Nat) (pi : Bool) {a b : Expr md}, a.Good P → b.Good P →
      SimV (defeqLoop mode r env d n pi a b)
        (defeqLoop mode r' env' d n pi (a.mapKeys f) (b.mapKeys f))
  | 0, _, _, _, _, _ => SimE.throw'
  | n + 1, pi, _, _, ha, hb => by
    simp only [defeqLoop]
    exact defeqStep_sim mode hE hr d
      (fun pi _ _ ha hb => defeqLoop_sim mode hE hr d n pi ha hb) pi ha hb

theorem defeqBody_sim (mode : CheckMode) (hE : EnvRelG P f L env env') (hr : CoreSim P f r r')
    (d : Nat) {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (defeqBody mode r env d a b) (defeqBody mode r' env' d (a.mapKeys f) (b.mapKeys f)) :=
  defeqLoop_sim mode hE hr d _ true ha hb

end Ix.Kernel
