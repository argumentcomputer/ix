module

public import IxC.Kernel.Verify.Rename.Modeled4

@[expose] public section

/-!
# The renaming walk through the modeled route: the projection functions (step 7.3, chunk (iii))

The public↔model renamings of a structure's projection types (`projBack`,
`projFwd`) commute with an input renaming on good keys; the projection
function's lookups, type, iota theorem and install (`checkProjLookups`,
`checkProjTy`, `checkProjIota`, `checkProjFn`, `installProjFnStep`) at a renamed
structure over related environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-! ## The public↔model renamings -/

theorem find?_range_beq_map (hf : InjOn f P) {k : Key md} (hk : k.Good P) (g : Nat → Key md)
    (hg : ∀ j, (g j).Good P) (g' : Nat → Key md') (hg' : ∀ j, g' j = (g j).map f) (n : Nat) :
    (List.range n).find? (fun j => k.map f == g' j) = (List.range n).find? (fun j => k == g j) := by
  congr 1
  funext j
  rw [hg' j, Key.map_beq hf hk (hg j)]

theorem projBack_map (hf : InjOn f P) {T ctor : Key md} (hT : T.Good P) (hc : ctor.Good P)
    (nF : Nat) : ∀ k : Key md, k.Good P →
      (projBack T ctor nF k).map f = projBack (T.map f) (ctor.map f) nF (k.map f) := by
  intro k hk
  unfold projBack
  have h1 : k.map f = auxKey (T.map f) .model ↔ k = auxKey T .model :=
    Key.map_eq_map_iff hf hk (show (auxKey T .model).Good P from hT)
  have h2 : k.map f = auxKey (ctor.map f) .model ↔ k = auxKey ctor .model :=
    Key.map_eq_map_iff hf hk (show (auxKey ctor .model).Good P from hc)
  by_cases hA : k = auxKey T .model
  · rw [ite_eq_left hA, ite_eq_left (h1.mpr hA)]
  · rw [ite_eq_right hA, ite_eq_right (fun h => hA (h1.mp h))]
    by_cases hB : k = auxKey ctor .model
    · rw [ite_eq_left hB, ite_eq_left (h2.mpr hB)]
    · rw [ite_eq_right hB, ite_eq_right (fun h => hB (h2.mp h))]
      rw [find?_range_beq_map hf hk (projModelName T) (fun _ => hT) (projModelName (T.map f))
        (fun _ => rfl)]
      cases (List.range nF).find? (fun j => k == projModelName T j) <;> rfl

theorem projBack_good {T ctor : Key md} (hT : T.Good P) (hc : ctor.Good P) (nF : Nat) :
    ∀ k : Key md, k.Good P → (projBack T ctor nF k).Good P := by
  intro k hk
  unfold projBack
  split
  · exact hT
  · split
    · exact hc
    · split
      · exact hT
      · exact hk

theorem projFwd_map (hf : InjOn f P) {T ctor : Key md} (hT : T.Good P) (hc : ctor.Good P)
    (nF : Nat) : ∀ k : Key md, k.Good P →
      (projFwd T ctor nF k).map f = projFwd (T.map f) (ctor.map f) nF (k.map f) := by
  intro k hk
  unfold projFwd
  have h1 : k.map f = T.map f ↔ k = T := Key.map_eq_map_iff hf hk hT
  have h2 : k.map f = ctor.map f ↔ k = ctor := Key.map_eq_map_iff hf hk hc
  by_cases hA : k = T
  · rw [ite_eq_left hA, ite_eq_left (h1.mpr hA)]
    rfl
  · rw [ite_eq_right hA, ite_eq_right (fun h => hA (h1.mp h))]
    by_cases hB : k = ctor
    · rw [ite_eq_left hB, ite_eq_left (h2.mpr hB)]
      rfl
    · rw [ite_eq_right hB, ite_eq_right (fun h => hB (h2.mp h))]
      rw [find?_range_beq_map hf hk (projFnName T) (fun _ => hT) (projFnName (T.map f))
        (fun _ => rfl)]
      cases (List.range nF).find? (fun j => k == projFnName T j) <;> rfl

theorem projFwd_good {T ctor : Key md} (hT : T.Good P) (hc : ctor.Good P) (nF : Nat) :
    ∀ k : Key md, k.Good P → (projFwd T ctor nF k).Good P := by
  intro k hk
  unfold projFwd
  split
  · exact hT
  · split
    · exact hc
    · split
      · exact hT
      · exact hk

/-! ## The projection function's checks -/

theorem checkProjLookups_sim {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {T ctorName : Key md} (hT : T.Good P) (hc : ctorName.Good P) (lps : List LevelParam)
    (nP nF i : Nat) :
    SimE (fun r : ConstantVal md × ConstantVal md => r.1.Good P ∧ r.2.Good P)
      (fun r => (r.1.mapKeys f, r.2.mapKeys f))
      (checkProjLookups (m := CheckM md) env T ctorName lps nP nF i)
      (checkProjLookups (m := CheckM md') env' (T.map f) (ctorName.map f) lps nP nF i) := by
  unfold checkProjLookups
  rw [hE.find ctorName hc]
  cases h₁ : env.find? ctorName with
  | none => exact SimE.throw'
  | some c₁ =>
    have hc₁ := hE.good ctorName c₁ hc h₁
    cases c₁ with
    | ctorInfo cvj cnP cnF =>
      simp only [Option.map_some, ConstantInfo.mapKeys]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      have hk : (projModelName T i).Good P := hT
      rw [show projModelName (T.map f) i = (projModelName T i).map f from rfl, hE.find _ hk]
      cases h₂ : env.find? (projModelName T i) with
      | none => exact SimE.throw'
      | some c₂ =>
        have hc₂ := hE.good _ c₂ hk h₂
        cases c₂ with
        | defnInfo mcv mval hint =>
          simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams]
          refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
          have hfn : (projFnName T i).Good P := hT
          have hnone : (env'.find? (projFnName (T.map f) i)).isNone =
              (env.find? (projFnName T i)).isNone := by
            rw [show projFnName (T.map f) i = (projFnName T i).map f from rfl,
              ← Option.not_isSome, ← Option.not_isSome, hE.find_isSome hfn]
          rw [hnone]
          refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
          rw [hE.find_isSome hT]
          refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
          have heq := find_eq_pin_ren hE (k := eqName) (hE.pre .eq (by decide)) (pin := eqA)
            (ConstantInfo.good_of_pinIn hE.pre eqA_pinIn)
          simp only [eqA_mapKeys] at heq
          refine SimE.ite (decide_eq_decide.mp heq.symm) (fun _ => ?_) (fun _ => SimE.throw_bind)
          exact SimE.pure' ⟨hc₁, hc₂.1⟩ rfl
        | _ => exact SimE.throw'
    | _ => exact SimE.throw'

theorem checkProjTy_sim {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {T ctorName : Key md} (hT : T.Good P) (hc : ctorName.Good P) (lps : List LevelParam)
    {mty : Expr md} (hm : mty.Good P) (nP nF : Nat) :
    SimX P f (checkProjTy (m := CheckM md) env T ctorName lps mty nP nF)
      (checkProjTy (m := CheckM md') env' (T.map f) (ctorName.map f) lps (mty.mapKeys f) nP nF) := by
  have hf := hE.inj
  unfold checkProjTy
  have hpb := projBack_map hf hT hc nF
  have hpbg := projBack_good hT hc nF
  have hpf := projFwd_map hf hT hc nF
  have hpfg := projFwd_good hT hc nF
  have hpty : (mty.renameConsts (projBack T ctorName nF)).Good P :=
    Expr.Good.renameConsts hpbg hm
  simp only [← mapKeys_renameConsts_good hpb hm, ← mapKeys_renameConsts_good hpf hpty]
  rw [Expr.mapKeys_beq hf (Expr.Good.renameConsts hpfg hpty) hm]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [constsResolve_ren hE hpty]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  simp only [Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys,
    Expr.allLevelParamsDefined_mapKeys, Expr.stripPis_mapKeys, Option.isSome_map]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => SimE.pure' hpty rfl) (fun _ => SimE.throw_bind)


theorem bvarList_map (n : Nat) (g : Nat → Nat) :
    ((List.range n).map fun k => (Expr.bvar (g k) : Expr md)).map (Expr.mapKeys f) =
      (List.range n).map fun k => Expr.bvar (g k) := by
  simp [List.map_map, Function.comp_def, Expr.mapKeys]

theorem bvarList_good (n : Nat) (g : Nat → Nat) :
    Expr.GoodList P ((List.range n).map fun k => (Expr.bvar (g k) : Expr md)) := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  trivial

theorem projIotaLhs_map (T ctorName : Key md) (lps lvls : List LevelParam) (nP nF i : Nat) :
    (Expr.mkAppN (.const (projModelName (T.map f) i) (lps.map .param))
      (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
        [Expr.mkAppN (.const (auxKey (ctorName.map f) .model) (lvls.map .param))
          (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
            (List.range nF).map fun k => Expr.bvar (nF - 1 - k))]) : Expr md') =
    (Expr.mkAppN (.const (projModelName T i) (lps.map .param))
      (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
        [Expr.mkAppN (.const (auxKey ctorName .model) (lvls.map .param))
          (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
            (List.range nF).map fun k => Expr.bvar (nF - 1 - k))]) : Expr md).mapKeys f := by
  simp [Expr.mapKeys_mkAppN, List.map_append, List.map_map, Function.comp_def, Expr.mapKeys]
  rfl

theorem projIotaLhs_good {T ctorName : Key md} (hT : T.Good P) (hc : ctorName.Good P)
    (lps lvls : List LevelParam) (nP nF i : Nat) :
    (Expr.mkAppN (.const (projModelName T i) (lps.map .param))
      (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
        [Expr.mkAppN (.const (auxKey ctorName .model) (lvls.map .param))
          (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
            (List.range nF).map fun k => Expr.bvar (nF - 1 - k))]) : Expr md).Good P := by
  refine Expr.Good.mkAppN (show Expr.Good P (Expr.const (projModelName T i) _) from hT) ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact bvarList_good nP _ x hx
  · simp only [List.mem_singleton] at hx
    subst hx
    refine Expr.Good.mkAppN (show Expr.Good P (Expr.const (auxKey ctorName .model) _) from hc) ?_
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact bvarList_good nP _ y hy
    · exact bvarList_good nF _ y hy

/-- **The projection iota theorem's check at a renamed structure.** -/
theorem checkProjIota_sim (mode : CheckMode) (hops : OpsSim P f L ops ops')
    {env₁ envS : Env md} {env₁' envS' : Env md'} (hE₁ : EnvRelG P f L env₁ env₁')
    (hES : EnvRelG P f L envS envS') {T ctorName : Key md} (hT : T.Good P) (hc : ctorName.Good P)
    (lps : List LevelParam) {cvj : ConstantVal md} (hcvj : cvj.Good P) (nP nF i : Nat) :
    SimV (checkProjIota mode ops env₁ envS T ctorName lps cvj nP nF i)
      (checkProjIota mode ops' env₁' envS' (T.map f) (ctorName.map f) lps (cvj.mapKeys f)
        nP nF i) := by
  have hf := hES.inj
  unfold checkProjIota
  have hk : (auxKey (projModelName T i) .projIota).Good P := hT
  rw [show auxKey (projModelName (T.map f) i) .projIota =
    (auxKey (projModelName T i) .projIota).map f from rfl, hE₁.find _ hk]
  cases h₁ : env₁.find? (auxKey (projModelName T i) .projIota) with
  | none => exact SimE.throw'
  | some c₁ =>
    have hc₁ := hE₁.good _ c₁ hk h₁
    cases c₁ with
    | thmInfo tcv tval =>
      simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
      cases h₂ : Expr.stripPis (nP + nF) tcv.type with
      | none => exact SimE.throw'
      | some q₂ =>
        obtain ⟨sbinders, sbody⟩ := q₂
        obtain ⟨hsb, hsbody⟩ := Expr.stripPis_good hc₁.1.2 h₂
        cases h₃ : Expr.stripPis (nP + nF) cvj.type with
        | none => exact SimE.throw'
        | some q₃ =>
          obtain ⟨cbindersR, _⟩ := q₃
          obtain ⟨hcb, _⟩ := Expr.stripPis_good hcvj.2 h₃
          simp only [Option.map_some, Expr.mapTele]
          have hpf := projFwd_map hf hT hc nF
          have hpfg := projFwd_good hT hc nF
          rw [domsMatchAux_ren (g := fun _ e => e.renameConsts (projFwd T ctorName nF))
            (fun _ e he => mapKeys_renameConsts_good hpf he)
            (fun _ e he => Expr.Good.renameConsts hpfg he) hf hsb hcb]
          refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
          cases sbody with
          | app s₁ rhsC =>
            cases s₁ with
            | app s₂ lhsC =>
              cases s₂ with
              | app s₃ tySlot =>
                cases s₃ with
                | const c us =>
                  cases us with
                  | cons ℓ rest =>
                    cases rest with
                    | nil =>
                      simp only [Expr.Good] at hsbody
                      obtain ⟨⟨⟨hcg, _⟩, hlhsC⟩, hrhsC⟩ := hsbody
                      simp only [Expr.mapKeys]
                      have hceq : (c.map f = eqName) ↔ (c = eqName) := by
                        simp only [eqName, roleKey, Key.map_eq_role_iff]
                      refine SimE.ite hceq.symm (fun _ => ?_) (fun _ => SimE.throw_bind)
                      rw [projIotaLhs_map, Expr.mapKeys_beq hf hlhsC
                        (projIotaLhs_good hT hc lps cvj.levelParams nP nF i)]
                      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
                      rw [Expr.mapKeys_beq_bvar']
                      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
                      rw [openPisAtFvars_mapKeys]
                      refine SimE.bind (SimE.unwrapOr'
                        (G := fun q : List (Expr md) × Expr md => q.2.Good P)
                        (fun q hq => (Expr.openPisAtFvars_good hc₁.1.2 hq).2)) (fun q hq => ?_)
                      obtain ⟨_, sbodyO⟩ := q
                      have hargsO := hq.getAppArgs
                      simp only [Expr.mapDoms, Expr.getAppArgs_mapKeys, getD_mapKeys_bvar]
                      exact checkIotaSidesTy_sim mode hops hES _ (hargsO.getD 0) (hargsO.getD 1)
                        (hargsO.getD 2) _ (projModelName T i)
                    | cons _ _ => first | exact SimE.throw_bind | exact SimE.throw'
                  | nil => first | exact SimE.throw_bind | exact SimE.throw'
                | _ => first | exact SimE.throw_bind | exact SimE.throw'
              | _ => first | exact SimE.throw_bind | exact SimE.throw'
            | _ => first | exact SimE.throw_bind | exact SimE.throw'
          | _ => first | exact SimE.throw_bind | exact SimE.throw'
    | _ => exact SimE.throw'

theorem projFnRule_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {T ctorName : Key md} (hc : ctorName.Good P) (pty : Expr md) (nP nF i : Nat)
    {rhsA : Expr md} (hr : rhsA.Good P) :
    projFnRule env'.find? (T.map f) (ctorName.map f) (pty.mapKeys f) nP nF i (rhsA.mapKeys f) =
      (projFnRule env.find? T ctorName pty nP nF i rhsA).mapKeys f := by
  unfold projFnRule
  have hrl : RecRule.Good P
      ({ ctor := ctorName, nfields := nF, ctorParams := nP,
         fire := (if Expr.recRulePlain pty nP nP nP then .plain else .inert),
         rhs := rhsA, paramsBlind := false } : RecRule md) := by
    refine ⟨hc, ?_, hr⟩
    split <;> trivial
  have h := recRuleBits_ren hE (recName := projFnName T i) hrl
  rw [← h, Expr.recRulePlain_mapKeys]
  simp only [RecRule.mapKeys]
  split <;> rfl

theorem projFnRule_good {find? : Key md → Option (ConstantInfo md)} {T ctorName : Key md}
    (hc : ctorName.Good P) {pty rhsA : Expr md} (hr : rhsA.Good P) (nP nF i : Nat) :
    (projFnRule find? T ctorName pty nP nF i rhsA).Good P := by
  unfold projFnRule
  refine ⟨hc, ?_, hr⟩
  simp only [recRuleBits]
  split <;> trivial

/-- **A projection function's install at a renamed structure.** -/
theorem checkProjFn_sim (mode : CheckMode) (hops : OpsSim P f L ops ops') {env : Env md}
    {env' : Env md'} (hE : EnvRelG P f L env env') {T ctorName : Key md} (hT : T.Good P)
    (hc : ctorName.Good P) (lps : List LevelParam) (nP nF i : Nat) :
    SimR (EnvRelG P f L) (checkProjFn mode ops env T ctorName lps nP nF i)
      (checkProjFn mode ops' env' (T.map f) (ctorName.map f) lps nP nF i) := by
  unfold checkProjFn
  refine SimR.bindE (checkProjLookups_sim hE hT hc lps nP nF i) (fun r hr => ?_)
  obtain ⟨cvj, mcv⟩ := r
  obtain ⟨hcvj, hmcv⟩ := hr
  simp only [ConstantVal.mapKeys_type]
  refine SimR.bindE (checkProjTy_sim hE hT hc lps hmcv.2 nP nF) (fun pty hpty => ?_)
  refine SimR.bindE (checkProjShape_sim pty cvj.type nP nF) (fun _ _ => ?_)
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.bindE (checkProjRule_sim hops hE hpty hcvj lps nP nF i) (fun rhsA hrhsA => ?_)
  refine SimR.bindE (checkProjIota_sim mode hops hE hE hT hc lps hcvj nP nF i) (fun _ _ => ?_)
  rw [projFnRule_ren hE hc pty nP nF i hrhsA]
  refine SimR.pure' (hE.push (c := .recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [projFnRule env.find? T ctorName pty nP nF i rhsA]) ⟨⟨hT, hpty⟩, ?_⟩)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact projFnRule_good hc hrhsA nP nF i

theorem installProjFnStep_sim (mode : CheckMode) (hops : OpsSim P f L ops ops')
    {T ctorName : Key md} (hT : T.Good P) (hc : ctorName.Good P) (lps : List LevelParam)
    (nP nF : Nat) {e : Env md} {e' : Env md'} (hE : EnvRelG P f L e e') (i : Nat) :
    SimR (EnvRelG P f L) (installProjFnStep mode ops T ctorName lps nP nF e i)
      (installProjFnStep mode ops' (T.map f) (ctorName.map f) lps nP nF e' i) := by
  unfold installProjFnStep
  have hk : (projModelName T i).Good P := hT
  rw [show projModelName (T.map f) i = (projModelName T i).map f from rfl, hE.find_isSome hk]
  refine SimR.ite Iff.rfl (fun _ => checkProjFn_sim mode hops hE hT hc lps nP nF i)
    (fun _ => SimR.pure' hE)
end Ix.Kernel
