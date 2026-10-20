module

public import IxC.Kernel.Verify.Rename.Modeled2

@[expose] public section

/-!
# The renaming walk through the modeled route: the nested rules (step 7.3, chunk (iii))

The nested-auxiliary rule's shape (`nestedRuleShape`), its `iota_j` check
(`checkIotaThmN`), and the per-rule checks (`checkIotaRule`, `checkIotaRules`)
at a renamed recursor over related environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

theorem map_lowerBVars_mapKeys (l : List (Expr md)) (n c : Nat) :
    (l.map (Expr.mapKeys f)).map (Expr.lowerBVars n c) =
      (l.map (Expr.lowerBVars n c)).map (Expr.mapKeys f) := by
  simp [List.map_map, Function.comp_def, Expr.mapKeys_lowerBVars]

theorem map_liftLooseBVars_mapKeys (l : List (Expr md)) (n c : Nat) :
    (l.map (Expr.mapKeys f)).map (Expr.liftLooseBVars n c) =
      (l.map (Expr.liftLooseBVars n c)).map (Expr.mapKeys f) := by
  simp [List.map_map, Function.comp_def, Expr.mapKeys_liftLooseBVars]

theorem Expr.GoodList.map_lowerBVars {l : List (Expr md)} (h : Expr.GoodList P l) (n c : Nat) :
    Expr.GoodList P (l.map (Expr.lowerBVars n c)) := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (h y hy).lowerBVars n c

theorem Expr.GoodList.map_liftLooseBVars {l : List (Expr md)} (h : Expr.GoodList P l) (n c : Nat) :
    Expr.GoodList P (l.map (Expr.liftLooseBVars n c)) := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (h y hy).liftLooseBVars n c

/-- The guard on a nested rule's stored instantiations, at renamed pins. -/
theorem pins_all_map {envS : Env md} {envS' : Env md'} (hES : EnvRelG P f L envS envS')
    {pins : List (Expr md)} (hp : Expr.GoodList P pins) (rP : Nat) (lps : List LevelParam) :
    (pins.map (Expr.mapKeys f)).all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
        p.constsResolve envS' && p.allLevelParamsDefined lps) =
      pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP && p.constsResolve envS &&
        p.allLevelParamsDefined lps) := by
  rw [List.all_map]
  exact List.all_congr_mem' fun p hpm => by
    simp only [Function.comp, Expr.hasFvar_mapKeys, Expr.looseBVarsBounded_mapKeys,
      constsResolve_ren hES (hp p hpm), Expr.allLevelParamsDefined_mapKeys]

/-- **A nested rule's shape at a renamed recursor**: the renamed shape. -/
theorem nestedRuleShape_map {env₁ envS : Env md} {env₁' envS' : Env md'}
    (hE₁ : EnvRelG P f L env₁ env₁') (hES : EnvRelG P f L envS envS') {cvName : Key md}
    (hn : cvName.Good P) (lps : List LevelParam) {tyA : Expr md} (hty : tyA.Good P)
    (mI rP cnP j : Nat) :
    nestedRuleShape env₁' envS' (cvName.map f) lps (tyA.mapKeys f) mI rP cnP j =
      (nestedRuleShape env₁ envS cvName lps tyA mI rP cnP j).map
        (fun s => (s.1, s.2.map (Expr.mapKeys f))) := by
  have hf := hES.inj
  unfold nestedRuleShape
  have hk : (auxKey (auxKey cvName .model) (.iota j)).Good P := hn
  rw [show auxKey (auxKey (cvName.map f) .model) (.iota j) =
    (auxKey (auxKey cvName .model) (.iota j)).map f from rfl, hE₁.findCV? hk, Option.isSome_map,
    Expr.stripPis_mapKeys]
  by_cases hc : (env₁.findCV? (auxKey (auxKey cvName .model) (.iota j))).isSome = true ∧ rP ≤ mI
  · rw [ite_eq_left hc, ite_eq_left hc]
    cases hs : tyA.stripPis mI with
    | none => rfl
    | some q =>
      obtain ⟨bs, b⟩ := q
      obtain ⟨_, hb⟩ := Expr.stripPis_good hty hs
      cases b with
      | forallE dom body bm =>
        simp only [Expr.Good] at hb
        have hdom := hb.1
        simp only [Option.map_some, Expr.mapTele, Expr.mapKeys]
        rw [← Expr.mapKeys_getAppFn]
        have hfn := hdom.getAppFn
        cases hg : dom.getAppFn with
        | const D lvls =>
          have hargs := hdom.getAppArgs
          simp only [Expr.mapKeys, Expr.getAppArgs_mapKeys, List.length_map, ← List.map_take,
            ← List.map_drop, map_lowerBVars_mapKeys, map_liftLooseBVars_mapKeys]
          have hpins := (hargs.take cnP).map_lowerBVars (mI - rP) 0
          rw [list_beq_mapKeys hf (hargs.take cnP) (hpins.map_liftLooseBVars (mI - rP) 0),
            Expr.map_mapKeys_beq_bvars, pins_all_map hES hpins rP lps]
          split <;> rfl
        | _ => rfl
      | _ => rfl
  · rw [ite_eq_right hc, ite_eq_right hc]
    rfl

theorem nestedRuleShape_good {env₁ envS : Env md} {cvName : Key md} {lps : List LevelParam}
    {tyA : Expr md} (hty : tyA.Good P) {mI rP cnP j : Nat} {s : List Level × List (Expr md)}
    (h : nestedRuleShape env₁ envS cvName lps tyA mI rP cnP j = some s) : Expr.GoodList P s.2 := by
  unfold nestedRuleShape at h
  split at h
  · split at h
    · next bs dom body bm hs =>
      obtain ⟨_, hb⟩ := Expr.stripPis_good hty hs
      simp only [Expr.Good] at hb
      split at h
      · dsimp only at h
        split at h
        · cases h
          exact ((hb.1.getAppArgs.take cnP).map_lowerBVars _ 0)
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h


theorem map_instSpine_renameConsts {ρ : Key md → Key md} {ρ' : Key md' → Key md'}
    (hρ : ∀ k : Key md, k.Good P → (ρ k).map f = ρ' (k.map f)) (as : List (Expr md)) (t : Nat) :
    ∀ {pins : List (Expr md)}, Expr.GoodList P pins →
      (pins.map (Expr.mapKeys f)).map
          (fun p => Expr.instSpine (as.map (Expr.mapKeys f)) t (p.renameConsts ρ')) =
        (pins.map fun p => Expr.instSpine as t (p.renameConsts ρ)).map (Expr.mapKeys f)
  | [], _ => rfl
  | p :: ps, hp => by
    simp only [Expr.goodList_cons] at hp
    simp only [List.map_cons, Expr.mapKeys_instSpine, mapKeys_renameConsts_good hρ hp.1,
      map_instSpine_renameConsts hρ as t hp.2]

theorem map_instSpine_mapKeys (as : List (Expr md)) (t : Nat) (pins : List (Expr md)) :
    (pins.map (Expr.mapKeys f)).map (fun p => Expr.instSpine (as.map (Expr.mapKeys f)) t p) =
      (pins.map fun p => Expr.instSpine as t p).map (Expr.mapKeys f) := by
  simp [List.map_map, Function.comp_def, Expr.mapKeys_instSpine]

/-- **The nested rule's `iota_j` check at a renamed rule.** -/
theorem checkIotaThmN_sim (mode : CheckMode) (hops : OpsSim P f L ops ops')
    {env₁ envS : Env md} {env₁' envS' : Env md'} (hE₁ : EnvRelG P f L env₁ env₁')
    (hES : EnvRelG P f L envS envS') {ρ : Key md → Key md} {ρ' : Key md' → Key md'}
    (hρ : ∀ k : Key md, k.Good P → (ρ k).map f = ρ' (k.map f))
    (hρg : ∀ k : Key md, k.Good P → (ρ k).Good P)
    {cvName : Key md} (hn : cvName.Good P) (lps : List LevelParam) {tyA : Expr md}
    (hty : tyA.Good P) (mI rP j : Nat) {r : RecRule md} (hr : r.Good P) {cvj : ConstantVal md}
    (hcvj : cvj.Good P) (cnP cnF : Nat) {rhsA : Expr md} (hrhs : rhsA.Good P) :
    SimE (RecRuleFire.Good P) (RecRuleFire.mapKeys f)
      (checkIotaThmN mode ops env₁ envS ρ cvName lps tyA mI rP j r cvj cnP cnF rhsA)
      (checkIotaThmN mode ops' env₁' envS' ρ' (cvName.map f) lps (tyA.mapKeys f) mI rP j
        (r.mapKeys f) (cvj.mapKeys f) cnP cnF (rhsA.mapKeys f)) := by
  have hf := hES.inj
  unfold checkIotaThmN
  rw [nestedRuleShape_map hE₁ hES hn lps hty mI rP cnP j]
  cases hs : nestedRuleShape env₁ envS cvName lps tyA mI rP cnP j with
  | none => exact SimE.pure' trivial rfl
  | some s =>
  obtain ⟨lvls, pins⟩ := s
  have hpins : Expr.GoodList P pins := nestedRuleShape_good hty hs
  simp only [Option.map_some]
  have hk : (auxKey (auxKey cvName .model) (.iota j)).Good P := hn
  rw [show auxKey (auxKey (cvName.map f) .model) (.iota j) =
    (auxKey (auxKey cvName .model) (.iota j)).map f from rfl, hE₁.findCV? hk]
  refine SimE.bind (SimE.unwrapOr' (G := ConstantVal.Good P)
    (fun cv h => hE₁.findCV?_good hk h)) (fun cvt hcvt => ?_)
  simp only [ConstantVal.mapKeys_levelParams]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  simp only [ConstantVal.mapKeys_type, openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.openPisAtFvars_good hcvt.2 hq)) (fun q hq => ?_)
  obtain ⟨fvs, tbody⟩ := q
  obtain ⟨hfvs, htbody⟩ := hq
  have htargs := htbody.getAppArgs
  have hlhs := htargs.getD 1
  have hrhsS := htargs.getD 2
  have hlargs := hlhs.getAppArgs
  simp only [Expr.mapDoms, ← Expr.mapKeys_getAppFn, isEqHead_mapKeys, Expr.getAppArgs_mapKeys,
    List.length_map, getD_mapKeys_bvar]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [← hρ cvName hn, mapKeys_const_beq hf hlhs.getAppFn (hρg cvName hn)]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [← List.map_take, ← List.map_take,
    list_beq_mapKeys hf (hlargs.take rP) (hfvs.take rP)]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hpinsF : Expr.GoodList P
      (pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts ρ)) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact Expr.Good.instSpine (hfvs.take rP) (Expr.Good.renameConsts hρg (hpins p hp))
  have hctor : (r.mapKeys f).ctor = r.ctor.map f := rfl
  rw [hctor, ← hρ r.ctor hr.1, getLastD_mapKeys_bvar, ← List.map_drop]
  try rw [← List.map_take]
  rw [map_instSpine_renameConsts hρ _ _ hpins, map_append_mapKeys,
    show (Expr.const ((ρ r.ctor).map f) lvls : Expr md') =
      (Expr.const (ρ r.ctor) lvls : Expr md).mapKeys f from rfl,
    ← Expr.mapKeys_mkAppN]
  have hargs : Expr.GoodList P
      ((pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts ρ)) ++
        fvs.drop rP) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hpinsF x hx
    · exact hfvs.drop rP x hx
  rw [Expr.mapKeys_beq hf (hlargs.getLastD 0)
    (Expr.Good.mkAppN (show Expr.Good P (Expr.const (ρ r.ctor) lvls) from hρg r.ctor hr.1) hargs)]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md × BinderMeta) × Expr md => q.2.Good P)
    (fun q hq => (Expr.stripPis_good hcvj.2 hq).2)) (fun q hq₀ => ?_)
  obtain ⟨_, cbody0⟩ := q
  simp only [Expr.mapTele, ← Expr.mapKeys_getAppFn]
  refine SimE.ite (by generalize cbody0.getAppFn = g; cases g <;> exact Iff.rfl) (fun _ => ?_)
    (fun _ => SimE.throw_bind)
  try rw [ConstantVal.mapKeys_levelParams]
  rw [← Expr.mapKeys_instantiateLevelParams,
    ← mapKeys_renameConsts_good hρ (Expr.Good.instantiateLevelParams hcvj.2 _ _),
    Expr.instPisAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.instPisAt_good hargs
      (Expr.Good.renameConsts hρg (Expr.Good.instantiateLevelParams hcvj.2 _ _)) hq))
    (fun q hq => ?_)
  obtain ⟨cdoms, cres⟩ := q
  obtain ⟨hcdoms, hcres⟩ := hq
  simp only [Expr.mapDoms, Expr.getAppArgs_mapKeys, List.length_map]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  try rw [← List.map_drop]
  try rw [← List.map_take]
  try rw [← List.map_drop]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ ((hlargs.drop rP).take (mI - rP))
    (hcres.getAppArgs.drop cnP)) (fun _ _ => ?_)
  try rw [map_fvarTypeD_mapKeys]
  try rw [← List.map_drop]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ (hfvs.drop rP).map_fvarTypeD
    (hcdoms.drop cnP)) (fun _ _ => ?_)
  rw [← mapKeys_renameConsts_good hρ hty, Expr.instPisAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1)
    (fun q hq => (Expr.instPisAt_good (hfvs.take rP) (Expr.Good.renameConsts hρg hty) hq).1))
    (fun q hq => ?_)
  obtain ⟨rdoms, _⟩ := q
  simp only [Expr.mapDoms]
  try rw [map_fvarTypeD_mapKeys]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ (hfvs.take rP).map_fvarTypeD hq)
    (fun _ _ => ?_)
  try rw [openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1)
    (fun q hq => (Expr.openPisAtFvars_good hty hq).1)) (fun q hq => ?_)
  obtain ⟨fvsP, _⟩ := q
  simp only [Expr.mapDoms]
  try rw [← List.map_take]
  rw [map_instSpine_mapKeys]
  have hpinsP : Expr.GoodList P (pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact Expr.Good.instSpine (hq.take rP) (hpins p hp)
  refine SimE.bind (checkAnnotList_sim hops hES _ _ hpinsP) (fun _ _ => ?_)
  rw [Expr.instPisAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q h => Expr.instPisAt_good hpinsP (Expr.Good.instantiateLevelParams hcvj.2 _ _) h))
    (fun q hq₂ => ?_)
  obtain ⟨cdomsP, crestP⟩ := q
  obtain ⟨hcdomsP, hcrestP⟩ := hq₂
  simp only [Expr.mapDoms]
  refine SimE.bind (checkTypedList_sim hops hES _ _ _ hpinsP hcdomsP) (fun _ _ => ?_)
  try rw [openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q h => Expr.openPisAtFvars_good hcrestP h)) (fun q hq₃ => ?_)
  obtain ⟨xFvsP, crest2P⟩ := q
  obtain ⟨hq₃, _⟩ := hq₃
  simp only [Expr.mapDoms, Expr.getAppArgs_mapKeys, List.length_map]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hPX : Expr.GoodList P (fvsP ++ xFvsP) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hq x hx
    · exact hq₃ x hx
  rw [map_append_mapKeys, Expr.instLamsAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1)
    (fun q h => (Expr.instLamsAt_good hPX hrhs h).1)) (fun q hq₄ => ?_)
  obtain ⟨ldoms, _⟩ := q
  simp only [Expr.mapDoms]
  try rw [map_fvarTypeD_mapKeys]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ hPX.map_fvarTypeD hq₄) (fun _ _ => ?_)
  rw [← mapKeys_renameConsts_good hρ hrhs, ← Expr.mapKeys_mkAppN]
  refine SimE.bind (hops.isDefEq hES _ _ _ hrhsS
    (Expr.Good.mkAppN (Expr.Good.renameConsts hρg hrhs) hfvs)) (fun c _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.bind (checkIotaSidesTy_sim mode hops hES _ (htargs.getD 0) hlhs hrhsS _ cvName)
    (fun _ _ => ?_)
  exact SimE.pure' hpins rfl
end Ix.Kernel
