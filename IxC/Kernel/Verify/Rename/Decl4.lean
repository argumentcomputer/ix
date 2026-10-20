module

public import IxC.Kernel.Verify.Rename.Decl3

@[expose] public section

/-!
# Renaming and the well-founded operations' evidence check

`checkDivModEvidence` at renamed arguments: the environment guard, the
certificate guards and the closure condition answer alike, and the
certificate checks succeed alike, over related operation records and
environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]

/-- The certificate statements name role keys, fvars and the operation. -/
theorem divModCertStmts_good (hall : P.All) {c : Key md} (hc : c.Good P) :
    ∀ p ∈ divModCertStmts c, Expr.GoodList P p.1 ∧ p.2.Good P := by
  unfold divModCertStmts
  repeat' split
  all_goals (try subst_vars); simp [Expr.Good, Key.Good, Expr.GoodList, hc, show ∀ r, P.role r from hall]

theorem divModCertApplied_mapKeys (proofS : Expr md) (hyps : List (Expr md)) :
    divModCertApplied (proofS.mapKeys f) (hyps.map (Expr.mapKeys f)) =
      (divModCertApplied proofS hyps).mapKeys f := by
  unfold divModCertApplied
  rcases hyps with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩ <;> rfl

theorem divModCertApplied_good (hall : P.All) {proofS : Expr md} {hyps : List (Expr md)}
    (hp : proofS.Good P)
    (hh : Expr.GoodList P hyps) : (divModCertApplied proofS hyps).Good P := by
  unfold divModCertApplied
  rcases hyps with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩ <;>
    simp_all [Expr.Good, Key.Good, Expr.GoodList, show ∀ r, P.role r from hall]

theorem Expr.GoodList.map_substConst0 {n : Key md} {r : Expr md} (hr : r.Good P)
    {es : List (Expr md)} (h : Expr.GoodList P es) :
    Expr.GoodList P (es.map (Expr.substConst0 n r)) := by
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨e₀, h₀, rfl⟩ := he
  exact substConst0_good hr (h e₀ h₀)

theorem map_substConst0_ren (hf : InjOn f P) {n : Key md} (hn : n.Good P) (r : Expr md)
    {es : List (Expr md)} (h : Expr.GoodList P es) :
    (es.map (Expr.mapKeys f)).map (Expr.substConst0 (n.map f) (r.mapKeys f)) =
      (es.map (Expr.substConst0 n r)).map (Expr.mapKeys f) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro e he
  exact substConst0_ren hf hn r (h e he)

theorem divModCertGuard_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {c : Key md} (hc : c.Good P) {annVal : Expr md} (ha : annVal.Good P) {hyps : List (Expr md)}
    (hh : Expr.GoodList P hyps) {eqE proof : Expr md} (he : eqE.Good P) (hp : proof.Good P) :
    divModCertGuard env' (c.map f) (annVal.mapKeys f) (hyps.map (Expr.mapKeys f))
        (eqE.mapKeys f) (proof.mapKeys f) =
      divModCertGuard env c annVal hyps eqE proof := by
  unfold divModCertGuard
  rw [substConstAll_ren hE.inj hc annVal hp, substConst0_ren hE.inj hc annVal he,
    map_substConst0_ren hE.inj hc annVal hh, List.all_map]
  have hs := substConstAll_good (n := c) ha hp
  have hs0 := substConst0_good (n := c) ha he
  simp only [Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys,
    Expr.allLevelParamsDefined_mapKeys, constsResolve_ren hE hs, constsResolve_ren hE hs0,
    Function.comp_def]
  congr 2
  apply List.all_congr_mem
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨x₀, h₀, rfl⟩ := hx
  exact constsResolve_ren hE (substConst0_good ha (hh x₀ h₀))

theorem divModCertsGuard_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') (hall : P.All)
    {c : Key md} (hc : c.Good P) {annVal : Expr md} (ha : annVal.Good P)
    {proofs : List (Expr md)} (hps : Expr.GoodList P proofs) :
    divModCertsGuard (proofs.map (Expr.mapKeys f)) env' (c.map f) (annVal.mapKeys f) =
      divModCertsGuard proofs env c annVal := by
  unfold divModCertsGuard
  rw [divModCertStmts_map, List.zip_map, List.all_map]
  apply List.all_congr_mem
  intro p hp
  obtain ⟨⟨hyps, eqE⟩, proof⟩ := p
  have hst := divModCertStmts_good hall hc _ (List.of_mem_zip hp).1
  have hpr : proof.Good P := hps proof (List.of_mem_zip hp).2
  exact divModCertGuard_ren hE hc ha hst.1 hst.2 hpr

section Ops

variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

theorem checkDivModCerts_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') (hall : P.All) {c : Key md} (hc : c.Good P) {annVal : Expr md}
    (ha : annVal.Good P) :
    ∀ (stmts : List (List (Expr md) × Expr md)) (proofs : List (Expr md)),
      (∀ p ∈ stmts, Expr.GoodList P p.1 ∧ p.2.Good P) → Expr.GoodList P proofs →
      SimV (checkDivModCerts ops env c annVal stmts proofs)
        (checkDivModCerts ops' env' (c.map f) (annVal.mapKeys f)
          (stmts.map fun p => (p.1.map (Expr.mapKeys f), p.2.mapKeys f))
          (proofs.map (Expr.mapKeys f)))
  | [], [], _, _ => SimV.pureT true
  | [], _ :: _, _, _ => SimV.pureT false
  | _ :: _, [], _, _ => SimV.pureT false
  | (hyps, eqE) :: srest, proof :: prest, hs, hp => by
    simp only [List.mem_cons, forall_eq_or_imp] at hs
    simp only [Expr.goodList_cons] at hp
    obtain ⟨⟨hh, he⟩, hs⟩ := hs
    simp only [List.map_cons, checkDivModCerts]
    rw [divModCertGuard_ren hE hc ha hh he hp.1]
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
    have hsA := substConstAll_good (n := c) ha hp.1
    have hhs := Expr.GoodList.map_substConst0 (n := c) ha hh
    rw [substConstAll_ren hE.inj hc annVal hp.1, map_substConst0_ren hE.inj hc annVal hh,
      divModCertApplied_mapKeys]
    refine SimE.bind (hops.annotate hE 4 _ (divModCertApplied_good hall hsA hhs)) (fun aA haA => ?_)
    refine SimE.bind (hops.inferType hE 4 aA haA) (fun tp htp => ?_)
    rw [substConst0_ren hE.inj hc annVal he]
    refine SimE.bind (hops.isDefEq hE 4 tp _ htp (substConst0_good ha he)) (fun b _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
    exact checkDivModCerts_sim hops hE hall hc ha srest prest hs hp.2

theorem find_beq_pin_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') {k : Key md}
    (hk : k.Good P) {pin : ConstantInfo md} (hpin : pin.Good P) :
    (env'.find? (k.map f) == some (pin.mapKeys f)) = (env.find? k == some pin) := by
  have h := find_eq_pin_ren hE hk hpin
  simp only [decide_eq_decide] at h
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact h

theorem divModEnvGuard_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    (hall : P.All) (c : Key md) :
    divModEnvGuard env' (c.map f) = divModEnvGuard env c := by
  unfold divModEnvGuard
  have hq : (env'.find? eqName == some eqA) = (env.find? eqName == some eqA) :=
    find_beq_pin_ren hE (k := eqName) (pin := eqA) (hall _)
      (ConstantInfo.good_of_pinIn hE.pre eqA_pinIn)
  rw [natOpGuard_ren_of hE c (natOpDeps_good_all hall c), natOpDeps_map, List.all_map, hq]
  refine andC (andC (andC (andC rfl ?_) rfl) ?_) ?_
  · apply List.all_congr_mem
    intro k hk
    exact natOpStoredOk_ren hE (natOpDeps_good_all hall c k hk)
  · rw [hE.find_role (hall .boolTrue)]
    cases env.find? (roleKey .boolTrue) with
    | none => rfl
    | some ci =>
      simp only [Option.map_some, ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_type]
      exact Expr.mapKeys_beq_const_role
  · rw [hE.find_role (hall .boolFalse)]
    cases env.find? (roleKey .boolFalse) with
    | none => rfl
    | some ci =>
      simp only [Option.map_some, ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_type]
      exact Expr.mapKeys_beq_const_role

theorem checkDivModEvidence_sim (hops : OpsSim P f L ops ops') {env env₂ : Env md}
    {env' env₂' : Env md'} (hE : EnvRelG P f L env env') (hE₂ : EnvRelG P f L env₂ env₂')
    (hall : P.All) {ev : Evidences md} (hev : ev.Good P) {c : Key md} (hc : c.Good P) :
    SimV (checkDivModEvidence ops ev env env₂ c)
      (checkDivModEvidence ops' (ev.mapKeys f) env' env₂' (c.map f)) := by
  unfold checkDivModEvidence
  rw [divModEnvGuard_ren hE₂ hall c]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw')
  rw [hE₂.find c hc]
  cases hfc : env₂.find? c with
  | none => exact SimE.throw'
  | some ci =>
  have hci := hE₂.good c ci hc hfc
  cases ci with
  | defnInfo cv v h =>
    simp only [Option.map_some, ConstantInfo.mapKeys.eq_2]
    have hv : v.Good P := hci.2
    rw [evidenceProofs_ren]
    cases hpf : evidenceProofs ev c with
    | none => exact SimE.throw'
    | some proofs =>
      have hps := evidenceProofs_good hev hpf
      simp only [Option.map_some]
      rw [divModCertsGuard_ren hE hall hc hv hps, evidenceLocal_ren hE hall hc hv hps]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw')
      refine hops.orElse _ _ _ _ ?_ SimE.throw'
      rw [divModCertStmts_map]
      exact checkDivModCerts_sim hops hE hall hc hv _ _ (divModCertStmts_good hall hc) hps
  | _ => exact SimE.throw'

end Ops

end Ix.Kernel
