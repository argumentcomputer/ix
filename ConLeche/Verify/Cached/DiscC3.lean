module

public import ConLeche.Verify.Cached.DiscC2

public section

/-!
# Cached body walks, part 3: the stuck-major rescue and iota

Simulation walks for the cached `majorToCtorI`/`pinArgsI`/`iotaRecI`
(`ConLeche/Cached/CoreC.lean`) against `majorToCtor`/`iotaRec`
(`ConLeche/Verify/Disc.lean`, deleted at task #221) — the port of
`ConLeche/Verify/DiscI3.lean`
under the task #163 recipe.  The pure comparand side of every statement
is byte-identical to the interned original's.
-/

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

private theorem majorToCtor_unfold (env : Env) (d : Nat) (recName : Name)
    (rules : List RecRule) (major : Expr) :
    majorToCtor mode (fueledFns mode env) env d recName rules major =
    (if isCtorApp env major then pure major else
    match rules with
    | [rl] =>
      match env.find? rl.ctor with
      | some (.ctorInfo cvj cnP _cnF) =>
        match (cvj.type.piResult).getAppFn with
        | .const T _ =>
          match env.find? T with
          | some (.indInfo cvT caps) =>
            if rl.k = true then
              (fueledFns mode env).inferIO d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ cvj.levelParams.length = ust.length then
                  if cnP ≤ tmaj.getAppArgs.length then
                    let fab := Expr.mkAppN (.const rl.ctor ust)
                      (tmaj.getAppArgs.take cnP)
                    if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                        fab.fvarLeaves.all
                          (fun l => major.fvarLeaves.contains l) then
                      iotaCerts (fueledFns mode env) env d false
                          (cvj.type.instantiateLevelParams
                            cvj.levelParams ust)
                          (tmaj.getAppArgs.take cnP) >>= fun rc =>
                      if rc then
                        (fueledFns mode env).inferIO d fab >>= fun tfab =>
                        (fueledFns mode env).defeq d tmaj tfab >>= fun rd =>
                        if rd then
                          proofIrrel (fueledFns mode env) env d fab major >>=
                            fun r =>
                          if r then pure fab
                          else pure major
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else if rl.eta = true then
              (fueledFns mode env).inferIO d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                    ust.length = cvT.levelParams.length ∧
                    capsNeverZero cvT.levelParams ust caps = true then
                  let fab := Expr.mkAppN (.const caps.etaCtor ust)
                    (etaFabArgsE env T ust tmaj.getAppArgs major
                      caps.etaFields)
                  if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    iotaCerts (fueledFns mode env) env d false
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams ust)
                        (etaFabArgsE env T ust tmaj.getAppArgs major
                          caps.etaFields) >>= fun rc =>
                    if rc then
                      structEtaCertWith mode (fueledFns mode env) env d fab major
                          tmaj >>= fun r =>
                      if r then pure fab
                      else if caps.etaFields = 0 then
                        proofIrrel (fueledFns mode env) env d fab major >>=
                          fun r' =>
                        if r' then pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else if T = andName then
              (fueledFns mode env).inferIO d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
                    cvj.levelParams.length = ust.length ∧
                    andRescueSlots env rl.ctor cnP ust = true then
                  let fab := Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
                  if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    iotaCerts (fueledFns mode env) env d false
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams ust)
                        (tmaj.getAppArgs ++
                          [.proj T 0 major, .proj T 1 major]) >>= fun rc =>
                    if rc then
                      (fueledFns mode env).inferIO d fab >>= fun tfab =>
                      (fueledFns mode env).defeq d tmaj tfab >>= fun rd =>
                      if rd then
                        proofIrrel (fueledFns mode env) env d fab major >>=
                          fun r =>
                        if r then pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else pure major
          | _ => pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major) := rfl

/-- Port of `majorToCtorI_sim`. -/
theorem majorToCtorC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : Expr}
    {major : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i major) (hmaj : Expr.WScoped d major) :
    SimC mode env s₀ (RelEC d)
      (majorToCtorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName
        rules i)
      (majorToCtor mode (fueledFns mode env) env d recName rules major) := by
  obtain rfl := CheckMode.eq_verified hμ
  show SimC .verified env s₀ (RelEC d)
    (pure (isCtorAppC (mkFEnv env) i) >>=
      fun ctor =>
      if ctor then pure i else
      match rules with
      | [rl] =>
        match (mkFEnv env).find? rl.ctor with
        | some (.ctorInfo cvj cnP cnF) =>
          match (cvj.type.piResult).getAppFn with
          | .const T _ =>
            match (mkFEnv env).find? T with
            | some (.indInfo cvT caps) =>
              if rl.k = true then
                (coreKnotI .verified (mkFEnv env) f).inferIO d i >>= fun tm =>
                (coreKnotI .verified (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                
                match (Expr.getAppFn tmaj) with
                | .const T' ust =>
                  pure (T' == T) >>= fun bq =>
                  if bq ∧ cvj.levelParams.length = ust.length then
                    pure (Expr.getAppArgsC tmaj) >>= fun margs =>
                    if cnP ≤ margs.length then
                      pure rl.ctor >>= fun ctorI =>
                      pure (Expr.const ctorI ust) >>= fun h =>
                      mkAppNM h (margs.take cnP) >>= fun fab =>
                      pure (Expr.wscopedBC d fab &&
                        Expr.looseBVarsBounded 0 fab &&
                        Expr.leafGuard fab i) >>=
                        fun g =>
                      if g then
                        constTyAtM (mkFEnv env) ctorI rl.ctor ust >>=
                          fun tyCtor =>
                        iotaCertsI (coreKnotI .verified (mkFEnv env) f) (mkFEnv env)
                            d false tyCtor (margs.take cnP) >>= fun rc =>
                        if rc then
                          (coreKnotI .verified (mkFEnv env) f).inferIO d fab >>=
                            fun tfab =>
                          (coreKnotI .verified (mkFEnv env) f).defeq d tmaj
                              tfab >>= fun rd =>
                          if rd then
                            proofIrrelI (coreKnotI .verified (mkFEnv env) f)
                                (mkFEnv env) d fab i >>= fun r =>
                            if r then pure fab
                            else pure i
                          else pure i
                        else pure i
                      else pure i
                    else pure i
                  else pure i
                | _ => pure i
              else if rl.eta = true then
                (coreKnotI .verified (mkFEnv env) f).inferIO d i >>= fun tm =>
                (coreKnotI .verified (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                
                match (Expr.getAppFn tmaj) with
                | .const T' ust =>
                  pure (Expr.getAppArgsC tmaj) >>= fun margs =>
                  pure ust >>= fun ustL =>
                  pure (T' == T) >>= fun bq =>
                  if bq ∧ margs.length = caps.etaParams ∧
                      ust.length = cvT.levelParams.length ∧
                      capsNeverZero cvT.levelParams ustL caps
                        = true then
                    pure T >>= fun TI =>
                    projAppsI (mkFEnv env) T TI ust margs i
                        caps.etaFields >>= fun projs =>
                    pure caps.etaCtor >>= fun ctorI =>
                    pure (Expr.const ctorI ust) >>= fun h =>
                    mkAppNM h (margs ++ projs) >>= fun fab =>
                    pure (Expr.wscopedBC d fab &&
                      Expr.looseBVarsBounded 0 fab &&
                      Expr.leafGuard fab i) >>=
                      fun g =>
                    if g then
                      constTyAtM (mkFEnv env) ctorI rl.ctor ust >>=
                        fun tyCtor =>
                      iotaCertsI (coreKnotI .verified (mkFEnv env) f) (mkFEnv env)
                          d false tyCtor (margs ++ projs) >>= fun rc =>
                      if rc then
                        structEtaCertWithI .verified (coreKnotI .verified (mkFEnv env) f)
                            (mkFEnv env) d fab i tmaj >>= fun r =>
                        if r then pure fab
                        else if caps.etaFields = 0 then
                          proofIrrelI (coreKnotI .verified (mkFEnv env) f)
                              (mkFEnv env) d fab i >>= fun r' =>
                          if r' then pure fab
                          else pure i
                        else pure i
                      else pure i
                    else pure i
                  else pure i
                | _ => pure i
              else if T = andName then
                (coreKnotI .verified (mkFEnv env) f).inferIO d i >>= fun tm =>
                (coreKnotI .verified (mkFEnv env) f).whnf d tm >>= fun tmaj =>

                match (Expr.getAppFn tmaj) with
                | .const T' ust =>
                  pure (Expr.getAppArgsC tmaj) >>= fun margs =>
                  pure (T' == T) >>= fun bq =>
                  if bq ∧ margs.length = cnP ∧
                      cvj.levelParams.length = ust.length ∧
                      (mkFEnv env).andRescueSlotsF rl.ctor cnP ust = true then
                    pure T >>= fun TI =>
                    projNodesI TI i [0, 1] >>= fun projs =>
                    pure rl.ctor >>= fun ctorI =>
                    pure (Expr.const ctorI ust) >>= fun h =>
                    mkAppNM h (margs ++ projs) >>= fun fab =>
                    pure (Expr.wscopedBC d fab &&
                      Expr.looseBVarsBounded 0 fab &&
                      Expr.leafGuard fab i) >>=
                      fun g =>
                    if g then
                      constTyAtM (mkFEnv env) ctorI rl.ctor ust >>=
                        fun tyCtor =>
                      iotaCertsI (coreKnotI .verified (mkFEnv env) f) (mkFEnv env)
                          d false tyCtor (margs ++ projs) >>= fun rc =>
                      if rc then
                        (coreKnotI .verified (mkFEnv env) f).inferIO d fab >>=
                          fun tfab =>
                        (coreKnotI .verified (mkFEnv env) f).defeq d tmaj
                            tfab >>= fun rd =>
                        if rd then
                          proofIrrelI (coreKnotI .verified (mkFEnv env) f)
                              (mkFEnv env) d fab i >>= fun r =>
                          if r then pure fab
                          else pure i
                        else pure i
                      else pure i
                    else pure i
                  else pure i
                | _ => pure i
              else pure i
            | _ => pure i
          | _ => pure i
        | _ => pure i
      | _ => pure i)
    (majorToCtor .verified (fueledFns .verified env) env d recName rules major)
  rw [majorToCtor_unfold]
  refine SimC.pureB ?_
  obtain rfl := hden
  have hden : RelC i i := rfl
  rw [isCtorAppC_spec' rfl]
  by_cases hctor : isCtorApp env i
  · rw [if_pos hctor, if_pos hctor]
    exact SimC.pure hs ⟨hden, hmaj⟩
  · rw [if_neg hctor, if_neg hctor]
    match rules with
    | [] => exact SimC.pure hs ⟨hden, hmaj⟩
    | _ :: _ :: _ => exact SimC.pure hs ⟨hden, hmaj⟩
    | [rl] =>
      dsimp only
      rw [show (mkFEnv env).find? rl.ctor = env.find? rl.ctor from
        mkFEnv_find? env rl.ctor]
      cases hfj : env.find? rl.ctor with
      | none => exact SimC.pure hs ⟨hden, hmaj⟩
      | some ci =>
        cases ci with
        | ctorInfo cvj cnP cnF =>
          dsimp only
          cases hpr : (cvj.type.piResult).getAppFn with
          | const T lus =>
            dsimp only
            rw [show (mkFEnv env).find? T = env.find? T from
              mkFEnv_find? env T]
            cases hfT : env.find? T with
            | none => exact SimC.pure hs ⟨hden, hmaj⟩
            | some ciT =>
              cases ciT with
              | indInfo cvT caps =>
                dsimp only
                by_cases hK : rl.k = true
                · rw [if_pos hK, if_pos hK]
                  refine SimC.bind (ih.inferIO hs hden hmaj)
                    (fun s₁ tm tmx hs₁ hP => ?_)
                  obtain ⟨htmd, hwtm⟩ := hP
                  refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                    (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                  obtain ⟨rfl, hwtmaj⟩ := hP₂
                  have hmargs : RelCL (Expr.getAppArgsC tmaj)
                      (Expr.getAppArgs tmaj) :=
                    Expr.getAppArgsC_spec _
                  refine SimC.pureB ?_
                  generalize hg : Expr.getAppFn tmaj = g
                  cases g with
                  | const T' ust =>
                    dsimp only
                    refine SimC.bind_left (pureEq_eff hs₂ (T' == T))
                      (fun s₂b bq hs₂ hbq => ?_)
                    subst bq
                    simp only [beq_iff_eq]
                    split
                    · refine SimC.pureB ?_
                      simp only [hmargs.length]
                      split
                      rotate_left
                      · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      refine SimC.bind_left (pureEq_eff hs₂ rl.ctor)
                        (fun s₂n ctorI hs₂ hQctorI => ?_)
                      subst hQctorI
                      refine SimC.bind_left (pureC_eff hs₂
                        (x := Expr.const rl.ctor ust))
                        (fun s₃ hd hs₃ hQh => ?_)
                      refine SimC.bind_left (mkAppNM_eff hs₃ hQh
                        (hmargs.take cnP))
                        (fun s₄ fab hs₄ hQfab => ?_)
                      have hQfab' : RelC fab
                          (Expr.mkAppN (.const rl.ctor ust)
                            ((Expr.getAppArgs tmaj).take cnP)) := hQfab
                      refine SimC.pureB ?_
                      rw [wscopedB_spec' hQfab',
                        looseBVarsBounded_spec' hQfab',
                        leafGuard_spec' hQfab' rfl]
                      split
                      · rename_i hguard
                        have hwfab := Expr.WScoped.of_wscopedB
                          (by simp only [Bool.and_eq_true] at hguard
                              exact hguard.1.1)
                        -- the relocated synthetic-spine certificate
                        refine SimC.bind_left (constTyAtM_eff hs₄ hfj)
                          (fun s₄c tyCtor hs₄c hQty => ?_)
                        simp only [ConstantInfo.toConstantVal] at hQty
                        have hwty : Expr.WScoped d
                            (cvj.type.instantiateLevelParams
                              cvj.levelParams ust) := by
                          obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
                          exact wscoped_instLevels_of_not_hasFvar
                            htf _ _
                        refine SimC.bind (iotaCertsC_sim ih hs₄c hQty
                          hwty (hmargs.take cnP)
                          (fun x hx => hwtmaj.getAppArgs x
                            (List.mem_of_mem_take hx)))
                          (fun s₄d rc rc' hs₄d hPrc => ?_)
                        obtain rfl : rc = rc' := hPrc
                        cases rc with
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact SimC.pure hs₄d ⟨hden, hmaj⟩
                        | true =>
                          simp only [↓reduceIte]
                          -- the official `to_cnstr_when_K` type check
                          refine SimC.bind (ih.inferIO hs₄d hQfab' hwfab)
                            (fun s₄e tfab tfabx hs₄e hPtf => ?_)
                          obtain ⟨htfd, hwtf⟩ := hPtf
                          refine SimC.bind (ih.defeq hs₄e rfl
                            htfd hwtmaj hwtf)
                            (fun s₄f rd rd' hs₄f hPrd => ?_)
                          obtain rfl : rd = rd' := hPrd
                          cases rd with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₄f ⟨hden, hmaj⟩
                          | true =>
                            simp only [↓reduceIte]
                            refine SimC.bind (proofIrrelC_sim ih hs₄f
                              hQfab' hden hwfab hmaj)
                              (fun s₅ r r' hs₅ hPr => ?_)
                            obtain rfl : r = r' := hPr
                            cases r with
                            | true =>
                              simp only [↓reduceIte]
                              exact SimC.pure hs₅ ⟨hQfab', hwfab⟩
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimC.pure hs₅ ⟨hden, hmaj⟩
                      · exact SimC.pure hs₄ ⟨hden, hmaj⟩
                    · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | bvar k =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | sort u =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | lit l =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | fvar ix t =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | app f' a' =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | lam t b' m =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | forallE t b' m =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | letE t v b' =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | proj sn jx e' =>
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                · rw [if_neg hK, if_neg hK]
                  by_cases hEta : rl.eta = true
                  · rw [if_pos hEta, if_pos hEta]
                    refine SimC.bind (ih.inferIO hs hden hmaj)
                      (fun s₁ tm tmx hs₁ hP => ?_)
                    obtain ⟨htmd, hwtm⟩ := hP
                    refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                      (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                    obtain ⟨rfl, hwtmaj⟩ := hP₂
                    have hmargs : RelCL (Expr.getAppArgsC tmaj)
                        (Expr.getAppArgs tmaj) :=
                      Expr.getAppArgsC_spec _
                    refine SimC.pureB ?_
                    generalize hg : Expr.getAppFn tmaj = g
                    cases g with
                    | const T' ust =>
                      dsimp only
                      refine SimC.pureB ?_
                      refine SimC.bind_left (pureEq_eff hs₂ ust)
                        (fun s₂r ustL hs₂r hustL => ?_)
                      subst ustL
                      refine SimC.bind_left (pureEq_eff hs₂r (T' == T))
                        (fun s₂rb bq hs₂r hbq => ?_)
                      subst bq
                      simp only [hmargs.length,
                        beq_iff_eq]
                      split
                      · refine SimC.bind_left (pureEq_eff hs₂r T)
                          (fun s₂t TI hs₂r hQTI => ?_)
                        subst TI
                        refine SimC.bind_left (projAppsC_eff T ust
                          caps.etaFields hs₂r hmargs hden)
                          (fun s₃ projs hs₃ hQp => ?_)
                        refine SimC.bind_left (pureEq_eff hs₃
                          caps.etaCtor)
                          (fun s₃n ctorI hs₃ hQctorI => ?_)
                        subst hQctorI
                        refine SimC.bind_left (pureC_eff hs₃
                          (x := Expr.const caps.etaCtor ust))
                          (fun s₄ hd hs₄ hQh => ?_)
                        refine SimC.bind_left (mkAppNM_eff hs₄ hQh
                          (hmargs.append hQp))
                          (fun s₅ fab hs₅ hQfab => ?_)
                        have hQfab' : RelC fab
                            (Expr.mkAppN (.const caps.etaCtor ust)
                              (etaFabArgsE env T ust (Expr.getAppArgs tmaj) i
                                caps.etaFields)) := hQfab
                        refine SimC.pureB ?_
                        rw [wscopedB_spec' hQfab',
                          looseBVarsBounded_spec' hQfab',
                          leafGuard_spec' hQfab' rfl]
                        split
                        · rename_i hguard
                          have hwfab := Expr.WScoped.of_wscopedB
                            (by simp only [Bool.and_eq_true] at hguard
                                exact hguard.1.1)
                          -- the relocated synthetic-spine certificate
                          refine SimC.bind_left (constTyAtM_eff hs₅ hfj)
                            (fun s₅c tyCtor hs₅c hQty => ?_)
                          simp only [ConstantInfo.toConstantVal] at hQty
                          have hwty : Expr.WScoped d
                              (cvj.type.instantiateLevelParams
                                cvj.levelParams ust) := by
                            obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
                            exact wscoped_instLevels_of_not_hasFvar
                              htf _ _
                          refine SimC.bind (iotaCertsC_sim ih hs₅c hQty
                            hwty (hmargs.append hQp) (fun x hx => ?_))
                            (fun s₅d rc rc' hs₅d hPrc => ?_)
                          · rcases List.mem_append.mp hx with hx | hx
                            · exact hwtmaj.getAppArgs x hx
                            · unfold etaProjs at hx
                              split at hx
                              · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
                                simpa [Expr.WScoped] using hmaj
                              · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
                                refine Expr.WScoped.mkAppN
                                  (by simp [Expr.WScoped]) ?_
                                intro y hy
                                rcases List.mem_append.mp hy with hy | hy
                                · exact hwtmaj.getAppArgs y hy
                                · rw [List.mem_singleton.mp hy]
                                  exact hmaj
                          obtain rfl : rc = rc' := hPrc
                          cases rc with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₅d ⟨hden, hmaj⟩
                          | true =>
                            simp only [↓reduceIte]
                            refine SimC.bind (structEtaCertWithC_sim hμ ih
                              henv hs₅d hQfab' hden rfl
                              hwfab hmaj hwtmaj)
                              (fun s₆ r r' hs₆ hPr => ?_)
                            obtain rfl : r = r' := hPr
                            cases r with
                            | true =>
                              simp only [↓reduceIte]
                              exact SimC.pure hs₆ ⟨hQfab', hwfab⟩
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              split
                              · refine SimC.bind (proofIrrelC_sim ih hs₆
                                  hQfab' hden hwfab hmaj)
                                  (fun s₇ r₂ r₂' hs₇ hPr₂ => ?_)
                                obtain rfl : r₂ = r₂' := hPr₂
                                cases r₂ with
                                | true =>
                                  simp only [↓reduceIte]
                                  exact SimC.pure hs₇ ⟨hQfab', hwfab⟩
                                | false =>
                                  simp only [Bool.false_eq_true,
                                    ↓reduceIte]
                                  exact SimC.pure hs₇ ⟨hden, hmaj⟩
                              · exact SimC.pure hs₆ ⟨hden, hmaj⟩
                        · exact SimC.pure hs₅ ⟨hden, hmaj⟩
                      · exact SimC.pure hs₂r ⟨hden, hmaj⟩
                    | bvar k =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | sort u =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | lit l =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | fvar ix t =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | app f' a' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | lam t b' m =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | forallE t b' m =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | letE t v b' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | proj sn jx e' =>
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  · rw [if_neg hEta, if_neg hEta]
                    by_cases hAnd : T = andName
                    · rw [if_pos hAnd, if_pos hAnd]
                      refine SimC.bind (ih.inferIO hs hden hmaj)
                        (fun s₁ tm tmx hs₁ hP => ?_)
                      obtain ⟨htmd, hwtm⟩ := hP
                      refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                        (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                      obtain ⟨rfl, hwtmaj⟩ := hP₂
                      have hmargs : RelCL (Expr.getAppArgsC tmaj)
                          (Expr.getAppArgs tmaj) :=
                        Expr.getAppArgsC_spec _
                      refine SimC.pureB ?_
                      generalize hg : Expr.getAppFn tmaj = g
                      cases g with
                      | const T' ust =>
                        dsimp only
                        refine SimC.pureB ?_
                        refine SimC.bind_left (pureEq_eff hs₂ (T' == T))
                          (fun s₂b bq hs₂ hbq => ?_)
                        subst bq
                        rw [andRescueSlotsF_spec]
                        simp only [hmargs.length, beq_iff_eq]
                        split
                        · refine SimC.bind_left (pureEq_eff hs₂ T)
                            (fun s₂t TI hs₂ hQTI => ?_)
                          subst TI
                          refine SimC.bind_left
                            (projNodesC_eff T [0, 1] hs₂ hden)
                            (fun s₃ projs hs₃ hQp => ?_)
                          have hQp' : RelCL projs
                              [Expr.proj T 0 i, Expr.proj T 1 i] := hQp
                          refine SimC.bind_left (pureEq_eff hs₃ rl.ctor)
                            (fun s₃n ctorI hs₃ hQctorI => ?_)
                          subst hQctorI
                          refine SimC.bind_left (pureC_eff hs₃
                            (x := Expr.const rl.ctor ust))
                            (fun s₄ hd hs₄ hQh => ?_)
                          refine SimC.bind_left (mkAppNM_eff hs₄ hQh
                            (hmargs.append hQp'))
                            (fun s₅ fab hs₅ hQfab => ?_)
                          have hQfab' : RelC fab
                              (Expr.mkAppN (.const rl.ctor ust)
                                (Expr.getAppArgs tmaj ++
                                  [Expr.proj T 0 i, Expr.proj T 1 i])) := hQfab
                          refine SimC.pureB ?_
                          rw [wscopedB_spec' hQfab',
                            looseBVarsBounded_spec' hQfab',
                            leafGuard_spec' hQfab' rfl]
                          split
                          · rename_i hguard
                            have hwfab := Expr.WScoped.of_wscopedB
                              (by simp only [Bool.and_eq_true] at hguard
                                  exact hguard.1.1)
                            -- the relocated synthetic-spine certificate
                            refine SimC.bind_left (constTyAtM_eff hs₅ hfj)
                              (fun s₅c tyCtor hs₅c hQty => ?_)
                            simp only [ConstantInfo.toConstantVal] at hQty
                            have hwty : Expr.WScoped d
                                (cvj.type.instantiateLevelParams
                                  cvj.levelParams ust) := by
                              obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
                              exact wscoped_instLevels_of_not_hasFvar
                                htf _ _
                            refine SimC.bind (iotaCertsC_sim ih hs₅c hQty
                              hwty (hmargs.append hQp') (fun x hx => ?_))
                              (fun s₅d rc rc' hs₅d hPrc => ?_)
                            · rcases List.mem_append.mp hx with hx | hx
                              · exact hwtmaj.getAppArgs x hx
                              · have hx' : x = Expr.proj T 0 i ∨
                                    x = Expr.proj T 1 i := by simpa using hx
                                rcases hx' with rfl | rfl <;>
                                  simpa [Expr.WScoped] using hmaj
                            obtain rfl : rc = rc' := hPrc
                            cases rc with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimC.pure hs₅d ⟨hden, hmaj⟩
                            | true =>
                              simp only [↓reduceIte]
                              -- the fabrication's type against the major's
                              refine SimC.bind (ih.inferIO hs₅d hQfab' hwfab)
                                (fun s₅e tfab tfabx hs₅e hPtf => ?_)
                              obtain ⟨htfd, hwtf⟩ := hPtf
                              refine SimC.bind (ih.defeq hs₅e rfl
                                htfd hwtmaj hwtf)
                                (fun s₅f rd rd' hs₅f hPrd => ?_)
                              obtain rfl : rd = rd' := hPrd
                              cases rd with
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                exact SimC.pure hs₅f ⟨hden, hmaj⟩
                              | true =>
                                simp only [↓reduceIte]
                                refine SimC.bind (proofIrrelC_sim ih hs₅f
                                  hQfab' hden hwfab hmaj)
                                  (fun s₆ r r' hs₆ hPr => ?_)
                                obtain rfl : r = r' := hPr
                                cases r with
                                | true =>
                                  simp only [↓reduceIte]
                                  exact SimC.pure hs₆ ⟨hQfab', hwfab⟩
                                | false =>
                                  simp only [Bool.false_eq_true, ↓reduceIte]
                                  exact SimC.pure hs₆ ⟨hden, hmaj⟩
                          · exact SimC.pure hs₅ ⟨hden, hmaj⟩
                        · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | bvar k =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | sort u =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | lit l =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | fvar ix t =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | app f' a' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | lam t b' m =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | forallE t b' m =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | letE t v b' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      | proj sn jx e' =>
                        exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    · rw [if_neg hAnd, if_neg hAnd]
                      exact SimC.pure hs ⟨hden, hmaj⟩
              | axiomInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
              | defnInfo cv v h => exact SimC.pure hs ⟨hden, hmaj⟩
              | thmInfo cv v => exact SimC.pure hs ⟨hden, hmaj⟩
              | ctorInfo cv nP' nF' => exact SimC.pure hs ⟨hden, hmaj⟩
              | recInfo cv mI rP rules' => exact SimC.pure hs ⟨hden, hmaj⟩
              | projInfo entry => exact SimC.pure hs ⟨hden, hmaj⟩
          | bvar k => exact SimC.pure hs ⟨hden, hmaj⟩
          | fvar ix t => exact SimC.pure hs ⟨hden, hmaj⟩
          | sort u => exact SimC.pure hs ⟨hden, hmaj⟩
          | app f' a' => exact SimC.pure hs ⟨hden, hmaj⟩
          | lam t b' m => exact SimC.pure hs ⟨hden, hmaj⟩
          | forallE t b' m => exact SimC.pure hs ⟨hden, hmaj⟩
          | letE t v b' => exact SimC.pure hs ⟨hden, hmaj⟩
          | lit l => exact SimC.pure hs ⟨hden, hmaj⟩
          | proj s'ᵢ j' e' => exact SimC.pure hs ⟨hden, hmaj⟩
        | axiomInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
        | defnInfo cv v h => exact SimC.pure hs ⟨hden, hmaj⟩
        | thmInfo cv v => exact SimC.pure hs ⟨hden, hmaj⟩
        | indInfo cv caps => exact SimC.pure hs ⟨hden, hmaj⟩
        | recInfo cv mI rP rules' => exact SimC.pure hs ⟨hden, hmaj⟩
        | projInfo entry => exact SimC.pure hs ⟨hden, hmaj⟩

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- Port of `pinArgsI_eff`: the cached pin instantiations denote the
nested comparand's mapped list.  (The interned original's separate
`us : List LIdx` / `lus : List Level` pair collapses to the single
level list, so its `denoteLList` premise vanishes.) -/
theorem pinArgsC_eff (lps : List Name) (us : List Level) :
    ∀ (ps : List Expr) {s₀ : CState}, CSOK mode env s₀ →
      ∀ {args : List Expr} {xs : List Expr} (t : Nat),
      RelCL args xs →
      CEff mode env s₀ (fun rs => RelCL rs
          (ps.map fun p => Expr.instSpine xs t
            (p.instantiateLevelParams lps us)))
        (pinArgsI lps us args t ps)
  | [], s₀, hs, args, xs, t, hargs => by
    exact CEff.pure hs RelCL.nil
  | p :: ps, s₀, hs, args, xs, t, hargs => by
    show CEff mode env s₀ _
      (pure p >>= fun praw =>
        instLevelParamsM lps us praw >>= fun pi =>
        instSpineM args t pi >>= fun r =>
        pinArgsI lps us args t ps >>= fun rs =>
        pure (r :: rs))
    refine CEff.bind (pureC_eff hs p) (fun s₁ praw hs₁ hQpr => ?_)
    refine CEff.bind (instLevelParamsM_eff hs₁ hQpr)
      (fun s₁' pi hs₁' hQp => ?_)
    refine CEff.bind (instSpineM_eff hs₁' hQp hargs)
      (fun s₂ r hs₂ hQr => ?_)
    refine CEff.bind (pinArgsC_eff lps us ps hs₂ t hargs)
      (fun s₃ rs hs₃ hQrs => ?_)
    exact CEff.pure hs₃ (RelCL.cons hQr hQrs)

/-- Port of `iotaIndexOkI_sim`: the canonical-index comparison (the ι
batch) simulates its fueled original. -/
theorem iotaIndexOkC_sim (ih : SSimC mode env f) {d : Nat} {mI rP cnP : Nat}
    {tyCtor : Expr} {tyx : Expr} {margs idx : List Expr} {ys is : List Expr}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hty : RelC tyCtor tyx) (hwty : Expr.WScoped d tyx)
    (hmargs : RelCL margs ys) (hwys : ∀ y ∈ ys, Expr.WScoped d y)
    (hidx : RelCL idx is) (hwis : ∀ x ∈ is, Expr.WScoped d x) :
    SimC mode env s₀ RelVC
      (iotaIndexOkI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d mI rP cnP
        tyCtor margs idx)
      (iotaIndexOk (fueledFns mode env) env d mI rP cnP tyx ys is) := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOkI, iotaIndexOk, if_pos hmr]
    exact SimC.pure hs rfl
  · simp only [iotaIndexOkI, iotaIndexOk, if_neg hmr]
    refine SimC.bind_left (piResidualM_eff hs hty hmargs)
      (fun s₁ ores hs₁ hQres => ?_)
    cases hresx : piResidual tyx ys with
    | none =>
      rw [hresx] at hQres
      cases ores with
      | none => exact SimC.pure hs₁ rfl
      | some res => exact nomatch hQres
    | some residual =>
      rw [hresx] at hQres
      cases ores with
      | none => exact nomatch hQres
      | some res =>
        have hresd : RelC res residual := hQres
        have hresW : Expr.WScoped d residual :=
          piResidual_WScoped hresx hwty hwys
        obtain rfl := hresd
        dsimp only
        refine SimC.pureB ?_
        have hres : RelCL (Expr.getAppArgsC res) (Expr.getAppArgs res) :=
          Expr.getAppArgsC_spec res
        exact defEqListC_sim ih hs₁ (hres.drop cnP) hidx
          (fun x hx => hresW.getAppArgs x (List.mem_of_mem_drop hx)) hwis

/-- A `Bool`-valued block that chains two lookups and three checks and
is then branched on, is the nested chain that branches after each
check: a failed check leaves the later lookups undone on both sides,
and a passed one reaches the same continuation.  The ι step's
certificate family is written in the first shape (one `certAtI`, so
`.trusted` omits the lookups with the checks that read them), its pure
comparand in the second. -/
private theorem certBlock_reshape {α β γ : Type}
    (A : CheckCM α) (B : α → CheckCM Bool) (C : CheckCM β)
    (D E : β → CheckCM Bool) (F : CheckCM (Option γ)) :
    ((A >>= fun a =>
        B a >>= fun r₂ =>
        if r₂ then
          C >>= fun b =>
          D b >>= fun r₃ =>
          if r₃ then E b else pure false
        else pure false) >>= fun ok =>
      if ok then F else pure none)
      = (A >>= fun a =>
          B a >>= fun r₂ =>
          if r₂ then
            C >>= fun b =>
            D b >>= fun r₃ =>
            if r₃ then
              E b >>= fun r₄ =>
              if r₄ then F else pure none
            else pure none
          else pure none) := by
  simp only [bind_assoc]
  congr 1
  funext a
  congr 1
  funext r₂
  cases r₂ with
  | false => simp
  | true =>
    simp only [if_true, bind_assoc]
    congr 1
    funext b
    congr 1
    funext r₃
    cases r₃ with
    | false => simp
    | true => simp only [if_true]

/-- Port of `iotaRec_certs_tail`: the shared certificate tail of the
iota step (after the firing-mode comparands) — the two licensed
telescope runs and the canonical-index comparison.  The interned
original's `cI jI : NIdx` name indices stay as (unconstrained) `Name`
parameters; their `denoteN` premises vanish with the name collapse. -/
private theorem iotaRec_certs_tail (ih : SSimC mode env f) (henv : EnvWF env)
    {mi : CheckMode} {d : Nat} {i major : Expr} {ex majorx : Expr} {cI jI : Name}
    {c cj : Name}
    {us usj : List Level}
    {cv cvj : ConstantVal} {mI rP cnP cnF : Nat}
    {rules : List RecRule} {rl : RecRule}
    {args margs : List Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (_hden : RelC i ex) (hw : Expr.WScoped d ex)
    (hfc : env.find? c = some (.recInfo cv mI rP rules))
    (hfj : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmd : RelC major majorx) (hmaj : Expr.WScoped d majorx)
    (hargs : RelCL args ex.getAppArgs)
    (hmargs : RelCL margs majorx.getAppArgs) :
    SimC mode env s₀ (RelOC d)
      ((constTyAtM (mkFEnv env) cI c us >>= fun tyRec =>
          iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d mi.betaGate
              tyRec (args.take mI ++ [major]) >>= fun r₂ =>
          if r₂ then
            constTyAtM (mkFEnv env) jI cj usj >>= fun tyCtor =>
            iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
                mi.betaGate tyCtor margs >>= fun r₃ =>
            if r₃ then
              iotaIndexOkI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d mI rP
                  rl.ctorParams tyCtor margs ((args.take mI).drop rP)
            else pure false
          else pure false) >>= fun ok =>
        if ok then
          ruleRhsAtM (mkFEnv env) cI jI c cj us >>= fun rhs =>
          mkAppNM rhs (args.take rP ++
              margs.drop rl.ctorParams) >>= fun red =>
          pure (some red)
        else pure none)
      (iotaCerts (fueledFns mode env) env d mi.betaGate
          (cv.type.instantiateLevelParams cv.levelParams us)
          (ex.getAppArgs.take mI ++ [majorx]) >>= fun r₂ =>
        if r₂ then
          iotaCerts (fueledFns mode env) env d mi.betaGate
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              majorx.getAppArgs >>= fun r₃ =>
          if r₃ then
            iotaIndexOk (fueledFns mode env) env d mI rP rl.ctorParams
                (cvj.type.instantiateLevelParams cvj.levelParams usj)
                majorx.getAppArgs ((ex.getAppArgs.take mI).drop rP) >>=
              fun r₄ =>
            if r₄ then
              pure (some (Expr.mkAppN
                (rl.rhs.instantiateLevelParams cv.levelParams us)
                (ex.getAppArgs.take rP ++
                  majorx.getAppArgs.drop rl.ctorParams)))
            else pure none
          else pure none
        else pure none) := by
  rw [certBlock_reshape]
  have hwrecty : Expr.WScoped d
      (cv.type.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfc)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  have hwctorty : Expr.WScoped d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  refine SimC.bind_left (constTyAtM_eff hs hfc)
    (fun s₁ tyRec hs₁ hQrec => ?_)
  simp only [ConstantInfo.toConstantVal] at hQrec
  refine SimC.bind (iotaCertsC_sim ih hs₁ hQrec hwrecty
    ((hargs.take mI).append (RelCL.cons hmd RelCL.nil)) ?_)
    (fun s₂ r₂ r₂' hs₂ hPr₂ => ?_)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw.getAppArgs x (List.mem_of_mem_take hx)
    · rcases List.mem_singleton.mp hx with rfl
      exact hmaj
  obtain rfl : r₂ = r₂' := hPr₂
  cases r₂ with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.pure hs₂ trivial
  | true =>
    simp only [↓reduceIte]
    refine SimC.bind_left (constTyAtM_eff hs₂ hfj)
      (fun s₃ tyCtor hs₃ hQctor => ?_)
    simp only [ConstantInfo.toConstantVal] at hQctor
    refine SimC.bind (iotaCertsC_sim ih hs₃ hQctor hwctorty hmargs
      hmaj.getAppArgs)
      (fun s₄ r₃ r₃' hs₄ hPr₃ => ?_)
    obtain rfl : r₃ = r₃' := hPr₃
    cases r₃ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₄ trivial
    | true =>
      simp only [↓reduceIte]
      refine SimC.bind (iotaIndexOkC_sim ih hs₄ hQctor hwctorty hmargs
        hmaj.getAppArgs ((hargs.take mI).drop rP)
        (fun x hx => hw.getAppArgs x
          (List.mem_of_mem_take (List.mem_of_mem_drop hx))))
        (fun s₆ r₄ r₄' hs₆ hPr₄ => ?_)
      obtain rfl : r₄ = r₄' := hPr₄
      cases r₄ with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₆ trivial
      | true =>
        simp only [↓reduceIte]
        refine SimC.bind_left (ruleRhsAtM_eff hs₆ hfc hrule)
          (fun s₇ rhs hs₇ hQrhs => ?_)
        refine SimC.bind_left (mkAppNM_eff hs₇ hQrhs
          ((hargs.take rP).append (hmargs.drop rl.ctorParams)))
          (fun s₈ red hs₈ hQred => ?_)
        refine SimC.pure hs₈ ⟨hQred, ?_⟩
        refine Expr.WScoped.mkAppN ?_ ?_
        · obtain ⟨-, -, -, -, -, hrules, -⟩ :=
            henv _ (find?_mem hfc)
          obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules
            rfl rl (List.mem_of_find?_eq_some hrule)
          exact wscoped_instLevels_of_not_hasFvar hrf _ _
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hw.getAppArgs x (List.mem_of_mem_take hx)
          · exact hmaj.getAppArgs x (List.mem_of_mem_drop hx)

/-- Simulation of the major chain, in either order (the K flag is the
single rule's stored bit, read identically on both sides). -/
theorem prepareMajorC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : Expr}
    {major : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i major) (hmaj : Expr.WScoped d major) :
    SimC mode env s₀ (RelEC d)
      (prepareMajorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName
        rules i)
      (prepareMajor mode (fueledFns mode env) env d recName rules major) := by
  unfold prepareMajorI prepareMajor
  by_cases hk : recRuleK rules = true
  · rw [if_pos hk, if_pos hk]
    refine SimC.bind (majorToCtorC_sim hμ ih henv hs hden hmaj)
      (fun s₁ m₁ m₁x hs₁ hP₁ => ?_)
    obtain ⟨hd₁, hw₁⟩ := hP₁
    refine SimC.bind (ih.whnf hs₁ hd₁ hw₁) (fun s₂ m₂ m₂x hs₂ hP₂ => ?_)
    obtain ⟨hd₂, hw₂⟩ := hP₂
    exact litMajorToCtorC_sim ih hs₂ hd₂ hw₂
  · rw [if_neg hk, if_neg hk]
    refine SimC.bind (ih.whnf hs hden hmaj) (fun s₁ m₁ m₁x hs₁ hP₁ => ?_)
    obtain ⟨hd₁, hw₁⟩ := hP₁
    refine SimC.bind (litMajorToCtorC_sim ih hs₁ hd₁ hw₁)
      (fun s₂ m₂ m₂x hs₂ hP₂ => ?_)
    obtain ⟨hd₂, hw₂⟩ := hP₂
    exact majorToCtorC_sim hμ ih henv hs₂ hd₂ hw₂

private theorem iotaRec_unfold (mi : CheckMode) (env : Env) (d : Nat)
    (e : Expr) :
    iotaRec mi (fueledFns mode env) env d e =
    (match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.recInfo cv mI rP rules) =>
        if e.getAppArgs.length = mI + 1 ∧
            us.length = cv.levelParams.length then
          prepareMajor mi (fueledFns mode env) env d c rules
              (e.getAppArgs.getD mI (.bvar 0)) >>=
            fun major =>
          match major.getAppFn with
          | .const cj usj =>
            match env.find? cj with
            | some (.ctorInfo cvj _ _) =>
              match rules.find? (fun r' => r'.ctor == cj) with
              | some rl =>
                if major.getAppArgs.length = rl.ctorParams + rl.nfields
                    then
                  if rl.fire = .inert then
                    throw (.notImplemented
                      "iota reduction over a nested auxiliary recursor rule")
                  else
                    liftFueled "level comparison" (Level.isEquivList usj
                        (recFireComparands rl cv.levelParams us
                          cvj.levelParams e.getAppArgs rP).1) >>=
                      fun okl =>
                    if okl then
                      (if rl.compareParams then
                          defEqList (fueledFns mode env) env d
                            (major.getAppArgs.take rl.ctorParams)
                            (recFireComparands rl cv.levelParams us
                              cvj.levelParams e.getAppArgs rP).2
                          else pure true) >>=
                        fun r₁ =>
                      if r₁ then
                        iotaCerts (fueledFns mode env) env d mi.betaGate
                            (cv.type.instantiateLevelParams
                              cv.levelParams us)
                            (e.getAppArgs.take mI ++ [major]) >>=
                          fun r₂ =>
                        if r₂ then
                          iotaCerts (fueledFns mode env) env d mi.betaGate
                              (cvj.type.instantiateLevelParams
                                cvj.levelParams usj)
                              major.getAppArgs >>= fun r₃ =>
                          if r₃ then
                            iotaIndexOk (fueledFns mode env) env d mI rP
                                rl.ctorParams
                                (cvj.type.instantiateLevelParams
                                  cvj.levelParams usj)
                                major.getAppArgs
                                ((e.getAppArgs.take mI).drop rP) >>=
                              fun r₄ =>
                            if r₄ then
                              pure (some (Expr.mkAppN
                                (rl.rhs.instantiateLevelParams
                                  cv.levelParams us)
                                (e.getAppArgs.take rP ++
                                  major.getAppArgs.drop
                                    rl.ctorParams)))
                            else pure none
                          else pure none
                        else pure none
                      else pure none
                    else pure none
                else pure none
              | none => pure none
            | _ => pure none
          | _ => pure none
        else pure none
      | _ => pure none
    | _ => pure none) := rfl

/-- Port of `iotaRecI_sim`.  The ι mode `mi` is separate from the
knot's `mode` (the ι batch: `iotaRecI` now reads `mi.betaGate` for the
slot licence, so the two are no longer identified by the `ttChecks`
collapse; the walks apply this at the ι cone's own mode `mi`). -/
theorem iotaRecC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {mi : CheckMode} (hmi : mi.verifiedChecks = true) {d : Nat} {i : Expr} {ex : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelOC d)
      (iotaRecI mi (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (iotaRec mi (fueledFns mode env) env d ex) := by
  obtain rfl := CheckMode.eq_verified hμ
  obtain rfl := CheckMode.eq_verified hmi
  unfold iotaRecI
  rw [iotaRec_unfold .verified]
  refine SimC.pureB ?_
  obtain rfl := hden
  have hden : RelC i i := rfl
  have hargs : RelCL (Expr.getAppArgsC i) (Expr.getAppArgs i) :=
    Expr.getAppArgsC_spec i
  generalize hg : Expr.getAppFn i = g
  cases g with
  | const c us =>
    dsimp only
    refine SimC.bind_left (pureEq_eff hs c) (fun s₀c cw hs hcw => ?_)
    subst cw
    rw [mkFEnv_find?]
    cases hfc : env.find? c with
    | none => exact SimC.pure hs trivial
    | some ci =>
      cases ci with
      | recInfo cv mI rP rules =>
        dsimp only
        refine SimC.pureB ?_
        simp only [hargs.length]
        by_cases hlen : (Expr.getAppArgs i).length = mI + 1 ∧
            us.length = cv.levelParams.length
        · rw [if_pos hlen, if_pos hlen]
          refine SimC.bind_left
            (pureBvar_eff hs 0)
            (fun s₁ bvar0 hs₁ hQ0 => ?_)
          have hQ0' : RelC bvar0 (Expr.bvar 0) := hQ0
          refine SimC.bind (prepareMajorC_sim hμ ih henv hs₁
            (RelCL.getD hQ0' mI hargs) (wscoped_getD hw.getAppArgs _))
            (fun s₄ major majorx hs₄ hP₂ => ?_)
          obtain ⟨rfl, hmaj⟩ := hP₂
          have hmargs : RelCL (Expr.getAppArgsC major)
              (Expr.getAppArgs major) := Expr.getAppArgsC_spec major
          refine SimC.pureB ?_
          generalize hg' : Expr.getAppFn major = g'
          cases g' with
          | const cj usj =>
            dsimp only
            refine SimC.bind_left (pureEq_eff hs₄ cj)
              (fun s₄c cjw hs₄ hcjw => ?_)
            subst cjw
            rw [mkFEnv_find?]
            cases hfj : env.find? cj with
            | none => exact SimC.pure hs₄ trivial
            | some cij =>
              cases cij with
              | ctorInfo cvj cnP cnF =>
                dsimp only
                cases hrule : rules.find? (fun r' => r'.ctor == cj) with
                | none => exact SimC.pure hs₄ trivial
                | some rl =>
                  dsimp only
                  refine SimC.pureB ?_
                  simp only [hmargs.length]
                  by_cases hmlen : (Expr.getAppArgs major).length =
                      rl.ctorParams + rl.nfields
                  · rw [if_pos hmlen, if_pos hmlen]
                    by_cases hin : rl.fire = RecRuleFire.inert
                    · rw [if_pos hin, if_pos hin]
                      exact SimC.throw
                    · rw [if_neg hin, if_neg hin]
                      -- both isSome pins hold; walk the certificates
                      have hargsW : ∀ a ∈ (Expr.getAppArgs i),
                          Expr.WScoped d a := hw.getAppArgs
                      have hpinsW : ∀ lvls pins,
                          rl.fire = .nested lvls pins →
                          ∀ pin ∈ pins, pin.hasFvar = false := by
                        intro lvls pins hf' pin hpin
                        obtain ⟨-, -, -, -, -, hrules, -⟩ :=
                          henv _ (find?_mem hfc)
                        obtain ⟨-, -, -, -, g5⟩ := hrules cv mI rP rules
                          rfl rl (List.mem_of_find?_eq_some hrule)
                        exact ((g5 lvls pins hf').2.2.1 pin hpin).1
                      have hcmpW := recFireComparands_snd_WScoped rl
                        cv.levelParams us cvj.levelParams
                        (Expr.getAppArgs i) rP hargsW hpinsW
                      cases hfire : rl.fire with
                      | inert => simp [hfire] at *
                      | plain =>
                        simp only [recFireComparands, hfire] at hcmpW ⊢
                        refine SimC.bind_left (substLevelTreesM_eff hs₄
                          cv.levelParams us
                          (cvj.levelParams.map Level.param))
                          (fun s₄l cmpLvls hs₄l hQl => ?_)
                        rw [List.map_map] at hQl
                        subst cmpLvls
                        refine SimC.bind_pure_left ?_
                        refine SimC.bind_left (isEquivListLM_eff hs₄l)
                          (fun s₄o oL hs₄o hoL => ?_)
                        subst oL
                        refine SimC.bind (SimC.liftFueled _ _ hs₄o)
                          (fun s₆ okl okl' hs₆ hPok => ?_)
                        obtain rfl : okl = okl' := hPok
                        cases okl with
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact SimC.pure hs₆ trivial
                        | true =>
                          simp only [↓reduceIte]
                          refine SimC.bind (P := RelVC) ?_
                            (fun s₇ r₁ r₁' hs₇ hPr₁ => ?_)
                          · -- the parameter comparison, absent from both
                            -- sides at a `paramsBlind` rule
                            by_cases hcp : rl.compareParams = true
                            · rw [if_pos hcp, if_pos hcp]
                              exact defEqListC_sim ih hs₆
                                (hmargs.take rl.ctorParams)
                                (hargs.take rl.ctorParams)
                                (fun x hx => hmaj.getAppArgs x
                                  (List.mem_of_mem_take hx))
                                (fun x hx => hargsW x
                                  (List.mem_of_mem_take hx))
                            · rw [if_neg hcp, if_neg hcp]
                              exact SimC.pure hs₆ rfl
                          obtain rfl : r₁ = r₁' := hPr₁
                          cases r₁ with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₇ trivial
                          | true =>
                            simp only [↓reduceIte]
                            exact iotaRec_certs_tail ih henv hs₇ hden hw
                              hfc hfj hrule rfl hmaj hargs
                              hmargs
                      | nested lvls pins =>
                        simp only [recFireComparands, hfire] at hcmpW ⊢
                        refine SimC.bind_left (substLevelTreesM_eff hs₄
                          cv.levelParams us lvls)
                          (fun s₄l cmpLvls hs₄l hQl => ?_)
                        subst cmpLvls
                        refine SimC.bind_left (pinArgsC_eff
                          cv.levelParams us pins hs₄l (rP - 1)
                          (hargs.take rP))
                          (fun s₅ cmpArgs hs₅ hQc => ?_)
                        refine SimC.bind_left (isEquivListLM_eff hs₅)
                          (fun s₄o oL hs₄o hoL => ?_)
                        subst oL
                        refine SimC.bind (SimC.liftFueled _ _ hs₄o)
                          (fun s₆ okl okl' hs₆ hPok => ?_)
                        obtain rfl : okl = okl' := hPok
                        cases okl with
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact SimC.pure hs₆ trivial
                        | true =>
                          simp only [↓reduceIte]
                          rw [if_pos (RecRule.compareParams_nested hfire),
                            if_pos (RecRule.compareParams_nested hfire)]
                          refine SimC.bind (defEqListC_sim ih hs₆
                            (hmargs.take rl.ctorParams) hQc
                            (fun x hx => hmaj.getAppArgs x
                              (List.mem_of_mem_take hx))
                            hcmpW)
                            (fun s₇ r₁ r₁' hs₇ hPr₁ => ?_)
                          obtain rfl : r₁ = r₁' := hPr₁
                          cases r₁ with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₇ trivial
                          | true =>
                            simp only [↓reduceIte]
                            exact iotaRec_certs_tail ih henv hs₇ hden hw
                              hfc hfj hrule rfl hmaj hargs
                              hmargs
                  · rw [if_neg hmlen, if_neg hmlen]
                    exact SimC.pure hs₄ trivial
              | axiomInfo cv' => exact SimC.pure hs₄ trivial
              | defnInfo cv' v h => exact SimC.pure hs₄ trivial
              | thmInfo cv' v => exact SimC.pure hs₄ trivial
              | indInfo cv' caps => exact SimC.pure hs₄ trivial
              | recInfo cv' mI' rP' rules' => exact SimC.pure hs₄ trivial
              | projInfo entry => exact SimC.pure hs₄ trivial
          | bvar k =>
            exact SimC.pure hs₄ trivial
          | sort u =>
            exact SimC.pure hs₄ trivial
          | lit l =>
            exact SimC.pure hs₄ trivial
          | fvar ix t =>
            exact SimC.pure hs₄ trivial
          | app f' a' =>
            exact SimC.pure hs₄ trivial
          | lam t b' m =>
            exact SimC.pure hs₄ trivial
          | forallE t b' m =>
            exact SimC.pure hs₄ trivial
          | letE t v b' =>
            exact SimC.pure hs₄ trivial
          | proj sn jx e' =>
            exact SimC.pure hs₄ trivial
        · rw [if_neg hlen, if_neg hlen]
          exact SimC.pure hs trivial
      | axiomInfo cv => exact SimC.pure hs trivial
      | defnInfo cv v h => exact SimC.pure hs trivial
      | thmInfo cv v => exact SimC.pure hs trivial
      | indInfo cv caps => exact SimC.pure hs trivial
      | ctorInfo cv nP nF => exact SimC.pure hs trivial
      | projInfo entry => exact SimC.pure hs trivial
  | bvar k =>
    exact SimC.pure hs trivial
  | sort u =>
    exact SimC.pure hs trivial
  | lit l =>
    exact SimC.pure hs trivial
  | fvar ix t =>
    exact SimC.pure hs trivial
  | app f' a' =>
    exact SimC.pure hs trivial
  | lam t b' m =>
    exact SimC.pure hs trivial
  | forallE t b' m =>
    exact SimC.pure hs trivial
  | letE t v b' =>
    exact SimC.pure hs trivial
  | proj s'ᵢ j' e' =>
    exact SimC.pure hs trivial

end Walks2

end ConLeche.Cached
