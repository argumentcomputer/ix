module

public import ConLeche.Verify.Cached.BridgeCS1

public section

/-!
# Cached shared-state walks, part 2: the inductive-install checker
functions

Port of `ConLeche/Verify/BridgeS2.lean` for the cached tier.  The
single-environment functions of the modeled-inductive install path
(`checkMemberVal`, the iota-theorem checks, the projection stages), as
`SimC`s between the `sharedOpsC` and `(fueledOpsM mode)`
instantiations.  The per-site scoping facts mirror
`ConLeche/Verify/BridgeWfImp.lean`'s `_wfimp` walks; the operation
environment is the `SimC`'s `env` (for the iota checks that is
`envSelf` — the pure model lookups run at the separately passed
`env'`).

The *subjects* are the very same `Expr`-level checker functions as in
the interned original — only the operations record differs — so the
walks transpose by the recipe's substitutions alone (`SimAt → SimC`,
`ISOK → CSOK`, no `Ext` binder, state-free value relations).  The pure
comparand side of every statement is byte-identical to the interned
original's.
-/

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr

variable {mode : CheckMode}

section Walks2

variable {env : Env} {s₀ : CState}

/-- `unwrapOr` as a `SimC`, remembering the unwrapped value. -/
protected theorem SimC.unwrapOr' {α : Type} {o : Option α}
    {err : CheckError} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ o = some v)
      (unwrapOr o err : CheckCM α) (unwrapOr o err : FueledM α) := by
  cases o with
  | none => exact SimC.throw
  | some a => exact SimC.pure hs ⟨rfl, rfl⟩

/-- `checkTypedList` at the cached shared operations. -/
theorem checkTypedListS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {depth : Nat} :
    ∀ {as bs : List Expr},
      (∀ a ∈ as, Expr.WScoped depth a) → (∀ b ∈ bs, Expr.WScoped depth b) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkTypedList (sharedOpsC mode (mkFEnv env)) env depth as bs)
        (checkTypedList (fueledOpsM mode) env depth as bs)
  | [], [], _, _, s₀, hs => SimC.pure hs rfl
  | [], _ :: _, _, _, s₀, hs => SimC.throw
  | _ :: _, [], _, _, s₀, hs => SimC.throw
  | a :: as, b :: bs, ha, hb, s₀, hs => by
    unfold checkTypedList
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_infer_sim hμ henv hs (ha a List.mem_cons_self))
      (fun s₁ ty ty' hs₁ hP => ?_)
    obtain ⟨rfl, htyW⟩ := hP
    refine SimC.bind (opB_sim hμ henv hs₁ htyW (hb b List.mem_cons_self))
      (fun s₂ c c' hs₂ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkTypedListS_sim hμ henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) hs₂

/-- `checkDefEqList` at the cached shared operations. -/
theorem checkDefEqListS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {depth : Nat} :
    ∀ {as bs : List Expr},
      (∀ a ∈ as, Expr.WScoped depth a) → (∀ b ∈ bs, Expr.WScoped depth b) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDefEqList (sharedOpsC mode (mkFEnv env)) env depth as bs)
        (checkDefEqList (fueledOpsM mode) env depth as bs)
  | [], [], _, _, s₀, hs => SimC.pure hs rfl
  | [], _ :: _, _, _, s₀, hs => SimC.throw
  | _ :: _, [], _, _, s₀, hs => SimC.throw
  | a :: as, b :: bs, ha, hb, s₀, hs => by
    unfold checkDefEqList
    dsimp only [sharedOpsC]
    refine SimC.bind (opB_sim hμ henv hs (ha a List.mem_cons_self)
        (hb b List.mem_cons_self))
      (fun s₁ c c' hs₁ hP => ?_)
    obtain rfl : c = c' := hP
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkDefEqListS_sim hμ henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) hs₁

/-- `checkAnnotList` at the cached shared operations. -/
theorem checkAnnotListS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {depth : Nat} :
    ∀ {as : List Expr},
      (∀ a ∈ as, Expr.WScoped depth a) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkAnnotList (sharedOpsC mode (mkFEnv env)) env depth as)
        (checkAnnotList (fueledOpsM mode) env depth as)
  | [], _, s₀, hs => SimC.pure hs rfl
  | a :: as, ha, s₀, hs => by
    unfold checkAnnotList
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_annotate_sim hμ henv hs
        (ha a List.mem_cons_self))
      (fun s₁ aA aA' hs₁ hP => ?_)
    obtain ⟨rfl, -⟩ := hP
    by_cases hc : (aA == a) = true
    case neg =>
      simp only [if_neg hc]
      exact SimC.throw_bind
    case pos =>
      simp only [if_pos hc]
      exact checkAnnotListS_sim hμ henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) hs₁

/-- The iota-sides type certificate at the cached shared operations
(task #100 stage 3). -/
theorem checkIotaSidesTyS_sim (hμ : mode.verifiedChecks = true) {depth : Nat} {alphaS lhsS rhsS : Expr}
    {ℓA : Level} {cvName : Name} (henv : EnvWF env)
    (hα : Expr.WScoped depth alphaS) (hl : Expr.WScoped depth lhsS)
    (hr : Expr.WScoped depth rhsS) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkIotaSidesTy mode (sharedOpsC mode (mkFEnv env)) env depth alphaS
        lhsS rhsS ℓA cvName)
      (checkIotaSidesTy mode (fueledOpsM mode) env depth alphaS lhsS rhsS
        ℓA cvName) := by
  unfold checkIotaSidesTy
  dsimp only [sharedOpsC]
  refine SimC.bind (opE_infer_sim hμ henv hs hl)
    (fun s₁ tl tl' hs₁ hTl => ?_)
  obtain ⟨rfl, htlW⟩ := hTl
  refine SimC.bind (opB_sim hμ henv hs₁ htlW hα)
    (fun s₂ cl cl' hs₂ hCl => ?_)
  obtain rfl : cl = cl' := hCl
  cases cl with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (opE_infer_sim hμ henv hs₂ hr)
    (fun s₃ tr tr' hs₃ hTr => ?_)
  obtain ⟨rfl, htrW⟩ := hTr
  refine SimC.bind (opB_sim hμ henv hs₃ htrW hα)
    (fun s₄ cr cr' hs₄ hCr => ?_)
  obtain rfl : cr = cr' := hCr
  cases cr with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  -- the type slot's own sort (task #146) — mode-gated (task #147)
  cases htt : mode.ttChecks with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.pure hs₄ rfl
  | true =>
  simp only [↓reduceIte]
  refine SimC.bind (opE_infer_sim hμ henv hs₄ hα)
    (fun s₅ tα tα' hs₅ hTα => ?_)
  obtain ⟨rfl, htαW⟩ := hTα
  refine SimC.bind (opB_sim hμ henv hs₅ htαW (by simp [Expr.WScoped]))
    (fun s₆ cα cα' hs₆ hCα => ?_)
  obtain rfl : cα = cα' := hCα
  cases cα with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₆ rfl

/-- The iota-theorem check at the cached shared operations (the
operation environment is `env` = the provisioned `envSelf`; `env'` only
feeds the pure model lookups). -/
theorem checkIotaThmS_sim (hμ : mode.verifiedChecks = true) {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkIotaThm mode (sharedOpsC mode (mkFEnv env)) env' env f cvName lps
        tyA mI rP j r cvj cnP cnF rhsA)
      (checkIotaThm mode (fueledOpsM mode) env' env f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA) := by
  unfold checkIotaThm
  dsimp only [sharedOpsC]
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cvt p' hs₁ hP => ?_)
  obtain ⟨rfl, hthm⟩ := hP
  try dsimp only
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, hopen⟩ := hQ
  obtain ⟨fvs, tbody⟩ := q
  dsimp only
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen (Expr.WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      Expr.WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : Expr.WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : Expr.WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      Expr.WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
  by_cases h2 : isEqHead tbody.getAppFn = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : tbody.getAppArgs.length = 3
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  try dsimp only
  by_cases h4 : ((tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (f cvName) (lps.map .param)) = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  by_cases h5 : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length =
      mI + 1
  case neg => simp only [if_neg h5]; exact SimC.throw_bind
  simp only [if_pos h5]
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP == fvs.take rP) = true
  case neg => simp only [if_neg h6]; exact SimC.throw_bind
  simp only [if_pos h6]
  by_cases h7 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP)) = true
  case neg => simp only [if_neg h7]; exact SimC.throw_bind
  simp only [if_pos h7]
  by_cases h8 : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => simp only [if_neg h8]; exact SimC.throw_bind
  simp only [if_pos h8]
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ q2 q2' hs₃ hQ2 => ?_)
  obtain ⟨rfl, hcinst⟩ := hQ2
  obtain ⟨cdoms, cres⟩ := q2
  dsimp only
  have hcargW : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
      Expr.WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact hfvsW a (List.mem_of_mem_take hax)
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst
    (Expr.WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => simp only [if_neg h9]; exact SimC.throw_bind
  simp only [if_pos h9]
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => hlargsW a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      (fun b hb => Expr.WScoped.getAppArgs hcresW b
        (List.mem_of_mem_drop hb)) hs₃)
    (fun s₄ u1 u1' hs₄ hU1 => ?_)
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_drop hx)))
      (fun b hb => hcdomsW b (List.mem_of_mem_drop hb)) hs₄)
    (fun s₅ u2 u2' hs₅ hU2 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ q3 q3' hs₆ hQ3 => ?_)
  obtain ⟨rfl, hrinst⟩ := hQ3
  obtain ⟨rdoms, rrest⟩ := q3
  dsimp only
  have hrinstW := instPisAt_WScoped _ _ hrinst
    (Expr.WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact htyA))
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
  obtain ⟨hrdomsW, -⟩ := hrinstW
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_take hx)))
      (fun b hb => hrdomsW b hb) hs₆)
    (fun s₇ u3 u3' hs₇ hU3 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₇) (fun s₈ q4 q4' hs₈ hQ4 => ?_)
  obtain ⟨rfl, hopenP⟩ := hQ4
  obtain ⟨fvsP, restP⟩ := q4
  dsimp only
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP
    (Expr.WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  refine SimC.bind (SimC.unwrapOr' hs₈) (fun s₉ q5 q5' hs₉ hQ5 => ?_)
  obtain ⟨rfl, hcinstP⟩ := hQ5
  obtain ⟨cdomsP, crestP⟩ := q5
  dsimp only
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP
    (Expr.WScoped.of_not_hasFvar hctor)
    (fun a ha => hfvsPW a (List.mem_of_mem_take ha))
  obtain ⟨hcdomsPW, hcrestPW⟩ := hcinstPW
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact (fvarTypeD_WScoped
          (hfvsPW x (List.mem_of_mem_take hx))).mono (by omega))
      (fun b hb => (hcdomsPW b hb).mono (by omega)) hs₉)
    (fun s₉b uP uP' hs₉b hUP => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₉b) (fun s10 q6 q6' hs10 hQ6 => ?_)
  obtain ⟨rfl, hopenX⟩ := hQ6
  obtain ⟨xFvsP, crest2⟩ := q6
  dsimp only
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP hopenX hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, Expr.WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact Expr.WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  refine SimC.bind (SimC.unwrapOr' hs10) (fun s11 q7 q7' hs11 hQ7 => ?_)
  obtain ⟨rfl, hlinst⟩ := hQ7
  obtain ⟨ldoms, lrest⟩ := q7
  dsimp only
  have hlinstW := instLamsAt_WScoped _ _ hlinst
    (Expr.WScoped.of_not_hasFvar hrhsA) hfvsPW'
  obtain ⟨hldomsW, -⟩ := hlinstW
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsPW' x hx))
      (fun b hb => hldomsW b hb) hs11)
    (fun s12 u4 u4' hs12 hU4 => ?_)
  refine SimC.bind (opB_sim hμ henv hs12 hrhsSW
      (Expr.WScoped.mkAppN
        (Expr.WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hrhsA))
        (fun x hx => hfvsW x hx)))
    (fun s13 c c' hs13 hC => ?_)
  obtain rfl : c = c' := hC
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact checkIotaSidesTyS_sim hμ henv (WScoped_getD' htargsW 0)
      hlhsW hrhsSW hs13

/-- The nested-auxiliary iota-theorem check at the cached shared
operations. -/
theorem checkIotaThmNS_sim (hμ : mode.verifiedChecks = true) {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkIotaThmN mode (sharedOpsC mode (mkFEnv env)) env' env f cvName lps
        tyA mI rP j r cvj cnP cnF rhsA)
      (checkIotaThmN mode (fueledOpsM mode) env' env f cvName lps tyA
        mI rP j r cvj cnP cnF rhsA) := by
  unfold checkIotaThmN
  dsimp only [sharedOpsC]
  match hshape : nestedRuleShape env' env cvName lps tyA mI rP cnP j with
  | none => exact SimC.pure hs rfl
  | some (lvls, pins) =>
  dsimp only
  have hpinsF : ∀ p ∈ pins, p.hasFvar = false :=
    nestedRuleShape_pins hshape
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cvt p' hs₁ hP => ?_)
  obtain ⟨rfl, hthm⟩ := hP
  try dsimp only
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ q q' hs₂ hQ => ?_)
  obtain ⟨rfl, hopen⟩ := hQ
  obtain ⟨fvs, tbody⟩ := q
  dsimp only
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen (Expr.WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      Expr.WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : Expr.WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : Expr.WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      Expr.WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
  by_cases h2 : isEqHead tbody.getAppFn = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : tbody.getAppArgs.length = 3
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  try dsimp only
  by_cases h4 : ((tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (f cvName) (lps.map .param)) = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  by_cases h5 : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length =
      mI + 1
  case neg => simp only [if_neg h5]; exact SimC.throw_bind
  simp only [if_pos h5]
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP == fvs.take rP) = true
  case neg => simp only [if_neg h6]; exact SimC.throw_bind
  simp only [if_pos h6]
  by_cases h7 : (((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0))
      == (Expr.mkAppN (.const (f r.ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP))) = true
  case neg => simp only [if_neg h7]; exact SimC.throw_bind
  simp only [if_pos h7]
  refine SimC.bind (SimC.unwrapOr' hs₂)
    (fun s₂b q8 q8' hs₂b hQ8 => ?_)
  obtain ⟨rfl, hstrip8⟩ := hQ8
  obtain ⟨bs8, cbody8⟩ := q8
  dsimp only
  split
  case isFalse => exact SimC.throw_bind
  refine SimC.bind (SimC.unwrapOr' hs₂b) (fun s₃ q2 q2' hs₃ hQ2 => ?_)
  obtain ⟨rfl, hcinst⟩ := hQ2
  obtain ⟨cdoms, cres⟩ := q2
  dsimp only
  have hcargW : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
      fvs.drop rP, Expr.WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hax
      exact instSpine_WScoped (rP - 1)
        (Expr.WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hpinsF x hx))
        (fun a' ha' => hfvsW a' (List.mem_of_mem_take ha'))
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst
    (Expr.WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts, Expr.hasFvar_instantiateLevelParams]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
  case neg => simp only [if_neg h9]; exact SimC.throw_bind
  simp only [if_pos h9]
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => hlargsW a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      (fun b hb => Expr.WScoped.getAppArgs hcresW b
        (List.mem_of_mem_drop hb)) hs₃)
    (fun s₄ u1 u1' hs₄ hU1 => ?_)
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_drop hx)))
      (fun b hb => hcdomsW b (List.mem_of_mem_drop hb)) hs₄)
    (fun s₅ u2 u2' hs₅ hU2 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ q3 q3' hs₆ hQ3 => ?_)
  obtain ⟨rfl, hrinst⟩ := hQ3
  obtain ⟨rdoms, rrest⟩ := q3
  dsimp only
  have hrinstW := instPisAt_WScoped _ _ hrinst
    (Expr.WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact htyA))
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
  obtain ⟨hrdomsW, -⟩ := hrinstW
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_take hx)))
      (fun b hb => hrdomsW b hb) hs₆)
    (fun s₇ u3 u3' hs₇ hU3 => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₇) (fun s₈ q4 q4' hs₈ hQ4 => ?_)
  obtain ⟨rfl, hopenP⟩ := hQ4
  obtain ⟨fvsP, restP⟩ := q4
  dsimp only
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP
    (Expr.WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  refine SimC.bind (checkAnnotListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact (instSpine_WScoped (rP - 1)
          (Expr.WScoped.of_not_hasFvar (hpinsF x hx))
          (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha'))).mono
          (by omega)) hs₈)
    (fun s₈b uA uA' hs₈b hUA => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₈b) (fun s₉ q5 q5' hs₉ hQ5 => ?_)
  obtain ⟨rfl, hcinstP⟩ := hQ5
  obtain ⟨cdomsP, crestP⟩ := q5
  dsimp only
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP
    (Expr.WScoped.of_not_hasFvar (by
      rw [Expr.hasFvar_instantiateLevelParams]
      exact hctor))
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact instSpine_WScoped (rP - 1)
        (Expr.WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha')))
  obtain ⟨hcdomsPW, hcrestPW⟩ := hcinstPW
  refine SimC.bind (checkTypedListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact (instSpine_WScoped (rP - 1)
          (Expr.WScoped.of_not_hasFvar (hpinsF x hx))
          (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha'))).mono
          (by omega))
      (fun b hb => (hcdomsPW b hb).mono (by omega)) hs₉)
    (fun s₉b uP uP' hs₉b hUP => ?_)
  refine SimC.bind (SimC.unwrapOr' hs₉b) (fun s10 q6 q6' hs10 hQ6 => ?_)
  obtain ⟨rfl, hopenX⟩ := hQ6
  obtain ⟨xFvsP, crest2⟩ := q6
  dsimp only
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP hopenX hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, Expr.WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact Expr.WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  by_cases harX : (crest2.getAppArgs.length == cnP + (mI - rP)) = true
  case neg => simp only [if_neg harX]; exact SimC.throw_bind
  simp only [if_pos harX]
  refine SimC.bind (SimC.unwrapOr' hs10) (fun s11 q7 q7' hs11 hQ7 => ?_)
  obtain ⟨rfl, hlinst⟩ := hQ7
  obtain ⟨ldoms, lrest⟩ := q7
  dsimp only
  have hlinstW := instLamsAt_WScoped _ _ hlinst
    (Expr.WScoped.of_not_hasFvar hrhsA) hfvsPW'
  obtain ⟨hldomsW, -⟩ := hlinstW
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hfvsPW' x hx))
      (fun b hb => hldomsW b hb) hs11)
    (fun s12 u4 u4' hs12 hU4 => ?_)
  refine SimC.bind (opB_sim hμ henv hs12 hrhsSW
      (Expr.WScoped.mkAppN
        (Expr.WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hrhsA))
        (fun x hx => hfvsW x hx)))
    (fun s13 c c' hs13 hC => ?_)
  obtain rfl : c = c' := hC
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    refine SimC.bind (checkIotaSidesTyS_sim hμ henv
        (WScoped_getD' htargsW 0) hlhsW hrhsSW hs13)
      (fun s14 u u' hs14 hU => ?_)
    exact SimC.pure hs14 rfl

/-- One modeled recursor rule at the cached shared operations. -/
theorem checkIotaRuleS_sim (hμ : mode.verifiedChecks = true) {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    (htyA : tyA.hasFvar = false) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkIotaRule mode (sharedOpsC mode (mkFEnv env)) env' env f cvName lps
        tyA mI rP j r)
      (checkIotaRule mode (fueledOpsM mode) env' env f cvName lps tyA mI rP j r) := by
  unfold checkIotaRule
  dsimp only [sharedOpsC]
  match hf : env'.find? r.ctor with
  | none => exact SimC.throw
  | some (.axiomInfo _) => exact SimC.throw
  | some (.projInfo _) => exact SimC.throw
  | some (.defnInfo _ _ _) => exact SimC.throw
  | some (.thmInfo _ _) => exact SimC.throw
  | some (.indInfo _ _) => exact SimC.throw
  | some (.recInfo _ _ _ _) => exact SimC.throw
  | some (.ctorInfo cvj cnP cnF) =>
  dsimp only
  by_cases h2 : r.nfields = cnF
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : Expr.looseBVarsBounded 0 (RecRule.rhs r) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : (RecRule.rhs r).hasFvar = true
  · simp only [if_pos h4]; exact SimC.throw_bind
  simp only [if_neg h4]
  refine SimC.bind (opE_annotate_sim hμ henv hs
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h4)))
    (fun s₁ rhsA rhsA' hs₁ hP => ?_)
  obtain ⟨rfl, hwrhsA⟩ := hP
  have hrhsAF : rhsA.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero hwrhsA.fvarsBelow
  by_cases h5 : Expr.allLevelParamsDefined lps rhsA = true
  case neg => simp only [if_neg h5]; exact SimC.throw_bind
  simp only [if_pos h5]
  by_cases h6 : Expr.constsResolve env rhsA = true
  case neg => simp only [if_neg h6]; exact SimC.throw_bind
  simp only [if_pos h6]
  by_cases h7 : (rhsA.stripLams (rP + cnF)).isSome = true
  case neg => simp only [if_neg h7]; exact SimC.throw_bind
  simp only [if_pos h7]
  refine SimC.bind (opE_infer_sim hμ henv hs₁ hwrhsA)
    (fun s₂ rhsTy rhsTy' hs₂ hP₂ => ?_)
  have hctorF : cvj.type.hasFvar = false := (henv' _ (find?_mem hf)).1
  by_cases h8 : Expr.recRulePlain tyA mI rP cnP = true
  case neg =>
    simp only [if_neg h8]
    refine SimC.bind (checkIotaThmNS_sim hμ henv' henv htyA hctorF
        hrhsAF hs₂)
      (fun s₃ fire fire' hs₃ hP₃ => ?_)
    obtain rfl : fire = fire' := hP₃
    exact SimC.pure hs₃ rfl
  simp only [if_pos h8]
  refine SimC.bind (checkIotaThmS_sim hμ henv' henv htyA hctorF hrhsAF hs₂)
    (fun s₃ u u' hs₃ hP₃ => ?_)
  first
  | exact SimC.pure hs₃ rfl
  | exact SimC.bind_pure_left (SimC.bind_pure_right (SimC.pure hs₃ rfl))

/-- The rule fold at the cached shared operations. -/
theorem checkIotaRulesS_sim (hμ : mode.verifiedChecks = true) {env' : Env} (henv' : EnvWF env')
    (henv : EnvWF env) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP : Nat}
    (htyA : tyA.hasFvar = false) :
    ∀ {j : Nat} {rules : List RecRule} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkIotaRules mode (sharedOpsC mode (mkFEnv env)) env' env f cvName lps
          tyA mI rP j rules)
        (checkIotaRules mode (fueledOpsM mode) env' env f cvName lps tyA
          mI rP j rules)
  | _, [], s₀, hs => SimC.pure hs rfl
  | j, r :: rest, s₀, hs => by
    unfold checkIotaRules
    refine SimC.bind (checkIotaRuleS_sim hμ henv' henv htyA hs)
      (fun s₁ r' r'' hs₁ hP => ?_)
    obtain rfl : r' = r'' := hP
    refine SimC.bind (checkIotaRulesS_sim hμ henv' henv htyA hs₁)
      (fun s₂ rest' rest'' hs₂ hP₂ => ?_)
    obtain rfl : rest' = rest'' := hP₂
    exact SimC.pure hs₂ rfl

/-- The member-against-model check at the cached shared operations; the
returned constant's type is well-scoped. -/
theorem checkMemberValS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {blockNames : List Name}
    {cv : ConstantVal} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ Expr.WScoped 0 v.type)
      (checkMemberVal (sharedOpsC mode (mkFEnv env)) blockNames env cv)
      (checkMemberVal (fueledOpsM mode) blockNames env cv) := by
  unfold checkMemberVal
  refine SimC.bind (checkConstantValS_sim hμ henv hs)
    (fun s₁ cvA cvA' hs₁ hP => ?_)
  obtain ⟨rfl, hwty⟩ := hP
  by_cases h1 : cvA.name.isModelSuffix = true
  · simp only [if_pos h1]; exact SimC.throw_bind
  simp only [if_neg h1]
  match hm : env.find? (cvA.name.str "_model") with
  | none => exact SimC.throw
  | some (.axiomInfo _) => exact SimC.throw
  | some (.projInfo _) => exact SimC.throw
  | some (.thmInfo _ _) => exact SimC.throw
  | some (.indInfo _ _) => exact SimC.throw
  | some (.ctorInfo _ _ _) => exact SimC.throw
  | some (.recInfo _ _ _ _) => exact SimC.throw
  | some (.defnInfo cvm mval mhint) =>
  dsimp only
  by_cases h2 : cvm.levelParams = cvA.levelParams
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : ((cvA.type.renameConsts
      (fun n => if blockNames.contains n then n.str "_model" else n))
      == cvm.type) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  exact SimC.pure hs₁ ⟨rfl, hwty⟩

/-- The projection-rule stage at the cached shared operations. -/
theorem checkProjRuleS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {pty : Expr}
    {cvj : ConstantVal} {lps : List Name} {nP nF i : Nat}
    (hptyf : pty.hasFvar = false)
    (hCf : cvj.type.hasFvar = false)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkProjRule (sharedOpsC mode (mkFEnv env)) env pty cvj lps nP nF i)
      (checkProjRule (fueledOpsM mode) env pty cvj lps nP nF i) := by
  unfold checkProjRule
  dsimp only [sharedOpsC]
  match hrhs : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => exact SimC.throw
  | some rhs =>
  dsimp only
  by_cases h1 : (!rhs.hasFvar && Expr.looseBVarsBounded 0 rhs) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  have hrf : rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.1
  refine SimC.bind (opE_annotate_sim hμ henv hs
      (Expr.WScoped.of_not_hasFvar hrf))
    (fun s₁ rhsA rhsA' hs₁ hP => ?_)
  obtain ⟨rfl, hwrhsA⟩ := hP
  by_cases h2 : (Expr.allLevelParamsDefined lps rhsA &&
      Expr.constsResolve env rhsA && Expr.looseBVarsBounded 0 rhsA &&
      !rhsA.hasFvar) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  match hstrip : rhsA.stripLams (nP + nF) with
  | none => exact SimC.throw
  | some (rbinders, rrbody) =>
  dsimp only
  by_cases h3 : (rrbody == Expr.bvar (nF - 1 - i)) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  match hstripC : cvj.type.stripPis (nP + nF) with
  | none => exact SimC.throw
  | some (cbindersR, cbodyR) =>
  dsimp only
  by_cases h4 : domsMatchAux (fun _ e => e) rbinders cbindersR 0 0
      (nP + nF) = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  match hopenP : openPisAtFvars nP pty 0 with
  | none => exact SimC.throw
  | some (fvsP, rest0) =>
  dsimp only
  match hcinstP : Expr.instPisAt fvsP cvj.type with
  | none => exact SimC.throw
  | some (cdomsP, crestP) =>
  dsimp only
  obtain ⟨hfvsW0, -⟩ := openPisAtFvars_WScoped nP pty 0 hopenP
    (Expr.WScoped.of_not_hasFvar hptyf)
  have hfvsW : ∀ x ∈ fvsP, Expr.WScoped nP x := by
    intro x hx
    have h0 := hfvsW0 x hx
    rwa [Nat.zero_add] at h0
  obtain ⟨hcdW, hcrW⟩ := instPisAt_WScoped (d := nP) fvsP cvj.type
    hcinstP (Expr.WScoped.of_not_hasFvar hCf) hfvsW
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped ((hfvsW x hx).mono (by omega)))
      (fun b hb => (hcdW b hb).mono (by omega)) hs₁)
    (fun s₂ u1 u1' hs₂ hU1 => ?_)
  match hopenX : openPisAtFvars nF crestP nP with
  | none => exact SimC.throw
  | some (xFvs, crest2X) =>
  dsimp only
  match hlinst : Expr.instLamsAt (fvsP ++ xFvs) rhsA with
  | none => exact SimC.throw
  | some (ldoms, lrestL) =>
  dsimp only
  have hrhsAf : rhsA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h2
    exact h2.2
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped nF crestP nP hopenX hcrW
  have hspineW : ∀ a ∈ fvsP ++ xFvs, Expr.WScoped (nP + nF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsW a ha).mono (by omega)
    · exact hxW a ha
  obtain ⟨hldW, -⟩ := instLamsAt_WScoped (fvsP ++ xFvs) rhsA hlinst
    (Expr.WScoped.of_not_hasFvar hrhsAf) hspineW
  refine SimC.bind (checkDefEqListS_sim hμ henv
      (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact fvarTypeD_WScoped (hspineW x hx))
      (fun b hb => hldW b hb) hs₂)
    (fun s₃ u2 u2' hs₃ hU2 => ?_)
  refine SimC.bind (opE_infer_sim hμ henv hs₃
      (Expr.WScoped.of_not_hasFvar hrhsAf))
    (fun s₄ t t' hs₄ hP₄ => ?_)
  exact SimC.pure hs₄ rfl

/-- `checkProjLookups` (operation-free) as a `SimC`. -/
theorem checkProjLookupsS_sim {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkProjLookups env' T ctorName lps nP nF i : CheckCM _)
      (checkProjLookups env' T ctorName lps nP nF i : FueledM _) := by
  unfold checkProjLookups
  match h1 : env'.find? ctorName with
  | none => exact SimC.throw
  | some (.axiomInfo _) => exact SimC.throw
  | some (.projInfo _) => exact SimC.throw
  | some (.thmInfo _ _) => exact SimC.throw
  | some (.indInfo _ _) => exact SimC.throw
  | some (.defnInfo _ _ _) => exact SimC.throw
  | some (.recInfo _ _ _ _) => exact SimC.throw
  | some (.ctorInfo cvj cnP cnF) =>
  dsimp only
  by_cases h2 : cnP = nP ∧ cnF = nF
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  match h3 : env'.find? (projModelName T i) with
  | none => exact SimC.throw
  | some (.axiomInfo _) => exact SimC.throw
  | some (.projInfo _) => exact SimC.throw
  | some (.thmInfo _ _) => exact SimC.throw
  | some (.indInfo _ _) => exact SimC.throw
  | some (.ctorInfo _ _ _) => exact SimC.throw
  | some (.recInfo _ _ _ _) => exact SimC.throw
  | some (.defnInfo mcv _ _) =>
  dsimp only
  by_cases h4 : mcv.levelParams = lps
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  by_cases h5 : (env'.find? (projFnName T i)).isNone = true
  case neg => simp only [if_neg h5]; exact SimC.throw_bind
  simp only [if_pos h5]
  by_cases h6 : (env'.find? T).isSome = true
  case neg => simp only [if_neg h6]; exact SimC.throw_bind
  simp only [if_pos h6]
  by_cases h7 : env'.find? eqName = some eqA
  case neg => simp only [if_neg h7]; exact SimC.throw_bind
  simp only [if_pos h7]
  exact SimC.pure hs rfl

/-- `checkProjTy` (operation-free) as a `SimC`. -/
theorem checkProjTyS_sim {env' : Env} {T ctorName : Name}
    {lps : List Name} {mty : Expr} {nP nF : Nat} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkProjTy env' T ctorName lps mty nP nF : CheckCM _)
      (checkProjTy env' T ctorName lps mty nP nF : FueledM _) := by
  unfold checkProjTy
  dsimp only
  by_cases h1 : ((mty.renameConsts (projBack T ctorName nF)).renameConsts
      (projFwd T ctorName nF) == mty) = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  by_cases h2 : Expr.constsResolve env'
      (mty.renameConsts (projBack T ctorName nF)) = true
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  by_cases h3 : (Expr.looseBVarsBounded 0
      (mty.renameConsts (projBack T ctorName nF)) &&
      !(mty.renameConsts (projBack T ctorName nF)).hasFvar &&
      Expr.allLevelParamsDefined lps
        (mty.renameConsts (projBack T ctorName nF))) = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : ((mty.renameConsts
      (projBack T ctorName nF)).stripPis (nP + 1)).isSome = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  exact SimC.pure hs rfl

/-- `checkProjShape` (operation-free) as a `SimC`. -/
theorem checkProjShapeS_sim {pty cty : Expr} {nP nF : Nat}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkProjShape pty cty nP nF : CheckCM _)
      (checkProjShape pty cty nP nF : FueledM _) := by
  unfold checkProjShape
  match h1 : pty.stripPis nP with
  | none => exact SimC.throw
  | some (abinders, arest) => ?_
  dsimp only
  match h2 : cty.stripPis (nP + nF) with
  | none => exact SimC.throw
  | some (cbindersR, cbody) => ?_
  dsimp only
  by_cases h4 : (cbody.getAppArgs.length == nP) = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  match h5 : cbody.getAppFn with
  | .const _ _ => exact SimC.pure hs rfl
  | .bvar _ => exact SimC.throw
  | .fvar _ _ => exact SimC.throw
  | .sort _ => exact SimC.throw
  | .app _ _ => exact SimC.throw
  | .lam _ _ _ => exact SimC.throw
  | .forallE _ _ _ => exact SimC.throw
  | .letE _ _ _ => exact SimC.throw
  | .lit _ => exact SimC.throw
  | .proj _ _ _ => exact SimC.throw

/-- `checkProjIota` at the cached shared operations (task #100 stage 3:
the side certificates make it consult the ops at the opened statement
telescope). -/
theorem checkProjIotaS_sim (hμ : mode.verifiedChecks = true) {T ctorName : Name}
    (henv : EnvWF env)
    {lps : List Name} {cvj : ConstantVal} {nP nF i : Nat}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkProjIota mode (sharedOpsC mode (mkFEnv env)) env env T ctorName lps
        cvj nP nF i)
      (checkProjIota mode (fueledOpsM mode) env env T ctorName lps cvj nP nF
        i) := by
  unfold checkProjIota
  match h1 : env.find? ((projModelName T i).str "iota") with
  | none => exact SimC.throw
  | some (.axiomInfo _) => exact SimC.throw
  | some (.projInfo _) => exact SimC.throw
  | some (.defnInfo _ _ _) => exact SimC.throw
  | some (.indInfo _ _) => exact SimC.throw
  | some (.ctorInfo _ _ _) => exact SimC.throw
  | some (.recInfo _ _ _ _) => exact SimC.throw
  | some (.thmInfo tcv _) =>
  dsimp only
  by_cases h2 : tcv.levelParams = lps
  case neg => simp only [if_neg h2]; exact SimC.throw_bind
  simp only [if_pos h2]
  match h3 : tcv.type.stripPis (nP + nF) with
  | none => exact SimC.throw
  | some (sbinders, sbody) =>
  dsimp only
  match h4 : cvj.type.stripPis (nP + nF) with
  | none => exact SimC.throw
  | some (cbindersR, _) =>
  dsimp only
  by_cases h5 : domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) = true
  case neg => simp only [if_neg h5]; exact SimC.throw_bind
  simp only [if_pos h5]
  cases sbody with
  | app f3 rhsC =>
    cases f3 with
    | app f2 lhsC =>
      cases f2 with
      | app f1 tySlot =>
        cases f1 with
        | const c ls =>
          cases ls with
          | nil => exact SimC.throw
          | cons ℓ ls' =>
            cases ls' with
            | cons _ _ => exact SimC.throw
            | nil =>
              dsimp only
              by_cases h6 : c = eqName
              case neg => simp only [if_neg h6]; exact SimC.throw_bind
              simp only [if_pos h6]
              by_cases h7 : (lhsC == Expr.mkAppN
                  (.const (projModelName T i) (lps.map .param))
                  (((List.range nP).map fun k =>
                    Expr.bvar (nP + nF - 1 - k)) ++
                   [Expr.mkAppN (.const (ctorName.str "_model")
                     (cvj.levelParams.map .param))
                     ((((List.range nP).map fun k =>
                       Expr.bvar (nP + nF - 1 - k)) ++
                      (List.range nF).map fun k =>
                        Expr.bvar (nF - 1 - k)))])) = true
              case neg => simp only [if_neg h7]; exact SimC.throw_bind
              simp only [if_pos h7]
              by_cases h8 : (rhsC == Expr.bvar (nF - 1 - i)) = true
              case neg => simp only [if_neg h8]; exact SimC.throw_bind
              simp only [if_pos h8]
              refine SimC.bind (SimC.unwrapOr' hs)
                (fun s10 q q' hs10 hQ => ?_)
              obtain ⟨rfl, hopen⟩ := hQ
              obtain ⟨fvsO, sbodyO⟩ := q
              dsimp only
              have hcvtF : tcv.type.hasFvar = false :=
                (henv _ (find?_mem h1)).1
              have hopenW := openPisAtFvars_WScoped (nP + nF)
                tcv.type 0 hopen (Expr.WScoped.of_not_hasFvar hcvtF)
              rw [Nat.zero_add] at hopenW
              obtain ⟨-, htbodyW⟩ := hopenW
              have htargsW : ∀ x ∈ sbodyO.getAppArgs,
                  Expr.WScoped (nP + nF) x :=
                Expr.WScoped.getAppArgs htbodyW
              exact checkIotaSidesTyS_sim hμ henv
                (WScoped_getD' htargsW 0) (WScoped_getD' htargsW 1)
                (WScoped_getD' htargsW 2) hs10
        | _ => exact SimC.throw
      | _ => exact SimC.throw
    | _ => exact SimC.throw
  | _ => exact SimC.throw

end Walks2

end ConLeche.Cached
