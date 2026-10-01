module

public import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Inductives.FixParts
import ConLeche.Kernel.Inductives.NativeInstall

public section

/-!
# The direct recursive install: inversion (task #188)

The shape of a successful run of the recursive route's recursor stage
(`checkNativeRec`, `ConLeche/Kernel/Inductives/NativeInstall.lean`), read off
the monad: the generated recursor type with the inductive-hypothesis
binders, its scoping and sort, the comparison with the stream's, and
the generated rules — each the generator's output, scoped at the
environment holding the recursor's constant and NOT inferred.  The
former's and the constructors' stages are the sum route's
(`SumInv.lean`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem fixThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The generated rules loop: `k` rules for constructors `j, j+1, …`,
each the generator's output at its position, scoped at `envR`. -/
theorem checkNativeRules_inv {envR : Env} {rlps : List Name} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat} {tty : Expr}
    {ctors : List (Name × Nat × Expr × List Nat)} {recC : Name} {rlvls : List Level} :
    ∀ {k j : Nat} {rhss : List Expr},
      checkNativeRules (m := CheckM) envR rlps T lps elim large nP nIdx tty ctors recC
        rlvls k j = .ok rhss →
      rhss.length = k ∧
      ∀ i, i < k → ∃ rhs, rhss[i]? = some rhs ∧
        structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls (j + i) = some rhs ∧
        rhs.allLevelParamsDefined rlps = true ∧ rhs.constsResolve envR = true ∧
        rhs.looseBVarsBounded 0 = true ∧ rhs.hasFvar = false
  | 0, _, rhss, h => by
    simp only [checkNativeRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, j, rhss, h => by
    unfold checkNativeRules at h
    obtain ⟨rhs, hrh, h⟩ := exceptBind_ok h
    have hrh' := unwrapOr_ok hrh
    try simp only at h
    by_cases h1 : (Expr.allLevelParamsDefined rlps rhs && Expr.constsResolve envR rhs &&
        Expr.looseBVarsBounded 0 rhs && !rhs.hasFvar) = true
    case neg =>
      rw [if_neg h1] at h
      exfalso
      first
        | exact fixThrow_ne_ok h
        | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
    rw [if_pos h1] at h
    try simp only at h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkNativeRules_inv hrest
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    cases i with
    | zero =>
      exact ⟨rhs, rfl, by rw [Nat.add_zero]; exact hrh', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
    | succ i =>
      obtain ⟨rhs', hget, hgen, hlp, hres, hbv, hfv⟩ := hall i (by omega)
      have hget' : (rhs :: rest)[i + 1]? = some rhs' := by simpa using hget
      have hgen' : structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls (j + (i + 1))
          = some rhs' := by
        rw [show j + (i + 1) = j + 1 + i from by omega]; exact hgen
      exact ⟨rhs', hget', hgen', hlp, hres, hbv, hfv⟩

/-- **The recursor record's pins** (task #220): a successful recursor
stage says the block's recursor record is NAMED the one official
generates (`T.rec`) and carries its level parameters — the block's own,
with the fresh elimination parameter in front at the large eliminator.
Before task #220 both were recogniser conjuncts, so a block whose
recursor record was a stub fell through to a DECLINE; they are now
install checks whose failure REJECTS (official's replay finds no such
generated recursor, or one that differs from it), and this is where the
P tier reads them off. -/
theorem checkNativeRec_pins {env : Env} {p : NativeParts}
    {cvTa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {r : ConstantVal × List Expr} {F : Nat}
    (h : checkNativeRec (fueledOps mode F) env p cvTa ctorsA = .ok r) :
    p.cvR.name = p.cvT.name.str "rec" ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    (∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams) := by
  unfold checkNativeRec at h
  by_cases hn : (p.cvR.name == p.cvT.name.str "rec") = true
  case neg =>
    exfalso
    rw [if_neg hn] at h
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  rw [if_pos hn] at h
  try simp only [bind, Except.bind] at h
  by_cases hlp : nativeRecLpsOk p.toInductiveShape = true
  case neg =>
    exfalso
    rw [if_neg hlp] at h
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  unfold nativeRecLpsOk at hlp
  refine ⟨beq_iff_eq.mp hn, ?_, ?_⟩
  · intro hL
    rw [if_pos hL] at hlp
    simp only [beq_iff_eq] at hlp
    rw [hlp]
    exact List.mem_cons_self
  · intro q hq
    by_cases hL : p.large = true
    · rw [if_pos hL] at hlp
      simp only [beq_iff_eq] at hlp
      rw [hlp]
      exact List.mem_cons_of_mem _ hq
    · rw [if_neg hL] at hlp
      simp only [beq_iff_eq] at hlp
      rw [hlp]
      exact hq

/-- The recursor stage's shape. -/
theorem checkNativeRec_shape {env : Env} {p : NativeParts}
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {F : Nat}
    (h : checkNativeRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    ∃ (cvRi : ConstantVal) (recTy sty : Expr) (u : Level),
      checkConstantVal (fueledOps mode F) env p.cvR = .ok cvRi ∧
      structRecTyR p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
        (nativeCtors4 ctorsA p.kinds) = some recTy ∧
      recTy.allLevelParamsDefined p.cvR.levelParams = true ∧
      recTy.constsResolve env = true ∧
      recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false ∧
      inferTypeCore mode env F 0 recTy = .ok sty ∧
      ensureSortCore mode env F 0 sty = .ok u ∧
      isDefEqCore mode env F 0 cvRi.type recTy = .ok true ∧
      checkNativeRules (m := CheckM)
        ⟨.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ p.majorIdx p.rulePrefix []
          :: env.consts⟩
        p.cvR.levelParams p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
        (nativeCtors4 ctorsA p.kinds) p.cvR.name (p.cvR.levelParams.map .param)
        (nativeCtors4 ctorsA p.kinds).length 0 = .ok rhss ∧
      cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := by
  unfold checkNativeRec at h
  -- the recursor pin (task #220): the name and the record's structure
  by_cases hn : (p.cvR.name == p.cvT.name.str "rec") = true
  case neg =>
    exfalso
    rw [if_neg hn] at h
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  rw [if_pos hn] at h
  try simp only [bind, Except.bind] at h
  by_cases hlp : nativeRecLpsOk p.toInductiveShape = true
  case neg =>
    exfalso
    rw [if_neg hlp] at h
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  rw [if_pos hlp] at h
  try simp only [bind, Except.bind] at h
  by_cases hpin : p.recPinned = true
  case neg =>
    exfalso
    rw [if_neg hpin] at h
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  rw [if_pos hpin] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨cvRi, hcv, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨recTy, hrt, h⟩ := exceptBind_ok h
  have hrt' := unwrapOr_ok hrt
  try simp only at h
  by_cases h1 : (Expr.allLevelParamsDefined p.cvR.levelParams recTy &&
      Expr.constsResolve env recTy && Expr.looseBVarsBounded 0 recTy &&
      !recTy.hasFvar) = true
  case neg =>
    rw [if_neg h1] at h
    exfalso
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  rw [if_pos h1] at h
  try simp only at h
  obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exfalso
    first
      | exact fixThrow_ne_ok h
      | exact fixThrow_ne_ok (by simpa [bind, Except.bind] using h)
  | true =>
  rw [if_pos rfl] at h
  try simp only at h
  obtain ⟨rhss', hrules, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
  exact ⟨cvRi, recTy, sty, u, hcv, hrt', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, hsty, hu, hb,
    hrules, rfl⟩

/-- The kinds' classification at install (task #210 Part D): the
recogniser's syntactic reading of the stored constructors, with no
non-positive and no unmodeled occurrence. -/
theorem classifyFixKinds_inv {T : Name} {lps : List Name} {nP nIdx : Nat}
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List RecFieldKind)}
    (h : classifyFixKinds (m := CheckM) T lps nP nIdx ctorsA = .ok kinds) :
    ctorsA.mapM (recCtorKinds T lps nP nIdx) = some kinds ∧
    kinds.any (fun ks => ks.any (· == .negative)) = false ∧
    kinds.any (fun ks => ks.any (· == .unsupported)) = false ∧
    kinds.length = ctorsA.length := by
  unfold classifyFixKinds at h
  cases hk : ctorsA.mapM (recCtorKinds T lps nP nIdx) with
  | none => rw [hk] at h; exact nomatch h
  | some ks =>
  rw [hk] at h
  simp only [unwrapOr, bind, Except.bind, pure, Except.pure] at h
  by_cases hneg : ks.any (fun ks => ks.any (· == .negative)) = true
  · rw [if_pos hneg] at h; exact nomatch h
  rw [if_neg hneg] at h
  by_cases hun : ks.any (fun ks => ks.any (· == .unsupported)) = true
  · rw [if_pos hun] at h; exact nomatch h
  rw [if_neg hun] at h
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨rfl, by simpa using hneg, by simpa using hun, List.mapM_option_length hk⟩

/-- **One pass's shape** (task #268): the former's run at the record
at the verdict `isRec`, the constructors' runs at the former's
environment (the resolution guard pointed at that same environment),
the kinds classified on the stored constructors, the record completed
with them, and the settling bit — the classified record against the
one the pass ran at. -/
theorem checkNativePass_inv {env : Env} {p₀ : NativeParts} {isRec : Bool}
    {q : NativePass Env} {b : Bool} {F : Nat}
    (h : checkNativePass (fueledOps mode F) env p₀ isRec = .ok (q, b)) :
    ∃ (p₁ : InductiveShape) (kinds : List (List RecFieldKind)),
      checkSumInd (fueledOps mode F) env p₀.toInductiveShape
        (fun p₁ => nativeCapsAt p₁ isRec) = .ok (q.env₁, q.cvTa, p₁) ∧
      checkSumCtors (fueledOps mode F) q.env₁ q.env₁ (p₀.complete p₁).cvT.name
        (p₀.complete p₁).cvT.levelParams (p₀.complete p₁).nP (p₀.complete p₁).nIdx
        (p₀.complete p₁).resSort (p₀.complete p₁).isProp (p₀.complete p₁).large q.cvTa
        (p₀.complete p₁).ctors = .ok (q.ctorsA, q.sortss) ∧
      classifyFixKinds (m := CheckM) (p₀.complete p₁).cvT.name (p₀.complete p₁).cvT.levelParams
        (p₀.complete p₁).nP (p₀.complete p₁).nIdx q.ctorsA = .ok kinds ∧
      q.p = (p₀.complete p₁).withKinds kinds ∧
      b = (nativeCaps q.p == nativeCapsAt p₁ isRec) := by
  unfold checkNativePass at h
  obtain ⟨r₁, hInd, h⟩ := exceptBind_ok h
  obtain ⟨env₁, cvTa, p₁⟩ := r₁
  try simp only at h
  obtain ⟨r₂, hCtors, h⟩ := exceptBind_ok h
  obtain ⟨ctorsA, sortss⟩ := r₂
  try simp only at h
  obtain ⟨kinds, hK, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨p₁, kinds, hInd, hCtors, hK, rfl, rfl⟩

end ConLeche
