module

public import ConLeche.Verify.Inductives.SumWF
public import ConLeche.Verify.Inductives.FixInv

public section

/-!
# The direct recursive install: environment well-formedness (task #188)

`EnvWF` for the recursor stage of `checkNative`: the recursor's
cons with its rules, each rule's right-hand side scoped by
`checkNativeRules` at the environment holding the recursor's
constant (the rules mention the recursor) — which finds exactly the
names the stored cons finds.  The former's and the constructors'
stages are the sum route's (`SumWF.lean`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- The generators' constructor list is one entry per constructor
when the kinds are one list per constructor. -/
theorem nativeCtors4_length {ctorsA : List (ConstantVal × Nat)}
    {kinds : List (List RecFieldKind)} (h : ctorsA.length = kinds.length) :
    (nativeCtors4 ctorsA kinds).length = ctorsA.length := by
  simp [nativeCtors4, List.length_zipWith, h]

/-- The recursor stage's stored pieces, as its own guards checked
them; the rules resolve at the environment holding the recursor's
(rule-less) cons. -/
theorem checkNativeRec_facts {env : Env} {p : NativeParts}
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {F : Nat}
    (h : checkNativeRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
    (cvRa.type.hasFvar = false ∧
      cvRa.type.allLevelParamsDefined cvRa.levelParams = true ∧
      cvRa.type.constsResolve env = true ∧
      cvRa.type.looseBVarsBounded 0 = true) ∧
    rhss.length = (nativeCtors4 ctorsA p.kinds).length ∧
    ∀ rhs ∈ rhss, rhs.hasFvar = false ∧
      rhs.allLevelParamsDefined cvRa.levelParams = true ∧
      rhs.constsResolve ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩ = true ∧
      rhs.looseBVarsBounded 0 = true := by
  obtain ⟨cvRi, recTy, sty, u, -, -, hlp, hres, hbv, hfv, -, -, -, hrules, rfl⟩ :=
    checkNativeRec_shape h
  obtain ⟨hlen, hall⟩ := checkNativeRules_inv hrules
  refine ⟨rfl, rfl, ⟨hfv, hlp, hres, hbv⟩, hlen, ?_⟩
  intro rhs hrhs
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrhs
  have hi' : i < (nativeCtors4 ctorsA p.kinds).length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rhs', hget, -, hlp', hres', hbv', hfv'⟩ := hall i hi'
  obtain rfl := Option.some.inj (hi.symm.trans hget)
  exact ⟨hfv', hlp', hres', hbv'⟩

/-- Two conses of the same name find the same names. -/
theorem find?_isSome_cons_same {c c' : ConstantInfo} {env : Env} (hn : c.name = c'.name) :
    ∀ n, (Env.find? ⟨c :: env.consts⟩ n).isSome = true →
      (Env.find? ⟨c' :: env.consts⟩ n).isSome = true := by
  intro n h
  rw [Env.find?_cons] at h
  rw [Env.find?_cons, ← hn]
  split at h <;> split <;> simp_all

/-- Stage 3 at the run level: the recursor cons with its rules is
well-formed. -/
theorem direct_fix_rec_wf {env : Env} (henv : EnvWF env)
    {p : NativeParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {F : Nat}
    (h : checkNativeRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    EnvWF ⟨.recInfo cvRa p.majorIdx p.rulePrefix
      (sumRules env.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss) :: env.consts⟩ := by
  obtain ⟨-, -, ⟨htf, htp, htr, htb⟩, -, hall⟩ := checkNativeRec_facts h
  refine EnvWF.cons henv (structConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq) ?_)
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  obtain ⟨hmem, hfire⟩ := sumRules_mem hr
  obtain ⟨hrfv, hrlp, hrres, hrbv⟩ := hall r.rhs hmem
  refine ⟨hrfv, hrlp, Expr.constsResolve_of_find
    (find?_isSome_cons_same (c := .recInfo cvRa p.majorIdx p.rulePrefix [])
      (c' := .recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules env.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)) rfl) hrres, hrbv, ?_⟩
  intro lvls pins hf
  exact absurd hf (hfire lvls pins)

/-- The field-kinds guard, per constructor: the kind list has one
entry per field and the opened form passes the guard at the pre-block
environment. -/
theorem nativeFieldsOk_inv {env₀ : Env} {T : Name} {lps : List Name} {nP nIdx : Nat}
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List RecFieldKind)}
    (h : nativeFieldsOk env₀ T lps nP nIdx ctorsA kinds = true)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) :
    ∃ ks, kinds[j]? = some ks ∧ ks.length = cA.2 ∧
      nativeOpenedOk env₀ T lps nP nIdx cA.1.type cA.2 ks = true := by
  simp only [nativeFieldsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have := hall j hjl
  rw [hj] at this
  cases hk : kinds[j]? with
  | none => rw [hk] at this; exact nomatch this
  | some ks =>
    rw [hk] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨ks, rfl, this.1, this.2⟩


/-- **The fixpoint route's capability record names the parameter count
as its arity**: what `direct_sum_ind_wf` needs of `capsOf`
to establish `IndCapsWF` at the former's cons. -/
theorem nativeCapsAt_arity (p : InductiveShape) (isRec : Bool) :
    ((nativeCapsAt p isRec).unitlike = true → (nativeCapsAt p isRec).unitParams = p.nP) ∧
    ((nativeCapsAt p isRec).eta = true → (nativeCapsAt p isRec).etaParams = p.nP) := by
  unfold nativeCapsAt
  split
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- `nativeCapsAt_arity` at the classified verdict. -/
theorem nativeCaps_arity (p : NativeParts) :
    ((nativeCaps p).unitlike = true → (nativeCaps p).unitParams = p.nP) ∧
    ((nativeCaps p).eta = true → (nativeCaps p).etaParams = p.nP) :=
  nativeCapsAt_arity p.toInductiveShape (nativeIsRec p.kinds)

end ConLeche
