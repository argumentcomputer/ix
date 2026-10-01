module

public import ConLeche.Kernel.CheckerSplit
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Mono

public section

/-!
# The two halves are `checkDecl` (task #253)

`installConstantVal`/`installValue` and `checkValueGroup`
(`ConLeche/Kernel/CheckerSplit.lean`) are the install and check halves
of the declaration checker at a separable value kind.  This module
inverts each half into the facts it establishes (`*_inv`), assembles
each from those facts (`*_of_facts`), carries them up in fuel
(`*_mono`), and — the point — assembles `checkDecl`'s own run from the
two halves (`checkDecl_of_split_*`): a properly installed group whose
check half succeeded was checked by `checkDecl`, which is what the
model's declaration step consumes.
-/

namespace ConLeche

variable {μ : CheckMode} {F : Nat} {env : Env}
variable {pins : List NatOpPinSet}

/-! ## The install half -/

theorem installConstantVal_inv {cv cvA : ConstantVal}
    (h : installConstantVal (fueledOps μ F) env cv = .ok cvA) :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type',
      annotateCore μ env F 0 cv.type = .ok type' ∧
      type'.allLevelParamsDefined cv.levelParams = true ∧
      type'.constsResolve env = true ∧
      cvA = { cv with type := type' } := by
  simp only [installConstantVal, fueledOps_annotate, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  case pos =>
    rw [if_pos hres] at h
    exact nomatch h
  simp only [hres] at h
  by_cases hpshape : cv.name.isProjFnShape = true
  case pos =>
    rw [if_pos hpshape] at h
    exact nomatch h
  rw [if_neg hpshape] at h
  have hpshapeF : cv.name.isProjFnShape = false := by
    revert hpshape; cases cv.name.isProjFnShape <;> simp
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => simp [hnd] at h
  simp only [hnd] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : cv.type.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  cases hann : annotateCore μ env F 0 cv.type with
  | error e => rw [hann] at h; exact nomatch h
  | ok type =>
  rw [hann] at h
  try dsimp only at h
  by_cases htp : type.allLevelParamsDefined cv.levelParams = true
  case neg => simp [htp] at h
  simp only [htp] at h
  by_cases htr : type.constsResolve env = true
  case neg => simp [htr] at h
  simp only [htr] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  have hfind0 : env.find? cv.name = none := by
    revert hfind
    cases env.find? cv.name <;> simp
  exact ⟨hfind0, by simpa using hres, hpshapeF, hnd, hlb,
    by simpa using hif, type, rfl, htp, htr, h.symm⟩

theorem installConstantVal_of_facts {cv : ConstantVal} {type' : Expr}
    (hfind : env.find? cv.name = none)
    (hres : reservedBasisNames.contains cv.name = false)
    (hshape : cv.name.isProjFnShape = false)
    (hnd : Name.nodup cv.levelParams = true)
    (hlb : cv.type.looseBVarsBounded 0 = true)
    (hif : cv.type.hasFvar = false)
    (hann : annotateCore μ env F 0 cv.type = .ok type')
    (htp : type'.allLevelParamsDefined cv.levelParams = true)
    (htr : type'.constsResolve env = true) :
    installConstantVal (fueledOps μ F) env cv = .ok { cv with type := type' } := by
  simp only [installConstantVal, fueledOps_annotate, Bind.bind, Except.bind,
    Pure.pure, Except.pure, hfind, hres, hshape, hnd, hlb, hif, hann, htp, htr,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

theorem installValue_inv {cv : ConstantVal} {value jv : Expr}
    (h : installValue (fueledOps μ F) env cv value = .ok jv) :
    value.looseBVarsBounded 0 = true ∧
    value.hasFvar = false ∧
    annotateCore μ env F 0 value = .ok jv ∧
    jv.allLevelParamsDefined cv.levelParams = true ∧
    jv.constsResolve env = true := by
  simp only [installValue, fueledOps_annotate, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at h
  by_cases hlb : value.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : value.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  cases hann : annotateCore μ env F 0 value with
  | error e => rw [hann] at h; exact nomatch h
  | ok v =>
  rw [hann] at h
  try dsimp only at h
  by_cases hvp : v.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : v.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  subst h
  exact ⟨hlb, by simpa using hif, rfl, hvp, hvr⟩

theorem installValue_of_facts {cv : ConstantVal} {value jv : Expr}
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hann : annotateCore μ env F 0 value = .ok jv)
    (hvp : jv.allLevelParamsDefined cv.levelParams = true)
    (hvr : jv.constsResolve env = true) :
    installValue (fueledOps μ F) env cv value = .ok jv := by
  simp only [installValue, fueledOps_annotate, Bind.bind, Except.bind,
    Pure.pure, Except.pure, hlb, hif, hann, hvp, hvr, Bool.false_eq_true, ↓reduceIte]

/-! ## The check half -/

theorem checkValueGroup_inv {vg : ValueGroup}
    (h : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    ∃ stype u,
      inferTypeCore μ env F 0 vg.cvA.type = .ok stype ∧
      ensureSortCore μ env F 0 stype = .ok u ∧
      (vg.kind = .thm → Level.isEquiv u .zero = some true) ∧
      ∃ jv,
        (vg.kind = .thm → installValue (fueledOps μ F) env vg.cvA vg.jv = .ok jv) ∧
        (vg.kind ≠ .thm → jv = vg.jv) ∧
        ∃ vtype,
          inferTypeCore μ env F 0 jv = .ok vtype ∧
          isDefEqCore μ env F 0 vtype vg.cvA.type = .ok true := by
  simp only [checkValueGroup, fueledOps_inferType, fueledOps_ensureSort,
    fueledOps_isDefEq, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hst : inferTypeCore μ env F 0 vg.cvA.type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSortCore μ env F 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  try dsimp only at h
  -- the theorem test and the theorem's value install, then the value's
  -- typing
  by_cases hk : vg.kind = .thm
  · rw [if_pos hk] at h
    cases heqv : Level.isEquiv u .zero with
    | none => rw [heqv] at h; simp [liftFueled] at h
    | some b =>
    rw [heqv] at h
    simp only [liftFueled, Pure.pure, Except.pure] at h
    cases b with
    | false => simp at h
    | true =>
    simp only [↓reduceIte] at h
    cases hiv : installValue (fueledOps μ F) env vg.cvA vg.jv with
    | error e => rw [hiv] at h; exact nomatch h
    | ok jv =>
    rw [hiv] at h
    try dsimp only at h
    cases hvt : inferTypeCore μ env F 0 jv with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore μ env F 0 vtype vg.cvA.type with
    | error e => rw [hde] at h; exact nomatch h
    | ok r =>
    rw [hde] at h
    cases r with
    | false => simp at h
    | true => exact ⟨stype, u, rfl, hsort, fun _ => heqv, jv, fun _ => rfl,
        fun hk' => absurd hk hk', vtype, hvt, hde⟩
  · rw [if_neg hk] at h
    cases hvt : inferTypeCore μ env F 0 vg.jv with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore μ env F 0 vtype vg.cvA.type with
    | error e => rw [hde] at h; exact nomatch h
    | ok r =>
    rw [hde] at h
    cases r with
    | false => simp at h
    | true => exact ⟨stype, u, rfl, hsort, fun hk' => absurd hk' hk, vg.jv,
        fun hk' => absurd hk' hk, fun _ => rfl, vtype, hvt, hde⟩

theorem checkValueGroup_of_facts {vg : ValueGroup} {jv stype vtype : Expr} {u : Level}
    (hst : inferTypeCore μ env F 0 vg.cvA.type = .ok stype)
    (hsort : ensureSortCore μ env F 0 stype = .ok u)
    (hthm : vg.kind = .thm → Level.isEquiv u .zero = some true)
    (hjv : vg.kind = .thm → installValue (fueledOps μ F) env vg.cvA vg.jv = .ok jv)
    (hjv' : vg.kind ≠ .thm → jv = vg.jv)
    (hvt : inferTypeCore μ env F 0 jv = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype vg.cvA.type = .ok true) :
    checkValueGroup (fueledOps μ F) env vg = .ok () := by
  simp only [checkValueGroup, fueledOps_inferType, fueledOps_ensureSort,
    fueledOps_isDefEq, Bind.bind, Except.bind, Pure.pure, Except.pure, hst, hsort]
  by_cases hk : vg.kind = .thm
  · simp only [if_pos hk, liftFueled, hthm hk, Pure.pure, Except.pure, ↓reduceIte, hjv hk,
      hvt, hde]
  · obtain rfl := hjv' hk
    simp only [if_neg hk, hvt, hde, ↓reduceIte]

/-! ## Fuel -/

theorem installConstantVal_mono {F' : Nat} (hle : F ≤ F') {cv cvA : ConstantVal}
    (h : installConstantVal (fueledOps μ F) env cv = .ok cvA) :
    installConstantVal (fueledOps μ F') env cv = .ok cvA := by
  obtain ⟨hfind, hres, hshape, hnd, hlb, hif, type', hann, htp, htr, rfl⟩ :=
    installConstantVal_inv h
  exact installConstantVal_of_facts hfind hres hshape hnd hlb hif
    (annotateCore_mono hle hann) htp htr

theorem installValue_mono {F' : Nat} (hle : F ≤ F') {cv : ConstantVal} {value jv : Expr}
    (h : installValue (fueledOps μ F) env cv value = .ok jv) :
    installValue (fueledOps μ F') env cv value = .ok jv := by
  obtain ⟨hlb, hif, hann, hvp, hvr⟩ := installValue_inv h
  exact installValue_of_facts hlb hif (annotateCore_mono hle hann) hvp hvr

theorem checkValueGroup_mono {F' : Nat} (hle : F ≤ F') {vg : ValueGroup}
    (h : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    checkValueGroup (fueledOps μ F') env vg = .ok () := by
  obtain ⟨stype, u, hst, hsort, hthm, jv, hiv, hjv', vtype, hvt, hde⟩ := checkValueGroup_inv h
  exact checkValueGroup_of_facts (inferTypeCore_mono hle hst) (ensureSortCore_mono hle hsort)
    hthm (fun hk => installValue_mono hle (hiv hk)) hjv' (inferTypeCore_mono hle hvt)
    (isDefEqCore_mono hle hde)

/-! ## `checkDecl` from the two halves -/

theorem checkConstantVal_of_facts {cv : ConstantVal} {type' stype : Expr} {u : Level}
    (hfind : env.find? cv.name = none)
    (hres : reservedBasisNames.contains cv.name = false)
    (hshape : cv.name.isProjFnShape = false)
    (hnd : Name.nodup cv.levelParams = true)
    (hlb : cv.type.looseBVarsBounded 0 = true)
    (hif : cv.type.hasFvar = false)
    (hann : annotateCore μ env F 0 cv.type = .ok type')
    (htp : type'.allLevelParamsDefined cv.levelParams = true)
    (htr : type'.constsResolve env = true)
    (hst : inferTypeCore μ env F 0 type' = .ok stype)
    (hsort : ensureSortCore μ env F 0 stype = .ok u) :
    checkConstantVal (fueledOps μ F) env cv = .ok { cv with type := type' } := by
  simp only [checkConstantVal, fueledOps_annotate, fueledOps_inferType,
    fueledOps_ensureSort, Bind.bind, Except.bind, Pure.pure, Except.pure, hfind, hres,
    hshape, hnd, hlb, hif, hann, htp, htr, hst, hsort, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte]

theorem checkDefnVal_of_facts {cv : ConstantVal} {value jv vtype : Expr}
    {hint : ReducibilityHint}
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hann : annotateCore μ env F 0 value = .ok jv)
    (hvp : jv.allLevelParamsDefined cv.levelParams = true)
    (hvr : jv.constsResolve env = true)
    (hvt : inferTypeCore μ env F 0 jv = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype cv.type = .ok true) :
    checkDefnVal (fueledOps μ F) env cv value hint = .ok ⟨.defnInfo cv jv hint :: env.consts⟩ := by
  simp only [checkDefnVal, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    Bind.bind, Except.bind, Pure.pure, Except.pure, hlb, hif, hann, hvp, hvr, hvt, hde,
    Bool.false_eq_true, ↓reduceIte]

theorem checkThmVal_of_facts {cv : ConstantVal} {value jv vtype stype : Expr} {u : Level}
    (hst : inferTypeCore μ env F 0 cv.type = .ok stype)
    (hsort : ensureSortCore μ env F 0 stype = .ok u)
    (heqv : Level.isEquiv u .zero = some true)
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hann : annotateCore μ env F 0 value = .ok jv)
    (hvp : jv.allLevelParamsDefined cv.levelParams = true)
    (hvr : jv.constsResolve env = true)
    (hvt : inferTypeCore μ env F 0 jv = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype cv.type = .ok true) :
    checkThmVal (fueledOps μ F) env cv value = .ok ⟨.thmInfo cv value :: env.consts⟩ := by
  simp only [checkThmVal, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, liftFueled, Bind.bind, Except.bind, Pure.pure, Except.pure, hst,
    hsort, heqv, hlb, hif, hann, hvp, hvr, hvt, hde, Bool.false_eq_true, ↓reduceIte]

theorem checkOpaqueVal_of_facts {cv : ConstantVal} {value jv vtype : Expr}
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hann : annotateCore μ env F 0 value = .ok jv)
    (hvp : jv.allLevelParamsDefined cv.levelParams = true)
    (hvr : jv.constsResolve env = true)
    (hvt : inferTypeCore μ env F 0 jv = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype cv.type = .ok true) :
    checkOpaqueVal (fueledOps μ F) env cv value = .ok ⟨.axiomInfo cv :: env.consts⟩ := by
  simp only [checkOpaqueVal, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    Bind.bind, Except.bind, Pure.pure, Except.pure, hlb, hif, hann, hvp, hvr, hvt, hde,
    Bool.false_eq_true, ↓reduceIte]

/-- **A definition's two halves are `checkDecl`.** -/
theorem checkDecl_of_split_defn {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint} {vg : ValueGroup}
    (hnat : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = false)
    (hk : vg.kind = .defn)
    (hI : installConstantVal (fueledOps μ F) env cv = .ok vg.cvA)
    (hV : installValue (fueledOps μ F) env vg.cvA value = .ok vg.jv)
    (hC : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    checkDecl μ (fueledOps μ F) pins env (.defnDecl cv value hint)
      = .ok ⟨.defnInfo vg.cvA vg.jv hint :: env.consts⟩ := by
  obtain ⟨hfind, hres, hshape, hnd, hlb, hif, type', hann, htp, htr, hcvA⟩ :=
    installConstantVal_inv hI
  obtain ⟨hlbv, hivf, hannv, hvp, hvr⟩ := installValue_inv hV
  obtain ⟨stype, u, hst, hsort, -, jv, -, hjv', vtype, hvt, hde⟩ := checkValueGroup_inv hC
  obtain rfl : jv = vg.jv := hjv' (by rw [hk]; decide)
  obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hnat
  rw [hcvA] at hst hvp hde ⊢
  have hcc := checkConstantVal_of_facts hfind hres hshape hnd hlb hif hann htp htr hst hsort
  have hdv := checkDefnVal_of_facts (cv := { cv with type := type' }) (hint := hint)
    hlbv hivf hannv hvp hvr hvt hde
  simp only [checkDecl, Bind.bind, Except.bind, Pure.pure, Except.pure, hcc, hdv, h1, h2,
    Bool.false_eq_true, ↓reduceIte]

/-- **A theorem's two halves are `checkDecl`**: the header's install
half, and the check half holding the RAW value (which it annotates
itself). -/
theorem checkDecl_of_split_thm {cv : ConstantVal} {value : Expr} {vg : ValueGroup}
    (hk : vg.kind = .thm)
    (hI : installConstantVal (fueledOps μ F) env cv = .ok vg.cvA)
    (hjv : vg.jv = value)
    (hC : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    checkDecl μ (fueledOps μ F) pins env (.thmDecl cv value)
      = .ok ⟨.thmInfo vg.cvA value :: env.consts⟩ := by
  obtain ⟨hfind, hres, hshape, hnd, hlb, hif, type', hann, htp, htr, hcvA⟩ :=
    installConstantVal_inv hI
  obtain ⟨stype, u, hst, hsort, hthm, jv, hiv, -, vtype, hvt, hde⟩ := checkValueGroup_inv hC
  have hV := hiv hk
  rw [hjv] at hV
  obtain ⟨hlbv, hivf, hannv, hvp, hvr⟩ := installValue_inv hV
  rw [hcvA] at hst hvp hde ⊢
  have hcc := checkConstantVal_of_facts hfind hres hshape hnd hlb hif hann htp htr hst hsort
  have htv := checkThmVal_of_facts (cv := { cv with type := type' }) hst hsort (hthm hk)
    hlbv hivf hannv hvp hvr hvt hde
  simp only [checkDecl, Bind.bind, Except.bind, hcc, htv]

/-- **An opaque's two halves are `checkDecl`.** -/
theorem checkDecl_of_split_opaque {cv : ConstantVal} {value : Expr} {vg : ValueGroup}
    (hred : reduceOpNames.contains cv.name = false)
    (hk : vg.kind = .opaque)
    (hI : installConstantVal (fueledOps μ F) env cv = .ok vg.cvA)
    (hV : installValue (fueledOps μ F) env vg.cvA value = .ok vg.jv)
    (hC : checkValueGroup (fueledOps μ F) env vg = .ok ()) :
    checkDecl μ (fueledOps μ F) pins env (.opaqueDecl cv value)
      = .ok ⟨.axiomInfo vg.cvA :: env.consts⟩ := by
  obtain ⟨hfind, hres, hshape, hnd, hlb, hif, type', hann, htp, htr, hcvA⟩ :=
    installConstantVal_inv hI
  obtain ⟨hlbv, hivf, hannv, hvp, hvr⟩ := installValue_inv hV
  obtain ⟨stype, u, hst, hsort, -, jv, -, hjv', vtype, hvt, hde⟩ := checkValueGroup_inv hC
  obtain rfl : jv = vg.jv := hjv' (by rw [hk]; decide)
  rw [hcvA] at hst hvp hde ⊢
  have hcc := checkConstantVal_of_facts hfind hres hshape hnd hlb hif hann htp htr hst hsort
  have hov := checkOpaqueVal_of_facts (cv := { cv with type := type' })
    hlbv hivf hannv hvp hvr hvt hde
  simp only [checkDecl, Bind.bind, Except.bind, Pure.pure, Except.pure, hcc, hov, hred,
    Bool.false_eq_true, ↓reduceIte]

end ConLeche
