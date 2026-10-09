import Ix.CompileCert.Pj.ConstructorSteps
import IxC.Kernel.Inductives.SumInstall
import IxC.Kernel.Verify.Inductives.SumInv
import IxC.Kernel.Verify.Inductives.FixInv
import IxC.Kernel.Verify.InstLevels

/-!
Stored-header facts from the kernel's actual inductive installation stages.

`checkSumInd` and `checkSumCtor` are the former/constructor stages used by
the native installer. Their exported inversions describe the STORED types,
after the telescope WHNF/recheck and constructor normalization branches.
The lemmas below use those accepted runs to establish the Pj header read
and minor-result arity, also at arbitrary universe instantiations.

This does not restrict the final theorem to this installer route. The
modeled/nested route and source/export correspondence remain obligations.
In particular, matching the motive's dependent domains to the stored
former is retained explicitly; no equality of declared and normalized
types, no new caller arity law, and no annotation erasure is assumed.
This additive source has not been elaborated or audited.
-/

namespace Ix.CompileCert.Pj.InstalledHeader

/-- A complete stored sort telescope is accepted by the actual header
parser, at the supplied parameter split. All domain expressions and outer
binder metadata are retained in the returned take/drop views. -/
theorem readType_of_stripSort {np ni : Nat} {e : Kernel.Expr}
    {bs : Telescope} {s : Kernel.Level}
    (stripped : e.stripPis (np + ni) = some (bs, .sort s)) :
    readType np e = some ⟨bs.take np, bs.drop np, s⟩ ∧
      (bs.take np).length = np ∧ (bs.drop np).length = ni := by
  obtain ⟨shape, length⟩ := piJoin_of_stripPis (np + ni) e bs (.sort s) stripped
  have parameterLength : (bs.take np).length = np := by
    rw [List.length_take, length]
    omega
  have indexLength : (bs.drop np).length = ni := by
    rw [List.length_drop, length]
    omega
  have splitShape : e = piJoin (bs.take np) (piJoin (bs.drop np) (.sort s)) := by
    rw [← piJoin_append, List.take_append_drop]
    exact shape
  refine ⟨?_, parameterLength, indexLength⟩
  calc
    readType np e = readType (bs.take np).length
        (piJoin (bs.take np) (piJoin (bs.drop np) (.sort s))) := by
          rw [parameterLength, splitShape]
    _ = some ⟨bs.take np, bs.drop np, s⟩ := readType_piJoin _ _ _

/-- Kernel level instantiation preserves the complete stored telescope and
its sort end. This obtains the instantiated binders from the actual parser;
their annotations are substituted by the kernel, never copied unchanged. -/
theorem stripSort_instantiate {k : Nat} {e : Kernel.Expr}
    {bs : Telescope} {s : Kernel.Level}
    (stripped : e.stripPis k = some (bs, .sort s))
    (ks : List Kernel.Name) (us : List Kernel.Level) :
    ∃ bs', (e.instantiateLevelParams ks us).stripPis k =
      some (bs', .sort (Kernel.Level.subst ks us s)) := by
  have available : ((e.instantiateLevelParams ks us).stripPis k).isSome = true :=
    Kernel.Expr.stripPis_instantiateLevelParams_isSome ks us k
      (by simp only [stripped, Option.isSome_some])
  cases parsed : (e.instantiateLevelParams ks us).stripPis k with
  | none => simp only [parsed, Option.isSome_none, Bool.false_eq_true] at available
  | some result =>
    obtain ⟨bs', body⟩ := result
    have bodyEq := (Kernel.Expr.stripPis_instantiateLevelParams_eq ks us k
      stripped parsed).1
    have sortEq : body = .sort (Kernel.Level.subst ks us s) := by
      simpa only [Kernel.Expr.instantiateLevelParams] using bodyEq
    exact ⟨bs', by rw [← sortEq]; exact parsed⟩

/-- The actual installed-inductive lookup and a stored sort telescope
guarantee reader success at every correctly sized universe instance. No
scope, uniqueness or semantic-equality-from-hash premise is needed. -/
theorem read_of_stored_sort {env : Kernel.Env} {m : MotiveRd}
    {cv : Kernel.ConstantVal} {caps : Kernel.IndCaps} {np ni : Nat}
    {bs : Telescope} {s : Kernel.Level}
    (lookup : env.find? m.ind = some (.indInfo cv caps))
    (arity : m.indUs.length = cv.levelParams.length)
    (stripped : cv.type.stripPis (np + ni) = some (bs, .sort s)) :
    ∃ h, read env np m = some h ∧ h.parameters.length = np ∧ h.indices.length = ni := by
  obtain ⟨bs', parsed⟩ := stripSort_instantiate stripped cv.levelParams m.indUs
  obtain ⟨header, parameters, indices⟩ := readType_of_stripSort parsed
  refine ⟨⟨bs'.take np, bs'.drop np, Kernel.Level.subst cv.levelParams m.indUs s⟩,
    ?_, parameters, indices⟩
  simpa only [read, lookup, ite_eq_left arity] using header

/-- On a successful read, the index count is the count from the actual
stored former telescope, even after arbitrary universe substitution. -/
theorem read_index_count_of_stored_sort {env : Kernel.Env} {m : MotiveRd}
    {cv : Kernel.ConstantVal} {caps : Kernel.IndCaps} {np ni : Nat}
    {bs : Telescope} {s : Kernel.Level} {h : Header}
    (lookup : env.find? m.ind = some (.indInfo cv caps))
    (stripped : cv.type.stripPis (np + ni) = some (bs, .sort s))
    (accepted : read env np m = some h) : h.indices.length = ni := by
  by_cases arity : m.indUs.length = cv.levelParams.length
  · obtain ⟨actual, parsed, _, length⟩ := read_of_stored_sort lookup arity stripped
    have same : actual = h := Option.some.inj (parsed.symm.trans accepted)
    simpa only [same] using length
  · simp only [read, lookup, ite_eq_right arity, reduceCtorEq] at accepted

/-- A successful real former-install stage establishes the Pj header read
in the environment it returns. Both the declared telescope branch and the
WHNF/recheck branch are covered by `checkSumInd_shape`. The motive's other
fields are irrelevant to `read`; their domain match is a separate issue. -/
theorem read_of_checkSumInd {mode : Kernel.CheckMode} {fuel : Nat}
    {before installed : Kernel.Env} {p completed : Kernel.InductiveShape}
    {cv : Kernel.ConstantVal} {capsOf : Kernel.InductiveShape → Kernel.IndCaps}
    (accepted : Kernel.checkSumInd (Kernel.fueledOps mode fuel) before p capsOf =
      .ok (installed, cv, completed))
    (m : MotiveRd) (name : m.ind = cv.name)
    (arity : m.indUs.length = cv.levelParams.length) :
    ∃ h, read installed p.nP m = some h ∧
      h.parameters.length = p.nP ∧ h.indices.length = p.nIdx := by
  obtain ⟨_original, _sort, _, _, _, _, environment, _bs, stripped⟩ :=
    Kernel.checkSumInd_shape accepted
  have lookup : installed.find? m.ind = some (.indInfo cv (capsOf completed)) := by
    rw [environment, name]
    simp only [Kernel.Env.find?, List.find?_cons, Kernel.ConstantInfo.name,
      Kernel.ConstantInfo.toConstantVal, beq_self_eq_true, ↓reduceIte]
  exact read_of_stored_sort lookup arity stripped

/-- The former-header reader succeeds on the actual former environment
returned by a complete native pass, at the original parameter/index split.
The accepted pass supplies the former stage; the caller does not supply a
literal source telescope or a separate successful header read. -/
theorem read_of_checkNativePass {mode : Kernel.CheckMode} {fuel : Nat}
    {before : Kernel.Env} {p : Kernel.NativeParts} {isRec settled : Bool}
    {q : Kernel.NativePass Kernel.Env}
    (accepted : Kernel.checkNativePass (Kernel.fueledOps mode fuel) before p isRec =
      .ok (q, settled))
    (m : MotiveRd) (name : m.ind = q.cvTa.name)
    (arity : m.indUs.length = q.cvTa.levelParams.length) :
    ∃ h, read q.env₁ p.nP m = some h ∧
      h.parameters.length = p.nP ∧ h.indices.length = p.nIdx := by
  obtain ⟨_completed, _kinds, former, _, _, _, _⟩ := Kernel.checkNativePass_inv accepted
  exact read_of_checkSumInd former m name arity

/-- The constructor stage's residual count transfers through the actual
universe instantiation and the existing full CtorOk reconstruction. In
particular, the result-index count is NOT an additional reader premise. -/
theorem minor_result_count_of_checkSumCtor
    {mode : Kernel.CheckMode} {fuel : Nat}
    {before checkerEnv storedEnv : Kernel.Env} {T : Kernel.Name}
    {lps : List Kernel.Name} {np ni nf : Nat} {sort : Kernel.Level}
    {isProp large : Bool} {cvC cvT cvCa : Kernel.ConstantVal}
    {sorts : List Kernel.Level}
    (accepted : Kernel.checkSumCtor (Kernel.fueledOps mode fuel) before checkerEnv
      T lps np ni sort isProp large cvC nf cvT = .ok (cvCa, sorts))
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (lookup : storedEnv.find? n.ctor = some (.ctorInfo cvCa np nf))
    (checked : n.CtorOk storedEnv parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length) :
    n.resIdx.length = ni := by
  obtain ⟨bs, indices, raw, indexLength⟩ := (Kernel.checkSumCtor_shape accepted).2.1
  have data := checked
  simp only [MinorRd.CtorOk, lookup] at data
  obtain ⟨parameterCount, fieldCount, _, typeEq⟩ := data
  have rebuilt : (cvCa.type.instantiateLevelParams cvCa.levelParams n.ctorUs).stripPis
      (np + nf) = some (constructorBinders parameters motives n,
        constructorResult parameters.length motives n) := by
    rw [typeEq, parameterCount, fieldCount]
    exact strip_constructorType parameters motives n metadata
  have body := (Kernel.Expr.stripPis_instantiateLevelParams_eq
    cvCa.levelParams n.ctorUs (np + nf) raw rebuilt).1
  have lengths := congrArg (fun e : Kernel.Expr => e.getAppArgs.length) body
  have total : parameters.length + n.resIdx.length = np + ni := by
    simpa only [constructorResult, Kernel.Expr.getAppArgs_instantiateLevelParams,
      Kernel.Expr.getAppArgs_mkAppN, Kernel.Expr.getAppArgs, List.nil_append,
      List.length_map, List.length_append, bvarsAt, Kernel.structPsAt,
      List.length_range, indexLength] using lengths
  rw [parameterCount] at total
  exact Nat.add_left_cancel total

/-- Every positional constructor returned by the actual ordered stage has
the required residual index count. The source and stored entries are joined
at the SAME position; no successful-entry filter or reordered subset is
used. This is the per-position consequence of `checkSumCtors_inv`. -/
theorem minor_result_count_of_checkSumCtors
    {mode : Kernel.CheckMode} {fuel : Nat}
    {before checkerEnv storedEnv : Kernel.Env} {T : Kernel.Name}
    {lps : List Kernel.Name} {np ni : Nat} {sort : Kernel.Level}
    {isProp large : Bool} {cvT : Kernel.ConstantVal}
    {cs ctorsA : List (Kernel.ConstantVal × Nat)} {sortss : List (List Kernel.Level)}
    (accepted : Kernel.checkSumCtors (Kernel.fueledOps mode fuel) before checkerEnv
      T lps np ni sort isProp large cvT cs = .ok (ctorsA, sortss))
    (j : Nat) (c cA : Kernel.ConstantVal × Nat)
    (sourceAt : cs[j]? = some c) (storedAt : ctorsA[j]? = some cA)
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (lookup : storedEnv.find? n.ctor = some (.ctorInfo cA.1 np cA.2))
    (checked : n.CtorOk storedEnv parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length) :
    n.resIdx.length = ni := by
  obtain ⟨fields, _sorts, _, constructor⟩ :=
    (Kernel.checkSumCtors_inv accepted).2.2 j c cA sourceAt storedAt
  have joined : storedEnv.find? n.ctor = some (.ctorInfo cA.1 np c.2) := by
    simpa only [fields] using lookup
  exact minor_result_count_of_checkSumCtor constructor parameters motives n joined checked metadata

/-- The existing kernel former/constructor stages discharge the complete
minor-result check once the remaining motive-domain match is known. The
major bound, constructor reconstruction and metadata come from the existing
RecRd.Check, not new final caller laws. Actual output lookups join the stage
records to the environment in which the recursor was read. -/
theorem RecRd.minor_header_of_kernel_stages
    {mode : Kernel.CheckMode} {fuel : Nat}
    {env before installed ctorBefore ctorEnv : Kernel.Env}
    {r : Kernel.Name} {R : Ix.CompileCert.Pj.RecRd}
    (checked : R.Check env r) (n : MinorRd) (present : n ∈ R.minors)
    {p completed : Kernel.InductiveShape} {cvT cvC cvCa : Kernel.ConstantVal}
    {capsOf : Kernel.InductiveShape → Kernel.IndCaps}
    {caps : Kernel.IndCaps} {nf : Nat} {sorts : List Kernel.Level}
    (former : Kernel.checkSumInd (Kernel.fueledOps mode fuel) before p capsOf =
      .ok (installed, cvT, completed))
    (constructor : Kernel.checkSumCtor (Kernel.fueledOps mode fuel) ctorBefore ctorEnv
      p.cvT.name p.cvT.levelParams p.nP p.nIdx completed.resSort completed.isProp
      completed.large cvC nf cvT = .ok (cvCa, sorts))
    (formerLookup : env.find? (R.motives.getD n.motive default).ind =
      some (.indInfo cvT caps))
    (constructorLookup : env.find? n.ctor = some (.ctorInfo cvCa p.nP nf))
    {h : Header}
    (matched : matchMotive env R.params (R.motives.getD n.motive default) = some h) :
    checkMinorResult env R.params R.motives n = true := by
  have minor := checked.2.2.2.2 n present
  have bound : n.motive < R.motives.length := minor.1
  have metadata : n.paramMetas.length = R.params.length := minor.2.1
  have ctorOk := minor.2.2.2.2.2
  have ctorData := ctorOk
  simp only [MinorRd.CtorOk, constructorLookup] at ctorData
  have parameterCount : p.nP = R.params.length := ctorData.1
  have resultCount := minor_result_count_of_checkSumCtor constructor
    R.params R.motives n constructorLookup ctorOk metadata
  obtain ⟨_original, sort, _, _, _, _, _, bs, rawFormer⟩ :=
    Kernel.checkSumInd_shape former
  have storedFormer : cvT.type.stripPis (R.params.length + p.nIdx) =
      some (bs, .sort sort) := by
    simpa only [parameterCount] using rawFormer
  have headerCount := read_index_count_of_stored_sort formerLookup storedFormer
    (matchMotive_sound matched).1
  have residual := readConstructorResidual_of_CtorOk R.params R.motives n ctorOk metadata
  have prefixLength : (bvarsAt R.params.length n.fields.length).length = R.params.length := by
    simp only [bvarsAt, List.length_map, List.length_range]
  have suffix : n.resIdx.length = h.indices.length := resultCount.trans headerCount.symm
  have shape : (constructorResult R.params.length R.motives n).getAppFn =
        .const (R.motives.getD n.motive default).ind
          (R.motives.getD n.motive default).indUs ∧
      (constructorResult R.params.length R.motives n).getAppArgs.take R.params.length =
        bvarsAt R.params.length n.fields.length ∧
      (constructorResult R.params.length R.motives n).getAppArgs.length =
        R.params.length + h.indices.length := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [constructorResult, Kernel.Expr.getAppFn_mkAppN, Kernel.Expr.getAppFn]
    · simpa only [constructorResult, Kernel.Expr.getAppArgs_mkAppN,
        Kernel.Expr.getAppArgs, List.nil_append] using
          (List.take_left' (l₂ := n.resIdx) prefixLength)
    · simp only [constructorResult, Kernel.Expr.getAppArgs_mkAppN,
        Kernel.Expr.getAppArgs, List.nil_append, List.length_append, prefixLength, suffix]
  simpa only [checkMinorResult, ite_eq_left bound, matched, residual, decide_eq_true_eq]
    using shape

end Ix.CompileCert.Pj.InstalledHeader

#print axioms Ix.CompileCert.Pj.InstalledHeader.readType_of_stripSort
#print axioms Ix.CompileCert.Pj.InstalledHeader.stripSort_instantiate
#print axioms Ix.CompileCert.Pj.InstalledHeader.read_of_stored_sort
#print axioms Ix.CompileCert.Pj.InstalledHeader.read_index_count_of_stored_sort
#print axioms Ix.CompileCert.Pj.InstalledHeader.read_of_checkSumInd
#print axioms Ix.CompileCert.Pj.InstalledHeader.read_of_checkNativePass
#print axioms Ix.CompileCert.Pj.InstalledHeader.minor_result_count_of_checkSumCtor
#print axioms Ix.CompileCert.Pj.InstalledHeader.minor_result_count_of_checkSumCtors
#print axioms Ix.CompileCert.Pj.InstalledHeader.RecRd.minor_header_of_kernel_stages
