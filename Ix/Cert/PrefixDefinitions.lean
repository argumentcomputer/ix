import Ix.Cert.PrefixCore

/-! # Actual origins of every stored prefix definition

The reference checker creates definition entries only at actual defnDecls.
All native, modeled, basis, quotient and projection paths are covered by
their real output shapes. This producer precedes the semantic row.
-/

namespace Ix.Cert.PrefixDefinitions

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.ReferenceFronts

universe w
variable {md : Mode}

def isDefinition : Ix.Kernel.ConstantInfo md → Bool
  | .defnInfo .. => true
  | _ => false

/-- A proof-only observation of the actual environment, retaining exact
annotated types, values and hints rather than just names or skeletons. -/
def definitions (env : Env md) : List (Ix.Kernel.ConstantInfo md) :=
  env.consts.filter isDefinition

@[simp] theorem definition_mem {env : Env md} {cv : Ix.Kernel.ConstantVal md}
    {value : Ix.Kernel.Expr md} {hint : ReducibilityHint} :
    .defnInfo cv value hint ∈ definitions env ↔ .defnInfo cv value hint ∈ env.consts := by
  simp [definitions, isDefinition]

theorem fold_definitions {α : Type} (step : Env md → α → CheckM md (Env md)) :
    ∀ (xs : List α) (env : Env md),
      (∀ e x, x ∈ xs → ExPost (step e x) (fun e' => definitions e' = definitions e)) →
      ExPost (xs.foldlM step env) (fun e' => definitions e' = definitions env) := by
  intro xs
  induction xs with
  | nil => intro env _; simp
  | cons x xs ih =>
    intro env each
    rw [List.foldlM_cons, ExPost.post_bind]
    exact ExPost.mono (fun mid first => ExPost.mono (fun last rest => rest.trans first)
      (ih mid fun e y hy => each e y (List.mem_cons_of_mem _ hy)))
      (each env x List.mem_cons_self)

theorem basis_definitions (env : Env md) (kind : BasisKind) :
    ExPost (checkBasisDecl env kind : CheckM md (Env md))
      (fun e => definitions e = definitions env) := by
  have pins : ∀ ci ∈ kind.declsA, isDefinition (md := md) ci = false := by
    have all : (kind.declsA (md := md)).all (fun ci => !isDefinition ci) = true := by
      cases kind <;> rfl
    intro ci member
    simpa using List.all_eq_true.mp all ci member
  have folded := fold_definitions (installBasisDecl (m := CheckM md)) kind.declsA env
    (fun e ci member => by simp [installBasisDecl, definitions, pins ci member])
  simpa only [checkBasisDecl, ExPost.post_bind, ExPost.post_ite, ExPost.post_throw,
    ExPost.post_pure, imp_true_iff, and_true] using And.intro (fun _ _ => folded) (fun _ => folded)

variable (mode : CheckMode) (ops : (CheckerOps md) (CheckM md))

theorem member_definitions (blockNames : List (Key md)) (caps : IndCaps md)
    (env : Env md) (ci : Ix.Kernel.ConstantInfo md) :
    ExPost (checkIndMember ops blockNames caps env ci) (fun e => definitions e = definitions env) := by
  unfold checkIndMember
  rw [ExPost.post_bind]
  apply ExPost.of_forall
  intro cvA
  cases ci <;> simp [definitions, isDefinition]

theorem recs_definitions (blockNames : List (Key md)) (env : Env md)
    (recs : List (Ix.Kernel.ConstantInfo md)) :
    ExPost (checkIndRecs mode ops blockNames env recs) (fun e => definitions e = definitions env) := by
  unfold checkIndRecs
  simp only [ExPost.post_ite, ExPost.post_pure, ExPost.post_throw, ExPost.post_bind,
    imp_true_iff, true_and, and_true]
  intro _ _
  apply ExPost.of_forall
  intro pair
  apply fold_definitions
  intro e c _
  simp [definitions, isDefinition]

theorem projection_definitions (env : Env md) (T ctor : Key md) (lps : List LevelParam)
    (nP nF i : Nat) :
    ExPost (checkProjFn mode ops env T ctor lps nP nF i) (fun e => definitions e = definitions env) := by
  simp [checkProjFn, definitions, isDefinition]

theorem projection_step_definitions (T ctor : Key md) (lps : List LevelParam)
    (nP nF : Nat) (env : Env md) (i : Nat) :
    ExPost (installProjFnStep mode ops T ctor lps nP nF env i)
      (fun e => definitions e = definitions env) := by
  unfold installProjFnStep
  split
  · exact projection_definitions mode ops env T ctor lps nP nF i
  · simp

theorem modeled_definitions (env : Env md) (block : List (Ix.Kernel.ConstantInfo md)) :
    ExPost (checkModeled mode ops env block) (fun e => definitions e = definitions env) := by
  unfold checkModeled
  simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true, ExPost.post_bind]
  intro _
  split
  · rename_i cvT caps cvC nP nF _ _
    simp only [ExPost.post_pure, ExPost.post_bind]
    refine ExPost.mono (fun mid first => ?_) (fold_definitions _ _ env
      (fun e ci _ => member_definitions ops _ _ e ci))
    refine ExPost.mono (fun mid' second => ?_) (recs_definitions mode ops _ mid _)
    simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, ExPost.post_pure,
      imp_true_iff, and_true]
    intro _ _
    refine ⟨fun _ => ?_, fun _ => second.trans first⟩
    exact ExPost.mono (fun _ last => last.trans (second.trans first))
      (fold_definitions _ _ mid' fun e i _ => projection_step_definitions mode ops _ _ _ _ _ e i)
  · simp only [ExPost.post_bind]
    refine ExPost.mono (fun mid first => ?_) (fold_definitions _ _ env
      (fun e ci _ => member_definitions ops _ _ e ci))
    exact ExPost.mono (fun _ second => second.trans first) (recs_definitions mode ops _ mid _)

theorem constructors_definitions (nP : Nat) (cs : List (Ix.Kernel.ConstantVal md × Nat)) (env : Env md) :
    definitions (consSumCtors nP cs env) = definitions env := by
  induction cs generalizing env with
  | nil => rfl
  | cons c cs ih => simpa [consSumCtors, definitions, isDefinition] using ih ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩

theorem native_table_definitions (p : NativeParts md) (ctors : List (Ix.Kernel.ConstantVal md × Nat))
    (sorts : List (List Ix.Kernel.Level)) (env : Env md) :
    ExPost (checkNativeTable p ctors sorts env : CheckM md (Env md))
      (fun e => definitions e = definitions env) := by
  unfold checkNativeTable
  split
  · split
    · refine ExPost.mono (fun e shape => ?_) (checkStructProjTable_post _ _ _ _ _ _ _ _ _ env)
      obtain ⟨tbl, _, rfl, _⟩ := shape
      rfl
    · simp
  · simp

theorem native_pass_definitions (env : Env md) (p : NativeParts md) (isRec : Bool) :
    ExPost (checkNativePass ops env p isRec) (fun r => definitions r.1.env₁ = definitions env) := by
  unfold checkNativePass
  rw [ExPost.post_bind]
  refine ExPost.mono (fun r shape => ?_) (checkSumInd_post env p.toInductiveShape _)
  obtain ⟨mid, cvA, pA⟩ := r
  dsimp only at shape ⊢
  obtain ⟨rfl, _⟩ := shape
  simp [definitions, isDefinition]

theorem native_tail_definitions (env : Env md) (q : NativePass md (Env md)) :
    ExPost (checkNativeTail ops env q) (fun e => definitions e = definitions q.env₁) := by
  unfold checkNativeTail
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, true_and, imp_true_iff]
  intro _
  refine ExPost.of_forall fun _ => ExPost.of_forall fun _ =>
    ⟨fun _ => ⟨fun _ => ?_, trivial⟩, trivial⟩
  apply ExPost.of_forall
  intro result
  exact ExPost.mono (fun e preserved => preserved.trans (by
    simpa only [definitions, List.filter_cons, isDefinition, Bool.false_eq_true, ↓reduceIte] using
      constructors_definitions q.p.nP q.ctorsA q.env₁))
    (native_table_definitions _ _ _ _)

/-- Both settled paths return the tail of a pass run from the original
environment. A discarded first attempt contributes no stored definitions. -/
theorem native_definitions (env : Env md) (p : NativeParts md) :
    ExPost (checkNative ops env p) (fun e => definitions e = definitions env) := by
  unfold checkNative
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
  intro _
  refine ExPost.mono (fun result first => ?_) (native_pass_definitions ops env p _)
  obtain ⟨q, settled⟩ := result
  cases settled with
  | true => simpa using ExPost.mono (fun _ last => last.trans first) (native_tail_definitions ops env q)
  | false =>
    have follow : ExPost (checkNativePass ops env p (nativeIsRec q.p.kinds))
        (fun result => result.2 = true → ExPost (checkNativeTail ops env result.1)
          (fun e => definitions e = definitions env)) := by
      refine ExPost.mono (fun result second _ => ?_) (native_pass_definitions ops env p _)
      exact ExPost.mono (fun _ last => last.trans second) (native_tail_definitions ops env result.1)
    simpa using follow

/-- Every actual non-definition arm preserves the exact definition entries. -/
theorem checkDecl_definitions (ev : Evidences md) (env : Env md) (d : Declaration md)
    (nondef : ∀ cv value hint, d ≠ .defnDecl cv value hint) :
    ExPost (checkDecl mode ops ev env d) (fun e => definitions e = definitions env) := by
  cases d with
  | defnDecl cv value hint => exact (nondef cv value hint rfl).elim
  | thmDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    exact ExPost.of_forall fun cvA => ExPost.mono
      (fun e ⟨v, shape⟩ => by rw [shape]; rfl) (checkThmVal_post env cvA value)
  | opaqueDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    exact ExPost.of_forall fun cvA => ExPost.mono
      (fun e shape => by rw [shape]; rfl) (checkOpaqueVal_post env cvA value)
  | axiomDecl cv => simp [checkDecl, definitions, isDefinition]
  | basisDecl kind => exact basis_definitions env kind
  | indDecl block nP =>
    unfold checkDecl
    rw [ExPost.post_bind]
    apply ExPost.of_forall
    intro _
    split
    · exact basis_definitions env _
    · simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
      intro _
      split
      · exact native_definitions ops env _
      · exact modeled_definitions mode ops env block
  | quotDecl k cv =>
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
    intro _
    cases k <;> first | exact basis_definitions env .quotK | simp

/-- One real step either retained the exact entry or created it by an
actual definition check, with the original raw header and value fronts. -/
theorem step_definition_origin {ev : Evidences md} {env after : Env md} {d : Declaration md}
    {F : Nat} {cv : Ix.Kernel.ConstantVal md} {value : Ix.Kernel.Expr md} {hint : ReducibilityHint}
    (run : checkDecl .verified (fueledOps .verified F) ev env d = .ok after)
    (member : .defnInfo cv value hint ∈ after.consts) :
    .defnInfo cv value hint ∈ env.consts ∨ ∃ rawCv raw,
      d = .defnDecl rawCv raw hint ∧ rawCv.name = cv.name ∧ rawCv.levelParams = cv.levelParams ∧
      ConstantValRun .verified F env rawCv cv.type ∧ ValueFrontRun .verified F env rawCv raw cv.type value ∧
      after = ⟨.defnInfo cv value hint :: env.consts⟩ := by
  cases d with
  | defnDecl rawCv raw rawHint =>
    obtain ⟨T, checked, header, front, shape, _, _⟩ := declDefnRun_of run
    rw [shape, List.mem_cons] at member
    rcases member with same | old
    · obtain ⟨rfl, rfl, rfl⟩ := Ix.Kernel.ConstantInfo.defnInfo.inj same
      exact Or.inr ⟨rawCv, raw, rfl, rfl, rfl, header, front, shape⟩
    · exact Or.inl old
  | _ =>
    have same := checkDecl_definitions .verified (fueledOps .verified F) ev env _
      (by intros; simp) after run
    exact Or.inl (definition_mem.mp (same ▸ definition_mem.mpr member))

/-- The actual fold retains a complete split around the creating step.
An arbitrary initial environment is allowed internally; the public origin
starts at empty, so no unaccounted initial definition can escape. -/
theorem fold_definition_origin {ev : Evidences md} {F : Nat}
    {xs : List (Declaration md)} {initial final : Env md}
    {cv : Ix.Kernel.ConstantVal md} {value : Ix.Kernel.Expr md} {hint : ReducibilityHint}
    (run : xs.foldlM (checkDecl .verified (fueledOps .verified F) ev) initial = .ok final)
    (member : .defnInfo cv value hint ∈ final.consts) :
    .defnInfo cv value hint ∈ initial.consts ∨ ∃ pre rawCv raw post origin,
      xs = pre ++ .defnDecl rawCv raw hint :: post ∧
      pre.foldlM (checkDecl .verified (fueledOps .verified F) ev) initial = .ok origin ∧
      checkDecl .verified (fueledOps .verified F) ev origin (.defnDecl rawCv raw hint) =
        .ok ⟨.defnInfo cv value hint :: origin.consts⟩ ∧
      post.foldlM (checkDecl .verified (fueledOps .verified F) ev)
        ⟨.defnInfo cv value hint :: origin.consts⟩ = .ok final ∧
      rawCv.name = cv.name ∧ rawCv.levelParams = cv.levelParams ∧
      ConstantValRun .verified F origin rawCv cv.type ∧
      ValueFrontRun .verified F origin rawCv raw cv.type value := by
  induction xs generalizing initial with
  | nil => cases run; exact Or.inl member
  | cons d xs ih =>
    rw [List.foldlM_cons] at run
    cases first : checkDecl .verified (fueledOps .verified F) ev initial d with
    | error err => rw [first] at run; exact nomatch run
    | ok middle =>
      rw [first] at run
      rcases ih run with old | ⟨pre, rawCv, raw, post, origin, split, pref, step, suff, names, levels, header, front⟩
      · rcases step_definition_origin first old with old | ⟨rawCv, raw, rfl, names, levels, header, front, shape⟩
        · exact Or.inl old
        · exact Or.inr ⟨[], rawCv, raw, xs, initial, rfl, rfl, shape ▸ first, shape ▸ run,
            names, levels, header, front⟩
      · refine Or.inr ⟨d :: pre, rawCv, raw, post, origin, by rw [split]; rfl,
          ?_, step, suff, names, levels, header, front⟩
        rw [List.foldlM_cons, first]
        exact pref

/-- EVERY stored definition member has an actual creating declaration
index and exact annotated front. Generated model definitions are included;
native/modeled/basis/projection paths cannot create an untraced definition. -/
theorem reference_stored_definition_origin
    {ev : Evidences md} {xs : List (Declaration md)} {env : Env md}
    (accepted : Cached.AcceptsRef .verified ev xs env)
    {cv : Ix.Kernel.ConstantVal md} {value : Ix.Kernel.Expr md} {hint : ReducibilityHint}
    (stored : .defnInfo cv value hint ∈ env.consts) :
    ∃ j rawCv raw F origin,
      rawCv.name = cv.name ∧ rawCv.levelParams = cv.levelParams ∧
      DefinitionFrontAt ev xs env j rawCv raw hint F origin cv.type value := by
  obtain ⟨F, whole⟩ := accepted
  rcases fold_definition_origin whole stored with impossible |
      ⟨pre, rawCv, raw, post, origin, split, pref, step, suff, names, levels, header, front⟩
  · cases impossible
  · have cvEq : (⟨rawCv.name, rawCv.levelParams, cv.type⟩ : Ix.Kernel.ConstantVal md) = cv := by
      rw [names, levels]
    have atDecl : xs[pre.length]? = some (.defnDecl rawCv raw hint) := by simp [split]
    have preEq : xs.take pre.length = pre := by simp [split]
    have postEq : xs.drop (pre.length + 1) = post := by simp [split, List.drop_append]
    refine ⟨pre.length, rawCv, raw, F, origin, names, levels, ?_⟩
    unfold DefinitionFrontAt
    simp only [cvEq]
    refine ⟨atDecl, whole, ?_, step, ?_, header, front, ?_⟩
    · rw [preEq]; exact pref
    · rw [postEq]; exact suff
    · rw [names]
      apply (foldlM_checkDecl_post .verified (fueledOps .verified F) ev post _ env suff).persist
      simp only [Env.find?_cons, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal, ↓reduceIte]

end Ix.Cert.PrefixDefinitions

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Graded)
open Ix.Cert.PrefixDefinitions Ix.Cert.PrefixReadings Ix.Cert.ConversionValues

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- EVERY stored prefix definition reads to the supplied FINAL model's
own leaf. Actual all-kind origins supply the real full body runs and the
positive lookups; membership is never silently inverted into a lookup. -/
theorem DefinitionFrontAt.prefix_definitions_read
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∀ (ψ : LevelParam → Nat) (dcv : Ix.Kernel.ConstantVal md) (body : Ix.Kernel.Expr md),
      (∃ dhint, .defnInfo dcv body dhint ∈ before.consts) →
      denoteMeta M.internal.base2.acval before ψ 0 body = some (M.internal.base2.acval dcv.name ψ) := by
  have lookup : FindPreserved before envA := front.lookup_preserved
  obtain ⟨_, _, prefixRun, _, _, _, _, _⟩ := front
  have accepted : Cached.AcceptsRef .verified ev (ds.take i) before := ⟨F, prefixRun⟩
  intro ψ dcv body ⟨dhint, member⟩
  obtain ⟨j, rawCv, rawBody, fuel, origin, nameEq, levelsEq, created⟩ :=
    reference_stored_definition_origin accepted member
  have localLookup : FindPreserved origin before := created.lookup_preserved
  have finalLookup : FindPreserved origin envA := by
    intro n ci found
    exact lookup (localLookup found)
  obtain ⟨_, _, _, _, _, _, valueFront, stored⟩ := created
  obtain ⟨_, bodyInfer, _⟩ := valueFront.2.2.2.2.2
  obtain ⟨a, originRead, prefixRead⟩ := inferred_readings_preserved M.internal.base2.acval ψ
    localLookup (valueFront_frame valueFront) bodyInfer
  obtain ⟨b, originRead', finalRead⟩ := inferred_readings_preserved M.internal.base2.acval ψ
    finalLookup (valueFront_frame valueFront) bodyInfer
  have finalStored : envA.find? dcv.name = some (.defnInfo dcv body dhint) := by
    simpa only [nameEq, levelsEq] using lookup stored
  have pinned := M.internal.defn_reads ψ dcv body ⟨dhint, Semantics.Env.find?_mem finalStored⟩
  exact prefixRead.trans (originRead.symm.trans (originRead'.trans (finalRead.symm.trans pinned)))

/-- The actual front derives the UNIVERSAL definition-unfolding supplier
at the exact final interpretation, retaining the core/basic target package.
All other RulesInputs rows, baseline equality and source-form/translation
obligations remain separate; no prefix model's semantic fields are used. -/
theorem DefinitionFrontAt.final_prefix_defn
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ core : EnvModel V before,
      core.acval = M.internal.base2.acval ∧ cvalOf core.acval = M.model.cval ∧
      AcvalValid core ∧ (∀ φ : LevelParam → Nat, NatHeads core φ) ∧ EqLaw core ∧
      AcvalDefnInst core ∧
      ∀ φ : LevelParam → Nat,
        ∃ ha,
          denoteMeta core.acval before φ 0 expected = some ha ∧ Graded V [] ha ∧
          denoteMeta core.acval before φ 0 checked = some (core.acval cv.name φ) ∧
          Graded V [] (core.acval cv.name φ) ∧
          ∀ ρ : BVarIdx → V, interp V ρ (core.acval cv.name φ) ∈ˢ interp V ρ ha := by
  obtain ⟨core, acvalEq, cvalEq, valid, heads, eqLaw, target⟩ := front.final_prefix_core V M
  refine ⟨core, acvalEq, cvalEq, valid, heads, eqLaw, ?_, target⟩
  simpa only [AcvalDefnInst, acvalEq] using front.prefix_definitions_read V M

end Ix.Cert.ReferenceFronts
