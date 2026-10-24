import Ix.Cert.PrefixDefinitions

/-! # Constant typing through actual prefix growth

New projection tables belong to formers fresh in the ORIGINAL checker
prefix, including the native retry. Old stored structure heads therefore
keep all their slots. This is real producer evidence, not a global absence
assumption or a consequence of definition-entry preservation.
-/

namespace Ix.Cert.PrefixConstType

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.ReferenceFronts

universe w
variable {md : Mode}

def isTable : Ix.Kernel.ConstantInfo md → Bool
  | .projInfo _ => true
  | _ => false

def tables (env : Env md) : List (Ix.Kernel.ConstantInfo md) := env.consts.filter isTable

@[simp] theorem table_mem {env : Env md} {tbl : ProjTable md} :
    .projInfo tbl ∈ tables env ↔ .projInfo tbl ∈ env.consts := by simp [tables, isTable]

def TableOrigin (before after : Env md) : Prop := ∀ tbl,
  .projInfo tbl ∈ after.consts → .projInfo tbl ∈ before.consts ∨ before.find? tbl.structName = none

theorem TableOrigin.of_tables {before after : Env md} (same : tables after = tables before) :
    TableOrigin before after := fun _ member => Or.inl (table_mem.mp (same ▸ table_mem.mpr member))

theorem fold_tables {α : Type} (step : Env md → α → CheckM md (Env md)) :
    ∀ (xs : List α) (env : Env md),
      (∀ e x, x ∈ xs → ExPost (step e x) (fun e' => tables e' = tables e)) →
      ExPost (xs.foldlM step env) (fun e' => tables e' = tables env) := by
  intro xs
  induction xs with
  | nil => intro env _; simp
  | cons x xs ih =>
    intro env each
    rw [List.foldlM_cons, ExPost.post_bind]
    exact ExPost.mono (fun mid first => ExPost.mono (fun _ rest => rest.trans first)
      (ih mid fun e y hy => each e y (List.mem_cons_of_mem _ hy))) (each env x List.mem_cons_self)

theorem basis_tables (env : Env md) (kind : BasisKind) :
    ExPost (checkBasisDecl env kind : CheckM md (Env md)) (fun e => tables e = tables env) := by
  have pins : ∀ ci ∈ kind.declsA, isTable (md := md) ci = false := by
    have all : (kind.declsA (md := md)).all (fun ci => !isTable ci) = true := by cases kind <;> rfl
    intro ci member
    simpa using List.all_eq_true.mp all ci member
  have folded := fold_tables (installBasisDecl (m := CheckM md)) kind.declsA env
    (fun e ci member => by simp [installBasisDecl, tables, pins ci member])
  simpa only [checkBasisDecl, ExPost.post_bind, ExPost.post_ite, ExPost.post_throw,
    ExPost.post_pure, imp_true_iff, and_true] using And.intro (fun _ _ => folded) (fun _ => folded)

variable (mode : CheckMode) (ops : (CheckerOps md) (CheckM md))

theorem member_tables (names : List (Key md)) (caps : IndCaps md) (env : Env md)
    (ci : Ix.Kernel.ConstantInfo md) :
    ExPost (checkIndMember ops names caps env ci) (fun e => tables e = tables env) := by
  unfold checkIndMember
  rw [ExPost.post_bind]
  apply ExPost.of_forall
  intro cvA
  cases ci <;> simp [tables, isTable]

theorem recs_tables (names : List (Key md)) (env : Env md) (recs : List (Ix.Kernel.ConstantInfo md)) :
    ExPost (checkIndRecs mode ops names env recs) (fun e => tables e = tables env) := by
  unfold checkIndRecs
  simp only [ExPost.post_ite, ExPost.post_pure, ExPost.post_throw, ExPost.post_bind,
    imp_true_iff, true_and, and_true]
  intro _ _
  apply ExPost.of_forall
  intro pair
  apply fold_tables
  intro e c _
  simp [tables, isTable]

theorem projection_tables (T ctor : Key md) (lps : List LevelParam) (nP nF : Nat) (env : Env md) (i : Nat) :
    ExPost (installProjFnStep mode ops T ctor lps nP nF env i) (fun e => tables e = tables env) := by
  simp [installProjFnStep, checkProjFn, tables, isTable]

theorem modeled_tables (env : Env md) (block : List (Ix.Kernel.ConstantInfo md)) :
    ExPost (checkModeled mode ops env block) (fun e => tables e = tables env) := by
  unfold checkModeled
  simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true, ExPost.post_bind]
  intro _
  split
  · rename_i cvT caps cvC nP nF _ _
    simp only [ExPost.post_pure, ExPost.post_bind]
    refine ExPost.mono (fun mid first => ?_) (fold_tables _ _ env (fun e ci _ => member_tables ops _ _ e ci))
    refine ExPost.mono (fun mid' second => ?_) (recs_tables mode ops _ mid _)
    simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, ExPost.post_pure,
      imp_true_iff, and_true]
    intro _ _
    refine ⟨fun _ => ?_, fun _ => second.trans first⟩
    exact ExPost.mono (fun _ last => last.trans (second.trans first))
      (fold_tables _ _ mid' fun e i _ => projection_tables mode ops _ _ _ _ _ e i)
  · simp only [ExPost.post_bind]
    refine ExPost.mono (fun mid first => ?_) (fold_tables _ _ env (fun e ci _ => member_tables ops _ _ e ci))
    exact ExPost.mono (fun _ second => second.trans first) (recs_tables mode ops _ mid _)

theorem constructors_tables (nP : Nat) (cs : List (Ix.Kernel.ConstantVal md × Nat)) (env : Env md) :
    tables (consSumCtors nP cs env) = tables env := by
  induction cs generalizing env with
  | nil => rfl
  | cons c cs ih => simpa [consSumCtors, tables, isTable] using ih ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩

theorem native_table_origin (root : Env md) (p : NativeParts md)
    (ctors : List (Ix.Kernel.ConstantVal md × Nat)) (sorts : List (List Ix.Kernel.Level)) (env : Env md)
    (keeps : tables env = tables root) (fresh : root.find? p.cvT.name = none) :
    ExPost (checkNativeTable p ctors sorts env : CheckM md (Env md)) (TableOrigin root) := by
  unfold checkNativeTable
  split
  · split
    · refine ExPost.mono (fun e shape => ?_) (checkStructProjTable_post _ _ _ _ _ _ _ _ _ env)
      obtain ⟨tbl, head, rfl, _⟩ := shape
      intro other member
      rcases List.mem_cons.mp member with same | old
      · obtain rfl := Ix.Kernel.ConstantInfo.projInfo.inj same
        exact Or.inr (head ▸ fresh)
      · exact Or.inl (table_mem.mp (keeps ▸ table_mem.mpr old))
    · simpa using TableOrigin.of_tables keeps
  · simpa using TableOrigin.of_tables keeps

/-- Freshness is retained at root, BEFORE the former is inserted. -/
theorem native_pass_origin (root : Env md) (p : NativeParts md) (isRec : Bool) :
    ExPost (checkNativePass ops root p isRec) (fun r =>
      tables r.1.env₁ = tables root ∧ root.find? r.1.p.cvT.name = none) := by
  unfold checkNativePass
  rw [ExPost.post_bind]
  refine ExPost.mono (fun r shape => ?_) (checkSumInd_post root p.toInductiveShape _)
  obtain ⟨mid, cvA, pA⟩ := r
  dsimp only at shape ⊢
  obtain ⟨rfl, _, typeEq, _, _, fresh⟩ := shape
  simp [tables, isTable, NativeParts.complete, NativeParts.withKinds, typeEq, fresh]

theorem native_tail_origin (root : Env md) (q : NativePass md (Env md))
    (keeps : tables q.env₁ = tables root) (fresh : root.find? q.p.cvT.name = none) :
    ExPost (checkNativeTail ops root q) (TableOrigin root) := by
  unfold checkNativeTail
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, true_and, imp_true_iff]
  intro _
  refine ExPost.of_forall fun _ => ExPost.of_forall fun _ =>
    ⟨fun _ => ⟨fun _ => ?_, trivial⟩, trivial⟩
  apply ExPost.of_forall
  intro result
  apply native_table_origin root _ _ _ _ ?_ fresh
  simpa only [tables, List.filter_cons, isTable, Bool.false_eq_true, ↓reduceIte] using
    (constructors_tables q.p.nP q.ctorsA q.env₁).trans keeps

/-- Both settled paths use their actual pass at the ORIGINAL root. -/
theorem native_origin (root : Env md) (p : NativeParts md) :
    ExPost (checkNative ops root p) (TableOrigin root) := by
  unfold checkNative
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
  intro _
  refine ExPost.mono (fun result first => ?_) (native_pass_origin ops root p _)
  obtain ⟨q, settled⟩ := result
  cases settled with
  | true => simpa using native_tail_origin ops root q first.1 first.2
  | false =>
    have follow : ExPost (checkNativePass ops root p (nativeIsRec q.p.kinds))
        (fun result => result.2 = true → ExPost (checkNativeTail ops root result.1) (TableOrigin root)) := by
      exact ExPost.mono (fun result second _ => native_tail_origin ops root result.1 second.1 second.2)
        (native_pass_origin ops root p _)
    simpa using follow

/-- Actual checker dispatch: only the native arm can add a table, and its
former was fresh in this ORIGINAL pre-step environment. -/
theorem step_table_origin (ev : Evidences md) (env : Env md) (d : Declaration md) :
    ExPost (checkDecl mode ops ev env d) (TableOrigin env) := by
  cases d with
  | defnDecl cv value hint =>
    unfold checkDecl
    rw [ExPost.post_bind]
    apply ExPost.of_forall
    intro cvA
    rw [ExPost.post_bind]
    refine ExPost.mono (fun e shape => ?_) (checkDefnVal_post env cvA value hint)
    obtain ⟨v, rfl⟩ := shape
    have kept : TableOrigin env ⟨.defnInfo cvA v hint :: env.consts⟩ := TableOrigin.of_tables rfl
    simp [kept]
    intro _ _ _ _
    split <;> simp [kept]
  | thmDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    exact ExPost.of_forall fun cvA => ExPost.mono
      (fun e ⟨v, shape⟩ => by rw [shape]; exact TableOrigin.of_tables rfl) (checkThmVal_post env cvA value)
  | opaqueDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    exact ExPost.of_forall fun cvA => ExPost.mono
      (fun e shape => by rw [shape]; exact TableOrigin.of_tables rfl) (checkOpaqueVal_post env cvA value)
  | axiomDecl cv => simp (config := { contextual := true }) [checkDecl, TableOrigin]
  | basisDecl kind => exact ExPost.mono (fun _ same => TableOrigin.of_tables same) (basis_tables env kind)
  | indDecl block nP =>
    unfold checkDecl
    rw [ExPost.post_bind]
    apply ExPost.of_forall
    intro _
    split
    · exact ExPost.mono (fun _ same => TableOrigin.of_tables same) (basis_tables env _)
    · simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
      intro _
      split
      · exact native_origin ops env _
      · exact ExPost.mono (fun _ same => TableOrigin.of_tables same) (modeled_tables mode ops env block)
  | quotDecl k cv =>
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
    intro _
    cases k <;> first
      | exact ExPost.mono (fun _ same => TableOrigin.of_tables same) (basis_tables env .quotK)
      | simpa using TableOrigin.of_tables (rfl : tables env = tables env)

/-- Present OR absent slots stay fixed at every already-stored head. New
tables for genuinely new heads are unrestricted. -/
def StoredHeadSlots (before after : Env md) : Prop := ∀ T,
  (before.find? T).isSome = true → ∀ j, after.findProj? T j = before.findProj? T j

theorem checked_step_stored_slots {ev : Evidences md} {F : Nat} {before after : Env md}
    {d : Declaration md}
    (run : checkDecl .verified (fueledOps .verified F) ev before d = .ok after) :
    StoredHeadSlots before after := by
  have growth := checkDecl_post .verified (fueledOps .verified F) ev before d after run
  have lookup : FindPreserved before after := by intro n ci found; exact growth.persist found
  intro T present j
  have backwards : ∀ entry, after.findProj? T j = some entry → before.findProj? T j = some entry := by
    intro entry found
    obtain ⟨tbl, tableFound, bound, rfl⟩ := Env.findProj?_some found
    have headName : tbl.structName = T := projTableName_inj (Semantics.Env.find?_name tableFound)
    rcases growth.find_cases tableFound with old | ⟨_, absent⟩
    · exact Env.findProj?_of_table old bound
    · rcases step_table_origin .verified (fueledOps .verified F) ev before d after run tbl
          (Semantics.Env.find?_mem tableFound) with oldMember | fresh
      · have noTable : before.find? (Ix.Kernel.ConstantInfo.projInfo tbl).name = none := by
          simpa only [Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal, headName] using absent
        exact (name_ne_of_mem_of_fresh noTable _ oldMember rfl).elim
      · rw [headName] at fresh
        rw [fresh] at present
        cases present
  cases slot : before.findProj? T j with
  | none =>
    cases finalSlot : after.findProj? T j with
    | none => rfl
    | some entry => have old := backwards entry finalSlot; rw [slot] at old; cases old
  | some entry => exact PrefixReadings.projection_slot lookup slot

/-- The real successful suffix preserves old-head slots at EVERY step,
including generated/native/modeled/basis/quotient declarations. -/
theorem checked_suffix_stored_slots {ev : Evidences md} {F : Nat}
    {tail : List (Declaration md)} {before after : Env md}
    (run : tail.foldlM (checkDecl .verified (fueledOps .verified F) ev) before = .ok after) :
    StoredHeadSlots before after := by
  induction tail generalizing before with
  | nil => cases run; intro _ _ _; rfl
  | cons d tail ih =>
    obtain ⟨mid, step, rest⟩ := foldlM_cons_ok run
    have first := checked_step_stored_slots step
    have next := ih rest
    have growth := checkDecl_post .verified (fueledOps .verified F) ev before d mid step
    intro T present j
    cases found : before.find? T with
    | none => rw [found] at present; cases present
    | some ci =>
      have presentMid : (mid.find? T).isSome = true := by rw [growth.persist found]; rfl
      exact (next T presentMid j).trans (first T present j)

variable {before after : Env md}

theorem query_eq (lookup : FindPreserved before after) {n : Key md}
    (present : (before.find? n).isSome = true) : after.find? n = before.find? n := by
  cases found : before.find? n with
  | none => rw [found] at present; cases present
  | some ci => exact lookup found

/-- Guard equality is derived only when this subject's support names are
already present. Literal support may still grow elsewhere. -/
theorem nat_guard_eq (lookup : FindPreserved before after)
    (n : (before.find? natName).isSome = true) (z : (before.find? natZeroName).isSome = true)
    (s : (before.find? natSuccName).isSome = true) : natLitSupported after = natLitSupported before := by
  unfold natLitSupported
  rw [query_eq lookup n, query_eq lookup z, query_eq lookup s]

theorem string_queries_eq (lookup : FindPreserved before after) {s : String}
    (resolves : (Ix.Kernel.Expr.lit (.strVal s)).constsResolve before = true) :
    strLitSupported after = strLitSupported before ∧
    Ix.Kernel.Verify.levelParamsAt after listNilName = Ix.Kernel.Verify.levelParamsAt before listNilName ∧
    Ix.Kernel.Verify.levelParamsAt after listConsName = Ix.Kernel.Verify.levelParamsAt before listConsName := by
  simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at resolves
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨n, z⟩, s⟩, st⟩, ofList⟩, list⟩, nil⟩, cons⟩, char⟩, ofNat⟩ := resolves
  refine ⟨?_, (levelParamsAt_congr lookup nil).symm, (levelParamsAt_congr lookup cons).symm⟩
  unfold strLitSupported
  rw [nat_guard_eq lookup n z s, query_eq lookup st, query_eq lookup ofList, query_eq lookup list,
    query_eq lookup nil, query_eq lookup cons, query_eq lookup char, query_eq lookup ofNat]

/-- Every resolving subject has the same reading at the fixed acval.
Resolution supplies the literal queries and the OLD projection heads;
both table and pair-fallback branches are retained. No input reading,
model, grade, global guard equality or global absence premise is assumed. -/
theorem resolving_reading_eq
    (acval : Key md → (LevelParam → Nat) → AnnotTerm) (φ : LevelParam → Nat)
    (d : Nat) (e : Ix.Kernel.Expr md) (lookup : FindPreserved before after)
    (slots : StoredHeadSlots before after) (resolves : e.constsResolve before = true) :
    denoteMeta acval before φ d e = denoteMeta acval after φ d e := by
  revert resolves
  induction d, e using denoteMeta.induct (env := before) with
  | case1 d u => intro _; rw [denoteMeta, denoteMeta]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci found arity => intro _; rw [denoteMeta, found, denoteMeta, lookup found]
  | case4 d n us ci found arity => intro _; rw [denoteMeta, found, denoteMeta, lookup found]
  | case5 d n us absent => intro h; simp [Ix.Kernel.Expr.constsResolve, absent] at h
  | case6 d ty body mb ihty ihbody =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    rw [denoteMeta, denoteMeta, ihty h.1, ihbody (Ix.Kernel.Expr.constsResolve_instantiate1 h.1 0 h.2)]
  | case7 d ty body mb ihty ihbody =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    rw [denoteMeta, denoteMeta, ihty h.1, ihbody (Ix.Kernel.Expr.constsResolve_instantiate1 h.1 0 h.2)]
  | case8 d f a ihf iha =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    rw [denoteMeta, denoteMeta, ihf h.1, iha h.2]
  | case9 d ty val body => intro _; rw [denoteMeta, denoteMeta]
  | case10 d sn j e ih =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    rw [denoteMeta, denoteMeta, ih h.2, slots sn h.1 j]
  | case11 d n support =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    rw [denoteMeta, denoteMeta, nat_guard_eq lookup h.1.1 h.1.2 h.2]
  | case12 d n support =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    rw [denoteMeta, denoteMeta, nat_guard_eq lookup h.1.1 h.1.2 h.2]
  | case13 d s support =>
    intro h
    have queries := string_queries_eq lookup h
    rw [denoteMeta, denoteMeta, queries.1, queries.2.1, queries.2.2]
  | case14 d s support =>
    intro h
    have queries := string_queries_eq lookup h
    rw [denoteMeta, denoteMeta, queries.1, queries.2.1, queries.2.2]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b mb => exact absurd rfl (hlet ty v b mb)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l => cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end Ix.Cert.PrefixConstType

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Graded)
open Ix.Cert.PrefixConstType

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- The actual indexed current/suffix run supplies old-head slot stability;
it is not a caller-supplied environment or missing-slot agreement. -/
theorem DefinitionFrontAt.stored_head_slots
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked) :
    StoredHeadSlots before envA := by
  obtain ⟨_, _, _, step, suffix, _, _, _⟩ := front
  have run : (.defnDecl cv raw hint :: ds.drop (i + 1)).foldlM
      (checkDecl .verified (fueledOps .verified F) ev) before = .ok envA := by
    rw [List.foldlM_cons, step]
    exact suffix
  exact checked_suffix_stored_slots run

/-- UNIVERSAL constant typing at the exact supplied final interpretation.
Actual prefix WF gives resolution of every stored header; level
instantiation preserves it. The same final M supplies the arbitrary-depth,
arbitrary-level reading/grade/membership, transported by the derived
reading equation. Computed/pinned headers require no invented inference.
The existing tower exclusion and all other supplier obligations remain. -/
theorem DefinitionFrontAt.final_prefix_const_ty
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ core : EnvModel V before,
      core.acval = M.internal.base2.acval ∧ cvalOf core.acval = M.model.cval ∧
      AcvalValid core ∧ (∀ φ : LevelParam → Nat, NatHeads core φ) ∧ EqLaw core ∧
      AcvalDefnInst core ∧ (∀ φ : LevelParam → Nat, ConstType core φ) ∧
      ∀ φ : LevelParam → Nat,
        ∃ ha,
          denoteMeta core.acval before φ 0 expected = some ha ∧ Graded V [] ha ∧
          denoteMeta core.acval before φ 0 checked = some (core.acval cv.name φ) ∧
          Graded V [] (core.acval cv.name φ) ∧
          ∀ ρ : BVarIdx → V, interp V ρ (core.acval cv.name φ) ∈ˢ interp V ρ ha := by
  obtain ⟨core, acvalEq, cvalEq, valid, heads, eqLaw, definitions, target⟩ := front.final_prefix_defn V M
  have lookup : FindPreserved before envA := front.lookup_preserved
  have slots : StoredHeadSlots before envA := front.stored_head_slots
  refine ⟨core, acvalEq, cvalEq, valid, heads, eqLaw, definitions, ?_, target⟩
  intro φ d n ci us found notTower arity
  obtain ⟨ta, finalRead, grade, member⟩ := M.internal.constType (φ := φ) d n ci us
    (lookup found) notTower arity
  have resolves := (core.wf ci (Semantics.Env.find?_mem found)).2.2.1
  have instantiated : (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us).constsResolve
      before = true := by
    rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
    exact resolves
  have same := resolving_reading_eq M.internal.base2.acval φ d _ lookup slots instantiated
  refine ⟨ta, ?_, grade, ?_⟩
  · simpa only [acvalEq] using same.trans finalRead
  · simpa only [acvalEq] using member

end Ix.Cert.ReferenceFronts
