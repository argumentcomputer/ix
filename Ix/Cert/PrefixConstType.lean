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

end Ix.Cert.PrefixConstType
