module

public import IxC.Kernel.Verify.Rename.Union

@[expose] public section

/-!
# What a declaration installs (S1, the install lemma)

`checkDecl` extends the environment only by constants whose keys are over
the declaration's own names, or role keys (the pinned basis blocks): a key's
*base* (`Key.base`, the key with its derivations stripped) is one of the
declaration's names' bases, or a role. So a declaration changes no lookup
over any other base (`Grows.find_eq`). The union of two lists rests on it:
the keys over a base both lists declare come from that base's declaration
alone, in either list.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md : Mode}

/-! ## Bases and growth -/

@[simp] theorem Key.base_id (i : md.Id) : (Key.id i).base = .id i := rfl
@[simp] theorem Key.base_role (r : Role) : (Key.role r : Key md).base = .role r := rfl
@[simp] theorem Key.base_aux (k : Key md) (d : Derived) : (Key.aux k d).base = k.base := rfl
@[simp] theorem Key.base_auxKey (k : Key md) (d : Derived) : (auxKey k d).base = k.base := rfl

/-- A lookup missing from `new ++ env` is missing from `env`. -/
theorem Env.find?_none_of_append {new : List (ConstantInfo md)} {env : Env md} {k : Key md}
    (h : (⟨new ++ env.consts⟩ : Env md).find? k = none) : env.find? k = none := by
  simp only [Env.find?, List.find?_append, Option.or_eq_none_iff] at h
  exact h.2

/-- **Growth**: `env'` is `env` with constants in front, each named by a key
satisfying `Q` and missing from `env` (so `env`'s lookups persist,
`Grows.persist`), no two of them under one name (so name uniqueness
persists, `Grows.nodup`). -/
def Grows (Q : Key md → Prop) (env env' : Env md) : Prop :=
  ∃ new : List (ConstantInfo md), env'.consts = new ++ env.consts ∧
    (∀ c ∈ new, Q c.name ∧ env.find? c.name = none) ∧ (new.map (·.name)).Nodup

theorem Grows.refl (Q : Key md → Prop) (env : Env md) : Grows Q env env :=
  ⟨[], rfl, (fun _ h => nomatch h), List.nodup_nil⟩

/-- A name `env` misses is the name of none of its constants. -/
theorem Env.find?_none_ne {env : Env md} {k : Key md} (h : env.find? k = none)
    {c : ConstantInfo md} (hc : c ∈ env.consts) : c.name ≠ k := by
  intro he
  unfold Env.find? at h
  exact (List.find?_eq_none.mp h) c hc (beq_iff_eq.mpr he)

theorem Grows.trans {Q : Key md → Prop} {e₁ e₂ e₃ : Env md} (h₁ : Grows Q e₁ e₂)
    (h₂ : Grows Q e₂ e₃) : Grows Q e₁ e₃ := by
  obtain ⟨n₁, h₁, q₁, d₁⟩ := h₁
  obtain ⟨n₂, h₂, q₂, d₂⟩ := h₂
  refine ⟨n₂ ++ n₁, by rw [h₂, h₁, List.append_assoc], fun c hc => ?_, ?_⟩
  · rcases List.mem_append.mp hc with hc | hc
    · refine ⟨(q₂ c hc).1, ?_⟩
      have h := (q₂ c hc).2
      obtain ⟨cs₂⟩ := e₂
      simp only at h₁
      subst h₁
      exact Env.find?_none_of_append h
    · exact q₁ c hc
  · rw [List.map_append, List.nodup_append]
    refine ⟨d₂, d₁, fun a ha b hb hab => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hb
    have hmem : c' ∈ e₂.consts := by rw [h₁]; exact List.mem_append_left _ hc'
    exact Env.find?_none_ne (q₂ c hc).2 hmem hab.symm

theorem Grows.push {Q : Key md → Prop} {env : Env md} {c : ConstantInfo md} (hc : Q c.name)
    (hf : env.find? c.name = none) : Grows Q env ⟨c :: env.consts⟩ :=
  ⟨[c], rfl, (fun c' h => by rcases List.mem_singleton.mp h with rfl; exact ⟨hc, hf⟩),
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩

theorem Grows.mono {Q Q' : Key md → Prop} (hQ : ∀ k, Q k → Q' k) {env env' : Env md}
    (h : Grows Q env env') : Grows Q' env env' :=
  let ⟨n, h, q, d⟩ := h; ⟨n, h, fun c hc => ⟨hQ _ (q c hc).1, (q c hc).2⟩, d⟩

/-- **Growth keeps name uniqueness**: the names of `env'`'s constants are
pairwise distinct when `env`'s are. -/
theorem Grows.nodup {Q : Key md → Prop} {env env' : Env md} (h : Grows Q env env')
    (hn : (env.consts.map (·.name)).Nodup) : (env'.consts.map (·.name)).Nodup := by
  obtain ⟨n, h, q, d⟩ := h
  rw [h, List.map_append, List.nodup_append]
  refine ⟨d, hn, fun a ha b hb hab => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hb
  exact Env.find?_none_ne (q c hc).2 hc' hab.symm

/-- **Growth keeps every lookup** of the old environment. -/
theorem Grows.persist {Q : Key md → Prop} {env env' : Env md} (h : Grows Q env env')
    {k : Key md} {c : ConstantInfo md} (hk : env.find? k = some c) : env'.find? k = some c := by
  obtain ⟨n, h, q, -⟩ := h
  obtain ⟨cs'⟩ := env'
  simp only at h
  subst h
  simp only [Env.find?, List.find?_append]
  have hn : n.find? (·.name == k) = none := by
    rw [List.find?_eq_none]
    intro c' hc' he
    have hf := (q c' hc').2
    rw [beq_iff_eq.mp he, hk] at hf
    exact nomatch hf
  rw [hn]
  exact hk

/-- **A lookup outside the growth** is unchanged. -/
theorem Grows.find_eq {Q : Key md → Prop} {env env' : Env md} (h : Grows Q env env') {k : Key md}
    (hk : ¬ Q k) : env'.find? k = env.find? k := by
  obtain ⟨n, h, q, -⟩ := h
  obtain ⟨cs⟩ := env'
  obtain ⟨cs₀⟩ := env
  simp only at h
  subst h
  simp only [Env.find?]
  induction n with
  | nil => rfl
  | cons c n ih =>
    simp only [List.cons_append, List.find?_cons]
    have hc : (c.name == k) = false := by
      cases hck : (c.name == k)
      · rfl
      · exact absurd (beq_iff_eq.mp hck ▸ (q c List.mem_cons_self).1) hk
    rw [hc]
    exact ih (fun c' hc' => q c' (List.mem_cons_of_mem _ hc'))

/-! ## Postconditions of checker runs -/

/-- **A postcondition of a run**: every success satisfies `P`. -/
def ExPost {ε α : Type} (x : Except ε α) (P : α → Prop) : Prop := ∀ a, x = .ok a → P a

namespace ExPost

variable {ε α β : Type} {P : β → Prop}

@[simp] theorem post_bind {x : Except ε α} {k : α → Except ε β} :
    ExPost (x >>= k) P ↔ ExPost x (fun a => ExPost (k a) P) := by
  constructor
  · intro h a ha b hb
    exact h b (by rw [ha]; exact hb)
  · intro h b hb
    cases hx : x with
    | error e => rw [hx] at hb; exact nomatch hb
    | ok a => rw [hx] at hb; exact h a hx b hb

@[simp] theorem post_map {g : α → β} {x : Except ε α} :
    ExPost (g <$> x) P ↔ ExPost x (fun a => P (g a)) := by
  constructor
  · intro h a ha
    exact h (g a) (by rw [ha]; rfl)
  · intro h b hb
    cases hx : x with
    | error e => rw [hx] at hb; exact nomatch hb
    | ok a => rw [hx] at hb; cases hb; exact h a hx

@[simp] theorem post_pure {b : β} : ExPost (pure b : Except ε β) P ↔ P b :=
  ⟨fun h => h b rfl, fun h _ ha => by cases ha; exact h⟩

@[simp] theorem post_ok {b : β} : ExPost (.ok b : Except ε β) P ↔ P b :=
  ⟨fun h => h b rfl, fun h _ ha => by cases ha; exact h⟩

@[simp] theorem post_throw {e : ε} : ExPost (throw e : Except ε β) P ↔ True :=
  ⟨fun _ => trivial, fun _ _ h => nomatch h⟩

@[simp] theorem post_error {e : ε} : ExPost (.error e : Except ε β) P ↔ True :=
  ⟨fun _ => trivial, fun _ _ h => nomatch h⟩

@[simp] theorem post_ite {c : Prop} [Decidable c] {x y : Except ε β} :
    ExPost (if c then x else y) P ↔ (c → ExPost x P) ∧ (¬c → ExPost y P) := by
  by_cases h : c <;> simp [h]

@[simp] theorem post_true {x : Except ε β} : ExPost x (fun _ => True) ↔ True :=
  ⟨fun _ => trivial, fun _ _ _ => trivial⟩

theorem of_ok {x : Except ε β} {b : β} (h : ExPost x P) (hx : x = .ok b) : P b := h b hx

theorem of_forall {x : Except ε β} (h : ∀ b, P b) : ExPost x P := fun b _ => h b

theorem mono {Q : β → Prop} {x : Except ε β} (hPQ : ∀ b, P b → Q b) (h : ExPost x P) :
    ExPost x Q :=
  fun b hb => hPQ b (h b hb)

end ExPost

/-! ## The value declarations -/

section Values

variable {ops : (CheckerOps md) (CheckM md)}

theorem checkDefnVal_post (env : Env md) (cv : ConstantVal md) (value : Expr md)
    (hint : ReducibilityHint) :
    ExPost (checkDefnVal ops env cv value hint)
      (fun e => ∃ v, e = ⟨.defnInfo cv v hint :: env.consts⟩) := by
  simp [checkDefnVal]

theorem checkConstantVal_post (env : Env md) (cv : ConstantVal md) :
    ExPost (checkConstantVal ops env cv) (fun cv' => cv'.name = cv.name ∧ env.find? cv.name = none) := by
  unfold checkConstantVal
  by_cases hf : (env.find? cv.name).isSome = true
  · simp [hf]
  · have hn : env.find? cv.name = none := by simpa using hf
    simp [hn]

theorem checkThmVal_post (env : Env md) (cv : ConstantVal md) (value : Expr md) :
    ExPost (checkThmVal ops env cv value)
      (fun e => ∃ v, e = ⟨.thmInfo cv v :: env.consts⟩) := by
  simp [checkThmVal]

theorem checkOpaqueVal_post (env : Env md) (cv : ConstantVal md) (value : Expr md) :
    ExPost (checkOpaqueVal ops env cv value) (fun e => e = ⟨.axiomInfo cv :: env.consts⟩) := by
  simp [checkOpaqueVal]

theorem checkSumTele_post (env : Env md) (cv : ConstantVal md) (n : Nat) (cvTa₀ : ConstantVal md)
    (h₀ : cvTa₀.name = cv.name) :
    ExPost (checkSumTele ops env cv n cvTa₀) (fun r => r.1.name = cv.name) := by
  unfold checkSumTele
  split
  · simp [h₀]
  · simp [checkConstantVal]

theorem checkSumInd_post (env : Env md) (p : InductiveShape md)
    (capsOf : InductiveShape md → IndCaps md) :
    ExPost (checkSumInd ops env p capsOf) (fun r =>
      r.1 = ⟨.indInfo r.2.1 (capsOf r.2.2) :: env.consts⟩ ∧ r.2.1.name = p.cvT.name ∧
        r.2.2.cvT = p.cvT ∧ r.2.2.ctors = p.ctors ∧ r.2.2.cvR = p.cvR ∧
        env.find? p.cvT.name = none) := by
  unfold checkSumInd
  rw [ExPost.post_bind]
  refine ExPost.mono (fun cvTa₀ h₀ => ?_) (checkConstantVal_post env p.cvT)
  rw [ExPost.post_bind]
  refine ExPost.mono (fun r h₁ => ?_) (checkSumTele_post env p.cvT _ cvTa₀ h₀.1)
  obtain ⟨cvTa, s⟩ := r
  simp only at h₁
  simp [h₁, h₀.2, InductiveShape.withSort]

theorem normCtorVal_post (env : Env md) (T : Key md) (nP nF : Nat) (cvC cvCa : ConstantVal md)
    (h₀ : cvCa.name = cvC.name) :
    ExPost (normCtorVal ops env T nP nF cvC cvCa) (fun r => r.name = cvC.name) := by
  simp [normCtorVal, checkConstantVal, h₀]

theorem checkSumCtor_post (env₀ env : Env md) (T : Key md) (lps : List LevelParam)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvC : ConstantVal md) (nF : Nat)
    (cvTa : ConstantVal md) :
    ExPost (checkSumCtor ops env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa)
      (fun r => r.1.name = cvC.name ∧ env.find? cvC.name = none) := by
  unfold checkSumCtor
  rw [ExPost.post_bind]
  refine ExPost.mono (fun cvCa₀ h₀ => ?_) (checkConstantVal_post env cvC)
  rw [ExPost.post_bind]
  refine ExPost.mono (fun cvCa h₁ => ?_) (normCtorVal_post env T nP nF cvC cvCa₀ h₀.1)
  simp [h₁, h₀.2]

theorem checkSumCtors_post (env₀ env : Env md) (T : Key md) (lps : List LevelParam)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal md) :
    ∀ cs : List (ConstantVal md × Nat),
    ExPost (checkSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa cs)
      (fun r => r.1.map (·.1.name) = cs.map (·.1.name) ∧ ∀ c ∈ r.1, env.find? c.1.name = none)
  | [] => by simp [checkSumCtors]
  | c :: cs => by
    unfold checkSumCtors
    rw [ExPost.post_bind]
    refine ExPost.mono (fun r h₁ => ?_)
      (checkSumCtor_post env₀ env T lps nP nIdx resSort isProp large c.1 c.2 cvTa)
    obtain ⟨cvCa, sorts⟩ := r
    rw [ExPost.post_bind]
    refine ExPost.mono (fun r h₂ => ?_)
      (checkSumCtors_post env₀ env T lps nP nIdx resSort isProp large cvTa cs)
    obtain ⟨rest, srest⟩ := r
    simp only at h₁ h₂
    refine (ExPost.post_pure).mpr ⟨by simp [h₁.1, h₂.1], fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · simpa [h₁.1] using h₁.2
    · exact h₂.2 c hc

theorem checkNativeRec_post (env : Env md) (p : NativeParts md) (cvTa : ConstantVal md)
    (ctorsA : List (ConstantVal md × Nat)) :
    ExPost (checkNativeRec ops env p cvTa ctorsA)
      (fun r => r.1.name = p.cvR.name ∧ env.find? p.cvR.name = none) := by
  unfold checkNativeRec
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
  intro _ _
  refine ExPost.mono (fun cvRi h => ?_) (checkConstantVal_post env p.cvR)
  simp [h.2]

theorem checkStructProjTable_post (T C : Key md) (lps : List LevelParam) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal md) (env : Env md) :
    ExPost (checkStructProjTable T C lps nP nF resSort guards off cvCa env : CheckM md (Env md))
      (fun e => ∃ tbl : ProjTable md, tbl.structName = T ∧ e = ⟨.projInfo tbl :: env.consts⟩ ∧
        env.find? (projTableName T) = none) := by
  simp (config := { contextual := true }) [checkStructProjTable]

/-- **Over a list of names**: a key whose base is one of theirs, or a prelude role
(the pinned basis blocks' installs). -/
def Over (ns : List (Key md)) (k : Key md) : Prop :=
  k.base ∈ ns.map Key.base ∨ ∃ r ∈ preludeRoles, k.base = .role r

theorem Over.of_mem {ns : List (Key md)} {k : Key md} (h : k ∈ ns) : Over ns k :=
  Or.inl (List.mem_map_of_mem h)

theorem Over.auxKey {ns : List (Key md)} {k : Key md} (h : Over ns k) (d : Derived) :
    Over ns (auxKey k d) := by
  simpa [Over] using h

theorem Over.mono {ns ns' : List (Key md)} (hs : ∀ k ∈ ns, k ∈ ns') {k : Key md}
    (h : Over ns k) : Over ns' k := by
  rcases h with h | h
  · obtain ⟨k', hk', he⟩ := List.mem_map.mp h
    exact Or.inl (List.mem_map.mpr ⟨k', hs k' hk', he⟩)
  · exact Or.inr h

theorem Env.find?_cons_ne {env : Env md} {c : ConstantInfo md} {k : Key md} (h : c.name ≠ k) :
    (⟨c :: env.consts⟩ : Env md).find? k = env.find? k := by
  simp [Env.find?, List.find?_cons, h]

theorem consSumCtors_grows {Q : Key md → Prop} (nP : Nat) :
    ∀ (cs : List (ConstantVal md × Nat)) (env : Env md),
      (∀ c ∈ cs, Q c.1.name ∧ env.find? c.1.name = none) → (cs.map (·.1.name)).Nodup →
      Grows Q env (consSumCtors nP cs env)
  | [], env, _, _ => Grows.refl Q env
  | c :: cs, env, h, hnd => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    refine (Grows.push (c := .ctorInfo c.1 nP c.2) (h c List.mem_cons_self).1
      (h c List.mem_cons_self).2).trans (consSumCtors_grows nP cs _ (fun c' hc' => ?_) hnd.2)
    refine ⟨(h c' (List.mem_cons_of_mem _ hc')).1, ?_⟩
    rw [Env.find?_cons_ne]
    · exact (h c' (List.mem_cons_of_mem _ hc')).2
    · intro he
      exact hnd.1 ⟨c', hc', he.symm⟩

theorem checkNativeTable_post {Q : Key md → Prop} (p : NativeParts md)
    (ctorsA : List (ConstantVal md × Nat)) (sortss : List (List Level)) (env : Env md)
    (hT : Q (projTableName p.cvT.name)) :
    ExPost (checkNativeTable p ctorsA sortss env : CheckM md (Env md)) (Grows Q env) := by
  unfold checkNativeTable
  split
  · split
    · refine ExPost.mono (fun e he => ?_) (checkStructProjTable_post _ _ _ _ _ _ _ _ _ env)
      obtain ⟨tbl, htbl, rfl, hf⟩ := he
      have hn : (ConstantInfo.projInfo tbl).name = projTableName p.cvT.name := by
        rw [show (ConstantInfo.projInfo tbl).name = projTableName tbl.structName from rfl, htbl]
      exact Grows.push (by rw [hn]; exact hT) (by rw [hn]; exact hf)
    · simp [Grows.refl]
  · simp [Grows.refl]

theorem checkNativeTail_post {Q : Key md → Prop} (env : Env md) (q : NativePass md (Env md))
    (hR : Q q.p.cvR.name) (hC : ∀ c ∈ q.ctorsA, Q c.1.name ∧ q.env₁.find? c.1.name = none)
    (hnd : (q.ctorsA.map (·.1.name)).Nodup) (hT : Q (projTableName q.p.cvT.name)) :
    ExPost (checkNativeTail ops env q) (Grows Q q.env₁) := by
  unfold checkNativeTail
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, true_and, imp_true_iff]
  intro _
  refine ExPost.of_forall fun _ => ExPost.of_forall fun _ =>
    ⟨fun _ => ⟨fun _ => ?_, trivial⟩, trivial⟩
  refine ExPost.mono (fun r hr => ?_) (checkNativeRec_post _ _ _ _)
  refine ExPost.mono (fun e he => ?_) (checkNativeTable_post _ _ _ _ hT)
  refine (consSumCtors_grows _ _ _ hC hnd).trans ((Grows.push ?_ ?_).trans he)
  · show Q r.1.name
    rw [hr.1]
    exact hR
  · show Env.find? _ r.1.name = none
    rw [hr.1]
    exact hr.2

theorem checkNativePass_post {Q : Key md → Prop} (env : Env md) (p₀ : NativeParts md)
    (isRec : Bool) (hT : Q p₀.cvT.name) :
    ExPost (checkNativePass ops env p₀ isRec) (fun r =>
      Grows Q env r.1.env₁ ∧ r.1.p.cvT = p₀.cvT ∧ r.1.p.cvR = p₀.cvR ∧ r.1.p.ctors = p₀.ctors ∧
        r.1.ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) ∧
        ∀ c ∈ r.1.ctorsA, r.1.env₁.find? c.1.name = none) := by
  unfold checkNativePass
  rw [ExPost.post_bind]
  refine ExPost.mono (fun r hr => ?_) (checkSumInd_post env p₀.toInductiveShape _)
  obtain ⟨env₁, cvTa, p₁⟩ := r
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
  dsimp only at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  rw [ExPost.post_bind]
  refine ExPost.mono (fun r hr => ?_) (checkSumCtors_post _ _ _ _ _ _ _ _ _ _ _)
  obtain ⟨ctorsA, sortss⟩ := r
  dsimp only at hr ⊢
  rw [ExPost.post_bind]
  refine ExPost.of_forall fun kinds => ?_
  simp only [ExPost.post_pure]
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.2⟩
  · rw [h₁]
    exact Grows.push (by show Q cvTa.name; rw [h₂]; exact hT)
      (by show env.find? cvTa.name = none; rw [h₂]; exact h₆)
  · simpa [NativeParts.withKinds, NativeParts.complete] using h₃
  · simpa [NativeParts.withKinds, NativeParts.complete] using h₅
  · simpa [NativeParts.withKinds, NativeParts.complete] using h₄
  · simpa [NativeParts.withKinds, NativeParts.complete, h₄] using hr.1

theorem checkNative_post {Q : Key md → Prop} (env : Env md) (p₀ : NativeParts md)
    (hT : Q p₀.cvT.name) (hR : Q p₀.cvR.name) (hC : ∀ c ∈ p₀.ctors, Q c.1.name)
    (hPT : Q (projTableName p₀.cvT.name)) :
    ExPost (checkNative ops env p₀) (Grows Q env) := by
  have tail : (p₀.ctors.map (·.1.name)).Nodup → ∀ q : NativePass md (Env md),
      (Grows Q env q.env₁ ∧ q.p.cvT = p₀.cvT ∧ q.p.cvR = p₀.cvR ∧ q.p.ctors = p₀.ctors ∧
        q.ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) ∧
        ∀ c ∈ q.ctorsA, q.env₁.find? c.1.name = none) →
      ExPost (checkNativeTail ops env q) (Grows Q env) := by
    intro hnd q ⟨hg, h₁, h₂, _, h₄, h₅⟩
    refine ExPost.mono (fun e he => hg.trans he) (checkNativeTail_post env q ?_ ?_ (h₄ ▸ hnd) ?_)
    · rw [h₂]; exact hR
    · intro c hc
      have hm : c.1.name ∈ p₀.ctors.map (·.1.name) := h₄ ▸ List.mem_map_of_mem hc
      obtain ⟨c', hc', he⟩ := List.mem_map.mp hm
      exact ⟨by rw [← he]; exact hC c' hc', h₅ c hc⟩
    · rw [h₁]; exact hPT
  unfold checkNative
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, imp_true_iff]
  refine ⟨fun hnd => ExPost.mono (fun r hr => ⟨fun _ => tail hnd r.1 hr, fun _ => ?_⟩)
    (checkNativePass_post env p₀ _ hT), trivial⟩
  exact ExPost.mono (fun r hr => ⟨fun _ => tail hnd r.1 hr, trivial⟩)
    (checkNativePass_post env p₀ _ hT)

/-! ### The modeled route -/

theorem foldlM_grows {α : Type} {Q : Key md → Prop} (step : Env md → α → CheckM md (Env md)) :
    ∀ (l : List α) (env : Env md), (∀ e x, x ∈ l → ExPost (step e x) (Grows Q e)) →
      ExPost (l.foldlM step env) (Grows Q env)
  | [], env, _ => by simp [Grows.refl]
  | x :: l, env, h => by
    simp only [List.foldlM_cons, ExPost.post_bind]
    refine ExPost.mono (fun e he => ?_) (h env x List.mem_cons_self)
    exact ExPost.mono (fun e' he' => he.trans he')
      (foldlM_grows step l e fun e' y hy => h e' y (List.mem_cons_of_mem _ hy))

theorem Env.find?_cons_none {env : Env md} {c : ConstantInfo md} {k : Key md}
    (h : (⟨c :: env.consts⟩ : Env md).find? k = none) : c.name ≠ k ∧ env.find? k = none := by
  by_cases hc : c.name = k
  · subst hc
    simp [Env.find?] at h
  · rw [Env.find?_cons_ne hc] at h
    exact ⟨hc, h⟩

/-- **A fold of named pushes**: each step leaves the environment or pushes
one constant named by the item, the names fresh and pairwise distinct. -/
theorem foldlM_push_grows {α : Type} {Q : Key md → Prop} (step : Env md → α → CheckM md (Env md))
    (nm : α → Key md)
    (hstep : ∀ e x, ExPost (step e x)
      (fun e' => e' = e ∨ ∃ c : ConstantInfo md, c.name = nm x ∧ e' = ⟨c :: e.consts⟩)) :
    ∀ (l : List α) (env : Env md), (∀ x ∈ l, Q (nm x) ∧ env.find? (nm x) = none) →
      (l.map nm).Nodup → ExPost (l.foldlM step env) (Grows Q env)
  | [], env, _, _ => by simp [Grows.refl]
  | x :: l, env, h, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.foldlM_cons, ExPost.post_bind]
    refine ExPost.mono (fun e he => ?_) (hstep env x)
    have hrest : ∀ y ∈ l, Q (nm y) ∧ e.find? (nm y) = none := by
      intro y hy
      refine ⟨(h y (List.mem_cons_of_mem _ hy)).1, ?_⟩
      rcases he with rfl | ⟨c, hc, rfl⟩
      · exact (h y (List.mem_cons_of_mem _ hy)).2
      · rw [Env.find?_cons_ne]
        · exact (h y (List.mem_cons_of_mem _ hy)).2
        · rw [hc]; intro he'; exact hnd.1 ⟨y, hy, he'.symm⟩
    have hg : Grows Q env e := by
      rcases he with rfl | ⟨c, hc, rfl⟩
      · exact Grows.refl Q _
      · exact Grows.push (by rw [hc]; exact (h x List.mem_cons_self).1)
          (by rw [hc]; exact (h x List.mem_cons_self).2)
    exact ExPost.mono (fun e' he' => hg.trans he') (foldlM_push_grows step nm hstep l e hrest hnd.2)

theorem checkMemberVal_post (blockNames : List (Key md)) (env' : Env md) (cv : ConstantVal md) :
    ExPost (checkMemberVal ops blockNames env' cv)
      (fun r => r.name = cv.name ∧ env'.find? cv.name = none) := by
  unfold checkMemberVal
  rw [ExPost.post_bind]
  refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env' cv)
  by_cases hs : cvA.name.isModelSuffix = true
  · simp [hs]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    split
    · simp [h]
    · simp

theorem checkIndMember_post {Q : Key md → Prop} (blockNames : List (Key md)) (caps : IndCaps md)
    (env' : Env md) (ci : ConstantInfo md) (hQ : Q ci.name) :
    ExPost (checkIndMember ops blockNames caps env' ci) (Grows Q env') := by
  unfold checkIndMember
  rw [ExPost.post_bind]
  refine ExPost.mono (fun cvA h => ?_) (checkMemberVal_post blockNames env' ci.toConstantVal)
  cases ci with
  | indInfo cv c =>
    exact (ExPost.post_pure).mpr (Grows.push (by show Q cvA.name; rw [h.1]; exact hQ)
      (by show env'.find? cvA.name = none; rw [h.1]; exact h.2))
  | ctorInfo cv a b =>
    exact (ExPost.post_pure).mpr (Grows.push (by show Q cvA.name; rw [h.1]; exact hQ)
      (by show env'.find? cvA.name = none; rw [h.1]; exact h.2))
  | _ => simp

theorem provisionRecs_post (blockNames : List (Key md)) :
    ∀ (envAcc : Env md) (recs : List (ConstantInfo md)),
      ExPost (provisionRecs ops blockNames envAcc recs)
        (fun r => (∀ c ∈ r.2, c.1.name ∈ recs.map (·.name) ∧ envAcc.find? c.1.name = none) ∧
          (r.2.map (·.1.name)).Nodup)
  | envAcc, [] => by simp [provisionRecs]
  | envAcc, ci :: rest => by
    unfold provisionRecs
    cases ci with
    | recInfo cv mI rP rules =>
      dsimp only
      rw [ExPost.post_bind]
      refine ExPost.mono (fun cvA h => ?_) (checkMemberVal_post blockNames envAcc _)
      rw [ExPost.post_bind]
      refine ExPost.mono (fun r hr => ?_) (provisionRecs_post blockNames _ rest)
      obtain ⟨envSelf, others⟩ := r
      simp only [ExPost.post_pure, List.mem_cons, List.map_cons, List.nodup_cons]
      have hfr : ∀ c ∈ others, cvA.name ≠ c.1.name ∧ envAcc.find? c.1.name = none :=
        fun c hc => Env.find?_cons_none (hr.1 c hc).2
      refine ⟨?_, ?_, hr.2⟩
      · rintro c (rfl | hc)
        · exact ⟨Or.inl h.1, by rw [h.1]; exact h.2⟩
        · exact ⟨Or.inr (hr.1 c hc).1, (hfr c hc).2⟩
      · intro hm
        obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
        exact (hfr c hc).1 he.symm
    | _ => simp

theorem checkIndRecs_post {Q : Key md → Prop} (blockNames : List (Key md)) (env₂ : Env md)
    (recs : List (ConstantInfo md)) (hQ : ∀ ci ∈ recs, Q ci.name) :
    ExPost (checkIndRecs mode ops blockNames env₂ recs) (Grows Q env₂) := by
  unfold checkIndRecs
  by_cases he : recs.isEmpty = true
  · simp [he, Grows.refl]
  simp only [he, Bool.false_eq_true, ↓reduceIte, ExPost.post_bind, ExPost.post_ite,
    ExPost.post_throw, imp_true_iff, and_true]
  intro _
  refine ExPost.mono (fun r hr => ?_) (provisionRecs_post blockNames env₂ recs)
  obtain ⟨envSelf, checked⟩ := r
  dsimp only at hr ⊢
  refine foldlM_push_grows _ (fun c => c.1.name) (fun e c => ?_) checked env₂ (fun c hc => ?_) hr.2
  · rw [ExPost.post_bind]
    refine ExPost.of_forall fun rules' => ?_
    simp only [ExPost.post_pure]
    exact Or.inr ⟨_, rfl, rfl⟩
  · obtain ⟨hm, hf⟩ := hr.1 c hc
    obtain ⟨ci, hci, he⟩ := List.mem_map.mp hm
    exact ⟨by rw [← he]; exact hQ ci hci, hf⟩

theorem checkProjFn_post (env' : Env md) (T ctorName : Key md) (lps : List LevelParam)
    (nP nF i : Nat) :
    ExPost (checkProjFn mode ops env' T ctorName lps nP nF i)
      (fun e => ∃ c : ConstantInfo md, c.name = projFnName T i ∧ e = ⟨c :: env'.consts⟩) := by
  simp [checkProjFn, ConstantInfo.name, ConstantInfo.toConstantVal]

theorem installProjFnStep_post (T ctorName : Key md) (lps : List LevelParam) (nP nF : Nat)
    (e : Env md) (i : Nat) :
    ExPost (installProjFnStep mode ops T ctorName lps nP nF e i)
      (fun e' => e' = e ∨ ∃ c : ConstantInfo md, c.name = projFnName T i ∧ e' = ⟨c :: e.consts⟩) := by
  unfold installProjFnStep
  split
  · exact ExPost.mono (fun e' he' => Or.inr he') (checkProjFn_post e T ctorName lps nP nF i)
  · simp

theorem checkModeled_post {Q : Key md → Prop} (env : Env md) (block : List (ConstantInfo md))
    (hQ : ∀ ci ∈ block, Q ci.name) (hP : ∀ ci ∈ block, ∀ i, Q (projFnName ci.name i)) :
    ExPost (checkModeled mode ops env block) (Grows Q env) := by
  unfold checkModeled
  simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true, ExPost.post_bind]
  intro _
  have hmem : ∀ {p : ConstantInfo md → Bool} {ci : ConstantInfo md},
      ci ∈ block.filter p → ci ∈ block :=
    fun h => (List.mem_filter.mp h).1
  split
  · rename_i cvT caps cvC nP nF h1 _
    have hT : ConstantInfo.indInfo cvT caps ∈ block := by
      have h := List.mem_singleton_self (ConstantInfo.indInfo cvT caps)
      rw [← h1] at h
      exact hmem h
    simp only [ExPost.post_pure, ExPost.post_bind]
    refine ExPost.mono (fun env₂ h₂ => ?_) (foldlM_grows _ _ env fun e ci hci =>
      checkIndMember_post _ _ e ci (hQ ci (hmem hci)))
    refine ExPost.mono (fun env₃ h₃ => ?_)
      (checkIndRecs_post (mode := mode) (ops := ops) _ env₂ _ fun ci hci => hQ ci (hmem hci))
    simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, ExPost.post_pure,
      imp_true_iff, and_true]
    intro _ hfree
    refine ⟨fun _ => ExPost.mono (fun e he => h₂.trans (h₃.trans he))
      (foldlM_push_grows _ (projFnName cvT.name) (installProjFnStep_post _ _ _ _ _)
        (List.range nF) env₃ (fun i hi => ⟨hP _ hT i, ?_⟩) ?_), fun _ => h₂.trans h₃⟩
    · have := List.all_eq_true.mp hfree i hi
      simpa using this
    · exact List.pairwise_map.mpr
        (List.Pairwise.imp (fun hne heq => hne (projFnName_inj heq).2) List.nodup_range)
  · simp only [ExPost.post_bind]
    refine ExPost.mono (fun env₂ h₂ => ?_) (foldlM_grows _ _ env fun e ci hci =>
      checkIndMember_post _ _ e ci (hQ ci (hmem hci)))
    exact ExPost.mono (fun e he => h₂.trans he)
      (checkIndRecs_post (mode := mode) (ops := ops) _ env₂ _ fun ci hci => hQ ci (hmem hci))

/-! ### The native route's names -/

theorem sumSplit_mem :
    ∀ {l : List (ConstantInfo md)} {cs : List (ConstantVal md × Nat × Nat)} {cvR : ConstantVal md}
      {mI rP : Nat} {rules : List (RecRule md)}, sumSplit l = some (cs, cvR, mI, rP, rules) →
      ConstantInfo.recInfo cvR mI rP rules ∈ l ∧ ∀ c ∈ cs, ConstantInfo.ctorInfo c.1 c.2.1 c.2.2 ∈ l
  | [.recInfo _ _ _ _], _, _, _, _, _, h => by
    simp only [sumSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨List.mem_singleton_self _, fun _ h => nomatch h⟩
  | .ctorInfo cvC nP nF :: rest, cs, cvR, mI, rP, rules, h => by
    simp only [sumSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', q⟩, hq, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hr, hc⟩ := sumSplit_mem hq
    refine ⟨List.mem_cons_of_mem _ hr, fun c hc' => ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hc c hc')
  | [], _, _, _, _, _, h => nomatch h
  | .recInfo _ _ _ _ :: _ :: _, _, _, _, _, _, h => nomatch h
  | .axiomInfo _ :: _, _, _, _, _, _, h => nomatch h
  | .defnInfo _ _ _ :: _, _, _, _, _, _, h => nomatch h
  | .thmInfo _ _ :: _, _, _, _, _, _, h => nomatch h
  | .indInfo _ _ :: _, _, _, _, _, _, h => nomatch h
  | .projInfo _ :: _, _, _, _, _, _, h => nomatch h

theorem nativeParts?_names {nP : Nat} {block : List (ConstantInfo md)} {p : NativeParts md}
    (h : nativeParts? nP block = some p) :
    p.cvT.name ∈ block.map (·.name) ∧ p.cvR.name ∈ block.map (·.name) ∧
      ∀ c ∈ p.ctors, c.1.name ∈ block.map (·.name) := by
  simp only [nativeParts?, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  unfold nativeShape? at hs
  split at hs
  · rename_i cvT caps rest
    split at hs
    · rename_i cs cvR mI rP rules hsplit
      obtain ⟨hr, hc⟩ := sumSplit_mem hsplit
      have key : s.cvT = cvT ∧ s.cvR = cvR ∧ s.ctors = cs.map fun c => (c.1, c.2.2) := by
        repeat' split at hs
        all_goals first
          | (simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, rfl⟩)
          | (simp at hs; obtain ⟨-, rfl⟩ := hs; exact ⟨rfl, rfl, rfl⟩)
          | (simp at hs; obtain ⟨-, hs⟩ := hs
             split at hs <;> (simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, rfl⟩))
          | (simp at hs)
      obtain ⟨h1, h2, h3⟩ := key
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact List.mem_map_of_mem List.mem_cons_self
      · rw [h2]
        exact List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ hr, rfl⟩
      · intro c hc'
        rw [h3] at hc'
        obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
        exact List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (hc c₀ hc₀), rfl⟩
    · exact nomatch hs
  · exact nomatch hs

/-! ### The pinned basis -/

theorem Key.pinIn_base {rs : List Role} : ∀ {k : Key md}, k.pinIn rs = true →
    ∃ r ∈ rs, k.base = .role r
  | .id _, h => nomatch h
  | .role r, h => ⟨r, List.contains_iff_mem.mp h, rfl⟩
  | .aux k _, h => Key.pinIn_base (k := k) h

theorem ConstantInfo.pinIn_name {rs : List Role} {c : ConstantInfo md} (h : c.pinIn rs = true) :
    c.name.pinIn rs = true := by
  cases c <;> simp_all [ConstantInfo.pinIn, ConstantVal.pinIn, ConstantInfo.name,
    ConstantInfo.toConstantVal]

theorem checkBasisDecl_post (ns : List (Key md)) (env : Env md) (kind : BasisKind) :
    ExPost (checkBasisDecl env kind : CheckM md (Env md)) (Grows (Over ns) env) := by
  have step : ∀ e ci, ci ∈ kind.declsA (md := md) →
      ExPost (installBasisDecl e ci : CheckM md (Env md)) (Grows (Over ns) e) := by
    intro e ci hci
    have hp := List.all_eq_true.mp (declsA_pinIn (md := md) kind) ci hci
    obtain ⟨r, hrm, hr⟩ := Key.pinIn_base (ConstantInfo.pinIn_name hp)
    unfold installBasisDecl
    simp only [ExPost.post_ite, ExPost.post_throw, ExPost.post_pure, imp_true_iff, and_true]
    exact ⟨fun hf' => Grows.push (Or.inr ⟨r, hrm, hr⟩) (by simpa using hf'), fun _ => by simp⟩
  unfold checkBasisDecl
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true,
    ExPost.post_pure]
  exact ⟨fun _ _ => foldlM_grows _ _ env step, fun _ => foldlM_grows _ _ env step⟩

end Values

/-! ## What a declaration installs -/

/-- **The install lemma**: an accepted declaration extends the environment only by
constants over its own names, or role keys. -/
theorem checkDecl_post (mode : CheckMode) (ops : (CheckerOps md) (CheckM md))
    (ev : Evidences md) (env : Env md) (d : Declaration md) :
    ExPost (checkDecl mode ops ev env d) (Grows (Over d.names) env) := by
  cases d with
  | defnDecl cv value hint =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    rw [ExPost.post_bind]
    refine ExPost.mono (fun env2 h2 => ?_) (checkDefnVal_post env cvA value hint)
    obtain ⟨v, rfl⟩ := h2
    have hg : Grows (Over (Declaration.names (.defnDecl cv value hint))) env
        ⟨.defnInfo cvA v hint :: env.consts⟩ :=
      Grows.push (Over.of_mem (by simp [Declaration.names, ConstantInfo.name,
        ConstantInfo.toConstantVal, h]))
        (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
    simp [hg]
    intro _ _ _ _
    split <;> simp [hg]
  | thmDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    refine ExPost.mono (fun e he => ?_) (checkThmVal_post env cvA value)
    obtain ⟨v, rfl⟩ := he
    exact Grows.push (Over.of_mem (by simp [Declaration.names, ConstantInfo.name,
      ConstantInfo.toConstantVal, h]))
      (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
  | opaqueDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    refine ExPost.mono (fun e he => ?_) (checkOpaqueVal_post env cvA value)
    subst he
    exact Grows.push (Over.of_mem (by simp [Declaration.names, ConstantInfo.name,
      ConstantInfo.toConstantVal, h]))
      (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
  | axiomDecl cv =>
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_pure, ExPost.post_throw, imp_true_iff, and_true,
      ExPost.post_bind]
    refine ⟨fun _ _ => Grows.refl _ env, fun _ => ?_⟩
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    have hg : Grows (Over (Declaration.names (.axiomDecl cv))) env
        ⟨.axiomInfo cvA :: env.consts⟩ :=
      Grows.push (Over.of_mem (by simp [Declaration.names, ConstantInfo.name,
        ConstantInfo.toConstantVal, h]))
        (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
    simp [hg, Grows.refl]
  | basisDecl kind =>
    unfold checkDecl
    exact checkBasisDecl_post _ env kind
  | indDecl block nP =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.of_forall fun _ => ?_
    split
    · exact checkBasisDecl_post _ env _
    · simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
      intro _
      have hn : Declaration.names (.indDecl block nP) = block.map (·.name) := rfl
      split
      · rename_i p hp
        obtain ⟨hT, hR, hC⟩ := nativeParts?_names hp
        rw [hn]
        exact checkNative_post env p (Over.of_mem hT) (Over.of_mem hR)
          (fun c hc => Over.of_mem (hC c hc)) ((Over.of_mem hT).auxKey _)
      · rw [hn]
        exact checkModeled_post env block
          (fun ci hci => Over.of_mem (List.mem_map_of_mem hci))
          (fun ci hci i => (Over.of_mem (List.mem_map_of_mem hci)).auxKey _)
  | quotDecl k cv =>
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
    intro _
    split <;> first | exact checkBasisDecl_post _ env _ | simp [Grows.refl]

end Ix.Kernel
