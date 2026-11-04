module

public import IxC.Kernel.Verify.Rename.Install2
public import IxC.Kernel.Inductives.NativeInstall

@[expose] public section

/-!
# The renaming walk through the fixpoint route: the pure helpers (step 7.3, chunk (iii))

The field kinds (`recFamOk`, `recPositivity`, `recFieldKind`, `recCtorKinds`),
the capability record (`nativeCapsAt`, `nativeCaps`, `nativeRawRec`) and the
free-variable test (`Expr.mentionsFvar`) at renamed arguments. The kinds name
no key, so they are the original kinds.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

/-- `List.any` at functions that agree on the list's members. -/
theorem List.any_congr_mem' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem Expr.mentionsFvar_mapKeys (q : Nat) (e : Expr md) :
    (e.mapKeys f).mentionsFvar q = e.mentionsFvar q := by
  simp only [Expr.mentionsFvar, Expr.fvarLeaves_mapKeys, List.any_map]
  congr 1

/-- The family test at a renamed term. -/
theorem recFamOk_map (hf : InjOn f P) {T : Key md} (hT : T.Good P) (lps : List LevelParam)
    (nP nIdx o : Nat) {e : Expr md} (he : e.Good P) :
    recFamOk (T.map f) lps nP nIdx o (e.mapKeys f) = recFamOk T lps nP nIdx o e := by
  unfold recFamOk
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys, List.length_map, ← List.map_take,
    ← List.map_drop]
  have h1 : (Expr.const (T.map f) (lps.map Level.param) : Expr md') =
      (Expr.const T (lps.map Level.param) : Expr md).mapKeys f := rfl
  rw [h1, Expr.mapKeys_beq hf he.getAppFn (show Expr.Good P (Expr.const T _) from hT),
    ← structPsAt_map (f := f) o nP,
    list_beq_mapKeys hf (he.getAppArgs.take nP) (structPsAt_good o nP), List.all_map]
  congr 1
  apply List.all_congr_mem'
  intro a ha
  simp only [Function.comp, Expr.mentionsConst_map hf hT (he.getAppArgs.drop nP a ha)]

/-- `recPositivity`'s last clause (a term that is not a `∀`). -/
def recPositivityLeaf (T : Key md) (lps : List LevelParam) (nP nIdx o : Nat) (e : Expr md)
    (k : Nat) : RecFieldKind :=
  if !e.mentionsConst T then .ordinary
  else if e.getAppFn == Expr.const T (lps.map .param) then
    if e.getAppArgs.length == nP + nIdx && e.getAppArgs.take nP == structPsAt (o + k) nP then
      (if recFamOk T lps nP nIdx (o + k) e then
        (if k == 0 then .recursive else .reflexive)
       else .negative)
    else .negative
  else
    match e.getAppFn with
    | .const T' _ => if T' == T then .negative else .unsupported
    | _ => .unsupported

theorem recPositivity_leaf (T : Key md) (lps : List LevelParam) (nP nIdx o : Nat) :
    ∀ (e : Expr md) (k : Nat), (∀ dom body bm, e ≠ .forallE dom body bm) →
      recPositivity T lps nP nIdx o e k = recPositivityLeaf T lps nP nIdx o e k
  | .forallE dom body bm, _, h => absurd rfl (h dom body bm)
  | .bvar _, _, _ | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .app _ _, _, _
  | .lam _ _ _, _, _ | .letE _ _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => rfl

theorem recPositivityLeaf_map (hf : InjOn f P) {T : Key md} (hT : T.Good P)
    (lps : List LevelParam) (nP nIdx o : Nat) {e : Expr md} (he : e.Good P) (k : Nat) :
    recPositivityLeaf (T.map f) lps nP nIdx o (e.mapKeys f) k =
      recPositivityLeaf T lps nP nIdx o e k := by
  unfold recPositivityLeaf
  rw [Expr.mentionsConst_map hf hT he, ← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys,
    List.length_map, ← List.map_take, recFamOk_map hf hT lps nP nIdx (o + k) he]
  have h1 : (Expr.const (T.map f) (lps.map Level.param) : Expr md') =
      (Expr.const T (lps.map Level.param) : Expr md).mapKeys f := rfl
  rw [h1, Expr.mapKeys_beq hf he.getAppFn (show Expr.Good P (Expr.const T _) from hT),
    ← structPsAt_map (f := f) (o + k) nP,
    list_beq_mapKeys hf (he.getAppArgs.take nP) (structPsAt_good (o + k) nP)]
  have hg := he.getAppFn
  generalize e.getAppFn = g at hg ⊢
  cases g with
  | const T' us =>
    simp only [Expr.mapKeys, Key.map_beq hf hg hT]
  | _ => rfl

theorem Expr.mapKeys_ne_forallE {e : Expr md} (h : ∀ dom body bm, e ≠ .forallE dom body bm) :
    ∀ dom body bm, (e.mapKeys f) ≠ .forallE dom body bm := by
  intro dom body bm he
  cases e with
  | forallE d b m => exact h d b m rfl
  | _ => simp [Expr.mapKeys] at he

/-- **Official's positivity walk at a renamed domain** answers alike. -/
theorem recPositivity_map (hf : InjOn f P) {T : Key md} (hT : T.Good P) (lps : List LevelParam)
    (nP nIdx o : Nat) : ∀ (e : Expr md) (k : Nat), e.Good P →
      recPositivity (T.map f) lps nP nIdx o (e.mapKeys f) k = recPositivity T lps nP nIdx o e k
  | .forallE dom body bm, k, he => by
    simp only [Expr.Good] at he
    simp only [Expr.mapKeys, recPositivity, Expr.mentionsConst_map hf hT he.1,
      recPositivity_map hf hT lps nP nIdx o body (k + 1) he.2]
  | e, k, he => by
    by_cases hpi : ∃ dom body bm, e = .forallE dom body bm
    · obtain ⟨dom, body, bm, rfl⟩ := hpi
      simp only [Expr.Good] at he
      simp only [Expr.mapKeys, recPositivity, Expr.mentionsConst_map hf hT he.1,
        recPositivity_map hf hT lps nP nIdx o body (k + 1) he.2]
    · have hne : ∀ dom body bm, e ≠ .forallE dom body bm := fun d b m h => hpi ⟨d, b, m, h⟩
      rw [recPositivity_leaf _ _ _ _ _ _ _ (Expr.mapKeys_ne_forallE hne),
        recPositivity_leaf _ _ _ _ _ _ _ hne]
      exact recPositivityLeaf_map hf hT lps nP nIdx o he k

theorem recFieldKind_map (hf : InjOn f P) {T : Key md} (hT : T.Good P) (lps : List LevelParam)
    (nP nIdx o : Nat) {dom : Expr md} (hd : dom.Good P) :
    recFieldKind (T.map f) lps nP nIdx o (dom.mapKeys f) = recFieldKind T lps nP nIdx o dom := by
  unfold recFieldKind
  rw [Expr.mentionsConst_map hf hT hd, recPositivity_map hf hT lps nP nIdx o dom 0 hd]

/-- **The field kinds of a renamed constructor are its kinds.** -/
theorem recCtorKinds_map (hf : InjOn f P) {T : Key md} (hT : T.Good P) (lps : List LevelParam)
    (nP nIdx : Nat) {c : ConstantVal md × Nat} (hc : c.1.Good P) :
    recCtorKinds (T.map f) lps nP nIdx (c.1.mapKeys f, c.2) = recCtorKinds T lps nP nIdx c := by
  unfold recCtorKinds
  simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
  cases h : Expr.stripPis (nP + c.2) c.1.type with
  | none => rfl
  | some q =>
    obtain ⟨cbs, cbody⟩ := q
    obtain ⟨hbs, hb⟩ := Expr.stripPis_good hc.2 h
    simp only [Option.map_some, Expr.mapTele, Expr.mapBinders_getD, structUsedLater_map,
      Expr.getAppArgs_mapKeys, ← List.map_drop, List.all_map]
    have hks : ∀ i, recFieldKind (T.map f) lps nP nIdx i
        ((cbs.getD (nP + i) default).1.mapKeys f) =
          recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 :=
      fun i => recFieldKind_map hf hT lps nP nIdx i (hbs.getD (nP + i))
    simp only [hks]
    have hall : (cbody.getAppArgs.drop nP).all
        ((fun a => !a.mentionsConst (T.map f)) ∘ Expr.mapKeys f) =
          (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) := by
      apply List.all_congr_mem'
      intro a ha
      simp only [Function.comp, Expr.mentionsConst_map hf hT (hb.getAppArgs.drop nP a ha)]
    rw [hall]

/-! ## The capability record -/

theorem nativeCapsAt_map (p : InductiveShape md) (isRec : Bool) :
    nativeCapsAt (p.mapKeys f) isRec = (nativeCapsAt p isRec).mapKeys f := by
  unfold nativeCapsAt
  simp only [InductiveShape.mapKeys]
  rcases p.ctors with _ | ⟨c, _ | _⟩ <;> rfl

theorem nativeCapsAt_good {p : InductiveShape md} (hp : p.Good P) (isRec : Bool) :
    (nativeCapsAt p isRec).Good P := by
  unfold nativeCapsAt
  have hcs := hp.ctors
  rcases hpc : p.ctors with _ | ⟨c, _ | _⟩
  · intro k hk; simp at hk
  · intro k hk
    simp only [Option.mem_def, Option.some.injEq] at hk
    rw [← hk]
    exact (hcs c (by rw [hpc]; exact List.mem_cons_self)).1
  · intro k hk; simp at hk

theorem nativeCaps_map (p : NativeParts md) :
    nativeCaps (p.mapKeys f) = (nativeCaps p).mapKeys f :=
  nativeCapsAt_map p.toInductiveShape _

theorem nativeRawRec_map (hf : InjOn f P) {p : NativeParts md} (hp : p.Good P) :
    nativeRawRec (p.mapKeys f) = nativeRawRec p := by
  unfold nativeRawRec
  simp only [NativeParts.mapKeys_toInductiveShape, InductiveShape.mapKeys]
  have hcs := hp.ctors
  rcases hpc : p.ctors with _ | ⟨c, _ | _⟩
  · rfl
  · have hc : c.1.Good P := hcs c (by rw [hpc]; exact List.mem_cons_self)
    simp only [List.map_cons, List.map_nil, ConstantVal.mapKeys_type, Expr.stripPis_mapKeys,
      ConstantVal.mapKeys_name]
    cases h : Expr.stripPis (p.nP + c.2) c.1.type with
    | none => rfl
    | some q =>
      obtain ⟨cbs, _⟩ := q
      obtain ⟨hbs, _⟩ := Expr.stripPis_good hc.2 h
      simp only [Option.map_some, Expr.mapTele, Expr.mapBinders, ← List.map_drop, List.any_map]
      apply List.any_congr_mem'
      intro b hb
      simp only [Function.comp]
      exact Expr.mentionsConst_map hf hp.cvT.1 (hbs b (List.mem_of_mem_drop hb))
  · rfl

end Ix.Kernel
