module

public import IxC.Kernel.Verify.Rename.Sim

@[expose] public section

/-!
# Renaming and the fast prop-ness readers

The head-symbol readers of `IxC/Kernel/PropRead.lean` answer alike at a
renamed term over a related lookup: they read the head's stored type
through `find?` and the binder data, which renaming keeps.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {env : Env md} {env' : Env md'}

@[simp] theorem Expr.peelNeverPis_mapKeys (n : Nat) (e : Expr md) :
    (e.mapKeys f).peelNeverPis n = (e.peelNeverPis n).map (Expr.mapKeys f) := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    cases e with
    | forallE t b m =>
      simp only [Expr.mapKeys, Expr.peelNeverPis]
      split <;> simp [ih]
    | _ => rfl

theorem Expr.Good.peelNeverPis {e : Expr md} (he : e.Good P) {n : Nat} {r : Expr md}
    (h : e.peelNeverPis n = some r) : r.Good P := by
  induction n generalizing e with
  | zero => cases h; exact he
  | succ n ih =>
    cases e with
    | forallE t b m =>
      simp only [Expr.peelNeverPis] at h
      split at h
      · exact ih he.2 h
      · exact nomatch h
    | _ => exact nomatch h

@[simp] theorem Expr.numArgs_mapKeys (e : Expr md) : (e.mapKeys f).numArgs = e.numArgs := by
  induction e <;> simp_all [Expr.numArgs]

@[simp] theorem residualPW_map (o : Option (Expr md)) :
    residualPW (o.map (Expr.mapKeys f)) = residualPW o := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;> rfl

@[simp] theorem ConstantInfo.isTowerEntry_mapKeys (c : ConstantInfo md) :
    (c.mapKeys f).isTowerEntry = c.isTowerEntry := by
  cases c <;> rfl

theorem headTypePW_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) (n : Nat) :
    headTypePW env'.find? (e.mapKeys f) n = headTypePW env.find? e n := by
  cases e with
  | const I us =>
    simp only [Expr.mapKeys, headTypePW]
    rw [hE.find I he]
    cases env.find? I with
    | none => rfl
    | some ci =>
      simp only [Option.map_some, ConstantInfo.isTowerEntry_mapKeys,
        ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_levelParams,
        ConstantVal.mapKeys_type, Expr.peelNeverPis_mapKeys, residualPW_map]
  | fvar i t =>
    simp only [Expr.mapKeys, headTypePW, Expr.peelNeverPis_mapKeys, residualPW_map]
  | _ => rfl

theorem typeSortPW_eq_head {find? : Key md → Option (ConstantInfo md)} {e : Expr md}
    (h1 : ∀ t b m, e ≠ .forallE t b m) (h2 : ∀ u, e ≠ .sort u) :
    typeSortPW find? e = headTypePW find? e.getAppFn e.numArgs := by
  cases e <;> first | rfl | (exact absurd rfl (h1 _ _ _)) | (exact absurd rfl (h2 _))

theorem typeSortPW_ren (hE : EnvRelG P f L env env') {T : Expr md} (hT : T.Good P) :
    typeSortPW env'.find? (T.mapKeys f) = typeSortPW env.find? T := by
  by_cases h1 : ∃ t b m, T = .forallE t b m
  · obtain ⟨t, b, m, rfl⟩ := h1; rfl
  by_cases h2 : ∃ u, T = .sort u
  · obtain ⟨u, rfl⟩ := h2; rfl
  have h1' : ∀ t b m, T ≠ .forallE t b m := fun t b m h => h1 ⟨t, b, m, h⟩
  have h2' : ∀ u, T ≠ .sort u := fun u h => h2 ⟨u, h⟩
  have h1'' : ∀ t b m, T.mapKeys f ≠ .forallE t b m := by
    intro t b m h
    rw [Expr.mapKeys_eq_forallE_iff] at h
    obtain ⟨_, _, hT', -⟩ := h
    exact h1' _ _ _ hT'
  have h2'' : ∀ u, T.mapKeys f ≠ .sort u := fun u h => h2' u (Expr.mapKeys_eq_sort_iff.mp h)
  rw [typeSortPW_eq_head h1'' h2'', typeSortPW_eq_head h1' h2', ← Expr.mapKeys_getAppFn,
    headTypePW_ren hE (Expr.Good.getAppFn hT), Expr.numArgs_mapKeys]

theorem headProofPW_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) :
    headProofPW env'.find? (e.mapKeys f) = headProofPW env.find? e := by
  cases e with
  | const c us =>
    simp only [Expr.mapKeys, headProofPW]
    rw [hE.find c he]
    cases hc : env.find? c with
    | none => rfl
    | some ci =>
      have hg := hE.good c ci he hc
      simp only [Option.map_some, ConstantInfo.isTowerEntry_mapKeys,
        ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_levelParams,
        ConstantVal.mapKeys_type, typeSortPW_ren hE hg.toConstantVal.2]
  | fvar i t =>
    simp only [Expr.mapKeys, headProofPW]
    exact typeSortPW_ren hE he
  | _ => rfl

theorem proofPW_eq_head {find? : Key md → Option (ConstantInfo md)} {e : Expr md}
    (h1 : ∀ t b m, e ≠ .lam t b m) : proofPW find? e = headProofPW find? e.getAppFn := by
  cases e <;> first | rfl | (exact absurd rfl (h1 _ _ _))

theorem proofPW_ren (hE : EnvRelG P f L env env') {a : Expr md} (ha : a.Good P) :
    proofPW env'.find? (a.mapKeys f) = proofPW env.find? a := by
  by_cases h1 : ∃ t b m, a = .lam t b m
  · obtain ⟨t, b, m, rfl⟩ := h1; rfl
  have h1' : ∀ t b m, a ≠ .lam t b m := fun t b m h => h1 ⟨t, b, m, h⟩
  have h1'' : ∀ t b m, a.mapKeys f ≠ .lam t b m := by
    intro t b m h
    rw [Expr.mapKeys_eq_lam_iff] at h
    obtain ⟨_, _, ha', -⟩ := h
    exact h1' _ _ _ ha'
  rw [proofPW_eq_head h1'', proofPW_eq_head h1', ← Expr.mapKeys_getAppFn,
    headProofPW_ren hE (Expr.Good.getAppFn ha)]

theorem notProofFast_ren (hE : EnvRelG P f L env env') {a : Expr md} (ha : a.Good P) :
    notProofFast env'.find? (a.mapKeys f) = notProofFast env.find? a := by
  simp only [notProofFast, proofPW_ren hE ha]

theorem isProofFast_ren (hE : EnvRelG P f L env env') {a : Expr md} (ha : a.Good P) :
    isProofFast env'.find? (a.mapKeys f) = isProofFast env.find? a := by
  simp only [isProofFast, proofPW_ren hE ha]

end Ix.Kernel
