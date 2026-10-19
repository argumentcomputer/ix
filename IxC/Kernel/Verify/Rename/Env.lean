module

public import IxC.Kernel.Verify.Rename.ExprOps

@[expose] public section

/-!
# Renaming and the environment

`EnvRel P f env env'`: the renamed run's environment `env'` answers every
lookup of a good key as `env` does, renamed, and `env` stores good constants
at good keys. Renaming a good environment gives one (`EnvRel.mapKeys`);
locality is the case `f = id` with two environments that agree on a
covering set.

Then the core's fuel-free helpers over an environment
(`IxC/Kernel/CoreDefs.lean`): each one, at a renamed argument and the
related environment, is the original's answer, renamed where it is a
term.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}

/-! ## Inverting a renamed term's shape -/

namespace Expr

@[simp] theorem mapKeys_eq_fvar_iff {e : Expr md} {i : Nat} {t : Expr md'} :
    e.mapKeys f = .fvar i t ↔ ∃ t', e = .fvar i t' ∧ t = t'.mapKeys f := by
  constructor
  · intro h; cases e <;> simp at h
    obtain ⟨rfl, h2⟩ := h; exact ⟨_, rfl, h2.symm⟩
  · rintro ⟨t', rfl, rfl⟩; rfl

@[simp] theorem mapKeys_eq_const_iff {e : Expr md} {k : Key md'} {us : List Level} :
    e.mapKeys f = .const k us ↔ ∃ k', e = .const k' us ∧ k = k'.map f := by
  constructor
  · intro h; cases e <;> simp at h
    obtain ⟨h1, rfl⟩ := h; exact ⟨_, rfl, h1.symm⟩
  · rintro ⟨k', rfl, rfl⟩; rfl

@[simp] theorem mapKeys_eq_app_iff {e : Expr md} {a b : Expr md'} :
    e.mapKeys f = .app a b ↔ ∃ a' b', e = .app a' b' ∧ a = a'.mapKeys f ∧ b = b'.mapKeys f := by
  constructor
  · intro h; cases e <;> simp at h
    exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩
  · rintro ⟨a', b', rfl, rfl, rfl⟩; rfl

@[simp] theorem mapKeys_eq_lam_iff {e : Expr md} {a b : Expr md'} {m : BinderMeta} :
    e.mapKeys f = .lam a b m ↔
      ∃ a' b', e = .lam a' b' m ∧ a = a'.mapKeys f ∧ b = b'.mapKeys f := by
  constructor
  · intro h; cases e <;> simp at h
    obtain ⟨h1, h2, rfl⟩ := h; exact ⟨_, _, rfl, h1.symm, h2.symm⟩
  · rintro ⟨a', b', rfl, rfl, rfl⟩; rfl

@[simp] theorem mapKeys_eq_forallE_iff {e : Expr md} {a b : Expr md'} {m : BinderMeta} :
    e.mapKeys f = .forallE a b m ↔
      ∃ a' b', e = .forallE a' b' m ∧ a = a'.mapKeys f ∧ b = b'.mapKeys f := by
  constructor
  · intro h; cases e <;> simp at h
    obtain ⟨h1, h2, rfl⟩ := h; exact ⟨_, _, rfl, h1.symm, h2.symm⟩
  · rintro ⟨a', b', rfl, rfl, rfl⟩; rfl

@[simp] theorem mapKeys_eq_letE_iff {e : Expr md} {a v b : Expr md'} {l : LetMeta} :
    e.mapKeys f = .letE a v b l ↔
      ∃ a' v' b', e = .letE a' v' b' l ∧ a = a'.mapKeys f ∧ v = v'.mapKeys f ∧
        b = b'.mapKeys f := by
  constructor
  · intro h; cases e <;> simp at h
    obtain ⟨h1, h2, h3, rfl⟩ := h; exact ⟨_, _, _, rfl, h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨a', v', b', rfl, rfl, rfl, rfl⟩; rfl

@[simp] theorem mapKeys_eq_proj_iff {e : Expr md} {s : Key md'} {i : Nat} {x : Expr md'} :
    e.mapKeys f = .proj s i x ↔ ∃ s' x', e = .proj s' i x' ∧ s = s'.map f ∧ x = x'.mapKeys f := by
  constructor
  · intro h; cases e <;> simp at h
    obtain ⟨h1, rfl, h3⟩ := h; exact ⟨_, _, rfl, h1.symm, h3.symm⟩
  · rintro ⟨s', x', rfl, rfl, rfl⟩; rfl

@[simp] theorem fvar_eq_mapKeys_iff {e : Expr md} {i : Nat} {t : Expr md'} :
    Expr.fvar i t = e.mapKeys f ↔ ∃ t', e = .fvar i t' ∧ t = t'.mapKeys f := by
  rw [eq_comm]; exact mapKeys_eq_fvar_iff

@[simp] theorem const_eq_mapKeys_iff {e : Expr md} {k : Key md'} {us : List Level} :
    Expr.const k us = e.mapKeys f ↔ ∃ k', e = .const k' us ∧ k = k'.map f := by
  rw [eq_comm]; exact mapKeys_eq_const_iff

@[simp] theorem app_eq_mapKeys_iff {e : Expr md} {a b : Expr md'} :
    Expr.app a b = e.mapKeys f ↔ ∃ a' b', e = .app a' b' ∧ a = a'.mapKeys f ∧ b = b'.mapKeys f := by
  rw [eq_comm]; exact mapKeys_eq_app_iff

@[simp] theorem lam_eq_mapKeys_iff {e : Expr md} {a b : Expr md'} {m : BinderMeta} :
    Expr.lam a b m = e.mapKeys f ↔
      ∃ a' b', e = .lam a' b' m ∧ a = a'.mapKeys f ∧ b = b'.mapKeys f := by
  rw [eq_comm]; exact mapKeys_eq_lam_iff

@[simp] theorem forallE_eq_mapKeys_iff {e : Expr md} {a b : Expr md'} {m : BinderMeta} :
    Expr.forallE a b m = e.mapKeys f ↔
      ∃ a' b', e = .forallE a' b' m ∧ a = a'.mapKeys f ∧ b = b'.mapKeys f := by
  rw [eq_comm]; exact mapKeys_eq_forallE_iff

@[simp] theorem bvar_eq_mapKeys_iff {e : Expr md} {i : Nat} :
    Expr.bvar i = e.mapKeys f ↔ e = .bvar i := by
  rw [eq_comm]; exact mapKeys_eq_bvar_iff

@[simp] theorem sort_eq_mapKeys_iff {e : Expr md} {u : Level} :
    Expr.sort u = e.mapKeys f ↔ e = .sort u := by
  rw [eq_comm]; exact mapKeys_eq_sort_iff

/-- An application of renamed terms is the renamed application. -/
theorem app_mapKeys_fold (x y : Expr md) :
    Expr.app (x.mapKeys f) (y.mapKeys f) = (Expr.app x y).mapKeys f := rfl

end Expr

/-- Refute `h : t.mapKeys f = PAT'` against the fall-through hypothesis of
the original's match: invert `h` into an equation of `t` with the original
pattern (prenex, destructured, substituted), which `simp_all` refutes. -/
macro "shape_refute " h:ident : tactic => `(tactic| (
  simp only [Expr.mapKeys_eq_fvar_iff, Expr.mapKeys_eq_const_iff, Expr.mapKeys_eq_app_iff,
    Expr.mapKeys_eq_lam_iff, Expr.mapKeys_eq_forallE_iff, Expr.mapKeys_eq_letE_iff,
    Expr.mapKeys_eq_proj_iff, Expr.mapKeys_eq_bvar_iff, Expr.mapKeys_eq_sort_iff,
    Expr.mapKeys_eq_lit_iff, Expr.fvar_eq_mapKeys_iff, Expr.const_eq_mapKeys_iff,
    Expr.app_eq_mapKeys_iff, Expr.lam_eq_mapKeys_iff, Expr.forallE_eq_mapKeys_iff,
    Expr.bvar_eq_mapKeys_iff, Expr.sort_eq_mapKeys_iff] at $h:ident
  simp only [← exists_and_left, ← exists_and_right, and_assoc] at $h:ident
  repeat (obtain ⟨_, $h:ident⟩ := $h:ident)
  subst_vars
  first | solve_by_elim | simp_all))

/-- Close `(match t with pats) = (match t.mapKeys f with pats)`: split the
original's match; where it fires, the renamed one reduces; where it falls
through, a firing renamed match is refuted (`shape_refute`). -/
macro "shape_match" : tactic =>
  `(tactic| (split <;> first
    | (simp_all; done)
    | (split
       · rename_i h; exfalso; shape_refute h
       · rfl)))

/-! ## Related environments -/

/-- **The renamed run's environment**: on good keys it answers as `env`
does, renamed, and `env`'s constants at good keys are good; `f` is injective
on `P`. -/
structure EnvRel (P : md.Id → Prop) (f : md.Id → md'.Id) (env : Env md) (env' : Env md') :
    Prop where
  inj : InjOn f P
  find : ∀ k : Key md, k.Good P → env'.find? (k.map f) = (env.find? k).map (ConstantInfo.mapKeys f)
  good : ∀ (k : Key md) (c : ConstantInfo md), k.Good P → env.find? k = some c → c.Good P

/-- A good environment and its renaming are related. -/
theorem EnvRel.mapKeys {env : Env md} (hf : InjOn f P) (henv : env.Good P) :
    EnvRel P f env (env.mapKeys f) where
  inj := hf
  find _ hk := Env.find?_mapKeys hf henv hk
  good _ _ _ h := henv.find? h

/-- A role's lookup, renamed. -/
theorem EnvRel.find_role {env : Env md} {env' : Env md'} (h : EnvRel P f env env') (r : Role) :
    env'.find? (roleKey r) = (env.find? (roleKey r)).map (ConstantInfo.mapKeys f) :=
  h.find (roleKey r) trivial

/-- The good constant at a good key. -/
theorem EnvRel.good_of {env : Env md} {env' : Env md'} (h : EnvRel P f env env') {k : Key md}
    (hk : k.Good P) {c : ConstantInfo md} (hc : env.find? k = some c) : c.Good P :=
  h.good k c hk hc

/-- `isSome` of a lookup at a good key. -/
theorem EnvRel.find_isSome {env : Env md} {env' : Env md'} (h : EnvRel P f env env')
    {k : Key md} (hk : k.Good P) : (env'.find? (k.map f)).isSome = (env.find? k).isSome := by
  rw [h.find k hk]; cases env.find? k <;> rfl

/-- The projection-table lookup, renamed. -/
theorem EnvRel.findProj? {env : Env md} {env' : Env md'} (h : EnvRel P f env env')
    {T : Key md} (hT : T.Good P) (i : Nat) :
    env'.findProj? (T.map f) i = (env.findProj? T i).map (ProjEntry.mapKeys f) := by
  unfold Env.findProj?
  have hk := h.find (projTableName T) hT
  simp only [projTableName, auxKey, Key.map_aux] at hk ⊢
  rw [hk]
  cases env.find? (.aux T .projTable) with
  | none => rfl
  | some c =>
    cases c with
    | projInfo tbl =>
      simp only [Option.map_some, ConstantInfo.mapKeys]
      have hn : (tbl.mapKeys f).numFields = tbl.numFields := rfl
      rw [hn]
      split
      · simp [ProjTable.mapKeys_entry]
      · rfl
    | _ => rfl

/-- A projection-table entry at a good key is good. -/
theorem EnvRel.findProj?_good {env : Env md} {env' : Env md'} (h : EnvRel P f env env')
    {T : Key md} (hT : T.Good P) {i : Nat} {e : ProjEntry md}
    (he : env.findProj? T i = some e) : e.Good P := by
  unfold Env.findProj? at he
  cases hc : env.find? (projTableName T) with
  | none => rw [hc] at he; exact nomatch he
  | some c =>
    rw [hc] at he
    have hg := h.good (projTableName T) c hT hc
    cases c with
    | projInfo tbl =>
      simp only at he
      split at he
      · cases he; exact ProjTable.good_entry hg i
      · exact nomatch he
    | _ => exact nomatch he

end Ix.Kernel
