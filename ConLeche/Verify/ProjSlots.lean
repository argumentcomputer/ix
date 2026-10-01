module

public import ConLeche.Verify.Abstract

public section

/-!
# Projection nodes and their table slots (task #175 wiring, W4c S6)

The tower-cons transport's syntactic side condition.  Consing a
tower-backed entry `(T, i)` changes the reading of exactly one node
shape — `.proj T i e` with *no* entry stored (the pair fallback) —
so a prefix reading survives the cons whenever the subject has **no
`.proj T i` node** (`Expr.NoProjAt`).  Two sources discharge it for
every stored expression:

* `noProjAt_of_constsResolve` — a resolving expression names only
  stored structures in its `.proj` nodes (`constsResolve`'s clause
  reads `find? s`), so when `T` is not stored there is no `.proj T _`
  node at all: the pre-block constants;
* `annotateCore_projSlotsOk` — the annotation pass emits a `.proj`
  node only where a *tower* table entry types it
  (`annotateCore_proj_inv`'s first arm; the other arm rewrites the
  node away and re-annotates), hereditarily through the fvar types
  the pass threads (`Expr.ProjSlotsOk`).  So an annotated expression
  has no `.proj T i` node when the slot `(T, i)` was empty at
  annotation time (`ProjSlotsOk.noProjAt`): the block's own
  constants, annotated before their entries exist.

Both predicates are hereditary through `.fvar` type annotations, as
`ConstsBound` is, because `denoteMeta` opens binders at annotated fvars.
-/

namespace ConLeche

open ConLeche.Expr

/-! ## `NoProjAt` -/

/-- No `.proj T i` node, hereditarily (through fvar types). -/
@[expose] def Expr.NoProjAt (T : Name) (i : Nat) : Expr → Prop
  | .proj s j e => ¬ (s = T ∧ j = i) ∧ NoProjAt T i e
  | .app f a => NoProjAt T i f ∧ NoProjAt T i a
  | .lam ty b _ => NoProjAt T i ty ∧ NoProjAt T i b
  | .forallE ty b _ => NoProjAt T i ty ∧ NoProjAt T i b
  | .letE t v b => NoProjAt T i t ∧ NoProjAt T i v ∧ NoProjAt T i b
  | .fvar _ ty => NoProjAt T i ty
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

namespace Expr

variable {T : Name} {i : Nat}

@[simp] theorem noProjAt_proj {s : Name} {j : Nat} {e : Expr} :
    NoProjAt T i (.proj s j e) ↔ ¬ (s = T ∧ j = i) ∧ NoProjAt T i e := by
  rw [NoProjAt]
@[simp] theorem noProjAt_app {f a : Expr} :
    NoProjAt T i (.app f a) ↔ NoProjAt T i f ∧ NoProjAt T i a := by
  rw [NoProjAt]
@[simp] theorem noProjAt_lam {ty b : Expr} {m : BinderMeta} :
    NoProjAt T i (.lam ty b m) ↔ NoProjAt T i ty ∧ NoProjAt T i b := by
  rw [NoProjAt]
@[simp] theorem noProjAt_forallE {ty b : Expr} {m : BinderMeta} :
    NoProjAt T i (.forallE ty b m) ↔ NoProjAt T i ty ∧ NoProjAt T i b := by
  rw [NoProjAt]
@[simp] theorem noProjAt_letE {t v b : Expr} :
    NoProjAt T i (.letE t v b) ↔
      NoProjAt T i t ∧ NoProjAt T i v ∧ NoProjAt T i b := by
  rw [NoProjAt]
@[simp] theorem noProjAt_fvar {idx : Nat} {ty : Expr} :
    NoProjAt T i (.fvar idx ty) ↔ NoProjAt T i ty := by
  rw [NoProjAt]
@[simp] theorem noProjAt_bvar {j : Nat} : NoProjAt T i (.bvar j) := by
  rw [NoProjAt] <;> simp
@[simp] theorem noProjAt_sort {u : Level} : NoProjAt T i (.sort u) := by
  rw [NoProjAt] <;> simp
@[simp] theorem noProjAt_const {n : Name} {us : List Level} :
    NoProjAt T i (.const n us) := by
  rw [NoProjAt] <;> simp
@[simp] theorem noProjAt_lit {l : Literal} : NoProjAt T i (.lit l) := by
  rw [NoProjAt] <;> simp

/-- Instantiation preserves the absence: every node of the result is a
node of the body or of the substituted term. -/
theorem NoProjAt.instantiate1 {v : Expr} (hv : NoProjAt T i v) :
    ∀ (e : Expr) (d : Nat), NoProjAt T i e →
      NoProjAt T i (e.instantiate1 v d) := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [Expr.instantiate1]
    split
    · exact hv
    · split <;> simp
  | sort u => intro d _; rw [Expr.instantiate1]; simp
  | const n us => intro d h; rw [Expr.instantiate1]; exact h
  | fvar idx ty => intro d h; rw [Expr.instantiate1]; exact h
  | lit l => intro d _; rw [Expr.instantiate1]; simp
  | app f a ihf iha =>
    intro d h
    rw [noProjAt_app] at h
    rw [Expr.instantiate1, noProjAt_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [noProjAt_lam] at h
    rw [Expr.instantiate1, noProjAt_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [noProjAt_forallE] at h
    rw [Expr.instantiate1, noProjAt_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [noProjAt_letE] at h
    rw [Expr.instantiate1, noProjAt_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d h
    rw [noProjAt_proj] at h
    rw [Expr.instantiate1, noProjAt_proj]
    exact ⟨h.1, ihe d h.2⟩

/-- Level instantiation moves no node. -/
theorem NoProjAt.instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, NoProjAt T i e →
      NoProjAt T i (e.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | bvar j => intro _; simp [Expr.instantiateLevelParams]
  | sort u => intro _; simp [Expr.instantiateLevelParams]
  | const n vs => intro _; simp [Expr.instantiateLevelParams]
  | lit l => intro _; simp [Expr.instantiateLevelParams]
  | fvar idx ty ih =>
    intro h
    rw [noProjAt_fvar] at h
    rw [Expr.instantiateLevelParams, noProjAt_fvar]
    exact ih h
  | app f a ihf iha =>
    intro h
    rw [noProjAt_app] at h
    rw [Expr.instantiateLevelParams, noProjAt_app]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro h
    rw [noProjAt_lam] at h
    rw [Expr.instantiateLevelParams, noProjAt_lam]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro h
    rw [noProjAt_forallE] at h
    rw [Expr.instantiateLevelParams, noProjAt_forallE]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE t val b iht ihval ihb =>
    intro h
    rw [noProjAt_letE] at h
    rw [Expr.instantiateLevelParams, noProjAt_letE]
    exact ⟨iht h.1, ihval h.2.1, ihb h.2.2⟩
  | proj s j e ihe =>
    intro h
    rw [noProjAt_proj] at h
    rw [Expr.instantiateLevelParams, noProjAt_proj]
    exact ⟨h.1, ihe h.2⟩

/-- Abstraction drops fvar nodes and moves nothing else. -/
theorem NoProjAt.abstract1 :
    ∀ (e : Expr) (d k : Nat), NoProjAt T i e →
      NoProjAt T i (e.abstract1 d k) := by
  intro e
  induction e with
  | bvar j => intro d k _; simp [Expr.abstract1]
  | sort u => intro d k _; simp [Expr.abstract1]
  | const n vs => intro d k _; simp [Expr.abstract1]
  | lit l => intro d k _; simp [Expr.abstract1]
  | fvar idx ty ih =>
    intro d k h
    rw [Expr.abstract1]
    split
    · simp
    · exact h
  | app f a ihf iha =>
    intro d k h
    rw [noProjAt_app] at h
    rw [Expr.abstract1, noProjAt_app]
    exact ⟨ihf d k h.1, iha d k h.2⟩
  | lam ty b m ihty ihb =>
    intro d k h
    rw [noProjAt_lam] at h
    rw [Expr.abstract1, noProjAt_lam]
    exact ⟨ihty d k h.1, ihb d (k + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d k h
    rw [noProjAt_forallE] at h
    rw [Expr.abstract1, noProjAt_forallE]
    exact ⟨ihty d k h.1, ihb d (k + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d k h
    rw [noProjAt_letE] at h
    rw [Expr.abstract1, noProjAt_letE]
    exact ⟨iht d k h.1, ihval d k h.2.1, ihb d (k + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d k h
    rw [noProjAt_proj] at h
    rw [Expr.abstract1, noProjAt_proj]
    exact ⟨h.1, ihe d k h.2⟩

/-- **The pre-block source**: a resolving expression names only stored
structures in its `.proj` nodes, so an unstored `T` occurs in none. -/
theorem noProjAt_of_constsResolve {env : Env} (hT : env.find? T = none) :
    ∀ e : Expr, e.constsResolve env = true → NoProjAt T i e := by
  intro e
  induction e with
  | bvar j => intro _; simp
  | sort u => intro _; simp
  | lit l => intro _; simp
  | const n us => intro _; simp
  | fvar idx ty ih =>
    intro h
    rw [noProjAt_fvar]
    exact ih (by simpa [Expr.constsResolve] using h)
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b mb ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b mb ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE ty v b ihty ihv ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_letE.mpr ⟨ihty h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s j e ihe =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    refine noProjAt_proj.mpr ⟨?_, ihe h.2⟩
    rintro ⟨rfl, -⟩
    rw [hT] at h
    exact nomatch h.1

/-! ## `ProjSlotsOk` and `FvarTysOk` -/

/-- Every `.proj s j` node's slot holds a projection-table entry,
hereditarily (through fvar types). -/
def ProjSlotsOk (env : Env) : Expr → Prop
  | .proj s j e => (∃ entry : ProjEntry, env.findProj? s j = some entry) ∧
      ProjSlotsOk env e
  | .app f a => ProjSlotsOk env f ∧ ProjSlotsOk env a
  | .lam ty b _ => ProjSlotsOk env ty ∧ ProjSlotsOk env b
  | .forallE ty b _ => ProjSlotsOk env ty ∧ ProjSlotsOk env b
  | .letE t v b => ProjSlotsOk env t ∧ ProjSlotsOk env v ∧ ProjSlotsOk env b
  | .fvar _ ty => ProjSlotsOk env ty
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Every fvar node's type annotation is `ProjSlotsOk` (the annotation
pass's input discipline: it threads annotated fvars and copies fvar
nodes verbatim). -/
def FvarTysOk (env : Env) : Expr → Prop
  | .fvar _ ty => ProjSlotsOk env ty
  | .proj _ _ e => FvarTysOk env e
  | .app f a => FvarTysOk env f ∧ FvarTysOk env a
  | .lam ty b _ => FvarTysOk env ty ∧ FvarTysOk env b
  | .forallE ty b _ => FvarTysOk env ty ∧ FvarTysOk env b
  | .letE t v b => FvarTysOk env t ∧ FvarTysOk env v ∧ FvarTysOk env b
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

variable {env : Env}

@[simp] theorem projSlotsOk_proj {s : Name} {j : Nat} {e : Expr} :
    ProjSlotsOk env (.proj s j e) ↔
      (∃ entry : ProjEntry, env.findProj? s j = some entry) ∧
        ProjSlotsOk env e := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_app {f a : Expr} :
    ProjSlotsOk env (.app f a) ↔ ProjSlotsOk env f ∧ ProjSlotsOk env a := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_lam {ty b : Expr} {m : BinderMeta} :
    ProjSlotsOk env (.lam ty b m) ↔
      ProjSlotsOk env ty ∧ ProjSlotsOk env b := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_forallE {ty b : Expr}
    {m : BinderMeta} :
    ProjSlotsOk env (.forallE ty b m) ↔
      ProjSlotsOk env ty ∧ ProjSlotsOk env b := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_letE {t v b : Expr} :
    ProjSlotsOk env (.letE t v b) ↔
      ProjSlotsOk env t ∧ ProjSlotsOk env v ∧ ProjSlotsOk env b := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_fvar {idx : Nat} {ty : Expr} :
    ProjSlotsOk env (.fvar idx ty) ↔ ProjSlotsOk env ty := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_bvar {j : Nat} : ProjSlotsOk env (.bvar j) := by
  rw [ProjSlotsOk] <;> simp
@[simp] theorem projSlotsOk_sort {u : Level} : ProjSlotsOk env (.sort u) := by
  rw [ProjSlotsOk] <;> simp
@[simp] theorem projSlotsOk_const {n : Name} {us : List Level} :
    ProjSlotsOk env (.const n us) := by
  rw [ProjSlotsOk] <;> simp
@[simp] theorem projSlotsOk_lit {l : Literal} : ProjSlotsOk env (.lit l) := by
  rw [ProjSlotsOk] <;> simp

@[simp] theorem fvarTysOk_fvar {idx : Nat} {ty : Expr} :
    FvarTysOk env (.fvar idx ty) ↔ ProjSlotsOk env ty := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_proj {s : Name} {j : Nat} {e : Expr} :
    FvarTysOk env (.proj s j e) ↔ FvarTysOk env e := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_app {f a : Expr} :
    FvarTysOk env (.app f a) ↔ FvarTysOk env f ∧ FvarTysOk env a := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_lam {ty b : Expr} {m : BinderMeta} :
    FvarTysOk env (.lam ty b m) ↔ FvarTysOk env ty ∧ FvarTysOk env b := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_forallE {ty b : Expr} {m : BinderMeta} :
    FvarTysOk env (.forallE ty b m) ↔
      FvarTysOk env ty ∧ FvarTysOk env b := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_letE {t v b : Expr} :
    FvarTysOk env (.letE t v b) ↔
      FvarTysOk env t ∧ FvarTysOk env v ∧ FvarTysOk env b := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_bvar {j : Nat} : FvarTysOk env (.bvar j) := by
  rw [FvarTysOk] <;> simp
@[simp] theorem fvarTysOk_sort {u : Level} : FvarTysOk env (.sort u) := by
  rw [FvarTysOk] <;> simp
@[simp] theorem fvarTysOk_const {n : Name} {us : List Level} :
    FvarTysOk env (.const n us) := by
  rw [FvarTysOk] <;> simp
@[simp] theorem fvarTysOk_lit {l : Literal} : FvarTysOk env (.lit l) := by
  rw [FvarTysOk] <;> simp

/-- A closed (fvar-free) expression satisfies the input discipline
vacuously. -/
theorem FvarTysOk.of_not_hasFvar :
    ∀ e : Expr, e.hasFvar = false → FvarTysOk env e := by
  intro e
  induction e with
  | bvar j => intro _; simp
  | sort u => intro _; simp
  | const n us => intro _; simp
  | lit l => intro _; simp
  | fvar idx ty => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_letE.mpr ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s j e ihe =>
    intro h
    exact fvarTysOk_proj.mpr (ihe (by simpa [Expr.hasFvar] using h))

/-- Every fvar leaf of a `ProjSlotsOk` expression carries a
`ProjSlotsOk` type. -/
theorem ProjSlotsOk.fvarLeaves :
    ∀ e : Expr, ProjSlotsOk env e →
      ∀ l ∈ e.fvarLeaves, ProjSlotsOk env l.2 := by
  intro e
  induction e with
  | bvar j => intro _ l hl; simp [Expr.fvarLeaves] at hl
  | sort u => intro _ l hl; simp [Expr.fvarLeaves] at hl
  | const n us => intro _ l hl; simp [Expr.fvarLeaves] at hl
  | lit l' => intro _ l hl; simp [Expr.fvarLeaves] at hl
  | fvar idx ty ih =>
    intro h l hl
    rw [projSlotsOk_fvar] at h
    rw [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact h
    · exact ih h l hl
  | app f a ihf iha =>
    intro h l hl
    rw [projSlotsOk_app] at h
    rw [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf h.1 l hl
    · exact iha h.2 l hl
  | lam ty b m ihty ihb =>
    intro h l hl
    rw [projSlotsOk_lam] at h
    rw [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty h.1 l hl
    · exact ihb h.2 l hl
  | forallE ty b m ihty ihb =>
    intro h l hl
    rw [projSlotsOk_forallE] at h
    rw [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty h.1 l hl
    · exact ihb h.2 l hl
  | letE t v b iht ihv ihb =>
    intro h l hl
    rw [projSlotsOk_letE] at h
    rw [Expr.fvarLeaves, List.mem_append, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht h.1 l hl
    · exact ihv h.2.1 l hl
    · exact ihb h.2.2 l hl
  | proj s j e ihe =>
    intro h l hl
    rw [projSlotsOk_proj] at h
    rw [Expr.fvarLeaves] at hl
    exact ihe h.2 l hl

/-- Instantiation keeps the input discipline when the substituted term
has it. -/
theorem FvarTysOk.instantiate1 {v : Expr} (hv : FvarTysOk env v) :
    ∀ (e : Expr) (d : Nat), FvarTysOk env e →
      FvarTysOk env (e.instantiate1 v d) := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [Expr.instantiate1]
    split
    · exact hv
    · split <;> simp
  | sort u => intro d _; rw [Expr.instantiate1]; simp
  | const n us => intro d h; rw [Expr.instantiate1]; exact h
  | fvar idx ty => intro d h; rw [Expr.instantiate1]; exact h
  | lit l => intro d _; rw [Expr.instantiate1]; simp
  | app f a ihf iha =>
    intro d h
    rw [fvarTysOk_app] at h
    rw [Expr.instantiate1, fvarTysOk_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [fvarTysOk_lam] at h
    rw [Expr.instantiate1, fvarTysOk_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [fvarTysOk_forallE] at h
    rw [Expr.instantiate1, fvarTysOk_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [fvarTysOk_letE] at h
    rw [Expr.instantiate1, fvarTysOk_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d h
    rw [fvarTysOk_proj] at h
    rw [Expr.instantiate1, fvarTysOk_proj]
    exact ihe d h

/-- Abstraction drops fvar nodes and keeps every slot fact. -/
theorem ProjSlotsOk.abstract1 :
    ∀ (e : Expr) (d k : Nat), ProjSlotsOk env e →
      ProjSlotsOk env (e.abstract1 d k) := by
  intro e
  induction e with
  | bvar j => intro d k _; simp [Expr.abstract1]
  | sort u => intro d k _; simp [Expr.abstract1]
  | const n vs => intro d k _; simp [Expr.abstract1]
  | lit l => intro d k _; simp [Expr.abstract1]
  | fvar idx ty _ =>
    intro d k h
    rw [Expr.abstract1]
    split
    · simp
    · exact h
  | app f a ihf iha =>
    intro d k h
    rw [projSlotsOk_app] at h
    rw [Expr.abstract1, projSlotsOk_app]
    exact ⟨ihf d k h.1, iha d k h.2⟩
  | lam ty b m ihty ihb =>
    intro d k h
    rw [projSlotsOk_lam] at h
    rw [Expr.abstract1, projSlotsOk_lam]
    exact ⟨ihty d k h.1, ihb d (k + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d k h
    rw [projSlotsOk_forallE] at h
    rw [Expr.abstract1, projSlotsOk_forallE]
    exact ⟨ihty d k h.1, ihb d (k + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d k h
    rw [projSlotsOk_letE] at h
    rw [Expr.abstract1, projSlotsOk_letE]
    exact ⟨iht d k h.1, ihval d k h.2.1, ihb d (k + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d k h
    rw [projSlotsOk_proj] at h
    rw [Expr.abstract1, projSlotsOk_proj]
    exact ⟨h.1, ihe d k h.2⟩

/-- **The annotation source**: an occupied slot at every `.proj` node
means an *empty* slot's node is absent. -/
theorem ProjSlotsOk.noProjAt (hslot : env.findProj? T i = none) :
    ∀ e : Expr, ProjSlotsOk env e → NoProjAt T i e := by
  intro e
  induction e with
  | bvar j => intro _; simp
  | sort u => intro _; simp
  | const n us => intro _; simp
  | lit l => intro _; simp
  | fvar idx ty ih =>
    intro h
    rw [projSlotsOk_fvar] at h
    exact noProjAt_fvar.mpr (ih h)
  | app f a ihf iha =>
    intro h
    rw [projSlotsOk_app] at h
    exact noProjAt_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro h
    rw [projSlotsOk_lam] at h
    exact noProjAt_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro h
    rw [projSlotsOk_forallE] at h
    exact noProjAt_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h
    rw [projSlotsOk_letE] at h
    exact noProjAt_letE.mpr ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s j e ihe =>
    intro h
    rw [projSlotsOk_proj] at h
    obtain ⟨⟨entry, hfe⟩, he⟩ := h
    refine noProjAt_proj.mpr ⟨?_, ihe he⟩
    rintro ⟨rfl, rfl⟩
    rw [hslot] at hfe
    exact nomatch hfe

end Expr

/-! ## The annotation pass emits only slotted projection nodes -/

variable (mode : CheckMode)

/-- **The annotation walk**: every `.proj` node of an annotated
expression sits at a tower table slot (hereditarily), provided the
input's fvar annotations do — which is vacuous for the checker's
closed inputs and preserved by the pass's own openings. -/
theorem annotateCore_projSlotsOk {env : Env} :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore mode env fuel d e = .ok e' → Expr.FvarTysOk env e →
      Expr.ProjSlotsOk env e'
  | 0, _, _, _, h, _ => by simp [annotateCore_zero, throw, throwThe,
      MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]; simp
  | fuel + 1, .fvar idx ty, d, e', h, hf => by
    rw [annotateCore_succ] at h
    simp only [annotateBody] at h
    revert h
    split
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
      exact Expr.projSlotsOk_fvar.mpr (Expr.fvarTysOk_fvar.mp hf)
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .sort u, d, e', h, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]; simp
  | fuel + 1, .const n us, d, e', h, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]; simp
  | fuel + 1, .lit l, d, e', h, _ => by
    rw [annotateCore_succ] at h
    match l, h with
    | .natVal n, h => ?natCase
    | .strVal sv, h => ?strCase
    case strCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]; simp
    case natCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]; simp
  | fuel + 1, .app f a, d, e', h, hf => by
    rw [Expr.fvarTysOk_app] at hf
    obtain ⟨f', a', hfa, haa, rfl⟩ := annotateCore_app_inv h
    exact Expr.projSlotsOk_app.mpr
      ⟨annotateCore_projSlotsOk fuel f hfa hf.1,
        annotateCore_projSlotsOk fuel a haa hf.2⟩
  | fuel + 1, .proj sn i e, d, e', h, hf => by
    rw [Expr.fvarTysOk_proj] at hf
    obtain ⟨e₂, tt, te, he, -, -, T, us, entry, -, hfe, -, rfl⟩ :=
      annotateCore_proj_inv h
    have hok₂ := annotateCore_projSlotsOk fuel e he hf
    exact Expr.projSlotsOk_proj.mpr ⟨⟨entry, hfe⟩, hok₂⟩
  | fuel + 1, .forallE ty body m, d, e', h, hf => by
    rw [Expr.fvarTysOk_forallE] at hf
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_forallE_inv h
    have hty'ok := annotateCore_projSlotsOk fuel ty hty hf.1
    have hbody'ok := annotateCore_projSlotsOk fuel
      (body.instantiate1 (.fvar d ty')) hbody
      (Expr.FvarTysOk.instantiate1 (Expr.fvarTysOk_fvar.mpr hty'ok) body 0 hf.2)
    exact Expr.projSlotsOk_forallE.mpr
      ⟨hty'ok, Expr.ProjSlotsOk.abstract1 body' d 0 hbody'ok⟩
  | fuel + 1, .lam ty body m, d, e', h, hf => by
    rw [Expr.fvarTysOk_lam] at hf
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_lam_inv h
    have hty'ok := annotateCore_projSlotsOk fuel ty hty hf.1
    have hbody'ok := annotateCore_projSlotsOk fuel
      (body.instantiate1 (.fvar d ty')) hbody
      (Expr.FvarTysOk.instantiate1 (Expr.fvarTysOk_fvar.mpr hty'ok) body 0 hf.2)
    exact Expr.projSlotsOk_lam.mpr
      ⟨hty'ok, Expr.ProjSlotsOk.abstract1 body' d 0 hbody'ok⟩
  | fuel + 1, .letE ty v b, d, e', h, hf => by
    rw [Expr.fvarTysOk_letE] at hf
    obtain ⟨ty', v', -, -, hb, -⟩ := annotateCore_letE_inv h
    exact annotateCore_projSlotsOk fuel _ hb
      (Expr.FvarTysOk.instantiate1 hf.2.1 b 0 hf.2.2)

/-- **The block-side source, packaged**: an expression annotated from a
closed input at an environment where the slot `(T, i)` is empty has no
`.proj T i` node. -/
theorem annotateCore_noProjAt {env : Env} {fuel d : Nat} {e e' : Expr}
    {T : Name} {i : Nat}
    (h : annotateCore mode env fuel d e = .ok e') (hfv : e.hasFvar = false)
    (hslot : env.findProj? T i = none) :
    Expr.NoProjAt T i e' :=
  Expr.ProjSlotsOk.noProjAt hslot e'
    (annotateCore_projSlotsOk mode fuel e h (Expr.FvarTysOk.of_not_hasFvar e hfv))

end ConLeche
