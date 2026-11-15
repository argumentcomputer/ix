module

public import IxC.Kernel.CoreDefs

@[expose] public section

namespace Ix.Kernel.Expr

/-- Erase free-variable type annotations while preserving variable indices and binder data. -/
def eraseFvarTypes : Expr md → Expr md
  | .bvar i => .bvar i
  | .fvar i _ => .fvar i (.sort .zero)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (eraseFvarTypes f) (eraseFvarTypes a)
  | .lam ty b m => .lam (eraseFvarTypes ty) (eraseFvarTypes b) m
  | .forallE ty b m => .forallE (eraseFvarTypes ty) (eraseFvarTypes b) m
  | .letE ty v b m => .letE (eraseFvarTypes ty) (eraseFvarTypes v) (eraseFvarTypes b) m
  | .lit l => .lit l
  | .proj s i e => .proj s i (eraseFvarTypes e)

/-- Every memoized erasure preserves the pure result. -/
def EraseFvarTypesMemoInv (memo : Std.HashMap (Expr md) (Expr md)) : Prop :=
  ∀ (k r : Expr md), memo[k]? = some r → r = eraseFvarTypes k

theorem EraseFvarTypesMemoInv.empty : (EraseFvarTypesMemoInv (md := md)) {} := by
  intro k r h; simp at h

theorem EraseFvarTypesMemoInv.insert {memo : Std.HashMap (Expr md) (Expr md)} (hm : EraseFvarTypesMemoInv memo)
    {e r : Expr md} (heq : r = eraseFvarTypes e) : EraseFvarTypesMemoInv (memo.insert e r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `eraseFvarTypes`. -/
def eraseFvarTypesGo (memo : Std.HashMap (Expr md) (Expr md)) : Expr md → Expr md × Std.HashMap (Expr md) (Expr md)
  | .bvar i => (.bvar i, memo)
  | .sort u => (.sort u, memo)
  | .const n us => (.const n us, memo)
  | .lit l => (.lit l, memo)
  | .fvar i _ => (.fvar i (.sort .zero), memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr md × Std.HashMap (Expr md) (Expr md) :=
        match e with
        | .app f a =>
          let (f', memo) := eraseFvarTypesGo memo f
          let (a', memo) := eraseFvarTypesGo memo a
          (.app f' a', memo)
        | .lam ty body bm =>
          let (t, memo) := eraseFvarTypesGo memo ty
          let (b, memo) := eraseFvarTypesGo memo body
          (.lam t b bm, memo)
        | .forallE ty body bm =>
          let (t, memo) := eraseFvarTypesGo memo ty
          let (b, memo) := eraseFvarTypesGo memo body
          (.forallE t b bm, memo)
        | .letE ty val body lmeta =>
          let (t, memo) := eraseFvarTypesGo memo ty
          let (w, memo) := eraseFvarTypesGo memo val
          let (b, memo) := eraseFvarTypesGo memo body
          (.letE t w b lmeta, memo)
        | .proj s i sub =>
          let (u, memo) := eraseFvarTypesGo memo sub
          (.proj s i u, memo)
        | e => (e, memo)
      (r, memo.insert e r)

/-- **The memoized walk is `eraseFvarTypes`.** -/
theorem eraseFvarTypesGo_spec :
    ∀ (e : Expr md) (memo : Std.HashMap (Expr md) (Expr md)), EraseFvarTypesMemoInv memo →
      (eraseFvarTypesGo memo e).1 = eraseFvarTypes e ∧ EraseFvarTypesMemoInv (eraseFvarTypesGo memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [eraseFvarTypesGo]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [eraseFvarTypes, h1, h3], ?_⟩
      exact h4.insert (by simp [eraseFvarTypes, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [eraseFvarTypesGo]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [eraseFvarTypes, h1, h3], ?_⟩
      exact h4.insert (by simp [eraseFvarTypes, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [eraseFvarTypesGo]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [eraseFvarTypes, h1, h3], ?_⟩
      exact h4.insert (by simp [eraseFvarTypes, h1, h3])
  | letE ty val body _ iht ihv ihb =>
    intro memo hm
    rw [eraseFvarTypesGo]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [eraseFvarTypes, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [eraseFvarTypes, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [eraseFvarTypesGo]
    split
    · rename_i r hhit
      exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [eraseFvarTypes, h1], ?_⟩
      exact h2.insert (by simp [eraseFvarTypes, h1])

/-- The executed `eraseFvarTypes` (one memoized DAG walk). -/
def eraseFvarTypesFast (e : Expr md) : Expr md := (eraseFvarTypesGo {} e).1

@[csimp] theorem eraseFvarTypes_eq_eraseFvarTypesFast : @eraseFvarTypes = @eraseFvarTypesFast := by
  funext md e
  exact (eraseFvarTypesGo_spec e {} EraseFvarTypesMemoInv.empty).1.symm

/-- Constant resolution for readings, which ignore free-variable type annotations.
Declaration typing continues to use the hereditary `constsResolve` check. -/
def constsResolveShallow (env : Env md) (e : Expr md) : Bool :=
  (eraseFvarTypes e).constsResolve env

end Ix.Kernel.Expr
