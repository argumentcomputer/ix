import Ix.CompileCert.Conv.Rel
import Batteries.Tactic.OpenPrivate

/-!
# M7 X1: the compiler's term functions commute with the erasure

The hashed constructors (`Ix.Expr.mk*`) erase to the plain ones whatever hash they compute, and
the compiler's de Bruijn helpers (`Ix.Compile.Canon.liftLoose`, `lowerLoose`, `getAppFnArgs`,
`mkAppN`) erase to `Tm.lift`, `Tm.lower`, `Tm.appN`. Statements about the compiler's functions
are made through these equations: nothing below depends on a hash.
-/

open private Ix.Compile.Canon.liftLoose.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Canon.lowerLoose.go from Ix.Compile.Canon.Expr

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose)

@[simp] theorem er_mkBVar (i : Nat) : er (Expr.mkBVar i) = .bvar i := rfl
@[simp] theorem er_mkFVar (x : Name) : er (Expr.mkFVar x) = .fvar x := rfl
@[simp] theorem er_mkSort (u : Level) : er (Expr.mkSort u) = .sort u := rfl
@[simp] theorem er_mkConst (x : Name) (us : Array Level) : er (Expr.mkConst x us) = .const x us := rfl
@[simp] theorem er_mkApp (f a : Expr) : er (Expr.mkApp f a) = .app (er f) (er a) := rfl
@[simp] theorem er_mkLam (n : Name) (t b : Expr) (bi : Lean.BinderInfo) :
    er (Expr.mkLam n t b bi) = .lam (er t) (er b) := rfl
@[simp] theorem er_mkForallE (n : Name) (t b : Expr) (bi : Lean.BinderInfo) :
    er (Expr.mkForallE n t b bi) = .pi (er t) (er b) := rfl
@[simp] theorem er_mkLetE (n : Name) (t v b : Expr) (nd : Bool) :
    er (Expr.mkLetE n t v b nd) = .letE (er t) (er v) (er b) := rfl
@[simp] theorem er_mkProj (n : Name) (i : Nat) (e : Expr) :
    er (Expr.mkProj n i e) = .proj n i (er e) := rfl
@[simp] theorem er_mkMData (d : Array (Name × Ix.DataValue)) (e : Expr) :
    er (Expr.mkMData d e) = er e := rfl

/-- An application spine erases to the spine of the erasures. -/
theorem er_getAppFnArgs : ∀ (e : Expr),
    er e = Tm.appN (er (getAppFnArgs e).1) ((getAppFnArgs e).2.toList.map er)
  | .app f a h => by
    have ih := er_getAppFnArgs f
    simp only [getAppFnArgs, er]
    rw [ih, Array.toList_push, List.map_append, List.map_cons, List.map_nil, Tm.appN_concat]
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lam .. | .forallE .. | .letE ..
  | .lit .. | .mdata .. | .proj .. => by simp [getAppFnArgs, Tm.appN]

theorem er_mkAppN_list (f : Expr) (as : List Expr) :
    er (as.foldl Expr.mkApp f) = Tm.appN (er f) (as.map er) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons, ih, er_mkApp, List.map_cons, Tm.appN_cons]

theorem er_mkAppN (f : Expr) (as : Array Expr) :
    er (mkAppN f as) = Tm.appN (er f) (as.toList.map er) := by
  simp only [mkAppN, ← Array.foldl_toList, er_mkAppN_list]

theorem er_liftLoose_go (n : Nat) : ∀ (e : Expr) (c : Nat),
    er (Ix.Compile.Canon.liftLoose.go n e c) = Tm.lift n c (er e)
  | .bvar i _, c => by
    simp only [Ix.Compile.Canon.liftLoose.go, er, Tm.lift]
    by_cases h : i ≥ c
    · simp only [h, ↓reduceIte, er_mkBVar]
    · simp only [h, ↓reduceIte, er_mkBVar]
  | .app f a _, c => by simp only [Ix.Compile.Canon.liftLoose.go, er_mkApp, er, Tm.lift, er_liftLoose_go n f c,
      er_liftLoose_go n a c]
  | .lam _ t b _ _, c => by simp only [Ix.Compile.Canon.liftLoose.go, er_mkLam, er, Tm.lift, er_liftLoose_go n t c,
      er_liftLoose_go n b (c + 1)]
  | .forallE _ t b _ _, c => by simp only [Ix.Compile.Canon.liftLoose.go, er_mkForallE, er, Tm.lift,
      er_liftLoose_go n t c, er_liftLoose_go n b (c + 1)]
  | .letE _ t v b _ _, c => by simp only [Ix.Compile.Canon.liftLoose.go, er_mkLetE, er, Tm.lift,
      er_liftLoose_go n t c, er_liftLoose_go n v c, er_liftLoose_go n b (c + 1)]
  | .proj _ _ s _, c => by simp only [Ix.Compile.Canon.liftLoose.go, er_mkProj, er, Tm.lift, er_liftLoose_go n s c]
  | .mdata _ x _, c => by simp only [Ix.Compile.Canon.liftLoose.go, er_mkMData, er, er_liftLoose_go n x c]
  | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _ | .lit .., _ => rfl

theorem er_liftLoose (e : Expr) (n c : Nat) : er (liftLoose e n c) = Tm.lift n c (er e) := by
  unfold liftLoose
  by_cases h : n = 0
  · subst h; simp [Tm.lift_zero]
  · simp only [beq_iff_eq, h, ↓reduceIte, er_liftLoose_go]

theorem er_lowerLoose_go (n : Nat) : ∀ (e : Expr) (c : Nat),
    er (Ix.Compile.Canon.lowerLoose.go n e c) = Tm.lower n c (er e)
  | .bvar i _, c => by
    simp only [Ix.Compile.Canon.lowerLoose.go, er, Tm.lower]
    by_cases h : i ≥ c + n
    · simp only [h, ↓reduceIte, er_mkBVar]
    · simp only [h, ↓reduceIte, er_mkBVar]
  | .app f a _, c => by simp only [Ix.Compile.Canon.lowerLoose.go, er_mkApp, er, Tm.lower, er_lowerLoose_go n f c,
      er_lowerLoose_go n a c]
  | .lam _ t b _ _, c => by simp only [Ix.Compile.Canon.lowerLoose.go, er_mkLam, er, Tm.lower,
      er_lowerLoose_go n t c, er_lowerLoose_go n b (c + 1)]
  | .forallE _ t b _ _, c => by simp only [Ix.Compile.Canon.lowerLoose.go, er_mkForallE, er, Tm.lower,
      er_lowerLoose_go n t c, er_lowerLoose_go n b (c + 1)]
  | .letE _ t v b _ _, c => by simp only [Ix.Compile.Canon.lowerLoose.go, er_mkLetE, er, Tm.lower,
      er_lowerLoose_go n t c, er_lowerLoose_go n v c, er_lowerLoose_go n b (c + 1)]
  | .proj _ _ s _, c => by simp only [Ix.Compile.Canon.lowerLoose.go, er_mkProj, er, Tm.lower,
      er_lowerLoose_go n s c]
  | .mdata _ x _, c => by simp only [Ix.Compile.Canon.lowerLoose.go, er_mkMData, er, er_lowerLoose_go n x c]
  | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _ | .lit .., _ => rfl

theorem Tm.lower_zero : ∀ (c : Nat) (t : Tm), Tm.lower 0 c t = t
  | c, .bvar i => by simp [Tm.lower]
  | c, .app f a => by simp [Tm.lower, Tm.lower_zero c f, Tm.lower_zero c a]
  | c, .lam t b => by simp [Tm.lower, Tm.lower_zero c t, Tm.lower_zero (c + 1) b]
  | c, .pi t b => by simp [Tm.lower, Tm.lower_zero c t, Tm.lower_zero (c + 1) b]
  | c, .letE t v b => by
    simp [Tm.lower, Tm.lower_zero c t, Tm.lower_zero c v, Tm.lower_zero (c + 1) b]
  | c, .proj s i e => by simp [Tm.lower, Tm.lower_zero c e]
  | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl

theorem er_lowerLoose (e : Expr) (n c : Nat) : er (lowerLoose e n c) = Tm.lower n c (er e) := by
  unfold lowerLoose
  by_cases h : n = 0
  · subst h; simp [Tm.lower_zero]
  · simp only [beq_iff_eq, h, ↓reduceIte, er_lowerLoose_go]

/-! ## The projection of a pair, as the development tests it -/

/-- `Ix.Compile.Image.projCtor?` finds a pair constructor applied to four arguments, under a
pair projection, and returns the projected field. -/
theorem projCtor?_spec {s : Name} {i : Nat} {e f : Expr}
    (h : Ix.Compile.Image.projCtor? s i e = some f) :
    ∃ c us α β a b, er e = pair4 c us (er α) (er β) (er a) (er b) ∧ pairName s c = true ∧
      ((i = 0 ∧ f = a) ∨ (i = 1 ∧ f = b)) := by
  have he := er_getAppFnArgs e
  unfold Ix.Compile.Image.projCtor? at h
  cases hg : getAppFnArgs e with
  | mk hd args =>
    rw [hg] at h he
    cases hd
    case const c us _ =>
      simp only at h he
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨hsz, hi⟩, hp⟩ := hc
        have hl : args.toList.length = 4 := by simp [hsz]
        match hargs : args.toList, hl with
        | [x0, x1, x2, x3], _ =>
          have hget : args[2 + i]? = [x0, x1, x2, x3][2 + i]? := by rw [← hargs]; simp
          rw [hget] at h
          refine ⟨c, us, x0, x1, x2, x3, ?_, hp, ?_⟩
          · rw [he, hargs]; rfl
          · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
            · have h' : some x2 = some f := h
              exact .inl ⟨rfl, (Option.some.inj h').symm⟩
            · have h' : some x3 = some f := h
              exact .inr ⟨rfl, (Option.some.inj h').symm⟩
      · cases h
    all_goals simp at h

end Ix.CompileCert.Conv
