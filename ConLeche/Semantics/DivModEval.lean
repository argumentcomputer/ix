module

public import ConLeche.Verify.DivModInv
import ConLeche.Verify.Denote
public import ConLeche.SetTheory.Basic

@[expose] public section

/-!
# The div/mod certificates' model-free half (task #161, S1)

THE SEPARATION's shared base: the syntactic and `V`-generic half of
`SetR/DivModPin.lean` (design census §3.3, edge 11) — the two
`substConst0` invariances, the pinned-type inversions, the applied
form's leaf lemmas, the `dmLeavesOk` decision procedure, the frame's
well-scopedness lemmas and `dmEvalV`, the statement fragment's value
at a valuation of the heads.  None of them mentions `EnvS`, `denote`
or a relation of the `Infer`/`DefEq` family: `dmEvalV` is `SetTheory`
evaluation over an abstract `val : Name → W`, and the rest is `Expr`
syntax.  The collapsed lane's `DivModPin.lean` builds its certificate
discharges on them; the graded lane's `Interp/DivModCertP.lean`
consumes exactly these 17 symbols and nothing else of that file.

Statements verbatim from their old home; the namespace is unchanged.
-/

universe w

namespace ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory

variable {V : Type w} [SetTheory V]

/-- A closed replacement moves no leaf. -/
theorem fvarLeaves_substConst0 {n : Name} {r : Expr}
    (hr : r.hasFvar = false) :
    ∀ e : Expr, (Expr.substConst0 n r e).fvarLeaves = e.fvarLeaves
  | .const c us => by
    simp only [Expr.substConst0]
    split
    · exact (Expr.fvarLeaves_eq_nil_of_not_hasFvar hr).trans
        (Expr.fvarLeaves_eq_nil_of_not_hasFvar
          (e := .const c us) (by simp [Expr.hasFvar])).symm
    · rfl
  | .app f a => by
    simp only [Expr.substConst0, Expr.fvarLeaves,
      fvarLeaves_substConst0 hr f, fvarLeaves_substConst0 hr a]
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ => rfl

/-- A `looseBVars`-closed replacement keeps the bound. -/
theorem looseBVarsBounded_substConst0 {n : Name} {r : Expr}
    (hr : r.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) {k : Nat}, e.looseBVarsBounded k = true →
      (Expr.substConst0 n r e).looseBVarsBounded k = true
  | .const c us, k, he => by
    simp only [Expr.substConst0]
    split
    · exact Expr.looseBVarsBounded_mono (Nat.zero_le k) hr
    · exact he
  | .app f a, k, he => by
    simp only [Expr.substConst0, Expr.looseBVarsBounded,
      Bool.and_eq_true] at he ⊢
    exact ⟨looseBVarsBounded_substConst0 hr f he.1,
      looseBVarsBounded_substConst0 hr a he.2⟩
  | .bvar _, _, he | .fvar _ _, _, he | .sort _, _, he
  | .lit _, _, he | .lam _ _ _, _, he | .forallE _ _ _, _, he
  | .letE _ _ _, _, he | .proj _ _ _, _, he => he

/-- The binary pinned type, inverted. -/
theorem natOpTyPinned_binaryE {env : Env} {n : Name} {ty : Expr}
    (hn : ¬(n = natPredName))
    (h : natOpTyPinned env n ty = true) :
    ∃ mb mb2 cod, ty = .forallE (.const natName [])
      (.forallE (.const natName []) cod mb2) mb ∧
      natOpCod env n cod = true := by
  unfold natOpTyPinned at h
  rw [if_neg hn] at h
  revert h
  match ty with
  | .forallE dom (.forallE dom2 cod mb2) mb =>
    intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨mb, mb2, cod, by rw [h.1.1, h.1.2], h.2⟩
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _
  | .forallE _ (.bvar _) _ | .forallE _ (.fvar _ _) _
  | .forallE _ (.sort _) _ | .forallE _ (.const _ _) _
  | .forallE _ (.app _ _) _ | .forallE _ (.lam _ _ _) _
  | .forallE _ (.letE _ _ _) _ | .forallE _ (.lit _) _
  | .forallE _ (.proj _ _ _) _ => intro h; exact nomatch h

/-- The codomain is a stored, level-monomorphic constant. -/
theorem natOpCod_stored {env : Env} {n : Name} {cod : Expr}
    (h : natOpCod env n cod = true) :
    (∃ ci, cod = .const boolName [] ∧
      env.find? boolName = some ci ∧
      ci.toConstantVal.levelParams = []) ∨ cod = .const natName [] := by
  unfold natOpCod at h
  split at h
  · refine Or.inl ?_
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    revert h2
    cases hb : env.find? boolName with
    | none => intro h2; exact nomatch h2
    | some ci =>
      intro h2
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h2
      exact ⟨ci, rfl, rfl, h2.1⟩
  · exact Or.inr (by simpa using h)

/-- `Nat.ble`'s codomain is the stored `Bool`. -/
theorem natOpCod_ble {env : Env} {cod : Expr}
    (h : natOpCod env natBleName cod = true) :
    cod = Expr.const boolName [] ∧ ∃ ci,
      env.find? boolName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  unfold natOpCod at h
  rw [if_pos (show (decide (natBleName = natBeqName) ||
    decide (natBleName = natBleName)) = true from by decide)] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, h2⟩ := h
  revert h2
  cases hb : env.find? boolName with
  | none => intro h2; exact nomatch h2
  | some ci =>
    intro h2
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h2
    exact ⟨rfl, ci, rfl, h2.1, h2.2⟩

/-- Where a leaf of the two-hypothesis applied form can come from. -/
theorem divModCertApplied_mem2 {p h1 h2 : Expr}
    (hp : p.hasFvar = false) {l : Nat × Expr}
    (hl : l ∈ (divModCertApplied p [h1, h2]).fvarLeaves) :
    l = (0, Expr.const natName []) ∨
    l = (1, Expr.const natName []) ∨
    l = (2, h1) ∨ l ∈ h1.fvarLeaves ∨
    l = (3, h2) ∨ l ∈ h2.fvarLeaves := by
  simp only [divModCertApplied, Expr.fvarLeaves,
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hp, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((h | h) | h | h) | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- Where a leaf of the one-hypothesis applied form can come from. -/
theorem divModCertApplied_mem1 {p h1 : Expr}
    (hp : p.hasFvar = false) {l : Nat × Expr}
    (hl : l ∈ (divModCertApplied p [h1]).fvarLeaves) :
    l = (0, Expr.const natName []) ∨
    l = (1, Expr.const natName []) ∨
    l = (2, h1) ∨ l ∈ h1.fvarLeaves := by
  simp only [divModCertApplied, Expr.fvarLeaves,
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hp, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (h | h) | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ## The statements' syntactic frame, decided

Every div/mod certificate statement mentions exactly the two frame
variables `x` and `y`, both at `Nat`.  That is a decidable property of
the (literal) statement, and it is all the depth-4 frame needs from
it. -/

/-- Is every leaf of `e` the frame's `x` or `y`, at `Nat`? -/
def dmLeavesOk (e : Expr) : Bool :=
  e.fvarLeaves.all (fun l =>
    (l.1 == 0 && l.2 == Expr.const natName []) ||
    (l.1 == 1 && l.2 == Expr.const natName []))

/-- A leaf of a `dmLeavesOk` term, identified. -/
theorem dmLeavesOk_mem {e : Expr} (h : dmLeavesOk e = true)
    {l : Nat × Expr} (hl : l ∈ e.fvarLeaves) :
    l = (0, Expr.const natName []) ∨
    l = (1, Expr.const natName []) := by
  have hm := List.all_eq_true.mp h l hl
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by
      rcases l with ⟨i, t⟩
      simp only at h1 h2
      rw [h1, h2])
  · exact Or.inr (by
      rcases l with ⟨i, t⟩
      simp only at h1 h2
      rw [h1, h2])

/-- `dmLeavesOk` survives the operation substitution. -/
theorem dmLeavesOk_substConst0 {c : Name} {value' e : Expr}
    (hvf : value'.hasFvar = false) (h : dmLeavesOk e = true) :
    dmLeavesOk (Expr.substConst0 c value' e) = true := by
  unfold dmLeavesOk at h ⊢
  rw [fvarLeaves_substConst0 hvf e]
  exact h

/-- A `dmLeavesOk` term is leaf-bounded: `Nat` has no loose bound
variables. -/
theorem dmLeavesOk_leavesBounded {e : Expr} (h : dmLeavesOk e = true) :
    Expr.LeavesBounded e := by
  intro l hl
  rcases dmLeavesOk_mem h hl with rfl | rfl <;> rfl

/-- A frame variable is well-scoped at depth 4. -/
theorem dmFvar_wscoped {i : Nat} {ty : Expr} (hi : i < 4)
    (hty : Expr.WScoped i ty) :
    Expr.WScoped 4 (Expr.fvar i ty) := by
  simp only [Expr.WScoped]
  exact ⟨hi, hty⟩

/-- Scope composes over applications. -/
theorem dmApp_wscoped {d : Nat} {f a : Expr} (hf : Expr.WScoped d f)
    (ha : Expr.WScoped d a) : Expr.WScoped d (.app f a) := by
  simp only [Expr.WScoped]
  exact ⟨hf, ha⟩

/-- The two-hypothesis applied form's scope and bound-variable
facts. -/
theorem dmApplied2_frame {p a b : Expr}
    (hpf : p.hasFvar = false) (hpb : p.looseBVarsBounded 0 = true)
    (hwa : Expr.WScoped 2 a) (hwb : Expr.WScoped 3 b) :
    Expr.WScoped 4 (divModCertApplied p [a, b]) ∧
      (divModCertApplied p [a, b]).looseBVarsBounded 0 = true := by
  refine ⟨?_, ?_⟩
  · show Expr.WScoped 4 (.app (.app (.app (.app p _) _) _) _)
    exact dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
      (Expr.WScoped.of_not_hasFvar hpf)
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) hwa) |> fun h =>
        dmApp_wscoped h (dmFvar_wscoped (by omega) hwb)
  · show ((((p.app _).app _).app _).app _).looseBVarsBounded 0 = true
    simp [Expr.looseBVarsBounded, hpb]

/-- The one-hypothesis applied form's scope and bound-variable
facts. -/
theorem dmApplied1_frame {p a : Expr}
    (hpf : p.hasFvar = false) (hpb : p.looseBVarsBounded 0 = true)
    (hwa : Expr.WScoped 2 a) :
    Expr.WScoped 4 (divModCertApplied p [a]) ∧
      (divModCertApplied p [a]).looseBVarsBounded 0 = true := by
  refine ⟨?_, ?_⟩
  · show Expr.WScoped 4 (.app (.app (.app p _) _) _)
    exact dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
      (Expr.WScoped.of_not_hasFvar hpf)
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) (Expr.WScoped.of_not_hasFvar rfl)))
      (dmFvar_wscoped (by omega) hwa)
  · show (((p.app _).app _).app _).looseBVarsBounded 0 = true
    simp [Expr.looseBVarsBounded, hpb]

/-- The grammar's value at a valuation of the heads. -/
noncomputable def dmEvalV (W : Type w) [SetTheory W]
    (val : Name → W) (x y : W) : Expr → W
  | Expr.const n _ => val n
  | Expr.app f a =>
    SetTheory.app (dmEvalV W val x y f) (dmEvalV W val x y a)
  | Expr.fvar i _ => if i = 0 then x else y
  | _ => pt

@[simp] theorem dmEvalV_const (val : Name → V) (x y : V) (n : Name)
    (us : List Level) : dmEvalV V val x y (Expr.const n us) = val n := rfl

@[simp] theorem dmEvalV_app (val : Name → V) (x y : V) (f a : Expr) :
    dmEvalV V val x y (Expr.app f a)
      = SetTheory.app (dmEvalV V val x y f) (dmEvalV V val x y a) := rfl

@[simp] theorem dmEvalV_fvar (val : Name → V) (x y : V) (i : Nat)
    (ty : Expr) :
    dmEvalV V val x y (Expr.fvar i ty) = if i = 0 then x else y := rfl


/-- The `ble`-guarded value-level clauses of a pin-certified
WF-recursive operation, over a value valuation of the level-mono
heads (`DivModClauses` transpose, verbatim — value-level). -/
def DivModClausesV (V : Type w) [SetTheory V] (val : Name → V) (c : Name) (x y : V) : Prop :=
  let vT := val boolTrueName
  let vF := val boolFalseName
  let one : V := SetTheory.app (val natSuccName) (val natZeroName)
  let two : V := SetTheory.app (val natSuccName) one
  let ble2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natBleName) a) b
  let op2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val c) a) b
  let sub2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natSubName) a) b
  let add2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natAddName) a) b
  let mul2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natMulName) a) b
  let div2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natDivName) a) b
  let mod2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natModName) a) b
  if c = natGcdName then
    (ble2 one x = vT → op2 x y = op2 (mod2 y x) x) ∧
    (ble2 one x = vF → op2 x y = y)
  else if c = natShiftLeftName then
    (ble2 one y = vT → op2 x y = op2 (mul2 two x) (sub2 y one)) ∧
    (ble2 one y = vF → op2 x y = x)
  else if c = natShiftRightName then
    (ble2 one y = vT → op2 x y = div2 (op2 x (sub2 y one)) two) ∧
    (ble2 one y = vF → op2 x y = x)
  else if c = natLandName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two))) ∧
    (ble2 one x = vF → op2 x y = val natZeroName)
  else if c = natLorName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two)))) ∧
    (ble2 one x = vF → op2 x y = y)
  else if c = natXorName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two)) ∧
    (ble2 one x = vF → op2 x y = y)
  else
    (ble2 y x = vT → ble2 one y = vT →
     op2 x y =
       (if c = natDivName then
          SetTheory.app (val natSuccName) (op2 (sub2 x y) y)
        else op2 (sub2 x y) y)) ∧
    (ble2 y x = vF →
     op2 x y = (if c = natDivName then val natZeroName else x)) ∧
    (ble2 one y = vF →
     op2 x y = (if c = natDivName then val natZeroName else x))

/-- For `c` one of `Nat.div`/`Nat.mod`, the clause dispatch collapses
to the original three `ble`-guarded clauses. -/
theorem divModClausesV_divmod {V : Type w} [SetTheory V] {val : Name → V} {c : Name} {x y : V}
    (hc : c = natDivName ∨ c = natModName)
    (h : DivModClausesV V val c x y) :
    (app (app (val natBleName) y) x = val boolTrueName →
     app (app (val natBleName)
       (app (val natSuccName) (val natZeroName))) y =
       val boolTrueName →
     app (app (val c) x) y =
       (if c = natDivName then
         app (val natSuccName)
           (app (app (val c) (app (app (val natSubName) x) y)) y)
        else app (app (val c) (app (app (val natSubName) x) y)) y)) ∧
    (app (app (val natBleName) y) x = val boolFalseName →
     app (app (val c) x) y =
       (if c = natDivName then val natZeroName else x)) ∧
    (app (app (val natBleName)
       (app (val natSuccName) (val natZeroName))) y =
       val boolFalseName →
     app (app (val c) x) y =
       (if c = natDivName then val natZeroName else x)) := by
  rcases hc with rfl | rfl <;>
    simpa +decide only [DivModClausesV, if_false, if_true,
      reduceCtorEq, decide_true, decide_false] using h

end ConLeche.Semantics
