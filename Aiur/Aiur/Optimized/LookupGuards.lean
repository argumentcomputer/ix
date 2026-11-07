import Aiur.Optimized.ControlCertificate
import Aiur.Optimized.PhysicalSemantics

namespace Aiur.Optimized.LookupMerging

variable {F : Type} [Field F] [DecidableEq F]

/-- The constraints of the emitted chip remain anchors while lookup slots are
merged. Scope labels only authorize sharing after their control equations have
been checked. -/
structure Context (F : Type) [Field F] [DecidableEq F] where
  logical : ScopedChip F
  layout : ColumnLayout
  control : Control.Certificate logical
  boolean : ∀ scope ∈ List.range logical.scopes.size,
    Control.ZeroEquation logical
      (.mul (logical.activation scope) (.sub (logical.activation scope) (.const 1)))

def Context.Valid (ctx : Context F) (a : Witness → F) : Prop :=
  Circuit.Satisfies (emitChip ctx.logical ctx.layout).constraints a

def Context.guard (ctx : Context F) (scope : ScopeId) : Polynomial F :=
  ctx.layout.expression (ctx.logical.activation scope)

theorem Context.logicalValid (ctx : Context F) {a : Witness → F} (valid : ctx.Valid a) :
    ctx.logical.ValidAssignment (⟨ctx.logical.cells.toList.map fun cell =>
      (cell.address.denote (a ∘ ctx.layout.column),
        cell.value.map (Circuit.ArithExpr.denote (a ∘ ctx.layout.column)))⟩ : WireROM F)
      (a ∘ ctx.layout.column) := by
  refine ⟨(emitChip_constraints _ _ _).mp valid, ?_⟩
  intro cell member _
  exact List.mem_map.mpr ⟨cell, member, rfl⟩

theorem Context.guard_boolean (ctx : Context F) {a : Witness → F} (valid : ctx.Valid a)
    {scope : ScopeId} (bound : scope < ctx.logical.scopes.size) :
    (ctx.guard scope).denote a = 0 ∨ (ctx.guard scope).denote a = 1 := by
  have zero := ctx.control.zero (ctx.logicalValid valid)
    (ctx.boolean scope (List.mem_range.mpr bound))
  simpa only [Context.guard, ColumnLayout.expression_denote, Scalar.Circuit.ArithExpr.denote,
    mul_eq_zero, sub_eq_zero] using zero

def Context.exclusive (ctx : Context F) (left right : ScopeId) : Bool :=
  match ctx.logical.scopes[left]?, ctx.logical.scopes[right]? with
  | some left, some right => left.path.exclusive right.path
  | _, _ => false

theorem Context.exclusive_sound (ctx : Context F) {a : Witness → F} (valid : ctx.Valid a)
    {left right : ScopeId} (different : ctx.exclusive left right = true)
    (active : (ctx.guard left).denote a ≠ 0) : (ctx.guard right).denote a = 0 := by
  unfold Context.exclusive at different
  cases l : ctx.logical.scopes[left]? with
  | none => simp [l] at different
  | some ls =>
    cases r : ctx.logical.scopes[right]? with
    | none => simp [r] at different
    | some rs =>
      simp only [l, r] at different
      by_contra other
      apply ctx.control.paths_exclusive (ctx.logicalValid valid) different
      · apply ctx.control.activePath (ctx.logicalValid valid) l
        simpa only [Context.guard, ColumnLayout.expression_denote] using active
      · apply ctx.control.activePath (ctx.logicalValid valid) r
        simpa only [Context.guard, ColumnLayout.expression_denote] using other

structure Guard (ctx : Context F) where
  expr : Polynomial F
  scopes : List ScopeId
  boolean : ∀ a, ctx.Valid a → expr.denote a = 0 ∨ expr.denote a = 1
  origin : ∀ a, ctx.Valid a → expr.denote a ≠ 0 →
    ∃ scope ∈ scopes, (ctx.guard scope).denote a ≠ 0

def Guard.ofScope (ctx : Context F) (scope : ScopeId) (bound : scope < ctx.logical.scopes.size) : Guard ctx :=
  ⟨ctx.guard scope, [scope], fun _ h => ctx.guard_boolean h bound,
    fun _ _ active => ⟨scope, by simp, active⟩⟩

def Guard.exclusive {ctx : Context F} (left right : Guard ctx) : Bool :=
  left.scopes.all fun l => right.scopes.all (ctx.exclusive l)

theorem Guard.exclusive_sound {ctx : Context F} {left right : Guard ctx}
    (different : left.exclusive right = true) {a : Witness → F} (valid : ctx.Valid a)
    (active : left.expr.denote a ≠ 0) : right.expr.denote a = 0 := by
  by_contra other
  obtain ⟨l, lm, la⟩ := left.origin a valid active
  obtain ⟨r, rm, ra⟩ := right.origin a valid other
  exact ra (ctx.exclusive_sound valid
    (List.all_eq_true.mp (List.all_eq_true.mp different l lm) r rm) la)

def Guard.join {ctx : Context F} (left right : Guard ctx)
    (different : left.exclusive right = true) : Guard ctx where
  expr := .add left.expr right.expr
  scopes := left.scopes ++ right.scopes
  boolean a valid := by
    rcases left.boolean a valid with l | l
    · simpa only [Scalar.Circuit.ArithExpr.denote, l, zero_add] using right.boolean a valid
    · have r := Guard.exclusive_sound different valid (by rw [l]; exact one_ne_zero)
      simp [Scalar.Circuit.ArithExpr.denote, l, r]
  origin a valid active := by
    by_cases l : left.expr.denote a = 0
    · have r : right.expr.denote a ≠ 0 := by simpa [Scalar.Circuit.ArithExpr.denote, l] using active
      obtain ⟨scope, member, enabled⟩ := right.origin a valid r
      exact ⟨scope, List.mem_append_right _ member, enabled⟩
    · obtain ⟨scope, member, enabled⟩ := left.origin a valid l
      exact ⟨scope, List.mem_append_left _ member, enabled⟩

/-- A zero guard contributes no payload. When exactly one guard is one, the
quadratic sum is exactly that branch's value, including in small fields. -/
def mix (leftGuard rightGuard left right : Polynomial F) : Polynomial F :=
  Polynomial.simplify (.add (.mul leftGuard left) (.mul rightGuard right))

theorem mix_left {g h x y : Polynomial F} {a : Witness → F}
    (left : g.denote a = 1) (right : h.denote a = 0) :
    (mix g h x y).denote a = x.denote a := by
  simp [mix, Scalar.Circuit.ArithExpr.denote, left, right]

theorem mix_right {g h x y : Polynomial F} {a : Witness → F}
    (left : g.denote a = 0) (right : h.denote a = 1) :
    (mix g h x y).denote a = y.denote a := by
  simp [mix, Scalar.Circuit.ArithExpr.denote, left, right]

def wireShape (wire : WireValue α) : Ty × Nat := (wire.type, wire.words.length)


end Aiur.Optimized.LookupMerging
