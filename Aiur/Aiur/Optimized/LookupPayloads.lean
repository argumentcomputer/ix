import Aiur.Optimized.LookupGuards

namespace Aiur.Optimized.LookupMerging

variable {F : Type} [Field F] [DecidableEq F]

def wireZip (f : Polynomial F → Polynomial F → Polynomial F)
    (left right : WireValue (Polynomial F)) : WireValue (Polynomial F) :=
  ⟨left.type, List.zipWith f left.words right.words⟩

def wiresZip (f : Polynomial F → Polynomial F → Polynomial F)
    (left right : List (WireValue (Polynomial F))) : List (WireValue (Polynomial F)) :=
  List.zipWith (wireZip f) left right

def denoteWires (a : Witness → F) (wires : List (WireValue (Polynomial F))) : List (WireValue F) :=
  wires.map (WireValue.map (Circuit.ArithExpr.denote a))

def ZeroWires (a : Witness → F) (wires : List (WireValue (Polynomial F))) : Prop :=
  ∀ wire ∈ wires, ∀ p ∈ wire.words, p.denote a = 0

omit [DecidableEq F] in
theorem wireZip_left {f : Polynomial F → Polynomial F → Polynomial F}
    {left right : WireValue (Polynomial F)} (shape : wireShape left = wireShape right)
    {a : Witness → F} (same : ∀ x ∈ left.words, ∀ y ∈ right.words,
      (f x y).denote a = x.denote a) :
    (wireZip f left right).map (Circuit.ArithExpr.denote a) = left.map (Circuit.ArithExpr.denote a) := by
  rcases left with ⟨lt, ls⟩; rcases right with ⟨rt, rs⟩
  have length : ls.length = rs.length := congrArg Prod.snd shape
  clear shape
  simp only [wireZip, WireValue.map]
  congr 1
  induction ls generalizing rs with
  | nil => simp
  | cons x xs ih =>
    cases rs with
    | nil => simp at length
    | cons y ys =>
      change (f x y).denote a :: _ = x.denote a :: _
      rw [same x (by simp) y (by simp)]
      exact congrArg (List.cons _) (ih ys
        (fun x hx y hy => same x (by simp [hx]) y (by simp [hy])) (by simpa using length))

omit [DecidableEq F] in
theorem wireZip_right {f : Polynomial F → Polynomial F → Polynomial F}
    {left right : WireValue (Polynomial F)} (shape : wireShape left = wireShape right)
    {a : Witness → F} (same : ∀ x ∈ left.words, ∀ y ∈ right.words,
      (f x y).denote a = y.denote a) :
    (wireZip f left right).map (Circuit.ArithExpr.denote a) = right.map (Circuit.ArithExpr.denote a) := by
  rcases left with ⟨lt, ls⟩; rcases right with ⟨rt, rs⟩
  obtain ⟨rfl, length⟩ := Prod.mk.inj shape
  clear shape
  change ls.length = rs.length at length
  simp only [wireZip, WireValue.map]
  congr 1
  induction ls generalizing rs with
  | nil => cases rs <;> simp_all
  | cons x xs ih =>
    cases rs with
    | nil => simp at length
    | cons y ys =>
      change (f x y).denote a :: _ = y.denote a :: _
      rw [same x (by simp) y (by simp)]
      exact congrArg (List.cons _) (ih ys
        (fun x hx y hy => same x (by simp [hx]) y (by simp [hy])) (by simpa using length))

theorem wiresZip_left {f : Polynomial F → Polynomial F → Polynomial F}
    {left right : List (WireValue (Polynomial F))} (shape : left.map wireShape = right.map wireShape)
    {a : Witness → F} (same : ∀ l ∈ left, ∀ r ∈ right, ∀ x ∈ l.words, ∀ y ∈ r.words,
      (f x y).denote a = x.denote a) :
    denoteWires a (wiresZip f left right) = denoteWires a left := by
  induction left generalizing right with
  | nil => simp [wiresZip, denoteWires]
  | cons l ls ih =>
    cases right with
    | nil => simp at shape
    | cons r rs =>
      simp only [List.map_cons, List.cons.injEq] at shape
      change _ :: _ = _ :: _
      rw [wireZip_left shape.1 (same l (by simp) r (by simp))]
      exact congrArg (List.cons _) (ih shape.2
        (fun l hl r hr => same l (by simp [hl]) r (by simp [hr])))

theorem wiresZip_right {f : Polynomial F → Polynomial F → Polynomial F}
    {left right : List (WireValue (Polynomial F))} (shape : left.map wireShape = right.map wireShape)
    {a : Witness → F} (same : ∀ l ∈ left, ∀ r ∈ right, ∀ x ∈ l.words, ∀ y ∈ r.words,
      (f x y).denote a = y.denote a) :
    denoteWires a (wiresZip f left right) = denoteWires a right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [wiresZip, denoteWires]
  | cons l ls ih =>
    cases right with
    | nil => simp at shape
    | cons r rs =>
      simp only [List.map_cons, List.cons.injEq] at shape
      change _ :: _ = _ :: _
      rw [wireZip_right shape.1 (same l (by simp) r (by simp))]
      exact congrArg (List.cons _) (ih shape.2
        (fun l hl r hr => same l (by simp [hl]) r (by simp [hr])))

private theorem zipWith_member {α β γ : Type} {f : α → β → γ} {xs : List α} {ys : List β} {z : γ}
    (member : z ∈ List.zipWith f xs ys) : ∃ x ∈ xs, ∃ y ∈ ys, f x y = z := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons x xs ih =>
    cases ys with
    | nil => simp at member
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨x, by simp, y, by simp, rfl⟩
      · obtain ⟨a, ha, b, hb, rfl⟩ := ih member
        exact ⟨a, by simp [ha], b, by simp [hb], rfl⟩

omit [DecidableEq F] in
theorem wiresZip_zero {f : Polynomial F → Polynomial F → Polynomial F}
    {left right : List (WireValue (Polynomial F))} {a : Witness → F}
    (zero : ∀ l ∈ left, ∀ r ∈ right, ∀ x ∈ l.words, ∀ y ∈ r.words, (f x y).denote a = 0) :
    ZeroWires a (wiresZip f left right) := by
  intro wire member p occurs
  obtain ⟨l, hl, r, hr, rfl⟩ := zipWith_member member
  obtain ⟨x, hx, y, hy, rfl⟩ := zipWith_member occurs
  exact zero l hl r hr x hx y hy

/-- A merged payload is already weighted. Further merges add weighted payloads
rather than multiplying them by another selector; its degree stays quadratic. -/
structure Payload (ctx : Context F) where
  guard : Guard ctx
  wires : List (WireValue (Polynomial F))
  weighted : Bool
  zero : ∀ a, ctx.Valid a → guard.expr.denote a = 0 → weighted = true → ZeroWires a wires

def Payload.single {ctx : Context F} (guard : Guard ctx) (wires : List (WireValue (Polynomial F))) : Payload ctx :=
  ⟨guard, wires, false, by simp⟩

def Payload.factor {ctx : Context F} (payload : Payload ctx) : Polynomial F :=
  if payload.weighted then .const 1 else payload.guard.expr

theorem Payload.factor_active {ctx : Context F} (p : Payload ctx) {a : Witness → F}
    (active : p.guard.expr.denote a = 1) : p.factor.denote a = 1 := by
  simp only [Payload.factor]
  split <;> simp [Scalar.Circuit.ArithExpr.denote, active]

theorem Payload.factor_inactive {ctx : Context F} (p : Payload ctx) {a : Witness → F}
    (valid : ctx.Valid a) (inactive : p.guard.expr.denote a = 0)
    {wire : WireValue (Polynomial F)} (member : wire ∈ p.wires) {x : Polynomial F} (occurs : x ∈ wire.words) :
    p.factor.denote a * x.denote a = 0 := by
  unfold Payload.factor
  split
  · simp [Scalar.Circuit.ArithExpr.denote, p.zero a valid inactive (by assumption) wire member x occurs]
  · simp [inactive]

def Payload.join {ctx : Context F} (left right : Payload ctx)
    (different : left.guard.exclusive right.guard = true) : Payload ctx where
  guard := left.guard.join right.guard different
  wires := wiresZip (mix left.factor right.factor) left.wires right.wires
  weighted := true
  zero a valid inactive _ := by
    have l : left.guard.expr.denote a = 0 := by
      rcases left.guard.boolean a valid with zero | one
      · exact zero
      · have r := Guard.exclusive_sound different valid (by rw [one]; exact one_ne_zero)
        simp [Guard.join, Scalar.Circuit.ArithExpr.denote, one, r] at inactive
    have r : right.guard.expr.denote a = 0 := by
      simpa [Guard.join, Scalar.Circuit.ArithExpr.denote, l] using inactive
    apply wiresZip_zero
    intro lw lm rw rm x hx y hy
    simp only [mix, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote]
    rw [left.factor_inactive valid l lm hx, right.factor_inactive valid r rm hy, add_zero]

theorem Payload.join_left {ctx : Context F} {left right : Payload ctx}
    (different : left.guard.exclusive right.guard = true)
    (shape : left.wires.map wireShape = right.wires.map wireShape)
    {a : Witness → F} (valid : ctx.Valid a) (active : left.guard.expr.denote a = 1) :
    denoteWires a (left.join right different).wires = denoteWires a left.wires := by
  have inactive := Guard.exclusive_sound different valid (by rw [active]; exact one_ne_zero)
  apply wiresZip_left shape
  intro lw lm rw rm x hx y hy
  change (Polynomial.simplify _).denote a = _
  rw [Polynomial.denote_simplify]
  change left.factor.denote a * x.denote a + right.factor.denote a * y.denote a = _
  rw [left.factor_active active, one_mul, right.factor_inactive valid inactive rm hy, add_zero]

theorem Payload.join_right {ctx : Context F} {left right : Payload ctx}
    (different : left.guard.exclusive right.guard = true)
    (shape : left.wires.map wireShape = right.wires.map wireShape)
    {a : Witness → F} (valid : ctx.Valid a) (active : right.guard.expr.denote a = 1) :
    denoteWires a (left.join right different).wires = denoteWires a right.wires := by
  have inactive : left.guard.expr.denote a = 0 := by
    by_contra other
    have := Guard.exclusive_sound different valid other
    simp [active] at this
  apply wiresZip_right shape
  intro lw lm rw rm x hx y hy
  change (Polynomial.simplify _).denote a = _
  rw [Polynomial.denote_simplify]
  change left.factor.denote a * x.denote a + right.factor.denote a * y.denote a = _
  rw [left.factor_inactive valid inactive lm hx, right.factor_active active, one_mul, zero_add]

end Aiur.Optimized.LookupMerging
