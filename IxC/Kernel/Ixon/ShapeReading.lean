import IxC.Kernel.Ixon.ReaderSpec
import IxC.Kernel.Ixon.ShapeSpec

/-! # Successful expression readings have symbolic shapes

The symbolic pass keeps the expression reader's ordered sharing behavior. It
does not introduce failures at a raw expression which the real reader accepts.
Unused failed sharing entries impose no obligation.
-/

namespace Ix.Kernel.Reader.Shape

private theorem bind_ok {α β : Type} {x : ReadM α} {f : α → ReadM β} {value : β}
    (ran : (x >>= f) = .ok value) : ∃ input, x = .ok input ∧ f input = .ok value := by
  cases x with
  | error error => cases ran
  | ok input => exact ⟨input, rfl, ran⟩

def TablesCover (actual : Array (ReadM (CExpr md))) (shapes : Array (Option Term)) : Prop :=
  actual.size = shapes.size ∧ ∀ (i : Nat) (value : CExpr md), actual[i]? = some (.ok value) →
    ∃ shape, shapes[i]? = some (some shape)

theorem convert_exists (context : ECx md) {actual : Array (ReadM (CExpr md))}
    {shapes : Array (Option Term)} (tables : TablesCover actual shapes) :
    ∀ {raw : Ixon.Expr} {value : CExpr md}, convExpr context actual raw = .ok value →
      ∃ shape, convert shapes raw = some shape := by
  intro raw
  induction raw with
  | var i | sort i | ref i us | recur i us | str i | nat i =>
    intro value _
    exact ⟨_, rfl⟩
  | prj i field sub ih =>
    intro value ran
    obtain ⟨key, _, ran⟩ := bind_ok ran
    obtain ⟨subValue, subRead, _⟩ := bind_ok ran
    obtain ⟨shape, shapeRead⟩ := ih subRead
    exact ⟨.proj (refKey i.toNat) field.toNat shape, by simp [convert, shapeRead]⟩
  | app fn arg ihf iha | lam fn arg ihf iha | all fn arg ihf iha =>
    intro value ran
    obtain ⟨fnValue, fnRead, ran⟩ := bind_ok ran
    obtain ⟨argValue, argRead, _⟩ := bind_ok ran
    obtain ⟨fnShape, fnShapeRead⟩ := ihf fnRead
    obtain ⟨argShape, argShapeRead⟩ := iha argRead
    refine ⟨_, ?_⟩
    rw [convert, fnShapeRead, argShapeRead]
    rfl
  | letE nonDep mode type val body _ ihv ihb =>
    intro value ran
    obtain ⟨typeValue, _, ran⟩ := bind_ok ran
    obtain ⟨valValue, valRead, ran⟩ := bind_ok ran
    obtain ⟨bodyValue, bodyRead, _⟩ := bind_ok ran
    obtain ⟨valShape, valShapeRead⟩ := ihv valRead
    obtain ⟨bodyShape, bodyShapeRead⟩ := ihb bodyRead
    exact ⟨bodyShape.instantiate1Lift valShape, by simp [convert, valShapeRead, bodyShapeRead]⟩
  | share i =>
    intro value ran
    simp only [convExpr] at ran
    cases found : actual[i.toNat]? with
    | none => simp [found, malformed, throw, throwThe, MonadExceptOf.throw] at ran
    | some entry =>
      simp only [found] at ran
      subst entry
      obtain ⟨shape, shapeFound⟩ := tables.2 _ _ found
      exact ⟨shape, by simp [convert, shapeFound]⟩

theorem TablesCover.push {actual : Array (ReadM (CExpr md))} {shapes : Array (Option Term)}
    (tables : TablesCover actual shapes) {entry : ReadM (CExpr md)} {shape : Option Term}
    (converted : ∀ value, entry = .ok value → ∃ result, shape = some result) :
    TablesCover (actual.push entry) (shapes.push shape) := by
  refine ⟨by simp [tables.1], fun i value found => ?_⟩
  rw [Array.getElem?_push] at found ⊢
  rw [← tables.1]
  by_cases last : i = actual.size
  · simp only [last, ↓reduceIte, Option.some.injEq] at found ⊢
    exact converted _ found
  · simp only [last, ↓reduceIte] at found ⊢
    exact tables.2 _ _ found

theorem fold_cover (context : ECx md) (raw : List Ixon.Expr)
    {actual : Array (ReadM (CExpr md))} {shapes : Array (Option Term)}
    (tables : TablesCover actual shapes) :
    TablesCover (raw.foldl (fun table entry => table.push (convExpr context table entry)) actual)
      (raw.foldl (fun table entry => table.push (convert table entry)) shapes) := by
  induction raw generalizing actual shapes with
  | nil => exact tables
  | cons first rest ih =>
    exact ih (tables.push (fun value ran => convert_exists context tables ran))

/-- A real successful member reading supplies the symbolic conversion needed by
result analysis, including its sharing dependencies. -/
theorem memberReader_exists (context : Ctx md) (constant : Ixon.Constant)
    (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
    {raw : Ixon.Expr} {value : CExpr md}
    (ran : (MemberReader.mk' context constant param self).read raw = .ok value) :
    ∃ shape, read constant raw = some shape := by
  simp only [MemberReader.mk', MemberReader.read, Id.run, Array.forIn_pure_yield_eq_foldl,
    Array.mkEmpty, ← Array.foldl_toList] at ran
  unfold read sharing
  rw [← Array.foldl_toList]
  exact convert_exists _ (fold_cover _ constant.sharing.toList
    ⟨rfl, fun i value found => by simp at found⟩) ran

end Ix.Kernel.Reader.Shape
