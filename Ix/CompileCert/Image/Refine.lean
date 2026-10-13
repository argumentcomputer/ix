import Ix.CompileCert.Image.Build

/-!
# The image construction with a development that extends another

`Refines x y`: every successful run of `x` is a run of `y` from the same state, with the same value
and the same end state. A development `D2` refines `D1` (`DevRefines D1 D2`) when it returns `D1`'s
result wherever `D1` succeeds. The two development calls are the only steps of the construction
that depend on the development, so:

* `refines_buildRecAppW`, `refines_imageProgW`: with `DevRefines D1 D2`, the relocation step and the
  construction's program at `D2` refine their runs at `D1`;
* `imageOfW_of_refines`: **a construction that succeeds with `D1` returns the same image with
  `D2`.**

The proofs follow the program's shape (`refines_auto`): every step other than a development call
or the relocation step's recursive call is the same program on both sides (`Refines.refl`).
-/

namespace Ix.CompileCert.Img

open Ix (Name Expr ConstantInfo)
open Ix.Compile.Image (GenM GenState GenOptions ImageSpec Image LCtx)

theorem run_bind {α β : Type} (x : GenM α) (f : α → GenM β) (st : GenState) :
    (x >>= f).run st = (do let (a, st1) ← x.run st; (f a).run st1) := rfl

theorem run_pure {α : Type} (a : α) (st : GenState) : (pure a : GenM α).run st = .ok (a, st) := rfl

/-- Every successful run of `x` is a run of `y`: from the same state, `y` returns the same value and
ends in the same state. -/
def Refines {α : Type} (x y : GenM α) : Prop :=
  ∀ st r, x.run st = .ok r → y.run st = .ok r

namespace Refines

theorem refl {α : Type} (x : GenM α) : Refines x x := fun _ _ h => h

theorem trans {α : Type} {x y z : GenM α} (hxy : Refines x y) (hyz : Refines y z) : Refines x z :=
  fun st r h => hyz st r (hxy st r h)

theorem bind {α β : Type} {x y : GenM α} {f g : α → GenM β} (hx : Refines x y)
    (hf : ∀ a, Refines (f a) (g a)) : Refines (x >>= f) (y >>= g) := by
  intro st r h
  rw [run_bind] at h ⊢
  cases hxr : x.run st with
  | error e => rw [hxr] at h; cases h
  | ok p =>
    obtain ⟨a, st1⟩ := p
    rw [hxr] at h
    rw [hx st _ hxr]
    exact hf a st1 r h

theorem liftExcept {α : Type} {x y : Except String α} (h : ∀ a, x = .ok a → y = .ok a) :
    Refines (Ix.Compile.Image.liftExcept x) (Ix.Compile.Image.liftExcept y) := by
  intro st r hx
  cases x with
  | error e => cases hx
  | ok a => rw [h a rfl]; exact hx

theorem forIn_list {α β : Type} {f g : α → β → GenM (ForInStep β)}
    (hfg : ∀ a b, Refines (f a b) (g a b)) :
    ∀ (l : List α) (b : β), Refines (forIn l b f) (forIn l b g)
  | [], b => by simp only [List.forIn_nil]; exact refl _
  | a :: l, b => by
    simp only [List.forIn_cons]
    refine bind (hfg a b) fun r => ?_
    cases r with
    | done b' => exact refl _
    | yield b' => exact forIn_list hfg l b'

theorem forIn_array {α β : Type} {f g : α → β → GenM (ForInStep β)}
    (hfg : ∀ a b, Refines (f a b) (g a b)) (xs : Array α) (b : β) :
    Refines (forIn xs b f) (forIn xs b g) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_list hfg _ b

theorem forIn'_list {α β : Type} :
    ∀ (l : List α) {f g : (a : α) → a ∈ l → β → GenM (ForInStep β)},
      (∀ a h b, Refines (f a h b) (g a h b)) → ∀ b, Refines (forIn' l b f) (forIn' l b g)
  | [], _, _, _, b => by simp only [List.forIn'_nil]; exact refl _
  | a :: l, _, _, hfg, b => by
    simp only [List.forIn'_cons]
    refine bind (hfg a _ b) fun r => ?_
    cases r with
    | done b' => exact refl _
    | yield b' => exact forIn'_list l (fun a h b => hfg a _ b) b'

theorem forIn'_range {β : Type} (r : Std.Legacy.Range)
    {f g : (a : Nat) → a ∈ r → β → GenM (ForInStep β)}
    (hfg : ∀ a h b, Refines (f a h b) (g a h b)) (b : β) : Refines (forIn' r b f) (forIn' r b g) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact forIn'_list _ (fun a h b => hfg a _ b) b

theorem forIn_range {β : Type} (r : Std.Legacy.Range) {f g : Nat → β → GenM (ForInStep β)}
    (hfg : ∀ a b, Refines (f a b) (g a b)) (b : β) : Refines (forIn r b f) (forIn r b g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_list hfg _ b

/-- Run from the initial state, a program's refinement returns its value. -/
theorem run' {α : Type} {x y : GenM α} (h : Refines x y) {a : α}
    (hx : Ix.Compile.Image.GenM.run' x = .ok a) : Ix.Compile.Image.GenM.run' y = .ok a := by
  unfold Ix.Compile.Image.GenM.run' StateT.run' at hx ⊢
  cases hr : x.run {} with
  | error e =>
    have e1 : x {} = Except.error e := hr
    rw [e1] at hx; cases hx
  | ok p =>
    have e1 : x {} = Except.ok p := hr
    have e2 : y {} = Except.ok p := h _ _ hr
    rw [e1] at hx; rw [e2]; exact hx

end Refines

/-- `D2` returns `D1`'s result on every call `D1` succeeds on. -/
structure DevRefines (D1 D2 : DevOps) : Prop where
  subst : ∀ xs vs e r, D1.subst xs vs e = .ok r → D2.subst xs vs e = .ok r
  inst : ∀ f args r, D1.inst f args = .ok r → D2.inst f args = .ok r

theorem DevRefines.trans {D1 D2 D3 : DevOps} (h12 : DevRefines D1 D2) (h23 : DevRefines D2 D3) :
    DevRefines D1 D3 :=
  ⟨fun xs vs e r h => h23.subst xs vs e r (h12.subst xs vs e r h),
    fun f args r h => h23.inst f args r (h12.inst f args r h)⟩

theorem DevRefines.lift_subst {D1 D2 : DevOps} (hD : DevRefines D1 D2) (xs : Array Name)
    (vs : Array Expr) (e : Expr) :
    Refines (Ix.Compile.Image.liftExcept (D1.subst xs vs e))
      (Ix.Compile.Image.liftExcept (D2.subst xs vs e)) :=
  Refines.liftExcept (hD.subst xs vs e)

theorem DevRefines.lift_inst {D1 D2 : DevOps} (hD : DevRefines D1 D2) (f : Expr) (args : Array Expr) :
    Refines (Ix.Compile.Image.liftExcept (D1.inst f args))
      (Ix.Compile.Image.liftExcept (D2.inst f args)) :=
  Refines.liftExcept (hD.inst f args)

/-- The refinement of a program by the same program at a refining development, by the program's
shape: the development calls by `hD`, the relocation step's recursive call by `ih`, every other step
the same program on both sides. -/
syntax "refines_auto" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| refines_auto) => `(tactic| repeat' first
    | with_reducible exact Refines.refl _
    | with_reducible exact hD.lift_subst _ _ _
    | with_reducible exact hD.lift_inst _ _
    | with_reducible exact ih ..
    | with_reducible refine Refines.bind ?_ (fun _ => ?_)
    | with_reducible refine Refines.forIn'_range _ (fun _ _ _ => ?_) _
    | with_reducible refine Refines.forIn_range _ (fun _ _ => ?_) _
    | with_reducible refine Refines.forIn_array (fun _ _ => ?_) _ _
    | split
    | dsimp only)

/-- **The relocation step at a refining development** refines it at the first. -/
theorem refines_buildRecAppW {D1 D2 : DevOps} (hD : DevRefines D1 D2) :
    ∀ (fuel : Nat) (c : LCtx) (t : Nat) (idx : Array Expr) (major : Expr),
      Refines (buildRecAppW D1 fuel c t idx major) (buildRecAppW D2 fuel c t idx major)
  | 0, c, t, idx, major => by unfold buildRecAppW; exact Refines.refl _
  | fuel + 1, c, t, idx, major => by
    have ih := refines_buildRecAppW hD fuel c
    unfold buildRecAppW
    refines_auto

/-- **The construction's program at a refining development** refines it at the first. -/
theorem refines_imageProgW {D1 D2 : DevOps} (hD : DevRefines D1 D2) (opts : GenOptions)
    (const? : Name → Option ConstantInfo) (spec : ImageSpec) (r : Name) :
    Refines (imageProgW D1 opts const? spec r) (imageProgW D2 opts const? spec r) := by
  have ih := refines_buildRecAppW hD
  unfold imageProgW
  refines_auto

/-- **A construction that succeeds with one development returns the same image with a development
that refines it.** -/
theorem imageOfW_of_refines {D1 D2 : DevOps} (hD : DevRefines D1 D2) {opts : GenOptions}
    {const? : Name → Option ConstantInfo} {spec : ImageSpec} {r : Name} {img : Image}
    (h : imageOfW D1 opts const? spec r = .ok img) : imageOfW D2 opts const? spec r = .ok img :=
  (refines_imageProgW hD opts const? spec r).run' h

end Ix.CompileCert.Img
