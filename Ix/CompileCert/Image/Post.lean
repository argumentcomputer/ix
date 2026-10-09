import Ix.CompileCert.Image.SimRec
import Ix.Compile.Pass.ImageView

/-!
# M7 L2a-syn: what a successful run of the construction establishes

`Post P x`: every successful run of `x` returns a value satisfying `P`. With `post_auto` (the
program's shape, as `mono_auto`), the facts the construction's code makes true by construction:

* `imageOfP_type` (**L2a-2**): the image's type is Lean's recursor type over the canonical
  constants, `img.type = spec.tr rv.type` (`imageOf` sets `type := ty`, `ty = spec.tr rv.cnst.type`).
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo InductiveVal RecursorVal)
open Ix.Compile.Image (GenM GenState freshName Local telescope LCtx Elim LeanMinor ImageSpec
  GenOptions Image)

/-- Every successful run of `x` returns a value satisfying `P`. -/
def Post {α : Type} (P : α → Prop) (x : GenM α) : Prop :=
  ∀ st a st1, x.run st = .ok (a, st1) → P a

theorem Post.pure {α : Type} {P : α → Prop} {a : α} (h : P a) : Post P (Pure.pure a : GenM α) := by
  intro st a' st1 hx; rw [run_pure] at hx; cases hx; exact h

theorem Post.bind {α β : Type} {P : β → Prop} {x : GenM α} {f : α → GenM β}
    (hf : ∀ a, Post P (f a)) : Post P (x >>= f) := by
  intro st b st2 h
  rw [run_bind] at h
  cases hxr : x.run st with
  | error e => rw [hxr] at h; cases h
  | ok p =>
    obtain ⟨a, st1⟩ := p
    rw [hxr] at h
    exact hf a _ _ _ h

theorem Post.bind_of {α β : Type} {Q : α → Prop} {P : β → Prop} {x : GenM α} {f : α → GenM β}
    (hx : Post Q x) (hf : ∀ a, Q a → Post P (f a)) : Post P (x >>= f) := by
  intro st b st2 h
  rw [run_bind] at h
  cases hxr : x.run st with
  | error e => rw [hxr] at h; cases h
  | ok p =>
    obtain ⟨a, st1⟩ := p
    rw [hxr] at h
    exact hf a (hx _ _ _ hxr) _ _ _ h

theorem Post.throw {α : Type} {P : α → Prop} (e : String) : Post P (throw e : GenM α) := by
  intro st a st1 h; cases h

theorem Post.liftExcept {α : Type} (x : Except String α) :
    Post (fun a => x = .ok a) (Ix.Compile.Image.liftExcept x) := by
  intro st a st1 h
  cases x with
  | error e => cases h
  | ok a' => simp only [Ix.Compile.Image.liftExcept] at h; cases h; rfl

theorem Post.run' {α : Type} {P : α → Prop} {x : GenM α} (h : Post P x) {a : α}
    (hx : Ix.Compile.Image.GenM.run' x = .ok a) : P a := by
  unfold Ix.Compile.Image.GenM.run' StateT.run' at hx
  cases hr : x.run {} with
  | error e =>
    have e1 : x {} = Except.error e := hr
    rw [e1] at hx; cases hx
  | ok p =>
    obtain ⟨a', st1⟩ := p
    have e1 : x {} = Except.ok (a', st1) := hr
    rw [e1] at hx; cases hx
    exact h _ _ _ hr

/-- The program's shape: binds whose results are not needed, the branches of `match`/`if`,
and the final `pure` (left to `tac`). -/
syntax "post_auto" tactic : tactic
macro_rules
  | `(tactic| post_auto $tac) => `(tactic| first
    | done
    | with_reducible exact Post.throw _
    | (with_reducible refine Post.pure ?_ <;> $tac)
    | (with_reducible refine Post.bind (fun _ => ?_) <;> post_auto $tac)
    | (split <;> post_auto $tac)
    | (dsimp only <;> post_auto $tac))

/-- **L2a-2: the image's type.** `img(r)` has Lean's type over the canonical constants,
`tr_N(type r)`: `imageOf` sets `type := ty` with `ty = spec.tr rv.cnst.type`. That the image's
*value* has this type is the checker's per compile (or L2a-4). -/
theorem imageOfW_type (D : DevOps) {opts : GenOptions} {const? : Name → Option ConstantInfo} {spec : ImageSpec}
    {r : Name} {img : Image} (h : imageOfW D opts const? spec r = .ok img) :
    ∃ rv, const? r = some (.recInfo rv) ∧ img.type = spec.tr rv.cnst.type := by
  unfold imageOfW imageProgW at h
  refine Post.run' (P := fun img => ∃ rv, const? r = some (.recInfo rv) ∧ img.type = spec.tr rv.cnst.type)
    ?_ h
  refine Post.bind_of (Post.liftExcept _) fun rv hrv => ?_
  have hc := recOf_ok hrv
  set_option maxRecDepth 20000 in
  post_auto exact ⟨rv, hc, rfl⟩

theorem imageOfP_type {opts : GenOptions} {const? : Name → Option ConstantInfo} {spec : ImageSpec}
    {r : Name} {img : Image} (h : imageOfP opts const? spec r = .ok img) :
    ∃ rv, const? r = some (.recInfo rv) ∧ img.type = spec.tr rv.cnst.type :=
  imageOfW_type coreDev h

/-- L2a-2 for the executable itself (no development is involved in the type). -/
theorem imageOf_type {opts : GenOptions} {const? : Name → Option ConstantInfo} {spec : ImageSpec}
    {r : Name} {img : Image} (h : Ix.Compile.Image.imageOf opts const? spec r = .ok img) :
    ∃ rv, const? r = some (.recInfo rv) ∧ img.type = spec.tr rv.cnst.type :=
  imageOfW_type execDev (by rw [← imageOf_eq]; exact h)

/-- L2a-2 in the compiler: the type of the image constant of a changed block's Lean recursor
(`BlockView.image`, view names mapped back to `E` names) is Lean's type over the canonical constants,
mapped back. -/
theorem blockView_image_type {inp : Ix.Compile.Pass.ViewInput} {v : Ix.Compile.Pass.BlockView}
    {r : Name} {img : Image} (h : v.image inp r = .ok img) :
    ∃ rv, v.const? inp r = some (.recInfo rv) ∧
      img.type = Ix.Compile.Canon.canonicalizeConstNames v.back (v.spec.tr rv.cnst.type) := by
  unfold Ix.Compile.Pass.BlockView.image at h
  cases hi : Ix.Compile.Image.imageOf {} (v.const? inp) v.spec r with
  | error e => rw [hi] at h; cases h
  | ok img0 =>
    rw [hi] at h
    cases h
    obtain ⟨rv, hrv, hty⟩ := imageOf_type hi
    exact ⟨rv, hrv, by rw [← hty]⟩

end Ix.CompileCert.Img
