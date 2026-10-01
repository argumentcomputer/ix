module

public import ConLeche.Model.Inductives.SumRecFrames
import ConLeche.Model.Inductives.SumStageCtor
import ConLeche.Model.IndPointKit
public section

/-!
# The sum recursor's cons (task #175 sum-types, indexed)

`stageSumRec`: the P step at the sum recursor's cons.  The stored
recursor is the generated one: its data is read off syntactically
(`sumRecData_of`), its leaf is `sumRecAV` over that data, the
field chains, the index readings and the sources, the frames' walks
(`sumRecLeafFacts` over `sumRecFrames`) give the leaf's grading and
membership, the capability laws are vacuous (the block claims no eta
or unit law; rule K needs no law — the kernel's K rescue is certified
by proof irrelevance at the fire), and every stored rule's law is
`sumRecRuleLaw` over the generated rule at its constructor's position
(an inert rule owes nothing).  The rule law consumes the kernel's
index pin (`IotaIndexPin`, from `iotaIndexOk`): the constructor's
index values at the fields are the recursor application's index
arguments.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- A lifted telescope strips as the telescope does, the body lifted
above the stripped binders. -/
theorem stripPis_liftLooseBVars :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr} (n c : Nat),
      e.stripPis k = some (bs, body) →
      ∃ bs', (e.liftLooseBVars n c).stripPis k = some (bs', body.liftLooseBVars n (c + k))
  | 0, e, bs, body, n, c, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis]⟩
  | k + 1, e, bs, body, n, c, h => by
    match e, h with
    | .forallE ty b mb, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hs, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨bs'', hs''⟩ := stripPis_liftLooseBVars k n (c + 1) hs
      refine ⟨(ty.liftLooseBVars n c, mb) :: bs'', ?_⟩
      show (Expr.forallE (Expr.liftLooseBVars n c ty) (Expr.liftLooseBVars n (c + 1) b) mb).stripPis
        (k + 1) = _
      simp only [Expr.stripPis, hs'', Option.map_some]
      rw [show c + 1 + k = c + (k + 1) from by omega]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-! ## The rule data's shape -/

/-! ## The per-constructor facts across a cons -/

/-! ## The rule law -/

/-! ## The stage -/

end ConLeche.Model
