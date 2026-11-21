module

public import IxC.Kernel.Semantics.DeclJ
public import IxC.Kernel.Rules.TransportKit

public section

/-!
# A declaration step extends the environment

Derivations move along `EnvExt` (`Rules/Transport.lean`): typing a theorem's value
where it is unfolded reads the theorem's own check in a later environment. This
module gives the extension for each declaration step the restated records
describe (`DeclRunJ`):

* a value kind (definition, theorem, opaque, axiom) conses one fresh constant
  whose name is not a projection-table key (`ConstantValRunJ` refuses the
  projection shapes), so it extends (`declRunJ_envExt`);
* a pinned basis block and an inductive block are premises: a step extends when
  every constant it adds is fresh and none is the table of a structure stored
  before the step. A structure's table is installed in the same step as the
  structure (or not at all, on the modeled route), which is what those premises
  ask of the inductive tier.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel

theorem projTableName_isProjFnShape (T : Key md) : (projTableName T).isProjFnShape = true :=
  rfl

/-- A fresh constant whose name passes the front door's shape test extends. -/
theorem envExt_of_constantValRunJ {J : Judgements md} {env : Env md} {cv : ConstantVal md}
    {type' : Expr md} (h : ConstantValRunJ J env cv type') {c : ConstantInfo md}
    (hc : c.name = cv.name) : EnvExt env ⟨c :: env.consts⟩ := by
  obtain ⟨hfresh, -, hshape, -⟩ := h
  refine EnvExt.cons (by rw [hc]; exact Option.isNone_iff_eq_none.mp hfresh) ?_
  intro T _ _ _ e
  rw [hc] at e
  rw [e, projTableName_isProjFnShape] at hshape
  exact nomatch hshape

/-- **Each declaration step extends**, given that basis blocks and inductive blocks
do. -/
theorem declRunJ_envExt {J : Judgements md} {Ind : List (ConstantInfo md) → Nat → Env md → Prop}
    {env : Env md}
    (hbasis : ∀ {kind : BasisKind} {env₂ : Env md}, DeclBasisRun env kind env₂ → EnvExt env env₂)
    (hind : ∀ {block : List (ConstantInfo md)} {nP : Nat} {env₂ : Env md},
      Ind block nP env₂ → EnvExt env env₂) :
    ∀ {d : Declaration md} {env₂ : Env md}, DeclRunJ J Ind env d env₂ → EnvExt env env₂
  | .defnDecl _ _ _, _, h => by
    obtain ⟨_, _, hcv, -, rfl, -⟩ := h
    exact envExt_of_constantValRunJ hcv rfl
  | .thmDecl _ _, _, h => by
    obtain ⟨_, _, hcv, -, -, rfl⟩ := h
    exact envExt_of_constantValRunJ hcv rfl
  | .opaqueDecl _ _, _, h => by
    obtain ⟨_, _, hcv, -, rfl⟩ := h
    exact envExt_of_constantValRunJ hcv rfl
  | .axiomDecl _, _, h => by
    rcases h with ⟨-, rfl⟩ | ⟨_, hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact EnvExt.refl _
    · exact envExt_of_constantValRunJ hcv rfl
    · exact EnvExt.refl _
  | .basisDecl _, _, h => hbasis h
  | .indDecl _ _, _, h => by
    simp only [DeclRunJ] at h
    split at h
    · exact hbasis h
    · exact hind h
  | .quotDecl _ _, _, h => by
    simp only [DeclRunJ] at h
    split at h
    · exact hbasis h
    · subst h; exact EnvExt.refl _

end Ix.Kernel.Semantics
