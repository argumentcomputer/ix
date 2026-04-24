module
public import Ix.Aiur.Stages.Bytecode

/-!
`LawfulBEq Block` / `LawfulBEq Ctrl` for the manual mutual `BEq` defined in
`Ix/Aiur/Stages/Bytecode.lean`. Unblocks `skeleton_eq_of_same_class` in
`DedupSound.lean` (the private `assignClasses_values_eq_of_classes_eq` wants
`LawfulBEq` on the element type).
-/

public section

namespace Aiur
namespace Bytecode

mutual
  private theorem Block.beq_self : ∀ b : Block, Block.beq b b = true
    | ⟨ops, ctrl⟩ => by
        simp only [Block.beq, beq_self_eq_true, Bool.true_and]
        exact Ctrl.beq_self ctrl

  private theorem Ctrl.beq_self : ∀ c : Ctrl, Ctrl.beq c c = true
    | .return _ _ => by simp [Ctrl.beq]
    | .yield _ _ => by simp [Ctrl.beq]
    | .match _ br none => by
        simp only [Ctrl.beq, beq_self_eq_true, Bool.true_and,
                   Ctrl.beqBranches_self br.toList]
    | .match _ br (some b) => by
        simp only [Ctrl.beq, beq_self_eq_true, Bool.true_and,
                   Ctrl.beqBranches_self br.toList, Block.beq_self b]
    | .matchContinue _ br none _ _ _ k => by
        simp only [Ctrl.beq, beq_self_eq_true, Bool.and_self,
                   Ctrl.beqBranches_self br.toList, Block.beq_self k]
    | .matchContinue _ br (some b) _ _ _ k => by
        simp only [Ctrl.beq, beq_self_eq_true, Bool.and_self,
                   Ctrl.beqBranches_self br.toList, Block.beq_self b,
                   Block.beq_self k]

  private theorem Ctrl.beqBranches_self :
      ∀ l : List (G × Block), Ctrl.beqBranches l l = true
    | [] => rfl
    | (k, b) :: rest => by
        simp only [Ctrl.beqBranches, beq_self_eq_true, Bool.true_and,
                   Block.beq_self b, Ctrl.beqBranches_self rest]
end

mutual
  private theorem Ctrl.eq_of_beq : ∀ {c₁ c₂ : Ctrl}, Ctrl.beq c₁ c₂ = true → c₁ = c₂
    | .return s₁ v₁, .return s₂ v₂, h => by
        simp only [Ctrl.beq, Bool.and_eq_true] at h
        obtain ⟨hs, hv⟩ := h
        rw [eq_of_beq hs, eq_of_beq hv]
    | .yield s₁ v₁, .yield s₂ v₂, h => by
        simp only [Ctrl.beq, Bool.and_eq_true] at h
        obtain ⟨hs, hv⟩ := h
        rw [eq_of_beq hs, eq_of_beq hv]
    | .match v₁ br₁ none, .match v₂ br₂ none, h => by
        simp only [Ctrl.beq, Bool.and_eq_true] at h
        obtain ⟨hv, hbr⟩ := h
        have hv' := eq_of_beq hv
        have hbr' : br₁.toList = br₂.toList := Ctrl.beqBranches_eq_of_beq hbr
        have hbr'' : br₁ = br₂ := Array.ext' hbr'
        rw [hv', hbr'']
    | .match v₁ br₁ (some b₁), .match v₂ br₂ (some b₂), h => by
        simp only [Ctrl.beq, Bool.and_eq_true] at h
        obtain ⟨⟨hv, hbr⟩, hb⟩ := h
        have hv' := eq_of_beq hv
        have hbr' : br₁.toList = br₂.toList := Ctrl.beqBranches_eq_of_beq hbr
        have hbr'' : br₁ = br₂ := Array.ext' hbr'
        have hb' := Block.eq_of_beq hb
        rw [hv', hbr'', hb']
    | .match _ _ none, .match _ _ (some _), h => by simp [Ctrl.beq] at h
    | .match _ _ (some _), .match _ _ none, h => by simp [Ctrl.beq] at h
    | .matchContinue v₁ br₁ none o₁ sa₁ sl₁ k₁,
      .matchContinue v₂ br₂ none o₂ sa₂ sl₂ k₂, h => by
        simp only [Ctrl.beq, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨hv, ho⟩, hsa⟩, hsl⟩, hbr⟩, hk⟩ := h
        have hv' := eq_of_beq hv
        have ho' := eq_of_beq ho
        have hsa' := eq_of_beq hsa
        have hsl' := eq_of_beq hsl
        have hbr' : br₁.toList = br₂.toList := Ctrl.beqBranches_eq_of_beq hbr
        have hbr'' : br₁ = br₂ := Array.ext' hbr'
        have hk' := Block.eq_of_beq hk
        rw [hv', ho', hsa', hsl', hbr'', hk']
    | .matchContinue v₁ br₁ (some b₁) o₁ sa₁ sl₁ k₁,
      .matchContinue v₂ br₂ (some b₂) o₂ sa₂ sl₂ k₂, h => by
        simp only [Ctrl.beq, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨hv, ho⟩, hsa⟩, hsl⟩, hbr⟩, hb⟩, hk⟩ := h
        have hv' := eq_of_beq hv
        have ho' := eq_of_beq ho
        have hsa' := eq_of_beq hsa
        have hsl' := eq_of_beq hsl
        have hbr' : br₁.toList = br₂.toList := Ctrl.beqBranches_eq_of_beq hbr
        have hbr'' : br₁ = br₂ := Array.ext' hbr'
        have hb' := Block.eq_of_beq hb
        have hk' := Block.eq_of_beq hk
        rw [hv', ho', hsa', hsl', hbr'', hb', hk']
    | .matchContinue _ _ none .., .matchContinue _ _ (some _) .., h => by
        simp [Ctrl.beq] at h
    | .matchContinue _ _ (some _) .., .matchContinue _ _ none .., h => by
        simp [Ctrl.beq] at h
    | .return _ _, .yield _ _, h => by simp [Ctrl.beq] at h
    | .return _ _, .match _ _ none, h => by simp [Ctrl.beq] at h
    | .return _ _, .match _ _ (some _), h => by simp [Ctrl.beq] at h
    | .return _ _, .matchContinue _ _ none .., h => by simp [Ctrl.beq] at h
    | .return _ _, .matchContinue _ _ (some _) .., h => by simp [Ctrl.beq] at h
    | .yield _ _, .return _ _, h => by simp [Ctrl.beq] at h
    | .yield _ _, .match _ _ none, h => by simp [Ctrl.beq] at h
    | .yield _ _, .match _ _ (some _), h => by simp [Ctrl.beq] at h
    | .yield _ _, .matchContinue _ _ none .., h => by simp [Ctrl.beq] at h
    | .yield _ _, .matchContinue _ _ (some _) .., h => by simp [Ctrl.beq] at h
    | .match _ _ none, .return _ _, h => by simp [Ctrl.beq] at h
    | .match _ _ (some _), .return _ _, h => by simp [Ctrl.beq] at h
    | .match _ _ none, .yield _ _, h => by simp [Ctrl.beq] at h
    | .match _ _ (some _), .yield _ _, h => by simp [Ctrl.beq] at h
    | .match _ _ none, .matchContinue _ _ none .., h => by simp [Ctrl.beq] at h
    | .match _ _ none, .matchContinue _ _ (some _) .., h => by simp [Ctrl.beq] at h
    | .match _ _ (some _), .matchContinue _ _ none .., h => by simp [Ctrl.beq] at h
    | .match _ _ (some _), .matchContinue _ _ (some _) .., h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ none .., .return _ _, h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ (some _) .., .return _ _, h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ none .., .yield _ _, h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ (some _) .., .yield _ _, h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ none .., .match _ _ none, h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ none .., .match _ _ (some _), h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ (some _) .., .match _ _ none, h => by simp [Ctrl.beq] at h
    | .matchContinue _ _ (some _) .., .match _ _ (some _), h => by simp [Ctrl.beq] at h

  private theorem Ctrl.beqBranches_eq_of_beq :
      ∀ {l₁ l₂ : List (G × Block)}, Ctrl.beqBranches l₁ l₂ = true → l₁ = l₂
    | [], [], _ => rfl
    | (k₁, b₁) :: rest₁, (k₂, b₂) :: rest₂, h => by
        simp only [Ctrl.beqBranches, Bool.and_eq_true] at h
        obtain ⟨⟨hk, hb⟩, hrest⟩ := h
        rw [eq_of_beq hk, Block.eq_of_beq hb,
            Ctrl.beqBranches_eq_of_beq hrest]
    | [], _ :: _, h => by simp [Ctrl.beqBranches] at h
    | _ :: _, [], h => by simp [Ctrl.beqBranches] at h

  private theorem Block.eq_of_beq : ∀ {b₁ b₂ : Block}, Block.beq b₁ b₂ = true → b₁ = b₂
    | ⟨ops₁, ctrl₁⟩, ⟨ops₂, ctrl₂⟩, h => by
        simp only [Block.beq, Bool.and_eq_true] at h
        obtain ⟨hops, hctrl⟩ := h
        rw [eq_of_beq hops, Ctrl.eq_of_beq hctrl]
end

private instance : LawfulBEq Ctrl where
  rfl := Ctrl.beq_self _
  eq_of_beq := Ctrl.eq_of_beq

instance : LawfulBEq Block where
  rfl := Block.beq_self _
  eq_of_beq := Block.eq_of_beq

/-- `LawfulBEq` for `FunctionLayout`. Its derived `BEq` performs
field-by-field comparison which agrees with structural equality. The derived
beq has the short-circuiting shape
`match i₁ == i₂ with | false => false | true => s₁ == s₂ && ...` so we split
on each inner match. -/
instance : LawfulBEq FunctionLayout where
  rfl := by
    rintro ⟨i, s, a, l⟩
    show (match i == i with
          | false => false
          | true => s == s && (a == a && l == l)) = true
    simp
  eq_of_beq := by
    rintro ⟨i₁, s₁, a₁, l₁⟩ ⟨i₂, s₂, a₂, l₂⟩ h
    change (match i₁ == i₂ with
            | false => false
            | true => s₁ == s₂ && (a₁ == a₂ && l₁ == l₂)) = true at h
    split at h
    · exact absurd h (by simp)
    rename_i hi
    obtain ⟨hs, ha, hl⟩ : s₁ = s₂ ∧ a₁ = a₂ ∧ l₁ = l₂ := by
      simpa [Bool.and_eq_true] using h
    have hi' : i₁ = i₂ := by simpa using hi
    subst hi'; subst hs; subst ha; subst hl
    rfl

end Bytecode
end Aiur

end -- public section
