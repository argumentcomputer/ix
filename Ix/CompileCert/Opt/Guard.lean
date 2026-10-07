import Ix.CompileCert.Opt.O4

/-!
# M7 L3-def: the proof-justified passes decline outside a definition's value

O7, O8 (`Engine.pjPasses`) and O9, O10, O12 (`Engine.emitPasses`) end with the site guard
`if !pjAllowed o then none` (`Opt/Packed.lean`: `pjAllowed o := o.site.isSome`, decision 5, D1:
they fire only in the value of a definition, for its canonical `_ix` form). A firing passed the
guard (`O7_pjAllowed`, …), so at an occurrence with no site they return `none`
(`O7_site_none`, …). The proofs walk the do-block (`owalk`): every bind that succeeded
(`obind`), every guard passed (`oguard`), every matcher split (its failing branch is a `none`),
until the site guard.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Pass.Opt

/-- A run through a `none`, without `simp` (the walk's live branches are large). -/
macro "onone " h:ident : tactic =>
  `(tactic| first
    | (dsimp only at $h:ident; rw [onone_bind] at $h:ident; cases $h:ident)
    | (rw [onone_bind] at $h:ident; cases $h:ident)
    | (cases $h:ident; done))

/-- One step down a successful run of a do-block: a bind that succeeded, a guard passed, or a
matcher split (its failing branches closed). -/
macro "ostep " h:ident : tactic => `(tactic| first
  | (have hg := by exact obind.1 $h:ident
     obtain ⟨_, _, $h:ident⟩ := hg
     try dsimp only at $h:ident)
  | (have hg := by exact oguard $h:ident
     obtain ⟨_, $h:ident⟩ := hg)
  | (split at $h:ident <;> try onone $h:ident))

/-- Walk every successful run down past the site guard, then use it. -/
syntax "owalk " ident : tactic
macro_rules
  | `(tactic| owalk $h:ident) => `(tactic| first
      | exact bnot_false (by assumption)
      | (ostep $h:ident <;> owalk $h:ident))

theorem O7_pjAllowed {env : OptEnv} {o : Occ} {e : Expr} (h : O7.apply env o = some e) :
    pjAllowed o = true := by
  unfold O7.apply at h
  obtain ⟨⟨k, r⟩, _, h⟩ := obind.1 h
  try dsimp only at h
  owalk h

theorem O8_pjAllowed {env : OptEnv} {o : Occ} {e : Expr} (h : O8.apply env o = some e) :
    pjAllowed o = true := by
  unfold O8.apply at h
  obtain ⟨⟨k, r⟩, _, h⟩ := obind.1 h
  try dsimp only at h
  owalk h

theorem O9_pjAllowed {env : OptEnv} {o : Occ} {x : Expr × Array ConstantInfo}
    (h : O9.apply env o = some x) : pjAllowed o = true := by
  unfold O9.apply at h
  obtain ⟨⟨k, r⟩, _, h⟩ := obind.1 h
  try dsimp only at h
  owalk h

theorem O10_pjAllowed {env : OptEnv} {o : Occ} {x : Expr × Array ConstantInfo}
    (h : O10.apply env o = some x) : pjAllowed o = true := by
  unfold O10.apply at h
  owalk h

set_option maxRecDepth 16384 in
theorem O12_pjAllowed {env : OptEnv} {o : Occ} {x : Expr × Array ConstantInfo}
    (h : O12.apply env o = some x) : pjAllowed o = true := by
  unfold O12.apply at h
  owalk h

theorem pjAllowed_of_site {o : Occ} (h : pjAllowed o = true) : o.site.isSome = true := h

/-- At an occurrence with no site, every proof-justified pass declines. -/
theorem pj_site_none {env : OptEnv} {o : Occ} (hs : o.site = none) :
    O7.apply env o = none ∧ O8.apply env o = none ∧ O9.apply env o = none ∧
      O10.apply env o = none ∧ O12.apply env o = none := by
  have hf : pjAllowed o = false := by unfold pjAllowed; rw [hs]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases h : O7.apply env o with
    | none => rfl
    | some _ => have := O7_pjAllowed h; rw [hf] at this; cases this
  · cases h : O8.apply env o with
    | none => rfl
    | some _ => have := O8_pjAllowed h; rw [hf] at this; cases this
  · cases h : O9.apply env o with
    | none => rfl
    | some _ => have := O9_pjAllowed h; rw [hf] at this; cases this
  · cases h : O10.apply env o with
    | none => rfl
    | some _ => have := O10_pjAllowed h; rw [hf] at this; cases this
  · cases h : O12.apply env o with
    | none => rfl
    | some _ => have := O12_pjAllowed h; rw [hf] at this; cases this

end Ix.CompileCert.Opt
