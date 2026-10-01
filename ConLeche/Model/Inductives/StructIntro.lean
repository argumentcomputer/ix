module

public import ConLeche.Model.Claims
public import ConLeche.Semantics.Tower.TowerRec

public section

/-!
# The direct-structure leaves' bit validity and P packages (task #175, stage 4a)

`AnnotValid` for the three synthesized leaves, completing the
`WellDenotedV` currency (`WellDenoted` landed with the leaves themselves in
`SetBase/Tower{Leaf,Mk,Rec}.lean`).

The leaves contain **no `.pi` node** — λ, application, constants,
bound variables and the uniform `.proj` spelling only — so their bit
validity is pure hereditary plumbing: `AnnotValid`'s one genuine
clause (the `pi` codomain component) never fires, and every lemma
here is a walk with no semantic content beyond the λ-clause guards.
`UnderTowerValid` is the single hereditary premise shape, shared by
all three leaves (each IS a `mkLamsC` tower).

The `WellDenotedV` packages (`structTyAV_okP`/`structMkAV_okP`/
`structRecAV_okP`) pair the SetBase `_ok2` laws with the validity
walks — the `hAok`/`hAvalid` rows of `declStep_preserves_of_basis_cons`, per
leaf.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- Hereditary bit validity of a field chain. -/
@[expose] def FieldsValid (ρ : Nat → V) : List AnnotTerm → Prop
  | [] => True
  | F :: Fs => AnnotValid V ρ F ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsValid (cons a ρ) Fs

/-- The carrier body (graph regime) is bit-valid (no `pi` nodes;
hereditary). -/
theorem towerBodyAVPos_validV {w : Nat} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      AnnotValid V ρ (towerBodyAVPos w Fs)
  | [], _, _ => trivial
  | F :: Fs, ρ, hv => by
    show AnnotValid V ρ (.app (.app (.const .psigma [w, w]) F)
      (.lam (w + 1) F (towerBodyAVPos w Fs)))
    rw [AnnotValid_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValid_app]
      exact ⟨trivial, hv.1⟩
    · rw [AnnotValid_lam]
      exact ⟨hv.1, fun a ha => towerBodyAVPos_validV (hv.2 a ha)⟩

/-- The carrier body (squash regime) is bit-valid: every `pi` node
carries bit `0` over a truth-value codomain (`piR 0`, or `Empty`). -/
theorem sqBodyAV_validV :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsValid ρ Fs →
      AnnotValid V ρ (sqBodyAV Fs)
  | [], _, _ => trivial
  | F :: Fs, ρ, hv => by
    show AnnotValid V ρ (negAV (.pi 0 0 F (negAV (sqBodyAV Fs))))
    unfold negAV
    rw [AnnotValid_pi]
    refine ⟨?_, fun _ _ => by simp, fun _ _ _ => ?_⟩
    · rw [AnnotValid_pi]
      refine ⟨hv.1, fun x hx => ?_, fun _ x _ => ?_⟩
      · rw [AnnotValid_pi]
        exact ⟨sqBodyAV_validV (hv.2 x hx), fun _ _ => by simp,
          fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩
      · exact piR_zero_mem_univZero
    · rw [← univ_zero]; exact empty_mem_univ 0

/-- The carrier body is bit-valid, both regimes. -/
theorem towerBodyAV_validV {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V}
    (hv : FieldsValid ρ Fs) : AnnotValid V ρ (towerBodyAV w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_validV hv
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_validV hv

/-- The uniform projection spelling is bit-valid whenever its subject
is (the projections' validity clause is hereditary). -/
theorem projAV_validV :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ e → AnnotValid V σ (projAV i e)
  | 0, e, σ, h => by
    show AnnotValid V σ (.fst e)
    rw [AnnotValid_fst]
    exact h
  | i + 1, e, σ, h => by
    show AnnotValid V σ (projAV i (.snd e))
    exact projAV_validV (by rw [AnnotValid_snd]; exact h)

/-- Application spines are bit-valid from their parts. -/
theorem mkAppN_validV :
    ∀ {args : List AnnotTerm} {f : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ f → (∀ a ∈ args, AnnotValid V σ a) →
      AnnotValid V σ (AnnotTerm.mkAppN f args)
  | [], _, _, hf, _ => hf
  | a :: args, f, σ, hf, hargs => by
    rw [AnnotTerm.mkAppN_cons]
    refine mkAppN_validV ?_ fun a' ha' => hargs a' (.tail _ ha')
    rw [AnnotValid_app]
    exact ⟨hf, hargs a (.head _)⟩

/-- The constructor tupler is bit-valid at a fitting frame — the one
walk that crosses the λ-frame lifts (`AnnotValid_liftN` +
`shiftE_consList`). -/
theorem mkTowerGoPos_validV {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρp : Nat → V} {bs : List V},
      FieldsValid ρp Fs → FieldsBound w ρp Fs → SpineFit ρp Fs bs →
      AnnotValid V (consList bs ρp) (mkTowerGoPos w Fs)
  | [], _, [], _, _, _ => trivial
  | [], _, _ :: _, _, _, hsp => hsp.elim
  | _ :: _, _, [], _, _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hv, hb, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    show AnnotValid V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (w + 1) (F.liftN (Fs.length + 1))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoPos w Fs))
    rw [AnnotValid_app]
    refine ⟨?_, mkTowerGoPos_validV hw (hv.2 b hsp.1) (hb.2 b hsp.1) hsp.2⟩
    rw [AnnotValid_app]
    refine ⟨?_, by rw [AnnotValid_bvar]; trivial⟩
    rw [AnnotValid_app]
    refine ⟨?_, ?_⟩
    · rw [AnnotValid_app]
      refine ⟨by rw [AnnotValid_const]; trivial, ?_⟩
      rw [AnnotValid_liftN, hshift]
      exact hv.1
    · rw [AnnotValid_lam]
      refine ⟨by rw [AnnotValid_liftN, hshift]; exact hv.1, ?_⟩
      intro x hx
      rw [hA] at hx
      rw [AnnotValid_liftN, ← cons_shiftE, hshift]
      exact towerBodyAV_validV (hv.2 x hx)

/-- The constructor tupler is bit-valid at a fitting frame, both
regimes. -/
theorem mkTowerGo_validV {w : Nat} {Fs : List AnnotTerm} {ρp : Nat → V}
    {bs : List V} (hv : FieldsValid ρp Fs)
    (hb : w ≠ 0 → FieldsBound w ρp Fs) (hsp : SpineFit ρp Fs bs) :
    AnnotValid V (consList bs ρp) (mkTowerGo w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; trivial
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_validV hw hv (hb hw) hsp

/-- The single hereditary validity premise of a `mkLamsC` leaf. -/
@[expose] def UnderTowerValid (ρ : Nat → V) (b : AnnotTerm) :
    List (Nat × Nat × AnnotTerm) → Prop
  | [] => AnnotValid V ρ b
  | d :: ds => AnnotValid V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → UnderTowerValid (cons a ρ) b ds

/-- A constant-bit λ-tower is bit-valid from the hereditary premise
(the λ clause of `AnnotValid` carries no bit component). -/
theorem mkLamsC_validV {m : Nat} {b : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      UnderTowerValid ρ b ds → AnnotValid V ρ (mkLamsC m ds b)
  | [], _, h => h
  | d :: ds, ρ, h => by
    show AnnotValid V ρ (.lam m d.2.2 (mkLamsC m ds b))
    rw [AnnotValid_lam]
    exact ⟨h.1, fun a ha => mkLamsC_validV (h.2 a ha)⟩

/-! ## The `WellDenotedV` packages -/

end ConLeche.Model
