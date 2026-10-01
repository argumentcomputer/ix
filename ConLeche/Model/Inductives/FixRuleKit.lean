module

public import ConLeche.Model.Inductives.FixRecPre
public section

/-!
# The rule right-hand side's gradedness: the kit (task #188)

The sum route certifies a rule's right-hand side by the kernel's own
inference run at the pre-recursor environment; a recursive rule
mentions the recursor, so its gradedness is proved semantically from
the model instead (`FixRuleOkP.lean`).  This module holds the kit: the
minor space's application chain, the ih-moved index expressions'
grading and validity, domain walks over prefixes, appends and lifted
fields, and the validity walk over binder data.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## λ-towers with the binders' own bits -/

/-- **A λ-tower with the telescope's own bits inhabits its Π-tower's
reading** (`mkLamsC_mem` with per-binder bits). -/
theorem mkLamsAV_bits_mem {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b T ds →
      interp V ρ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b) ∈ˢ interp V ρ (mkPisAV ds T)
  | [], _, _, h => h.2.1
  | d :: ds, ρ, hz, h => by
    show (lamR d.2.1 (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b))
      ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun a => interp V (cons a ρ) (mkPisAV ds T)
    exact lamR_mem_zero_agree Iff.rfl
      fun a ha => mkLamsAV_bits_mem (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha)

/-- **A λ-tower with the telescope's own bits is graded.** -/
theorem mkLamsAV_bits_wellDenoted {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b T ds →
      WellDenoted V ρ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b)
  | [], _, _, h => h.1
  | d :: ds, ρ, hz, h => by
    show WellDenoted V ρ (.lam d.2.1 d.2.2 (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b))
    rw [WellDenoted_lam]
    refine ⟨h.1, fun a ha => mkLamsAV_bits_wellDenoted (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV ds T),
       fun a ha => mkLamsAV_bits_mem (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha),
       fun h0 a ha => underTowerOk_res_univZero ((hz d (.head _)).mpr h0)
         (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha)⟩⟩

/-- **A λ-tower with the telescope's own bits is bit-valid.** -/
theorem mkLamsAV_bits_validV {b : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      UnderTowerValid ρ b ds → AnnotValid V ρ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b)
  | [], _, h => h
  | d :: ds, ρ, h => by
    show AnnotValid V ρ (.lam d.2.1 d.2.2 (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b))
    rw [AnnotValid_lam]
    exact ⟨h.1, fun a ha => mkLamsAV_bits_validV (h.2 a ha)⟩

/-! ## The ih-moved index expressions -/

/-! ## Domain walks -/

/-- A walk over a prefix. -/
theorem domsWalk_take :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} (k : Nat),
      DomsWalk ρ ds → DomsWalk ρ (ds.take k)
  | [], _, _, _ => by simp [DomsWalk]
  | _ :: _, _, 0, _ => trivial
  | d :: ds, ρ, k + 1, h => ⟨h.1, fun a ha => domsWalk_take k (h.2 a ha)⟩

/-- A walk over an append: the prefix's walk and the suffix's at every
fitting spine of the prefix. -/
theorem domsWalk_append :
    ∀ {xs ys : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      DomsWalk ρ xs →
      (∀ as : List V, SpineFit ρ (xs.map (·.2.2)) as → DomsWalk (consList as ρ) ys) →
      DomsWalk ρ (xs ++ ys)
  | [], ys, ρ, _, hys => by simpa using hys [] trivial
  | x :: xs, ys, ρ, hx, hys => by
    refine ⟨hx.1, fun a ha => domsWalk_append (hx.2 a ha) fun as hsp => ?_⟩
    have := hys (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- A walk is insensitive to the bits. -/
theorem domsWalk_rebit (b : Nat) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, DomsWalk ρ ds → DomsWalk ρ (rebit b ds)
  | [], _, _ => trivial
  | _ :: ds, _, h => ⟨h.1, fun a ha => domsWalk_rebit b (ds := ds) (h.2 a ha)⟩

/-- Lifted fields walk at a frame shifting to a frame where they are
graded. -/
theorem domsWalk_liftDoms {w n : Nat} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat) (σ : Nat → V),
      FieldsOkB w (shiftE n k σ) (ds.map (·.2.2)) → DomsWalk σ (liftDoms n k ds)
  | [], _, _, _ => trivial
  | d :: ds, k, σ, h => by
    refine ⟨?_, fun a ha => ?_⟩
    · show WellDenoted V σ (d.2.2.liftN n k)
      rw [WellDenoted_liftN]; exact h.1
    · have ha' : a ∈ˢ interp V (shiftE n k σ) d.2.2 := by
        rwa [show interp V σ (d.2.2.liftN n k) = interp V (shiftE n k σ) d.2.2 from
          interp_liftN V n d.2.2 k σ] at ha
      refine domsWalk_liftDoms (w := w) ds (k + 1) (cons a σ) ?_
      rw [shiftE_succ_cons']
      exact h.2.2 a ha'

/-! ## Validity walks -/

/-- A tower is valid under binder data from the validity of every
domain at its prefix's fitting spines and of the body at the leaves. -/
theorem underTowerValid_of :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {b : AnnotTerm},
      (∀ k d, ds[k]? = some d → ∀ as : List V, SpineFit ρ ((ds.take k).map (·.2.2)) as →
        AnnotValid V (consList as ρ) d.2.2) →
      (∀ as : List V, SpineFit ρ (ds.map (·.2.2)) as → AnnotValid V (consList as ρ) b) →
      UnderTowerValid ρ b ds
  | [], ρ, b, _, hb => by
    have := hb [] trivial
    rwa [consList_nil] at this
  | d :: ds, ρ, b, hd, hb => by
    refine ⟨by have := hd 0 d rfl [] trivial; rwa [consList_nil] at this,
      fun a ha => underTowerValid_of ?_ ?_⟩
    · intro k d' hk as hsp
      have := hd (k + 1) d' (by simpa using hk) (a :: as) ⟨ha, hsp⟩
      rwa [consList_cons] at this
    · intro as hsp
      have := hb (a :: as) ⟨ha, hsp⟩
      rwa [consList_cons] at this

end ConLeche.Model
