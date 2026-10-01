module

public import ConLeche.Model.Inductives.StructLaws
import ConLeche.Model.Inductives.StructRows
import ConLeche.Verify.InstLevels
public import ConLeche.Semantics.Tower.TowerWire
import ConLeche.Model.Annot.BitLevels
public section

/-!
# The direct block's stage data (task #175 W4c, P3 module 6, part 1)

The readings the leaves are built over, packaged per stored constant:
`FormerData` (the type former's Π-peel, its bits, gradings, bounds
and level dependence) and — later in the file — the constructor's.
Each is derived once from the stage's run (`formerData_of`) and
crossed to the later stage environments (`FormerData.cross`), where
the readings survive because the block's constants are stored and
the head's slot mentions none of them.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

theorem mkPisAV_inj :
    ∀ {pps₁ pps₂ : List (Nat × Nat × AnnotTerm)} {b₁ b₂ : AnnotTerm},
      pps₁.length = pps₂.length → mkPisAV pps₁ b₁ = mkPisAV pps₂ b₂ →
      pps₁ = pps₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | d₁ :: pps₁, d₂ :: pps₂, b₁, b₂, hlen, h => by
    simp only [mkPisAV, AnnotTerm.pi.injEq] at h
    obtain ⟨hu, hv, hA, hB⟩ := h
    obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by simpa using hlen) hB
    refine ⟨?_, rfl⟩
    congr 1
    exact Prod.ext hu (Prod.ext hv hA)

/-- A `.pi` context is a successful peel, with the peel's domains
reversed. -/
theorem stripPisAV_of_piTeleAV :
    ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R →
      ∃ pps : List (Nat × Nat × AnnotTerm),
        stripPisAV k T = some (pps, R) ∧ (pps.map (·.2.2)).reverse = Γ := by
  intro k T Γ R h
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons k u v A B R Γ' _ ih =>
    obtain ⟨pps, hst, hΓ⟩ := ih
    refine ⟨(u, v, A) :: pps, ?_, ?_⟩
    · simp only [stripPisAV, hst, Option.map_some]
    · simp [hΓ]

theorem DomsBelow.drop {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} (j : Nat), DomsBelow k ds →
      DomsBelow (k + j) (ds.drop j)
  | _, 0, h => by simpa using h
  | [], _ + 1, _ => trivial
  | _ :: ds, j + 1, h => by
    rw [List.drop_succ_cons, show k + (j + 1) = k + 1 + j from by omega]
    exact DomsBelow.drop (k := k + 1) (ds := ds) j h.2

/-! ## The former's data -/

/-- **The type former's reading, peeled**: at every assignment the
stored type reads as the Π-tower over the parameter data ending in
the result sort, with nonzero codomain bits, graded, bounded, and
depending only on the block's level parameters. -/
structure FormerData {env : Env} (m : EnvModel V env) (cvT : ConstantVal)
    (nP : Nat) (resSort : Level)
    (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop where
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvT.type
    = some (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))
  len : ∀ ψ : Name → Nat, (pps ψ).length = nP
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ pps ψ → d.2.1 ≠ 0
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (pps ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvT.levelParams, ψ₁ p = ψ₂ p) →
    pps ψ₁ = pps ψ₂ ∧ resSort.eval ψ₁ = resSort.eval ψ₂

/-- The former's data, from its `checkConstantVal` run at the
pre-block environment and the annotated telescope shape. -/
theorem formerData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {cvT cvTa : ConstantVal} {nP : Nat} {resSort : Level}
    {bs : List (Expr × ConLeche.BinderMeta)}
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa)
    (hstrip : cvTa.type.stripPis nP = some (bs, .sort resSort)) :
    ∃ pps : (Name → Nat) → List (Nat × Nat × AnnotTerm),
      FormerData mp.base2 cvTa nP resSort pps := by
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', htr', hst,
    hens, rfl⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' htr' hst hens hstrip
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  obtain ⟨fvs, hop⟩ := openPisAtFvars_of_stripPis_sort nP 0 hstrip
  -- the bits: the opened body is `Sort resSort`, of sort `succ resSort`
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ nP hop hst hens
  obtain rfl := inferTypeCore_sort_inv hib
  obtain rfl := ensureSortCore_sort_eq hensb
  -- per assignment: the reading, its peel, its grading
  have hper : ∀ ψ : Name → Nat, ∃ pps : List (Nat × Nat × AnnotTerm),
      denoteMeta mp.base2.acval env ψ 0 type'
        = some (mkPisAV pps (.sort (resSort.eval ψ))) ∧
      pps.length = nP ∧
      (∀ d ∈ pps, d.2.1 ≠ 0) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps (.sort (resSort.eval ψ)))) ∧
      DomsBelow 0 pps := by
    intro ψ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReads_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOk.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, WellDenotedV V ρ Ta := fun ρ =>
      hokT ρ (Sat_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := opened_of hop htf' hbt' hTa hokT'
    have hR : R = .sort (resSort.eval ψ) := by
      have := hop'.body
      rw [denoteMeta_sort] at this
      exact (Option.some.inj this).symm
    subst hR
    obtain ⟨pps, hst', -⟩ := stripPisAV_of_piTeleAV htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    refine ⟨pps, hTa, hlen, ?_, hokT', ?_⟩
    · intro d hd
      have := stripPisAV_bits nP (hbits ψ) hTa hst' d hd
      simp only [Level.eval, Nat.succ_ne_zero, iff_false] at this
      exact this
    · exact (stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)).1
  refine ⟨fun ψ => Classical.choose (hper ψ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ψ => (Classical.choose_spec (hper ψ)).1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.2
  · intro ψ₁ ψ₂ hφ
    have h2 := (Classical.choose_spec (hper ψ₂)).1
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (.sort (resSort.eval ψ₁))) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 type' htp']
      exact (Classical.choose_spec (hper ψ₁)).1
    obtain ⟨hp, hb⟩ := mkPisAV_inj
      (by rw [(Classical.choose_spec (hper ψ₁)).2.1,
        (Classical.choose_spec (hper ψ₂)).2.1])
      (Option.some.inj (h1.symm.trans h2))
    exact ⟨hp, AnnotTerm.sort.inj hb⟩

/-- The former's data crosses a cons whose slot does not mention the
stored type (any block cons after the former's). -/
theorem FormerData.cross {m : EnvModel V env} {cvT : ConstantVal}
    {nP : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : FormerData m cvT nP resSort pps)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvT.type)
    (hcb : ConstsBound env cvT.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FormerData m₂ cvT nP resSort pps where
  read ψ := by
    rw [hac]
    exact denoteMeta_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

end ConLeche.Model
