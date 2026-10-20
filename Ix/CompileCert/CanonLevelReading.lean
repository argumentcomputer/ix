import Ix.CompileCert.ExpressionIngress
import Ix.LeanIngress.CanonLevel

/-! # Levels read syntactically (N-READS, N2)

The reading chain related a compiled level to its Source level by value only
(`ExpressionState.related_ingress_value`): Source mode lowered levels as Lean
wrote them. IxC's U lowers them to the compiler's canonical form
(`Ix.LeanIngress.canonLevelIn`: `canonUniv` over the constant's own level
parameters), and the compiler reads the canonical form of its exact lowering
(`UniversePipeline.LevelMeaning.exact`). So, with the reader's parameter map
the constant's level parameters (`param i = σ params[i]`) and `σ` keeping them
apart, the two are equal:

* `idxIn_map`, `univOfLevel_ingress`: Source's numbering lowers a level as the
  compiler does;
* `levelOfUniv_eq_convUniv`: the two readings of a universe agree;
* `canonLevelIn_ingress`, `levelMeaning_canon`: the reader's level is the
  Source level in canonical form;
* `related_ingress_canon`: the Source term and the reader's term agree
  syntactically at every level. -/

namespace Ix.CompileCert.CanonLevelReading

open Ix.LeanIngress (ingressLevel canonLevelIn univOfLevel levelOfUniv idxIn ofIdxIn)
open Ix.Compile.ExactKey (nameIndex)
open Ix.CompileCert.UniverseMeaning (lower)
open Ix.CompileCert.CanonUnivScope (Occurs)
open Ix.Kernel (Mode)
open Ix.Kernel.Reader (CName CExpr)

/-- On parameters `σ` keeps apart, the position of `σ name` in `params.map σ`
is `name`'s index in `params`. -/
theorem idxIn_map {params : List Ix.Name} {σ : Ix.Name → Kernel.LevelParam}
    (inj : ∀ a ∈ params, ∀ b ∈ params, σ a = σ b → a = b) {name : Ix.Name} {i : Nat}
    (found : nameIndex name params = some i) : idxIn (params.map σ) (σ name) = i := by
  unfold nameIndex at found
  obtain ⟨hi, hname, hfirst⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  have heq : params[i] = name := (Ix.Compile.ExactKey.nameEq_iff _ _).1 hname
  have hidx : (params.map σ).idxOf? (σ name) = some i := by
    rw [List.idxOf?_eq_some_iff]
    refine ⟨by simpa using hi, by simp [heq], fun j hj e => ?_⟩
    simp only [List.getElem_map] at e
    have same := inj _ (List.getElem_mem (by omega)) _ (List.getElem_mem hi) (e.trans (by rw [heq]))
    exact absurd ((Ix.Compile.ExactKey.nameEq_iff _ _).2 (same.trans heq)) (by simpa using hfirst j hj)
  unfold idxIn
  rw [hidx]

/-- **Source's numbering lowers a level as the compiler does**: its level,
numbered by positions in `params.map σ`, is the compiler's exact lowering. -/
theorem univOfLevel_ingress {params : List Ix.Name} {σ : Ix.Name → Kernel.LevelParam}
    (inj : ∀ a ∈ params, ∀ b ∈ params, σ a = σ b → a = b) :
    ∀ {source : Ix.Level} {raw : Ixon.Univ} {target : Kernel.Level},
      lower params source = some raw → ingressLevel σ source = .ok target →
        univOfLevel (idxIn (params.map σ)) target = raw := by
  intro source
  induction source with
  | zero h =>
    intro raw target hl hi
    simp only [lower, Option.some.injEq, ingressLevel, pure, Except.pure, Except.ok.injEq] at hl hi
    subst hl hi
    rfl
  | succ l h ih =>
    intro raw target hl hi
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨r, hr, rfl⟩ := hl
    simp only [ingressLevel, bind, Except.bind] at hi
    split at hi <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hi
    subst hi
    simp only [univOfLevel, ih hr (by assumption)]
  | max l r h ihl ihr =>
    intro raw target hl hi
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨a, ha, b, hb, rfl⟩ := hl
    simp only [ingressLevel, bind, Except.bind] at hi
    split at hi <;> try simp only [reduceCtorEq] at hi
    split at hi <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hi
    subst hi
    simp only [univOfLevel, ihl ha (by assumption), ihr hb (by assumption)]
  | imax l r h ihl ihr =>
    intro raw target hl hi
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨a, ha, b, hb, rfl⟩ := hl
    simp only [ingressLevel, bind, Except.bind] at hi
    split at hi <;> try simp only [reduceCtorEq] at hi
    split at hi <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hi
    subst hi
    simp only [univOfLevel, ihl ha (by assumption), ihr hb (by assumption)]
  | param name h =>
    intro raw target hl hi
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
    obtain ⟨index, found, hl'⟩ := hl
    split at hl' <;> simp only [Option.some.injEq, reduceCtorEq] at hl'
    subst hl'
    simp only [ingressLevel, pure, Except.pure, Except.ok.injEq] at hi
    subst hi
    simp only [univOfLevel, idxIn_map inj found]
  | mvar name h => intro raw target hl hi; simp [lower] at hl

/-- The two readings of a universe agree when the reader's parameter map is
the positions of `lps` on every variable that occurs. -/
theorem levelOfUniv_eq_convUniv {lps : List Kernel.LevelParam} {param : Nat → Kernel.LevelParam}
    (aligned : ∀ i (h : i < lps.length), param i = lps[i]) :
    ∀ u : Ixon.Univ, (∀ p, Occurs p u → p.toNat < lps.length) →
      levelOfUniv (ofIdxIn lps) u = Kernel.Reader.convUniv param u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih => intro h; simp only [levelOfUniv, Kernel.Reader.convUniv, ih h]
  | max a b iha ihb =>
    intro h
    simp only [levelOfUniv, Kernel.Reader.convUniv, iha (fun p o => h p (.inl o)),
      ihb (fun p o => h p (.inr o))]
  | imax a b iha ihb =>
    intro h
    simp only [levelOfUniv, Kernel.Reader.convUniv, iha (fun p o => h p (.inl o)),
      ihb (fun p o => h p (.inr o))]
  | var i =>
    intro h
    have lt := h i rfl
    simp only [levelOfUniv, Kernel.Reader.convUniv, ofIdxIn, lt, ↓reduceDIte, aligned]

/-- **A level reads as Source's canonical level**: the reader's level of the
canonical form of the compiler's exact lowering is the Source level in the
compiler's canonical form (`canonLevelIn`, what IxC's U lowers Source levels
to), when the reader's parameter map is the constant's level parameters
(`param i = σ params[i]`) and `σ` keeps them apart. -/
theorem canonLevelIn_ingress {params : List Ix.Name} {σ : Ix.Name → Kernel.LevelParam}
    {param : Nat → Kernel.LevelParam} (inj : ∀ a ∈ params, ∀ b ∈ params, σ a = σ b → a = b)
    (aligned : ∀ i (h : i < params.length), param i = σ params[i]) {source : Ix.Level}
    {raw : Ixon.Univ} {target : Kernel.Level} (lowered : lower params source = some raw)
    (ingress : ingressLevel σ source = .ok target) :
    canonLevelIn (params.map σ) target = Kernel.Reader.convUniv param (Ixon.canonUniv raw) := by
  unfold canonLevelIn
  rw [univOfLevel_ingress inj lowered ingress]
  apply levelOfUniv_eq_convUniv
  · intro i h
    simp only [List.length_map] at h
    simp [aligned i h]
  · intro p occurs
    simpa using UniverseMeaning.lower_occurs lowered p (CanonUnivScope.canonUniv_occurs raw p occurs)

/-- **A level's meaning, syntactically**: with the reader's parameter map the
constant's level parameters, the reader's level is the Source level in the
compiler's canonical form. -/
theorem levelMeaning_canon {params : List Ix.Name} {σ : Ix.Name → Kernel.LevelParam}
    {param : Nat → Kernel.LevelParam} (inj : ∀ a ∈ params, ∀ b ∈ params, σ a = σ b → a = b)
    (aligned : ∀ i (h : i < params.length), param i = σ params[i]) {source : Ix.Level}
    {level : Kernel.Level} (meaning : UniversePipeline.LevelMeaning params σ param source level) :
    ∃ target, ingressLevel σ source = .ok target ∧ canonLevelIn (params.map σ) target = level := by
  obtain ⟨target, ingress, -⟩ := meaning.value
  obtain ⟨raw, lowered, rfl⟩ := meaning.exact
  exact ⟨target, ingress, canonLevelIn_ingress inj aligned lowered ingress⟩

/-- **The Source term and the reader's term agree syntactically at levels**
(N2; `ExpressionState.related_ingress_value` agrees by value): at every level,
the reader's level is the Source level in the compiler's canonical form, when
the reader's parameter map is the constant's level parameters and `σ` keeps
them apart. -/
theorem related_ingress_canon {md : Mode} {names : Ix.Name → CName md → Prop}
    {params : List Ix.Name} {σ : Ix.Name → Kernel.LevelParam} {param : Nat → Kernel.LevelParam}
    (inj : ∀ a ∈ params, ∀ b ∈ params, σ a = σ b → a = b)
    (aligned : ∀ i (h : i < params.length), param i = σ params[i])
    {source : Ix.Expr} {target : CExpr md}
    (related : ExpressionState.Related names (UniversePipeline.LevelMeaning params σ param) source target) :
    ∃ converted, Ix.LeanIngress.ingressExpr σ source = .ok converted ∧
      ExpressionState.Matches (fun key key' => ∃ name, key = Ix.LeanIngress.ingressKey name ∧ names name key')
        (fun level level' => canonLevelIn (params.map σ) level = level') converted target :=
  ExpressionState.related_ingress σ (fun _ _ meaning => levelMeaning_canon inj aligned meaning) related

end Ix.CompileCert.CanonLevelReading
