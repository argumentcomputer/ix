import Ix.CompileCert.Opt.LevelSemantics
import Ix.Compile.Canon.OccurrenceKey

/-!
# Structural universe normalization and substitution

The structural specifications below refine the actual smart helpers and level
substitution, including arbitrary cached fields and optional parameter values.
Each preservation theorem starts from a successful original evaluation and
proves the same value after transformation, using the existing Translate
semantics. No theorem turns an evaluator refusal into a successful premise.
Collision and differing-cache neighbours exercise the same actual runtime
functions used by the refinement theorems.

Source-export guards derive the internal parameter-scope facts used by the
composition and argument-provenance lemmas. Actual ingestion correspondence,
referenced-spine arity, term conversion and capture-avoiding helper obligations
remain separate. These intermediate lemmas neither add a final compiler-domain
premise nor introduce a universe equivalence rule into Conv.
-/

namespace Ix.CompileCert.Opt.LevelRefinement

open Ix (Name Level)
open Ix.Compile.Canon (KeyLevel keyName keyLevelShape levelPeelSucc levelExplicitOffset)

/-- Optional parameter values retain refusal; they are not replaced by zero. -/
def evalP (φ : Lean.Name → Option Nat) : Level → Option Nat
  | .zero _ => some 0
  | .succ u _ => return (← evalP φ u) + 1
  | .max u v _ => return max (← evalP φ u) (← evalP φ v)
  | .imax u v _ => do
    let a ← evalP φ u
    let b ← evalP φ v
    return if b = 0 then 0 else max a b
  | .param n _ => φ (keyName n)
  | .mvar .. => none

def keyEvalP (φ : Lean.Name → Option Nat) : KeyLevel → Option Nat
  | .zero => some 0
  | .succ u => return (← keyEvalP φ u) + 1
  | .max u v => return max (← keyEvalP φ u) (← keyEvalP φ v)
  | .imax u v => do
    let a ← keyEvalP φ u
    let b ← keyEvalP φ v
    return if b = 0 then 0 else max a b
  | .param n => φ n
  | .mvar .. => none

theorem keyName_eq_ixName (n : Name) : keyName n = ixName n := by
  induction n <;> simp_all [keyName, Ix.SemanticContract.toLeanName, ixName]

theorem evalP_total (φ : Lean.Name → Nat) (l : Level) :
    evalP (some ∘ φ) l = ixLevelEval φ l := by
  induction l <;> simp_all [evalP, ixLevelEval, keyName_eq_ixName]

theorem keyEvalP_shape (φ : Lean.Name → Option Nat) (l : Level) :
    keyEvalP φ (keyLevelShape l) = evalP φ l := by
  induction l <;> simp_all [keyLevelShape, keyEvalP, evalP]

def eqShape (x y : Level) : Bool := decide (keyLevelShape x = keyLevelShape y)

theorem eqShape_eval (φ : Lean.Name → Option Nat) {x y : Level}
    (h : eqShape x y = true) : evalP φ x = evalP φ y := by
  have same : keyLevelShape x = keyLevelShape y := by simpa [eqShape] using h
  rw [← keyEvalP_shape φ x, ← keyEvalP_shape φ y, same]

theorem evalP_succ_inv {φ : Lean.Name → Option Nat} {u : Level} {hash : Address}
    {n : Nat} (h : evalP φ (.succ u hash) = some n) :
    ∃ a, evalP φ u = some a ∧ a + 1 = n := by
  cases hu : evalP φ u <;> simp_all [evalP]

theorem evalP_max_inv {φ : Lean.Name → Option Nat} {u v : Level} {hash : Address}
    {n : Nat} (h : evalP φ (.max u v hash) = some n) :
    ∃ a b, evalP φ u = some a ∧ evalP φ v = some b ∧ max a b = n := by
  cases hu : evalP φ u <;> cases hv : evalP φ v <;> simp_all [evalP]

theorem evalP_imax_inv {φ : Lean.Name → Option Nat} {u v : Level} {hash : Address}
    {n : Nat} (h : evalP φ (.imax u v hash) = some n) :
    ∃ a b, evalP φ u = some a ∧ evalP φ v = some b ∧
      (if b = 0 then 0 else max a b) = n := by
  cases hu : evalP φ u <;> cases hv : evalP φ v <;> simp_all [evalP]

theorem peel_eval {φ : Lean.Name → Option Nat} (l : Level) {n : Nat}
    (h : evalP φ l = some n) :
    ∃ a, evalP φ (levelPeelSucc l).1 = some a ∧ a + (levelPeelSucc l).2 = n := by
  induction l generalizing n with
  | succ u hash ih =>
    obtain ⟨b, hb, hn⟩ := evalP_succ_inv h
    obtain ⟨a, ha, hab⟩ := ih hb
    exact ⟨a, by simpa [levelPeelSucc] using ha,
      by simp only [levelPeelSucc]; omega⟩
  | _ => exact ⟨n, h, by simp [levelPeelSucc]⟩

theorem explicit_eval {φ : Lean.Name → Option Nat} {l : Level} {n a : Nat}
    (h : evalP φ l = some a) (explicit : levelExplicitOffset l = some n) : a = n := by
  obtain ⟨b, hb, hba⟩ := peel_eval l h
  unfold levelExplicitOffset at explicit
  cases hp : levelPeelSucc l with
  | mk base off =>
    rw [hp] at explicit hb hba
    cases base <;> simp_all [evalP]
    omega

def absorbs (outer inner : Level) : Bool :=
  match outer with
  | .max a b _ => eqShape a inner || eqShape b inner
  | _ => false

theorem absorbs_le {φ : Lean.Name → Option Nat} {outer inner : Level} {a b : Nat}
    (ho : evalP φ outer = some a) (hi : evalP φ inner = some b)
    (hit : absorbs outer inner = true) : b ≤ a := by
  cases outer <;> try simp [absorbs] at hit
  rename_i x y hash
  obtain ⟨u, v, hx, hy, huv⟩ := evalP_max_inv ho
  rcases hit with h | h
  · have e := eqShape_eval φ h
    rw [hx, hi] at e
    have : u = b := Option.some.inj e
    subst b
    omega
  · have e := eqShape_eval φ h
    rw [hy, hi] at e
    have : v = b := Option.some.inj e
    subst b
    omega

/-- The same nonnumeric branches as Canon.levelMaxSmart, with structural tests. -/
def maxTail (x y : Level) : Level :=
  if eqShape x y then x
  else match x, y with
    | .zero _, _ => y
    | _, .zero _ => x
    | _, _ =>
      if absorbs y x then y
      else if absorbs x y then x
      else
        let (bx, ox) := levelPeelSucc x
        let (by_, oy) := levelPeelSucc y
        if eqShape bx by_ then (if ox ≥ oy then x else y)
        else Level.mkMax x y

def maxSmart (x y : Level) : Level :=
  match levelExplicitOffset x, levelExplicitOffset y with
  | some ox, some oy => if ox ≥ oy then x else y
  | _, _ => maxTail x y

private theorem maxTail_postZero_eval {φ : Lean.Name → Option Nat} {x y : Level}
    {a b : Nat} (hx : evalP φ x = some a) (hy : evalP φ y = some b) :
    evalP φ (if absorbs y x then y else if absorbs x y then x else
      let (bx, ox) := levelPeelSucc x
      let (by_, oy) := levelPeelSucc y
      if eqShape bx by_ then (if ox ≥ oy then x else y) else Level.mkMax x y) =
      some (max a b) := by
  split
  · rename_i hit
    have hab := absorbs_le hy hx hit
    simpa [Nat.max_eq_right hab] using hy
  · split
    · rename_i hit
      have hba := absorbs_le hx hy hit
      simpa [Nat.max_eq_left hba] using hx
    · obtain ⟨u, hu, hua⟩ := peel_eval x hx
      obtain ⟨v, hv, hvb⟩ := peel_eval y hy
      rcases hpx : levelPeelSucc x with ⟨bx, ox⟩
      rcases hpy : levelPeelSucc y with ⟨by_, oy⟩
      simp only [hpx, hpy] at hu hua hv hvb ⊢
      split
      · rename_i same
        have he := eqShape_eval φ same
        rw [hu, hv] at he
        have huv : u = v := Option.some.inj he
        split
        · rename_i off
          have : b ≤ a := by omega
          simpa [Nat.max_eq_left this] using hx
        · rename_i off
          have : a ≤ b := by omega
          simpa [Nat.max_eq_right this] using hy
      · simp [Level.mkMax, Id.run, evalP, hx, hy]

theorem maxTail_eval {φ : Lean.Name → Option Nat} {x y : Level} {a b : Nat}
    (hx : evalP φ x = some a) (hy : evalP φ y = some b) :
    evalP φ (maxTail x y) = some (max a b) := by
  unfold maxTail
  split
  · rename_i same
    have e := eqShape_eval φ same
    rw [hx, hy] at e
    have hab : a = b := Option.some.inj e
    simpa [hab] using hx
  · split
    · have ha : a = 0 := (Option.some.inj hx).symm
      simpa [ha] using hy
    · have hb : b = 0 := (Option.some.inj hy).symm
      simpa [hb] using hx
    · exact maxTail_postZero_eval hx hy

theorem maxSmart_eval {φ : Lean.Name → Option Nat} {x y : Level} {a b : Nat}
    (hx : evalP φ x = some a) (hy : evalP φ y = some b) :
    evalP φ (maxSmart x y) = some (max a b) := by
  unfold maxSmart
  split
  · rename_i ox oy ex ey
    have ha := explicit_eval hx ex
    have hb := explicit_eval hy ey
    split
    · rename_i h
      have : b ≤ a := by omega
      simpa [Nat.max_eq_left this] using hx
    · rename_i h
      have : a ≤ b := by omega
      simpa [Nat.max_eq_right this] using hy
  · exact maxTail_eval hx hy

def imaxTail (x y : Level) : Level :=
  match x with
  | .zero _ => y
  | .succ (.zero _) _ => y
  | _ => if eqShape x y then x else Level.mkIMax x y

def imaxSmart (x y : Level) : Level :=
  match y with
  | .succ .. => maxSmart x y
  | .zero _ => y
  | _ => imaxTail x y

theorem imaxTail_eval {φ : Lean.Name → Option Nat} {x y : Level} {a b : Nat}
    (hx : evalP φ x = some a) (hy : evalP φ y = some b) :
    evalP φ (imaxTail x y) = some (if b = 0 then 0 else max a b) := by
  unfold imaxTail
  split
  · have ha : a = 0 := (Option.some.inj hx).symm
    by_cases hb : b = 0 <;> simpa [ha, hb] using hy
  · have ha : a = 1 := by simpa [evalP] using hx.symm
    by_cases hb : b = 0
    · simpa [ha, hb] using hy
    · have hle : 1 ≤ b := by omega
      simpa [ha, hb, Nat.max_eq_right hle] using hy
  · split
    · rename_i same
      have e := eqShape_eval φ same
      rw [hx, hy] at e
      have hab : a = b := Option.some.inj e
      by_cases hb : b = 0 <;> simpa [hab, hb] using hx
    · simp [Level.mkIMax, Id.run, evalP, hx, hy]

theorem imaxSmart_eval {φ : Lean.Name → Option Nat} {x y : Level} {a b : Nat}
    (hx : evalP φ x = some a) (hy : evalP φ y = some b) :
    evalP φ (imaxSmart x y) = some (if b = 0 then 0 else max a b) := by
  unfold imaxSmart
  split
  · obtain ⟨n, _, hn⟩ := evalP_succ_inv hy
    have hb : b ≠ 0 := by omega
    simpa only [hb, ↓reduceIte] using maxSmart_eval hx hy
  · have hb : b = 0 := (Option.some.inj hy).symm
    simpa [hb] using hy
  · exact imaxTail_eval hx hy

def normalize : Level → Level
  | .succ u _ => Level.mkSucc (normalize u)
  | .max u v _ => maxSmart (normalize u) (normalize v)
  | .imax u v _ => imaxSmart (normalize u) (normalize v)
  | l => l

/-- Arbitrary parameters and arbitrary cache fields; successful evaluation is preserved. -/
theorem normalize_evalP (φ : Lean.Name → Option Nat) (l : Level) {n : Nat}
    (h : evalP φ l = some n) : evalP φ (normalize l) = some n := by
  induction l generalizing n with
  | succ u hash ih =>
    obtain ⟨a, ha, hn⟩ := evalP_succ_inv h
    simp [normalize, Level.mkSucc, Id.run, evalP, ih ha, hn]
  | max x y hash ihx ihy =>
    obtain ⟨a, b, ha, hb, hab⟩ := evalP_max_inv h
    simpa [normalize, hab] using maxSmart_eval (ihx ha) (ihy hb)
  | imax x y hash ihx ihy =>
    obtain ⟨a, b, ha, hb, hab⟩ := evalP_imax_inv h
    simpa [normalize, hab] using imaxSmart_eval (ihx ha) (ihy hb)
  | _ => exact h

theorem normalize_ixLevelEval (φ : Lean.Name → Nat) (l : Level) {n : Nat}
    (h : ixLevelEval φ l = some n) : ixLevelEval φ (normalize l) = some n := by
  rw [← evalP_total] at h ⊢
  exact normalize_evalP _ _ h

/-- First structural parameter match, retaining short-array fallback exactly. -/
def lookupArg (ps : Array Name) (us : Array Level) (n : Lean.Name) : Option Level :=
  ((ps.map keyName).idxOf? n).bind fun i => us[i]?

def subst (ps : Array Name) (us : Array Level) : Level → Level
  | .succ u _ => Level.mkSucc (subst ps us u)
  | .max u v _ => maxSmart (subst ps us u) (subst ps us v)
  | .imax u v _ => imaxSmart (subst ps us u) (subst ps us v)
  | l@(.param n _) => (lookupArg ps us (keyName n)).getD l
  | l => l

/-- The exact semantic update induced by lookup, including missing arguments. -/
def substVal (φ : Lean.Name → Option Nat) (ps : Array Name) (us : Array Level)
    (n : Lean.Name) : Option Nat :=
  match lookupArg ps us n with
  | some u => evalP φ u
  | none => φ n

/-- The scalar substitution soundness statement has no name/hash or closedness premise.
Only successful evaluation under its exact induced valuation is transported. -/
theorem subst_evalP (φ : Lean.Name → Option Nat) (ps : Array Name) (us : Array Level)
    (l : Level) {n : Nat} (h : evalP (substVal φ ps us) l = some n) :
    evalP φ (subst ps us l) = some n := by
  induction l generalizing n with
  | param name hash =>
    simp only [evalP, substVal] at h
    simp only [subst]
    cases hl : lookupArg ps us (keyName name) <;> simp_all [evalP]
  | succ u hash ih =>
    obtain ⟨a, ha, hn⟩ := evalP_succ_inv h
    simp [subst, Level.mkSucc, Id.run, evalP, ih ha, hn]
  | max x y hash ihx ihy =>
    obtain ⟨a, b, ha, hb, hab⟩ := evalP_max_inv h
    simpa [subst, hab] using maxSmart_eval (ihx ha) (ihy hb)
  | imax x y hash ihx ihy =>
    obtain ⟨a, b, ha, hb, hab⟩ := evalP_imax_inv h
    simpa [subst, hab] using imaxSmart_eval (ihx ha) (ihy hb)
  | _ => exact h

theorem lookupArg_map (ps : Array Name) (us : Array Level) (n : Lean.Name)
    (f : Level → Level) : lookupArg ps (us.map f) n = (lookupArg ps us n).map f := by
  unfold lookupArg
  cases (ps.map keyName).idxOf? n <;> simp [Array.getElem?_map]

/-- Explicit syntax membership, used to expose rather than assume source scope. -/
def ParamOccurs (n : Lean.Name) : Level → Prop
  | .param k _ => keyName k = n
  | .succ u _ => ParamOccurs n u
  | .max u v _ | .imax u v _ => ParamOccurs n u ∨ ParamOccurs n v
  | _ => False

/-- Evaluation respects successful parameter values at the actual occurrences. -/
theorem evalP_refines (φ ψ : Lean.Name → Option Nat) (l : Level)
    (aligned : ∀ k, ParamOccurs k l → ∀ a, φ k = some a → ψ k = some a)
    {n : Nat} (h : evalP φ l = some n) : evalP ψ l = some n := by
  induction l generalizing n with
  | param name hash => exact aligned (keyName name) rfl n h
  | succ u hash ih =>
    obtain ⟨a, ha, hn⟩ := evalP_succ_inv h
    have hv := ih (fun k hk a hka => aligned k hk a hka) ha
    simp [evalP, hv, hn]
  | max x y hash ihx ihy =>
    obtain ⟨a, b, ha, hb, hab⟩ := evalP_max_inv h
    have hxa := ihx (fun k hk a hka => aligned k (Or.inl hk) a hka) ha
    have hyb := ihy (fun k hk a hka => aligned k (Or.inr hk) a hka) hb
    simp [evalP, hxa, hyb, hab]
  | imax x y hash ihx ihy =>
    obtain ⟨a, b, ha, hb, hab⟩ := evalP_imax_inv h
    have hxa := ihx (fun k hk a hka => aligned k (Or.inl hk) a hka) ha
    have hyb := ihy (fun k hk a hka => aligned k (Or.inr hk) a hka) hb
    simp [evalP, hxa, hyb, hab]
  | zero => exact h
  | mvar => cases h

/-- Exact composed-instantiation refinement at every covered source parameter.
Coverage is an internal source/spine obligation, not a new final compiler premise. -/
theorem subst_compose_evalP (φ : Lean.Name → Option Nat)
    (outerPs : Array Name) (outerUs : Array Level)
    (innerPs : Array Name) (innerUs : Array Level) (l : Level)
    (covered : ∀ k, ParamOccurs k l → ∃ u, lookupArg innerPs innerUs k = some u)
    {n : Nat}
    (h : evalP (substVal (substVal φ outerPs outerUs) innerPs innerUs) l = some n) :
    evalP φ (subst outerPs outerUs (subst innerPs innerUs l)) = some n ∧
    evalP φ (subst innerPs (innerUs.map (subst outerPs outerUs)) l) = some n := by
  constructor
  · exact subst_evalP φ outerPs outerUs _
      (subst_evalP (substVal φ outerPs outerUs) innerPs innerUs l h)
  · apply subst_evalP
    apply evalP_refines _ _ l _ h
    intro k occurs a hk
    obtain ⟨u, hu⟩ := covered k occurs
    simp only [substVal, hu] at hk
    simp only [substVal, lookupArg_map, hu, Option.map_some]
    exact subst_evalP φ outerPs outerUs u hk

theorem lookupArg_some_of_mem (ps : Array Name) (us : Array Level) (n : Lean.Name)
    (member : n ∈ ps.map keyName) (arity : ps.size ≤ us.size) :
    ∃ u, lookupArg ps us n = some u := by
  cases hi : (ps.map keyName).finIdxOf? n with
  | none =>
    have absent : (ps.map keyName).idxOf? n = none := by
      simp only [Array.idxOf?_eq_map_finIdxOf?_val, hi, Option.map_none]
    exact False.elim ((Array.idxOf?_eq_none_iff.mp absent) member)
  | some i =>
    have bound : i.val < us.size := by
      have hi' := i.isLt
      simp only [Array.size_map] at hi'
      omega
    refine ⟨us[i.val], ?_⟩
    simp [lookupArg, Array.idxOf?_eq_map_finIdxOf?_val, hi, bound]

/-- The needed coverage follows from the referenced declaration's scope and its
actual occurrence spine. The outer caller's arrays remain completely arbitrary. -/
theorem subst_compose_of_scope_evalP (φ : Lean.Name → Option Nat)
    (outerPs : Array Name) (outerUs : Array Level)
    (innerPs : Array Name) (innerUs : Array Level) (l : Level)
    (scope : ∀ k, ParamOccurs k l → k ∈ innerPs.map keyName)
    (arity : innerPs.size ≤ innerUs.size)
    {n : Nat}
    (h : evalP (substVal (substVal φ outerPs outerUs) innerPs innerUs) l = some n) :
    evalP φ (subst outerPs outerUs (subst innerPs innerUs l)) = some n ∧
    evalP φ (subst innerPs (innerUs.map (subst outerPs outerUs)) l) = some n :=
  subst_compose_evalP φ outerPs outerUs innerPs innerUs l
    (fun k hk => lookupArg_some_of_mem innerPs innerUs k (scope k hk) arity) h

/-! Exact runtime refinement. These equalities use the actual imported
structural keys and actual patched helpers, with arbitrary cached fields. -/

theorem maxSmart_eq_runtime (x y : Level) :
    maxSmart x y = Ix.Compile.Canon.levelMaxSmart x y := by rfl

theorem imaxSmart_eq_runtime (x y : Level) :
    imaxSmart x y = Ix.Compile.Canon.levelImaxSmart x y := by rfl

theorem normalize_eq_runtime : normalize = Ix.Compile.Canon.normalizeLevel := by
  funext l
  induction l with
  | succ u hash ih => simp only [normalize, Ix.Compile.Canon.normalizeLevel, ih]
  | max u v hash ihu ihv =>
    simp only [normalize, Ix.Compile.Canon.normalizeLevel, ihu, ihv, maxSmart_eq_runtime]
  | imax u v hash ihu ihv =>
    simp only [normalize, Ix.Compile.Canon.normalizeLevel, ihu, ihv, imaxSmart_eq_runtime]
  | _ => rfl

theorem subst_eq_runtime (ps : Array Name) (us : Array Level) :
    subst ps us = Ix.Compile.Canon.substLevel ps us := by
  funext l
  induction l with
  | succ u hash ih => simp only [subst, Ix.Compile.Canon.substLevel, ih]
  | max u v hash ihu ihv =>
    simp only [subst, Ix.Compile.Canon.substLevel, ihu, ihv, maxSmart_eq_runtime]
  | imax u v hash ihu ihv =>
    simp only [subst, Ix.Compile.Canon.substLevel, ihu, ihv, imaxSmart_eq_runtime]
  | param name hash =>
    cases hit : (ps.map keyName).idxOf? (keyName name) with
    | none =>
      simp only [subst, lookupArg, Ix.Compile.Canon.substLevel, hit, Option.bind]
      rfl
    | some i =>
      simp only [subst, lookupArg, Ix.Compile.Canon.substLevel, hit, Option.bind]
  | _ => rfl

/-- Polymorphic normalization of the actual runtime, without a hash premise. -/
theorem normalizeLevel_evalP (φ : Lean.Name → Option Nat) (l : Level) {n : Nat}
    (evaluated : evalP φ l = some n) :
    evalP φ (Ix.Compile.Canon.normalizeLevel l) = some n := by
  simpa only [normalize_eq_runtime] using normalize_evalP φ l evaluated

theorem normalizeLevel_ixLevelEval (φ : Lean.Name → Nat) (l : Level) {n : Nat}
    (evaluated : ixLevelEval φ l = some n) :
    ixLevelEval φ (Ix.Compile.Canon.normalizeLevel l) = some n := by
  simpa only [normalize_eq_runtime] using normalize_ixLevelEval φ l evaluated

/-- The induced valuation retains every actual lookup/fallback decision. -/
theorem substLevel_evalP (φ : Lean.Name → Option Nat) (ps : Array Name)
    (us : Array Level) (l : Level) {n : Nat}
    (evaluated : evalP (substVal φ ps us) l = some n) :
    evalP φ (Ix.Compile.Canon.substLevel ps us l) = some n := by
  simpa only [subst_eq_runtime] using subst_evalP φ ps us l evaluated

theorem substLevel_compose_of_scope_evalP (φ : Lean.Name → Option Nat)
    (outerPs : Array Name) (outerUs : Array Level)
    (innerPs : Array Name) (innerUs : Array Level) (l : Level)
    (scope : ∀ k, ParamOccurs k l → k ∈ innerPs.map keyName)
    (arity : innerPs.size ≤ innerUs.size) {n : Nat}
    (evaluated : evalP (substVal (substVal φ outerPs outerUs) innerPs innerUs) l = some n) :
    evalP φ (Ix.Compile.Canon.substLevel outerPs outerUs
      (Ix.Compile.Canon.substLevel innerPs innerUs l)) = some n ∧
    evalP φ (Ix.Compile.Canon.substLevel innerPs
      (innerUs.map (Ix.Compile.Canon.substLevel outerPs outerUs)) l) = some n := by
  simpa only [subst_eq_runtime] using
    subst_compose_of_scope_evalP φ outerPs outerUs innerPs innerUs l scope arity evaluated

/-! Finite raw-cache controls. These are not produced hash collisions, source
declarations, or evidence of a default compiler defect. -/
private def h0 : Address := ⟨⟨#[]⟩⟩
private def h1 : Address := ⟨⟨#[1]⟩⟩
private def uName : Name := .str (.anonymous h0) "u" h0
private def vCollisionName : Name := .str (.anonymous h0) "v" h0
private def vNeighbourName : Name := .str (.anonymous h0) "v" h1
private def uOtherCache : Name := .str (.anonymous h1) "u" h1
private def z : Level := .zero h0
private def one : Level := .succ z h0
private def u : Level := .param uName h0
private def vc : Level := .param vCollisionName h0
private def vn : Level := .param vNeighbourName h1
private def φ (n : Lean.Name) : Nat := if n = `u then 0 else 1

theorem candidate_max_collision_control :
    ixLevelEval φ (normalize (.max u vc h0)) = some 1 ∧
    ixLevelEval φ (normalize (.max u vn h0)) = some 1 := by
  constructor <;> apply normalize_ixLevelEval <;> decide

theorem candidate_parameter_collision_control :
    ixLevelEval φ (subst #[uName] #[z] vc) = some 1 ∧
    ixLevelEval φ (subst #[uName] #[z] vn) = some 1 := by
  simp [subst, lookupArg, vc, vn, uName, vCollisionName, vNeighbourName,
    keyName, Ix.SemanticContract.toLeanName, List.idxOf?_cons, ixLevelEval,
    ixName, φ]

/-- The two raw-cache inputs now choose the same structurally correct branch.
Both conclusions concern the actual structurally confirmed lookup. -/
theorem runtime_parameter_collision_repaired :
    ixLevelEval φ (Ix.Compile.Canon.substLevel #[uName] #[z] vc) = some 1 ∧
    ixLevelEval φ (Ix.Compile.Canon.substLevel #[uName] #[z] vn) = some 1 := by
  simpa only [subst_eq_runtime] using candidate_parameter_collision_control

theorem runtime_max_collision_repaired :
    ixLevelEval φ (Ix.Compile.Canon.normalizeLevel (.max u vc h0)) = some 1 ∧
    ixLevelEval φ (Ix.Compile.Canon.normalizeLevel (.max u vn h0)) = some 1 := by
  simpa only [normalize_eq_runtime] using candidate_max_collision_control


theorem candidate_lookup_controls :
    lookupArg #[uName] #[one] (keyName uOtherCache) = some one ∧
    lookupArg #[uName, uOtherCache] #[z, one] (keyName uName) = some z ∧
    lookupArg #[uName, vNeighbourName] #[one] (keyName vNeighbourName) = none ∧
    lookupArg #[uName, uOtherCache] #[] (keyName uName) = none := by
  simp [lookupArg, uName, uOtherCache, vNeighbourName, keyName,
    Ix.SemanticContract.toLeanName, List.idxOf?_cons]



/-! Parameter provenance through the candidate's actual scalar branches.
These are internal induction facts, not extra final compiler assumptions. -/

theorem maxTail_choice (x y : Level) :
    maxTail x y = x ∨ maxTail x y = y ∨ maxTail x y = Level.mkMax x y := by
  unfold maxTail
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl rfl)
      · split
        · exact Or.inl rfl
        · rcases hx : levelPeelSucc x with ⟨bx, ox⟩
          rcases hy : levelPeelSucc y with ⟨by_, oy⟩
          dsimp only
          split
          · split
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)

theorem maxSmart_choice (x y : Level) :
    maxSmart x y = x ∨ maxSmart x y = y ∨ maxSmart x y = Level.mkMax x y := by
  unfold maxSmart
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact maxTail_choice x y

theorem maxSmart_params (k : Lean.Name) (x y : Level)
    (h : ParamOccurs k (maxSmart x y)) : ParamOccurs k x ∨ ParamOccurs k y := by
  rcases maxSmart_choice x y with hx | hy | hm
  · exact Or.inl (hx ▸ h)
  · exact Or.inr (hy ▸ h)
  · simpa only [hm, Level.mkMax, Id.run, ParamOccurs] using h

theorem imaxTail_params (k : Lean.Name) (x y : Level)
    (h : ParamOccurs k (imaxTail x y)) : ParamOccurs k x ∨ ParamOccurs k y := by
  unfold imaxTail at h
  split at h
  · exact Or.inr h
  · exact Or.inr h
  · split at h
    · exact Or.inl h
    · simpa only [Level.mkIMax, Id.run, ParamOccurs] using h

theorem imaxSmart_params (k : Lean.Name) (x y : Level)
    (h : ParamOccurs k (imaxSmart x y)) : ParamOccurs k x ∨ ParamOccurs k y := by
  unfold imaxSmart at h
  split at h
  · exact maxSmart_params k _ _ h
  · exact Or.inr h
  · exact imaxTail_params k _ _ h

theorem normalize_params (k : Lean.Name) (l : Level) :
    ParamOccurs k (normalize l) → ParamOccurs k l := by
  induction l with
  | succ u hash ih =>
    simpa only [normalize, Level.mkSucc, Id.run, ParamOccurs] using ih
  | max x y hash ihx ihy =>
    intro h
    exact (maxSmart_params k _ _ h).elim (Or.inl ∘ ihx) (Or.inr ∘ ihy)
  | imax x y hash ihx ihy =>
    intro h
    exact (imaxSmart_params k _ _ h).elim (Or.inl ∘ ihx) (Or.inr ∘ ihy)
  | _ => exact id

theorem lookupArg_mem {ps : Array Name} {us : Array Level} {k : Lean.Name} {u : Level}
    (h : lookupArg ps us k = some u) : u ∈ us := by
  unfold lookupArg at h
  cases hi : (ps.map keyName).idxOf? k with
  | none => simp only [hi, Option.bind_none] at h; cases h
  | some i =>
    simp only [hi, Option.bind_some] at h
    exact Array.mem_of_getElem? h

/-- Every output parameter either survives an unmatched source occurrence or
comes from one of this invocation's actual universe arguments. -/
theorem subst_params (ps : Array Name) (us : Array Level) (k : Lean.Name) (l : Level) :
    ParamOccurs k (subst ps us l) →
      (ParamOccurs k l ∧ lookupArg ps us k = none) ∨
        ∃ u ∈ us, ParamOccurs k u := by
  induction l with
  | param name hash =>
    simp only [subst]
    cases hl : lookupArg ps us (keyName name) with
    | none =>
      simp only [Option.getD_none]
      intro h
      exact Or.inl ⟨h, (show keyName name = k from h) ▸ hl⟩
    | some u =>
      simp only [Option.getD_some]
      intro h
      exact Or.inr ⟨u, lookupArg_mem hl, h⟩
  | succ u hash ih =>
    simpa only [subst, Level.mkSucc, Id.run, ParamOccurs] using ih
  | max x y hash ihx ihy =>
    intro h
    rcases maxSmart_params k _ _ h with hx | hy
    · rcases ihx hx with ⟨ho, hn⟩ | ha
      · exact Or.inl ⟨Or.inl ho, hn⟩
      · exact Or.inr ha
    · rcases ihy hy with ⟨ho, hn⟩ | ha
      · exact Or.inl ⟨Or.inr ho, hn⟩
      · exact Or.inr ha
  | imax x y hash ihx ihy =>
    intro h
    rcases imaxSmart_params k _ _ h with hx | hy
    · rcases ihx hx with ⟨ho, hn⟩ | ha
      · exact Or.inl ⟨Or.inl ho, hn⟩
      · exact Or.inr ha
    · rcases ihy hy with ⟨ho, hn⟩ | ha
      · exact Or.inl ⟨Or.inr ho, hn⟩
      · exact Or.inr ha
  | zero | mvar => intro h; cases h

/-- A scoped referenced declaration with a sufficient occurrence spine leaves
only parameters from that spine. The caller's later substitution is unrestricted. -/
theorem subst_params_from_arguments (ps : Array Name) (us : Array Level) (l : Level)
    (scope : ∀ k, ParamOccurs k l → k ∈ ps.map keyName)
    (arity : ps.size ≤ us.size) {k : Lean.Name}
    (h : ParamOccurs k (subst ps us l)) : ∃ u ∈ us, ParamOccurs k u := by
  rcases subst_params ps us k l h with ⟨occurs, absent⟩ | result
  · obtain ⟨u, found⟩ := lookupArg_some_of_mem ps us k (scope k occurs) arity
    rw [absent] at found
    cases found
  · exact result

def SourceParamOccurs (k : Lean.Name) : Lean.Level → Prop
  | .param name => name = k
  | .succ u => SourceParamOccurs k u
  | .max u v | .imax u v => SourceParamOccurs k u ∨ SourceParamOccurs k v
  | _ => False

/-- The existing independent structural level view preserves exact parameter
occurrence. This statement does not presume that CanonM's caches refine that view. -/
theorem ixLevel_params {l : Level} {view : Lean.Level}
    (h : ixLevel l = .ok view) (k : Lean.Name) :
    ParamOccurs k l ↔ SourceParamOccurs k view := by
  induction l generalizing view
  all_goals try simp only [ixLevel, bind, Except.bind, pure, Except.pure] at h
  all_goals repeat' split at h
  all_goals try simp only [Except.ok.injEq] at h
  all_goals try subst view
  all_goals simp_all [ParamOccurs, SourceParamOccurs, keyName_eq_ixName]



/-! Scope from the existing independent source exporter. These are reader/check
facts only: the general compiler endpoint must still derive the actual source
view and source-acceptance facts; successful image construction does not do so. -/

theorem exportUniv_scope {ps : List Lean.Name} {u : Lean.Level} {wire : Ixon.Univ}
    (exported : exportUniv ps u = .ok wire) {k : Lean.Name}
    (occurs : SourceParamOccurs k u) : k ∈ ps := by
  induction u generalizing wire with
  | zero | mvar => cases occurs
  | succ u ih =>
    simp only [exportUniv] at exported
    obtain ⟨inner, hi, _⟩ := except_bind_ok exported
    exact ih hi occurs
  | max u v ihu ihv =>
    simp only [exportUniv] at exported
    obtain ⟨left, hl, exported⟩ := except_bind_ok exported
    obtain ⟨right, hr, _⟩ := except_bind_ok exported
    exact occurs.elim (ihu hl) (ihv hr)
  | imax u v ihu ihv =>
    simp only [exportUniv] at exported
    obtain ⟨left, hl, exported⟩ := except_bind_ok exported
    obtain ⟨right, hr, _⟩ := except_bind_ok exported
    exact occurs.elim (ihu hl) (ihv hr)
  | param name =>
    have hk : name = k := occurs
    subst k
    cases hi : ps.idxOf? name with
    | none => simp [exportUniv, hi] at exported
    | some i =>
      have found : (ps.idxOf? name).isSome := by simp [hi]
      exact List.isSome_idxOf?.mp found

/-- The independent source-level exporter actually checks the original
declaration telescope before normalization. Its success implies this scope fact. -/
theorem exportSourceLevel_scope {ps : List Lean.Name} {u : Lean.Level}
    {out : Kernel.Level} (exported : exportSourceLevel ps u = .ok out)
    {k : Lean.Name} (occurs : SourceParamOccurs k u) : k ∈ ps := by
  unfold exportSourceLevel at exported
  obtain ⟨wire, hw, _⟩ := except_bind_ok exported
  exact exportUniv_scope hw occurs

/-- Transfer that actual source scope through the independent structural Ix
view. No cached name/level equality is used to transport membership. -/
theorem ixLevel_source_scope (ps : Array Name) {l : Level} {view : Lean.Level}
    {out : Kernel.Level} (viewed : ixLevel l = .ok view)
    (exported : exportSourceLevel (ps.map keyName).toList view = .ok out) :
    ∀ k, ParamOccurs k l → k ∈ ps.map keyName := by
  intro k occurs
  have hs := exportSourceLevel_scope exported ((ixLevel_params viewed k).mp occurs)
  simpa using hs

/-- The source-export guard and an actual structural view discharge the scalar
scope side of argument provenance. Obtaining both from the original source and
its ingestion remains separate from the successful image-construction predicate. -/
theorem subst_params_of_source_export (ps : Array Name) (us : Array Level)
    {l : Level} {view : Lean.Level} {out : Kernel.Level}
    (viewed : ixLevel l = .ok view)
    (exported : exportSourceLevel (ps.map keyName).toList view = .ok out)
    (arity : ps.size ≤ us.size) {k : Lean.Name}
    (occurs : ParamOccurs k (subst ps us l)) : ∃ u ∈ us, ParamOccurs k u :=
  subst_params_from_arguments ps us l (ixLevel_source_scope ps viewed exported) arity occurs


/-- An actual independent source view/export supplies the same internal
scope needed by the actual runtime composition theorem. The arity still must
come from the real referenced source declaration; this is not a final law. -/
theorem substLevel_compose_of_source_export_evalP (φ : Lean.Name → Option Nat)
    (outerPs : Array Name) (outerUs : Array Level)
    (innerPs : Array Name) (innerUs : Array Level) {l : Level}
    {view : Lean.Level} {out : Kernel.Level}
    (viewed : ixLevel l = .ok view)
    (exported : exportSourceLevel (innerPs.map keyName).toList view = .ok out)
    (arity : innerPs.size ≤ innerUs.size) {n : Nat}
    (evaluated : evalP (substVal (substVal φ outerPs outerUs) innerPs innerUs) l = some n) :
    evalP φ (Ix.Compile.Canon.substLevel outerPs outerUs
      (Ix.Compile.Canon.substLevel innerPs innerUs l)) = some n ∧
    evalP φ (Ix.Compile.Canon.substLevel innerPs
      (innerUs.map (Ix.Compile.Canon.substLevel outerPs outerUs)) l) = some n :=
  substLevel_compose_of_scope_evalP φ outerPs outerUs innerPs innerUs l
    (ixLevel_source_scope innerPs viewed exported) arity evaluated

theorem substLevel_params_of_source_export (ps : Array Name) (us : Array Level)
    {l : Level} {view : Lean.Level} {out : Kernel.Level}
    (viewed : ixLevel l = .ok view)
    (exported : exportSourceLevel (ps.map keyName).toList view = .ok out)
    (arity : ps.size ≤ us.size) {k : Lean.Name}
    (occurs : ParamOccurs k (Ix.Compile.Canon.substLevel ps us l)) :
    ∃ u ∈ us, ParamOccurs k u := by
  apply subst_params_of_source_export ps us viewed exported arity
  simpa only [subst_eq_runtime] using occurs


end Ix.CompileCert.Opt.LevelRefinement
