import Ix.CompileCert.Pj.ConstructorSteps
import Init.Data.List.Nat.Range

/-!
Complete member coverage for the installed recursor reader.

The accepted constructor-step theorem concludes the predicate at one
recursor's major. This module checks an actual installed recursor at EVERY
position of the common motive family, transports the complete shared
parameter/motive/minor data, and assembles the conclusions for all members.
It also derives constructor coverage from recursor membership, rather than
assuming that a model's carrier contains only constructor values.

This is an internal reader/semantic bridge, not a new final input domain.
The source/export adapter must still produce this complete ordered recursor
list and discharge the existing literal-header checks or their general
WHNF/annotation counterpart. No accepted-source completeness, general
O7--O12 theorem, or runtime change is claimed here. The source is uncompiled.
-/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

namespace RecFamily

/-- Read the actual installed entry. Compare the full common data, not just
its dimensions; only the member's major and final binder metadata may vary.
The ordinary reader retains its complete Check, including RecOk and CtorOk. -/
def checkMember (env : Kernel.Env) (common : RecRd) (j : Nat)
    (r : Kernel.Name) : Bool :=
  match readRec env r common.np common.nm common.nmin with
  | none => false
  | some member => decide (member.params = common.params ∧
      member.motives = common.motives ∧ member.minors = common.minors ∧
      member.major = j)

theorem checkMember_iff {env : Kernel.Env} {common : RecRd}
    {j : Nat} {r : Kernel.Name} :
    checkMember env common j r = true ↔
      ∃ member, readRec env r common.np common.nm common.nmin = some member ∧
        member.params = common.params ∧ member.motives = common.motives ∧
        member.minors = common.minors ∧ member.major = j := by
  constructor
  · intro accepted
    cases parsed : readRec env r common.np common.nm common.nmin with
    | none => simp only [checkMember, parsed, Bool.false_eq_true] at accepted
    | some member =>
      refine ⟨member, rfl, ?_⟩
      exact of_decide_eq_true (by simpa only [checkMember, parsed] using accepted)
  · rintro ⟨member, parsed, shared⟩
    simpa only [checkMember, parsed, decide_eq_true_eq] using shared

/-- Exact ordered coverage: one source recursor name per common motive,
with no prefix, subset, deduplication, successful-entry filtering or hash key.
Even the empty family is handled without an additional nonempty premise. -/
def check (env : Kernel.Env) (common : RecRd) (recursors : List Kernel.Name) : Bool :=
  decide (recursors.length = common.nm) &&
    recursors.zipIdx.all (fun entry => checkMember env common entry.2 entry.1)

/-- Both directions preserve every actual read and every shared field. In
particular a missing or extra source recursor cannot be silently discarded. -/
theorem check_iff {env : Kernel.Env} {common : RecRd}
    {recursors : List Kernel.Name} :
    check env common recursors = true ↔
      recursors.length = common.nm ∧
      ∀ j (bound : j < recursors.length),
        ∃ member,
          readRec env recursors[j] common.np common.nm common.nmin = some member ∧
          member.params = common.params ∧ member.motives = common.motives ∧
          member.minors = common.minors ∧ member.major = j := by
  constructor
  · intro accepted
    obtain ⟨length, entries⟩ := Bool.and_eq_true_iff.mp accepted
    refine ⟨of_decide_eq_true length, ?_⟩
    intro j bound
    have present : (recursors[j], j) ∈ recursors.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem bound)
    exact checkMember_iff.mp ((List.all_eq_true.mp entries) _ present)
  · rintro ⟨length, entries⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true length, List.all_eq_true.mpr ?_⟩
    intro entry present
    have bound : entry.2 < recursors.length := by
      simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx present
    have selected : recursors[entry.2] = entry.1 :=
      Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans
        (List.mem_zipIdx_iff_getElem?.mp present))
    have member := entries entry.2 bound
    rw [selected] at member
    exact checkMember_iff.mpr member

/-- Every motive position obtains a real installed, checked recursor. The
caller supplies a family position, not a separate per-member lookup premise. -/
theorem checked_member {env : Kernel.Env} {common : RecRd}
    {recursors : List Kernel.Name} (accepted : check env common recursors = true)
    (j : Nat) (bound : j < common.nm) :
    ∃ r member, recursors[j]? = some r ∧
      readRec env r common.np common.nm common.nmin = some member ∧
      member.Check env r ∧ member.params = common.params ∧
      member.motives = common.motives ∧ member.minors = common.minors ∧
      member.major = j := by
  obtain ⟨length, entries⟩ := check_iff.mp accepted
  have inside : j < recursors.length := by simpa only [length] using bound
  obtain ⟨member, parsed, shared⟩ := entries j inside
  exact ⟨recursors[j], member, List.getElem?_eq_getElem inside, parsed,
    readRec_sound parsed, shared⟩

/-- Distinct family positions cannot be certified by reusing a single
installed recursor name. This follows from the actual deterministic read and
major index, and needs no external name-injectivity or hash assumption. -/
theorem member_names_injective {env : Kernel.Env} {common : RecRd}
    {recursors : List Kernel.Name} (accepted : check env common recursors = true)
    {i j : Nat} (hi : i < recursors.length) (hj : j < recursors.length)
    (same : recursors[i] = recursors[j]) : i = j := by
  have entries := (check_iff.mp accepted).2
  obtain ⟨left, leftRead, _, _, _, leftMajor⟩ := entries i hi
  obtain ⟨right, rightRead, _, _, _, rightMajor⟩ := entries j hj
  have records : left = right := by
    rw [same] at leftRead
    exact Option.some.inj (leftRead.symm.trans rightRead)
  exact leftMajor.symm.trans ((congrArg RecRd.major records).trans rightMajor)

/-- Simultaneous member assembly from the original semantic constructor
steps. Header checks are shared once for the complete minor inventory;
every member's recursor membership is obtained from the actual family read.
The arbitrary model, universe assignment, valuation and typed major tuples
are retained. Source/WHNF completeness remains an upstream obligation. -/
theorem predicate_of_constructor_steps
    {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env} {common : RecRd}
    {recursors : List Kernel.Name} (accepted : check env common recursors = true)
    (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (common.params.map Prod.fst) params)
    (predicate : Nat → List V → Prop)
    (headers : ∀ n ∈ common.minors,
      InstalledHeader.checkMinorResult env common.params common.motives n = true)
    (recursiveHeaders : ∀ n ∈ common.minors,
      InstalledHeader.checkRecursiveFields env common.params common.motives n = true)
    (steps : ∀ n ∈ common.minors,
      MinorStep.ConstructorStep strong.public.cval env φ ρ params
        common.np common.motives n predicate) :
    ∀ j, j < common.nm → ∀ arguments,
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        (((common.motives.getD j default).tele common.np).map Prod.fst) arguments →
      predicate j arguments := by
  intro j bound arguments typed
  obtain ⟨r, member, _, _, checked, parameters, motives, minors, major⟩ :=
    checked_member accepted j bound
  have memberParams : TeleTyped strong.public.cval env φ ρ
      (member.params.map Prod.fst) params := by
    simpa only [parameters] using paramsTyped
  have memberHeaders : ∀ n ∈ member.minors,
      InstalledHeader.checkMinorResult env member.params member.motives n = true := by
    simpa only [parameters, motives, minors] using headers
  have memberRecursiveHeaders : ∀ n ∈ member.minors,
      InstalledHeader.checkRecursiveFields env member.params member.motives n = true := by
    simpa only [parameters, motives, minors] using recursiveHeaders
  have memberSteps : ∀ n ∈ member.minors,
      MinorStep.ConstructorStep strong.public.cval env φ ρ params
        member.np member.motives n predicate := by
    simpa only [RecRd.np, parameters, motives, minors] using steps
  have memberTyped : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      ((member.majorMotive.tele member.np).map Prod.fst) arguments := by
    simpa only [RecRd.majorMotive, RecRd.np, parameters, motives, major] using typed
  have result := member.predicate_of_literal_header_constructor_steps checked strong
    φ ρ params memberParams predicate memberHeaders memberRecursiveHeaders memberSteps
    arguments memberTyped
  simpa only [major] using result

/-- The entire family has constructor coverage, including all typed carrier
elements of an arbitrary strong model. This is derived from the recursors'
membership laws; it is not an element-inversion premise. All field domains,
constructor universe instances and result-index readings are retained. -/
theorem exists_constructor_of_typed
    {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env} {common : RecRd}
    {recursors : List Kernel.Name} (accepted : check env common recursors = true)
    (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (common.params.map Prod.fst) params)
    (headers : ∀ n ∈ common.minors,
      InstalledHeader.checkMinorResult env common.params common.motives n = true)
    (recursiveHeaders : ∀ n ∈ common.minors,
      InstalledHeader.checkRecursiveFields env common.params common.motives n = true)
    (j : Nat) (bound : j < common.nm) (arguments : List V)
    (typed : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      (((common.motives.getD j default).tele common.np).map Prod.fst) arguments) :
    ∃ n ∈ common.minors, n.motive = j ∧ ∃ fields constructor indices,
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        ((n.fieldTys common.np common.motives).map Prod.fst) fields ∧
      (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) ∧
      DenotesSpine strong.public.cval env φ (pushArguments ρ (params ++ fields))
        n.resIdx indices ∧
      arguments = indices ++ [(params ++ fields).foldl app constructor] := by
  let predicate : Nat → List V → Prop := fun k values =>
    ∃ n ∈ common.minors, n.motive = k ∧ ∃ fields constructor indices,
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        ((n.fieldTys common.np common.motives).map Prod.fst) fields ∧
      (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) ∧
      DenotesSpine strong.public.cval env φ (pushArguments ρ (params ++ fields))
        n.resIdx indices ∧
      values = indices ++ [(params ++ fields).foldl app constructor]
  have steps : ∀ n ∈ common.minors,
      MinorStep.ConstructorStep strong.public.cval env φ ρ params
        common.np common.motives n predicate := by
    intro n present fields fieldsTyped _ constructor indices constructorRead indexRead
    exact ⟨n, present, rfl, fields, constructor, indices, fieldsTyped,
      constructorRead, indexRead, rfl⟩
  exact predicate_of_constructor_steps accepted strong φ ρ params paramsTyped
    predicate headers recursiveHeaders steps j bound arguments typed

end RecFamily

end Ix.CompileCert.Pj

#print axioms Ix.CompileCert.Pj.RecFamily.checkMember_iff
#print axioms Ix.CompileCert.Pj.RecFamily.check_iff
#print axioms Ix.CompileCert.Pj.RecFamily.checked_member
#print axioms Ix.CompileCert.Pj.RecFamily.member_names_injective
#print axioms Ix.CompileCert.Pj.RecFamily.predicate_of_constructor_steps
#print axioms Ix.CompileCert.Pj.RecFamily.exists_constructor_of_typed
