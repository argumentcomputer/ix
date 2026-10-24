import Ix.Cert.PrefixTowers
import IxC.Kernel.Verify.DivModInv

/-! # Actual prefix Nat-operation guards and fixed-interpretation readings

Every stored operation has its actual creating step. Its post-step guard
survives the actual suffix, supplying both subject and reduct resolution
without a prefix model or backwards inference from final support.
-/

namespace Ix.Cert.PrefixNatOps

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.PrefixConstType Ix.Cert.PrefixDefinitions Ix.Cert.ReferenceFronts

variable {md : Mode} {before final : Env md}

/-- Preserve only an actually true guard, through its positive queries. -/
theorem guard_preserved (lookup : FindPreserved before final) {c : Key md}
    (guard : natOpGuard before c = true) : natOpGuard final c = true := by
  obtain ⟨support, deps, bool⟩ := natOpGuard_inv guard
  refine natOpGuard_intro (PrefixReadings.nat_support lookup support) ?_ ?_
  · intro n member
    obtain ⟨cv, body, hint, found, levels⟩ := deps n member
    exact ⟨cv, body, hint, lookup found, levels⟩
  · intro comparison
    obtain ⟨⟨ciT, foundT, levelsT⟩, ⟨ciF, foundF, levelsF⟩⟩ := bool comparison
    exact ⟨⟨ciT, lookup foundT, levelsT⟩, ⟨ciF, lookup foundF, levelsF⟩⟩

/-- EVERY guard comes from its actual creating POST environment and suffix.
Structural and WF-certified operations use their original run guard packs. -/
theorem reference_nat_op_guards {ev : Evidences md} {ds : List (Declaration md)}
    {env : Env md} (accepted : Cached.AcceptsRef .verified ev ds env) : NatOpGuardLaw env := by
  intro c relevant stored
  obtain ⟨cv, body, hint, found⟩ := natOpStored_inv stored
  obtain ⟨j, rawCv, raw, F, origin, names, _, created⟩ :=
    reference_stored_definition_origin accepted (Semantics.Env.find?_mem found)
  have name : rawCv.name = c := names.trans (Semantics.Env.find?_name found)
  obtain ⟨_, _, _, step, suffix, _, _, _⟩ := created
  let after : Env md :=
    ⟨.defnInfo ⟨rawCv.name, rawCv.levelParams, cv.type⟩ body hint :: origin.consts⟩
  obtain ⟨_, _, _, _, _, structural, wf⟩ := declDefnRun_of step
  have guard : natOpGuard after rawCv.name = true := by
    rcases relevant with member | member
    · exact (structural (List.contains_iff_mem.mpr (by simpa only [name] using member))).1
    · exact (divModEnvGuard_inv
        (wf (List.contains_iff_mem.mpr (by simpa only [name] using member))).1).1
  have growth := foldlM_checkDecl_post .verified (fueledOps .verified F) ev
    (ds.drop (j + 1)) after env suffix
  have lookup : FindPreserved after env := by intro n ci hit; exact growth.persist hit
  simpa only [name] using guard_preserved lookup guard

theorem binary_mem {c : Key md} (member : c ∈ Ix.Kernel.Rules.natBinOpNames) :
    c ∈ natOpNames ∨ c ∈ natDivModNames := by
  rcases List.mem_append.mp member with member | member
  · exact Or.inl (List.mem_cons_of_mem natPredName member)
  · exact Or.inr member

theorem literal_resolves (support : natLitSupported before = true) (n : Nat) :
    (Ix.Kernel.Expr.lit (.natVal n)).constsResolve before = true := by
  obtain ⟨_, _, _, _, _, _, _, _, foundN, foundZ, foundS, _⟩ := natLitSupported_inv support
  simp only [Ix.Kernel.Expr.constsResolve, foundN, foundZ, foundS, Option.isSome_some, Bool.and_true]

theorem raw_literal_resolves (support : natLitSupported before = true)
    {arg : Ix.Kernel.Expr md} {n : Nat} (raw : rawNatLit? arg = some n) :
    arg.constsResolve before = true := by
  match arg, raw with
  | .lit (.natVal k), _ => exact literal_resolves support k
  | .const c [], raw =>
    simp only [rawNatLit?] at raw
    split at raw
    · next eq =>
      subst eq
      obtain ⟨_, _, _, _, _, _, _, _, _, foundZ, _⟩ := natLitSupported_inv support
      simp only [Ix.Kernel.Expr.constsResolve, foundZ, Option.isSome_some]
    · exact nomatch raw

/-- Successful results are Nat literals or the exact guarded Bool heads. -/
theorem result_resolves {c : Key md} {a b : Nat} {r : Ix.Kernel.Expr md}
    (guard : natOpGuard before c = true) (result : natOpResult c a b = some r) :
    r.constsResolve before = true := by
  obtain ⟨support, _, bool⟩ := natOpGuard_inv guard
  rcases natOpResult_atom result with ⟨n, rfl⟩ | ⟨comparison, shape⟩
  · exact literal_resolves support n
  · obtain ⟨⟨ciT, foundT, _⟩, ⟨ciF, foundF, _⟩⟩ := bool
      (comparison.elim Or.inl (fun h => Or.inr (Or.inl h)))
    rcases shape with rfl | rfl <;>
      simp only [Ix.Kernel.Expr.constsResolve, foundT, foundF, Option.isSome_some]

/-- Both reading equations at arbitrary acval/depth, from the ORIGINAL
row's raw/stored/result facts and the produced prefix guard law. -/
theorem guarded_nat_op_readings (guards : NatOpGuardLaw before)
    (lookup : FindPreserved before final) (slots : StoredHeadSlots before final)
    (acval : Key md → (LevelParam → Nat) → AnnotTerm) (φ : LevelParam → Nat) (d : Nat)
    {c : Key md} {wa wb r : Ix.Kernel.Expr md} {a b : Nat}
    (member : c ∈ Ix.Kernel.Rules.natBinOpNames) (stored : natOpStored before c = true)
    (rawA : rawNatLit? wa = some a) (rawB : rawNatLit? wb = some b)
    (result : natOpResult c a b = some r) :
    natOpStored final c = true ∧
    denoteMeta acval before φ d (.app (.app (.const c []) wa) wb) =
      denoteMeta acval final φ d (.app (.app (.const c []) wa) wb) ∧
    denoteMeta acval before φ d r = denoteMeta acval final φ d r := by
  have guard := guards c (binary_mem member) stored
  obtain ⟨cv, body, hint, found⟩ := natOpStored_inv stored
  have subject : (.app (.app (.const c []) wa) wb : Ix.Kernel.Expr md).constsResolve before = true := by
    simp only [Ix.Kernel.Expr.constsResolve, found, Option.isSome_some, Bool.true_and, Bool.and_eq_true]
    exact ⟨raw_literal_resolves (natOpGuard_inv guard).1 rawA,
      raw_literal_resolves (natOpGuard_inv guard).1 rawB⟩
  refine ⟨?_, resolving_reading_eq acval φ d _ lookup slots subject,
    resolving_reading_eq acval φ d _ lookup slots (result_resolves guard result)⟩
  simp only [natOpStored, lookup found]

end Ix.Cert.PrefixNatOps

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.PrefixNatOps

variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- The SAME actual take-i prefix supplies every operation guard. -/
theorem DefinitionFrontAt.prefix_nat_op_guards
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked) :
    NatOpGuardLaw before := by
  obtain ⟨_, _, prefixRun, _, _, _, _, _⟩ := front
  exact reference_nat_op_guards ⟨F, prefixRun⟩

end Ix.Cert.ReferenceFronts
