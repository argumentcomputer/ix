import IxVMRefinement.Decl.DeclRoleStep
import IxVMRefinement.Decl.TheoremRestoreInstall

/-! # Typed theorem rows from actual prefix checks

The local lookup simulation transports a checked value and its proposition check. A fresh
theorem row is established before it is added to the simulation, so no global typing premise
for that fresh theorem is assumed.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Refinement.Assembly

namespace ThmKind

/-- Existing theorem typing survives an actual environment extension. -/
theorem typed_weaken {before after : Env .anon} {cv : ConstantVal .anon} {value : Expr .anon}
    (extension : EnvExt before after) (typed : ThmValueTyped before cv value) :
    ThmValueTyped after cv value := by
  obtain ⟨closed, bounded, vt, st, u, hv, hd, ht, hs, hz⟩ := typed
  exact ⟨closed, bounded, vt, st, u, Rules.Infer.weaken extension hv, Rules.DefEq.weaken extension hd,
    Rules.Infer.weaken extension ht, Rules.Red.weaken extension hs, hz⟩

/-- A plain extension changes no opaque definition into a theorem, so it needs no theorem rows. -/
theorem of_envExt {before after : Env .anon} (extension : EnvExt before after) :
    ThmSimAt before after where
  thmTyped := by
    intro name cv value original restored
    have same := extension.find original
    rw [restored] at same
    cases same
  find_sim := fun found => .inl (extension.find found)
  tables_eq := extension.tables

/-- Checked value and proposition derivations at the real prefix construct the target theorem row. -/
theorem value_typed {before after : Env .anon} (simulation : ThmSimAt before after)
    {cv : ConstantVal .anon} {rawValue type value : Expr .anon}
    (checked : ValueFrontRunJ rulesJ before cv rawValue type value)
    (proposition : ∃ st u, rulesJ.infer before 0 type st ∧ rulesJ.sort before 0 st u ∧ rulesJ.isZero u) :
    ThmValueTyped after { cv with type } value := by
  obtain ⟨bounded, closed, annotated, _, _, vt, inferred, converted⟩ := checked
  obtain ⟨outputClosed, outputBounded⟩ := (judgeFrames_rulesJ before).annot_syntax annotated closed bounded
  obtain ⟨st, u, typeInferred, sorted, zero⟩ := proposition
  exact ⟨outputClosed, outputBounded, vt, st, u, simulation.infer inferred,
    simulation.defEq converted, simulation.infer typeInferred, simulation.red sorted, zero⟩

/-- Actual kernel calls supply the theorem row, including the proposition result at that prefix. -/
theorem value_typed_of_runs {before after : Env .anon} (simulation : ThmSimAt before after)
    {fuel propFuel : Nat} {cv : ConstantVal .anon} {rawValue type value st : Expr .anon} {u : Level}
    (checked : ValueFrontRun .verified fuel before cv rawValue type value)
    (typeInferred : inferTypeCore .verified before propFuel 0 type = .ok st)
    (sorted : ensureSortCore .verified before propFuel 0 st = .ok u)
    (zero : u.isZero = true) :
    ThmValueTyped after { cv with type } value :=
  value_typed simulation (valueFrontRun_rulesJ checked)
    ⟨st, u, (verifiedRunMap propFuel).infer typeInferred,
      (verifiedRunMap propFuel).sort sorted, (verifiedRunMap propFuel).isZero zero⟩

/-- The keys whose opaque definitions may be viewed as theorem entries by the core transfer. -/
def AllowedKey (name : Key .anon) : Prop :=
  name ∉ Rules.natBinOpNames ∧ name.isProjFnShape = false ∧ name ≠ punitName ∧ name ≠ punitRecName

private theorem not_table {name T : Key .anon} (shape : name.isProjFnShape = false) :
    name ≠ projTableName T := by
  intro same
  rw [same, Ix.Kernel.Semantics.projTableName_isProjFnShape] at shape
  cases shape

/-- Install a freshly checked theorem row into the local simulation. -/
theorem cons_theorem {before after : Env .anon} (simulation : ThmSimAt before after)
    {cv : ConstantVal .anon} {value : Expr .anon}
    (fresh : after.find? cv.name = none) (allowed : AllowedKey cv.name)
    (typed : ThmValueTyped after cv value) :
    ThmSimAt ⟨.defnInfo cv value .opaque :: before.consts⟩
      ⟨.thmInfo cv value :: after.consts⟩ := by
  have extension : EnvExt after ⟨.thmInfo cv value :: after.consts⟩ :=
    EnvExt.cons fresh (fun _ => not_table allowed.2.1)
  have newTyped := typed_weaken extension typed
  refine ⟨?_, ?_, ?_⟩
  · intro name cv' value' original restored
    rw [Env.find?_cons] at original restored
    change (if cv.name = name then some (.defnInfo cv value .opaque) else before.find? name) =
      some (.defnInfo cv' value' .opaque) at original
    change (if cv.name = name then some (.thmInfo cv value) else after.find? name) =
      some (.thmInfo cv' value') at restored
    by_cases same : cv.name = name
    · rw [ite_eq_left same] at original
      obtain ⟨rfl, rfl, _⟩ := ConstantInfo.defnInfo.inj (Option.some.inj original)
      exact newTyped
    · rw [ite_eq_right same] at original restored
      exact typed_weaken extension (simulation.thmTyped name cv' value' original restored)
  · intro name ci original
    rw [Env.find?_cons] at original ⊢
    change (if cv.name = name then some (.defnInfo cv value .opaque) else before.find? name) = some ci at original
    by_cases same : cv.name = name
    · rw [ite_eq_left same] at original
      obtain rfl := Option.some.inj original
      refine .inr ⟨cv, value, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [← same] using allowed.1
      · simpa only [← same] using allowed.2.1
      · simpa only [← same] using allowed.2.2.1
      · simpa only [← same] using allowed.2.2.2
      · simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, same, ↓reduceIte]
    · rw [ite_eq_right same] at original
      rcases simulation.find_sim original with unchanged | ⟨val, body, kind, hn, hs, hp, hr, found⟩
      · exact .inl (by simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, ite_eq_right same] using unchanged)
      · exact .inr ⟨val, body, kind, hn, hs, hp, hr,
          by simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, ite_eq_right same] using found⟩
  · intro T val flags found
    rw [Env.find?_cons] at found
    split at found
    · cases found
    · have oldTable := simulation.tables_eq found
      rw [Env.find?_cons, Env.find?_cons]
      have different := not_table (T := T) allowed.2.1
      simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, ite_eq_right different] using oldTable

end ThmKind
end IxVM.Refinement.Decl
