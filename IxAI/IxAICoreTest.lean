import IxAICore

/-!
Build-time tests for the certified core: every `#guard` runs when this library builds.
-/

namespace IxAICoreTest

open IxAICore


-- Answer positions agree with each answer type's enumeration.
#guard (Finite.all : List Bool).map Finite.index == [0, 1]
#guard (Finite.all : List Head).map Finite.index == List.range 5
#guard (Finite.all : List Coverage).map Finite.index == List.range 4
#guard Triage.spec.outputs == 11

def coreTiny : Config :=
  { seed := 42, hidden := 4, lrRaw := 2, epochs := 1, batch := 8, trainSize := 16, testSize := 16 }
def coreSmall : Config :=
  { seed := 42, hidden := 8, lrRaw := 2, epochs := 2, batch := 16, trainSize := 64, testSize := 32 }

-- Labels come from the decision procedures.
#guard (coreSmall.data Triage.spec).all fun f =>
  Triage.spec.targets f == (Triage.spec.slots.flatMap fun q =>
    (List.range q.arity).map fun k => if k == q.target f then Fx.one else Fx.zero)
#guard Triage.coverageOf (.imp (.atom 0) (.atom 0)) == .always
#guard Triage.headOf (.imp (.atom 1) (.and (.atom 0) .top)) == .none

def coreTen : Config := { coreSmall with epochs := 10 }

-- Ten epochs improve every question's held-out Brier score over the initial weights.
#guard
  let before := card Triage.spec coreTen (coreTen.init Triage.spec)
  let after := card Triage.spec coreTen (train Triage.spec coreTen)
  (before.questions.zip after.questions).all fun (b, a) => a.brierRaw < b.brierRaw

-- The per-step chain ends at the specified training result.
#guard
  let ex := (coreSmall.data Triage.spec).map Triage.spec.example
  let links := coreSmall.schedule.foldl (fun (acc : Model × List (Link Model (List Nat))) idx =>
    let m' := coreSmall.stepFn Triage.spec ex acc.1 idx
    (m', acc.2 ++ [⟨acc.1, idx, m'⟩])) (coreSmall.init Triage.spec, [])
  chainEnd (coreSmall.init Triage.spec) links.2 == train Triage.spec coreSmall

-- The gate never publishes an invalid formula, for trained, initial or arbitrary weights.
#guard
  let fs := coreSmall.test Triage.spec
  let ms := [train Triage.spec coreSmall, coreSmall.init Triage.spec,
    { (coreSmall.init Triage.spec) with b2 := (List.range 11).map fun _ => Fx.ofInt 5 }]
  ms.all fun m => fs.all fun f => Triage.act ⟨0⟩ m f != .publish || f.valid


/-! ### The gate's domain -/

-- `valid` enumerates only `P0 … P2`: it calls `P3 → P0` valid, yet the assignment making only
-- `P3` true falsifies it.
def outOfScope : Formula := .imp (.atom 3) (.atom 0)
#guard outOfScope.valid && !outOfScope.eval (fun n => n == 3)
#guard !outOfScope.inScope
-- The gate's entry refuses it whatever the weights and threshold.
#guard [train Triage.spec coreSmall, coreSmall.init Triage.spec].all fun m =>
  ([-100000, 0, 256] : List Int).all fun t => Triage.admit ⟨t⟩ m outOfScope == none
-- Within the domain the entry is the gate.
#guard
  let m := train Triage.spec coreSmall
  (coreSmall.test Triage.spec).all fun f => Triage.admit ⟨100⟩ m f == some (Triage.act ⟨100⟩ m f)
#guard Triage.admit ⟨-100000⟩ (coreSmall.init Triage.spec) (.imp (.atom 2) (.atom 2)) == some .publish
-- Generated formulas are in the domain (proved for every config: `Triage.data_scoped`).
#guard (coreSmall.data Triage.spec).all (·.inScope) && (coreSmall.test Triage.spec).all (·.inScope)
example : ∀ f ∈ coreSmall.data Triage.spec, f.inScope = true := Triage.data_scoped coreSmall
-- On scoped formulas `valid` is truth under every assignment, and so is what the gate publishes.
example (f : Formula) (hs : f.inScope = true) : f.valid = true ↔ ∀ v, f.eval v = true :=
  Formula.valid_iff_forall_eval f hs
example (g : Triage.Gate) (m : Model) (f : Formula) (h : Triage.admit g m f = some .publish) :
    ∀ v, f.eval v = true :=
  Triage.admit_publish_true g m f h

/-! ### Variants for new specifications -/

-- `probabilities` caps outputs at 1: `[1.0, 2.0]` becomes a tie although the model answers the
-- second. `probabilitiesNonneg` keeps the margin.
#guard probabilities [⟨256⟩, ⟨512⟩] == [⟨128⟩, ⟨128⟩] && argmax [⟨256⟩, ⟨512⟩] == 1
#guard probabilitiesNonneg [⟨256⟩, ⟨512⟩] == [⟨85⟩, ⟨170⟩]
-- Both agree when every output is at most 1.
#guard probabilitiesNonneg [⟨10⟩, ⟨-5⟩, ⟨200⟩] == probabilities [⟨10⟩, ⟨-5⟩, ⟨200⟩]
#guard probabilitiesNonneg [⟨-10⟩, ⟨-5⟩] == probabilities [⟨-10⟩, ⟨-5⟩]
-- `chunk 0` yields `fuel` empty chunks; `chunkPos` cuts chunks of at least one element.
#guard chunk 0 [1, 2, 3] 3 == [[], [], []]
#guard chunkPos 0 [1, 2, 3] 3 == [[1], [2], [3]]
#guard chunkPos 2 [1, 2, 3, 4, 5] 5 == chunk 2 [1, 2, 3, 4, 5] 5

end IxAICoreTest
