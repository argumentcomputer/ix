import IxCCTests.Aiur.Static.Fixtures

namespace IxCCTests.Aiur.Static

open IxCC.Aiur
open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode

def inferredCounter (toplevel : Toplevel) (mode : UnitCounter.Mode) (step : G) : Bool :=
  match Static.prepare {} toplevel with
  | .error _ => false
  | .ok program =>
      match program.plans[0]? with
      | none => false
      | some plan =>
          match plan.counter with
          | none => false
          | some candidate => candidate.mode == mode && candidate.column == 0 &&
              candidate.step == step && !plan.component.ranked

def runPrograms (count : IO.Ref Nat) : IO Unit := do
  for increasing in [false, true] do
    let step : G := if increasing then 1 else 0 - 1
    need count s!"input direction inferred {increasing}" (inferredCounter (inputProgram increasing) .input step)
    need count s!"output direction inferred {increasing}" (inferredCounter (outputProgram increasing) .output step)
    need count s!"input metadata accepted {increasing}" (inputProgram increasing).validCallComponents
    need count s!"output metadata accepted {increasing}" (outputProgram increasing).validCallComponents
  need count "input +1 normalization" (Static.normalizedCounter ⟨.input, 0, 1⟩ [2] [8] == 2)
  need count "input -1 normalization" (Static.normalizedCounter ⟨.input, 0, 0 - 1⟩ [2] [8] == 0 - 2)
  need count "output +1 normalization" (Static.normalizedCounter ⟨.output, 0, 1⟩ [2] [8] == 0 - 8)
  need count "output -1 normalization" (Static.normalizedCounter ⟨.output, 0, 0 - 1⟩ [2] [8] == 8)
  need count "missing observation stays absent"
    ((Static.counterObservation ⟨.output, 0, 1⟩ [2] []).isNone)
  need count "mixed flags are accepted upstream" mixedProgram.validCallComponents
  match Static.prepare {} mixedProgram with
  | .error error => throw (IO.userError s!"mixed program rejected: {repr error}")
  | .ok program =>
      let some ranked := program.plans[0]? | throw (IO.userError "missing ranked plan")
      let some counter := program.plans[1]? | throw (IO.userError "missing counter plan")
      need count "ranked and counter order separated" (ranked.order == 2 && counter.order == 1)
      need count "refined order fixes global mode"
        (Static.rankedOrder ranked.order && !Static.rankedOrder counter.order)
      need count "ranked function needs no counter" ranked.counter.isNone
      need count "unranked recursive function keeps counter" counter.counter.isSome
  match Static.prepare {} fallbackProgram with
  | .error error => throw (IO.userError s!"fallback rejected: {repr error}")
  | .ok program =>
      need count "empty metadata supplies ranked fallback"
        (program.plans.all (fun plan => plan.component.ranked && plan.order == 2 && plan.counter.isNone))
  match Static.prepare {} orderedProgram with
  | .error error => throw (IO.userError s!"ordered program rejected: {repr error}")
  | .ok program =>
      need count "nonrecursive functions need no counter" (program.plans.all (·.counter.isNone))
      need count "cross-component order retained"
        ((program.plans.map (·.order)).toList == [1, 3])
  need count "empty program admitted" (Static.prepare {} WireFixtures.empty).isOk
  need count "fallback function count bounded"
    (failed (Static.prepare { maxFunctions := 0 } fallbackProgram) .functionLimit)
  need count "nonempty component function count bounded"
    (failed (Static.prepare { maxFunctions := 0 } (inputProgram false)) .functionLimit)
  need count "component work preflight preserved"
    (failed (Static.prepare { maxWork := 0 } (inputProgram false))
      (.components "Aiur bytecode: component analysis resource limit"))
  let huge := { inputProgram false with functions := #[
    { (inputProgram false).functions[0]! with layout := ⟨2 ^ 64, 1, 0, 0⟩ }] }
  need count "compact huge input count rejected before analysis"
    (failed (Static.prepare {} huge) (.components "Aiur bytecode: component analysis resource limit"))
  need count "ranked fallback does not allocate from input count"
    (Static.prepare {} { huge with callComponents := #[] }).isOk
  need count "backward component edge rejected"
    (failed (Static.prepare {} { orderedProgram with callComponents := #[⟨1, false⟩, ⟨0, false⟩] })
      (.components "Aiur bytecode: invalid static call components"))
  need count "unranked mutual recursion rejected"
    (failed (Static.prepare {} { Execution.rankedProgram with callComponents := #[⟨0, false⟩, ⟨0, false⟩] })
      (.components "Aiur bytecode: invalid static call components"))
  need count "component table length checked"
    (failed (Static.prepare {} { orderedProgram with callComponents := #[⟨0, false⟩] })
      (.components "Aiur bytecode: invalid static call components"))
  need count "component order bound checked"
    (failed (Static.prepare {} { inputProgram false with callComponents := #[⟨1, false⟩] })
      (.components "Aiur bytecode: invalid static call components"))

end IxCCTests.Aiur.Static
