import CompilatrixTests.Ixby.Inline.Support

namespace CompilatrixTests.Ixby.Inline

open Ix.Ixby Compilatrix.Ixby.Inline Compilatrix.Tools.Check

private def operations : IO Unit := do
  compare "large naturals" add #[natural (2 ^ 80), natural 17] (.ok (natural (2 ^ 80 + 17)))
  compare "reordered arguments"
    (fixture ⟨2, .primitive .natSub [.local 0, .local 1]⟩ [.local 1, .local 0])
    #[natural 3, natural 17] (.ok (natural 14))
  compare "duplicated arguments"
    (fixture ⟨2, .primitive .natAdd [.local 1, .local 1]⟩ [.local 0, .local 1])
    #[natural 3, natural 17] (.ok (natural 34))
  compare "unused argument and literal"
    (fixture ⟨2, .copy (.local 1)⟩ [.local 0, literal 91] 1)
    #[.erased] (.ok (natural 91))
  compare "erased operand"
    (fixture ⟨1, .copy .erased⟩ [literal 1] 0) #[] (.ok .erased)
  compare "literal in leaf"
    (fixture ⟨1, .copy (literal 23)⟩ [.local 0] 1) #[.erased] (.ok (natural 23))
  let constructor := fixture ⟨2, .construct 0 [.local 1, .local 0]⟩ [.local 0, .local 1]
  compare "constructor" constructor #[natural 3, .erased] (.ok (.ctor { block := 1 } #[.erased, natural 3]))
  let projection := fixture ⟨1, .project (.local 0) 1⟩ [.local 0] 1
  compare "projection" projection #[.ctor { block := 1 } #[.erased, natural 19]] (.ok (natural 19))
  compare "erased projection" projection #[.erased] (.ok .erased)
  compare "nonconstructor projection" projection #[natural 3] (.error .notConstructor)
  compare "bad projection" (fixture ⟨1, .project (.local 0) 2⟩ [.local 0] 1)
    #[.ctor { block := 1 } #[.erased, .erased]] (.error (.invalidProjection 2))
  compare "primitive type" add #[natural 3, .scalar (.bool true)] (.error (.primitiveType .natAdd))
  compare "primitive capacity" add #[natural 255, natural 1] (.error (.limit .natBits)) { natBits := 8 }
  compare "input capacity" add #[natural 256, natural 1] (.error (.limit .natBits)) { natBits := 8 }
  compare "input node budget" add #[natural 3, natural 1] (.error (.limit .inputNodes)) { inputNodes := 1 }
  compare "input arity" add #[natural 3] (.error (.arityMismatch 2 1))

private def control : IO Unit := do
  let recursive : Program := { functions := #[
    { arity := 1, blocks := #[
      ⟨1, .caseNat (.local 0) 1 2⟩, ⟨1, .ret (literal 0)⟩,
      ⟨2, .letOp (.callSelf [.local 1]) 3⟩,
      ⟨3, .letOp (.call 1 [.local 2, literal 1]) 4⟩,
      ⟨4, .ret (.local 3)⟩] },
    (Leaf.mk 2 (.primitive .natAdd [.local 0, .local 1])).function] }
  for n in [0, 1, 9] do compare "self recursion" recursive #[natural n] (.ok (natural n))
  let mutualCaller : Function := { arity := 1, blocks := #[⟨1, .tailCall 0 [.local 0]⟩] }
  let mutualProgram := { recursive with functions := recursive.functions.push mutualCaller }
  let mutualProgram := instruction mutualProgram 0 2 (.letOp (.call 2 [.local 1]) 3)
  compare "mutual recursion" mutualProgram #[natural 7] (.ok (natural 7))
  let higher : Program := { functions := #[
    { arity := 0, blocks := #[⟨0, .letOp (.closure 1 []) 1⟩,
      ⟨1, .letOp (.apply (.local 0) [literal 5, literal 9]) 2⟩,
      ⟨2, .ret (.local 1)⟩] },
    { arity := 1, blocks := #[⟨1, .letOp (.closure 2 [.local 0]) 1⟩,
      ⟨2, .ret (.local 1)⟩] },
    wrapper 2 3 [.local 0, .local 1],
    (Leaf.mk 2 (.primitive .natAdd [.local 0, .local 1])).function] }
  compare "closure and overapplication" higher #[] (.ok (natural 14))
  compare "bad dynamic apply" (instruction higher 0 1 (.letOp (.apply (literal 0) [literal 1]) 2))
    #[] (.error .notFunction)
  let looping : Function := { arity := 0, blocks := #[⟨0, .tailCallSelf []⟩] }
  let cycle := { add with functions := add.functions.push looping, entry := 2 }
  compare "nonterminating self call" cycle #[] (.error .outOfFuel)

private def resources : IO Unit := do
  let selected ← checked (optimize {} add)
  let input := #[natural 2, natural 3]
  for fuel in [:10] do
    let baseline := execute {} add input fuel
    let optimized := execute {} selected.program input fuel
    let expect (threshold : Nat) : Except Error Value :=
      if fuel ≥ threshold then .ok (natural 5) else .error .outOfFuel
    need (same baseline (expect 6)) s!"baseline fuel boundary {fuel}"
    need (same optimized (expect 3)) s!"optimized fuel boundary {fuel}"
  let zeroStack : Limits := { continuations := 0, locals := 3, operands := 2 }
  let tight ← checked (optimize zeroStack add)
  need (same (execute zeroStack add input 100) (.error (.limit .continuations))) "original stack boundary"
  need (same (execute zeroStack tight.program input 3) (.ok (natural 5))) "optimized stack boundary"
  need (same (execute { zeroStack with continuations := 1 } add input 12) (.ok (natural 5)))
    "reflection's additional continuation"
  for limits in [{ locals := 2 : Limits }, { operands := 1 : Limits }, { functions := 1 : Limits }] do
    match optimize limits add with
    | .ok _ => throw (IO.userError "inlining hid an original admission failure")
    | .error _ => pure ()
  let artifact : Compilatrix.Ixby.Binary.Artifact := { limits := {}, maxSteps := 100, program := selected.program }
  let encoded ← checked (Compilatrix.Ixby.Binary.encode artifact |>.mapError reprStr)
  let decoded ← checked (Compilatrix.Ixby.Binary.decode encoded |>.mapError reprStr)
  discard <| checked (check decoded.value.limits add decoded.value.program)
  need (decoded.value == artifact) "inlining binary roundtrip differs"

def execution : IO Unit := do
  operations
  control
  resources
  IO.println "inline execution: operations, errors, recursion, closures, fuel, limits and binary rechecking passed"

end CompilatrixTests.Ixby.Inline
