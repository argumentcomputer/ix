import CompilatrixTests.Ixby.Inline.Support

namespace CompilatrixTests.Ixby.Inline

open Ix.Ixby Compilatrix.Ixby.Inline Compilatrix.Tools.Check

def checking : IO Unit := do
  let selected ← checked (optimize {} add)
  need (selected.status == .optimized 1) "inline site count"
  let replay ← checked (optimize {} add)
  need (replay.program == selected.program) "inlining is not deterministic"
  let fixedPoint ← checked (optimize {} selected.program)
  need (fixedPoint.status == .unchanged && fixedPoint.program == selected.program) "inlining fixed point"
  for (policy, expected) in [
      ({ enabled := false : Policy }, Status.disabled),
      ({ version := 2 : Policy }, .unsupportedVersion 2),
      ({ maxWork := 0 : Policy }, .workLimit (work add) 0),
      ({ protectedPrefix := 2 : Policy }, .unchanged)] do
    let result ← checked (optimize {} add policy)
    need (result.program == add && result.status == expected) s!"inline fallback {reprStr expected}"
  let atBudget ← checked (optimize {} add { maxWork := work add })
  need (atBudget.program == selected.program) "exact optimizer work budget"
  let target := selected.program
  rejected "wrong primitive" add (instruction target 0 0 (.letOp (.primitive .natSub [.local 0, .local 1]) 1))
  rejected "wrong substitution" add (instruction target 0 0 (.letOp (.primitive .natAdd [.local 0, .local 0]) 1))
  rejected "changed continuation" add (instruction target 0 0 (.letOp (.primitive .natAdd [.local 0, .local 1]) 0))
  rejected "callee return" add (instruction target 1 1 (.ret (.local 0)))
  rejected "caller return" add (instruction target 0 1 (.ret (.local 0)))
  rejected "program entry" add { target with entry := 1 }
  rejected "constructor identity" add { target with constructors := #[⟨{ block := 2 }, 2⟩] }
  rejected "protected body" add target 1
  rejected "extra function" add { target with functions := target.functions.push target.functions[0]! }
  rejected "missing function" add { target with functions := target.functions.extract 0 1 }
  rejected "function signature" add { target with functions := target.functions.modify 0 fun fn => { fn with arity := 1 } }
  rejected "block locals" add { target with functions := target.functions.modify 0 fun fn =>
    { fn with blocks := fn.blocks.modify 1 fun block => { block with locals := 2 } } }
  let dead := { add with functions := add.functions.modify 0 fun fn =>
    { fn with blocks := fn.blocks.push ⟨0, .ret (literal 4)⟩ } }
  let deadSelected ← checked (optimize {} dead)
  rejected "changed dead block" dead (instruction deadSelected.program 0 2 (.ret (literal 5)))
  let original ← checked (check {} add add)
  let failed := selectCandidate original (instruction target 1 1 (.ret (.local 0))) 1
  need (failed.program == add) "rejected candidate was selected"
  need (match failed.status with | .rejected _ => true | _ => false) "missing rejected-candidate fallback"
  -- A changed, structurally valid two-block callee is not a leaf returning its operation.
  let nonleaf := instruction add 1 1 (.ret (.local 0))
  let nonleafSelected ← checked (optimize {} nonleaf)
  need (nonleafSelected.program == nonleaf && nonleafSelected.status == .unchanged) "non-leaf was inlined"
  let tail := instruction add 0 0 (.tailCall 1 [.local 0, .local 1])
  let tailSelected ← checked (optimize {} tail)
  need (tailSelected.program == tail && tailSelected.status == .unchanged) "tail call was rewritten"
  let unread := instruction add 0 0 (.letOp (.call 1 [.local 0, .local 9]) 1)
  match optimize {} unread with
  | .ok _ => throw (IO.userError "unreadable original argument was admitted")
  | .error _ => pure ()
  IO.println "inline checking: mutation rejection, complete dead code, protected bodies and all fallbacks passed"

end CompilatrixTests.Ixby.Inline
