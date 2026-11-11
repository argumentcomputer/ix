import IxCC.X86.Exe.Validate
import IxCC.CompileClaim

/-!
# Standalone executables of compiled roots

`Exe.build` turns a compiled artifact into a static Linux x86-64 executable
that runs its first root (the object's entry symbol) on decimal arguments
and prints the result (`X86.Exe.writeChecked`; the shell's behaviour is in
`X86/Exe/Code.lean`, the layout and the driver contract it keeps in
`X86/Exe/Layout.lean`, the file in `X86/Exe/Write.lean`).

**The fragment executables run.** A root whose parameters are all `Nat` and
at most five (`CompileClaim.rootParamsAllNat`, the claims' own test), level
monomorphic, whose result is a `Nat` or a constructor without fields of an
inductive whose constructors all have none, `Bool` among them
(`CompileClaim.isImmortalViewType`: the shapes the shell renders, as `n` and
`#k`), on any of the three policies. Refused, each with its own code:

* `exe.params`: a parameter that is not a `Nat` (a proof, an `Empty`, a
  structure), or a level-polymorphic root;
* `exe.result`: a result the shell cannot render: a constructor tree (the
  plain-RC route's results), or a type with no readback type;
* `exe.layout`: a stack or region outside the driver contract;
* `exe.write`: the writer or its check refused (it should not).

The C driver (`fixtures/x86/runtime_driver.c`) also runs roots outside this
fragment: constructor-tree results (its C decoder renders them), roots whose
parameters are not `Nat` (it passes any word), fewer arguments than
parameters (it passes zero), several roots of one object, one input line
after another in one process (with a fresh `cx_init` for each), regions
under 4 KiB (`cx_init` refuses them), timing and a dump of the object area.
-/

namespace IxCC.Exe

open IxCC.Recheck

def err (code message : String) : Err := { stage := .exe, code, message }

/-- The root an executable of `a` runs, and how its result is rendered. -/
def fragment (a : Artifact) : Except Err (Root × X86.Exe.ResultKind) := do
  let some root := a.roots.head? | throw (err "exe.root" "the program has no root")
  unless root.params ≤ maxParams do
    throw (err "exe.params" s!"root {root.name} takes {root.params} parameters; an executable passes at most {maxParams}")
  unless CompileClaim.rootParamsAllNat a.src root do
    throw (err "exe.params" s!"root {root.name} has a parameter that is not a Nat or is level-polymorphic; \
      an executable passes decimal natural numbers")
  match root.ty with
  | some (_, .nat) => pure (root, .nat)
  | some (sig, .ind i) =>
    if CompileClaim.isImmortalViewType sig (.ind i) then
      pure (root, .enum ((sig.inds[i]?.map List.length).getD 0))
    else throw (err "exe.result" s!"root {root.name} returns constructors with fields; an executable \
      renders a Nat or a constructor without fields")
  | none => throw (err "exe.result" s!"root {root.name} has no readback type")

/-- The writer's input for `a`'s first root with `layout`. -/
def input (a : Artifact) (layout : X86.Exe.Layout := {}) : Except Err X86.Exe.Input := do
  let (root, result) ← fragment a
  unless layout.check do throw (err "exe.layout" X86.Exe.Error.layout.render)
  pure { object := a.object, root := root.symbol, arity := root.params, result, layout }

/-- Build and check the executable of `a`'s first root with `layout`. -/
def build (a : Artifact) (layout : X86.Exe.Layout := {}) :
    Except Err ((i : X86.Exe.Input) × X86.Exe.Certified i) := do
  let i ← input a layout
  match X86.Exe.writeChecked i with
  | .ok c => pure ⟨i, c⟩
  | .error e => throw (err "exe.write" e.render)

end IxCC.Exe
