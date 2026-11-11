import IxCC.X86.Exe.Validate
import IxCC.X86.Exe.Machine
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

The native suites' test executables (`IxCCTests.Exe.TestShell`) also run
roots outside this fragment: constructor-tree results (the host reads them
back), roots whose parameters are not `Nat` (it passes any word), fewer
arguments than parameters (it passes zero), several roots of one object, one input line
after another in one process (with a fresh `cx_init` for each), regions
under 4 KiB (`cx_init` refuses them), timing and a dump of the object area.

**Numeric state machines** (`buildMachine`, `--exe FILE --machine`): the
first root is a step `Nat → Nat → Nat` of a state and an event whose result
packs the next state and a request (`IxCC/Exe/Machine.lean`), run by the
generic shell of `IxCC/X86/Exe/Machine.lean`, which parses and renders
nothing. Refused: `exe.machine` (a first root of another shape),
`exe.layout`, `exe.write`.
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


/-! ## Numeric state machines (`--machine`) -/

/-- The root a machine executable runs: the first, of exactly two `Nat`
parameters (a state and an event; declared and at Cfg) and a `Nat` result
(the next state and a request, `IxCC/Exe/Machine.lean`); else
`exe.machine`. -/
def machine (a : Artifact) : Except Err Root := do
  let some root := a.roots.head? | throw (err "exe.root" "the program has no root")
  unless root.params == 2 && CompileClaim.rootParamsAllNat a.src root do
    throw (err "exe.machine" s!"root {root.name} is not a numeric state machine: its step takes two Nat \
      parameters, a state and an event")
  match root.ty with
  | some (_, .nat) => pure root
  | _ => throw (err "exe.machine" s!"root {root.name} is not a numeric state machine: its step returns a Nat, \
      the next state and a request")

/-- Build and check the machine executable of `a`'s first root with layout `L`. -/
def buildMachine (a : Artifact) (L : X86.Exe.Machine.Layout := {}) :
    Except Err ((root : Root) × X86.Exe.Machine.Certified L root.symbol a.object) := do
  let root ← machine a
  unless L.check do throw (err "exe.layout" X86.Exe.Error.layout.render)
  match X86.Exe.Machine.writeChecked L root.symbol a.object with
  | .ok c => pure ⟨root, c⟩
  | .error e => throw (err "exe.write" e.render)

end IxCC.Exe
