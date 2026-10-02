import Lean.Compiler.CSimpAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Ix.CompileM
import Ix.Compile.Verify.Audit.Statements

/-!
# Compiled-code replacements on the compiler's path

A `@[csimp]` theorem `@f = @g` makes compiled code call `g` wherever it calls
`f`, while every theorem keeps talking about `f`. The compiler (`Ix.CompileM`
and everything it imports) therefore runs a body that only the csimp theorem
ties to its specification, so that theorem must be checked like any other
claim: every csimp theorem declared in an `Ix` module on the compiler's
import path must be a root of the statement manifest
(`Ix.Compile.Verify.Audit.Statements.roots`), whose check fixes its axioms
exactly and rejects `sorryAx`. The theorems are read from the environment's
csimp extension, not from a hand-kept list, so a new unregistered one fails
this module.

The sharing core (`Ix.Sharing.*`) may replace a compiled body in no other
way: none of its declarations is `unsafe`, `partial`, `@[implemented_by]` or
`@[extern]`, except the items of `acceptedUnsafe`. The `_unsafe_rec`
definitions Lean generates to compile well-founded recursion are the
compiler's own translation of a checked definition, not replacements, and are
skipped.
-/

open Lean Lean.Elab.Command

namespace Ix.Compile.Verify.Audit.CompiledCode

/-- The accepted unsafe items of `Ix.Sharing.*`, by the declaration they come
from: the interner's pointer-cache key `exprPtr` (`unsafe ptrAddrUnsafe`).
Logically it is an arbitrary function of the expression; no theorem inspects
it, so every theorem holds for the address map of any run. -/
def acceptedUnsafe : Array Lean.Name := #[``Ix.Sharing.Exact.exprPtr]

/-- The modules `root` imports, transitively, and `root` itself. -/
def importClosure (env : Lean.Environment) (root : Lean.Name) : Lean.NameSet := Id.run do
  let names := env.header.moduleNames
  let mut index : Std.HashMap Lean.Name Nat := {}
  for h : i in [0:names.size] do
    index := index.insert names[i] i
  let mut seen : Lean.NameSet := {}
  let mut stack := #[root]
  while !stack.isEmpty do
    let m := stack.back!
    stack := stack.pop
    if seen.contains m then continue
    seen := seen.insert m
    if let some i := index[m]? then
      for imp in env.header.moduleData[i]!.imports do
        unless seen.contains imp.module do stack := stack.push imp.module
  return seen

def moduleOf? (env : Lean.Environment) (name : Lean.Name) : Option Lean.Name :=
  (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx.toNat]!

def checkCSimpRoots : CommandElabM Unit := do
  let env ← getEnv
  let compiler := importClosure env `Ix.CompileM
  let registered : Lean.NameSet :=
    Statements.roots.foldl (fun s a => s.insert a.root) {}
  let thms := ((Lean.Compiler.CSimp.ext.getState env).thmNames.toList.filter fun n =>
    match moduleOf? env n with
    | some mod => (`Ix).isPrefixOf mod && compiler.contains mod
    | none => false).toArray.qsort Lean.Name.lt
  let missing := thms.filter (!registered.contains ·)
  unless missing.isEmpty do
    throwError m!"{missing.size} @[csimp] theorem(s) on the compiler's import path are not \
      roots of Ix.Compile.Verify.Audit.Statements:\n\
      {String.intercalate "\n" (missing.toList.map (s!"  {·}"))}"
  logInfo m!"compiled-code audit: all {thms.size} @[csimp] theorems of Ix modules on the \
    compiler's import path are audit roots"

def checkSharingReplacements : CommandElabM Unit := do
  let env ← getEnv
  let accepted (n : Lean.Name) : Bool :=
    acceptedUnsafe.any fun a => a.isPrefixOf (privateToUserName n)
  let mut flagged : Array String := #[]
  let mut acceptedItems : Array Lean.Name := #[]
  for (name, info) in env.constants.toList do
    let some mod := moduleOf? env name | continue
    unless (`Ix.Sharing).isPrefixOf mod do continue
    let generatedRec := name.isStr && name.getString! == "_unsafe_rec" &&
      match env.find? name.getPrefix with
      | some (.defnInfo _) =>
        (Lean.Compiler.implementedByAttr.getParam? env name.getPrefix).isNone
      | _ => false
    let impl := (Lean.Compiler.implementedByAttr.getParam? env name).isSome
    let ext := Lean.isExtern env name
    let replaces := impl || ext || info.isUnsafe || (info.isPartial && !generatedRec)
    if replaces then
      if accepted name then acceptedItems := acceptedItems.push name
      else flagged := flagged.push s!"  {mod} :: {name}"
  unless flagged.isEmpty do
    throwError m!"{flagged.size} unsafe, partial, implemented_by or extern declaration(s) in \
      Ix.Sharing.* outside the accepted list:\n{String.intercalate "\n" flagged.toList}"
  let sortedAccepted := acceptedItems.qsort Lean.Name.lt
  logInfo m!"compiled-code audit: Ix.Sharing.* replaces no compiled body except the accepted \
    {sortedAccepted.size} item(s) of {acceptedUnsafe}: {sortedAccepted}"

run_cmd checkCSimpRoots
run_cmd checkSharingReplacements

end Ix.Compile.Verify.Audit.CompiledCode
