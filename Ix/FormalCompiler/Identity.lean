import Lean
import Blake3.Pure

/-!
`compiler_identity% [roots] [prefixes]` elaborates to the identity of the
code reachable from `roots`, plus every constant of a module whose name
starts with one of `prefixes` (the frontend's syntax and parser
registrations, which code reaches by category rather than by reference).

The walk follows types, values, constructors, recursors and
`@[implemented_by]` targets, and stops at the Lean toolchain (`Init`,
`Std`, `Lean`, `Lake`), whose version is hashed instead. Each constant
contributes its name and the structural hashes of its type and value, in
name order; the identity is the BLAKE3 digest of that sequence, as a
lowercase hex string literal. A module that changes any reachable constant therefore
changes the identity, and since the term depends on those modules, Lake
recompiles it whenever they change.
-/

namespace Ix.FormalCompiler.Identity
open Lean Elab Term Meta

private def toolchain : List Name := [`Init, `Std, `Lean, `Lake]

private def outside (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => toolchain.contains (env.header.moduleNames[idx.toNat]!).getRoot
  | none => false

private def edges (env : Environment) (c : ConstantInfo) : Array Name := Id.run do
  let mut out := c.type.getUsedConstants
  match c with
  | .defnInfo v => out := out ++ v.value.getUsedConstants
  | .thmInfo v => out := out ++ v.value.getUsedConstants
  | .opaqueInfo v => out := out ++ v.value.getUsedConstants
  | .inductInfo v => out := out ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for rule in v.rules do out := out ++ rule.rhs.getUsedConstants
  | _ => pure ()
  if let some target := Compiler.getImplementedBy? env c.name then out := out.push target
  return out

private def valueHash : ConstantInfo → UInt64
  | .defnInfo v => v.value.hash
  | .thmInfo v => v.value.hash
  | .opaqueInfo v => v.value.hash
  | .recInfo v => v.rules.foldl (fun h r => mixHash h r.rhs.hash) 0
  | .inductInfo v => hash v.ctors
  | .ctorInfo v => mixHash (hash v.induct) (hash v.cidx)
  | _ => 0

private def pushWord (b : ByteArray) (w : UInt64) : ByteArray := Id.run do
  let mut b := b
  for i in [0:8] do b := b.push (w >>> (8 * i).toUInt64).toUInt8
  return b

def identity (env : Environment) (roots : Array Name) (prefixes : Array Name) : String := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if prefixes.any (·.isPrefixOf m) then stack := stack.push n
  let mut found : Array ConstantInfo := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n || outside env n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    found := found.push c
    stack := stack ++ edges env c
  let sorted := found.qsort (fun a b => a.name.quickLt b.name)
  let mut bytes := s!"ix-formal-compiler/1 {Lean.versionString} {Lean.githash}".toUTF8
  for c in sorted do
    bytes := bytes ++ c.name.toString.toUTF8 |>.push 0
    bytes := pushWord (pushWord bytes c.type.hash) (valueHash c)
  let digest := (Blake3.Pure.hash bytes).val
  let digit (n : UInt8) : Char := "0123456789abcdef".toList[n.toNat]!
  return digest.foldl (init := "") fun acc b => (acc.push (digit (b >>> 4))).push (digit (b &&& 15))

syntax (name := compilerIdentity) "compiler_identity% " "[" ident,* "]" "[" ident,* "]" : term

@[term_elab compilerIdentity] def elabCompilerIdentity : TermElab := fun stx _ => do
  let roots ← stx[2].getSepArgs.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
  let prefixes := stx[5].getSepArgs.map (·.getId)
  let digest := identity (← getEnv) roots prefixes
  return toExpr digest

end Ix.FormalCompiler.Identity
