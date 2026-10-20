/-
  Ix.AuxGen.LiteralSupport: the literal support a selected closure lacks, for
  the drivers' Source service only (AuxGen M3; `auxgen-m3.md` §9).

  A literal references no constant, so a selected closure (`ix compile-lean
  --local`, `--consts`, `--module`; the closure suites) can carry a `String`
  or `Nat` literal without the declarations IxC needs to type it
  (`Ix.Kernel.Reader.strLitSupportNames`, which include
  `natLitSupportNames`). The drivers' Source service then refuses every
  group with such a literal, and AuxGen falls back to `Ix.Tc` there
  (`compile-closure-whole`'s `MCasesPat` closure).

  `literalSupportFor` gives the service those declarations from the Lean
  environment the closure was taken from: the selected closure of the
  support names, minus the constants the input already has. **Generation
  side only.** The drivers hand it to the Source service, which reads it
  as a second lookup beside the input (`Ix.CompileM.DriverOptions.serviceSupport`,
  `AuxIxcOptions.serviceInput`). Nothing compiled, published or certified
  reads it: the compile input, `Ix.LeanIngress.checkSource` and everything
  `SourceAccepts` reads are unchanged.
-/
module
public import Ix.EnvScope
public import IxC.Kernel.Ixon.Reader
public section

namespace Ix.AuxGen

/-- An IxC name as a Lean name. -/
def kernelNameToLean : Ix.Kernel.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (kernelNameToLean p) s
  | .num p n => .num (kernelNameToLean p) n

/-- The Lean names of the literal support (`strLitSupportNames`, `Nat`'s
included): role keys at `.source`, spelled by their roles' Lean names. -/
def literalSupportLeanNames : List Lean.Name :=
  (Ix.Kernel.Reader.strLitSupportNames (md := .source)).filterMap fun
    | .role r => some (kernelNameToLean r.leanName)
    | .id n => some (kernelNameToLean n)
    | .aux _ _ => none

/-- **The literal support a compile input lacks**, from the Lean environment
it was taken from: the selected closure of the support declarations, minus
the constants the input already has; nothing when the input has them all. -/
def literalSupportFor (env : Lean.Environment) (input : List (Lean.Name × Lean.ConstantInfo)) :
    List (Lean.Name × Lean.ConstantInfo) :=
  let given : Lean.NameSet := input.foldl (fun s (n, _) => s.insert n) {}
  if literalSupportLeanNames.all given.contains then []
  else
    let seeds := literalSupportLeanNames.filter env.contains
    (Ix.EnvScope.collectSelectedDeps env seeds).filter fun (n, _) => !given.contains n

end Ix.AuxGen

end
