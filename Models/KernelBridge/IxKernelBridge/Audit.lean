import Lean.Elab.Command
import Lean.Util.FoldConsts
import IxKernelBridge.NatBridge

/-!
# Checked Dependency and Axiom Audit of `IxKernelBridge` (`IxKernelBridge.Audit`)

1. Traverses declaration types, bodies, and constructor fields directly across the
   transitive constant closure of the core kernel-bridge adequacy theorems to verify
   that they depend only on the three standard Lean axioms (`propext`,
   `Classical.choice`, `Quot.sound`).
2. Guards `#print axioms` on every Layer 1, Layer 2, and Layer 3 theorem.
-/

namespace IxKernelBridge.Audit

open Lean Elab Command

private def directConstants (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ match info with
  | .thmInfo value => value.value.getUsedConstants
  | .defnInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | .inductInfo value => value.ctors.toArray
  | _ => #[]

private partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closure env rest seen
    else match env.checked.get.find? name with
    | some info => closure env ((directConstants info).toList ++ rest) (seen.insert name)
    | none => closure env rest (seen.insert name)

/-- Core kernel-bridge adequacy theorems that must depend only on the three
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). -/
def standardRoots : List Name :=
  [ ``IxKernelBridge.srcRun_to_red
  , ``IxKernelBridge.red_to_denotes_nat
  , ``IxKernelBridge.infer_red_to_denotes_nat
  , ``IxKernelBridge.srcRun_to_denotes_nat
  , ``IxKernelBridge.srcRun_infer_to_denotes_nat
  , ``IxKernelBridge.checkDecls_srcRun_denotes_nat
  , ``IxKernelBridge.checkDecls_recheck_x86_denotes_nat
  ]

run_cmd do
  let env ← getEnv
  for root in standardRoots do
    unless env.contains root do throwError m!"required root is missing: {root}"
    let dependencies := closure env [root]
    let actual := dependencies.toList.toArray.filter fun name =>
      match env.checked.get.find? name with
      | some (.axiomInfo _) => true
      | _ => false
    let expected := #[``propext, ``Classical.choice, ``Quot.sound]
    unless actual.qsort Name.lt == expected.qsort Name.lt do
      throwError m!"kernel-bridge axiom boundary changed at {root}:\n{actual.qsort Name.lt}"

/-- info: 'IxKernelBridge.srcRun_to_red' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.srcRun_to_red

/-- info: 'IxKernelBridge.red_to_denotes_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.red_to_denotes_nat

/-- info: 'IxKernelBridge.infer_red_to_denotes_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.infer_red_to_denotes_nat

/-- info: 'IxKernelBridge.srcRun_to_denotes_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.srcRun_to_denotes_nat

/-- info: 'IxKernelBridge.srcRun_infer_to_denotes_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.srcRun_infer_to_denotes_nat

/-- info: 'IxKernelBridge.checkDecls_srcRun_denotes_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.checkDecls_srcRun_denotes_nat

/-- info: 'IxKernelBridge.checkDecls_recheck_x86_denotes_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.checkDecls_recheck_x86_denotes_nat

/-- info: 'IxKernelBridge.checkDecls_verifyBytes_immortal_denotes_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxKernelBridge.checkDecls_verifyBytes_immortal_denotes_nat

end IxKernelBridge.Audit
