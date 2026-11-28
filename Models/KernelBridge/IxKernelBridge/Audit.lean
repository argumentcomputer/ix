import Lean.Elab.Command
import Lean.Util.FoldConsts
import IxKernelBridge.NatBridge
import IxKernelBridge.Examples
import IxKernelBridge.KernelFront

/-!
# Checked dependency and axiom audit of `IxKernelBridge` (`IxKernelBridge.Audit`)

1. Traverses declaration types, bodies and constructor fields across the transitive
   constant closure of the simulation lemma, its compositions and the examples below, and
   fails unless each depends on exactly the three standard Lean axioms (`propext`,
   `Classical.choice`, `Quot.sound`).
2. Guards `#print axioms` on every Layer 1, Layer 2 and Layer 3 theorem and on every theorem
   of `IxKernelBridge.Examples` and `IxKernelBridge.KernelFront`.
   `checkDecls_verifyBytes_immortal_denotes_nat` rests on the same three as
   `IxCC.CompileClaim.verifyBytes_immortal_sound`, every address IxCC computes being pure
   BLAKE3; `ble_premise_false` and `pow_premise_false` use only `propext` and `Quot.sound`.

`lake run check-kernel-bridge` (the root lakefile) builds this module and compares the set
of fenced theorems with its recorded inventory, so a fence cannot disappear unnoticed.
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

/-- Theorems that must depend on exactly the three standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`): the simulation lemma, its compositions (the byte-level
one included), and the instances and per-operation facts of `IxKernelBridge.Examples`
that use all three. -/
def standardRoots : List Name :=
  [ ``IxKernelBridge.srcRun_to_red
  , ``IxKernelBridge.red_to_denotes_nat
  , ``IxKernelBridge.infer_red_to_denotes_nat
  , ``IxKernelBridge.srcRun_to_denotes_nat
  , ``IxKernelBridge.srcRun_infer_to_denotes_nat
  , ``IxKernelBridge.checkDecls_srcRun_denotes_nat
  , ``IxKernelBridge.checkDecls_recheck_x86_denotes_nat
  , ``IxKernelBridge.checkDecls_verifyBytes_immortal_denotes_nat
  , ``IxKernelBridge.Examples.add_premise
  , ``IxKernelBridge.Examples.sub_premise
  , ``IxKernelBridge.Examples.mul_premise
  , ``IxKernelBridge.Examples.div_premise
  , ``IxKernelBridge.Examples.mod_premise
  , ``IxKernelBridge.Examples.gcd_premise
  , ``IxKernelBridge.Examples.land_premise
  , ``IxKernelBridge.Examples.lor_premise
  , ``IxKernelBridge.Examples.xor_premise
  , ``IxKernelBridge.Examples.shiftLeft_premise
  , ``IxKernelBridge.Examples.shiftRight_premise
  , ``IxKernelBridge.Examples.beq_premise_false
  , ``IxKernelBridge.Examples.id_bridge
  , ``IxKernelBridge.Examples.succ_bridge
  , ``IxKernelBridge.Examples.add_bridge
  , ``IxKernelBridge.Examples.addLit_bridge
  , ``IxKernelBridge.Examples.addLit_concrete
  , ``IxKernelBridge.KernelFront.infer_derives
  , ``IxKernelBridge.KernelFront.whnf_derives
  , ``IxKernelBridge.KernelFront.annotate_runs
  , ``IxKernelBridge.KernelFront.classifyTerm_derivations
  , ``IxKernelBridge.KernelFront.classifyTerm_sound
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

/-! ## Layers 1 to 3 -/

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

/-- info: 'IxKernelBridge.checkDecls_verifyBytes_immortal_denotes_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.checkDecls_verifyBytes_immortal_denotes_nat

/-! ## `IxKernelBridge.Examples` -/

/-- info: 'IxKernelBridge.Examples.add_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.add_premise

/-- info: 'IxKernelBridge.Examples.sub_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.sub_premise

/-- info: 'IxKernelBridge.Examples.mul_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.mul_premise

/-- info: 'IxKernelBridge.Examples.div_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.div_premise

/-- info: 'IxKernelBridge.Examples.mod_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.mod_premise

/-- info: 'IxKernelBridge.Examples.gcd_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.gcd_premise

/-- info: 'IxKernelBridge.Examples.land_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.land_premise

/-- info: 'IxKernelBridge.Examples.lor_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.lor_premise

/-- info: 'IxKernelBridge.Examples.xor_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.xor_premise

/-- info: 'IxKernelBridge.Examples.shiftLeft_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.shiftLeft_premise

/-- info: 'IxKernelBridge.Examples.shiftRight_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.shiftRight_premise

/-- info: 'IxKernelBridge.Examples.beq_premise_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.beq_premise_false

/-- info: 'IxKernelBridge.Examples.ble_premise_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.ble_premise_false

/-- info: 'IxKernelBridge.Examples.pow_premise_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.pow_premise_false

/-- info: 'IxKernelBridge.Examples.id_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.id_bridge

/-- info: 'IxKernelBridge.Examples.succ_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.succ_bridge

/-- info: 'IxKernelBridge.Examples.add_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.add_bridge

/-- info: 'IxKernelBridge.Examples.addLit_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.addLit_bridge

/-- info: 'IxKernelBridge.Examples.addLit_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.Examples.addLit_concrete

/-! ## `IxKernelBridge.KernelFront` -/

/-- info: 'IxKernelBridge.KernelFront.infer_derives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.KernelFront.infer_derives

/-- info: 'IxKernelBridge.KernelFront.whnf_derives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.KernelFront.whnf_derives

/-- info: 'IxKernelBridge.KernelFront.annotate_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.KernelFront.annotate_runs

/-- info: 'IxKernelBridge.KernelFront.classifyTerm_derivations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.KernelFront.classifyTerm_derivations

/-- info: 'IxKernelBridge.KernelFront.classifyTerm_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxKernelBridge.KernelFront.classifyTerm_sound

end IxKernelBridge.Audit
