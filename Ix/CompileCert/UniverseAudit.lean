import Ix.CompileCert.CanonUnivEmit
import IxC.Kernel.Audit.Axioms
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ImplementedByAttr

/-! # Audit of the universe canonicalization proofs

Every theorem of `Ix.CompileCert.{UniverseEval, CanonUnivMeaning,
CanonUnivSubsumption, CanonUnivPaths, CanonUnivGateOrder, CanonUnivEmit}`
that a later proof uses is a root here. Each root must exist, occur once, and
depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`
(`Ix.Kernel.Audit.collectCached`, the certified kernel's traversal of checked
types and bodies, so `sorryAx` fails it). The headline theorem is frozen with
its exact axioms in `Ix.Cert.Audit`.

The proofs are about the definitions that run: the canonicalizer's phases
carry no `@[csimp]` replacement and no `@[implemented_by]`, and are safe
definitions, which the last check enforces. -/

open Lean Elab Command

namespace Ix.CompileCert.UniverseAudit

def standard : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Fail unless every root exists, occurs once, and has every axiom of its
transitive closure in `standard`. Report the roots and their axioms. -/
def checkRoots (label : String) (roots : Array Lean.Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut seen : Lean.NameSet := {}
  let mut duplicates : Array Lean.Name := #[]
  let mut missing : Array Lean.Name := #[]
  let mut violations : Array MessageData := #[]
  let mut used : Array Lean.Name := #[]
  let mut cache : Ix.Kernel.Audit.Cache := {}
  for root in roots do
    if seen.contains root then
      duplicates := duplicates.push root
      continue
    seen := seen.insert root
    unless env.contains root do
      missing := missing.push root
      continue
    let (state, cache') := Ix.Kernel.Audit.collectCached env root cache
    cache := cache'
    for ax in state.axioms do
      unless used.contains ax do used := used.push ax
    let extra := state.axioms.filter (!standard.contains ·)
    unless extra.isEmpty do
      violations := violations.push m!"{root}: {extra}"
  unless duplicates.isEmpty do
    throwError m!"{label}: duplicate roots: {duplicates}"
  unless missing.isEmpty do
    throwError m!"{label}: required roots are missing: {missing}"
  unless violations.isEmpty do
    throwError m!"{label}: roots depend on axioms outside {standard}:\n\
      {MessageData.joinSep violations.toList "\n"}"
  logInfo m!"[universe-audit] {label}: {roots.size} roots; axioms used: {used.qsort Lean.Name.lt}"

/-- The structural equality of wire universes, which the memo proofs use. -/
def evalRoots : Array Lean.Name :=
  #[`univ_beq_iff, `lawfulUnivBEq].map (`Ix.CompileCert ++ ·)

/-- Exact evaluation of the cached normalization pass, its state invariants,
and the emission guards. -/
def meaningRoots : Array Lean.Name :=
  #[`pathCompare_eq, `pathCompare_trans, `pathCompare_lawful,
    `maxChain_eval, `addSuccs_eval, `emitGated_eval, `emitGated_absorbed,
    `addVar_eval, `norm_merge_eval, `norm_addVar_eval, `norm_addConst_supported_eval,
    `Supports.insert, `normalizeAux_mono, `normalizeImaxDispatch_mono,
    `normalizeAux_le, `normalizeImaxDispatch_le, `normalizeAux_newWithin,
    `normalizeImaxDispatch_newWithin, `SeenSound.completeAux, `SeenSound.completeDispatch,
    `call_lower, `normalizeAux_lower, `normalizeImaxDispatch_lower,
    `normalizeAux_eval, `normalizeAux_initial_eval, `normalize_selfGated,
    `subsumption_selfGated, `covered_sound, `gatesLeakFree_sound,
    `gateOrder_members, `active_gateOrder, `stripped_emission_le,
    `stripped_normalized_emission_le].map (`Ix.CompileCert.CanonUnivMeaning ++ ·)

/-- Subsumption and its composition with cached normalization. -/
def subsumptionRoots : Array Lean.Name :=
  #[`varsEval_le, `subsumeVars_le, `node_zero_le, `node_subsume_le,
    `norm_insert_le, `subsumption_le, `isSubset_sublist, `isSubset_active,
    `insert_findD_property, `subsumeVars_go_keepsResult, `subsumeVars_go_keepsBig,
    `subsumeVars_keepsBig, `subsumption_keeps_var, `offsetFold_le, `nodeOffset_le,
    `keepConst_true, `subsumption_keeps_const, `subsumption_ge,
    `subsumption_eval, `normalize_eval].map (`Ix.CompileCert.CanonUnivSubsumption ++ ·)

/-- Gate availability, path shape and the gate-order prefix laws. -/
def gateRoots : Array Lean.Name :=
  (#[`entriesEval_gt, `varsEval_gt, `constant_le_oneBound, `variable_le_oneBound,
    `spike_pos, `spike_other_le, `absorbable_of_spike, `absorbable_mono,
    `Ready.nil, `Ready.mono, `Ready.insert, `Ready.subsumption,
    `AllReady.insert, `AllReady.addConst, `AllReady.addVar, `subsumption_paths,
    `AllReady.subsumption, `Remaining.pick, `gateLoop_accepts, `Ready.gatesLeakFree,
    `normalizeAux_ready, `normalizeImaxDispatch_ready, `normalize_ready, `normalize_gatesLeakFree,
    `normalize_paths, `orderedInsert_strict, `normalize_strictPaths,
    `StrictPath.sorted, `StrictPath.nodup].map (`Ix.CompileCert.CanonUnivPaths ++ ·)) ++
  (#[`chooseGate_mem, `find_filter_kept, `chooseGate_filter, `gateLoop_order,
    `gateOrder_eq, `orderAux_mem, `orderAux_nodup, `orderAux_length_le,
    `gateOrder_nodup, `gateOrder_length_le, `orderAux_restrict, `gateOrder_restrict,
    `sorted_take_filter, `gateOrder_sorted_prefix, `normalize_prefix,
    `normalize_filtered_prefix, `consumption_context_shorter].map (`Ix.CompileCert.CanonUnivGateOrder ++ ·))

/-- Grouping, marker witnesses and complete emission. `canonUniv_eval`
quantifies over every input universe and every valuation. -/
def emissionRoots : Array Lean.Name :=
  #[`MapValue.insert_merge, `atoms_insert_eval, `groups_insert_const_eval,
    `groups_insert_atom_eval, `listLoop_covers, `arrayLoop_covers,
    `atomHome_ge, `groupAtoms_covers, `home_atom_le, `groupAtoms_le,
    `buildGroups_le, `buildGroups_covers, `buildGroups_eval, `buildGroups_goodPaths,
    `buildGroups_rootZero, `consumeMarkers_valid, `ConsumedBy.longer, `ConsumedBy.prefix,
    `collectVars_eq, `emitRow_eq, `rootLoop_eq, `emitGroups_split, `emitGroups_terms,
    `rootPass_flag, `finishEmission_ge, `finishEmission_root, `emitGroups_root_le,
    `retainedTerms_eval_le, `fullTerms_eval, `fullTerms_nonempty, `potentialTerm_eval,
    `emitGated_mono, `gated_marker_le, `gated_chain_le, `potential_bound_step,
    `potential_output_le, `emitGroups_ge, `emitGroups_le, `linearize_phases,
    `linearize_normalize_eval, `canonUniv_eval].map (`Ix.CompileCert.CanonUnivEmit ++ ·)

end Ix.CompileCert.UniverseAudit

run_cmd Ix.CompileCert.UniverseAudit.checkRoots "evaluation" Ix.CompileCert.UniverseAudit.evalRoots
run_cmd Ix.CompileCert.UniverseAudit.checkRoots "normalization" Ix.CompileCert.UniverseAudit.meaningRoots
run_cmd Ix.CompileCert.UniverseAudit.checkRoots "subsumption" Ix.CompileCert.UniverseAudit.subsumptionRoots
run_cmd Ix.CompileCert.UniverseAudit.checkRoots "gates" Ix.CompileCert.UniverseAudit.gateRoots
run_cmd Ix.CompileCert.UniverseAudit.checkRoots "emission" Ix.CompileCert.UniverseAudit.emissionRoots

/-- The runtime definitions the proofs are about carry no compiled
replacement and are safe. -/
def Ix.CompileCert.UniverseAudit.checkRuntime (label : String) (names : Array Lean.Name) :
    CommandElabM Unit := do
  let env ← getEnv
  let substitutions := (Lean.Compiler.CSimp.ext.getState env).map
  for name in names do
    unless (substitutions.find? name).isNone &&
        (Lean.Compiler.getImplementedBy? env name).isNone do
      throwError m!"{label}: unreviewed runtime substitution: {name}"
    let some (.defnInfo definition) := env.find? name
      | throwError m!"{label}: not a definition: {name}"
    unless definition.safety == .safe do
      throwError m!"{label}: not a safe definition: {name}"
  logInfo m!"[universe-audit] {label}: {names.size} safe definitions, no runtime substitution"

/-- The canonicalizer's phases. -/
def Ix.CompileCert.UniverseAudit.canonicalizer : Array Lean.Name :=
  (#[`normalizeAux, `normalizeImaxMax, `normalizeImaxImax,
    `normalizeImaxDispatch, `CNode.addVar, `CNorm.addConst, `CNorm.addVar,
    `NState.addConst, `NState.addVar, `orderedInsert, `subsumeVars,
    `subsumeVars.go, `subsumption, `normalize, `covered, `gateOrderChecked,
    `gateOrder, `gatesLeakFree, `maxChain, `linearize].map (`Ixon.CanonUniv ++ ·)) ++
      #[``Ixon.Univ.addSuccs, ``Ixon.canonUniv]

run_cmd Ix.CompileCert.UniverseAudit.checkRuntime "canonicalizer" Ix.CompileCert.UniverseAudit.canonicalizer
