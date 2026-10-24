module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.CompileM
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.KernelError

/-! Shared address resolution, checked-query observations and per-tail state. -/
public section
namespace Ix.AuxGen
open Ix.CompileM (CompileM CompileError)

/-! ## Address resolution (provisional) -/

/-- Name→address view for the bridge. Mirrors Rust
    `resolve_lean_name_addr` (kernel ingress.rs:2133): compiled address
    (`name_to_addr`), then aux table, then the NAME HASH as a provisional
    stand-in. Provisional addresses are internally consistent within one
    bridge kenv — that is all the kernel needs. -/
structure AddrMaps where
  nameToAddr : Name → Option Address
  auxNameToAddr : Name → Option Address := fun _ => none

def AddrMaps.resolve (maps : AddrMaps) (name : Name) : Address :=
  match maps.nameToAddr name with
  | some a => a
  | none =>
    match maps.auxNameToAddr name with
    | some a => a
    | none => name.getHash

/-- The compile-env view (production callers thread `auxNameToAddr` from
    block state once orchestration lands; mirrors `stt.resolve_addr`,
    compile.rs:261-274). `primary` overlays the CURRENT block's member
    projection registrations (BlockState.blockNameToAddr) — Rust's
    `compile_mutual` inserts those into the global `name_to_addr` right
    before the aux tail runs, so the tail must see them on the
    first-hop map. -/
def AddrMaps.ofCompileEnv (cenv : Ix.CompileM.CompileEnv)
    (aux : Std.HashMap Ix.Compile.ExactKey.ExactName Address := {})
    (primary : Std.HashMap Ix.Compile.ExactKey.ExactName Address := {}) : AddrMaps where
  nameToAddr := fun n => match primary.get? n with
    | some a => some a
    | none => cenv.nameToAddr.get? n
  auxNameToAddr := fun n => aux.get? n

/-- **What AuxGen M2a's IxC arm saw in one aux tail** (`AuxKernel.ixc`):
`.below`'s level questions on the scopes routed to IxC. -/
structure IxcStats where
  /-- `getLevel` on a scope routed to IxC -/
  queries : Nat := 0
  /-- answered by IxC's fast path -/
  ixcFast : Nat := 0
  /-- answered by IxC -/
  answered : Nat := 0
  /-- refused by IxC: the query, or the scope it was asked in -/
  refused : Nat := 0
  /-- IxC scopes refused (`new`, `push`, `pop`) -/
  scopesRefused : Nat := 0
  /-- the block's own flat block installed, and refused -/
  flatInstalled : Nat := 0
  flatRefused : Nat := 0
  /-- `isDefEq?` questions on a checked scope. -/
  decisions : Nat := 0
  /-- AuxGen M3: `inferType?` and `whnf?` on a scope routed to IxC, and IxC
  answered -/
  exprQueries : Nat := 0
  exprAnswered : Nat := 0
  /-- AuxGen M3: the generated `.below` constants admitted to IxC, and refused -/
  belowAdmitted : Nat := 0
  belowRefused : Nat := 0
  /-- AuxGen T3 (M7 Q1): the Prop-level `.below` families installed for their
  recursors' generation (`AuxKernel.withFamily`), and refused -/
  familyInstalled : Nat := 0
  familyRefused : Nat := 0
  /-- AuxGen T3: 1 when the tail is an unsafe block's on the IxC arm, and 1 when
  that block is tier-installed (the oracle's block status) -/
  unsafeBlock : Nat := 0
  tier : Nat := 0
  /-- Named recursor-generator WHNF answers and their actual routes. -/
  recWhnf : Nat := 0
  recStuck : Nat := 0
  recSame : Nat := 0
  recReplayed : Nat := 0
  recBeta : Nat := 0
  recRefused : Nat := 0
  /-- `findRecTarget` fields skipped because they name no block member. -/
  recSkipped : Nat := 0
  /-- AuxGen M4: questions that needed the service (escaped the fast paths) -/
  recForced : Nat := 0
  /-- Elimination decisions asked and refused. -/
  elim : Nat := 0
  elimRefused : Nat := 0
  /-- AuxGen M4: for a block whose layout is Lean's, its canonical recursors
  equal to Lean's own, and not -/
  leanRecSame : Nat := 0
  leanRecDiffer : Nat := 0
  /-- AuxGen M4: 1 when the run-ahead asked for the block -/
  asked : Nat := 0
  /-- the first disagreements and refusals, as text -/
  samples : Array String := #[]
  deriving Inhabited

namespace IxcStats

/-- How many samples a tail keeps. -/
def cap : Nat := 4

def sample (st : IxcStats) (msg : String) : IxcStats :=
  if st.samples.size < cap then { st with samples := st.samples.push msg } else st

/-- Actual checked work, traced once per tail. -/
def line (key : Name) (st : IxcStats) : String :=
  s!"[auxgen-ixc] {key.pretty}: queries {st.queries} ixcFast {st.ixcFast} \
    answered {st.answered} refused {st.refused} \
    scopesRefused {st.scopesRefused} flat {st.flatInstalled}/{st.flatRefused} \
    decisions {st.decisions} exprQueries {st.exprQueries} exprAnswered {st.exprAnswered} \
    below {st.belowAdmitted}/{st.belowRefused} \
    recWhnf {st.recWhnf} recStuck {st.recStuck} recSame {st.recSame} recReplayed {st.recReplayed} \
    recBeta {st.recBeta} recRefused {st.recRefused} recSkipped {st.recSkipped} \
    recForced {st.recForced} elim {st.elim} elimRefused {st.elimRefused} \
    leanRecSame {st.leanRecSame} leanRecDiffer {st.leanRecDiffer} \
    family {st.familyInstalled}/{st.familyRefused} unsafe {st.unsafeBlock} tier {st.tier} \
    asked {st.asked}\
    {String.join (st.samples.toList.map fun s => s!"\n[auxgen-ixc]   {s.take 400}")}"

end IxcStats

/-- Checked generation observations, fresh for each tail. -/
structure AuxKernelCtx where
  ixcStats : IxcStats := {}
  /-- AuxGen M4c: the canonical-block check's verdict
      (`AuxKernel.checkCanonicalBlock`), when it ran; the driver records it in
      the block's state (`Ix.CompileM.BlockState.auxReport`). -/
  canonical : Option CanonicalVerdict := none
  /-- AuxGen M5: the oracle after the canonical flat block's install, when the
      check installed one; the tail admits the block's other auxiliaries over
      it (`admitGenerated`). -/
  canonicalOracle : Option AuxOracle := none
  /-- AuxGen M5: the auxiliaries the tail generated, with their kinds, and the
      verdicts on those it checked (`accepted`, `refused`, `exempt`); the
      driver records them in the block's report. -/
  generated : Array (Name × GeneratedKind) := #[]
  admitted : Array (Name × AuxVerdict) := #[]

/-- Fresh checked-generation state. -/
def AuxKernelCtx.new : AuxKernelCtx := {}

/-- Bridge monad: aux kernel state over CompileM. -/
abbrev KBridgeM := StateT AuxKernelCtx CompileM

/-- A bridge refusal crosses the compiler boundary as the compiler error it
    renders to (`AuxKernelError.toCompileError`). -/
def throwBridge (e : AuxKernelError) : KBridgeM α :=
  throw e.toCompileError

/-- Pure conversion errors cross the compiler boundary as named refusals. -/
def liftBridgeResult (result : Except AuxKernelError α) : KBridgeM α :=
  match result with
  | .ok value => pure value
  | .error e => throwBridge e

/-- Mirrors Rust `collect_const_refs` (recursor.rs:2694).

    Collect all constant names referenced in an expression, appended onto
    `out` (a work queue, NOT a set — dedup happens at the consumer's
    `seen`). Explicit stack, matching the Rust traversal order, with a
    digest-keyed visited set so structurally shared subterms are walked
    once (DAG cost, not unshared-tree cost). -/
def collectConstRefs (expr : Expr) (out : Array Name) : Array Name := Id.run do
  let mut out := out
  let mut visited : Std.HashSet Address := {}
  let mut stack : Array Expr := #[expr]
  repeat
    if let some e := stack.back? then
      stack := stack.pop
      if visited.contains e.getHash then
        continue
      visited := visited.insert e.getHash
      match e with
      | .const n _ _ => out := out.push n
      | .app f a _ =>
        stack := stack.push f
        stack := stack.push a
      | .forallE _ d b _ _ | .lam _ d b _ _ =>
        stack := stack.push d
        stack := stack.push b
      | .letE _ t v b _ _ =>
        stack := stack.push t
        stack := stack.push v
        stack := stack.push b
      | .proj name _ e' _ =>
        out := out.push name
        stack := stack.push e'
      | .mdata _ e' _ =>
        stack := stack.push e'
      | _ => pure ()
    else
      break
  return out

/-- The kernel's elimination decision for a block's original classes. -/
structure ElimDecision where
  /-- Large elimination: Lean's `elim_only_at_universe_zero`, negated. -/
  isLarge : Bool
  /-- The WHNF-peeled result sort is semantically zero. -/
  isProp : Bool
  deriving BEq, Inhabited, Repr

end Ix.AuxGen

end
