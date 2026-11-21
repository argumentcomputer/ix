import IxVMRefinement.Endpoint.ComposedResidual
import IxVMRefinement.Ingress.Decode
import IxVMRefinement.Claim.RefSafety
import Lean
import Std.Data.HashSet

/-! # The proof closure of the endpoint theorem, audited at the kernel level

`IxVM.Refinement.Endpoint.circuitComposed` is checked here against the environment the kernel
accepted, not against source text. The check walks every constant the theorem reaches,
through types, definition values, theorem values (proofs), constructors and recursor rules,
and fails the build unless:

* the theorem's type is exactly the public statement `IxVM.Consistency.CircuitComposed.{u}`
  with no hypothesis;
* the only axioms reached are `propext`, `Classical.choice` and `Quot.sound`;
* no constant of a trust escape is reached: `sorryAx`, `Lean.ofReduceBool`,
  `Lean.ofReduceNat`, `Lean.trustCompiler`, and the compiler-evaluation hooks
  `Lean.reduceBool` and `Lean.reduceNat` behind `native_decide`;
* no unsafe constant is reached.

It also reports the size of the closure and the constants in it that carry
`@[implemented_by]` or `@[extern]` outside the Lean core library (`Init`, `Std`, `Lean`).
Such attributes change compiled code only; the kernel checks proofs against the
definitions themselves, so they are reported for review, not refused. -/

namespace IxVM.Refinement.ClosureAudit

open Lean Elab Command

/-- The constants a constant names, its proof included. -/
def allDeps (ci : ConstantInfo) : Array Name :=
  let ofExprs (es : List Expr) : Array Name :=
    es.foldl (fun acc e => acc ++ e.getUsedConstants) #[]
  match ci with
  | .axiomInfo v => ofExprs [v.type]
  | .defnInfo v => ofExprs [v.type, v.value] ++ v.all.toArray
  | .thmInfo v => ofExprs [v.type, v.value] ++ v.all.toArray
  | .opaqueInfo v => ofExprs [v.type, v.value] ++ v.all.toArray
  | .quotInfo v => ofExprs [v.type]
  | .inductInfo v => ofExprs [v.type] ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => ofExprs [v.type] ++ #[v.induct]
  | .recInfo v =>
    ofExprs (v.type :: v.rules.map (·.rhs)) ++ v.all.toArray ++ (v.rules.map (·.ctor)).toArray

/-- Every constant reachable from `root`, proofs included. -/
def proofClosure (env : Environment) (root : Name) : Except String (Array ConstantInfo) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  let mut out : Array ConstantInfo := #[]
  seen := seen.insert root
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    let some ci := env.find? n | throw s!"unknown constant {n}"
    out := out.push ci
    for d in allDeps ci do
      unless seen.contains d do
        seen := seen.insert d
        todo := todo.push d
  return out

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def escapes : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler, ``Lean.reduceBool,
   ``Lean.reduceNat]

def isUnsafeConst : ConstantInfo → Bool
  | .axiomInfo v => v.isUnsafe
  | .defnInfo v => v.safety == .unsafe
  | .opaqueInfo v => v.isUnsafe
  | .inductInfo v => v.isUnsafe
  | .ctorInfo v => v.isUnsafe
  | .recInfo v => v.isUnsafe
  | _ => false

elab "#audit_proof_closure" : command => do
  let env ← getEnv
  let root := ``IxVM.Refinement.Endpoint.circuitComposed
  let some rootCi := env.find? root | throwError "no constant {root}"
  let expected := mkConst ``IxVM.Consistency.CircuitComposed (rootCi.levelParams.map mkLevelParam)
  unless rootCi.levelParams.length == 1 && rootCi.type == expected do
    throwError "the type of {root} is not the public statement: {rootCi.type}"
  unless (rootCi matches .thmInfo _) do throwError "{root} is not a theorem"
  let cis ← match proofClosure env root with
    | .ok cs => pure cs
    | .error e => throwError "proof closure: {e}"
  let mods := env.allImportedModuleNames
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => mods[i]?.getD .anonymous
    | none => .anonymous
  let isCore (m : Name) : Bool :=
    m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean
  let mut problems : Array String := #[]
  let mut axs : Array Name := #[]
  let mut unsafeCount := 0
  let mut partialCount := 0
  let mut thms := 0
  let mut defs := 0
  let mut hooks : Array String := #[]
  let mut coreHooks := 0
  for ci in cis do
    if (ci matches .axiomInfo _) then axs := axs.push ci.name
    if (ci matches .thmInfo _) then thms := thms + 1
    if (ci matches .defnInfo _) then defs := defs + 1
    if escapes.contains ci.name then problems := problems.push s!"trust escape reached: {ci.name}"
    if isUnsafeConst ci then
      unsafeCount := unsafeCount + 1
      problems := problems.push s!"unsafe constant reached: {ci.name}"
    if let .defnInfo v := ci then
      if v.safety == .partial then partialCount := partialCount + 1
    let impl := Compiler.getImplementedBy? env ci.name
    let ext := isExtern env ci.name
    if impl.isSome || ext then
      if isCore (modOf ci.name) then coreHooks := coreHooks + 1
      else
        let extTxt := if ext then " @[extern]" else ""
        let implTxt := match impl with
          | some i => " @[implemented_by " ++ toString i ++ "]"
          | none => ""
        hooks := hooks.push (toString ci.name ++ " (" ++ toString (modOf ci.name) ++ ")" ++
          extTxt ++ implTxt)
  for a in axs do
    unless standardAxioms.contains a do problems := problems.push s!"axiom reached: {a}"
  let axsSorted := (axs.map toString).qsort (· < ·)
  logInfo m!"proof closure of {root}: {cis.size} constants ({thms} theorems, {defs} definitions, {partialCount} partial, {unsafeCount} unsafe); axioms {axsSorted.toList}; {coreHooks} Lean-core constants with @[extern]/@[implemented_by]; {hooks.size} outside the core library: {(hooks.qsort (· < ·)).toList}"
  unless problems.isEmpty do
    throwError "proof closure audit failed:\n{"\n".intercalate problems.toList}"

#audit_proof_closure

end IxVM.Refinement.ClosureAudit

/-! ## Compile-time statement pins for core ingress and reference-safety specs -/

example {bytes : List UInt8} {i : Nat}
    {stream r : Aiur.SourceValue IxVM.F} {h h' : Aiur.Heap IxVM.F}
    {cs : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    (rep : Aiur.Library.Bytes.RepByteStream IxVM.Refinement.byteStreamEnum h (bytes.drop i) stream)
    (ev : Aiur.Generic.SourceSemantics.ObsFn IxVM.Refinement.Obs.W
      "IxonDeserialize::get_constant" [stream] h r h' cs) :
    Aiur.Heap.Extends h h' ∧
    ∃ (c : Ixon.Constant) (n : Nat) (cVal restPtr : Aiur.SourceValue IxVM.F),
      Ixon.getConstant { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok c { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [cVal, restPtr] ∧
      c.info.maxLvls < Ixon.maxLevelCount ∧
      IxVM.Refinement.Ingress.infoLvlsLt 4294967296 c.info ∧
      IxVM.Refinement.Ingress.BinderBlocksParamsLt c.info.maxLvls c.binders ∧
      IxVM.Refinement.Ingress.BinderBlocksParamsLt 4294967296 c.binders ∧
      IxVM.Refinement.Ingress.ConstantTablesValid c ∧
      IxVM.Refinement.Ingress.RepConstant h' c cVal ∧
      Aiur.Library.Bytes.RepByteStream IxVM.Refinement.byteStreamEnum h' (bytes.drop (i + n)) restPtr :=
  IxVM.Refinement.Ingress.get_constant_spec rep ev

example {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    (hS : IxVM.Refinement.LoadedReads.RunStore calls E₀) (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rc rp used r : Aiur.SourceValue IxVM.F}
      {h h' : Aiur.Heap IxVM.F} {cs : List (Aiur.Generic.SourceSemantics.Call IxVM.F)},
      i + refs.length < 8589934592 →
      IxVM.Refinement.Claim.RCLimRep t bAddr lim h rc →
      Aiur.Library.List.RepList IxVM.Refinement.Obs.Names.«Lists::Node<&[Field; 32]>»
        IxVM.Refinement.Claim.RepAddrElem h refs rp →
      IxVM.Refinement.Claim.RepSortedIdxFrom h idxs i used →
      Aiur.Generic.SourceSemantics.ObsFn IxVM.Refinement.Obs.W "KernelClaim::assert_safe_used_refs"
        [rc, rp, used, .field (i : IxVM.F), .construct IxVM.Refinement.Core.addrMapEnum "Nil" []]
        h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs →
        ¬ IxVM.Refinement.Claim.CoveredAt t lim refs[j] →
        IxVM.Refinement.Claim.SourceSafe E₀ refs[j] :=
  IxVM.Refinement.Claim.assert_safe_used_refs_spec hS refs

example {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hS : IxVM.Refinement.LoadedReads.RunStore calls E₀)
    (hH : IxVM.Refinement.LoadedReads.HashedRecordsStored calls E₀)
    (hc : IxVM.Consistency.recordOf E₀ a = some c)
    (hsafe : IxVM.Refinement.Claim.SourceSafe E₀ a)
    (hg : IxVM.Refinement.Claim.RecordRefsIn calls t bAddr lim a c) :
    ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      ¬ IxVM.Refinement.Claim.CoveredAt t lim x → IxVM.Refinement.Claim.SourceSafe E₀ x :=
  hg.safe hS hH hc hsafe
