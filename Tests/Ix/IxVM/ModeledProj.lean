import Ix.Meta
import Ix.IxVM.Model
import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.ModelAdvice
import Tests.Ix.IxVM.ModeledProjDefs

/-! # Modeled structure projections: positive coverage and negative controls

Tests certified `.proj` support on 1-constructor, 0-index, never-zero-sort members of
modeled (mutual/nested) inductive blocks under `IX_AIUR_CIRCUIT_VERDICT=1`:

* **Positive fixtures**:
  - Nested-recursive 1-constructor structures (`NestedDoc`, `MyTree`, `NatTree`, `DepNested`,
    `SortPolyParam`), including `nP = 0` and `nP > 0`, `Prop` fields, `Sort u` fields,
    dependent fields, and definitional ι-reduction theorems (`rfl`).
  - Mutual-recursive 1-constructor structures (`GuardedExp` / `GuardedExprs`), both
    projection functions and nested definitional ι-reduction theorems (`rfl`).
  - Live Lean 4 core projections on nested structures (`Lean.Doc.Part.{title,content,subParts}`,
    `Lean.Language.SnapshotTree.{element,children}`, `Lean.Lsp.Ipc.CallHierarchy.{item,children}`,
    `Lean.Lsp.Ipc.ModuleHierarchy.{item,children}`).
* **Adversarial projection advice (must reject)**:
  - Swapped projection entries (`left` / `right`) on `NatTree (n : Nat)`.
  - Parameter-dependent `swap01` projection branching on `n : Nat` via `Nat.rec`.
  - Non-pure projection (`fun n t => Nat.rec _ (pm0 n t) _ Nat.zero`), whose ι-theorem holds by
    `Eq.refl` yet whose body is rejected by `KernelModeled::check_proj_pure`.
  - Truncated `projModels` array in the payload stream.
* **Disallowed `.proj` targets on modeled blocks (must reject)**:
  - 2-constructor mutual inductive (`TwoCtorMutA`).
  - 0-constructor mutual inductive (`ZeroCtorMutA`).
  - Indexed nested 1-constructor inductive (`IndexedNested`).
  - `Prop` mutual 1-constructor inductive (`PropMutA`).
  - Sort-polymorphic field depending on an earlier field (`SortPolyField.elem`).
  - Universe-polymorphic (`Sort u`, maybe-zero) mutual 1-constructor inductive.
  - Out-of-bounds field index (`idx = 3`) on `NestedDoc`. -/

namespace Tests.Ix.IxVM.ModeledProj

open IxVM.ClaimHarness IxVM.Model

private abbrev E := Ixon.Expr

private def defs (s : String) : Lean.Name :=
  s.splitOn "." |>.foldl (init := `Tests.Ix.IxVM.ModeledProjDefs) Lean.Name.mkStr

private def put (env : Ixon.Env) (c : Ixon.Constant)
    (hint : Lean.ReducibilityHints := .regular 0) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.serConstant c)
  let env := env.storeConst a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a hint }
    | _ => env
  (env, a)

private def blockOf (env : Ixon.Env) (a : Address) : IO Address := do
  let some c := env.getConst? a | throw (IO.userError s!"{a} is not stored")
  match c.info with
  | .iPrj p => pure p.block
  | .cPrj p => pure p.block
  | _ => throw (IO.userError s!"{a} is not a member of an inductive block")

private def positiveDefs : Array String := #[
  "NestedDoc.title", "NestedDoc.rank", "NestedDoc.subParts",
  "nestedDocTitleIota", "nestedDocRankIota", "nestedDocSubPartsIota",
  "MyTree.left", "MyTree.right", "MyTree.kids",
  "myTreeLeftIota", "myTreeRightIota",
  "NatTree.left", "NatTree.right", "natTreeLeftIota",
  "DepNested.idx", "DepNested.fin", "DepNested.proof", "DepNested.val", "DepNested.kids",
  "depNestedFinIota", "depNestedProofIota", "depNestedValIota",
  "SortPolyParam.elem", "SortPolyParam.kids",
  "sortPolyParamTypeIota", "sortPolyParamPropIota",
  "GuardedExp.guard", "GuardedExp.body", "GuardedExprs.binds", "GuardedExprs.gdes",
  "guardedExpGuardIota", "guardedExprsBindsIota", "guardedExpNestedProjIota"
]

private def negativeBaseDefs : Array String := #[
  "TwoCtorMutA", "ZeroCtorMutA", "IndexedNested", "PropMutA", "SortPolyField.elem"
]

private def liveLeanCoreProjs : Array Lean.Name := #[
  `Lean.Doc.Part.title,
  `Lean.Doc.Part.content,
  `Lean.Doc.Part.subParts,
  `Lean.Language.SnapshotTree.element,
  `Lean.Language.SnapshotTree.children,
  `Lean.Lsp.Ipc.CallHierarchy.item,
  `Lean.Lsp.Ipc.CallHierarchy.children,
  `Lean.Lsp.Ipc.ModuleHierarchy.item,
  `Lean.Lsp.Ipc.ModuleHierarchy.children
]

/-- Construct a hand-built definition `fun (x : ty) => x.<fieldIdx>` projecting out of `typeA`. -/
private def mkProjFn (env : Ixon.Env) (typeA retA : Address) (fieldIdx : UInt64)
    (extraRefs : Array Address := #[]) (typeArgs : Array E := #[]) : Ixon.Env × Address :=
  let dom : E := typeArgs.foldl Ixon.Expr.app (.ref 0 #[])
  let c : Ixon.Constant := ⟨.defn ⟨.defn, .safe, {}, 0,
    .all dom (.ref 1 #[]),
    .lam dom (.prj 0 fieldIdx (.var 0))⟩,
    #[], #[typeA, retA] ++ extraRefs, #[],
    #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
  put env c

/-- Construct a hand-built 1-constructor `Sort u` (maybe-zero sort) mutual inductive pair
and a projection on its first member. -/
private def sortPolyMutProjCase : Except String Case := do
  let env ← withRoleTable {} (← Ix.Kernel.Reader.defaultTableBytes)
  let table ← Ix.Kernel.Reader.defaultTable
  let some natA := table.addressOf? .nat | throw "default table lacks Nat"
  let ctor0 (typ : E) : Ixon.Constructor :=
    { isUnsafe := false, lvls := 1, cidx := 0, params := 0, fields := 1, typ }
  -- SortPolyA.{u} : Sort u | mk : SortPolyB.{u} → SortPolyA.{u}
  -- SortPolyB.{u} : Sort u | mk : SortPolyA.{u} → SortPolyB.{u}
  let block : Ixon.Constant := ⟨.muts #[
      .indc ⟨false, 1, 0, 0, .sort 0, #[ctor0 (.all (.recur 1 #[0]) (.recur 0 #[0]))]⟩,
      .indc ⟨false, 1, 0, 0, .sort 0, #[ctor0 (.all (.recur 0 #[0]) (.recur 1 #[0]))]⟩],
    #[], #[], #[.var 0],
    #[⟨false, 1, 0, #[.ifAllZero #[0] {}]⟩, ⟨false, 3, 0, #[.ifAllZero #[0] {}]⟩]⟩
  let (env, b) := put env block
  let (env, aA) := put env ⟨.iPrj ⟨0, b⟩, #[], #[], #[], #[]⟩
  let (env, bA) := put env ⟨.iPrj ⟨1, b⟩, #[], #[], #[], #[]⟩
  let (env, _) := put env ⟨.cPrj ⟨0, 0, b⟩, #[], #[], #[], #[]⟩
  let (env, _) := put env ⟨.cPrj ⟨1, 0, b⟩, #[], #[], #[], #[]⟩
  -- f.{u} : SortPolyA.{u} → SortPolyB.{u} := fun x => x.1
  let (env, fnA) := put env ⟨.defn ⟨.defn, .safe, {}, 1,
    .all (.ref 0 #[0]) (.ref 1 #[0]),
    .lam (.ref 0 #[0]) (.prj 0 0 (.var 0))⟩,
    #[], #[aA, bA], #[.var 0],
    #[⟨false, 0, 0, #[.ifAllZero #[0] {}]⟩, ⟨false, 1, 0, #[.ifAllZero #[0] {}]⟩]⟩
  let _ := natA
  let ctx ← Ix.ClaimContext.ofEnv env true
  Case.ofClaim "modeled-proj negative: Sort u (maybe-zero) mutual 1-ctor inductive"
    env (.check ctx fnA none) (accept := false)

/-- Rewrite every occurrence of `oldA` to `newA` inside a constant's `refs` table. -/
private def replaceRef (c : Ixon.Constant) (oldA newA : Address) : Ixon.Constant :=
  { c with refs := c.refs.map fun r => if r == oldA then newA else r }

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let localNames : Array Lean.Name :=
    (positiveDefs ++ negativeBaseDefs).map defs ++ #[``Nat, ``Nat.rec, ``Nat.zero]
  let missing := localNames.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-modeled-proj] missing fixture constants: {missing}"
    return 1
  let livePresent := liveLeanCoreProjs.filter (leanEnv.constants.contains ·)
  if livePresent.isEmpty then
    IO.eprintln "[ixvm-modeled-proj] expected live Lean core projections in environment"
    return 1
  let env0 ← loadSharedIxonEnv (localNames ++ livePresent) leanEnv
  let bare := { ModelAdvice.withoutModels env0 with modelsAttached := false }
  let (env, rep) ← IO.ofExcept (generateReport bare)
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let mut cases : Array Builder := #[]

  -- 1. Positive fixture cases (nested, mutual, parameterized, Prop/Sort-u/dependent fields, ι)
  for s in positiveDefs do
    let a ← lookupAddr env (defs s)
    cases := cases.push fun _ =>
      Case.ofClaim s!"modeled-proj positive: {s}" env (.check ctx a none) (accept := true)

  -- 2. Live real-world Lean 4 core projections
  for nm in livePresent do
    let a ← lookupAddr env nm
    cases := cases.push fun _ =>
      Case.ofClaim s!"modeled-proj live core: {nm}" env (.check ctx a none) (accept := true)

  -- 3. Adversarial projection advice attacks on `NatTree (n : Nat)` (using basis `Nat.rec`)
  let natTreeA ← lookupAddr env (defs "NatTree")
  let natTreeLeftA ← lookupAddr env (defs "NatTree.left")
  let natTreeB ← blockOf env natTreeA
  let some (_, advTree) := rep.advice.find? (·.1 == natTreeB)
    | throw (IO.userError "NatTree has no model advice")
  let pTree := advTree.layout
  if pTree.projModels.size < 3 then
    throw (IO.userError s!"NatTree expected 3 projModels entries, got {pTree.projModels.size}")
  let (pm0, pi0) := pTree.projModels[0]!
  let (pm1, pi1) := pTree.projModels[1]!
  let variant (bytes : ByteArray) (extra : Array (Address × Ixon.Constant) := #[]) : Ixon.Env :=
    { env with
      models := env.models.insert natTreeB bytes
      modelRecords := extra.foldl (fun m (a, c) => m.insert a c) env.modelRecords
      modelHints := extra.foldl (fun m (a, c) => match c.info with
        | .defn _ => m.insert a (.regular 0)
        | _ => m) env.modelHints
      modelDeps := env.modelDeps.insert natTreeB ((env.modelDeps.getD natTreeB #[]) ++ extra.map (·.1)) }

  -- Attack A: swap projModels[0] and projModels[1]
  let swappedProjs := pTree.projModels.set! 0 (pm1, pi1) |>.set! 1 (pm0, pi0)
  let envSwapped := variant { pTree with projModels := swappedProjs }.ser
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj attack: swapped left/right projModels on NatTree"
      envSwapped (.check ctx natTreeLeftA none) (accept := false)
      (rejectsWith := some "modeled projection")

  -- Attack B: parameter-dependent swap01 (`fun n t => Nat.rec (fun _ => Nat) (pm0 n t) (fun _ _ => pm1 n t) n`)
  let some pm0C := env.modelRecords[pm0]? | throw (IO.userError "NatTree pm0 record missing")
  let .defn pm0D := pm0C.info | throw (IO.userError "NatTree pm0 is not a defn")
  let natRecA ← lookupAddr env ``Nat.rec
  let natA ← lookupAddr env ``Nat
  let natZeroA ← lookupAddr env ``Nat.zero
  let rNatRec : UInt64 := pm0C.refs.size.toUInt64
  let rNat : UInt64 := rNatRec + 1
  let rZero : UInt64 := rNatRec + 2
  let rPm0 : UInt64 := rNatRec + 3
  let rPm1 : UInt64 := rNatRec + 4
  let uOne : UInt64 := pm0C.univs.size.toUInt64
  let pm0DomT : E := match pm0D.typ with | .all _ (.all d _) => d | _ => .ref rNat #[]
  let pm0TypBinders := pm0C.binders.filter fun b => !b.shared && b.index == 0
  let pm0SharedBinders := pm0C.binders.filter (·.shared)
  let swap01Body : E :=
    .lam (.ref rNat #[])
      (.lam pm0DomT
        (.app (.app (.app (.app (.ref rNatRec #[uOne])
            (.lam (.ref rNat #[]) (.ref rNat #[])))
          (.app (.app (.ref rPm0 #[]) (.var 1)) (.var 0)))
          (.lam (.ref rNat #[]) (.lam (.ref rNat #[])
            (.app (.app (.ref rPm1 #[]) (.var 3)) (.var 2)))))
          (.var 1)))
  let swap01C : Ixon.Constant := {
    info := .defn { pm0D with value := swap01Body }
    sharing := pm0C.sharing
    refs := pm0C.refs ++ #[natRecA, natA, natZeroA, pm0, pm1]
    univs := pm0C.univs.push (.succ .zero)
    binders := pm0TypBinders ++
      #[⟨false, 1, 0, #[.never {}, .never {}, .never {}, .never {}, .never {}]⟩] ++
      pm0SharedBinders
  }
  let swap01A := Address.blake3 (Ixon.serConstant swap01C)
  let some pi0C := env.modelRecords[pi0]? | throw (IO.userError "NatTree pi0 record missing")
  let swap01IotaC := replaceRef pi0C pm0 swap01A
  let swap01IotaA := Address.blake3 (Ixon.serConstant swap01IotaC)
  let extraWit : Array (Address × Nat × List Nat × List Nat) :=
    #[(natRecA, 0, [], []), (natA, 0, [], []), (natZeroA, 0, [], [])].filter fun w =>
      !pTree.witnesses.any (·.1 == w.1)
  let envSwap01 := variant
    { pTree with
      advice := pTree.advice ++ #[swap01A, swap01IotaA]
      witnesses := pTree.witnesses ++ extraWit
      projModels := pTree.projModels.set! 0 (swap01A, swap01IotaA) }.ser
    #[(swap01A, swap01C), (swap01IotaA, swap01IotaC)]
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj attack: parameter-dependent swap01 projection on NatTree (n : Nat)"
      envSwap01 (.check ctx natTreeLeftA none) (accept := false)
      (rejectsWith := some "inferred type is not def-eq")

  -- Attack C: impure projection (`fun n t => Nat.rec (fun _ => Nat) (pm0 n t) (fun _ _ => pm1 n t) Nat.zero`),
  -- whose iota STILL holds definitionally (`Nat.rec _ (pm0 n (mk ...)) _ 0 ≡ pm0 n (mk ...) ≡ left`)
  -- so it passes `check_proj_iota` and specifically exercises `KernelModeled::check_proj_pure`
  let impureBody : E :=
    .lam (.ref rNat #[])
      (.lam pm0DomT
        (.app (.app (.app (.app (.ref rNatRec #[uOne])
            (.lam (.ref rNat #[]) (.ref rNat #[])))
          (.app (.app (.ref rPm0 #[]) (.var 1)) (.var 0)))
          (.lam (.ref rNat #[]) (.lam (.ref rNat #[])
            (.app (.app (.ref rPm1 #[]) (.var 3)) (.var 2)))))
          (.ref rZero #[])))
  let impureC : Ixon.Constant := {
    info := .defn { pm0D with value := impureBody }
    sharing := pm0C.sharing
    refs := pm0C.refs ++ #[natRecA, natA, natZeroA, pm0, pm1]
    univs := pm0C.univs.push (.succ .zero)
    binders := pm0TypBinders ++
      #[⟨false, 1, 0, #[.never {}, .never {}, .never {}, .never {}, .never {}]⟩] ++
      pm0SharedBinders
  }
  let impureA := Address.blake3 (Ixon.serConstant impureC)
  let impureIotaC := replaceRef pi0C pm0 impureA
  let impureIotaA := Address.blake3 (Ixon.serConstant impureIotaC)
  let envImpure := variant
    { pTree with
      advice := pTree.advice ++ #[impureA, impureIotaA]
      witnesses := pTree.witnesses ++ extraWit
      projModels := pTree.projModels.set! 0 (impureA, impureIotaA) }.ser
    #[(impureA, impureC), (impureIotaA, impureIotaC)]
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj attack: impure projection (Nat.rec _ _ _ 0) with valid iota"
      envImpure (.check ctx natTreeLeftA none) (accept := false)
      (rejectsWith := some "modeled projection")

  -- Attack D: truncated `projModels`
  let envTrunc := variant { pTree with projModels := pTree.projModels.pop }.ser
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj attack: truncated projModels in payload"
      envTrunc (.check ctx natTreeLeftA none) (accept := false)

  -- 4. Disallowed `.proj` targets on modeled blocks (all must reject)
  let twoCtorA ← lookupAddr env (defs "TwoCtorMutA")
  let zeroCtorA ← lookupAddr env (defs "ZeroCtorMutA")
  let idxNestedA ← lookupAddr env (defs "IndexedNested")
  let propMutA ← lookupAddr env (defs "PropMutA")
  let nestedDocA ← lookupAddr env (defs "NestedDoc")

  let (env2, proj2A) := mkProjFn env twoCtorA natA 0
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj negative: 2-ctor mutual inductive"
      env2 (.check ctx proj2A none) (accept := false)

  let (env0c, proj0A) := mkProjFn env zeroCtorA natA 0
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj negative: 0-ctor mutual inductive"
      env0c (.check ctx proj0A none) (accept := false)

  let (envIdx, projIdxA) := mkProjFn env idxNestedA natA 0 #[natZeroA] #[.ref 2 #[]]
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj negative: indexed nested 1-ctor inductive"
      envIdx (.check ctx projIdxA none) (accept := false)

  let (envProp, projPropA) := mkProjFn env propMutA natA 0
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj negative: Prop mutual 1-ctor inductive"
      envProp (.check ctx projPropA none) (accept := false)

  let (envOob, projOobA) := mkProjFn env nestedDocA natA 3
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj negative: out-of-bounds field index on NestedDoc"
      envOob (.check ctx projOobA none) (accept := false)

  let sortPolyDepA ← lookupAddr env (defs "SortPolyField.elem")
  cases := cases.push fun _ =>
    Case.ofClaim "modeled-proj negative: sort-polymorphic field depending on earlier field"
      env (.check ctx sortPolyDepA none) (accept := false)
      (rejectsWith := some "sort-polymorphic field depends on earlier field")

  cases := cases.push fun _ => sortPolyMutProjCase

  runCases "ixvm-modeled-proj" cases (circuit := some true)

end Tests.Ix.IxVM.ModeledProj
