module

public import Ix.Meta
public import Ix.IxVM.Model
public import Tests.Ix.IxVM.Harness
public import Tests.Ix.IxVM.ModelAdvice
public import Tests.Ix.IxVMFixtures
public import Ix.SpecDigest

/-! # Must-reject advice for the modeled route

The modeled route (`IxVM/IxVM/Source/KernelModeled.lean`) trusts nothing about
the model advice. Each case below corrupts the advice of a legal block (the
mutual `IxVMInd.Even`/`Odd`, the nested `IxVMInd.Tree`) one way and requires the
program to reject a claim that needs the block:

* a member's model whose type is not the member's (a constructor's model in a
  type's slot);
* `iota_j` theorems with the wrong statement (two swapped), and one whose proof
  does not check (its statement as its value);
* an axiom among the advice records;
* advice that names the block itself, and a public member in a model slot;
* the payload of another block, a payload naming a claimed definition as the
  recursor family, no payload, a payload naming a record the store lacks;
* an oversized payload (an advice count far beyond its bytes);
* under a binding whose `Nat.add` record also names `Even`, so that the validation of
  `Nat.add`'s group (limit 8) checks Even's family: the record bound to `Nat.mul`, an operation
  of a later group, as the first advice record (the operation order at a payload record; the same
  binding with the advice unchanged is accepted).

With the unmodified advice the same claims on the block's types are accepted
(`ixvm-model-advice`). A claim on the family's recursor is refused at the recursor
while the program refuses the recursors of such families (`modeledRecursorsRefused`);
each case that was stated at the recursor is stated at the type as well, where the
family is still checked against its advice.
-/

public section

namespace Tests.Ix.IxVM.AdviceMustReject

open IxVM.ClaimHarness IxVM.Model

private def blockOf (env : Ixon.Env) (a : Address) : IO Address := do
  let some c := env.getConst? a | throw (IO.userError s!"{a} is not stored")
  match c.info with
  | .iPrj p => pure p.block
  | .cPrj p => pure p.block
  | _ => throw (IO.userError s!"{a} is not a member of an inductive block")

def run (lenv : Lean.Environment) : IO UInt32 := do
  let names : Array Lean.Name := #[`IxVMInd.Even, `IxVMInd.Even.rec, `IxVMInd.Tree, `IxVMInd.Tree.rec,
    `Nat.add]
  let env0 ← loadSharedIxonEnv names lenv
  let bare := { ModelAdvice.withoutModels env0 with modelsAttached := false }
  let (env, rep) ← IO.ofExcept (generateReport bare)
  let even ← lookupAddr env `IxVMInd.Even
  let evenRec ← lookupAddr env `IxVMInd.Even.rec
  let tree ← lookupAddr env `IxVMInd.Tree
  let natAdd ← lookupAddr env `Nat.add
  let evenB ← blockOf env even
  let treeB ← blockOf env tree
  let some (_, advE) := rep.advice.find? (·.1 == evenB) | throw (IO.userError "Even has no advice")
  let some (_, advT) := rep.advice.find? (·.1 == treeB) | throw (IO.userError "Tree has no advice")
  let pE := advE.layout
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  -- an environment whose payload for `b` is `bytes`, with extra records served
  let variant (b : Address) (bytes : ByteArray) (extra : Array (Address × Ixon.Constant) := #[]) :
      Ixon.Env :=
    { env with models := env.models.insert b bytes,
               modelRecords := extra.foldl (fun m (a, c) => m.insert a c) env.modelRecords,
               modelDeps := env.modelDeps.insert b ((env.modelDeps.getD b #[]) ++ extra.map (·.1)) }
  let caseOn (label : String) (e : Ixon.Env) (target : Address) (why : Option String) : Builder :=
    fun _ => Case.ofClaim s!"advice must-reject: {label}" e (.check ctx target none) (accept := false)
      (rejectsWith := why)
  -- the same at the recursor: refused there while the program refuses such recursors
  let atRecursor (label : String) (e : Ixon.Env) (why : Option String) : Builder := fun u => do
    let c ← caseOn s!"{label}, at the recursor" e evenRec why u
    return c.throughModeledRecursor
  -- a theorem whose value is its own statement (ill-typed proof)
  let some iota0 := pE.iotas[0]? | throw (IO.userError "Even.rec has no iota theorem")
  let some iota1 := pE.iotas[1]? | throw (IO.userError "Even.rec has one iota theorem")
  let some t0 := env.modelRecords[iota0]? | throw (IO.userError "iota_0 is not served")
  let badThm : Ixon.Constant := match t0.info with
    | .defn d => { t0 with info := .defn { d with value := d.typ } }
    | _ => t0
  let badThmA := Address.blake3 (Ixon.ser badThm)
  -- an axiom `ax : Prop`
  let ax : Ixon.Constant := ⟨.axio { isUnsafe := false, lvls := 0, typ := .sort 0 }, #[], #[], #[.zero], #[]⟩
  let axA := Address.blake3 (Ixon.ser ax)
  let swap (xs : Array Address) (i j : Nat) : Array Address :=
    match xs[i]?, xs[j]? with
    | some a, some b => (xs.set! i b).set! j a
    | _, _ => xs
  let some ctorModel := pE.ctorModels[0]? | throw (IO.userError "Even has no constructor model")
  let missing := Address.blake3 "a record nobody stores".toUTF8
  let swapped := variant evenB { pE with iotas := swap pE.iotas 0 1 }.ser
  let badProof := variant evenB
    { pE with iotas := pE.iotas.set! 0 badThmA, advice := (pE.advice.erase iota0).push badThmA }.ser
    #[(badThmA, badThm)]
  let otherBlock := variant evenB advT.layout.ser
  let definitionFamily := variant evenB { pE with recBlock := natAdd }.ser
  -- a binding whose `Nat.add` (group 8, validated at limit 8) is the default record with one
  -- more, unused, reference to `Even` (a sharing entry): the validation's walk of `Nat.add`
  -- reaches `Even`, whose family is checked there with its payload; with `Nat.mul`'s record
  -- (group 10, an operation not yet in force) as the payload's first advice record, the order
  -- assertion at the advice address must refuse it (`KernelRoles::assert_in_order`); with the
  -- payload unchanged, the same binding is accepted (control)
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let roleAt (r : Ix.Kernel.Role) : IO Address := match table.bound.find? (·.1 == r) with
    | some (_, a) => pure a
    | none => throw (IO.userError s!"role {repr r} is not bound")
  let addA ← roleAt .natAdd
  let mulA ← roleAt .natMul
  let some addC := env.getConst? addA | throw (IO.userError "the record bound to Nat.add is not stored")
  let addX : Ixon.Constant := { addC with
    sharing := addC.sharing.push (.ref addC.refs.size.toUInt64 #[]), refs := addC.refs.push even }
  let addXA := Address.blake3 (Ixon.serConstant addX)
  let tableX : Ix.Kernel.RoleTable :=
    { table with bound := table.bound.map fun (r, b) => (r, if r == .natAdd then addXA else b) }
  IO.ofExcept tableX.check
  let hinted := match env.anonHints[addA]? with
    | some h => { env with anonHints := env.anonHints.insert addXA h }
    | none => env
  let envX ← IO.ofExcept (withRoleTable (hinted.storeConst addXA addX) tableX.toBytes)
  let some bindingX := envX.roleBinding | throw (IO.userError "the rebound environment has no binding")
  let spec ← IO.ofExcept Ix.SpecDigest.specDigest
  let envLater := { envX with models := envX.models.insert evenB { pE with advice := #[mulA] ++ pE.advice }.ser }
  let orderCases : Array Builder := #[
    fun _ => Case.ofClaim
      "advice must-reject: Nat.add's record reaches Even, whose advice lists Nat.mul's record (a later operation)"
      envLater (.binding spec bindingX.address) (accept := false)
      (rejectsWith := some "an operation is reached before its group is validated"),
    fun _ => Case.ofClaim
      "advice must-reject control: Nat.add's record reaches Even, with Even's advice unchanged"
      envX (.binding spec bindingX.address)]
  let cases : Array Builder := orderCases ++ #[
    caseOn "a type's slot holds a constructor's model" (variant evenB
      { pE with typeModels := pE.typeModels.set! 0 ctorModel }.ser) even (some "model type mismatch"),
    caseOn "two iota theorems swapped" swapped even none,
    atRecursor "two iota theorems swapped" swapped none,
    caseOn "an iota theorem whose proof does not check" badProof even
      (some "inferred type is not def-eq"),
    atRecursor "an iota theorem whose proof does not check" badProof
      (some "inferred type is not def-eq"),
    caseOn "an axiom among the advice records" (variant evenB
      { pE with advice := pE.advice.push axA }.ser #[(axA, ax)]) even none,
    caseOn "the advice names the block itself" (variant evenB
      { pE with advice := pE.advice.push evenB }.ser) even (some "a mutual or nested inductive"),
    caseOn "a public member in a model slot" (variant evenB
      { pE with typeModels := pE.typeModels.set! 0 even, advice := pE.advice.push even }.ser) even
      (some "a projection of a block that is not advice"),
    caseOn "the payload of another block" otherBlock even none,
    atRecursor "the payload of another block" otherBlock
      (some "the payload names another recursor family"),
    caseOn "a payload naming a claimed definition as the family" definitionFamily even none,
    atRecursor "a payload naming a claimed definition as the family" definitionFamily
      (some "the payload names another recursor family"),
    caseOn "no payload" { env with models := env.models.erase evenB } even (some "missing hint"),
    caseOn "a payload naming a record the store lacks" (variant evenB
      { pE with advice := pE.advice.push missing }.ser) even (some "missing hint"),
    caseOn "an oversized advice count" (variant evenB { pE with adviceCount := some 1_000_000 }.ser) even none,
    -- controls: the unmodified advice at the type, and at the recursor (so the swap is a real change)
    fun _ => Case.ofClaim "advice must-reject control: Even" env (.check ctx even none),
    fun _ => do
      let c ← Case.ofClaim "advice must-reject control: Even.rec" env (.check ctx evenRec none)
      return c.throughModeledRecursor]
  if iota0 == iota1 then
    IO.eprintln "[ixvm-advice-must-reject] the two iota theorems coincide"
    return 1
  runCases "ixvm-advice-must-reject" cases

end Tests.Ix.IxVM.AdviceMustReject

end
