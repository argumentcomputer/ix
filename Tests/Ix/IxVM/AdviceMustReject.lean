module

public import Ix.Meta
public import Ix.IxVM.Model
public import Tests.Ix.IxVM.Harness
public import Tests.Ix.IxVM.ModelAdvice
public import Tests.Ix.IxVMFixtures

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
* an oversized payload (an advice count far beyond its bytes).

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
  -- an environment whose payload for `b` is `bytes`, with extra records served (and, for a
  -- hand-built definition record, the reducibility hint its conversion loads)
  let variant (b : Address) (bytes : ByteArray) (extra : Array (Address × Ixon.Constant) := #[]) :
      Ixon.Env :=
    { env with models := env.models.insert b bytes,
               modelRecords := extra.foldl (fun m (a, c) => m.insert a c) env.modelRecords,
               modelHints := extra.foldl (fun m (a, c) => match c.info with
                 | .defn _ => m.insert a (.regular 0) | _ => m) env.modelHints,
               modelDeps := env.modelDeps.insert b ((env.modelDeps.getD b #[]) ++ extra.map (·.1)) }
  -- a binder-free safe/unsafe `.defn` record (type and value are refs/apps, no section needed)
  let bare (safety : Ix.DefinitionSafety) (typ value : Ixon.Expr) (refs : Array Address)
      (univs : Array Ixon.Univ) : Address × Ixon.Constant :=
    let c : Ixon.Constant :=
      { info := .defn { kind := .defn, safety, lvls := 0, typ, value },
        sharing := #[], refs, univs, binders := #[] }
    (IxVM.Model.addressOf c, c)
  let natA ← lookupAddr env `Nat
  let bfA ← lookupAddr env `Bool.false
  let nzA ← lookupAddr env `Nat.zero
  let sorryA ← lookupAddr env `sorryAx
  let rNat : Ixon.Expr := .ref 0 #[]
  -- `dSorry : Nat := @sorryAx.{1} Nat Bool.false` (a safe def that uses the inert axiom)
  let (dSorryA, dSorry) := bare .safe (.ref 1 #[])
    (.app (.app (.ref 0 #[0]) (.ref 1 #[])) (.ref 2 #[])) #[sorryA, natA, bfA] #[.succ .zero]
  -- `dUnsafe : Nat := Nat.zero` flagged unsafe; `dRefsUnsafe : Nat := dUnsafe` (safe -> unsafe)
  let (dUnsafeA, dUnsafe) := bare .unsaf rNat (.ref 1 #[]) #[natA, nzA] #[]
  let (dRefsUnsafeA, dRefsUnsafe) := bare .safe rNat (.ref 1 #[]) #[natA, dUnsafeA] #[]
  -- `dBlock : Nat := <Even's block record>` (a term naming a block (Muts) address)
  let (dBlockA, dBlock) := bare .safe rNat (.ref 1 #[]) #[natA, evenB] #[]
  -- the benign accepted case needs a block reachable by a kind-1 path from the nested Tree's block
  let pT := advT.layout
  let listA ← lookupAddr env `List
  let some listB := (env.getConst? listA).bind IxVM.Model.projectionBlock?
    | throw (IO.userError "List is not a member of a block")
  let some treeBlockRec := env.getConst? treeB | throw (IO.userError "no Tree block record")
  let some jTreeList := treeBlockRec.refs.findIdx? (· == listA)
    | throw (IO.userError "the Tree block does not reference List")
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
  let cases : Array Builder := #[
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
    -- an advice record that uses an inert axiom, an unsafe record, or a block address: refused by
    -- the gates the inner reference checks lean on (the witnessed-set test, `run_check`'s
    -- `assert_safety` and `get_ci`), not by `assert_ref_allowed`/`assert_not_block_ref`
    caseOn "a definition that uses an inert axiom" (variant evenB
      { pE with advice := pE.advice.push dSorryA }.ser #[(dSorryA, dSorry)]) even
      (some "an unwitnessed outside reference"),
    caseOn "an unsafe record among the advice records" (variant evenB
      { pE with advice := pE.advice.push dUnsafeA }.ser #[(dUnsafeA, dUnsafe)]) even
      (some "an opaque, unsafe or partial definition"),
    caseOn "a safe advice record that references an unsafe record" (variant evenB
      { pE with advice := pE.advice.push dRefsUnsafeA }.ser
        #[(dUnsafeA, dUnsafe), (dRefsUnsafeA, dRefsUnsafe)]) even
      (some "safe constant references an unsafe constant"),
    caseOn "an advice term that names a block record's address" (variant evenB
      { pE with advice := pE.advice.push dBlockA }.ser #[(dBlockA, dBlock)]) even
      (some "no matching arm"),
    caseOn "a witness bound to a role outside the basis" (variant evenB
      { pE with witnesses := pE.witnesses.push (sorryA, 0, [], []) }.ser) even
      (some "a reference to a role outside the basis"),
    -- controls: the unmodified advice at the type, and at the recursor (so the swap is a real change)
    fun _ => Case.ofClaim "advice must-reject control: Even" env (.check ctx even none),
    fun _ => do
      let c ← Case.ofClaim "advice must-reject control: Even.rec" env (.check ctx evenRec none)
      return c.throughModeledRecursor,
    -- a benign pinned acceptance: a kind-1 dependency path ending at a block record is an unused
    -- witness, so the checked records and the environment are the control's (no harm)
    fun _ => Case.ofClaim "advice accepted (benign): a kind-1 path ending at a block record"
      (variant treeB { pT with witnesses := pT.witnesses.push (listB, 1, [jTreeList + 1, 0], []) }.ser)
      (.check ctx tree none)]
  if iota0 == iota1 then
    IO.eprintln "[ixvm-advice-must-reject] the two iota theorems coincide"
    return 1
  runCases "ixvm-advice-must-reject" cases

end Tests.Ix.IxVM.AdviceMustReject

end
