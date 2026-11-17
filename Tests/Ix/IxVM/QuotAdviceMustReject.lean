module

public import Ix.Meta
public import Ix.IxVM.Model
public import Tests.Ix.IxVM.Harness
public import Tests.Ix.IxVM.ModelAdvice
public import Tests.Ix.IxVMFixtures

/-! # Must-reject quotient advice

The circuit admits the quotient roles among the basis references of model advice, and
no other role outside the basis (`KernelModeled::basis_role_allowed`). From the advice of
the mutual `IxVMInd.Even` whose iota proofs use the quotient (`ModelAdvice.quotProofs`),
each case replaces the basis witness of `Quot.sound` by another address and requires the
circuit to refuse a claim that needs the block:

* `propext` (an axiom role outside the basis);
* `True` (a role outside the basis);
* an address bound to no role.

The unmodified advice is accepted at the type (control). A claim on the recursor is refused at
the recursor while the program refuses the recursors of such families.
-/

public section

namespace Tests.Ix.IxVM.QuotAdviceMustReject

open IxVM.ClaimHarness IxVM.Model

def run (lenv : Lean.Environment) : IO UInt32 := do
  let names : Array Lean.Name := #[`IxVMInd.Even, `IxVMInd.Even.rec]
  let env0 ← loadSharedIxonEnv names lenv
  let bare := { ModelAdvice.withoutModels env0 with modelsAttached := false }
  let (env, rep) ← IO.ofExcept (generateReport bare ModelAdvice.quotProofs)
  let even ← lookupAddr env `IxVMInd.Even
  let evenRec ← lookupAddr env `IxVMInd.Even.rec
  let some c := env.getConst? even | throw (IO.userError "Even is not stored")
  let evenB ← match c.info with
    | .iPrj p => pure p.block
    | _ => throw (IO.userError "Even is not a member of an inductive block")
  let some (_, adv) := rep.advice.find? (·.1 == evenB) | throw (IO.userError "Even has no advice")
  let p := adv.layout
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let roleAddr (r : Ix.Kernel.Role) : IO Address := match table.bound.find? (·.1 == r) with
    | some (_, a) => pure a
    | none => throw (IO.userError s!"role {repr r} is not bound")
  let sound ← roleAddr .quotSound
  let some i := p.witnesses.findIdx? (·.1 == sound)
    | throw (IO.userError "the advice has no basis witness for Quot.sound")
  let propext ← roleAddr .propext
  let trueA ← roleAddr .true
  let unbound := Address.blake3 "an address no role binds".toUTF8
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let witnessAt (x : Address) : Payload := { p with witnesses := p.witnesses.set! i (x, 0, [], []) }
  let variant (q : Payload) : Ixon.Env := { env with models := env.models.insert evenB q.ser }
  let caseOn (label : String) (q : Payload) (target : Address) (why : String) : Builder :=
    fun _ => Case.ofClaim s!"quotient advice must-reject: {label}" (variant q) (.check ctx target none)
      (accept := false) (rejectsWith := some why)
  let cases : Array Builder := #[
    caseOn "propext as a basis reference" (witnessAt propext) even
      "a reference to a role outside the basis",
    caseOn "True as a basis reference" (witnessAt trueA) even "a reference to a role outside the basis",
    caseOn "an unbound address as a basis reference" (witnessAt unbound) even
      "a basis reference is not bound to a role",
    fun u => do
      let c ← caseOn "propext as a basis reference, at the recursor" (witnessAt propext) evenRec
        "a reference to a role outside the basis" u
      return c.throughModeledRecursor,
    fun _ => Case.ofClaim "quotient advice must-reject control: Even" env (.check ctx even none),
    fun _ => do
      let c ← Case.ofClaim "quotient advice must-reject control: Even.rec" env (.check ctx evenRec none)
      return c.throughModeledRecursor]
  runCases "ixvm-quot-advice-must-reject" cases

end Tests.Ix.IxVM.QuotAdviceMustReject

end
