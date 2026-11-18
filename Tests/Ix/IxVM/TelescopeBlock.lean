import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.TelescopeBlockDefs
import Ix.IxVM.Consistency.StatementRel

/-! # An inductive type declared at its telescope, through the program (executed evidence)

The unit step of a one-type native block whose former is declared at its telescope (the
ordinary inductive type) reads the walk's check of the block under either validator. This suite
shows by execution that such blocks and their recursors are accepted in both validator modes,
for `inductive Vec (α : Type) : Nat → Type` (a parameter, an index, a recursive constructor)
and for `structure Both : Prop` (one constructor, no index, a sort that tests zero: the install
stores a projection table). It is executed evidence, not a kernel proof: nothing here enters a
theorem.

Every case is a typing claim the program must accept, under a validated or an assumed binding,
having called a named circuit function: the constructor loop for `Vec`
(`KernelCheck::check_inductive_shape_ctors`), the classifier's field loop for `Both`
(`KernelGuard::check_prop_fields`), the native recursor check for the two recursors
(`KernelCheck::nat_rec_check`), and the syntactic telescope test for `Vec`
(`KernelCheck::former_is_tele`).

With `IX_TELESCOPE_BLOCK_CONTROLS=1` the suite instead runs three claims that must fail: the
block of `Vec` does not call the family route (`KernelModeled::check_family`), nor the
telescope walk of a former declared at a definition (`KernelCheck::former_tele_at`), nor a
function that does not exist.
-/

namespace Tests.Ix.IxVM.TelescopeBlock

open IxVM.ClaimHarness

private def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.TelescopeBlockDefs ++ n.toName

/-- A typing claim on the constant `n`, which the program must accept having called `callee`. -/
private def calledCase (env : Ixon.Env) (n : String) (assumed : Bool) (callee : String) :
    Except String Case := do
  let some target := env.getAddr? (Ix.Name.fromLeanName (defs n))
    | throw s!"{defs n} is not in the Ixon environment"
  let ctx ← Ix.ClaimContext.ofEnv env assumed
  let how := if assumed then "typing, binding assumed" else "typing, binding validated"
  let c ← Case.ofClaim s!"{how}: {n}, having called {callee}" env (.check ctx target none) {}
    true none
  return { c with exercises := some callee }

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let names : Array Lean.Name := #[defs "Vec", defs "Vec.rec", defs "Both", defs "Both.rec"]
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-telescope-block] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv names leanEnv
  if (← IO.getEnv "IX_TELESCOPE_BLOCK_CONTROLS") == some "1" then
    let controls : Array Builder :=
      #["KernelModeled::check_family", "KernelCheck::former_tele_at",
        "KernelCheck::no_such_function"].map
        fun callee _ => calledCase env "Vec" false callee
    return (← runCases "ixvm-telescope-block" controls (jobs := 4) (circuit := some true))
  let mut cases : Array Builder := #[]
  for assumed in [false, true] do
    cases := cases.push
      (fun _ => calledCase env "Vec" assumed "KernelCheck::check_inductive_shape_ctors")
    cases := cases.push (fun _ => calledCase env "Vec.rec" assumed "KernelCheck::nat_rec_check")
    cases := cases.push (fun _ => calledCase env "Both" assumed "KernelGuard::check_prop_fields")
    cases := cases.push (fun _ => calledCase env "Both.rec" assumed "KernelCheck::nat_rec_check")
  cases := cases.push (fun _ => calledCase env "Vec" false "KernelCheck::former_is_tele")
  runCases "ixvm-telescope-block" cases (jobs := 4) (circuit := some true)

end Tests.Ix.IxVM.TelescopeBlock
