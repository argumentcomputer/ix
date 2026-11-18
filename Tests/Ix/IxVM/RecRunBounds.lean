import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.RecRunBoundsDefs
import Ix.IxVM.Consistency.StatementRel
import IxVMRefinement.Assembly.RecArmRunBounds

/-! # A native recursor's accepted run and its count bounds (executed evidence)

`IxVM.Refinement.Typing.recArmRunBounds_of_obs` derives the count bounds
`RecArmRunBounds rc ip ind` of a standalone native recursor from what the walk observed at its
record: the record's load as a `Rec` value, `check_const` on it, the member check's scan of the
type to the parent and its load of the parent. A run's observations are not a closed fact for
a concrete record, so this suite shows by execution that they occur for three compiled
recursors, none bound by the role table: of a structure, of an indexed recursive family, and
of a type whose recursive field has a telescope.

* Each recursor is claimed through the program, under a validated and under an assumed
  binding, and must be accepted having called `KernelCheck::nat_rec_check`. For the indexed
  family the claim is repeated once per function whose observation the derivation inverts; for
  the type with a telescope, once per function that builds an induction hypothesis from it.
* The bounds are evaluated on the compiled records, with the per-constructor field counts and
  the equalities between the recursor's counts and the member's that the arm asserts.

It is executed evidence, not a kernel proof: nothing here enters a theorem. Lines of the
record report start with `RB`; the exit code is `0` only if every check and every case passed.
-/

namespace Tests.Ix.IxVM.RecRunBounds

open IxVM.ClaimHarness

private def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.RecRunBoundsDefs ++ n.toName

/-- A typing claim on the recursor of the family `n`, which the program must accept having
called `callee`. -/
private def recursorCase (env : Ixon.Env) (n : String) (assumed : Bool) (callee : String) :
    Except String Case := do
  let some target := env.getAddr? (Ix.Name.fromLeanName (defs (n ++ ".rec")))
    | throw s!"{defs (n ++ ".rec")} is not in the Ixon environment"
  let ctx ← Ix.ClaimContext.ofEnv env assumed
  let how := if assumed then "typing, binding assumed" else "typing, binding validated"
  let c ← Case.ofClaim s!"{how}: {n}.rec, having called {callee}" env (.check ctx target none) {}
    true none
  return { c with exercises := some callee }

/-- One line of the record report. -/
private def line (name : String) (ok : Bool) (detail : String) : IO Bool := do
  IO.println s!"RB\t{name}\t{if ok then "PASS" else "FAIL"}\t{detail}"
  return ok

/-- The records of the recursor of `n` and of the family of its major premise in the compiled
environment, and the run's bounds evaluated on them. -/
private def recordBounds (env : Ixon.Env) (n : String) : IO Bool := do
  let some aRec := env.getAddr? (Ix.Name.fromLeanName (defs (n ++ ".rec")))
    | line s!"{n}: records" false "the recursor is not compiled"
  let some aInd := env.getAddr? (Ix.Name.fromLeanName (defs n))
    | line s!"{n}: records" false "the family is not compiled"
  let some c := IxVM.Consistency.recordOf env aRec
    | line s!"{n}: records" false "the recursor's record does not decode"
  let .recr rc := c.info
    | line s!"{n}: records" false "the recursor's record is not a standalone recursor"
  let some cm := IxVM.Consistency.recordOf env aInd
    | line s!"{n}: records" false "the family's record does not decode"
  let .iPrj ip := cm.info
    | line s!"{n}: records" false "the family's record is not an inductive projection"
  let some cb := IxVM.Consistency.recordOf env ip.block
    | line s!"{n}: records" false "the block's record does not decode"
  let .muts ms := cb.info
    | line s!"{n}: records" false "the block's record is not a block"
  let some (.indc ind) := ms[ip.idx.toNat]?
    | line s!"{n}: records" false "the projection's member is not an inductive"
  let fields := ind.ctors.toList.map (·.fields.toNat)
  IO.println s!"RB\tinfo\t{n}.rec at {aRec}: lvls={rc.lvls} params={rc.params} \
    indices={rc.indices} motives={rc.motives} minors={rc.minors} rules={rc.rules.size}; \
    {n} at {aInd}: lvls={ind.lvls} params={ind.params} indices={ind.indices} \
    constructors={ind.ctors.size} member={ip.idx} block members={ms.size} fields={fields}"
  let ok₁ ← line s!"{n}: RecArmRunBounds rc ip ind"
    (decide (IxVM.Refinement.Typing.RecArmRunBounds rc ip ind))
    "the proposition, evaluated on the compiled records"
  let ok₂ ← line s!"{n}: every constructor's field count is below 2^56"
    (fields.all (· < 72057594037927936)) s!"{fields}"
  let ok₃ ← line s!"{n}: the recursor's counts are the member's"
    (rc.params == ind.params && rc.indices == ind.indices && rc.motives == 1 &&
      rc.minors.toNat == ind.ctors.size && rc.rules.size == ind.ctors.size &&
      (rc.lvls == ind.lvls || rc.lvls == ind.lvls + 1))
    "parameters, indices, one motive, a minor premise and a rule per constructor, the level \
      count or one more"
  return ok₁ && ok₂ && ok₃

/-- The families whose recursors are claimed. -/
private def families : List String := ["Two", "Vec", "Tree"]

/-- The functions whose observations the derivation of the bounds inverts: the record's load,
the declaration check, the member check with its scan to the parent, the comparison, and the
constructor loads and projection addresses inside it. -/
private def inverted : List String :=
  ["Ingress::get_ci", "KernelCheck::check_const", "KernelCheck::check_recursor_member",
    "KernelCheck::rec_to_parent_addr", "Ingress::get_ci_cprj",
    "KernelCheck::projection_addr_ctor"]

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let names : Array Lean.Name :=
    (families.flatMap fun n => [defs n, defs (n ++ ".rec")]).toArray
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-rec-run-bounds] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv names leanEnv
  let mut ok := true
  for n in families do
    ok := (← recordBounds env n) && ok
  let mut cases : Array Builder := #[]
  for n in families do
    for assumed in [false, true] do
      cases := cases.push (fun _ => recursorCase env n assumed "KernelCheck::nat_rec_check")
  for callee in inverted do
    cases := cases.push (fun _ => recursorCase env "Vec" false callee)
  for callee in ["KernelCheck::nat_ih_pis", "KernelCheck::nat_tele_at"] do
    cases := cases.push (fun _ => recursorCase env "Tree" false callee)
  let code ← runCases "ixvm-rec-run-bounds" cases (jobs := 4) (circuit := some true)
  IO.println s!"[ixvm-rec-run-bounds] records: \
    {if ok then "every check passed" else "a check FAILED"} (executed evidence, not a kernel \
    proof)"
  return if ok then code else 1

end Tests.Ix.IxVM.RecRunBounds
