import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.AliasBlockDefs
import Ix.IxVM.Consistency.StatementRel

/-! # A family whose former is declared at a definition, through the program (executed evidence)

The unit step of a one-type native block whose former is declared at a definition that only
reduces to a telescope reads the walk's check of the block: the result-sort walk, the telescope
builder, the from-scratch check of the built telescope and its conversion with the declared
type. A run's observations are not a closed fact for a concrete record, so this suite shows by
execution that they occur for `inductive R (α : Type) : Rel α` with
`Rel α := α → α → Prop`, compiled by Ix's compiler and bound by no role.

* The family is claimed through the program under a validated and under an assumed binding,
  and must be accepted having called the telescope builder `KernelCheck::former_tele_at`
  (the program calls it only where the former's type is no syntactic telescope), and once per
  other function the step's derivation inverts.
* Its recursor is claimed under both bindings and must be accepted having called
  `KernelCheck::nat_rec_check` (the native recursor check, which rebuilds the telescope).
* The compiled record is read: one inductive member, one parameter, two indices (the program
  refuses such a former with no index), one constructor.

It is executed evidence, not a kernel proof: nothing here enters a theorem. Lines of the
record report start with `AB`; the exit code is `0` only if every check and every case passed.

With `IX_ALIAS_BLOCK_CONTROLS=1` the suite runs two controls in place of its cases, and must
then fail on each: the family claimed as having called the family check of a mutual or nested
block (the program treats it as native), and as having called a function the program does not
have.
-/

namespace Tests.Ix.IxVM.AliasBlock

open IxVM.ClaimHarness

private def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.AliasBlockDefs ++ n.toName

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

/-- One line of the record report. -/
private def line (name : String) (ok : Bool) (detail : String) : IO Bool := do
  IO.println s!"AB\t{name}\t{if ok then "PASS" else "FAIL"}\t{detail}"
  return ok

/-- An application spine over a reference, through the sharing table (`fuel` bounds the walk):
the executable mirror of `IxVM.Refinement.Typing.BlockIxonAppHeadRef`. -/
private def appHeadRef (sharing : Array Ixon.Expr) : Nat → Ixon.Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
    match e with
    | .ref _ _ => true
    | .recur _ _ => true
    | .app f _ => appHeadRef sharing fuel f
    | .share idx =>
      match sharing[idx.toNat]? with
      | some s => appHeadRef sharing fuel s
      | none => false
    | _ => false

/-- `n` literal binders and then an application spine over a reference, through the sharing
table: the executable mirror of `IxVM.Refinement.Typing.BlockIxonRetHead`. -/
private def retHead (sharing : Array Ixon.Expr) : Nat → Nat → Ixon.Expr → Bool
  | 0, _, _ => false
  | fuel + 1, n, e =>
    match e with
    | .share idx =>
      match sharing[idx.toNat]? with
      | some s => retHead sharing fuel n s
      | none => false
    | .all _ body =>
      match n with
      | 0 => false
      | n + 1 => retHead sharing fuel n body
    | e => n == 0 && appHeadRef sharing fuel e

/-- The number of leading literal binders of an expression, through the sharing table. -/
private def leadingBinders (sharing : Array Ixon.Expr) : Nat → Ixon.Expr → Nat
  | 0, _ => 0
  | fuel + 1, e =>
    match e with
    | .share idx =>
      match sharing[idx.toNat]? with
      | some s => leadingBinders sharing fuel s
      | none => 0
    | .all _ body => leadingBinders sharing fuel body + 1
    | _ => 0

/-- The compiled record of the family: its projection record, its block and its counts. -/
private def recordShape (env : Ixon.Env) : IO Bool := do
  let some aInd := env.getAddr? (Ix.Name.fromLeanName (defs "R"))
    | line "R: record" false "the family is not compiled"
  let some cm := IxVM.Consistency.recordOf env aInd
    | line "R: record" false "the family's record does not decode"
  let .iPrj ip := cm.info
    | line "R: record" false "the family's record is not an inductive projection"
  let some cb := IxVM.Consistency.recordOf env ip.block
    | line "R: record" false "the block's record does not decode"
  let .muts ms := cb.info
    | line "R: record" false "the block's record is not a block"
  let some (.indc ind) := ms[ip.idx.toNat]?
    | line "R: record" false "the projection's member is not an inductive"
  let fields := ind.ctors.toList.map (·.fields.toNat)
  IO.println s!"AB\tinfo\tR at {aInd}: block {ip.block} member={ip.idx} \
    block members={ms.size} lvls={ind.lvls} params={ind.params} indices={ind.indices} \
    constructors={ind.ctors.size} fields={fields} unsafe={ind.isUnsafe}"
  let ok₁ ← line "R: a block of one inductive member" (ms.size == 1 && ip.idx.toNat == 0)
    s!"members={ms.size} member={ip.idx}"
  let ok₂ ← line "R: one parameter and an index" (ind.params.toNat == 1 && ind.indices.toNat == 2)
    s!"params={ind.params} indices={ind.indices}"
  let ok₃ ← line "R: one constructor, in Lean's logic"
    (ind.ctors.size == 1 && !ind.isUnsafe) s!"constructors={ind.ctors.size}"
  let binders := leadingBinders cb.sharing 4096 ind.typ
  let ok₄ ← line "R: the declared type is no literal telescope of its parameters and indices"
    (binders < ind.params.toNat + ind.indices.toNat)
    s!"literal binders={binders}, parameters and indices={ind.params.toNat + ind.indices.toNat}"
  let ok₅ ← line "R: every constructor returns literally"
    (ind.ctors.toList.all fun ct =>
      retHead cb.sharing 4096 (ind.params.toNat + ct.fields.toNat) ct.typ)
    "the executable mirror of BlockCtorIxonRetHead on the block's record"
  return ok₁ && ok₂ && ok₃ && ok₄ && ok₅

/-- The functions whose observations the block's unit step inverts: the member's load and
check, the dispatch on the block, the result-sort walk, the test for a syntactic telescope, the
head reduction the telescope builder calls, the check of the built telescope and its
conversion with the declared type, the former's guard and the constructor loop. -/
private def inverted : List String :=
  ["Ingress::get_ci", "KernelCheck::check_const", "KernelModeled::block_is_modeled",
    "KernelCheck::check_inductive_shape", "KernelCheck::get_result_sort_level",
    "KernelCheck::former_is_tele", "KernelCheck::former_tele_typed",
    "KernelGuard::head", "KernelCheck::validate_expr_well_scoped",
    "KernelInfer::k_ensure_sort", "KernelDefEq::k_is_def_eq", "KernelCheck::former_decl_ok",
    "KernelCheck::check_inductive_shape_ctors"]

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let names : Array Lean.Name := #[defs "Rel", defs "R", defs "R.rec"]
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-alias-block] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv names leanEnv
  let ok ← recordShape env
  if (← IO.getEnv "IX_ALIAS_BLOCK_CONTROLS") == some "1" then
    let controls : Array Builder :=
      #["KernelModeled::check_family", "KernelCheck::no_such_function"].map
        fun callee _ => calledCase env "R" false callee
    return (← runCases "ixvm-alias-block" controls (jobs := 4) (circuit := some true))
  let mut cases : Array Builder := #[]
  for assumed in [false, true] do
    cases := cases.push (fun _ => calledCase env "R" assumed "KernelCheck::former_tele_at")
    cases := cases.push (fun _ => calledCase env "R.rec" assumed "KernelCheck::nat_rec_check")
  for callee in inverted do
    cases := cases.push (fun _ => calledCase env "R" false callee)
  cases := cases.push (fun _ => calledCase env "R.rec" false "KernelCheck::nat_former_tele")
  let code ← runCases "ixvm-alias-block" cases (jobs := 4) (circuit := some true)
  IO.println s!"[ixvm-alias-block] record: \
    {if ok then "every check passed" else "a check FAILED"} (executed evidence, not a kernel \
    proof)"
  return if ok then code else 1

end Tests.Ix.IxVM.AliasBlock
