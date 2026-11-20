import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.ValueRecordsDefs

/-! # Value records through the program: a theorem, an opaque constant, a block of definitions

`IxVM.Refinement.Typing.valueUnitStep_defn` and `valueUnitStep_defnBlock` state the step of a
standalone theorem or opaque record and of a block of definitions from what the walk observed
at the record: the load of the record (for a block, of each member through its projection
record) and `KernelCheck::check_const` on it, under a validating or an assuming role context.
A run's observations are not a closed fact for a concrete record, so this suite shows by
execution that they occur.

* A theorem and an opaque constant are compiled from Lean and each is claimed through the
  program, under a validated and under an assumed binding, and must be accepted.
* Two definitions of one Lean `mutual` block are compiled and their records reported. Lean's
  kernel admits no recursion among safe definitions, so the compiled reference graph has no
  cycle through them and the compiler writes each as a record of its own; the suite reports
  whether that is so.
* A block of three members in Lean's logic, a definition, an opaque constant and a theorem, is
  assembled over the compiled records: the definition's value is the compiled theorem, the
  opaque constant's value is the compiled opaque constant, the theorem's value is
  `True.intro`. The block is claimed at each member's projection address, under a validated and
  under an assumed binding, and must be accepted having called `Ingress::get_ci_dprj`, the load
  of a definition through its projection record: no other record of the claim, and no record a
  validation of the default table walks, is a member of a block of definitions. One claim so
  holds a theorem, an opaque constant and a block of definitions.
* The same block with a theorem member whose value is not a proof of its statement must be
  refused, under either binding.

It is executed evidence, not a kernel proof: nothing here enters a theorem. Lines of the
record report start with `VR`; the exit code is `0` only if every check and every case passed.

With `IX_VALUE_RECORDS_CONTROLS=1` the suite runs three controls in place of its cases, and
must then fail on each: the compiled theorem claimed, under the validated and under the assumed
binding, as having called the load of a definition through its projection record (its closure
holds no block of definitions), and as having called a function the program does not have.
The member check of a block (`KernelClaim::check_muts_member_at`) would not do as a control: the
theorem's claim calls it at the block of `True`, which the walk checks as a unit.
-/

namespace Tests.Ix.IxVM.ValueRecords

open IxVM.ClaimHarness

private def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.ValueRecordsDefs ++ n.toName

/-- One line of the record report. -/
private def line (name : String) (ok : Bool) (detail : String) : IO Bool := do
  IO.println s!"VR\t{name}\t{if ok then "PASS" else "FAIL"}\t{detail}"
  return ok

private def kindWord : Ix.DefKind → String
  | .defn => "definition"
  | .thm => "theorem"
  | .opaq => "opaque"

private def addrOf (env : Ixon.Env) (n : Lean.Name) : Except String Address :=
  match env.getAddr? (Ix.Name.fromLeanName n) with
  | some a => pure a
  | none => throw s!"{n} is not in the Ixon environment"

/-- Store a record at the address of its bytes. -/
private def put (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.serConstant c)
  let env := env.storeConst a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a .opaque }
    | _ => env
  (env, a)

/-- The block of three members over the compiled records, stored with its three projection
records: a definition whose value is the compiled theorem, an opaque constant whose value is
the compiled opaque constant, and a theorem whose value is `True.intro`, or with `broken` the
proposition `True` itself. Each member's type is `True`. Returns the environment, the block's
address and the members' projection addresses. -/
private def withBlock (env : Ixon.Env) (broken : Bool := false) :
    Except String (Ixon.Env × Address × Array Address) := do
  let aTrue ← addrOf env ``True
  let aIntro ← addrOf env ``True.intro
  let aThm ← addrOf env (defs "proved")
  let aOpq ← addrOf env (defs "sealed")
  let member (kind : Ix.DefKind) (value : UInt64) : Ixon.MutConst :=
    .defn { kind, safety := .safe, lvls := 0, typ := .ref 0 #[], value := .ref value #[] }
  let block : Ixon.Constant :=
    ⟨.muts #[member .defn 2, member .opaq 3, member .thm (if broken then 0 else 1)], #[],
      #[aTrue, aIntro, aThm, aOpq], #[], #[]⟩
  let (env, b) := put env block
  let (env, p0) := put env ⟨.dPrj ⟨0, b⟩, #[], #[], #[], #[]⟩
  let (env, p1) := put env ⟨.dPrj ⟨1, b⟩, #[], #[], #[], #[]⟩
  let (env, p2) := put env ⟨.dPrj ⟨2, b⟩, #[], #[], #[], #[]⟩
  return (env, b, #[p0, p1, p2])

/-- A typing claim on `target`, with the verdict the program must give and, for an acceptance,
a function it must have called. -/
private def typingCase (env : Ixon.Env) (label : String) (target : Address) (assumed : Bool)
    (accept : Bool := true) (callee : Option String := none) : Except String Case := do
  let ctx ← Ix.ClaimContext.ofEnv env assumed
  let how := if assumed then "typing, binding assumed" else "typing, binding validated"
  let called := match callee with
    | some f => s!", having called {f}"
    | none => ""
  let c ← Case.ofClaim s!"{how}: {label}{called}" env (.check ctx target none) {} accept none
  return { c with exercises := callee }

private def recordOf (E : Ixon.Env) (a : Address) : Option Ixon.Constant :=
  (E.consts.get? a).bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption

/-- The record of a compiled definition record at the name `n`: its kind and whether it is in
Lean's logic. -/
private def standaloneRecord (env : Ixon.Env) (n : String) (kind : Ix.DefKind) : IO Bool := do
  let some a := env.getAddr? (Ix.Name.fromLeanName (defs n))
    | line s!"{n}: record" false "not compiled"
  let some c := recordOf env a
    | line s!"{n}: record" false "the record does not decode"
  let .defn d := c.info
    | line s!"{n}: record" false "the record is not a standalone definition record"
  line s!"{n}: a standalone {kindWord kind} record in Lean's logic"
    (d.kind == kind && (Ix.Kernel.Reader.safetyDecline d).isNone)
    s!"at {a}: kind={kindWord d.kind} lvls={d.lvls} refs={c.refs.size}"

/-- What the compiler wrote for a definition of the Lean `mutual` block: a record of its own,
or a member of a block. Reported, not required. -/
private def mutualRecord (env : Ixon.Env) (n : String) : IO Unit := do
  let some a := env.getAddr? (Ix.Name.fromLeanName (defs n))
    | IO.println s!"VR\tinfo\t{n}: not compiled"
  let some c := recordOf env a
    | IO.println s!"VR\tinfo\t{n}: the record does not decode"
  match c.info with
  | .defn d =>
    IO.println s!"VR\tinfo\t{n} at {a}: a standalone {kindWord d.kind} record \
      (the compiler wrote no block for the Lean mutual declaration)"
  | .dPrj p =>
    let members := match (recordOf env p.block).map (·.info) with
      | some (.muts ms) => s!"{ms.size} members"
      | _ => "block not decoded"
    IO.println s!"VR\tinfo\t{n} at {a}: member {p.idx} of the definition block {p.block} \
      ({members})"
  | _ => IO.println s!"VR\tinfo\t{n} at {a}: neither a definition record nor a member of one"

/-- The assembled block's records: the block decodes as three definition members in Lean's
logic of the three kinds, and each projection record is the member's. -/
private def blockRecords (env : Ixon.Env) (b : Address) (ps : Array Address) : IO Bool := do
  let some cb := recordOf env b
    | line "block: record" false "the block's record does not decode"
  let .muts ms := cb.info
    | line "block: record" false "the block's record is not a block"
  let kinds := ms.toList.filterMap fun m => match m with
    | .defn d => some d.kind
    | _ => none
  let ok₁ ← line "block: every member is a definition record in Lean's logic"
    (ms.size == 3 && kinds.length == 3 && ms.all fun m => match m with
      | .defn d => (Ix.Kernel.Reader.safetyDecline d).isNone
      | _ => false)
    s!"at {b}: members={kinds.map kindWord} refs={cb.refs.size}"
  let ok₂ ← line "block: one member of each kind"
    (kinds == [.defn, .opaq, .thm]) s!"{kinds.map kindWord}"
  let mut ok₃ := true
  for (p, i) in ps.zipIdx do
    let isMember := match (recordOf env p).map (·.info) with
      | some (.dPrj q) => q.idx.toNat == i && q.block == b
      | _ => false
    ok₃ := (← line s!"block: the projection record of member {i}" isMember s!"at {p}") && ok₃
  return ok₁ && ok₂ && ok₃

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let names : Array Lean.Name :=
    #[defs "proved", defs "sealed", defs "isEven", defs "isOdd", ``True, ``True.intro]
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-value-records] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv names leanEnv
  let aThm ← IO.ofExcept (addrOf env (defs "proved"))
  let aOpq ← IO.ofExcept (addrOf env (defs "sealed"))
  if (← IO.getEnv "IX_VALUE_RECORDS_CONTROLS") == some "1" then
    let controls : Array Builder :=
      #[(false, "Ingress::get_ci_dprj"), (true, "Ingress::get_ci_dprj"),
        (true, "KernelCheck::no_such_function")].map
        fun (assumed, callee) _ =>
          typingCase env "the compiled theorem" aThm assumed true (some callee)
    return (← runCases "ixvm-value-records" controls (jobs := 4) (circuit := some true))
  let mut ok := true
  ok := (← standaloneRecord env "proved" .thm) && ok
  ok := (← standaloneRecord env "sealed" .opaq) && ok
  mutualRecord env "isEven"
  mutualRecord env "isOdd"
  let (envB, b, ps) ← IO.ofExcept (withBlock env)
  ok := (← blockRecords envB b ps) && ok
  let (envX, _, psX) ← IO.ofExcept (withBlock env (broken := true))
  let mut cases : Array Builder := #[]
  for assumed in [false, true] do
    cases := cases.push (fun _ => typingCase env "the compiled theorem" aThm assumed true
      (some "KernelCheck::check_const"))
    cases := cases.push (fun _ => typingCase env "the compiled opaque constant" aOpq assumed true
      (some "KernelCheck::check_const"))
    for (p, i) in ps.zipIdx do
      cases := cases.push (fun _ => typingCase envB
        s!"the block of a definition, an opaque constant and a theorem, at member {i}" p
        assumed true (some "Ingress::get_ci_dprj"))
    for (p, i) in psX.zipIdx do
      cases := cases.push (fun _ => typingCase envX
        s!"the block with an ill-typed theorem member, at member {i}" p assumed false none)
  let code ← runCases "ixvm-value-records" cases (jobs := 4) (circuit := some true)
  IO.println s!"[ixvm-value-records] records: \
    {if ok then "every check passed" else "a check FAILED"} (executed evidence, not a kernel \
    proof)"
  return if ok then code else 1

end Tests.Ix.IxVM.ValueRecords
