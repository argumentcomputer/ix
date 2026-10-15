import LSpec
import Ix.Meta
import Ix.Cert.Audit
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.SourceContract.SyntaxFixture

/-! # The certification statements on the Source-mode fixtures (`lake test -- cert-statement`)

* **Compile parity.** `Ix.Cert.compile`, the function the statements are
  about, against the IO pipeline (`Ix.CompileM.compileLeanConsts`) and the
  Rust compiler (`Ix.CompileM.rsCompileEnvFFI`), on the closure of every
  constant of `Tests.Ix.Kernel.ReaderFidelityDefs` and
  `Tests.Ix.Kernel.SourceIngressDefs`: the serialized environments
  (`Ixon.serEnv`) are byte-identical, and so are the published addresses.
  `cert-compile-parity-init` (ignored) does the same on `Init`.
* **The statements' hypotheses and conclusion, per root, on the accepted
  fixtures** (`Tests.Ix.Kernel.SourceIngress.acceptedSeeds` and the prelude's
  constants):
  - the computed closure (`Ix.Cert.closure`) is the closure the Source-mode
    test checks, and is closed under `DependsOn`;
  - Source mode accepts it under the compiler's grouping (`Ix.Cert.blocksOf`);
  - the compile publishes every constant of it (`Ix.Cert.Published`);
  - a dependency-first order of the compiled closure meets `ClosureOrder`
    and is accepted by the certified entry at BLAKE3 (`Ix.Cert.IxonAccepts`);
  - the reading (`Ix.Cert.reading`) reads every constant of the closure as an
    installed compiled constant with as many level parameters as it has
    level arguments, the condition under which `Commutes` can hold.
* **Binder contracts on both sides**, on declarations of the source-contract
  syntax fixture (`Tests.Ix.SourceContract.SyntaxFixture`) with input and
  result contracts on arrows, λs and lets: their source contracts resolved
  (`Ix.Compile.prepareRegisteredConstants`, as the IO pipeline does) and
  canonicalized, Source mode accepts them, and every constant's binders carry
  the same contracts in Source mode as its reading does in the certified
  entry's environment of `Ix.Cert.compile`'s output.

Importing `Ix.Cert.Audit` builds the statements' freeze with the tests. -/

namespace Tests.Ix.Cert.Statement

open LSpec
open Tests.Ix.Kernel.SourceIngress (defsModule ownModule acceptedSeeds preludeNames)

/-- The fixture modules' constants and everything they reach, as Lean
constants. -/
def fixtureConsts (leanEnv : Lean.Environment) : IO (List (Lean.Name × Lean.ConstantInfo)) := do
  let some idx := leanEnv.getModuleIdx? defsModule | throw (IO.userError "fixture module not loaded")
  let some idx' := leanEnv.getModuleIdx? ownModule | throw (IO.userError "fixture module not loaded")
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    let m := leanEnv.getModuleIdxFor? n
    if m == some idx || m == some idx' then some n else none
  IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv (seeds ++ #[`Nat.div] ++ preludeNames))

/-- The published addresses of two compiled environments that differ, by name. -/
def addressDiffs (a b : Ixon.Env) : Array String := Id.run do
  let mut out := #[]
  for (n, na) in a.named.toList do
    match b.named.get? n with
    | some nb => unless na.addr == nb.addr do out := out.push s!"{n}: {na.addr} vs {nb.addr}"
    | none => out := out.push s!"{n}: missing from the second"
  for (n, _) in b.named.toList do
    unless a.named.contains n do out := out.push s!"{n}: missing from the first"
  return out

/-- `Ix.Cert.compile` against the IO pipeline and the Rust compiler on
`consts`: errors, and lines for the report. -/
def parity (label : String) (consts : List (Lean.Name × Lean.ConstantInfo)) (workers : Nat) :
    IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let t0 ← IO.monoMsNow
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts.toArray workers
  let t1 ← IO.monoMsNow
  let pure? ← IO.lazyPure fun _ => Ix.Cert.compile env
  let t2 ← IO.monoMsNow
  let ixe ← match pure? with
    | .ok ixe => pure ixe
    | .error e => return (#[s!"{label}: Ix.Cert.compile failed: {e}"], lines)
  let some pureBytes := (Ixon.serEnv ixe).toOption
    | return (#[s!"{label}: serEnv of Ix.Cert.compile's output failed"], lines)
  lines := lines.push s!"{label}: {consts.length} constants; canon {t1 - t0} ms, \
    Ix.Cert.compile {t2 - t1} ms: {ixe.consts.size} records, {ixe.named.size} names, \
    {pureBytes.size} bytes"
  -- the IO pipeline
  let t3 ← IO.monoMsNow
  match ← Ix.CompileM.compileLeanConsts consts (numWorkers := workers) with
  | .error e => errors := errors.push s!"{label}: compileLeanConsts failed: {e}"
  | .ok out =>
    let t4 ← IO.monoMsNow
    lines := lines.push s!"{label}: compileLeanConsts {t4 - t3} ms: {out.bytes.size} bytes, \
      {out.ungroundedCount} ungrounded, {out.cenv.ungrounded.size} per-block failures"
    unless out.bytes == pureBytes do
      errors := errors.push s!"{label}: serEnv bytes differ from compileLeanConsts's \
        ({pureBytes.size} vs {out.bytes.size})"
    let diffs := addressDiffs ixe out.env
    unless diffs.isEmpty do
      errors := errors.push s!"{label}: {diffs.size} published addresses differ from \
        compileLeanConsts's: {diffs.toList.take 5}"
  -- the Rust compiler
  let raw ← Ix.CompileM.rsCompileEnvFFI consts
  let rust := raw.toEnv
  match Ixon.serEnv rust with
  | .error e => errors := errors.push s!"{label}: serEnv of the Rust output failed: {e}"
  | .ok rustBytes =>
    lines := lines.push s!"{label}: Rust compiler: {rust.consts.size} records, {rustBytes.size} bytes"
    unless rustBytes == pureBytes do
      errors := errors.push s!"{label}: serEnv bytes differ from the Rust compiler's \
        ({pureBytes.size} vs {rustBytes.size})"
    let diffs := addressDiffs ixe rust
    unless diffs.isEmpty do
      errors := errors.push s!"{label}: {diffs.size} published addresses differ from the \
        Rust compiler's: {diffs.toList.take 5}"
  return (errors, lines)

/-! ## The Ixon side of one closure -/

/-- The records a record needs (`Ix.Cert.RecordEdge`): its block, for a
projection, and the records of its reference table. -/
def edges (ixe : Ixon.Env) (a : Address) : Array Address :=
  match Ix.Cert.recordAt ixe a with
  | none => #[]
  | some c =>
    let o := Ix.Cert.ownerOf a c
    (if o != a then #[o] else #[]) ++ c.refs.filter (ixe.consts.contains ·)

/-- The compiled closure of `seeds`, dependencies first: a depth-first
postorder over `edges`. -/
def closureOrder (ixe : Ixon.Env) (seeds : Array Address) : Array Address := Id.run do
  let mut done : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  for root in seeds do
    unless ixe.consts.contains root do continue
    let mut stack : Array (Address × Bool) := #[(root, false)]
    while h : stack.size > 0 do
      let (node, expanded) := stack[stack.size - 1]
      stack := stack.pop
      if expanded then
        unless done.contains node do
          done := done.insert node
          out := out.push node
      else unless done.contains node do
        stack := stack.push (node, true)
        for d in edges ixe node do
          unless done.contains d do stack := stack.push (d, false)
  return out

/-- The compiled closure of `seeds` as a set, by a separate worklist. -/
def reach (ixe : Ixon.Env) (seeds : Array Address) : Std.HashSet Address := Id.run do
  let mut seen : Std.HashSet Address := {}
  let mut todo := seeds.filter (ixe.consts.contains ·)
  while h : todo.size > 0 do
    let a := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains a then continue
    seen := seen.insert a
    todo := todo ++ edges ixe a
  return seen

/-- `ClosureOrder`'s three conditions, decided on one order: the failures. -/
def closureOrderProblems (ixe : Ixon.Env) (seeds : Array Address) (order : Array Address) :
    Array String := Id.run do
  let mut out := #[]
  let mut position : Std.HashMap Address Nat := {}
  for (a, i) in order.zipIdx do
    if position.contains a then out := out.push s!"{a} occurs twice"
    position := position.insert a i
  let reached := reach ixe seeds
  unless reached.size == position.size && order.all reached.contains do
    out := out.push s!"the order has {position.size} records, the closure {reached.size}"
  for (a, i) in order.zipIdx do
    let some c := Ix.Cert.recordAt ixe a | out := out.push s!"{a} does not decode"
    for r in c.refs do
      if let some cr := Ix.Cert.recordAt ixe r then
        let b := Ix.Cert.ownerOf r cr
        if b != a then
          unless (position[b]?.map (decide <| · < i)).getD false do
            out := out.push s!"{a} comes before {b}, which it references"
  return out

/-- Bounds wide enough for a whole compiled library
(`Benchmarks.Kernel.CheckIxeEntry.limits`). -/
def limits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- The statements' hypotheses and conclusion on the closure of the accepted
fixtures: errors, and lines for the report. -/
def perRoot (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let env := Tests.Ix.Kernel.SourceIngressStep.canon (← fixtureConsts leanEnv).toArray
  let roots := (acceptedSeeds ++ preludeNames).toList.map Ix.Name.fromLeanName
  for r in roots do
    unless env.consts.contains r do errors := errors.push s!"root {r} is not in the environment"
  -- the closure, against the Source-mode test's
  let sub := Ix.Cert.closure env roots
  let expected ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv acceptedSeeds
  let extra := sub.consts.toList.filter fun (n, _) => !expected.consts.contains n
  let missing := expected.consts.toList.filter fun (n, _) => !sub.consts.contains n
  unless extra.isEmpty && missing.isEmpty do
    errors := errors.push s!"closure: {extra.length} constants the Source-mode test's closure \
      lacks ({(extra.map (·.1)).take 5}), {missing.length} it has ({(missing.map (·.1)).take 5})"
  -- closed under `DependsOn`, as `ClosureCorrect` states
  let recursors := Ix.Cert.recursorsByBlock env
  let mut open_ : Array String := #[]
  for (n, ci) in sub.consts.toList do
    for d in Ix.Cert.dependencies recursors ci do
      if env.consts.contains d && !sub.consts.contains d then open_ := open_.push s!"{n} → {d}"
  unless open_.isEmpty do
    errors := errors.push s!"closure: not closed: {open_.toList.take 5}"
  lines := lines.push s!"closure of {roots.length} roots in {env.consts.size} constants: \
    {sub.consts.size} constants, closed under DependsOn"
  -- Source acceptance
  let some envS := (Ix.LeanIngress.checkSource sub (Ix.Cert.blocksOf sub)).toOption
    | return (errors.push "Source mode refuses the closure under Ix.Cert.blocksOf", lines)
  lines := lines.push s!"Source accepts the closure: {envS.consts.length} kernel constants"
  -- the compile publishes the closure
  let some ixe := (Ix.Cert.compile env).toOption
    | return (errors.push "Ix.Cert.compile failed", lines)
  let unpublished := sub.consts.toList.filter fun (n, _) => !ixe.named.contains n
  unless unpublished.isEmpty do
    errors := errors.push s!"{unpublished.length} constants of the closure are not published: \
      {(unpublished.map (·.1)).take 5}"
  let seeds : Array Address := sub.consts.toArray.filterMap fun (n, _) =>
    (ixe.named.get? n).map (·.addr)
  let mut byAddress : Std.HashMap Address Nat := {}
  for a in seeds do byAddress := byAddress.insert a (byAddress.getD a 0 + 1)
  let aliased := byAddress.fold (fun k _ c => if c > 1 then k + c else k) 0
  -- the compiled closure in a dependency-first order
  let order := closureOrder ixe seeds
  for p in (closureOrderProblems ixe seeds order).toList.take 5 do
    errors := errors.push s!"ClosureOrder: {p}"
  let records := Ix.Cert.recordsOf ixe order.toList
  let blobs := Ix.Cert.blobsOf ixe order.toList
  lines := lines.push s!"compiled closure: {seeds.size} published addresses \
    ({byAddress.size} distinct; {aliased} names share an address), {order.size} records, \
    {blobs.length} blobs"
  let some binding := Ix.Kernel.Admission.defaultBinding.toOption
    | return (errors.push "the default role table does not load", lines)
  let envA ← match Ixon.Authenticated.checkBytes binding limits records blobs (Ix.Cert.hintsOf ixe) with
    | .ok envA => pure envA
    | .error e => return (errors.push s!"the certified entry refuses the compiled closure: {e}", lines)
  lines := lines.push s!"the certified entry accepts it: {envA.consts.length} kernel constants"
  -- the reading
  let some cx := Ix.Cert.admissionContext binding limits ixe order.toList
    | return (errors.push "no admission context", lines)
  let mut read := 0
  let mut unread : Array Ix.Kernel.Key := #[]
  let mut bad : Array String := #[]
  for c in envS.consts do
    match Ix.Cert.reading ixe cx c with
    | none => unread := unread.push c.name
    | some t@(.const k us) =>
      read := read + 1
      match envA.find? k with
      | none => bad := bad.push s!"{c.name} reads as {k}, which is not installed"
      | some ci =>
        unless us.length == ci.toConstantVal.levelParams.length do
          bad := bad.push s!"{c.name} reads as {repr t}: {ci.toConstantVal.levelParams.length} \
            level parameters"
    | some t => bad := bad.push s!"{c.name} reads as {repr t}"
  for b in bad.toList.take 5 do errors := errors.push s!"reading: {b}"
  -- every constant of the closure is read
  let subNames : Std.HashSet Ix.Kernel.Key :=
    sub.consts.fold (fun s n _ => s.insert (Ix.LeanIngress.ingressKey n)) {}
  let unreadOwn := unread.filter subNames.contains
  unless unreadOwn.isEmpty do
    errors := errors.push s!"reading: {unreadOwn.size} constants of the closure are not read: \
      {unreadOwn.toList.take 5}"
  lines := lines.push s!"reading: {read} of {envS.consts.length} Source constants read, \
    all installed with their level arity; not read: {unread.size}, none from the closure \
    (for example {unread.toList.take 6})"
  return (errors, lines)

/-! ## Binder contracts on both sides -/

def syntaxModule : Lean.Name := `Tests.Ix.SourceContract.SyntaxFixture

/-- Declarations of the syntax fixture whose binders carry contracts: inputs,
arrow results, λs, and value and borrow lets. -/
def contractSeeds : Array Lean.Name := #[`linear, `unique, `erased, `dependent, `withInstance,
  `localResult, `localUniqueResult, `curriedResult, `dependentArrow, `anonymousArrow,
  `quantified, `nestedLambda, `lambdaDefinition, `localLet, `sharedLoan].map (syntaxModule ++ ·)

abbrev Contracts := List (Ixon.BinderContract × Ixon.ValueContract)

/-- The contracts of a term's binders, in preorder. -/
def contractsOf : Ix.Kernel.Expr → Contracts
  | .lam t b m | .forallE t b m => (m.contract, m.result) :: (contractsOf t ++ contractsOf b)
  | .app f a => contractsOf f ++ contractsOf a
  | .letE t v b => contractsOf t ++ contractsOf v ++ contractsOf b
  | .proj _ _ e | .fvar _ e => contractsOf e
  | _ => []

/-- An installed constant's type's and value's binder contracts. -/
def installedContracts : Ix.Kernel.ConstantInfo → Contracts × Contracts
  | .defnInfo cv v _ => (contractsOf cv.type, contractsOf v)
  | .thmInfo cv v => (contractsOf cv.type, contractsOf v)
  | ci => (contractsOf ci.toConstantVal.type, [])

/-- The resolved syntax fixtures in Source mode and through `Ix.Cert.compile`
and the certified entry: errors, and lines for the report. -/
def contractAgreement (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv (contractSeeds ++ preludeNames))
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv closed)
  let env := Tests.Ix.Kernel.SourceIngressStep.canon prepared.toArray
  let envS ← match Ix.LeanIngress.checkSource env (Ix.Cert.blocksOf env) with
    | .ok envS => pure envS
    | .error e => return (#[s!"Source mode refuses the resolved fixtures: {e}"], lines)
  let ixe ← match Ix.Cert.compile env with
    | .ok ixe => pure ixe
    | .error e => return (#[s!"Ix.Cert.compile failed on the resolved fixtures: {e}"], lines)
  let seeds : Array Address := env.consts.toArray.filterMap fun (n, _) => (ixe.named.get? n).map (·.addr)
  let order := closureOrder ixe seeds
  let records := Ix.Cert.recordsOf ixe order.toList
  let blobs := Ix.Cert.blobsOf ixe order.toList
  let some binding := Ix.Kernel.Admission.defaultBinding.toOption
    | return (#["the default role table does not load"], lines)
  let envA ← match Ixon.Authenticated.checkBytes binding limits records blobs (Ix.Cert.hintsOf ixe) with
    | .ok envA => pure envA
    | .error e => return (#[s!"the certified entry refuses the compiled fixtures: {e}"], lines)
  let some cx := Ix.Cert.admissionContext binding limits ixe order.toList
    | return (#["no admission context"], lines)
  let mut contracted : Array Lean.Name := #[]
  let mut seen : Std.HashMap Lean.Name (Contracts × Contracts) := {}
  for n in contractSeeds do
    let some c := envS.find? (Ix.Kernel.Key.ofName (Ix.Kernel.Name.ofLeanName n))
      | errors := errors.push s!"{n}: not installed in Source mode"
    let some (.const k _) := Ix.Cert.reading ixe cx c
      | errors := errors.push s!"{n}: not read"
    let some ci := envA.find? k
      | errors := errors.push s!"{n}: its reading {k} is not installed"
    let s := installedContracts c
    let a := installedContracts ci
    unless s == a do errors := errors.push s!"{n}: Source {repr s} but Ixon {repr a}"
    if (s.1 ++ s.2).any (· != (.many, .shared)) then contracted := contracted.push n
    seen := seen.insert n s
  -- every declaration keeps a binder contract on both sides except `localLet`,
  -- whose only contract is its `let`'s: erased on both sides, as the checker's
  -- `letE` has no field for it
  let letOnly := syntaxModule ++ `localLet
  unless contracted == contractSeeds.filter (· != letOnly) do
    errors := errors.push s!"declarations that keep a contract: {contracted}"
  -- the resolved contracts themselves
  let expect (n : Lean.Name) (s : Contracts × Contracts) :=
    seen.get? (syntaxModule ++ n) == some s
  unless expect `linear ([(.linear, .shared)], [(.linear, .shared)]) &&
      expect `localUniqueResult
        ([({ uses := .linear, value := .localUnique }, .localUnique)],
          [({ uses := .linear, value := .localUnique }, .shared)]) &&
      expect `anonymousArrow ([(.many, .localUnique)], [(.many, .shared)]) do
    errors := errors.push s!"unexpected contracts: {repr (seen.toList.filter fun (n, _) =>
      [`linear, `localUniqueResult, `anonymousArrow].any (syntaxModule ++ · == n))}"
  lines := lines.push s!"contracts: {env.consts.size} resolved constants; Source accepts them \
    ({envS.consts.length} kernel constants), the certified entry accepts the compile \
    ({envA.consts.length}); {contractSeeds.size} declarations with contracts, each carrying the \
    same contracts on both sides ({contracted.size} keep one; `localLet`'s is a `let`'s)"
  return (errors, lines)

def report (name : String) (action : IO (Array String × Array String)) (count : Nat) : TestSeq :=
  .individualIO name none (do
    let (errors, lines) ← action
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, count, 0, msg)) .done

def suite : List TestSeq := [
  report "Ix.Cert.compile against the IO pipeline and the Rust compiler, on the fixtures" (do
    let leanEnv ← getCompileEnv #[defsModule, ownModule]
    parity "fixtures" (← fixtureConsts leanEnv) 4) 1,
  report "the statements' hypotheses and conclusion, per root, on the accepted fixtures" (do
    perRoot (← getCompileEnv #[defsModule, ownModule])) 1,
  report "binder contracts on both sides, on the resolved source-contract syntax fixtures" (do
    contractAgreement (← getCompileEnv #[syntaxModule])) 1]

/-- `cert-compile-parity-init` (ignored): the parity on `Init`. -/
def initSuite : List TestSeq := [
  report "Ix.Cert.compile against the IO pipeline and the Rust compiler, on Init" (do
    let leanEnv ← getCompileEnv #[`Init]
    parity "Init" leanEnv.constants.toList 6) 1]

end Tests.Ix.Cert.Statement
