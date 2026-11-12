import IxCCTests.Src.Support
import IxCC.Src.Table.Cert

/-! The unfolding table on the K1 packs: on ingress's reading (the records the
seeds reach) an `eqn` proposal of `k1.ixe` and of each bench-k1 closure is
accepted exactly when its subject is read, and on every record read (as ingress
read before 2026-11-12) every one is accepted; the `case`, `prim` and `lazy`
entries resolve, and each entry check refuses one mutation while accepting the
unmutated input. -/

namespace IxCCTests.Src.Table

open IxCC IxCC.Src IxCC.Ixon IxCCTests.Src

def withDecl (p : Program) (c : CId) (decl : Decl) : Program :=
  p.setDecl c decl

/-- Append a constant with a fresh fake address. -/
def withConst (p : Program) (decl : Decl) : Program × CId :=
  let c := p.size
  let a := Builder.fakeAddr (c + 1000000)
  (p.push { ref := .member a 0, addr := a, decl }, c)

def isOk : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- The equation proposal named `name` in a pack: `(f, thm)`. -/
def eqnNamed (l : Loaded) (name : String) : IO (CId × CId) := do
  let some prop := l.hints.proposals.find? (·.name? == some name)
    | throw (IO.userError s!"no equation for {name}")
  let some f := l.program.lookup prop.subject | throw (IO.userError s!"{name} absent")
  let some ta := prop.theorem? | throw (IO.userError s!"{name}: no theorem")
  let some thm := l.program.lookup ta | throw (IO.userError s!"{name}: theorem absent")
  return (f, thm)

/-- The pack's `eqn` proposals under ingress's reading (the records the seeds
reach): one is accepted exactly when the program read holds its subject; the
others are `dropped` (by name, in the sidecar's order), and each has the one
diagnostic `Table.notRead`, the only diagnostics there are. -/
def reachedProposals (a : Assert) (l : Loaded) (label : String) (dropped : List String) : IO Unit := do
  let p := l.program
  let eqns := l.hints.proposals.filter (·.kind == .eqn)
  let held := eqns.filter fun prop => (p.lookup prop.subject).isSome
  let unheld := eqns.filter fun prop => (p.lookup prop.subject).isNone
  let accepted := l.tableStats.eqnAccepted.map p.addr
  expect a (held.all fun prop => accepted.contains prop.subject)
    s!"{label}: a proposal whose subject is read is not accepted"
  expectEq a accepted.size held.size s!"{label}: accepted eqn proposals, against those whose subject is read"
  expect a ((unheld.map (·.name?.getD "?")).toList == dropped)
    s!"{label}: proposals whose subject is not read {unheld.map (·.name?)}, expected {dropped}"
  expectEq a l.tableDiags.size unheld.size s!"{label}: table diagnostics {l.tableDiags.map toString}"
  expect a (l.tableDiags.all fun d => (d.message.splitOn Table.notRead).length > 1 &&
      unheld.any fun prop => d.addr == some prop.subject)
    s!"{label}: a diagnostic other than a subject not read: {l.tableDiags.map toString}"

/-- The table on every record of the pack read with proofs (`Ingress.readAll`),
as ingress read before it read only what the seeds reach. -/
def fullStats (l : Loaded) : IO (Array Diag × Table.Stats) := do
  let full ← IO.ofExcept (Ingress.readAll l.env (l.hints.roots.map (·.1)))
  let full := { full with known := { pins := KernelFront.pinsOfTable l.kernel.acc.table } }
  let full := { full with known := Pinned.known full, resource := l.hints.resource }
  let (_, d, s) := Table.build {} full l.hints.proposals
  return (d, s)

/-- On every record read, every `eqn` proposal of the sidecar is accepted
(every equation `ix compile` exports is acceptable), with no diagnostic, and
the pack has `cases` case entries. -/
def fullCounts (a : Assert) (l : Loaded) (label : String) (eqns cases : Nat) : IO Table.Stats := do
  let (d, s) ← fullStats l
  expectEq a s.eqnAccepted.size eqns s!"{label}, every record read: accepted eqn proposals"
  expectEq a s.eqnAccepted.size (l.hints.proposals.filter (·.kind == .eqn)).size
    s!"{label}, every record read: proposals not all accepted"
  expect a (s.eqnRefused.isEmpty && d.isEmpty)
    s!"{label}, every record read: refused {s.eqnRefused.map (·.2)}, diagnostics {d.map toString}"
  expectEq a s.caseAccepted.size cases s!"{label}, every record read: case entries"
  return s

def packCounts (a : Assert) (l : Loaded) (label : String) (eqns : Nat) (dropped : List String) :
    IO Unit := do
  let s := l.tableStats
  expectEq a s.eqnAccepted.size eqns s!"{label}: accepted eqn proposals"
  expect a s.eqnRefused.isEmpty s!"{label}: refused eqn proposals {s.eqnRefused.map (·.2)}"
  reachedProposals a l label dropped
  -- The pinned Nat.casesOn resolves as a case entry.
  if let some cases := l.program.lookup (Pinned.constAddr "Nat.casesOn") then
    match l.program.table.resolveOf cases with
    | some (.case r) =>
      let natRec := l.program.lookup (Pinned.constAddr "Nat.rec")
      expect a (some r == natRec) s!"{label}: Nat.casesOn resolves to Nat.rec"
    | _ => expect a false s!"{label}: Nat.casesOn is not a case entry"
  -- Every pinned primitive present resolves as a primitive.
  for (op, _, hex) in Pinned.primRows do
    if let some c := l.program.lookup (Pinned.addr hex) then
      match l.program.table.resolveOf c with
      | some (.prim op') => expect a (op == op') s!"{label}: {op.name} resolves to {op'.name}"
      | _ => expect a false s!"{label}: {op.name} is not a prim entry"

/-- Each entry check refuses one mutation and accepts the original. -/
def mutations (a : Assert) (l : Loaded) : IO Unit := do
  let p := l.program
  -- eqn: Nat.add.eq_def is `∀ x y, Nat.add x y = …`.
  let (add, addThm) ← eqnNamed l "Nat.add"
  expect a (isOk (Table.checkEqn p add addThm)) "eqn: Nat.add.eq_def accepted"
  let some (.defn kind safety lvls thmTy thmVal) := p.decl? addThm | throw (IO.userError "thm")
  let mutateThm := fun (ty : Term) => withDecl p addThm (.defn kind safety lvls ty thmVal)
  let (binders, body) := thmTy.pis
  let rebuild := fun (bs : List (Binder × Term)) (b : Term) =>
    bs.foldr (fun (bnd, d) acc => Term.pi bnd {} d acc) b
  match body.spine with
  | (eqHead, [(ty, m1), (lhs, m2), (rhs, m3)]) =>
    -- Swapped lhs arguments.
    let swapped := match lhs.spine with
      | (f, [(x, mx), (y, my)]) => Term.mkApps f [(y, mx), (x, my)]
      | _ => lhs
    let p1 := mutateThm (rebuild binders (Term.mkApps eqHead [(ty, m1), (swapped, m2), (rhs, m3)]))
    expect a (!isOk (Table.checkEqn p1 add addThm)) "eqn mutation: swapped lhs arguments"
    -- An extra binder.
    let p2 := mutateThm (.pi {} {} (binders[0]!.2) thmTy)
    expect a (!isOk (Table.checkEqn p2 add addThm)) "eqn mutation: extra binder"
    -- A binder type other than the subject's.
    let bs3 := binders.set 0 (binders[0]!.1, .sort .zero)
    let p3 := mutateThm (rebuild bs3 body)
    expect a (!isOk (Table.checkEqn p3 add addThm)) "eqn mutation: binder type differs"
  | _ => expect a false "eqn: Nat.add.eq_def is not an equation"
  -- Wrong levels, on a universe-polymorphic definition (List.map, 2 levels).
  let (map, mapThm) ← eqnNamed l "List.map"
  expect a (isOk (Table.checkEqn p map mapThm)) "eqn: List.map.eq_def accepted"
  let some (.defn mk ms ml mty mval) := p.decl? mapThm | throw (IO.userError "thm")
  let (mbs, mbody) := mty.pis
  match mbody.spine with
  | (eqHead, [(ty, m1), (lhs, m2), (rhs, m3)]) =>
    let lhs' := match lhs.spine with
      | (.const f us, args) => Term.mkApps (.const f us.reverse) args
      | _ => lhs
    let ty' := mbs.foldr (fun (bnd, d) acc => Term.pi bnd {} d acc)
      (Term.mkApps eqHead [(ty, m1), (lhs', m2), (rhs, m3)])
    let p4 := withDecl p mapThm (.defn mk ms ml ty' mval)
    expect a (!isOk (Table.checkEqn p4 map mapThm)) "eqn mutation: wrong levels"
  | _ => expect a false "eqn: List.map.eq_def is not an equation"
  -- A body outside the Lean fragment (a written erased binder).
  match p.decl? add with
  | some (.defn k s n t (.lam b d body)) =>
    let p5 := withDecl p add (.defn k s n t (.lam { b with contract := .erased } d body))
    match Table.checkEqn p5 add addThm with
    | .error msg => expect a (msg.startsWith "eqn-drops-contracts") s!"eqn mutation: {msg}"
    | .ok _ => expect a false "eqn mutation: non-leanFragment body accepted"
  | _ => expect a false "eqn: Nat.add's value is not a λ"
  -- csimp: `@f = @g` accepted, the reversed equation refused.
  let some eq := p.known.eq | throw (IO.userError "Eq absent")
  let some (.defn _ _ _ addTy addVal) := p.decl? add | throw (IO.userError "Nat.add")
  let (pg, g) := withConst p (.defn .defn .safe 0 addTy addVal)
  let csimpTy := fun (x y : CId) => Term.mkApps (.const eq [.succ .zero])
    [(addTy, .strict, .rel), (.const x [], .strict, .rel), (.const y [], .strict, .rel)]
  let (pc, fwd) := withConst pg (.defn .thm .safe 0 (csimpTy add g) (.natLit 0))
  let (pc, rev) := withConst pc (.defn .thm .safe 0 (csimpTy g add) (.natLit 0))
  expect a (isOk (Table.checkCsimp pc add g fwd)) "csimp: @f = @g accepted"
  expect a (!isOk (Table.checkCsimp pc add g rev)) "csimp mutation: reversed equation"
  -- case: Nat.casesOn accepted; a minor wrapper with a wrong IH count refused.
  let some cases := p.lookup (Pinned.constAddr "Nat.casesOn") | throw (IO.userError "casesOn")
  expect a (isOk (Table.checkCase p cases)) "case: Nat.casesOn accepted"
  match p.decl? cases with
  | some (.defn k s n t v) =>
    let (bs, body) := v.lams
    let (head, args) := body.spine
    -- The succ wrapper is argument 3 (params 0, motive, zero wrapper, succ wrapper, major).
    let args' := args.modify 3 fun (w, m) => match w with
      | .lam _ _ inner => (inner, m)
      | other => (Term.lam {} (.sort .zero) other, m)
    let v' := bs.foldr (fun (b, d) acc => Term.lam b d acc) (Term.mkApps head args')
    expect a (!isOk (Table.checkCase (withDecl p cases (.defn k s n t v')) cases))
      "case mutation: wrong IH count"
  | _ => expect a false "case: Nat.casesOn is not a definition"
  -- prim: Nat.add accepted at its type; refused at a mutated type.
  expect a (isOk (Table.checkPrim p add .add PrimOp.all)) "prim: Nat.add accepted"
  expect a (!isOk (Table.checkPrim p add .add [.sub])) "prim: an unconfigured op refused"
  match p.decl? add with
  | some (.defn k s n (.pi b r d _) v) =>
    expect a (!isOk (Table.checkPrim (withDecl p add (.defn k s n (.pi b r d d) v)) add .add PrimOp.all))
      "prim mutation: wrong type"
  | _ => expect a false "prim: Nat.add's type is not a Π"
  -- lazy: arity within the λs accepted, beyond refused.
  let lazyIds := l.tableStats.lazyAccepted
  match lazyIds[0]? with
  | some f =>
    let arity := (p.table.lazyOf f).getD 1
    expect a (isOk (Table.checkLazy p f arity)) "lazy: pinned row accepted"
    let lams := ((p.decl? f).map fun d => match d with
      | .defn _ _ _ _ v => v.lamCount
      | _ => 0).getD 0
    expect a (!isOk (Table.checkLazy p f (lams + 1))) "lazy mutation: arity beyond the λs"
  | none => expect a false "lazy: no accepted rows"

/-- Regressions for N7 (`checkAxiomClosure` across `.induct`/`.recr`) and N10 (`checkJsonText`
depth/size bounds). -/
def regressions (a : Assert) (l : Loaded) : IO Unit := do
  let p := l.program
  let (_, addThm) ← eqnNamed l "Nat.add"
  -- N7: `checkAxiomClosure` accepts `Nat.add.eq_def`, and rejects a non-standard axiom
  -- reachable behind an `.induct` or `.recr` declaration.
  expect a (isOk (Table.checkAxiomClosure p addThm)) "N7: Nat.add.eq_def axiom closure accepted"
  let (pAx, badAx) := withConst p (.axio false 0 (.sort .zero))
  let (pInd, indId) := withConst pAx (.induct true 0 0 0 (.sort (.succ .zero)) [badAx])
  let (pIndThm, indThm) := withConst pInd (.defn .thm .safe 0 (.const indId []) (.natLit 0))
  expect a (!isOk (Table.checkAxiomClosure pIndThm indThm))
    "N7: non-standard axiom behind .induct ctors rejected by checkAxiomClosure"
  let badRule : Rule := { ctor := badAx, fields := 0, rhs := .natLit 0 }
  let (pRec, recId) := withConst pAx (.recr true false 1 0 1 1 0 0 [badRule] (.sort .zero))
  let (pRecThm, recThm) := withConst pRec (.defn .thm .safe 0 (.sort .zero) (.const recId [.zero]))
  expect a (!isOk (Table.checkAxiomClosure pRecThm recThm))
    "N7: non-standard axiom behind .recr rules rejected by checkAxiomClosure"
  -- N10: `Hints.checkJsonText` rejects nesting > 512 and accepts nesting ≤ 512.
  let okDepth := String.ofList (List.replicate 512 '[') ++ String.ofList (List.replicate 512 ']')
  let badDepth := String.ofList (List.replicate 513 '[') ++ String.ofList (List.replicate 513 ']')
  let quotedBrackets := "\"" ++ String.ofList (List.replicate 600 '[') ++ "\""
  expect a (isOk (Hints.checkJsonText okDepth)) "N10: JSON nesting depth 512 accepted"
  expect a (!isOk (Hints.checkJsonText badDepth)) "N10: JSON nesting depth 513 rejected"
  expect a (isOk (Hints.checkJsonText quotedBrackets)) "N10: quoted brackets do not increase JSON depth"

/-! ## Sparse casesOn: `lazy` rows by shape (`Table.checkSparseCases`)

On the committed fixture `phase2-closures/sparse`, whose roots match with a
catch-all on a list, an option, an enumeration and a nested pattern. -/

def sparseDir : System.FilePath := "fixtures/corpus/phase2-closures"

def loadSparse : IO Loaded :=
  loadPack (sparseDir / "sparse.ixe") (sparseDir / "sparse.equations.json")

/-- The constant of the root the sidecar names `name`. -/
def rootId (l : Loaded) (name : String) : IO CId := do
  let some (addr, _) := l.hints.roots.find? (·.2 == some name)
    | throw (IO.userError s!"no root {name}")
  let some c := l.program.lookup addr | throw (IO.userError s!"{name} absent")
  return c

/-- The head constant of a definition's body under its λs. -/
def headOf (p : Program) (c : CId) : IO CId := do
  let some (.defn _ _ _ _ v) := p.decl? c | throw (IO.userError s!"c{c} is not a definition")
  let .const h _ := v.lams.2.spine.1 | throw (IO.userError s!"c{c}'s body has no constant head")
  return h

/-- The field counts of the rules of the recursor heading `c`'s body. -/
def ruleFields (p : Program) (c : CId) : List Nat :=
  match p.decl? c with
  | some (.defn _ _ _ _ v) =>
    match v.lams.2.spine.1 with
    | .const r _ =>
      match p.decl? r with
      | some (.recr _ _ _ _ _ _ _ _ rules _) => rules.map (·.fields)
      | _ => []
    | _ => []
  | _ => []

/-- `c` with its body's spine arguments rewritten by `f`. -/
def mutateArgs (p : Program) (c : CId) (f : List Term.Arg → List Term.Arg) : Program :=
  match p.decl? c with
  | some (.defn k s n t v) =>
    let (bs, body) := v.lams
    let (head, args) := body.spine
    withDecl p c (.defn k s n t
      (bs.foldr (fun (b, d) acc => Term.lam b d acc) (Term.mkApps head (f args))))
  | _ => p

/-- Argument `i` of a spine replaced by `t`. -/
def setArg (i : Nat) (t : Term) (args : List Term.Arg) : List Term.Arg :=
  args.modify i fun (_, m, r) => (t, m, r)

/-- A minor `λ ws. _` with its body replaced by `t`. -/
def reMinor (minor t : Term) : Term :=
  minor.lams.1.foldr (fun (b, d) acc => Term.lam b d acc) t

def refusedWith {α : Type} (r : Except String α) (prefix_ : String) : Bool :=
  match r with
  | .error m => m.startsWith prefix_
  | .ok _ => false

/-- The sparse casesOn of the fixture get `lazy` rows at their binder count,
which every route that checks a row accepts; their mutations, an ordinary
definition with a sparse casesOn's name, and a hinted row for an ordinary
definition are refused. -/
def sparseCases (a : Assert) (count : Nat) : IO Unit := do
  let l ← loadSparse
  let p := l.program
  let sparse := l.tableStats.sparseAccepted
  expectEq a sparse.size count "sparse.ixe: sparse casesOn given a lazy row"
  expect a l.tableDiags.isEmpty s!"sparse.ixe: table diagnostics {l.tableDiags.map toString}"
  for c in sparse do
    let arity := (p.table.lazyOf c).getD 0
    expect a (match Table.checkSparseCases p c with | .ok b => b == arity | .error _ => false)
      s!"sparse c{c}: the row's arity {arity} is the binder count"
    expect a (isOk (Table.checkLazy p c arity)) s!"sparse c{c}: checkLazy accepts its row"
    expect a (refusedWith (Table.checkLazy p c (arity - 1))
      s!"lazy: not a pinned row, and a sparse casesOn of {arity} binders, not {arity - 1}")
      s!"sparse c{c}: refused at a smaller arity"
  -- `l.program` is after `Lazify` (its `eqn` bodies carry by-name modes), so the
  -- table is rebuilt from the sidecar and checked on the program, as the
  -- producer does before the annotation.
  let (t0, _, _) := Table.build {} p l.hints.proposals
  let p0 := { p with table := t0 }
  expect a (t0.lazy.toList == p.table.lazy.toList) "sparse.ixe: the rebuilt table has the same lazy rows"
  match Table.validate {} p0, Table.ofCert {} p0 (Table.TableCert.ofTable t0) with
  | .ok (), .ok _ => expect a true "sparse.ixe: Table.validate and Table.ofCert accept the built table"
  | .error m, _ | _, .error m => expect a false s!"sparse.ixe: the built table refused: {m}"
  -- The roots' matchers reach the sparse casesOn of List, Option and Color.
  for (name, fields) in [("Sparse.minS", [0, 2]), ("Sparse.minO", [0, 1]), ("Sparse.minE", [0, 0, 0])] do
    expect a (sparse.any fun c => ruleFields p c == fields) s!"{name}: a sparse casesOn over rules {fields}"
  -- An ordinary function named as a sparse casesOn is (`Sparse.mimic._sparseCasesOn_1`,
  -- the head of `Sparse.minM`): no row, and a row for it is refused.
  let mimic ← headOf p (← rootId l "Sparse.minM")
  expect a (p.table.lazyOf mimic).isNone "mimic._sparseCasesOn_1: no lazy row"
  expect a (refusedWith (Table.checkLazy p mimic 2) "lazy: not a pinned row, and not a sparse casesOn")
    "mimic._sparseCasesOn_1: a lazy row refused"
  -- A hinted row for an ordinary definition is refused, with a diagnostic.
  let minS ← rootId l "Sparse.minS"
  let (t, diags, _) := Table.build {} p
    #[{ kind := .lazy, subject := p.addr minS, arity? := some 2, name? := some "Sparse.minS" }]
  expect a ((t.lazyOf minS).isNone && diags.any fun d => d.addr == some (p.addr minS) &&
      d.message.startsWith "lazy: not a pinned row, and not a sparse casesOn")
    "a hinted lazy row for Sparse.minS refused"
  -- Mutations of the enumeration's sparse casesOn (`λ motive major arm`, three
  -- minors, the first the arm's): the arm applied by two minors.
  let some colour := sparse.find? (ruleFields p · == [0, 0, 0]) | throw (IO.userError "no Color casesOn")
  let cArity := (p.table.lazyOf colour).getD 0
  let twice := mutateArgs p colour fun args => setArg 2 ((args[1]?.map (·.1)).getD (.natLit 0)) args
  expect a (refusedWith (Table.checkSparseCases twice colour)
    "sparse: the named constructors' minors do not apply each arm once") "mutation: one arm in two minors"
  expect a (!isOk (Table.checkLazy twice colour cArity)) "mutation: one arm in two minors, its row refused"
  -- Mutations of the list's (`λ α motive t nil`: binder 2 the major; minors 2
  -- (nil, the arm's) and 3 (cons, the catch-all)).
  let some list := sparse.find? (ruleFields p · == [0, 2]) | throw (IO.userError "no List casesOn")
  let lArity := (p.table.lazyOf list).getD 0
  expectEq a lArity 4 "List's sparse casesOn: four binders"
  -- Its row beside a `resolve` entry that replaces its value (`csimp list g thm`,
  -- valid on its own) is refused by `validate` and `ofCert`; the entry alone is not.
  let some (pc, g, thm) := withCsimpTwin p0 list | throw (IO.userError "no csimp twin")
  let us := match pc.decl? list with
    | some (.defn _ _ n _ _) => Table.paramUnivs n
    | _ => []
  let pairedMsg := s!"table entry of constant {list}: lazy: a sparse casesOn's row beside a resolve entry"
  let paired := { pc with table := { t0 with resolve := t0.resolve.insert list (.csimp g us thm) } }
  expect a (refusedWith (Table.validate {} paired) pairedMsg) "validate: a sparse row beside a csimp entry refused"
  let cert0 := Table.TableCert.ofTable t0
  let certPaired := { cert0 with resolve := (list, .csimp g thm) :: cert0.resolve }
  expect a (refusedWith (Table.ofCert {} pc certPaired) pairedMsg) "ofCert: a sparse row beside a csimp entry refused"
  expect a (isOk (Table.ofCert {} pc { certPaired with lazy := cert0.lazy.filter (·.1 != list) }))
    "ofCert: the csimp entry without the row accepted"
  -- the major also in a value position of the motive (`λ t'. t`): used twice
  let majorTwice := mutateArgs p list (setArg 1 (.lam {} (.sort .zero) (.var 2)))
  expect a (refusedWith (Table.checkSparseCases majorTwice list) "sparse: binder 2 is used more than once")
    "mutation: the major used twice"
  expect a (!isOk (Table.checkLazy majorTwice list lArity)) "mutation: the major used twice, its row refused"
  let consMinor := fun (args : List Term.Arg) => (args[3]?.map (·.1)).getD (.natLit 0)
  -- the catch-all's minor returning `else` itself, and applying it to the major
  let noProof := mutateArgs p list fun args => setArg 3 (reMinor (consMinor args) (.var 0)) args
  let openProof := mutateArgs p list fun args =>
    setArg 3 (reMinor (consMinor args) (.app (.var 0) (.var 5) .strict .rel)) args
  for (label, q) in [("the catch-all without its proof", noProof),
      ("the catch-all applied to the major", openProof)] do
    expect a (refusedWith (Table.checkSparseCases q list)
      "sparse: minor 1 is neither an arm on its fields nor the catch-all on a proof") s!"mutation: {label}"
    expect a (!isOk (Table.checkLazy q list lArity)) s!"mutation: {label}, its row refused"

/-- The counts the expectations below state, as observed (printed before they
are checked, so a regeneration that moves them shows every new value at once:
the expectations are reviewed literals, updated by hand). -/
def observedStats (label : String) (s : Table.Stats) : String :=
  s!"{label}: eqn {s.eqnAccepted.size}, case {s.caseAccepted.size}, prim {s.primAccepted.size}, lazy {s.lazyAccepted.size}, sparse casesOn {s.sparseAccepted.size}"

/-- Both readings' counts: the records the seeds reach (ingress's) and every
record (`fullStats`). -/
def observed (label : String) (l : Loaded) : IO String := do
  let (_, full) ← fullStats l
  return s!"{observedStats label l.tableStats}; every record read: {observedStats label full}"

/-- The proposals k1's sidecar makes for definitions none of its roots reaches
(each bench closure carries the whole sidecar of its source). -/
def unreachedK1 : List String :=
  ["Char.utf8Size", "Lean.Name.sizeOf", "List.filter", "List.getLast", "List.hasDecEq"]

def run (a : Assert) : IO Unit := do
  let k1 ← loadK1
  IO.println (← observed "k1.ixe" k1)
  for name in ["fib", "sum-loop", "ackermann", "tak", "gcd"] do
    IO.println (← observed name (← loadBench name))
  -- ingress's reading: the proposals on what the roots reach
  packCounts a k1 "k1.ixe" 41 unreachedK1
  expectEq a k1.tableStats.caseAccepted.size 23 "k1.ixe: case entries"
  expectEq a k1.tableStats.primAccepted.size 14 "k1.ixe: prim entries"
  expectEq a k1.tableStats.lazyAccepted.size 12 "k1.ixe: lazy entries"
  expectEq a k1.tableStats.sparseAccepted.size 2 "k1.ixe: sparse casesOn"
  -- every record read: every proposal accepted, the counts before ingress read what the seeds reach
  let full ← fullCounts a k1 "k1.ixe" 46 94
  expectEq a full.primAccepted.size 14 "k1.ixe, every record read: prim entries"
  expectEq a full.lazyAccepted.size 15 "k1.ixe, every record read: lazy entries"
  expectEq a full.sparseAccepted.size 3 "k1.ixe, every record read: sparse casesOn"
  -- a proposal whose subject is not in the artifact at all: the same diagnostic
  let absent := Builder.fakeAddr 4242424
  let (_, absentDiags, _) := Table.build {} k1.program
    #[{ kind := .eqn, subject := absent, theorem? := some absent, name? := some "absent" }]
  expect a (!k1.env.consts.contains absent && absentDiags.any fun d =>
      d.addr == some absent && (d.message.splitOn Table.notRead).length > 1)
    s!"an equation whose subject is absent from the artifact: {absentDiags.map toString}"
  mutations a k1
  regressions a k1
  IO.println (← observed "sparse" (← loadSparse))
  sparseCases a 3
  for (name, eqns, cases, dropped, fullEqns, fullCases) in
      [("fib", 3, 1, ([] : List String), 3, 16), ("sum-loop", 35, 22, unreachedK1, 40, 93),
       ("ackermann", 35, 21, unreachedK1, 40, 91), ("tak", 7, 5, ([] : List String), 7, 21),
       ("gcd", 9, 9, ["Nat.div.go"], 10, 23)] do
    let l ← loadBench name
    packCounts a l name eqns dropped
    expectEq a l.tableStats.caseAccepted.size cases s!"{name}: case entries"
    let _ ← fullCounts a l name fullEqns fullCases

end IxCCTests.Src.Table
