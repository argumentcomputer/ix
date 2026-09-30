import CompilatrixTests.Src.Support

/-! The unfolding table on the K1 packs (design note 01 §10 part 2): every
`eqn` proposal of `k1.ixe` and of each bench-k1 closure is accepted, the
`case`, `prim` and `lazy` entries resolve, and each §4.1 check refuses one
mutation while accepting the unmutated input. -/

namespace CompilatrixTests.Src.Table

open Compilatrix Compilatrix.Src Compilatrix.Ixon CompilatrixTests.Src

def withDecl (p : Program) (c : CId) (decl : Decl) : Program :=
  { p with consts := p.consts.modify c fun e => { e with decl } }

/-- Append a constant with a fresh fake address. -/
def withConst (p : Program) (decl : Decl) : Program × CId :=
  let c := p.size
  let a := Builder.fakeAddr (c + 1000000)
  ({ p with consts := p.consts.push { ref := .member a 0, addr := a, decl }
            byAddr := p.byAddr.insert a c }, c)

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

def packCounts (a : Assert) (l : Loaded) (label : String) (eqns : Nat) : IO Unit := do
  let s := l.tableStats
  expectEq a s.eqnAccepted.size eqns s!"{label}: accepted eqn proposals"
  expect a s.eqnRefused.isEmpty s!"{label}: refused eqn proposals {s.eqnRefused.map (·.2)}"
  expect a (l.tableDiags.isEmpty) s!"{label}: table diagnostics {l.tableDiags.map toString}"
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

/-- Each §4.1 check refuses one mutation and accepts the original. -/
def mutations (a : Assert) (l : Loaded) : IO Unit := do
  let p := l.program
  -- eqn: Nat.add.eq_def is `∀ x y, Nat.add x y = …`.
  let (add, addThm) ← eqnNamed l "Nat.add"
  expect a (isOk (Table.checkEqn p add addThm)) "eqn: Nat.add.eq_def accepted"
  let some (.defn kind safety lvls thmTy thmVal) := p.decl? addThm | throw (IO.userError "thm")
  let mutateThm := fun (ty : Term) => withDecl p addThm (.defn kind safety lvls ty thmVal)
  let (binders, body) := thmTy.pis
  let rebuild := fun (bs : Array (Binder × Term)) (b : Term) =>
    bs.foldr (fun (bnd, d) acc => Term.pi bnd {} d acc) b
  match body.spine with
  | (eqHead, #[(ty, m1), (lhs, m2), (rhs, m3)]) =>
    -- Swapped lhs arguments.
    let swapped := match lhs.spine with
      | (f, #[(x, mx), (y, my)]) => Term.mkApps f #[(y, mx), (x, my)]
      | _ => lhs
    let p1 := mutateThm (rebuild binders (Term.mkApps eqHead #[(ty, m1), (swapped, m2), (rhs, m3)]))
    expect a (!isOk (Table.checkEqn p1 add addThm)) "eqn mutation: swapped lhs arguments"
    -- An extra binder.
    let p2 := mutateThm (.pi {} {} (binders[0]!.2) thmTy)
    expect a (!isOk (Table.checkEqn p2 add addThm)) "eqn mutation: extra binder"
    -- A binder type other than the subject's.
    let bs3 := binders.set! 0 (binders[0]!.1, .sort .zero)
    let p3 := mutateThm (rebuild bs3 body)
    expect a (!isOk (Table.checkEqn p3 add addThm)) "eqn mutation: binder type differs"
  | _ => expect a false "eqn: Nat.add.eq_def is not an equation"
  -- Wrong levels, on a universe-polymorphic definition (List.map, 2 levels).
  let (map, mapThm) ← eqnNamed l "List.map"
  expect a (isOk (Table.checkEqn p map mapThm)) "eqn: List.map.eq_def accepted"
  let some (.defn mk ms ml mty mval) := p.decl? mapThm | throw (IO.userError "thm")
  let (mbs, mbody) := mty.pis
  match mbody.spine with
  | (eqHead, #[(ty, m1), (lhs, m2), (rhs, m3)]) =>
    let lhs' := match lhs.spine with
      | (.const f us, args) => Term.mkApps (.const f us.reverse) args
      | _ => lhs
    let ty' := mbs.foldr (fun (bnd, d) acc => Term.pi bnd {} d acc)
      (Term.mkApps eqHead #[(ty, m1), (lhs', m2), (rhs, m3)])
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
    #[(addTy, .strict, .rel), (.const x [], .strict, .rel), (.const y [], .strict, .rel)]
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

def run (a : Assert) : IO Unit := do
  let k1 ← loadK1
  packCounts a k1 "k1.ixe" 40
  expectEq a k1.tableStats.caseAccepted.size 23 "k1.ixe: case entries"
  expectEq a k1.tableStats.primAccepted.size 12 "k1.ixe: prim entries"
  expectEq a k1.tableStats.lazyAccepted.size 11 "k1.ixe: lazy entries"
  mutations a k1
  for (name, eqns, cases) in [("fib", 2, 1), ("sum-loop", 34, 22), ("ackermann", 34, 21),
      ("tak", 5, 5), ("gcd", 7, 9)] do
    let l ← loadBench name
    packCounts a l name eqns
    expectEq a l.tableStats.caseAccepted.size cases s!"{name}: case entries"

end CompilatrixTests.Src.Table
