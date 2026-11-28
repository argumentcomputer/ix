import IxCC.Own.Plain.Check

/-! # `programDomain`'s set forms against the list forms

`Own.Plain.programDomain` and `contractProgramDomain` check every numbered function's parameters
and body scope with the set forms of `Own/Plain/ScopeSet.lean` (`freshSet`, `scopeOkSet`, with
`signatureArity`); `programDomain_eq_list` proves them equal to their former definitions over the
list forms (`fresh`, `scopeOk`, with `signatures`), written out here as the independent reference.
On each program given (`tests-own-owned` passes every corpus root, then `synthetic`'s programs):
both domains, the set and list forms function by function, and one ill-scoped (or, for two kinds,
well-scoped) edit per kind per function, at its first site. Every edit must get the same verdict
from both forms; each refusal kind must be refused somewhere and each acceptance kind accepted.
On every program and every edited program, the zero-RC route's former check of the canonical map
(`checkContractPlainMap F (canonical F).bodies`) must equal the domain and pins alone, which
`Recheck.Artifact.checkContractOwn` now runs (`checkContractPlainMap_canonical`). -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned.ScopeSet

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var Arg)

/-- The list form: `programDomain`'s definition before the set forms. -/
def listDomainWith (dom : Fir.Fun → Bool) (P : Fir.Program) : Bool :=
  (List.range P.size).all fun f =>
    match P.fun? f with
    | none => false
    | some fd => dom fd && fresh [] (fd.params.map (·.1)) &&
        scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body

def listFun (P : Fir.Program) (fd : Fir.Fun) : Bool :=
  fresh [] (fd.params.map (·.1)) && scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body

def setFun (P : Fir.Program) (fd : Fir.Fun) : Bool :=
  freshSet .leaf (fd.params.map (·.1)) && scopeOkSet P (insertVars .leaf (fd.params.map (·.1))) [] fd.body

mutual
/-- Apply `edit` at the first node (preorder) it accepts. -/
partial def editFirst (edit : Fir.Code → Option Fir.Code) (c : Fir.Code) : Option Fir.Code :=
  match edit c with
  | some c' => some c'
  | none =>
    match c with
    | .bind x r k => (editFirst edit k).map (.bind x r ·)
    | .jp j ps rec b k =>
      match editFirst edit b with
      | some b' => some (.jp j ps rec b' k)
      | none => (editFirst edit k).map (.jp j ps rec b ·)
    | .case x alts d =>
      match editAlts edit alts with
      | some alts' => some (.case x alts' d)
      | none =>
        match d with
        | some dc => (editFirst edit dc).map fun dc' => .case x alts (some dc')
        | none => none
    | _ => none
partial def editAlts (edit : Fir.Code → Option Fir.Code) : List Fir.Alt → Option (List Fir.Alt)
  | [] => none
  | .mk key b :: rest =>
    match editFirst edit b with
    | some b' => some (.mk key b' :: rest)
    | none => (editAlts edit rest).map (.mk key b :: ·)
end

def zeros (n : Nat) : List Arg := List.replicate n (.lit (.nat 0))

/-- The kinds whose edits both forms must accept (the others are ill-scoped). -/
def acceptKinds : List String := ["callGood", "selfJumpRec"]

/-- One edit of `fd` per kind, at its first site; `v` is a variable no binder of `fd` uses. -/
def edits (F : Fir.Program) (fd : Fir.Fun) : List (String × Option Fir.Fun) :=
  let v := fd.vars + 1
  let ps := fd.params.map (·.1)
  let body (e : Fir.Code → Option Fir.Code) : Option Fir.Fun :=
    (editFirst e fd.body).map fun b => { fd with body := b }
  let g? := (List.range F.size).find? fun g => (F.fun? g).isSome
  let gArity := (g?.bind fun g => (F.fun? g).map (·.arity)).getD 0
  [ ("useBeforeBind", body fun | .bind x r k => some (.bind v (.arg (.var x)) (.bind x r k)) | _ => none),
    ("rebind", body fun | .bind x r k => some (.bind x r (.bind x (.arg (.var x)) k)) | _ => none),
    ("bindParam", ps.head?.map fun p => { fd with body := .bind p (.arg (.lit (.nat 0))) fd.body }),
    ("dupParam", ps.head?.map fun p => { fd with params := fd.params ++ [(p, .tobj)] }),
    ("unboundRet", some { fd with body := .ret (.var v) }),
    ("unboundCase", body fun | .case _ alts d => some (.case v alts d) | _ => none),
    ("unboundProj", body fun | .bind x (.proj _ c i) k => some (.bind x (.proj v c i) k) | _ => none),
    ("unboundArg", body fun
      | .bind x (.call f (_ :: as)) k => some (.bind x (.call f (.var v :: as)) k)
      | .bind x (.ctor c (_ :: as)) k => some (.bind x (.ctor c (.var v :: as)) k)
      | .bind x (.prim p (_ :: as)) k => some (.bind x (.prim p (.var v :: as)) k)
      | .tcall f (_ :: as) => some (.tcall f (.var v :: as))
      | .jmp j (_ :: as) => some (.jmp j (.var v :: as))
      | _ => none),
    ("callArityPlus", body fun
      | .bind x (.call f as) k => some (.bind x (.call f (as ++ zeros 1)) k)
      | .tcall f as => some (.tcall f (as ++ zeros 1))
      | _ => none),
    ("callArityMinus", body fun
      | .bind x (.call f (_ :: as)) k => some (.bind x (.call f as) k)
      | .tcall f (_ :: as) => some (.tcall f as)
      | _ => none),
    ("callUnknown", some { fd with body := .bind v (.call (F.size + 3) []) fd.body }),
    ("callGood", g?.map fun g => { fd with body := .bind v (.call g (zeros gArity)) fd.body, vars := v + 1 }),
    ("callWrongArity", g?.map fun g => { fd with body := .bind v (.call g (zeros (gArity + 1))) fd.body }),
    ("jumpArity", body fun | .jmp j as => some (.jmp j (as ++ zeros 1)) | _ => none),
    ("jumpUnknown", body fun | .jmp j as => some (.jmp (j + 100000) as) | _ => none),
    ("dupJoin", body fun | .jp j ps' rec b k => some (.jp j ps' rec b (.jp j [] false .trap k)) | _ => none),
    ("joinParamLive", body fun
      | .jp j ps' rec b k => ps.head?.map fun p => .jp j (ps' ++ [p]) rec b k
      | _ => none),
    ("joinParamDup", body fun
      | .jp j (q :: ps') rec b k => some (.jp j (q :: q :: ps') rec b k)
      | _ => none),
    ("selfJumpNonRec", body fun | .jp j ps' _ _ k => some (.jp j ps' false (.jmp j (zeros ps'.length)) k) | _ => none),
    ("selfJumpRec", body fun | .jp j ps' _ _ k => some (.jp j ps' true (.jmp j (zeros ps'.length)) k) | _ => none) ]

structure Tally where
  programs : Nat := 0
  functions : Nat := 0
  mutants : Nat := 0
  accepted : Nat := 0
  refused : Nat := 0
  /-- kind, mutants, accepted, refused -/
  byKind : List (String × Nat × Nat × Nat) := []
  failures : Array String := #[]
  /-- Programs (and edited programs) on which the zero-RC route's check of the canonical map
  (`checkContractPlainMap F (canonical F).bodies`) was compared with the domain and pins alone. -/
  canonical : Nat := 0

def Tally.fail (t : Tally) (msg : String) : Tally := { t with failures := t.failures.push msg }

def Tally.kind (t : Tally) (k : String) (acc : Bool) : Tally :=
  let a := if acc then 1 else 0
  if t.byKind.any (·.1 == k) then
    { t with byKind := t.byKind.map fun (k', n, x, r) =>
        if k' == k then (k', n + 1, x + a, r + (1 - a)) else (k', n, x, r) }
  else { t with byKind := t.byKind ++ [(k, 1, a, 1 - a)] }

/-- The zero-RC route's check of the canonical map (`checkContractPlainMap F (canonical F).bodies`,
the canonical map computed and compared with itself) against the domain and pins alone, which
`Recheck.Artifact.checkContractOwn` now runs (`checkContractPlainMap_canonical`). -/
def canonicalAgrees (t : Tally) (label : String) (F : Fir.Program) : Tally :=
  let old := checkContractPlainMap F (Program.canonical F).bodies
  let new := contractProgramDomain F && checkBoolPins F
  let t := { t with canonical := t.canonical + 1 }
  if old != new then t.fail s!"{label}: the canonical map's check {old}, the domain and pins {new}"
  else t

/-- Both forms on `F`, function by function, and on one edit per kind per function; on each, the
zero-RC route's two checks (`canonicalAgrees`). -/
def checkProgram (t : Tally) (label : String) (F : Fir.Program) : Tally := Id.run do
  let mut t := { t with programs := t.programs + 1 }
  let ld := listDomainWith funDomain F; let lc := listDomainWith contractFunDomain F
  if programDomain F != ld || contractProgramDomain F != lc then
    t := t.fail s!"{label}: programDomain {programDomain F} (list form {ld}), contractProgramDomain {contractProgramDomain F} (list form {lc})"
  t := canonicalAgrees t label F
  for f in List.range F.size do
    let some fd := F.fun? f | continue
    t := { t with functions := t.functions + 1 }
    if listFun F fd != setFun F fd then
      t := t.fail s!"{label} f{f}: list form {listFun F fd}, set form {setFun F fd}"
    for (kind, m?) in edits F fd do
      let some fd' := m? | continue
      let F' := { F with funs := F.funs.insert f fd' }
      let a := listFun F' fd'
      t := { t with mutants := t.mutants + 1 }
      t := t.kind kind a
      if a then t := { t with accepted := t.accepted + 1 } else t := { t with refused := t.refused + 1 }
      if a != setFun F' fd' || listDomainWith funDomain F' != programDomain F' ||
          listDomainWith contractFunDomain F' != contractProgramDomain F' then
        t := t.fail s!"{label} f{f} {kind}: the forms differ (function: list {a}, set {setFun F' fd'})"
      t := canonicalAgrees t s!"{label} f{f} {kind}" F'
  return t

/-! ## Synthetic programs -/

def fun1 (params : List Var) (body : Fir.Code) (vars : Nat) : Fir.Fun :=
  { (default : Fir.Fun) with params := params.map (·, .tobj), body, vars }

def prog (fs : List Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofList (fs.zipIdx.map fun (f, i) => (i, f)), size := fs.length,
    exports := [0], ctors := [], known := {} }

/-- A binary tree of `case x` with `k` leaves, leaves numbered from `base`. -/
def tree (x : Var) (leaf : Nat → Fir.Code) : Nat → Nat → Nat → Fir.Code
  | 0, base, _ => leaf base
  | fuel + 1, base, k =>
    if k ≤ 1 then leaf base
    else
      let h := k / 2
      .case x [.mk default (tree x leaf fuel base h), .mk default (tree x leaf fuel (base + h) (k - h))] none

/-- `G` functions of `P + 1` parameters, each a join capturing them jumped to from `K` leaves of
a `case` tree on the last; then one function making `K` calls of the last numbered function
(`G + 1`, no parameter). -/
def synthProgram (P K G : Nat) : Fir.Program :=
  let fan : Fir.Code := .jp 0 [] false .trap (tree P (fun _ => .jmp 0 []) 64 0 K)
  let calls := (List.range K).foldr (fun i k => Fir.Code.bind (P + 1 + i) (.call (G + 1) []) k) (.ret (.var P))
  prog (List.replicate G (fun1 (List.range (P + 1)) fan (P + 1)) ++
    [fun1 (List.range (P + 1)) calls (P + 1 + K), fun1 [] (.ret (.lit (.nat 0))) 0])

/-- The synthetic programs, and a call of a numbered entry past `size` (no arity in either form:
both must refuse it). -/
def synthetic (t : Tally) : Tally := Id.run do
  let mut t := t
  for (P, K, G) in [(0, 1, 1), (8, 9, 3), (64, 33, 2), (2048, 3, 2)] do
    t := checkProgram t s!"synthetic {P} {K} {G}" (synthProgram P K G)
  let F := synthProgram 4 2 1
  let past : Fir.Program := { F with funs := F.funs.insert F.size (fun1 [] .trap 0) }
  let callPast : Fir.Fun := fun1 [0] (.bind 1 (.call F.size []) (.ret (.var 1))) 2
  let F' : Fir.Program := { past with funs := past.funs.insert 0 callPast }
  if listFun F' callPast || setFun F' callPast then
    t := t.fail s!"a call of an entry past size: list form {listFun F' callPast}, set form {setFun F' callPast} (both must refuse)"
  t := checkProgram t "entry past size" F'
  return t

/-- The summary lines, and the failures for a refusal kind never refused or an acceptance kind
never accepted. -/
def report (t : Tally) : List String × Tally := Id.run do
  let mut t := t
  let mut lines := [s!"scope check (set form against list form): programs {t.programs}, functions {t.functions}, edits {t.mutants} (accepted {t.accepted}, refused {t.refused}); the canonical map's check against the domain and pins on {t.canonical} programs and edited programs"]
  for (k, n, a, r) in t.byKind do
    lines := lines ++ [s!"  {k}: {n} edits, accepted {a}, refused {r}"]
    if acceptKinds.contains k then
      if a == 0 then t := t.fail s!"scope check: the well-scoped edit {k} is never accepted"
    else if r == 0 then t := t.fail s!"scope check: the ill-scoped edit {k} is never refused"
    if !acceptKinds.contains k && a > 0 then
      t := t.fail s!"scope check: the ill-scoped edit {k} accepted {a} times"
  return (lines, t)

end IxCCTests.Own.Owned.ScopeSet
