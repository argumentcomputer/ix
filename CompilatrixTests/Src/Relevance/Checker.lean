import CompilatrixTests.Src.Support
import Compilatrix.Src.Relevance.Check

/-! The relevance checker's rules on synthetic programs (design note 02
§3.3): an accepted baseline, and one violation per rule, each rejected with
that rule's code; then the level-exact rules (D18): each decided at the
instance's universe profile, with one constant reached at two profiles. -/

namespace CompilatrixTests.Src.Relevance.Checker

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance CompilatrixTests.Src

/-- The base program plus the given definitions and one root definition
(the last constant). -/
def withConsts (decls : List Decl) (value : Term) : Program × Base × List CId × CId :=
  let (b, base) := base
  let (b, ids) := decls.foldl (init := (b, [])) fun (b, ids) d =>
    let (b, c) := b.add d
    (b, ids ++ [c])
  let (b, root) := b.add (.defn .defn .safe 0 ty value)
  (b.program #[root], base, ids, root)

/-- The base program plus one root definition. -/
def withRoot (value : Term) : Program × Base × CId :=
  let (p, base, _, root) := withConsts [] value
  (p, base, root)

/-- An annotation matching the installed terms: every constant relevant with
no parameter classes, every constructor keeping all fields, node tags read
off the runtime terms. -/
def annOf (p : Program) (keys : Array TermKey) : Ann :=
  let consts := (List.range p.size).map fun c => (c, { result := .rel, params := [] })
  let ctors := (List.range p.size).filterMap fun c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ _ nf _) => some (c, { fields := .replicate nf .keep })
    | _ => none
  { consts := NatMap.ofList consts, ctors := NatMap.ofList ctors
    nodes := keys.toList.filterMap fun k => (p.termOf k).map fun t => (k, t.tagOrder) }

def rootKeys (p : Program) : Array TermKey :=
  let values := (Array.range p.size).filterMap fun c =>
    match p.decl? c with
    | some (.defn .defn .safe ..) => some (TermKey.value c)
    | _ => none
  let rules := (Array.range p.size).flatMap fun c =>
    match p.decl? c with
    | some (.recr _ _ _ _ _ _ _ _ rules _) => (Array.range rules.length).map (TermKey.rule c)
    | _ => #[]
  values ++ rules

def rulesOf : Except (Array RelError) Checked → List String
  | .ok _ => []
  | .error es => es.toList.map (·.rule)

def expectRule (a : Assert) (p : Program) (ann : Ann) (rule : String) (msg : String) : IO Unit := do
  let r := check p ann
  let got := rulesOf r
  let shown := match r with
    | .ok _ => ""
    | .error es => String.intercalate "; " (es.toList.map (RelError.render p))
  if rule.isEmpty then expect a got.isEmpty s!"{msg}: expected acceptance, got {shown}"
  else expect a (got.contains rule) s!"{msg}: expected {rule}, got {shown}"

def setConst (ann : Ann) (c : CId) (rel : ConstRel) : Ann :=
  { ann with consts := ann.consts.insert c rel }

def setCtor (ann : Ann) (c : CId) (fields : List FieldClass) : Ann :=
  { ann with ctors := ann.ctors.insert c { fields } }

def c (id : CId) : Term := .const id []

/-- The universe `u` as a level: `0` or `1`. -/
def lv : Nat → Compilatrix.Ixon.Univ
  | 0 => .zero
  | _ => .succ .zero

def zeroAt0 : PropWhen := .allZero [0]

/-- The `i`-th constant `withConsts` adds after the base program. -/
def extraId (i : Nat) : CId := base.1.consts.size + i

/-- The level-exact rules (D18). `f.{u} (x : α)` with `α : Sort u` has a
parameter that is a proof exactly at u = 0; `g.{u}` passes a theorem in a
position that is a proof exactly at u = 0; `unitRec.{v, u}` is a
subsingleton eliminator exactly at u = 0; `ppairMk.{u}`'s first field is a
proof exactly at u = 0. -/
def levelExact (a : Assert) : IO Unit := do
  let b := base.2
  -- `f` is extra constant 0 and `thm` extra constant 1.
  let f := extraId 0
  let thm := extraId 1
  let fDecl : Decl := .defn .defn .safe 1 (.pi {} {} ty ty) (lam (.natLit 0) { rel := .proof zeroAt0 })
  let thmDecl : Decl := .defn .thm .safe 0 ty (.natLit 0)
  let build := fun (value : Term) =>
    let (p, _, _, _) := withConsts [fDecl, thmDecl] value
    let ann := annOf p (rootKeys p)
    let ann := setConst ann f { result := .rel, params := [.proof zeroAt0] }
    (p, setConst ann thm { result := Rel.prf, params := [] })
  -- C2 is an equality for proofs: a proof argument needs a parameter that is
  -- irrelevant at the callee's profile, and the reverse.
  for (u, arg, rule, msg) in
      [(1, ((Term.var 0), A.strict), "", "relevant argument, parameter relevant at u = 1"),
       (0, (.var 0, .strict), "C2", "relevant argument, parameter a proof at u = 0"),
       (0, (irrArg, .irr), "", "proof argument, parameter a proof at u = 0"),
       (1, (irrArg, .irr), "C2", "proof argument, parameter relevant at u = 1 (sort polymorphism)")] do
    let (p, ann) := build (lam (appM (.const f [lv u]) [arg]))
    expectRule a p ann rule s!"C2 at a profile: {msg}"
  -- A type for a parameter relevant at the instance is rejected too: no
  -- universe condition covers it (the `typeArg` case of src-sortpoly).
  let (pT, annT) := build (lam (.app (.const f [lv 1]) (.sort .zero) .strict .type))
  expectRule a pT annT "C2" "C2: a type for a parameter relevant at u = 1"
  let (pT0, annT0) := build (lam (.app (.const f [lv 0]) (.sort .zero) .strict .type))
  expectRule a pT0 annT0 "" "C2: a type for a parameter irrelevant at u = 0"
  -- One constant at two profiles: both instances are checked and recorded.
  let (pS, annS) := build (lam (app (c b.add)
    [appM (.const f [lv 0]) [(irrArg, .irr)], appM (.const f [lv 1]) [(.var 0, .strict)]]))
  match check pS annS with
  | .ok ch =>
    expect a ((ch.instances.filter (·.1 == f)).length == 2) "f is reached at two profiles"
    expect a (ch.profileSplit.contains f) "profile-split lists f"
  | .error es => expect a false s!"two profiles: {es.map (·.render pS)}"
  -- Per-profile closure: `g` (extra constant 1, after `thm`) passes the
  -- theorem in an argument that is a proof at u = 0, so `g.{0}` does not
  -- reach it and `g.{1}` does (C5).
  let gDecl := Decl.defn .defn .safe 1 ty
    (lam (appM (lam (.var 1) { rel := .proof zeroAt0 }) [(.const (extraId 0) [], .irrWhen zeroAt0)]))
  for (u, rule, msg) in [(0, "", "g.{0} does not reach the theorem"),
      (1, "C5", "g.{1} reaches the theorem relevantly")] do
    let (p, _, _, _) := withConsts [thmDecl, gDecl] (lam (app (.const (extraId 1) [lv u]) [.var 0]))
    let ann := setConst (annOf p (rootKeys p)) (extraId 0) { result := Rel.prf, params := [] }
    expectRule a p ann rule s!"closure per profile: {msg}"
    if u == 0 then
      match check p ann with
      | .ok ch => expect a (!ch.reached.contains (extraId 0)) "g.{0}: the theorem is not reached"
      | .error _ => pure ()
  -- C4 per profile: `unitRec.{1, u}` with an irrelevant major.
  for (u, rule, msg) in [(0, "", "a subsingleton eliminator at u = 0"),
      (1, "C4", "an ordinary eliminator at u = 1")] do
    let (p, _, _) := withRoot (lam (appM (.const b.unitRec [.succ .zero, lv u])
      [(irrArg, .irr), (.var 0, .strict), (irrArg, .irr)]))
    expectRule a p (annOf p (rootKeys p)) rule s!"C4 per profile: {msg}"
  -- S2 per profile: `ppairMk.{u}`'s first field is dropped exactly at u = 0.
  for (u, first, rule, msg) in [(0, A.strict, "S2", "a relevant first field at u = 0"),
      (1, A.strict, "", "a relevant first field at u = 1"),
      (0, A.irr, "", "an irrelevant first field at u = 0")] do
    let (p, _, _) := withRoot (lam (appM (.const b.ppairMk [lv u])
      [(.var 0, first), (.var 0, .strict)]))
    let ann := setCtor (annOf p (rootKeys p)) b.ppairMk [.proof zeroAt0, .keep]
    expectRule a p ann rule s!"S2 per profile: {msg}"
  -- Readback per profile: the dropped field has no observation.
  match check (withRoot (lam (.natLit 0))).1 (annOf (withRoot (lam (.natLit 0))).1
      (rootKeys (withRoot (lam (.natLit 0))).1)) with
  | .ok ch =>
    let ch := { ch with ctors := ch.ctors.insert b.ppairMk { fields := [.proof zeroAt0, .keep] } }
    expect a (!ch.keeps b.ppairMk [0] 0 && ch.keeps b.ppairMk [0] 1 && ch.keeps b.ppairMk [1] 0)
      "keeps is decided at the constructor value's levels"
  | .error es => expect a false s!"readback check: {es.map (·.rule)}"

def run (a : Assert) : IO Unit := do
  -- Baseline: λ x. add x (succ x).
  let b := base.2
  let (p, b, root) := withRoot (lam (app (c b.add) [.var 0, app (c b.succ) [.var 0]]))
  let ann := annOf p (rootKeys p)
  expectRule a p ann "" "baseline"
  -- S1: an unannotated runtime term, a missing record, a wrong field count,
  -- a propWhen beyond the levels.
  expectRule a p { ann with nodes := ann.nodes.filter (·.1 != .value root) } "S1" "unannotated root"
  expectRule a p { ann with consts := ann.consts.erase b.add } "S1" "missing ConstRel"
  expectRule a p (setCtor ann b.succ [.keep, .keep]) "S1" "CtorRel field count"
  let (p2, _, _) := withRoot (lam (.var 0) { propWhen := .allZero [3] })
  expectRule a p2 (annOf p2 (rootKeys p2)) "S1" "propWhen beyond the levels"
  let (p2', _, _) := withRoot (lam (appM (lam (.natLit 0)) [(.var 0, .irrWhen (.allZero [2]))]))
  expectRule a p2' (annOf p2' (rootKeys p2')) "S1" "an argument's condition beyond the levels"
  expectRule a p (setCtor ann b.succ [.proof (.allZero [0])]) "S1"
    "a field condition beyond the constructor's levels"
  -- S2: a dropped field built from a relevant argument.
  let (p3, b3, _) := withRoot (lam (app (c b.pairMk) [.var 0, .var 0]))
  let ann3 := annOf p3 (rootKeys p3)
  expectRule a p3 (setCtor ann3 b3.pairMk [.keep, .prf]) "S2" "dropped field from a relevant argument"
  let (p3', _, _) := withRoot (lam (appM (c b.pairMk) [(.var 0, .strict), (.var 0, .irr)]))
  expectRule a p3' (setCtor (annOf p3' (rootKeys p3')) b3.pairMk [.keep, .prf]) ""
    "dropped field from irr"
  -- S4: a subsingleton recursor whose constructor keeps a non-index field.
  let (p4, b4, _) := withRoot (lam (appM (.const b.isNatRec [.zero])
    [(irrArg, .irr), (lam (.var 0), .strict), (.var 0, .strict), (irrArg, .irr)]))
  let ann4 := annOf p4 (rootKeys p4)
  expectRule a p4 ann4 "" "subsingleton with an index field"
  let p4' := { p4 with table := { p4.table with
    recKind := p4.table.recKind.insert b4.isNatRec (.subsingleton .always [.proof]) } }
  expectRule a p4' ann4 "S4" "kept field not read from an index"
  -- C0: a binder written erased, annotated relevant.
  let (p5, _, _) := withRoot (lam (.var 0) { contract := .erased })
  expectRule a p5 (annOf p5 (rootKeys p5)) "C0" "erased binder annotated relevant"
  -- C1: a relevant use of an irrelevant binder.
  let (p6, _, _) := withRoot (lam (.var 0) { rel := Rel.prf })
  expectRule a p6 (annOf p6 (rootKeys p6)) "C1" "relevant use of a proof binder"
  -- C2: an irrelevant parameter given a relevant argument.
  expectRule a p (setConst ann b.add { result := .rel, params := [Rel.prf, .rel] }) "C2"
    "proof parameter with a relevant argument"
  -- C3: a casesOn minor binding a dropped field relevantly, and a projection.
  let (p7, b7, _) := withRoot (lam (appM (.const b.natCases [.succ .zero])
    [(irrArg, .irr), (.var 0, .strict), (.natLit 0, .strict), (lam (.var 0), .strict)]))
  let ann7 := annOf p7 (rootKeys p7)
  expectRule a p7 ann7 "" "casesOn minor"
  expectRule a p7 (setCtor ann7 b7.succ [.prf]) "C3" "minor binds a dropped field"
  let (p8, b8, _) := withRoot (lam (.proj b.pair 0 (app (c b.pairMk) [.var 0, .var 0])))
  expectRule a p8 (setCtor (annOf p8 (rootKeys p8)) b8.pairMk [.prf, .keep]) "C3"
    "projection of a dropped field"
  -- C4: an ordinary eliminator with an irrelevant major.
  let (p9, _, _) := withRoot (lam (appM (.const b.natCases [.succ .zero])
    [(irrArg, .irr), (.var 0, .irr), (.natLit 0, .strict), (lam (.var 0), .strict)]))
  expectRule a p9 (annOf p9 (rootKeys p9)) "C4" "ordinary eliminator on an irrelevant major"
  -- C5: a relevant reference to a proof constant.
  expectRule a p (setConst ann b.succ { result := Rel.prf, params := [] }) "C5"
    "relevant reference to a proof"
  -- C6: a λ in a relevant position that is a proof at the instance.
  let (p6', _, _) := withRoot (lam (.var 0) { propWhen := .always })
  expectRule a p6' (annOf p6' (rootKeys p6')) "C6" "a relevant λ that is a proof"
  -- The checker's closure: only terms reached through relevant positions.
  let (p10, _, _) := withRoot (lam (appIrr (lam (.var 1) { rel := Rel.prf }) (c b.nat)))
  let ann10 := annOf p10 (rootKeys p10)
  match check p10 ann10 with
  | .ok ch => expect a (!ch.reached.contains b.nat) "an irrelevant reference is not reached"
  | .error es => expect a false s!"irrelevant reference: {es.map (·.rule)}"
  levelExact a

end CompilatrixTests.Src.Relevance.Checker
