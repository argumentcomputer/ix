import CompilatrixTests.Src.Support
import Compilatrix.Src.Relevance.Check

/-! The relevance checker's rules on synthetic programs (design note 02
§3.3): an accepted baseline, and one violation per rule, each rejected with
that rule's code. -/

namespace CompilatrixTests.Src.Relevance.Checker

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance CompilatrixTests.Src

/-- The base program plus one root definition. -/
def withRoot (value : Term) (lvls : Nat := 0) : Program × Base × CId :=
  let (b, base) := base
  let (b, root) := b.add (.defn .defn .safe lvls ty value)
  (b.program #[root], base, root)

/-- An annotation matching the installed terms: every constant relevant with
no parameter classes, every constructor keeping all fields, node tags read
off the runtime terms. -/
def annOf (p : Program) (keys : Array TermKey) : Ann :=
  let consts := (Array.range p.size).map fun _ => some { result := .rel, params := #[] }
  let ctors := (Array.range p.size).map fun c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ _ nf _) => some { fields := .replicate nf .keep }
    | _ => none
  { consts, ctors, nodes := keys.filterMap fun k => (p.termOf k).map fun t => (k, t.tagOrder #[]) }

def rootKeys (p : Program) : Array TermKey :=
  let values := (Array.range p.size).filterMap fun c =>
    match p.decl? c with
    | some (.defn .defn .safe ..) => some (TermKey.value c)
    | _ => none
  let rules := (Array.range p.size).flatMap fun c =>
    match p.decl? c with
    | some (.recr _ _ _ _ _ _ _ _ rules _) => (Array.range rules.size).map (TermKey.rule c)
    | _ => #[]
  values ++ rules

def rulesOf : Except (Array RelError) Checked → List String
  | .ok _ => []
  | .error es => es.toList.map (·.rule)

def expectRule (a : Assert) (p : Program) (ann : Ann) (rule : String) (msg : String) : IO Unit := do
  let got := rulesOf (check p ann)
  if rule.isEmpty then expect a got.isEmpty s!"{msg}: expected acceptance, got {got}"
  else expect a (got.contains rule) s!"{msg}: expected {rule}, got {got}"

def setConst (ann : Ann) (c : CId) (rel : ConstRel) : Ann :=
  { ann with consts := ann.consts.set! c (some rel) }

def setCtor (ann : Ann) (c : CId) (fields : Array FieldClass) : Ann :=
  { ann with ctors := ann.ctors.set! c (some { fields }) }

def c (id : CId) : Term := .const id []

def run (a : Assert) : IO Unit := do
  -- Baseline: λ x. add x (succ x).
  let (_, b, _) := withRoot (.natLit 0)
  let (p, b, root) := withRoot (lam (app (c b.add) [.var 0, app (c b.succ) [.var 0]]))
  let ann := annOf p (rootKeys p)
  expectRule a p ann "" "baseline"
  -- S1: an unannotated runtime term, a missing record, a wrong field count,
  -- a propWhen beyond the levels.
  expectRule a p { ann with nodes := ann.nodes.filter (·.1 != .value root) } "S1" "unannotated root"
  expectRule a p { ann with consts := ann.consts.set! b.add none } "S1" "missing ConstRel"
  expectRule a p (setCtor ann b.succ #[.keep, .keep]) "S1" "CtorRel field count"
  let (p2, _, _) := withRoot (lam (.var 0) { propWhen := .allZero [3] })
  expectRule a p2 (annOf p2 (rootKeys p2)) "S1" "propWhen beyond the levels"
  -- S2: a dropped field built from a relevant argument.
  let (p3, b3, _) := withRoot (lam (app (c b.pairMk) [.var 0, .var 0]))
  let ann3 := annOf p3 (rootKeys p3)
  expectRule a p3 (setCtor ann3 b3.pairMk #[.keep, .proof]) "S2" "dropped field from a relevant argument"
  let (p3', _, _) := withRoot (lam (appM (c b.pairMk) [(.var 0, .strict), (.var 0, .irr)]))
  expectRule a p3' (setCtor (annOf p3' (rootKeys p3')) b3.pairMk #[.keep, .proof]) ""
    "dropped field from irr"
  -- S4: a subsingleton recursor whose constructor keeps a non-index field.
  let (p4, b4, _) := withRoot (lam (appM (.const b.isNatRec [.zero])
    [(irrArg, .irr), (lam (.var 0), .strict), (.var 0, .strict), (irrArg, .irr)]))
  let ann4 := annOf p4 (rootKeys p4)
  expectRule a p4 ann4 "" "subsingleton with an index field"
  let p4' := { p4 with table := { p4.table with
    recKind := p4.table.recKind.set! b4.isNatRec (some (.subsingleton #[.proof])) } }
  expectRule a p4' ann4 "S4" "kept field not read from an index"
  -- C0: a binder written erased, annotated relevant.
  let (p5, _, _) := withRoot (lam (.var 0) { contract := .erased })
  expectRule a p5 (annOf p5 (rootKeys p5)) "C0" "erased binder annotated relevant"
  -- C1: a relevant use of an irrelevant binder.
  let (p6, _, _) := withRoot (lam (.var 0) { rel := .proof })
  expectRule a p6 (annOf p6 (rootKeys p6)) "C1" "relevant use of a proof binder"
  -- C2: an irrelevant parameter given a relevant argument.
  expectRule a p (setConst ann b.add { result := .rel, params := #[.proof, .rel] }) "C2"
    "proof parameter with a relevant argument"
  -- C3: a casesOn minor binding a dropped field relevantly, and a projection.
  let (p7, b7, _) := withRoot (lam (appM (.const b.natCases [.succ .zero])
    [(irrArg, .irr), (.var 0, .strict), (.natLit 0, .strict), (lam (.var 0), .strict)]))
  let ann7 := annOf p7 (rootKeys p7)
  expectRule a p7 ann7 "" "casesOn minor"
  expectRule a p7 (setCtor ann7 b7.succ #[.proof]) "C3" "minor binds a dropped field"
  let (p8, b8, _) := withRoot (lam (.proj b.pair 0 (app (c b.pairMk) [.var 0, .var 0])))
  expectRule a p8 (setCtor (annOf p8 (rootKeys p8)) b8.pairMk #[.proof, .keep]) "C3"
    "projection of a dropped field"
  -- C4: an ordinary eliminator with an irrelevant major.
  let (p9, _, _) := withRoot (lam (appM (.const b.natCases [.succ .zero])
    [(irrArg, .irr), (.var 0, .irr), (.natLit 0, .strict), (lam (.var 0), .strict)]))
  expectRule a p9 (annOf p9 (rootKeys p9)) "C4" "ordinary eliminator on an irrelevant major"
  -- C5: a relevant reference to a proof constant.
  expectRule a p (setConst ann b.succ { result := .proof, params := #[] }) "C5"
    "relevant reference to a proof"
  -- The checker's closure: only terms reached through relevant positions.
  let (p10, _, _) := withRoot (lam (.app (lam (.var 1)) (c b.nat) .irr))
  let ann10 := annOf p10 (rootKeys p10)
  match check p10 ann10 with
  | .ok ch => expect a (!ch.reached.contains b.nat) "an irrelevant reference is not reached"
  | .error es => expect a false s!"irrelevant reference: {es.map (·.rule)}"

end CompilatrixTests.Src.Relevance.Checker
