import IxCCTests.Support.Bound
import IxCCTests.Recheck.Hostile
import IxCC.Recheck.Produce

/-! # The role-bound test builder, against the kernel front end

The builder `IxCCTests.Support.Bound` makes the in-memory test environments of
`tests-recheck`'s hostile families role-bound, with their recursors, so that
the certified kernel accepts them. Ported here from the hostile family's
enumeration case (`IxCCTests.Recheck.Hostile`: `pinFreeEnv`, `mkCase`,
`pinFree`) and run through the front end over the kernel (`Recheck.ingress`,
`produce`, `checkCanonicalRelevance`), each assertion naming the stage or
code a refusal must have:

* the writer reproduces the base's records, blobs, root and binding, and the
  kernel accepts the rewritten base;
* the enumeration program (`idc`, `main := idc c₁`, a root per constructor)
  on the base: the kernel accepts it, its honest certificate gives an object
  that returns constructor 1, and Stage A accepts that certificate; the hostile
  certificate (`idc`'s parameter and `main`'s argument retagged as types) is
  refused by `Recheck.run` at `relevance-S1` and by Stage A. On a role-bound
  base nothing is pin-free: the base binds `Nat`, `Bool` and `Eq`, so the
  original regression's precondition (no pinned identity, which once skipped
  `checkCanonical`) cannot be built; what remains is the refusal itself;
* a two-constructor enumeration is the base's `Bool` (the same block);
* the refusals of the kernel the builder exists to avoid, each with its
  stage and classification: an inductive block without its recursor
  (declined by the reader), an unreachable ill-typed constant (declined at the
  kernel as a type mismatch: the kernel does not take a failed conversion
  search as evidence that the input is wrong), an
  unreachable non-standard axiom (declined);
* the recursors of a recursive inductive (`T | leaf | node T T`) and of a
  monomorphic list over the enumeration are the kernel's. -/

namespace IxCCTests.KernelFront.Bound

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect)
open IxCCTests.Support.Bound (loadBase addEnum addTree addList simpleBlock Ind)
open IxCCTests.IxonV3.TypingFixtures (store block arrow lambda axiomType)
open IxCCTests.Recheck.Hostile (defn enumC sidecar mkCert driver ofErr)

abbrev X := IxCC.Ixon.V3.Expr
abbrev Addr := IxCC.Ixon.Address

def envBytes (label : String) (env : Env) : IO ByteArray :=
  match IxCCTests.Support.Bound.bytes env with
  | some b => pure b
  | none => throw (IO.userError s!"{label}: not role-bound")

/-- The hostile family's enumeration program on `env`: `idc (c : E) : E := c`,
`main : E := idc c₁` and a root `rᵢ := cᵢ` per constructor; with `illTyped`,
also an unreachable constant whose value does not have its type. -/
def enumProgram (env : Env) (n : Nat) (illTyped : Bool := false) :
    Env × Ind × Addr × Addr × List (String × Addr) := Id.run do
  let (e, en) := addEnum env n
  let (e, idc) := store e ⟨defn (arrow enumC enumC) (lambda enumC (.var 0)), #[], #[en.ind], #[]⟩
  let (e, main) := store e
    ⟨defn enumC (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[en.ind, idc, en.ctors[1]!], #[]⟩
  let mut e := e
  let mut roots := [("main", main)]
  for (c, i) in en.ctors.toList.zipIdx do
    let (e', r) := store e ⟨defn enumC (.ref 1 #[]), #[], #[en.ind, c], #[]⟩
    e := e'
    roots := roots ++ [(s!"r{i}", r)]
  if illTyped then
    e := (store e ⟨defn (arrow enumC enumC) (.ref 1 #[]), #[], #[en.ind, en.ctors[0]!], #[]⟩).1
  return (e, en, idc, main, roots)

def refusedAt (r : Except Src.KernelFront.Refusal α) (stage : Src.KernelFront.Stage)
    (outcome : Ix.Kernel.Admission.Outcome) : Bool :=
  match r with
  | .error e => e.stage == stage && e.outcome == some outcome
  | .ok _ => false

def describe : Except Src.KernelFront.Refusal α → String
  | .error e => e.render
  | .ok _ => "accepted"

def errText : Except Recheck.Err α → String
  | .error e => e.render
  | .ok _ => "accepted"

def run (a : Assert) : IO (List String) := do
  let base ← loadBase
  -- the writer
  let bb ← envBytes "base" base
  let back ← IO.ofExcept (decodeAnonymousEnv bb)
  expect a (back.root == base.root && back.consts.size == base.consts.size &&
      back.blobs.size == base.blobs.size && back.bindingAddress == base.bindingAddress &&
      back.hints.size == base.hints.size &&
      base.consts.toList.all (fun (k, v) => back.consts[k]? == some v))
    "bound writer: the base did not survive the role-bound writer"
  expect a (Src.KernelFront.accept back).toOption.isSome
    s!"bound writer: the kernel refused the rewritten base: {describe (Src.KernelFront.accept back)}"
  -- the enumeration program, honest and hostile
  let n := 3
  let (env, en, idc, main, roots) := enumProgram base n
  let bs ← envBytes "enum" env
  let json := sidecar roots
  let k ← ofErr "enum: kernel ingress" (Recheck.ingress bs json)
  expect a (k.kernel.acc.records.length == env.consts.size && !en.existing)
    "enum: the kernel did not receive every record, or the enumeration was the base's"
  let P := k.program
  let cfg := Recheck.Config.forInput {} k
  let honest ← ofErr "enum: produce" (Recheck.produce cfg k)
  let art ← ofErr "enum: Recheck.run (honest)" (Recheck.run cfg P honest)
  expect a ((art.linked driver).run (0, []) 1000000 matches .ok (some (.ctor 1 [])))
    "enum: the honest object does not return constructor 1"
  expect a (Recheck.checkCanonicalRelevance cfg k honest.table honest.relevance)
    "enum: Stage A refused the kernel annotator's own annotation"
  let some idcId := P.lookup idc | throw (IO.userError "enum: idc not ingested")
  let some mainId := P.lookup main | throw (IO.userError "enum: main not ingested")
  let hostileAnn : Src.Relevance.Ann :=
    { honest.relevance with
      consts := honest.relevance.consts.modify idcId fun cr =>
        { cr with params := cr.params.map fun _ => .type }
      nodes := honest.relevance.nodes.map fun (key, tags) =>
        if key == Src.TermKey.value mainId then
          (key, tags.map fun t => match t with
            | .arg _ => .arg .type
            | t => t)
        else (key, tags) }
  let hostile ← ofErr "enum: the hostile certificate" (mkCert cfg P honest.table hostileAnn)
  match Recheck.run cfg P hostile with
  | .ok _ => expect a false "enum: Recheck.run accepted the hostile certificate"
  | .error e =>
    expect a (e.stage == .relevance && e.code == "relevance-S1")
      s!"enum: Recheck.run refused the hostile certificate, but not by checkCanonical: {e.render}"
  expect a (!Recheck.checkCanonicalRelevance cfg k hostile.table hostile.relevance)
    "enum: Stage A accepted the hostile annotation"
  -- a two-constructor enumeration is the base's `Bool`
  let (_, two) := addEnum base 2
  expect a two.existing "bool: a two-constructor enumeration is not the base's Bool block"
  -- the refusals the builder avoids
  let (noRec, _) := block base (simpleBlock ((Array.range n).map fun _ => #[]))
  let r := Src.KernelFront.accept noRec
  expect a (refusedAt r .read .declined)
    s!"no recursor: an inductive block without its recursor was not declined by the reader: {describe r}"
  let (ill, _, _, _, _) := enumProgram base n (illTyped := true)
  let r := Src.KernelFront.accept ill
  expect a (refusedAt r .kernel .declined &&
      match r with | .error e => (e.message.splitOn "type mismatch").length > 1 | .ok _ => false)
    s!"ill-typed: an unreachable ill-typed constant was not declined by the kernel as a type mismatch: {describe r}"
  let (withAxiom, _) := store env axiomType
  let r := Src.KernelFront.accept withAxiom
  expect a (refusedAt r .kernel .declined &&
      match r with | .error e => (e.message.splitOn "non-standard axiom").length > 1 | .ok _ => false)
    s!"axiom: an unreachable non-standard axiom did not decline the artifact: {describe r}"
  -- what `ixcc` prints: the kernel's line verbatim, then the plain-words line
  let expected := match r with
    | .error e => e.render ++ "\n" ++ Src.KernelFront.PolicyDecline.nonStandardAxiom.explain
    | .ok _ => ""
  expect a (match r with | .error e => e.policy == some .nonStandardAxiom | .ok _ => false)
    "axiom: the refusal is not classified as the non-standard-axiom policy decline"
  let ing := Recheck.ingress (IxCCTests.Support.Bound.write withAxiom) (sidecar roots) []
  expect a (match ing with
      | .error e => e.stage == .ingress && e.code == "kernel" && e.message == expected
      | .ok _ => false)
    s!"axiom: ingress did not report the kernel's line and the explanation: {errText ing}"
  -- recursive inductives: the generated recursors are the kernel's
  let (te, tree) := addTree base
  let (te, tmain) := store te
    ⟨defn (.ref 0 #[]) (.app (.app (.ref 1 #[]) (.ref 2 #[])) (.ref 2 #[])), #[],
      #[tree.ind, tree.ctors[1]!, tree.ctors[0]!], #[]⟩
  let tk : Except Recheck.Err Recheck.Input := Recheck.ingress (← envBytes "tree" te) (sidecar [("main", tmain)])
  expect a (tk matches Except.ok _)
    s!"tree: the kernel front end refused a recursive inductive with its recursor: {errText tk}"
  let (le, list) := addList env en.ind
  let (le, lmain) := store le
    ⟨defn (.ref 0 #[]) (.app (.app (.ref 1 #[]) (.ref 3 #[])) (.ref 2 #[])), #[],
      #[list.ind, list.ctors[1]!, list.ctors[0]!, en.ctors[0]!], #[]⟩
  let lk : Except Recheck.Err Recheck.Input := Recheck.ingress (← envBytes "list" le) (sidecar [("main", lmain)])
  expect a (lk matches Except.ok _)
    s!"list: the kernel front end refused a list over the enumeration with its recursor: {errText lk}"
  return [s!"bound builder: the base ({base.consts.size} records) rewritten and accepted; enum-{n} on it \
    accepted ({env.consts.size} records), honest object returns constructor 1, Stage A accepts it; hostile \
    certificate refused (relevance-S1, Stage A); Bool control; refusals: no recursor (read, declined), \
    ill-typed (kernel, declined: type mismatch), axiom (kernel, declined); tree and list recursors accepted"]

end IxCCTests.KernelFront.Bound
