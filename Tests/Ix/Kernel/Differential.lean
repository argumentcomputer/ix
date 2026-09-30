/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Tc.Check
import Tests.Ix.Kernel.Fixtures
import Tests.Ix.Kernel.Inductives
import Tests.Ix.Kernel.Structures
import Tests.Ix.Kernel.Literals
import Tests.Ix.Kernel.Quotients
import Tests.Ix.Kernel.Axioms

/-! # Host-only supported-profile differential gate

The same raw declarations go to Ix.Kernel and a test adapter to Ix.Tc.
The adapter is not certified ingress. It assigns deterministic synthetic
identities, retains reference positions and declaration data, and separates
inductive and recursor storage groups as required by Ix.Tc. No source
declaration is accepted on the strength of the other checker's verdict.

JSONL retains raw inputs, both outcomes and reasons, and expected differences
for the eventual Rust oracle. The certified fixture modules stay independent
of this module and every host dependency.
-/

namespace Tests.Ix.Kernel.Differential

open _root_.Ix.Kernel
open _root_.Ix.Tc (KExpr KUniv KId KConst KEnv TcState TcM Primitives)

abbrev K := KExpr .anon
abbrev Id := KId .anon

/-- Length-prefixed fixture names avoid ambiguity before hashing. These are
test identities, not claims about the content address of a declaration. -/
def refId : ConstRef String → Id
  | .member b i => ⟨Address.blake3 s!"K2:{b.length}:{b}:member:{i}".toUTF8, ()⟩
  | .ctor b i j => ⟨Address.blake3 s!"K2:{b.length}:{b}:ctor:{i}:{j}".toUTF8, ()⟩

def storageId (b group : String) : Id :=
  ⟨Address.blake3 s!"K2:{b.length}:{b}:storage:{group}".toUTF8, ()⟩

def bounded (n : Nat) : Except String UInt64 :=
  if n < UInt64.size then .ok n.toUInt64 else .error "fixture exceeds Ix.Tc's UInt64 domain"

def level : VLevel → Except String (KUniv .anon)
  | .zero => return .mkZero
  | .succ u => return .mkSucc (← level u)
  | .max u v => return .mkMaxRaw (← level u) (← level v)
  | .imax u v => return .mkIMaxRaw (← level u) (← level v)
  | .param i => return .mkParam (← bounded i) ()

def expr : VExpr String → Except String K
  | .bvar i => return .mkVar (← bounded i) ()
  | .sort u => return .mkSort (← level u)
  | .const r us => return .mkConst (refId r) (← us.toArray.mapM level)
  | .app f a => return .mkApp (← expr f) (← expr a)
  | .lam D b => return .mkLam () () (← expr D) (← expr b)
  | .forallE D B => return .mkAll () () (← expr D) (← expr B)
  | .letE t v b => return .mkLet () (← expr t) (← expr v) (← expr b) false
  | .proj r i e => return .mkPrj (refId r) (← bounded i) (← expr e)
  | .natLit r n =>
    if r = .member "Nat" 0 then return .mkNatLit n
    else .error "Ix.Tc literals have one configured Nat family"

def defKind : DefKind → Ix.DefKind
  | .definition => .defn
  | .theorem => .thm
  | .opaque => .opaq

def safety : Safety → Ix.DefinitionSafety
  | .safe => .safe
  | .unsafe => .unsaf
  | .partial => .part

def quotKind : QuotKind → Ix.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def group : Const String → String
  | .induct .. => "inductive"
  | .recursor .. => "recursor"
  | .defn .. => "definition"
  | _ => "standalone"

def member (b : String) (i : Nat) (c : Const String) :
    Except String (List (Id × KConst .anon)) := do
  let id := refId (.member b i)
  let block := storageId b (group c)
  match c with
  | .axiom u t s => return [(id, .axio () () (s != .safe) (← bounded u) (← expr t))]
  | .defn u k t v s =>
    return [(id, .defn () () (defKind k) (safety s) (.regular 0)
      (← bounded u) (← expr t) (← expr v) () block)]
  | .quot k u t => return [(id, .quot () () (quotKind k) (← bounded u) (← expr t))]
  | .induct u p n t cs s =>
    let ctors ← cs.zipIdx.mapM fun (c, j) => do
      return (refId (.ctor b i j), KConst.ctor () () (c.safety != .safe)
        (← bounded c.uvars) id (← bounded j) (← bounded c.nparams)
        (← bounded c.nfields) (← expr c.type))
    return (id, .indc () () (← bounded u) (← bounded p) (← bounded n)
      (s != .safe) block (← bounded i) (← expr t) (ctors.map (·.1)).toArray ()) :: ctors
  | .recursor u p n mo mi t rs k s =>
    let rules ← rs.toArray.mapM fun r => do
      return { ctor := (), fields := ← bounded r.nfields, rhs := ← expr r.rhs : Ix.Tc.RecRule .anon }
    return [(id, .recr () () k (s != .safe) (← bounded u) (← bounded p)
      (← bounded n) (← bounded mo) (← bounded mi) block (← bounded i) (← expr t) rules ())]

/-- Ix.Tc checks a preloaded environment. Its storage groups contain only
one kind; the kernel's logical block can include both a family and recursor.
All term references retain their original member/constructor identities. -/
def environment (ds : List (Decl String)) : Except String (KEnv .anon × List Id) := do
  let mut env : KEnv .anon := .new .source
  let mut order := []
  for d in ds do
    for (c, i) in d.block.members.zipIdx do
      let entries ← member d.address i c
      for (id, value) in entries do
        env := env.insert id value
        order := id :: order
    for g in ["inductive", "recursor", "definition"] do
      let ids := (d.block.members.zipIdx.filter fun (c, _) => group c == g).map
        fun (_, i) => refId (.member d.address i)
      if !ids.isEmpty then env := env.insertBlock (storageId d.address g) ids.toArray
  return (env, order.reverse)

def primitives : Primitives .anon :=
  { Primitives.ofAnonAddrs with
    nat := refId (.member "Nat" 0), natZero := refId (.ctor "Nat" 0 0)
    natSucc := refId (.ctor "Nat" 0 1), natRec := refId (.member "Nat" 1)
    list := refId (.member "List" 0), listNil := refId (.ctor "List" 0 0)
    listCons := refId (.ctor "List" 0 1)
    eq := refId (.member "Eq" 0), eqRefl := refId (.ctor "Eq" 0 0)
    quotType := refId (.member "Quot" 0), quotCtor := refId (.member "Quot.mk" 0)
    quotLift := refId (.member "Quot.lift" 0), quotInd := refId (.member "Quot.ind" 0) }

inductive Verdict where
  | accept | reject | decline
  deriving BEq, Repr

def Verdict.label : Verdict → String
  | .accept => "accept"
  | .reject => "reject"
  | .decline => "decline"

structure Outcome where
  verdict : Verdict
  reason : String := ""

def certified (fuel : Nat) (ds : List (Decl String)) : Outcome :=
  match check.{0,1} {fuel} ds with
  | .ok _ => ⟨.accept, ""⟩
  | .error (.rejected r) => ⟨.reject, r⟩
  | .error (.declined r) => ⟨.decline, r⟩

def oracle (ds : List (Decl String)) : Except String Outcome := do
  let (env, order) ← environment ds
  let action : TcM .anon Unit := order.forM TcM.checkConst
  match action.run { TcState.new env primitives with noAccel := true } with
  | .ok _ _ => return ⟨.accept, ""⟩
  | .error e _ => return ⟨.reject, toString e⟩

structure Case where
  name : String
  declarations : List (Decl String)
  kernel : Verdict := .accept
  tc : Verdict := .accept
  fuel : Nat := 1000
  difference : String := ""

/-- Canonical K flags for the two eligible fixture families. This constructs
the shared input before either checker runs; the oracle adapter never repairs
metadata. Separate cases below retain both noncanonical flags. -/
def withK (d : Decl String) (enabled : Bool) : Decl String :=
  { d with block.members := d.block.members.map fun c => match c with
      | .recursor u p n mo mi t rs _ s => .recursor u p n mo mi t rs enabled s
      | other => other }

def canonicalFixture (d : Decl String) : Decl String :=
  if d.address == "Eq" || d.address == "True" then withK d true else d

def canonicalCases : List Case := [
  { name := "definitions", declarations := Fixtures.accepted },
  { name := "false", declarations := [Inductives.falseDecl] },
  { name := "true", declarations := [Inductives.trueDecl] },
  { name := "and", declarations := [Inductives.andDecl] },
  { name := "or", declarations := [Inductives.orDecl] },
  { name := "nat", declarations := [Inductives.natHand] },
  { name := "list", declarations := [Inductives.listDecl] },
  { name := "eq", declarations := [Inductives.eqDecl] },
  { name := "ordinary-computation", declarations := Inductives.arithmetic ++ [Inductives.addOneOne] },
  { name := "equality-k", declarations := [Inductives.natDecl, Inductives.eqDecl, Inductives.kSubst] },
  { name := "structure-projection-eta", declarations := Structures.accepted ++ [Structures.fstMk,
    Structures.etaProd, Structures.propertyDecl] },
  { name := "natural-literals", declarations := [Literals.natDecl, Literals.eqDecl, Literals.three,
    Literals.threeSucc, Literals.zeroZero, Literals.addDecl, Literals.twoPlusTwo] },
  { name := "quotients", declarations := Quotients.primitives ++ [Quotients.liftMk, Quotients.indMk] },
  { name := "standard-axioms", declarations := [Axioms.eqDecl, Axioms.iffDecl, Axioms.nonemptyDecl,
    Axioms.propextDecl, Axioms.choiceDecl, Axioms.usePropext, Axioms.pick] },
  { name := "bad-function", declarations := [Fixtures.defn "ill" 0 .definition
      Fixtures.type0 (.app Fixtures.prop Fixtures.prop)], kernel := .reject, tc := .reject },
  { name := "open-variable", declarations := [Fixtures.defn "open" 0 .definition
      Fixtures.type0 (.bvar 0)], kernel := .reject, tc := .reject },
  { name := "open-universe", declarations := [Fixtures.defn "open" 0 .definition
      Fixtures.idType Fixtures.idBody], kernel := .reject, tc := .reject },
  { name := "wrong-universe-arity", declarations := [Fixtures.idDecl,
      Fixtures.defn "wrong" 0 .definition Fixtures.idTType (.const (.member "id" 0) [])],
    kernel := .reject, tc := .reject },
  { name := "bad-theorem-kind", declarations := [Fixtures.defn "bad" 0 .theorem
      Fixtures.idTType (.lam Fixtures.type0 (.lam (.bvar 0) (.bvar 0)))], kernel := .reject, tc := .reject },
  { name := "polymorphic-theorem-kind", declarations := [Fixtures.defn "bad" 1 .theorem
      Fixtures.idType Fixtures.idBody], kernel := .decline, tc := .reject,
    difference := "the polymorphic sort was not established to be always Prop" },
  { name := "bad-definition-body", declarations := [Fixtures.defn "bad" 1 .definition
      Fixtures.idType (.lam Fixtures.sortU (.lam (.bvar 0) (.bvar 1)))],
    kernel := .decline, tc := .reject, difference := "conservative conversion search" },
  { name := "tampered-recursor", declarations := [Inductives.natTampered],
    kernel := .decline, tc := .reject, difference := "exact generated-block recognition" },
  { name := "wrong-iota", declarations := Inductives.arithmetic ++ [Inductives.addOneOneWrong],
    kernel := .decline, tc := .reject, difference := "conservative conversion search" },
  { name := "bad-projection-index", declarations := Structures.accepted ++ [Structures.badIndex],
    kernel := .reject, tc := .reject },
  { name := "wrong-projection", declarations := Structures.accepted ++ [Structures.fstMkWrong],
    kernel := .decline, tc := .reject, difference := "conservative conversion search" },
  { name := "wrong-natural-literal", declarations := [Literals.natDecl, Literals.eqDecl,
      Literals.twoThree], kernel := .decline, tc := .reject, difference := "conservative conversion search" },
  { name := "bad-quotient-former", declarations := [Quotients.eqDecl, Quotients.quotProp],
    kernel := .decline, tc := .reject, difference := "primitive recognition" },
  { name := "wrong-quotient-computation", declarations := Quotients.primitives ++ [Quotients.liftMkWrong],
    kernel := .decline, tc := .reject, difference := "conservative conversion search" },
  { name := "missing-axiom-interface", declarations := [Axioms.eqDecl, Axioms.propextDecl],
    kernel := .reject, tc := .reject },
  { name := "ordered-reference", declarations := [Fixtures.idFnDecl, Fixtures.fnDecl],
    kernel := .reject, difference := "certified declarations require installed dependencies" },
  { name := "duplicate-address", declarations := [Fixtures.idDecl, Fixtures.idDecl],
    kernel := .reject, difference := "preloaded oracle map overwrites duplicates" },
  { name := "fuel-exhaustion", declarations := [Fixtures.idDecl], fuel := 0,
    kernel := .decline, difference := "Ix.Kernel recursive depth budget" },
  { name := "unsupported-axiom", declarations := [Axioms.axiomProp],
    kernel := .decline, difference := "arbitrary axioms are outside the certified profile" },
  { name := "unsupported-unsafe", declarations := [Fixtures.defn "unsafe" 1 .definition
      Fixtures.idType Fixtures.idBody .unsafe],
    kernel := .decline, difference := "unsafe definitions are outside the certified profile" },
  { name := "opaque-transparency", declarations := [
      Fixtures.defn "opaqueType" 0 .opaque Fixtures.type1 Fixtures.type0,
      Fixtures.defn "useOpaque" 0 .definition (.const (.member "opaqueType" 0) []) Fixtures.prop],
    kernel := .decline, tc := .reject,
    difference := "conservative conversion search: like Ix.Tc, conversion does not unfold an opaque body" }
]

def cases : List Case :=
  (canonicalCases.map fun c => { c with declarations := c.declarations.map canonicalFixture }) ++ [
    { name := "eq-k-flag-false", declarations := [Inductives.eqDecl], tc := .reject,
      difference := "Ix.Kernel derives K-like reduction independently of the supplied flag" },
    { name := "true-k-flag-false", declarations := [Inductives.trueDecl], tc := .reject,
      difference := "Ix.Kernel derives K-like reduction independently of the supplied flag" },
    { name := "nat-k-flag-true", declarations := [withK Inductives.natDecl true],
      kernel := .reject, tc := .reject }
  ]

/-! Raw JSON uses tagged arrays and preserves every logical reference and
declaration field. It is independent of Ix.Tc's native data representation. -/

open Lean (Json toJson)

def tagged (tag : String) (fields : List Json := []) : Json :=
  .arr ((.str tag :: fields).toArray)

def refJson : ConstRef String → Json
  | .member b i => tagged "member" [toJson b, toJson i]
  | .ctor b i j => tagged "ctor" [toJson b, toJson i, toJson j]

def levelJson : VLevel → Json
  | .zero => tagged "zero"
  | .succ u => tagged "succ" [levelJson u]
  | .max u v => tagged "max" [levelJson u, levelJson v]
  | .imax u v => tagged "imax" [levelJson u, levelJson v]
  | .param i => tagged "param" [toJson i]

def exprJson : VExpr String → Json
  | .bvar i => tagged "bvar" [toJson i]
  | .sort u => tagged "sort" [levelJson u]
  | .const r us => tagged "const" [refJson r, .arr (us.map levelJson).toArray]
  | .app f a => tagged "app" [exprJson f, exprJson a]
  | .lam D b => tagged "lam" [exprJson D, exprJson b]
  | .forallE D B => tagged "forall" [exprJson D, exprJson B]
  | .letE t v b => tagged "let" [exprJson t, exprJson v, exprJson b]
  | .proj r i e => tagged "proj" [refJson r, toJson i, exprJson e]
  | .natLit r n => tagged "natLit" [refJson r, toJson n]

def constJson : Const String → Json
  | .axiom u t s => tagged "axiom" [toJson u, exprJson t, toJson (reprStr s)]
  | .defn u k t v s => tagged "defn" [toJson u, toJson (reprStr k), exprJson t, exprJson v, toJson (reprStr s)]
  | .quot k u t => tagged "quot" [toJson (reprStr k), toJson u, exprJson t]
  | .induct u p n t cs s => tagged "induct" [toJson u, toJson p, toJson n, exprJson t,
      .arr (cs.map fun c => tagged "constructor" [toJson c.uvars, toJson c.nparams,
        toJson c.nfields, exprJson c.type, toJson (reprStr c.safety)]).toArray, toJson (reprStr s)]
  | .recursor u p n mo mi t rs k s => tagged "recursor" [toJson u, toJson p, toJson n,
      toJson mo, toJson mi, exprJson t, .arr (rs.map fun r => tagged "rule"
        [toJson r.nfields, exprJson r.rhs]).toArray, toJson k, toJson (reprStr s)]

def outcomeJson (o : Outcome) : Json :=
  Json.mkObj [("outcome", toJson o.verdict.label), ("reason", toJson o.reason)]

def run : IO Unit := do
  let mut failed := false
  for c in cases do
    let k := certified c.fuel c.declarations
    let t ← match oracle c.declarations with
      | .ok result => pure result
      | .error reason => throw (IO.userError s!"test bridge failed for {c.name}: {reason}")
    let agrees := k.verdict == c.kernel && t.verdict == c.tc
    failed := failed || !agrees
    IO.println <| (Json.mkObj [
      ("schema", toJson (1 : Nat)), ("case", toJson c.name), ("lean", toJson Lean.versionString),
      ("fuel", toJson c.fuel), ("oracle", toJson "Ix.Tc/noAccel/preloaded"),
      ("expectedDifference", toJson c.difference), ("passed", toJson agrees),
      ("kernel", outcomeJson k), ("tc", outcomeJson t),
      ("input", .arr (c.declarations.map fun d => tagged "decl" [toJson d.address,
        .arr (d.block.members.map constJson).toArray]).toArray)]).compress
    unless agrees do
      IO.eprintln s!"{c.name}: kernel {k.verdict.label} ({k.reason}); Ix.Tc {t.verdict.label} ({t.reason})"
  if failed then throw (IO.userError "supported-profile differential gate failed")
  IO.eprintln s!"Certified differential gate passed: {cases.length} cases."

end Tests.Ix.Kernel.Differential

def main : IO Unit := Tests.Ix.Kernel.Differential.run
