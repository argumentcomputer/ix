import CompilatrixTests.Lam.Support
import CompilatrixTests.Src.Relevance.Checker

/-! Erasure on synthetic Src programs (design note 02 §5.1, §13): one root
per form — constructor parameters (evaluated, kept or unboxed), `casesOn`
of every kind (ordinary with λ and non-λ minors, subsingleton, empty,
over-applied), recursors with `Nat.rec` IHs, quotients, wrappers of
unsaturated heads, the `Decidable ↦ Bool` alias, `lazy` by-name variants,
a recursor at two universe profiles and a projection out of a structure at
two profiles — each compared with SrcEval (readback, traps, timeouts, least
clocks) and checked `WellFormed` and `ModesOk`; and the named declines (a
non-λ minor dispatched by name, an unsaturated recursor dispatched by name,
a string, an ordinary eliminator with an irrelevant major). -/

namespace CompilatrixTests.Lam.Erase

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance CompilatrixTests.Src
open CompilatrixTests.Src.Relevance.Checker (annOf rootKeys setCtor)
open CompilatrixTests.Lam

/-- The base program plus the declarations these tests need. -/
structure World where
  bld : Builder
  b : Base
  box : CId
  boxMk : CId
  wrap : CId
  wrapMk : CId
  isNatCases : CId
  emptyCases : CId
  dec : CId
  decF : CId
  decT : CId
  decRec : CId
  decCases : CId
  loop : CId
  ident : CId
  myIte : CId

def world : World := Id.run do
  let (bld, b) := base
  let mut bld := bld
  let natT : Term := .const b.nat []
  -- `Box (p : Nat)` with `mk (x : Nat)`: a relevant parameter and one field
  -- (placeholder type: not unboxed).
  let (b1, box) := bld.add (.induct true 0 1 0 ty #[])
  let (b1, boxMk) := b1.add (.ctor true 0 box 0 1 1 ty)
  bld := b1.setDecl box (.induct true 0 1 0 ty #[boxMk])
  -- `Wrap` with `mk (x : Nat)`, a real constructor type: unboxed (S3).
  let (b1, wrap) := bld.add (.induct true 0 0 0 ty #[])
  let (b1, wrapMk) := b1.add (.ctor true 0 wrap 0 0 1 (.pi {} {} natT (.const wrap [])))
  bld := b1.setDecl wrap (.induct true 0 0 0 ty #[wrapMk])
  -- `casesOn` keys for the subsingleton `IsNat` and the empty type.
  let (b1, isNatCases) := bld.add (.defn .defn .safe 1 ty (lams 4 (.natLit 0)))
  bld := { b1 with resolve := b1.resolve.set! isNatCases (some (.case b.isNatRec)) }
  let (b1, emptyCases) := bld.add (.defn .defn .safe 1 ty (lams 2 (.natLit 0)))
  bld := { b1 with resolve := b1.resolve.set! emptyCases (some (.case b.emptyRec)) }
  -- `Decidable`-like: one Prop parameter, `isFalse (h)`, `isTrue (h)`.
  let (b1, dec) := bld.add (.induct true 0 1 0 ty #[])
  let (b1, decF) := b1.add (.ctor true 0 dec 0 1 1 ty)
  let (b1, decT) := b1.add (.ctor true 0 dec 1 1 1 ty)
  bld := b1.setDecl dec (.induct true 0 1 0 ty #[decF, decT])
  let (b1, decRec) := bld.add (.recr true false 1 1 1 2 0 dec
    #[{ ctor := decF, fields := 1, rhs := lams 5 (appM (.var 2) [(irrArg, .irr)]) },
      { ctor := decT, fields := 1, rhs := lams 5 (appM (.var 1) [(irrArg, .irr)]) }] ty)
  bld := { b1 with recKind := b1.recKind.set! decRec (some .ordinary) }
  let (b1, decCases) := bld.add (.defn .defn .safe 1 ty (lams 5 (.natLit 0)))
  bld := { b1 with resolve := b1.resolve.set! decCases (some (.case decRec)) }
  let loopId := bld.consts.size
  let (b1, loop) := bld.add (.defn .defn .safe 0 ty (.const loopId []))
  let (b1, ident) := b1.add (.defn .defn .safe 0 ty (lam (.var 0)))
  -- myIte c t e := Bool.casesOn motive c e t (lazy, arity 3).
  let (b1, myIte) := b1.add (.defn .defn .safe 0 ty (lams 3
    (appM (.const b.boolCases [.zero]) [(irrArg, .irr), (.var 2, .strict), (.var 0, .strict),
      (.var 1, .strict)])))
  bld := { b1 with lazy := b1.lazy.set! myIte (some 3)
                   known := { b1.known with decIsFalse := some decF, decIsTrue := some decT } }
  return { bld, b, box, boxMk, wrap, wrapMk, isNatCases, emptyCases, dec, decF, decT, decRec,
           decCases, loop, ident, myIte }

def c (id : CId) : Term := .const id []
def lit (n : Nat) : Term := .natLit n
def n0 : Term := .var 0

/-- A program with one root definition, its annotation (every field kept
except where the world says otherwise), checked and lazified. -/
def prepare (w : World) (value : Term) : Except String (Program × Checked) := do
  let (bld, root) := w.bld.add (.defn .defn .safe 0 ty value)
  let p := bld.program #[root]
  let ann := annOf p (rootKeys p)
  let ann := setCtor ann w.decF #[FieldClass.prf]
  let ann := setCtor ann w.decT #[FieldClass.prf]
  let ann := setCtor ann w.b.ppairMk #[.proof (.allZero [0]), .keep]
  match check p ann with
  | .ok ch => return (Lazify.run p ch.keys, ch)
  | .error es => throw s!"checker: {es.toList.map (·.render p)}"

def rootOf (p : Program) : CId := (p.roots[0]?.map (·.2)).getD 0

/-- One accepted case: erase, check statically, compare on the arguments. -/
def accepted (a : Assert) (w : World) (label : String) (value : Term) (argss : List (List Nat))
    (t : Tally) : IO (Tally × Erased) := do
  let (p, ch) ← IO.ofExcept (prepare w value)
  let e ← match CompilatrixTests.Lam.erase p ch with
    | .ok e => pure e
    | .error msg => throw (IO.userError s!"{label}: declined: {msg}")
  checkStatic a e label
  let mut t := t
  for args in argss do
    t ← compareRun a e (rootOf p) args 10000 label t
  return (t, e)

/-- One declined case, with its code. -/
def declined (a : Assert) (w : World) (label : String) (value : Term) (code : String) :
    IO Unit := do
  let (p, ch) ← IO.ofExcept (prepare w value)
  match Compilatrix.Lam.erase p ch with
  | .ok _ => expect a false s!"{label}: erased, expected the decline {code}"
  | .error e => expect a (e.code == code) s!"{label}: declined with {e.code}, expected {code}: {e}"

/-- A declined case the checker would already reject (tier C): erased from
the annotation's records without the checker. -/
def declinedUnchecked (a : Assert) (w : World) (label : String) (value : Term) (code : String) :
    IO Unit := do
  let (bld, root) := w.bld.add (.defn .defn .safe 0 ty value)
  let p := bld.program #[root]
  let ann := annOf p (rootKeys p)
  let ch : Checked := { keys := #[], reached := #[], instances := #[], consts := ann.consts
                        ctors := ann.ctors }
  expect a ((check p ann) matches .error _) s!"{label}: the checker rejects it"
  match Compilatrix.Lam.erase p ch with
  | .ok _ => expect a false s!"{label}: erased, expected the decline {code}"
  | .error e => expect a (e.code == code) s!"{label}: declined with {e.code}, expected {code}: {e}"

def motive : Term × A := (irrArg, .irr)

def natArgs : List (List Nat) := [[0], [1], [2], [5]]

def keys (e : Erased) : List Key.GKey := e.lam.globalList.map (·.2.key)

def run (a : Assert) : IO (Array String) := do
  let w := world
  let b := w.b
  let mut t : Tally := {}
  let mut out := #[]
  -- Constructors: a relevant parameter is evaluated and discarded; a field
  -- is projected by its kept rank; an unboxed structure is its field.
  let (t1, _) ← accepted a w "constructor parameter"
    (lam (.proj w.box 0 (app (c w.boxMk) [n0, app (c b.add) [n0, lit 1]]))) natArgs t
  t := t1
  let (t1, _) ← accepted a w "a diverging parameter"
    (lam (.proj w.box 0 (app (c w.boxMk) [c w.loop, n0]))) [[3]] t
  t := t1
  let (t1, _) ← accepted a w "a trapping parameter"
    (lam (.proj w.box 0 (app (c w.boxMk) [appM (c b.emptyRec) [motive, (irrArg, .irr)], n0])))
    [[3]] t
  t := t1
  let (t1, _) ← accepted a w "a constructor value" (lam (app (c w.boxMk) [lit 9, n0])) natArgs t
  t := t1
  let (t1, eu) ← accepted a w "unboxed structure"
    (lam (.proj w.wrap 0 (app (c w.wrapMk) [app (c b.add) [n0, lit 2]]))) natArgs t
  t := t1
  expect a (eu.lam.ctors.all (·.key != .src w.wrapMk)) "an unboxed constructor has no table row"
  let (t1, _) ← accepted a w "unboxed value" (lam (app (c w.wrapMk) [n0])) natArgs t
  t := t1
  -- casesOn: ordinary (λ and non-λ minors, over-applied), subsingleton, empty.
  let (t1, _) ← accepted a w "Nat.casesOn"
    (lam (appM (.const b.natCases [.zero]) [motive, (n0, .strict), (lit 10, .strict),
      (lam (app (c b.add) [n0, n0]), .strict)])) natArgs t
  t := t1
  let (t1, _) ← accepted a w "Nat.casesOn with a non-λ minor"
    (lam (appM (.const b.natCases [.zero]) [motive, (n0, .strict), (lit 3, .strict),
      (c w.ident, .strict)])) natArgs t
  t := t1
  let (t1, _) ← accepted a w "over-applied Nat.casesOn"
    (lam (appM (.const b.natCases [.zero]) [motive, (n0, .strict), (lam n0, .strict),
      (lams 2 n0, .strict), (n0, .strict)])) natArgs t
  t := t1
  let (t1, _) ← accepted a w "Bool.casesOn on a primitive"
    (lam (appM (.const b.boolCases [.zero]) [motive, (app (c b.beq) [n0, lit 0], .strict),
      (lit 1, .strict), (lit 2, .strict)])) natArgs t
  t := t1
  let (t1, _) ← accepted a w "subsingleton casesOn (fields from the index)"
    (lam (appM (.const w.isNatCases [.zero]) [motive, (n0, .strict), (irrArg, .irr),
      (lam (app (c b.add) [n0, lit 1]), .strict)])) natArgs t
  t := t1
  let (t1, _) ← accepted a w "empty casesOn traps"
    (lam (appM (.const w.emptyCases [.zero]) [motive, (irrArg, .irr)])) natArgs t
  t := t1
  -- Recursors: r⋆ with a by-name IH; subsingleton and empty recursors.
  let (t1, er) ← accepted a w "Nat.rec with an IH"
    (lam (appM (.const b.natRec [.zero]) [motive, (lit 0, .strict),
      (lams 2 (app (c b.add) [n0, lit 2]), .strict), (n0, .strict)])) natArgs t
  t := t1
  expect a (keys er |>.any (· matches .recStar ..)) "Nat.rec is erased to r⋆"
  let (t1, _) ← accepted a w "subsingleton recursor"
    (lam (appM (.const b.isNatRec [.zero]) [motive, (lam (app (c b.add) [n0, lit 1]), .strict),
      (n0, .strict), (irrArg, .irr)])) natArgs t
  t := t1
  let (t1, _) ← accepted a w "empty recursor traps"
    (lam (appM (.const b.emptyRec [.zero]) [motive, (irrArg, .irr)])) natArgs t
  t := t1
  -- Quotients.
  let (t1, _) ← accepted a w "Quot.lift of Quot.mk"
    (lam (appM (.const b.quotLift [.zero, .zero]) [(irrArg, .irr), (irrArg, .irr), (irrArg, .irr),
      (lam (app (c b.add) [n0, lit 1]), .strict), (irrArg, .irr),
      (appM (.const b.quotMk [.zero]) [(irrArg, .irr), (irrArg, .irr), (n0, .strict)], .strict)]))
    natArgs t
  t := t1
  -- Wrappers of unsaturated special heads (Lam needs a larger clock).
  let (t1, ew) ← accepted a w "unsaturated primitive"
    (lam (.app (lam (app (.var 0) [.var 1, lit 1])) (c b.add) .strict .rel)) natArgs t
  t := t1
  expect a (hasWrappers ew.lam) "an unsaturated primitive goes through a wrapper"
  let (t1, _) ← accepted a w "unsaturated constructor"
    (lam (.app (lam (.proj b.pair 1 (app (.var 0) [.var 1, lit 7]))) (c b.pairMk) .strict .rel))
    natArgs t
  t := t1
  let (t1, _) ← accepted a w "unsaturated casesOn"
    (lam (.app (lam (appM (.var 0) [motive, (.var 1, .strict), (lit 4, .strict),
      (lam n0, .strict)])) (.const b.natCases [.zero]) .strict .rel)) natArgs t
  t := t1
  -- The Decidable ↦ Bool alias (D19).
  let decMinor := fun (n : Nat) => lam (lit n) { rel := Rel.prf }
  let (t1, ed) ← accepted a w "Decidable.casesOn on isTrue"
    (lam (appM (.const w.decCases [.zero]) [(irrArg, .irr), motive,
      (appM (c w.decT) [(irrArg, .irr), (irrArg, .irr)], .strict),
      (decMinor 0, .strict), (decMinor 1, .strict)])) natArgs t
  t := t1
  let (t1, ed2) ← accepted a w "a Decidable value"
    (lam (appM (c w.decF) [(irrArg, .irr), (irrArg, .irr)])) natArgs t
  t := t1
  expect a ((ed.lam.ctors ++ ed2.lam.ctors).all fun r =>
      r.key != .src w.decF && r.key != .src w.decT)
    "Decidable constructors are retagged as Bool's"
  -- lazy: the by-name variant evaluates only the branch taken.
  let (t1, el) ← accepted a w "lazy by-name variant"
    (lam (app (c w.myIte) [app (c b.beq) [n0, lit 0], lit 10, c w.loop])) natArgs t
  t := t1
  expect a (keys el |>.any (· matches .byName ..)) "a saturated lazy spine uses the by-name variant"
  -- One recursor at two profiles: two globals.
  let unitAt := fun (u : Nat) (minor : Nat) (major : A) =>
    let lv : Ixon.Univ := if u == 0 then .zero else .succ .zero
    appM (.const b.unitRec [.succ .zero, lv]) [motive, (lit minor, .strict),
      (.const b.unitMk [lv], major)]
  let (t1, e2) ← accepted a w "a recursor at two profiles"
    (lam (app (c b.add) [unitAt 0 3 .irr, unitAt 1 4 .strict])) natArgs t
  t := t1
  expect a (((keys e2).filter (· matches .recStar ..)).length == 2)
    "PUnit.rec at u = 0 and u = 1 are two r⋆ globals"
  -- Declines.
  declined a w "a non-λ minor dispatched by name"
    (lams 2 (appM (.const b.natRec [.zero]) [motive, (lit 0, .strict), (.var 1, .strict),
      (n0, .strict)])) "erase-minor"
  declined a w "an unsaturated recursor dispatched by name"
    (lam (.app (lam (appM (.var 0) [motive, (lit 0, .strict), (lams 2 n0, .strict),
        (.var 1, .strict)]))
      (.const b.natRec [.zero]) .strict .rel)) "erase-minor"
  -- A structure whose first field is a proof exactly at u = 0: one layout
  -- (□ in that field at u = 0), so a projection needs no profile.
  let (t1, ep) ← accepted a w "a sort-polymorphic projection"
    (lam (app (c b.add) [.proj b.ppair 1 (app (.const b.ppairMk [.succ .zero]) [n0, n0]),
      .proj b.ppair 1 (appM (.const b.ppairMk [.zero]) [(irrArg, .irr), (n0, .strict)])]))
    natArgs t
  t := t1
  expect a (ep.lam.ctors.any fun r => r.key == .src b.ppairMk && r.arity == 2)
    "one layout for a structure at two profiles"
  declined a w "a string" (lam (.strLit "s")) "erase-string"
  declinedUnchecked a w "casesOn with an irrelevant major (C4)"
    (lam (appM (.const b.natCases [.zero]) [motive, (irrArg, .irr), (lit 1, .byName),
      (lam n0, .byName)])) "erase-C4"
  declinedUnchecked a w "a recursor with an irrelevant major (C4)"
    (lam (appM (.const b.natRec [.zero]) [motive, (lit 0, .byName),
      (lams 2 n0, .byName), (irrArg, .irr)])) "erase-C4"
  out := out.push s!"synthetic: {t.render}"
  return out

end CompilatrixTests.Lam.Erase
