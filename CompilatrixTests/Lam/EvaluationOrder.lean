import CompilatrixTests.Lam.Support
import Compilatrix.Src.Recheck

/-! Synthetic consumer-order controls through the actual table/relevance/Lazify
rechecker and erasure. Fake addresses and placeholder types deliberately make
no kernel, ingress, resource-profile, or final-producer admission claim. -/

namespace CompilatrixTests.Lam.EvaluationOrder

open Compilatrix Compilatrix.Src CompilatrixTests.Src

private def c (id : CId) : Term := .const id []

private def choose (cases : CId) (major left right : Term) : Term :=
  appM (c cases) [(irrArg, .irr), (major, .strict), (left, .strict), (right, .strict)]

private structure World where
  builder : Builder
  left : CId
  right : CId
  recursor : CId
  cases : CId
  emptyRec : CId
  loop : CId
  strictChoose : CId
  strictExtra : CId

private def world : World := Id.run do
  let (b, two) := ({} : Builder).add (.induct true 0 0 0 ty [])
  let (b, left) := b.add (.ctor true 0 two 0 0 0 (c two))
  let (b, right) := b.add (.ctor true 0 two 1 0 0 (c two))
  let b := b.setDecl two (.induct true 0 0 0 ty [left, right])
  let rules : List Rule :=
    [{ ctor := left, fields := 0, rhs := lams 3 (.var 1) },
     { ctor := right, fields := 0, rhs := lams 3 (.var 0) }]
  let (b, recursor) := b.add (.recr true false 0 0 1 2 0 two rules ty)
  let b := { b with recKind := b.recKind.set! recursor (some .ordinary) }
  -- cases motive major left right := recursor motive left right major.
  -- This body, unlike the older erasure fixture's placeholder, passes checkCase.
  let body := lams 4 (appM (c recursor)
    [(.var 3, .irr), (.var 1, .strict), (.var 0, .strict), (.var 2, .strict)])
  let (b, cases) := b.add (.defn .defn .safe 0 ty body)
  let b := { b with resolve := b.resolve.set! cases (some (.case recursor)) }
  let (b, empty) := b.add (.induct true 0 0 0 ty [])
  let (b, emptyRec) := b.add (.recr true false 0 0 1 0 0 empty [] ty)
  let b := { b with recKind := b.recKind.set! emptyRec (some .empty) }
  let loop := b.consts.size
  let (b, _) := b.add (.defn .defn .safe 0 ty (c loop))
  -- Ordinary strict delta wrapper; no lazy or case entry is proposed for it.
  let (b, strictChoose) := b.add (.defn .defn .safe 0 ty
    (lams 3 (choose cases (.var 2) (.var 1) (.var 0))))
  let trap := appM (c emptyRec) [(irrArg, .irr), (.natLit 0, .strict)]
  let (b, strictExtra) := b.add (.defn .defn .safe 0 ty
    (lam (app (choose cases (c left) trap (lam (.var 0))) [.var 0])))
  return {
    builder := b
    left
    right
    recursor
    cases
    emptyRec
    loop
    strictChoose
    strictExtra
  }

private def annotation (p : Program) : Relevance.Ann :=
  let keys := (Array.range p.size).flatMap fun k =>
    match p.decl? k with
    | some (.defn .defn .safe ..) => #[TermKey.value k]
    | some (.recr _ _ _ _ _ _ _ _ rules _) =>
      (Array.range rules.length).map (TermKey.rule k)
    | _ => #[]
  let consts : List (CId × Relevance.ConstRel) :=
    (List.range p.size).map fun k => (k, { result := Rel.rel, params := [] })
  let ctors : List (CId × Relevance.CtorRel) := (List.range p.size).filterMap fun k =>
    match p.decl? k with
    | some (.ctor _ _ _ _ _ nf _) => some (k, { fields := List.replicate nf .keep })
    | _ => none
  { consts := NatMap.ofList consts, ctors := NatMap.ofList ctors,
    nodes := keys.toList.filterMap fun k => (p.termOf k).map fun t => (k, t.tagOrder) }

private inductive Expected where
  | nat (n : Nat)
  | trap
  | timeout

private def Expected.src : Expected → Sem.Result Value → Bool
  | .nat n, .ok (.lit m) => n == m
  | .trap, .trap | .timeout, .timeout => true
  | _, _ => false

private def Expected.lam : Expected → Sem.Result Compilatrix.Lam.Val → Bool
  | .nat n, .ok (.lit (.nat m)) => n == m
  | .trap, .trap | .timeout, .timeout => true
  | _, _ => false

private def examples (w : World) : List (String × Term × Expected) :=
  let left := c w.left
  let right := c w.right
  let loop := c w.loop
  let trap := appM (c w.emptyRec) [(irrArg, .irr), (.natLit 0, .strict)]
  let select := choose w.cases
  let strict := fun major a b => app (c w.strictChoose) [major, a, b]
  let identity := lam (.var 0)
  [ ("direct-left-unused-loop", select left (.natLit 42) loop, .nat 42),
    ("direct-right-unused-loop", select right loop (.natLit 19), .nat 19),
    ("direct-left-selected-loop", select left loop (.natLit 19), .timeout),
    ("direct-right-selected-loop", select right (.natLit 42) loop, .timeout),
    ("strict-left-unused-loop", strict left (.natLit 42) loop, .timeout),
    ("strict-right-unused-loop", strict right loop (.natLit 19), .timeout),
    ("strict-left-finite", strict left (.natLit 42) (.natLit 19), .nat 42),
    ("strict-right-finite", strict right (.natLit 42) (.natLit 19), .nat 19),
    ("trap-positive", trap, .trap),
    ("extra-after-selected-trap", app (select left trap identity) [loop], .trap),
    ("extra-after-selected-loop", app (select left loop identity) [trap], .timeout),
    ("extra-finite", app (select left identity (lam (.natLit 19))) [.natLit 23], .nat 23),
    ("extra-unselected-trap", app (select right trap identity) [.natLit 23], .nat 23),
    ("extra-still-strict", app (select left (lam (.natLit 17)) loop) [loop], .timeout),
    ("wrapper-extra-before-trap", app (c w.strictExtra) [loop], .timeout),
    ("wrapper-extra-finite", app (c w.strictExtra) [.natLit 23], .trap) ]

private def modes (p : Program) (root : CId) : List Mode :=
  match p.decl? root with
  | some (.defn .defn .safe _ _ body) => body.spine.2.map (·.2.1)
  | _ => []

def run (a : Assert) : IO Unit := do
  let w := world
  let p := w.builder.program
  expect a (match Table.checkCase p w.cases with
    | .ok (.case r) => r == w.recursor
    | _ => false) "case-order: real case wrapper shape"
  expect a ((p.table.resolveOf w.strictChoose).isNone &&
    (p.table.lazyOf w.strictChoose).isNone) "case-order: ordinary strict wrapper route"
  for (label, value, expected) in examples w do
    let (b, root) := w.builder.add (.defn .defn .safe 0 ty value)
    let before := b.program #[root]
    let (checked, proof) ← match Src.Recheck.run {} before (annotation before) with
      | .ok result => pure result
      | .error _ => throw (IO.userError s!"case-order {label}: Src.Recheck refused synthetic fixture")
    if label.startsWith "direct-" || label.startsWith "extra-" then
      let ms := modes checked root
      expect a (ms.take 4 == [.strict, .strict, .byName, .byName]) s!"{label}: selected minors lazy"
      if label.startsWith "extra-" then
        expect a (ms.drop 4 == [.strict]) s!"{label}: extra remains strict"
    if label.startsWith "strict-" || label.startsWith "wrapper-" then
      expect a ((modes checked root).all (· == .strict)) s!"{label}: wrapper arguments strict"
    let e ← IO.ofExcept (erase checked proof)
    checkStatic a e label
    let target ← lamRoot e root
    for clock in [128, 512] do
      let sourceResult ← runSrc checked clock root []
      let targetResult ← runLam e.lam clock target []
      expect a (expected.src sourceResult) s!"{label}/{clock}: Src got {outcome sourceResult}"
      expect a (expected.lam targetResult) s!"{label}/{clock}: Lam got {lamOutcome targetResult}"

end CompilatrixTests.Lam.EvaluationOrder
