import IxCCTests.KernelFront.Reference
import IxCCTests.Support.Bound
import IxCCTests.Src.Support
import IxCC.Recheck

/-! # The annotator's λ-runs against the per-λ reference

Since 2026-11-13 `Src.KernelFront.annotate` asks the kernel for a λ's condition once per maximal
run of λs, of the run's innermost body (`walk`'s `run`, `Ctx.openLams`), and `Ctx.sortCond`
continues with the empty memo when the kernel fails it. The reference (`Reference.annotate`) is
the definition it replaced: the kernel asked at every λ, the pre-call state kept. The two are not
proved equal: they agree because the sort of `Π x : A, B` is `imax` of the two sorts, whose zero
condition is `B`'s, and because the memo only caches the kernel's answers (an answer can depend
on it only where the kernel's fuel decides). This part tests that they agree:

* on every committed role-bound closure under `fixtures/` (the corpus, `fixtures/rc/`, the
  benchmarks' and the rest; `Run` passes the list and skips the closures the kernel declines or
  ingress refuses), each with every root of its sidecar at once, its table built and validated as
  the producer builds it, and root by root where the whole program is refused;
* on adversarial programs built on the role-bound base (`adversarial`): runs whose innermost
  body is function-typed (η-short), runs interrupted by a `let` or a β-redex, an erased binder in
  a run, runs over universe parameters whose body is a proof at some assignments only (`Sort u`,
  `Sort (max u v)` both ways round, `Sort (imax u v)`), a body that is always a proof, a body
  that is a type, a λ inside a binder's type, a run of 102 binders, a run in function position,
  and a large eliminator's rules (whose motive's level the reader renames);

and `IxCCTests/Recheck/Erased.lean` compares the two on every program it ingests. Equal means
the same annotation (`Ann.eqb`), or the same refusal message. The times of both over the
committed closures are printed (box evidence of Stage A's cost before and after). -/

namespace IxCCTests.KernelFront.LamRuns

open IxCC IxCC.Src IxCC.Src.Relevance
open IxCCTests.Src (Assert expect)

structure Tally where
  programs : Nat := 0
  terms : Nat := 0
  lams : Nat := 0
  /-- λ tags whose condition is not `never` -/
  conditional : Nat := 0
  /-- λs (in the terms compared) whose body is a λ: the positions the change touches -/
  runInner : Nat := 0
  /-- programs both refuse, with the same message -/
  bothRefuse : Nat := 0
  /-- roots (or closures without named roots) ingress refuses: no program to compare -/
  ingressRefused : Nat := 0
  newMs : Nat := 0
  oldMs : Nat := 0
  differences : Array String := #[]

/-- λ nodes of a Src term whose body is a λ. -/
partial def lamInLam : Term → Nat
  | .lam _ d body =>
    (match body with | .lam .. => 1 | _ => 0) + lamInLam d + lamInLam body
  | .app f a _ _ => lamInLam f + lamInLam a
  | .pi _ _ d c => lamInLam d + lamInLam c
  | .letE _ _ ty v body => lamInLam ty + lamInLam v + lamInLam body
  | .proj _ _ e => lamInLam e
  | _ => 0

def countTags (t : Tally) (p : Program) (ann : Ann) : Tally := Id.run do
  let mut t := t
  for (key, tags) in ann.nodes do
    t := { t with terms := t.terms + 1 }
    for tag in tags do
      if let .lam _ pw := tag then
        t := { t with lams := t.lams + 1, conditional := t.conditional + (if pw == .never then 0 else 1) }
    if let some term := p.termOf key then t := { t with runInner := t.runInner + lamInLam term }
  return t

/-- The new annotator and the reference on `p` (a program with its table); `some` the difference. -/
def compareOn (k : KernelFront.Kernel) (p : Program) (t : Tally) : IO (Tally × Option String) := do
  let t0 ← IO.monoMsNow
  let n ← IO.lazyPure fun _ => KernelFront.annotate k.fe k.rd p
  let t1 ← IO.monoMsNow
  let o ← IO.lazyPure fun _ => Reference.annotate k.fe k.rd p
  let t2 ← IO.monoMsNow
  let t := { t with programs := t.programs + 1, newMs := t.newMs + (t1 - t0), oldMs := t.oldMs + (t2 - t1) }
  match n, o with
  | .ok a, .ok b =>
    if a.eqb b then return (countTags t p a, none)
    let firstDiff := (a.nodes.zip b.nodes).find? (fun (x, y) => x != y)
    return (t, some s!"the annotations differ (consts {decide (a.consts = b.consts)}, ctors \
      {decide (a.ctors = b.ctors)}, nodes {a.nodes.length}/{b.nodes.length}); first differing term: \
      {(firstDiff.map fun (x, y) => s!"{repr x.1}: new {repr x.2} / old {repr y.2}").getD "none"}")
  | .error m, .error m' =>
    if m == m' then return ({ t with bothRefuse := t.bothRefuse + 1 }, none)
    return (t, some s!"both refuse, with different messages: new {m.take 300} / old {m'.take 300}")
  | .ok _, .error m => return (t, some s!"the new annotator accepts, the reference refuses: {m.take 300}")
  | .error m, .ok _ => return (t, some s!"the new annotator refuses, the reference accepts: {m.take 300}")

/-- Ingress with every root, the table as the producer builds it, the two annotators; root by
root when both refuse the whole program. -/
def compareInput (label : String) (inp : Recheck.Input) (t : Tally) : IO Tally := do
  let cfg := Recheck.Config.forInput {} inp
  let P := inp.program
  let (table, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let p0 := { P with table }
  let (t, d) ← compareOn inp.kernel p0 t
  let mut t := match d with
    | some m => { t with differences := t.differences.push s!"{label}: {m}" }
    | none => t
  match KernelFront.annotate inp.kernel.fe inp.kernel.rd p0 with
  | .ok _ => return t
  | .error _ =>
    if P.roots.length > 1 then
      for r in P.roots do
        let (t', d) ← compareOn inp.kernel { p0 with roots := [r] } t
        t := match d with
          | some m => { t' with differences := t'.differences.push s!"{label} (root {r.2}): {m}" }
          | none => t'
    return t

/-- Ingress with every root of the sidecar; where that is refused, each named root alone. -/
def compareBytes (label : String) (bytes : ByteArray) (json : Lean.Json) (t : Tally) : IO Tally := do
  match Recheck.ingress bytes json [] with
  | .ok inp => compareInput label inp t
  | .error _ =>
    let names : List String := match Src.Hints.ofK1Json json with
      | .ok h => h.roots.toList.filterMap fun (r : IxCC.Ixon.Address × Option String) => r.2
      | .error _ => []
    let mut t := t
    for n in names do
      match Recheck.ingress bytes json [n] with
      | .ok inp => t ← compareInput s!"{label} ({n})" inp t
      | .error _ => t := { t with ingressRefused := t.ingressRefused + 1 }
    if names.isEmpty then t := { t with ingressRefused := t.ingressRefused + 1 }
    return t

/-- Every committed closure the caller gives (with its sidecar). -/
def onClosures (closures : Array (System.FilePath × System.FilePath)) : IO Tally := do
  let mut t : Tally := {}
  for (path, sidecar) in closures do
    let bytes ← IO.FS.readBinFile path
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile sidecar))
    t ← compareBytes path.toString bytes json t
  return t

/-! ## Adversarial programs -/

abbrev X := IxCC.Ixon.V3.Expr
open IxCC.Ixon.V3 (BinderContract)
open IxCCTests.IxonV3.Builder (store arrow lambda)

def dfn (lvls : Nat) (ty val : X) : IxCC.Ixon.V3.ConstantInfo := .defn ⟨.defn, .safe, lvls.toUInt64, ty, val⟩

def sidecar (roots : List (String × IxCC.Ixon.Address)) : Lean.Json :=
  Lean.Json.mkObj [
    ("format", Lean.Json.str "ixcc/k1-equations/1"),
    ("roots", Lean.Json.arr (roots.map fun (n, a) =>
      Lean.Json.mkObj [("name", Lean.Json.str n), ("address", Lean.Json.str (toString a))]).toArray),
    ("equations", Lean.Json.arr #[])]

/-- `λ x₁ … xₙ, body` over the same binder type. -/
def lams (n : Nat) (ty body : X) : X := (List.range n).foldl (fun b _ => lambda ty b) body

def arrows (n : Nat) (ty res : X) : X := (List.range n).foldl (fun b _ => arrow ty b) res

/-- The adversarial programs, every definition a root. -/
def adversarialEnv : IO (IxCC.Ixon.V3.Env × List (String × IxCC.Ixon.Address)) := do
  let (e, en) := IxCCTests.Support.Bound.addEnum (← IxCCTests.Support.Bound.loadBase) 3
  let (e, tr) := IxCCTests.Support.Bound.addTree e
  let E : X := .ref 0 #[]
  let c (i : Nat) := en.ctors[i]!
  let (e, idc) := store e ⟨dfn 0 (arrow E E) (lambda E (.var 0)), #[], #[en.ind], #[]⟩
  -- an η-short innermost body: λ x y, idc
  let (e, etaShort) := store e ⟨dfn 0 (arrow E (arrow E (arrow E E))) (lambda E (lambda E (.ref 1 #[]))),
    #[], #[en.ind, idc], #[]⟩
  -- a run interrupted by a let: λ x, let z := x; λ y, z
  let (e, letRun) := store e ⟨dfn 0 (arrow E (arrow E E)) (lambda E (.letE (.lean false) E (.var 0) (lambda E (.var 1)))),
    #[], #[en.ind], #[]⟩
  -- a run whose body is a β-redex of another run: λ x, (λ y w, y) x
  let (e, betaBody) := store e ⟨dfn 0 (arrow E (arrow E E))
    (lambda E (.app (lambda E (lambda E (.var 1))) (.var 0))), #[], #[en.ind], #[]⟩
  -- an erased binder in a run: λ (x :₀ E) (y : E), y
  let (e, erasedRun) := store e ⟨dfn 0 (.all BinderContract.erased .shared E (arrow E E))
    (.lam BinderContract.erased E (lambda E (.var 0))), #[], #[en.ind], #[]⟩
  -- universe parameters: λ (α : Sort u) (a b : α), b
  let (e, poly) := store e ⟨dfn 1 (.all .many .shared (.sort 0) (arrow (.var 0) (arrow (.var 1) (.var 2))))
    (lambda (.sort 0) (lambda (.var 0) (lambda (.var 1) (.var 0)))), #[], #[], #[.var 0]⟩
  -- λ (α : Sort u) (β : Sort v) (a : α) (b : β), b
  let (e, poly2) := store e ⟨dfn 2 (.all .many .shared (.sort 0) (.all .many .shared (.sort 1)
      (arrow (.var 1) (arrow (.var 1) (.var 2)))))
    (lambda (.sort 0) (lambda (.sort 1) (lambda (.var 1) (lambda (.var 1) (.var 0))))), #[], #[], #[.var 0, .var 1]⟩
  -- λ (γ : Sort ℓ) (c d : γ), d at ℓ = max u v, max v u, imax u v, imax (u+1) v
  let gammaRun (ℓ : IxCC.Ixon.Univ) : IxCC.Ixon.V3.Constant :=
    ⟨dfn 2 (.all .many .shared (.sort 0) (arrow (.var 0) (arrow (.var 1) (.var 2))))
      (lambda (.sort 0) (lambda (.var 0) (lambda (.var 1) (.var 0)))), #[], #[], #[ℓ]⟩
  let (e, maxUV) := store e (gammaRun (.max (.var 0) (.var 1)))
  let (e, maxVU) := store e (gammaRun (.max (.var 1) (.var 0)))
  let (e, imaxUV) := store e (gammaRun (.imax (.var 0) (.var 1)))
  let (e, imaxSV) := store e (gammaRun (.imax (.succ (.var 0)) (.var 1)))
  -- always a proof: λ (P : Prop) (h : P) (x : E), h
  let (e, prfRun) := store e ⟨dfn 0 (.all .many .shared (.sort 0) (arrow (.var 0) (arrow (.ref 0 #[]) (.var 2))))
    (lambda (.sort 0) (lambda (.var 0) (lambda (.ref 0 #[]) (.var 1)))), #[], #[en.ind], #[.zero]⟩
  -- a body that is a type: λ x y, Prop
  let (e, sortBody) := store e ⟨dfn 0 (arrow E (arrow E (.sort 1))) (lambda E (lambda E (.sort 0))),
    #[], #[en.ind], #[.zero, .succ .zero]⟩
  -- a λ inside a binder's type: λ (y : (λ x, E) c₀) (z : E), y
  let redex : X := .app (lambda E E) (.ref 1 #[])
  let (e, typeLam) := store e ⟨dfn 0 (arrow redex (arrow E E)) (lambda redex (lambda E (.var 1))),
    #[], #[en.ind, c 0], #[]⟩
  -- a run of 102 binders over a universe parameter: λ (α : Sort u) x₁ … x₁₀₀ (a : α), a
  let (e, deep) := store e ⟨dfn 1 (.all .many .shared (.sort 0) (arrows 100 (.ref 0 #[]) (arrow (.var 100) (.var 101))))
    (lambda (.sort 0) (lams 100 (.ref 0 #[]) (lambda (.var 100) (.var 0)))), #[], #[en.ind], #[.var 0]⟩
  -- a run in function position: (λ x y, x) c₀ c₁
  let (e, argRun) := store e ⟨dfn 0 E (.app (.app (lambda E (lambda E (.var 1))) (.ref 1 #[])) (.ref 2 #[])),
    #[], #[en.ind, c 0, c 1], #[]⟩
  -- the level-polymorphic ones used at concrete levels (`univs` here: `0` is `1`, `1` is `0`),
  -- and a large eliminator's rules: T.rec.{1} (λ _, E) c₀ (λ l r il ir, il) leaf
  let use (f : IxCC.Ixon.Address) (us : Array UInt64) (types : Nat) (vals : List X) : IxCC.Ixon.V3.Constant :=
    let head : X := (List.range types).foldl (fun h _ => .app h (.ref 0 #[])) (.ref 1 us)
    ⟨dfn 0 E (vals.foldl (fun h v => .app h v) head), #[], #[en.ind, f, c 0, c 1], #[.succ .zero, .zero]⟩
  let two : List X := [.ref 2 #[], .ref 3 #[]]
  let (e, usePoly) := store e (use poly #[0] 1 two)
  let (e, usePoly2) := store e (use poly2 #[0, 0] 2 two)
  let (e, useMaxUV) := store e (use maxUV #[0, 0] 1 two)
  let (e, useMaxVU) := store e (use maxVU #[0, 0] 1 two)
  let (e, useImaxUV) := store e (use imaxUV #[0, 0] 1 two)
  let (e, useImaxSV) := store e (use imaxSV #[1, 0] 1 two)
  let (e, useDeep) := store e (use deep #[0] 1 (List.replicate 100 (.ref 2 #[]) ++ [.ref 3 #[]]))
  let T : X := .ref 2 #[]
  let (e, useRec) := store e ⟨dfn 0 E (.app (.app (.app (.app (.ref 1 #[0]) (lambda T (.ref 0 #[])))
      (.ref 3 #[])) (lambda T (lambda T (lambda E (lambda E (.var 1)))))) (.ref 4 #[])),
    #[], #[en.ind, tr.recursor, tr.ind, c 0, tr.ctors[0]!], #[.succ .zero]⟩
  let roots := [("etaShort", etaShort), ("letRun", letRun), ("betaBody", betaBody), ("erasedRun", erasedRun),
    ("prfRun", prfRun), ("sortBody", sortBody), ("typeLam", typeLam), ("argRun", argRun),
    ("usePoly", usePoly), ("usePoly2", usePoly2), ("useMaxUV", useMaxUV), ("useMaxVU", useMaxVU),
    ("useImaxUV", useImaxUV), ("useImaxSV", useImaxSV), ("useDeep", useDeep), ("useRec", useRec)]
  return (e, roots)

/-- The adversarial programs: all roots at once, then each root alone (its own ingress). -/
def adversarial : IO Tally := do
  let (e, roots) ← adversarialEnv
  let bytes := IxCCTests.Support.Bound.write e
  let json := sidecar roots
  let mut t ← compareBytes "adversarial" bytes json {}
  for (name, _) in roots do
    match Recheck.ingress bytes json [name] with
    | .ok inp => t ← compareInput s!"adversarial {name}" inp t
    | .error err => t := { t with differences := t.differences.push s!"adversarial {name}: ingress refused: {err.render.take 300}" }
  return t

def Tally.render (t : Tally) : String :=
  s!"{t.programs} programs, {t.terms} terms, {t.lams} λ tags ({t.conditional} with a condition other than \
    never), {t.runInner} λs whose body is a λ; {t.bothRefuse} refused by both with the same message; \
    {t.ingressRefused} roots refused at ingress; {t.differences.size} differences; annotator time \
    {t.newMs} ms (per λ-run) against {t.oldMs} ms (per λ)"

/-- The suite part: the committed closures, then the adversarial programs. -/
def run (a : Assert) (closures : Array (System.FilePath × System.FilePath)) : IO (Array String) := do
  let c ← onClosures closures
  for d in c.differences do IO.eprintln s!"  {d}"
  expect a (c.differences.isEmpty && c.ingressRefused == 0 && c.programs ≥ closures.size)
    s!"λ-runs: the committed closures: {c.differences.size} differences"
  let v ← adversarial
  for d in v.differences do IO.eprintln s!"  {d}"
  expect a (v.differences.isEmpty && v.ingressRefused == 0 && v.conditional > 0 && v.runInner > 100)
    s!"λ-runs: the adversarial programs: {v.differences.size} differences ({v.conditional} conditional λ tags)"
  return #[s!"λ-runs against the per-λ reference, the committed closures: {c.render}",
           s!"λ-runs against the per-λ reference, the adversarial programs: {v.render}"]

/-- For other suites: the two annotators on one ingested program (its table built as the
producer builds it); an `IO` error on any difference. -/
def agree (label : String) (inp : Recheck.Input) : IO Unit := do
  let t ← compareInput label inp {}
  unless t.differences.isEmpty do
    throw (IO.userError s!"{label}: the λ-run annotator differs from the per-λ reference: {t.differences}")

end IxCCTests.KernelFront.LamRuns
