import IxCC.Src.KernelFront.Annotate
import IxCCGrounding.Direct.Check

/-! # The kernel as an oracle for the direct route (`tests-grounding`)

`sitesDirectB` (`IxCCGrounding.Direct.Check`) decides that the application sites SrcEval may
evaluate are typed, by its own small conversion. Its soundness is proved (`direct_sound`); this
module asks an independent implementation the same question, the kernel's cached typing core
(the core the front end runs over the closure, `KernelFront.coreOf`), at every site the check
accepts:

* **agreement**: at each profile at which the site is evaluated, the kernel infers the function
  part's type, reduces it to a `∀` whose domain is definitionally equal to the argument's
  inferred type, and the `∀`'s binder datum is "not a proposition" at that profile (the graph
  regime the check requires);
* **refusal where the datum holds**: an accepted site whose kernel binder datum is "a
  proposition" at some profile of its constant's level parameters is re-checked at that profile
  alone, where the check must refuse it;
* **self-check**: the positions the walk refuses are, in number, the sites `runRefused` (the set
  the theorems quantify over) returns.

Every site of a run term is visited exactly as `termRefused` visits it (each maximal evaluated
spine once, at the profiles at which it is evaluated). Agreement is evidence that the check's
conversion is no more permissive than the kernel's at these sites, not a proof.
-/

namespace IxCCTests.Grounding.Oracle

open IxCC IxCC.Grounding
open Ix.Kernel (PropWhen)
open IxCC.Src (Term CId Program)

abbrev Core := Ix.Kernel.Cached.CoreFnsI .anon

/-- `e` with the variables of a context of `n` binders, at depth `k`, replaced by the kernel's
free variables `0 … n-1` (outermost first), each with its domain in `doms`. -/
def closeF (doms : Array KExpr) (n : Nat) : Nat → KExpr → KExpr
  | k, .bvar i =>
    if i ≥ k then
      let j := i - k
      if j < n then .fvar (n - 1 - j) (doms.getD (n - 1 - j) (.sort .zero)) else .bvar (i - n)
    else .bvar i
  | k, .app f a => .app (closeF doms n k f) (closeF doms n k a)
  | k, .lam d b m => .lam (closeF doms n k d) (closeF doms n (k + 1) b) m
  | k, .forallE d b m => .forallE (closeF doms n k d) (closeF doms n (k + 1) b) m
  | k, .letE t v b m =>
    .letE (closeF doms n k t) (closeF doms n k v) (closeF doms n (k + 1) b) m
  | k, .proj s i e => .proj s i (closeF doms n k e)
  | _, e => e

/-- The context `Γ` (innermost first) as the kernel's free variables' domains, outermost first,
each closed over the ones before it. -/
def openCtx (Γ : List KExpr) : Array KExpr := Id.run do
  let n := Γ.length
  let mut doms : Array KExpr := #[]
  for j in [0:n] do
    let T := Γ.getD (n - 1 - j) (.sort .zero)
    doms := doms.push (closeF doms j 0 T)
  return doms

/-- **The kernel's typing of a site**, profile-free: whether `f`'s inferred type reduces to a `∀`
whose domain is definitionally equal to `a`'s inferred type, and that `∀`'s binder datum. -/
def kernelSite (core : Core) (Γ : List KExpr) (f a : KExpr) : Except String (Bool × PropWhen) :=
  let doms := openCtx Γ
  let n := Γ.length
  let r := (do
    let f' ← core.annotate n (closeF doms n 0 f)
    let a' ← core.annotate n (closeF doms n 0 a)
    let tf ← core.infer n f'
    let tf ← core.whnf n tf
    match tf with
    | .forallE A _ m =>
      let ta ← core.infer n a'
      let ok ← core.defeq n ta A
      pure (ok, m.pw)
    | _ => pure (false, PropWhen.never) : Ix.Kernel.Cached.CheckCM .anon (Bool × PropWhen))
    ({} : Ix.Kernel.Cached.CState .anon)
  match r with
  | .ok (b, _) => .ok b
  | .error e => .error s!"{e}"

/-- **The kernel's head normal form** of a closed term. -/
def kernelWhnf (core : Core) (e : KExpr) : Except String KExpr :=
  let r := (do
    let e' ← core.annotate 0 e
    core.whnf 0 e' : Ix.Kernel.Cached.CheckCM .anon KExpr) ({} : Ix.Kernel.Cached.CState .anon)
  match r with
  | .ok (v, _) => .ok v
  | .error e => .error s!"{e}"

/-- A position's verdict: the profiles at which it is evaluated, the site, whether the walk
accepts it, and its spine's head, arguments and index along the spine. -/
abbrev Verdict := List IxCC.Src.Profile × Site × Bool × KExpr × List KExpr × Nat

def spineVerdicts (x : DCtx) (n : Nat) (Γ : List KExpr) (h : KExpr) (args : List KExpr) :
    List Verdict :=
  let k := spineAccepted x n Γ h args
  (spineSites Γ h args).zipIdx.map fun (s, j) => (x.profs, s, decide (j < k), h, args, j)

/-- Every site position of a run term with the walk's verdict, visited as `termRefused` visits
them. -/
def termVerdicts (tab : KTab) (lps : List Nat) (n : Nat) :
    List IxCC.Src.Profile → List KExpr → Term → KExpr → List KExpr → List Verdict
  | P, Γ, .app f a _ r, .app f' a', acc =>
    let P' := P.filter fun prof => !r.irrP prof
    (if P'.isEmpty then [] else termVerdicts tab lps n P' Γ a a' []) ++
      termVerdicts tab lps n P Γ f f' (a' :: acc)
  | P, Γ, .lam _ _ body, .lam d' body' m, acc =>
    spineVerdicts { tab, lps, profs := P } n Γ (.lam d' body' m) acc ++
      termVerdicts tab lps n P (d' :: Γ) body body' []
  | P, Γ, .proj _ _ t, .proj s i e, acc =>
    spineVerdicts { tab, lps, profs := P } n Γ (.proj s i e) acc ++
      termVerdicts tab lps n P Γ t e []
  -- under a `let` every site `evalSitesP` lists is refused (the route is not extended there)
  | P, Γ, .letE c r ty v b, e, acc =>
    spineVerdicts { tab, lps, profs := P } n Γ e acc ++
      (evalSitesP P Γ (.letE c r ty v b) e).map fun s => (P, s, false, s.2.1, [s.2.2], 0)
  | P, Γ, _, e, acc => spineVerdicts { tab, lps, profs := P } n Γ e acc

/-- What the comparison counts. -/
structure Tally where
  /-- site positions, and site-profile instances -/
  sites : Nat := 0
  instances : Nat := 0
  /-- positions (instances) the walk accepts -/
  accepted : Nat := 0
  acceptedInstances : Nat := 0
  /-- accepted instances the kernel types in the graph regime; types otherwise; fails on -/
  agree : Nat := 0
  disagree : Nat := 0
  errors : Nat := 0
  /-- pairs of an accepted position and a profile of its constant's level parameters at which
  the kernel's binder datum holds (a proposition), and how many of those the walk refuses at
  that profile alone -/
  datumHolds : Nat := 0
  refusedThere : Nat := 0
  /-- run pairs whose refused positions differ in number from `runRefused` -/
  selfCheckBad : Nat := 0
  /-- constants of `Sl` above `maxDirectParams` level parameters (all their sites refused) -/
  declined : Nat := 0
  deriving Repr

/-- **The comparison on a closure** (see the module note). -/
def tally (core : Core) (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Tally := Id.run do
  let tab := KTab.of env
  let mut t : Tally := {}
  for c in Sl do
    let lps := lpsOf c
    if lvlsOf p c > maxDirectParams then
      t := { t with declined := t.declined + 1 }
      continue
    let P := okProfiles p ann c
    if P.isEmpty then continue
    for (tm, e) in runPairsB p env κ c do
      let vs := termVerdicts tab lps directFuel P [] tm e []
      let nref := (vs.filter fun v => !v.2.2.1).length
      if nref != (runRefused p env lpsOf ann c tm e).length then
        t := { t with selfCheckBad := t.selfCheckBad + 1 }
      for (P', (Γ, f, a), ok, h, args, j) in vs do
        t := { t with sites := t.sites + 1, instances := t.instances + P'.length }
        if !ok then continue
        t := { t with accepted := t.accepted + 1,
                      acceptedInstances := t.acceptedInstances + P'.length }
        match kernelSite core Γ f a with
        | .ok (dok, pw) =>
          for prof in P' do
            if dok && pwAt lps prof pw == some false then t := { t with agree := t.agree + 1 }
            else t := { t with disagree := t.disagree + 1 }
          for prof' in profiles (lvlsOf p c) do
            if pwAt lps prof' pw == some true then
              t := { t with datumHolds := t.datumHolds + 1 }
              let x' : DCtx := { tab, lps, profs := [prof'] }
              if spineAccepted x' directFuel Γ h (args.take (j + 1)) ≤ j then
                t := { t with refusedThere := t.refusedThere + 1 }
        | .error _ => t := { t with errors := t.errors + P'.length }
  return t

end IxCCTests.Grounding.Oracle
