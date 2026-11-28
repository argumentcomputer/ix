import IxCCTests.Grounding.Run
import IxCCGrounding.GradedHead

/-! # `tests-grounding`: the η-short step of 1b's type reader (`TyRead.deltaShort`)

A definition with no level parameter whose value has fewer λs than the arguments it is applied to
(an η-reduced abbreviation, `M := StateT Nat Id` applied to `α`) is unfolded at the λs it has, its
body applied to the arguments left, lifted past those λs (`IxCCGrounding.GradedHead`). Asserted in
`IxCCTests.Grounding.GradedHead`'s pass over the 51 closures (one load each):

* **The corpus, against the landed reader.** `tyReadL` and `spineReadL` below are the text of
  `tyReadB` and `spineReadB` in `IxCCGrounding/GradedHead.lean` at commit `27006d16b` (landing 78,
  the last before the η-short step), frozen here, in the test tree only (no library module imports
  this file). On every maximal spine of every run pair of every closure, wherever the landed reader
  reads, the reader reads the same data; it reads exactly ten spines more, all at
  `phase2-closures/closures` c38, whose context types meet one η-short definition (no level
  parameter, a value with no λ, applied to one argument), and accepts them: `headRegimeSB` holds on
  `closures` (whose family is unchanged: the check still refuses it at `caseRec` and `caseShape`).
* **Planted on `closures`**, each refusing every one of the ten spines and making `headRegimeSB` and
  `headRegimeGB` false on the closure: the η-short definition's value made `Type` (its unfolding is
  not a `∀`); made the definition itself (the η-short unfolding never ends: the fuel runs out); the
  first λ datum of the definition its value applies made a proposition everywhere (a datum read past
  the η-short step).
* **Synthetic readings**, over two of `closures`' definitions with no level parameter, `D` and `E`,
  their values replaced (`E := λ (x y z : Type). ∀ (_ : y) (_ : z), x`):
  `D := λ (x : Type). E x` applied to three arguments (one λ, two arguments spliced) reads `D`'s λ
  datum then exactly what `E` applied to the same three reads, and the landed reader refuses it;
  `D`'s λ datum made a proposition: read, the datum among the data, refused at the one profile;
  `D` given a level parameter: refused, **the completeness limit** (a definition's own parameters
  would capture the spliced arguments'), not an error; `D := λ (x y : Type). ∀ (_ : x), y` (more λs
  than arguments) applied to one argument takes the δ step as landed and gives the landed answer
  (none), and applied to two, the landed answer (read). -/

namespace IxCCTests.Grounding.EtaShort

open IxCC IxCC.Grounding IxCCTests.Grounding
open Ix.Kernel (Level BinderMeta PropWhen Expr ConstantInfo)
open IxCC.Src (CId)

/-! ## The landed reader, frozen (`IxCCGrounding/GradedHead.lean` at `27006d16b`) -/

/-- `tyReadB` as landed at `27006d16b`, before the η-short step. -/
def tyReadL (tab : KTab) : Nat → List KExpr → LChain → Bnd → KExpr → Option (List PropWhen)
  | _, [], ch, _, .forallE _ _ m => some [pwChain ch m.pw]
  | fuel, a :: as, ch, bnd, .forallE _ b m =>
    (tyReadL tab fuel as ch (some a :: bnd) b).map (pwChain ch m.pw :: ·)
  | 0, _, _, _, _ => none
  | fuel + 1, as, ch, bnd, T =>
    match T.getAppFn with
    | .const D vs =>
      match tab[D]? with
      | some (.defnInfo cv val _) =>
        if vs.length = cv.levelParams.length then
          match lamPeel T.getAppArgs.length val with
          | some (lds, body) =>
            (tyReadL tab fuel as ((cv.levelParams, vs) :: ch) [] body).map
              (lds.map (pwChain ((cv.levelParams, vs) :: ch)) ++ ·)
          | none => none
        else none
      | _ => none
    | .bvar i =>
      match bnd[i]? with
      | some (some a) =>
        match lamPeel T.getAppArgs.length a with
        | some (lds, body) => (tyReadL tab fuel as [] [] body).map (lds ++ ·)
        | none => none
      | _ => none
    | _ => none
termination_by fuel as => (fuel, as.length)

/-- `spineReadB` as landed at `27006d16b` (over `tyReadL`). -/
def spineReadL (tab : KTab) : Nat → List KExpr → KExpr → List KExpr → Option (List PropWhen)
  | fuel, _, .const k us, as =>
    match tab[k]? with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        tyReadL tab fuel as [(ci.toConstantVal.levelParams, us)] [] ci.toConstantVal.type
      else none
    | none => none
  | fuel, Γ, .bvar i, as =>
    match Γ[i]? with
    | some T => tyReadL tab fuel as [] [] T
    | none => none
  | _, _, .lam _ _ m, [] => some [m.pw]
  | fuel + 1, Γ, .lam d b m, _ :: as =>
    (spineReadL tab fuel (d :: Γ) b.getAppFn (b.getAppArgs ++ as.map (·.liftLooseBVars 1 0))).map
      (m.pw :: ·)
  | _, _, _, _ => none

/-! ## The corpus against the landed reader -/

/-- A spine's verdict from its reading: read, and every datum false at every profile it is
evaluated at (as `headRegimeSB1`). -/
def acceptedBy (lps : List Nat) (sp : SpineAt) : Option (List PropWhen) → Bool
  | some ds => sp.profs.all fun prof => ds.all fun pw => pwAt lps prof pw == some false
  | none => false

/-- Every maximal spine of every run pair of `Sl`, with its constant (as `headRegimeSB1` lists
them). -/
def spinesOf (i : Input) : List (CId × SpineAt) :=
  i.Sl.flatMap fun c => (runPairsB i.src i.env i.κ c).flatMap fun x =>
    (spinesPs (okProfiles i.src i.ann c) [] x.1 x.2 []).map (c, ·)

/-- One closure read by the landed reader and by the reader. -/
structure Cmp where
  spines : Nat := 0
  /-- the landed reader reads, and the reader reads the same data -/
  same : Nat := 0
  /-- the landed reader reads, and the reader reads something else (expected: never) -/
  differ : List CId := []
  /-- the landed reader does not read, and the reader does -/
  more : List (CId × SpineAt) := []
  /-- of those, the ones the reader accepts -/
  moreAccepted : Nat := 0

/-- Every spine of the closure, read by both readers against its arguments less the last. -/
def compare (i : Input) : Cmp := Id.run do
  let tab := KTab.of i.env
  let mut r : Cmp := {}
  for (c, sp) in spinesOf i do
    let l := spineReadL tab headFuel sp.ctx sp.head sp.args.dropLast
    let n := spineReadB tab headFuel sp.ctx sp.head sp.args.dropLast
    r := { r with spines := r.spines + 1 }
    match l with
    | some _ =>
      if n == l then r := { r with same := r.same + 1 } else r := { r with differ := r.differ ++ [c] }
    | none =>
      if n.isSome then
        r := { r with more := r.more ++ [(c, sp)],
                      moreAccepted := r.moreAccepted + (if acceptedBy (i.lpsOf c) sp n then 1 else 0) }
  return r

/-- The definitions at the head of the extra spines' context types that are applied there to more
arguments than their values have λs (the η-short definitions met first on those spines). -/
def shortHeads (i : Input) (more : List (CId × SpineAt)) : List KKey :=
  let tab := KTab.of i.env
  (more.filterMap fun (_, sp) => match sp.head with
    | .bvar j => (sp.ctx[j]?).bind fun T => match T.getAppFn with
      | .const D _ => match tab[D]? with
        | some (.defnInfo _ val _) => if (lamPeel T.getAppArgs.length val).isNone then some D else none
        | _ => none
      | _ => none
    | _ => none).eraseDups

/-- The stored record of a definition: its level parameters and its value. -/
def defnOf (env : KEnv) (D : KKey) : Option (List Nat × KExpr) :=
  match env.find? D with
  | some (.defnInfo cv val _) => some (cv.levelParams, val)
  | _ => none

/-- Each extra spine refused on a planted reading (not read, or a datum holding). -/
def allRefused (i : Input) (env : KEnv) (more : List (CId × SpineAt)) : Bool :=
  let tab := KTab.of env
  more.all fun (c, sp) =>
    !acceptedBy (i.lpsOf c) sp (spineReadB tab headFuel sp.ctx sp.head sp.args.dropLast)

/-- A definition's value (and level parameters) replaced. -/
def setDefn (env : KEnv) (D : KKey) (lps : List Nat) (val : KExpr) : KEnv :=
  mapConst env D fun
    | .defnInfo cv _ h => .defnInfo { cv with levelParams := lps } val h
    | ci => ci

/-- The planted controls on the η-short definition `D` (its value applying `F`). -/
def plants (env : KEnv) (D : KKey) : List (String × KEnv) :=
  let F? : Option KKey := match defnOf env D with
    | some (_, val) => match val.getAppFn with
      | .const F _ => some F
      | _ => none
    | none => none
  [("the η-short unfolding made `Type` (not a ∀)", setDefn env D [] (.sort (.succ .zero))),
   ("the η-short unfolding made endless (the definition itself)", setDefn env D [] (.const D []))] ++
  (match F? with
    | some F =>
      [("the first λ datum of the applied definition made a proposition", mapConst env F fun
        | .defnInfo cv (.lam d b m) h => .defnInfo cv (.lam d b { m with pw := .ifAllZero [] }) h
        | ci => ci)]
    | none => [])

/-! ## Synthetic readings -/

def ty1 : KExpr := .sort (.succ .zero)

def bm (pw : PropWhen) : BinderMeta := { pw }

/-- `E := λ (x y z : Type). ∀ (_ : y) (_ : z), x`. -/
def eVal : KExpr :=
  .lam ty1 (.lam ty1 (.lam ty1
    (.forallE (.bvar 1) (.forallE (.bvar 1) (.bvar 4) (bm .never)) (bm .never))
    (bm .never)) (bm .never)) (bm .never)

/-- `D := λ (x : Type). E x`, its λ's datum `pw`. -/
def dVal (E : KKey) (pw : PropWhen) : KExpr := .lam ty1 (.app (.const E []) (.bvar 0)) (bm pw)

/-- `D := λ (x y : Type). ∀ (_ : x), y` (more λs than one argument). -/
def dMore : KExpr := .lam ty1 (.lam ty1 (.forallE (.bvar 1) (.bvar 1) (bm .never)) (bm .never)) (bm .never)

/-- The three arguments `Type`, `#0`, `#1` (two of them site variables, lifted when spliced), and
the one site argument the reading consumes at `E`'s first `∀`. -/
def args3 : List KExpr := [ty1, .bvar 0, .bvar 1]
def siteArgs : List KExpr := [.bvar 2]

/-- The synthetic readings over `D` and `E` (two definitions with no level parameter of `env`):
each a name, its verdict, and what was read. -/
def synthetic (env : KEnv) (D E : KKey) : List (String × Bool × String) :=
  let read (e : KEnv) (T : KExpr) (as : List KExpr) := tyReadB (KTab.of e) headFuel as [] [] T
  let readL (e : KEnv) (T : KExpr) (as : List KExpr) := tyReadL (KTab.of e) headFuel as [] [] T
  let held (ds : List PropWhen) := ds.any fun pw => pwAt [] [] pw == some true
  let tD := Expr.mkAppN (.const D []) args3
  let tE := Expr.mkAppN (.const E []) args3
  -- j = 1: one λ, two arguments spliced
  let e1 := setDefn (setDefn env E [] eVal) D [] (dVal E .never)
  let (r1, r1E, r1L) := (read e1 tD siteArgs, read e1 tE siteArgs, readL e1 tD siteArgs)
  let ok1 := r1E.isSome && r1 == r1E.map (PropWhen.never :: ·) && r1L.isNone &&
    !(r1.map held).getD true
  -- the λ's datum a proposition
  let e2 := setDefn (setDefn env E [] eVal) D [] (dVal E (.ifAllZero []))
  let r2 := read e2 tD siteArgs
  let ok2 := r2 == r1E.map (PropWhen.ifAllZero [] :: ·) && (r2.map held).getD false
  -- a level parameter: the completeness limit
  let e3 := setDefn (setDefn env E [] eVal) D [0] (dVal E .never)
  let tD3 := Expr.mkAppN (.const D [.zero]) args3
  let r3 := read e3 tD3 siteArgs
  let ok3 := r3.isNone && r1.isSome
  -- more λs than arguments: the δ step as landed, the landed answer
  let e4 := setDefn env D [] dMore
  let t4a := Expr.mkAppN (.const D []) [ty1]
  let t4b := Expr.mkAppN (.const D []) [ty1, ty1]
  let (r4a, r4aL, r4b, r4bL) := (read e4 t4a [], readL e4 t4a [], read e4 t4b [], readL e4 t4b [])
  let ok4 := r4a.isNone && r4aL.isNone && r4b.isSome && r4b == r4bL
  [("D := λ x. E x applied to three (j = 1): D's datum, then E's reading; the landed reader refuses",
      ok1, s!"read {repr r1}, E {repr r1E}, landed {repr r1L}"),
   ("D's λ datum made a proposition: read, refused at the profile", ok2, s!"read {repr r2}"),
   ("D given a level parameter: refused (the completeness limit, not an error)", ok3,
      s!"read {repr r3}"),
   ("D := λ x y. ∀ (_ : x), y (more λs than arguments): the landed path and answer", ok4,
      s!"one argument {repr r4a} (landed {repr r4aL}), two {repr r4b} (landed {repr r4bL})")]

end IxCCTests.Grounding.EtaShort
