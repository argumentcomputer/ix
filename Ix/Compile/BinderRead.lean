module

public import Ix.Compile.BinderData
public import Ix.LeanIngress.Expr

public section

/-!
# Binder data read off a record's Lean source

A binder's datum is the zero-ness of its codomain's sort. Most binders show it
in their source without any inference, and this reader takes exactly those:

* **a ∀-run**: the run's body is a type; its sort is read off its head. A sort
  `Sort u` has sort `Sort (u+1)`, never zero. An application `c a₁ … aₙ` of a
  constant whose declared type is exactly `n` ∀s followed by `Sort s` has sort
  `s` at the application's levels; so does an application of a bound variable
  whose declared type has that shape. A body that is itself a ∀ reads its own
  body (the zero-ness of `imax u v` is that of `v`).
* **a λ-run**: every λ of the run has the zero-ness of the sort of the run's
  type, which the reader carries in from where the λ-run stands: a theorem's
  value (always zero), a definition's value (its type's), a `let`'s value (its
  declared type's), an argument of an application of a constant or a bound
  variable (the zero-ness of the sort of the head's domain at that position,
  read as above), a recursor's rule right-hand side (its elimination level's),
  the head of an application (the application's own: the head's type `∀ x⃗, B`
  has the zero-ness of the sort of `B`, the sort of the application's type).
  It passes unchanged into the run's body, a `let`'s body and a share.

A head's declared type is peeled through the definitions that return one of their
arguments (`outParam T` is `T`). A head is a constant, a bound variable (its
declared type), or a field of a bound variable whose declared type is a structure
(the field's declared type). An argument beyond its head's ∀s, where the head's
type ends in one of the head's own variables (a `casesOn`'s `motive t`), takes its
domain from the actual argument there, `λ y⃗, R` with as many λs as that variable
has arguments: the domain is `R`'s. A `let` at the head of a type is read through
(its body has the sort of its ζ-reduct).

Anything else (a body headed by a projection of anything but a bound variable, a
redex, a match whose motive computes a sort, a constant whose type is not
syntactically such a telescope)
is not read, and the record falls to IxC's pass (`Ix.Compile.KernelAnnotate`):
the reader never guesses. Every datum it does read is the one IxC's pass
computes, because the source is Lean-checked and Lean's conversion has no
equality reflection: an argument's inferred type is definitionally its head's
domain there, and definitionally equal types have equivalent sorts.

The numbering of the data and of share variants is the compiler's
(`Ix.CompileM.withBinderSection`), as IxC's pass gives it: the record's tree
numbers the nodes, a share's entry is read once per context of the variables it
can name, and a variant is a distinct node list.
-/

namespace Ix.Compile.BinderRead

open Ix.Kernel (PropWhen)
open Ix.LeanIngress (Numbering ingressLevel)
open IxVM.PwHints (Node Block)

/-- How the reader finds a constant's declaration. -/
abbrev Find := Ix.Name → Option Ix.ConstantInfo

/-- `e` without its `mdata` wrappers. -/
def unmeta : Ix.Expr → Ix.Expr
  | .mdata _ e _ => unmeta e
  | e => e

/-- A spine's head (without `mdata`) and its argument count. -/
def headArgs : Ix.Expr → Ix.Expr × Nat
  | .app f _ _ => let (h, n) := headArgs f; (h, n + 1)
  | .mdata _ e _ => headArgs e
  | e => (e, 0)

/-- A constant's own numbering of its level parameters: their positions. -/
def posIn (names : Array Ix.Name) (n : Ix.Name) : Nat :=
  (names.findIdx? (Ix.Name.beqRaw · n)).getD names.size

/-- A definition whose value returns one of its own arguments (`outParam`,
`optParam`, `autoParam`, `semiOutParam`, `id`): its arity and which argument. -/
def wrapperOf : Ix.ConstantInfo → Option (Nat × Nat)
  | .defnInfo d =>
    let rec go : Nat → Ix.Expr → Option (Nat × Nat)
      | m, .lam _ _ b _ _ => go (m + 1) b
      | m, .mdata _ e _ => go m e
      | m, .bvar j _ => if j < m then some (m, m - 1 - j) else none
      | _, _ => none
    go 0 d.value
  | _ => none

/-- The arguments of a spine, outermost first. -/
def spineArgs : Ix.Expr → Array Ix.Expr → Array Ix.Expr
  | .app f a _, acc => spineArgs f (acc.push a)
  | .mdata _ e _, acc => spineArgs e acc
  | _, acc => acc

/-- `t` with argument-returning definitions at its head unfolded (δβ, exact):
`outParam T ↦ T`. -/
def unwrap (find : Find) : Nat → Ix.Expr → Ix.Expr
  | 0, t => t
  | fuel + 1, t =>
    let t := unmeta t
    match headArgs t with
    | (.const c _ _, n) =>
      match (find c).bind wrapperOf with
      | some (m, i) =>
        if m ≤ n then
          let args := (spineArgs t #[]).reverse
          match args[i]? with
          | some a => unwrap find fuel (args.extract m args.size |>.foldl (fun f x => Ix.Expr.mkApp f x) a)
          | none => t
        else t
      | none => t
    | _ => t

/-- `t` past exactly `n` leading ∀s, each found after unfolding argument-returning
definitions at the head (`unwrap`: a class's `outParam (α → β → Sort u)`). -/
def peelN (find : Find) : Nat → Ix.Expr → Option Ix.Expr
  | 0, t => some (unmeta t)
  | n + 1, t => match unwrap find 8 t with
    | .forallE _ _ b _ _ => peelN find n b
    | _ => none

/-- The `n`-th ∀-domain of `t`, with the domains before it, innermost first; each ∀
found as `peelN` finds it. -/
def domainAt (find : Find) : Nat → Ix.Expr → List (Option Ix.Expr) →
    Option (Ix.Expr × List (Option Ix.Expr))
  | n, t, acc => match unwrap find 8 t, n with
    | .forallE _ d _ _ _, 0 => some (d, acc)
    | .forallE _ d b _ _, n + 1 => domainAt find n b (some d :: acc)
    | _, _ => none

/-- The final sort of a ∀-telescope `t`, if it is syntactically a sort. -/
def leafSort : Ix.Expr → Option Ix.Level
  | .sort l _ => some l
  | .forallE _ _ b _ _ => leafSort b
  | .mdata _ e _ => leafSort e
  | _ => none

/-- The level of `a` when it is `Sort l` under exactly `k` λs. -/
def lamSort : Nat → Ix.Expr → Option Ix.Level
  | 0, a => match unmeta a with
    | .sort l _ => some l
    | _ => none
  | k + 1, a => match unmeta a with
    | .lam _ _ b _ _ => lamSort k b
    | _ => none

/-- `a` as exactly `k` λs: their binder types (innermost first, before `acc`) and
the body. -/
def lamsExact : Nat → Ix.Expr → List (Option Ix.Expr) → Option (List (Option Ix.Expr) × Ix.Expr)
  | 0, a, acc => some (acc, unmeta a)
  | k + 1, a, acc => match unmeta a with
    | .lam _ ty b _ _ => lamsExact k b (some ty :: acc)
    | _ => none

/-- The number of ∀s of `t`, each found as `peelN` finds it. -/
def piCount (find : Find) : Nat → Ix.Expr → Nat
  | 0, _ => 0
  | fuel + 1, t => match unwrap find 8 t with
    | .forallE _ _ b _ _ => piCount find fuel b + 1
    | _ => 0

/-- Bounds the ∀s and `let`s a sort is read through. -/
def sortFuel : Nat := 1 <<< 12

/-- **The field a projection `.proj S i v` reads**, when `v` is a bound variable
whose declared type (under `ctx`) is `S.{us} p⃗`, `S` a structure (one
constructor, no indices): the field's type in its constructor's telescope, the
constructor's domains before it (innermost first), the constructor's level
parameters, and `us`. -/
def projField (find : Find) (ctx : List (Option Ix.Expr)) (sName : Ix.Name) (i : Nat)
    (v : Ix.Expr) : Option (Ix.Expr × List (Option Ix.Expr) × Array Ix.Name × Array Ix.Level) := do
  let .bvar k _ := unmeta v | none
  let vty ← (ctx[k]?).join
  let (vh, np) := headArgs (unwrap find 8 vty)
  let .const S us _ := vh | none
  guard (Ix.Name.beqRaw S sName)
  let .inductInfo ind ← find S | none
  guard (ind.numIndices == 0 && np == ind.numParams)
  let #[c] := ind.ctors | none
  let .ctorInfo ctor ← find c | none
  let (d, before) ← domainAt find (ind.numParams + i) ctor.cnst.type []
  pure (d, before, ctor.cnst.levelParams, us)

/-- **The zero-ness of the sort of the type `t`, read syntactically.** `σ`
numbers the level parameters `t` and `ctx` (the types of `t`'s loose variables,
innermost first) are written over, and `sub` maps levels in that numbering to
the reader's. A `let` at the head is read through (its body has the sort of its
ζ-reduct). `none` where the reading does not apply. -/
def sortPw (find : Find) (σ : Ix.Name → Nat) (sub : Ix.Kernel.Level → Ix.Kernel.Level) :
    Nat → List (Option Ix.Expr) → Ix.Expr → Option PropWhen
  | 0, _, _ => none
  | fuel + 1, ctx, t =>
    match unwrap find 8 t with
    | .sort _ _ => some .never
    | .forallE _ d b _ _ => sortPw find σ sub fuel (some d :: ctx) b
    | .letE _ ty _ b _ _ => sortPw find σ sub fuel (some ty :: ctx) b
    | t =>
      let (h, n) := headArgs t
      let lvl? : Option Ix.Kernel.Level := match h with
        | .const c us _ => do
          let ci ← find c
          let cv := ci.getCnst
          match unwrap find 8 (← peelN find n cv.type) with
          | .sort l _ =>
            let lc ← (ingressLevel (posIn cv.levelParams) l).toOption
            let us' ← (us.toList.mapM (ingressLevel σ)).toOption
            pure (Ix.Kernel.Level.subst (List.range cv.levelParams.size) us' lc)
          | r =>
            -- the type there is one of the head's own variables applied to `k`
            -- arguments (a matcher's `motive x`, `ite`'s `α`): the actual argument
            -- there, a sort under exactly `k` λs, is the sort (a level names no term
            -- variable, so the arguments do not matter)
            let (rh, k) := headArgs r
            let .bvar j _ := rh | none
            guard (j < n)
            let a ← (spineArgs t #[]).reverse[n - 1 - j]?
            let l ← lamSort k a
            (ingressLevel σ l).toOption
        | .bvar i _ => do
          let ty ← (ctx[i]?).join
          let .sort l _ := unwrap find 8 (← peelN find n ty) | none
          (ingressLevel σ l).toOption
        | .proj sName i v _ => do
          -- a field of a bound structure variable: the field's declared type
          let (fty, _, lps, us) ← projField find ctx sName i v
          let .sort l _ := unwrap find 8 (← peelN find n fty) | none
          let lc ← (ingressLevel (posIn lps) l).toOption
          let us' ← (us.toList.mapM (ingressLevel σ)).toOption
          pure (Ix.Kernel.Level.subst (List.range lps.size) us' lc)
        | _ => none
      lvl?.map fun l => Ix.Kernel.Level.zeronessOf (sub l)

/-- **The domain of the argument at `idx` beyond its head's ∀s**: the head's type
`ty` has `m ≤ idx` ∀s and ends in one of the head's own variables applied to `k`
arguments (a `casesOn`'s `motive t`); the actual argument there (`args`, the
spine's, outermost first) is `λ y⃗, R` with exactly `k` λs, so the type there is
`R` with the arguments for `y⃗`, and the domain is `R`'s at `idx - m`. The domain
and the types of its loose variables (innermost first, the spine's `ctx` last),
its levels in the spine's numbering. -/
def beyondDomain (find : Find) (ctx : List (Option Ix.Expr)) (ty : Ix.Expr)
    (args : Array Ix.Expr) (idx : Nat) : Option (Ix.Expr × List (Option Ix.Expr)) := do
  let m := piCount find sortFuel ty
  guard (m ≤ idx)
  let r ← peelN find m ty
  let (rh, k) := headArgs (unwrap find 8 r)
  let .bvar j _ := rh | none
  guard (j < m)
  let a ← args[m - 1 - j]?
  let (ys, body) ← lamsExact k a []
  let (d, before) ← domainAt find (idx - m) body []
  pure (d, before ++ ys ++ ctx)

/-- The zero-ness of the sort of the domain at `idx` of the type of the spine
head `h` (a constant, a bound variable under `ctx`, or a field of a bound structure
variable; `args` the spine's arguments before `idx`, outermost first): what an
argument there has as its type's sort. -/
def argPw (find : Find) (σ : Ix.Name → Nat) (ctx : List (Option Ix.Expr)) (h : Ix.Expr)
    (args : Array Ix.Expr) (idx : Nat) : Option PropWhen :=
  match h with
  | .const c us _ => do
    let ci ← find c
    let cv := ci.getCnst
    match domainAt find idx cv.type [] with
    | some (d, before) =>
      let us' ← (us.toList.mapM (ingressLevel σ)).toOption
      sortPw find (posIn cv.levelParams)
        (Ix.Kernel.Level.subst (List.range cv.levelParams.size) us') sortFuel before d
    | none =>
      let (d, dctx) ← beyondDomain find ctx cv.type args idx
      sortPw find σ id sortFuel dctx d
  | .bvar i _ => do
    let ty ← (ctx[i]?).join
    match domainAt find idx ty [] with
    | some (d, before) => sortPw find σ id sortFuel (before ++ ctx.drop (i + 1)) d
    | none =>
      let (d, dctx) ← beyondDomain find ctx ty args idx
      sortPw find σ id sortFuel dctx d
  | .proj sName j v _ => do
    let (fty, fctx, lps, us) ← projField find ctx sName j v
    let (d, before) ← domainAt find idx fty []
    let us' ← (us.toList.mapM (ingressLevel σ)).toOption
    sortPw find (posIn lps) (Ix.Kernel.Level.subst (List.range lps.size) us') sortFuel
      (before ++ fctx) d
  | _ => none

/-! ## The reading of a record -/

/-- What a record's reading reads. -/
structure Cx where
  find : Find
  /-- the root's numbering of level parameters -/
  σ : Numbering
  sharing : Array Ixon.Expr
  bounds : Array Nat

/-- A source level parameter's index in the record's numbering (the inverse of
`Numbering.pos`: a large eliminator's source numbers its motive universe last,
the record first). -/
def Cx.recordParam (cx : Cx) (p : Nat) : Nat :=
  if cx.σ.large then (if p + 1 == cx.σ.names.size then 0 else p + 1) else p

/-- The node of a datum, its parameters in the record's numbering. -/
def Cx.nodeOf (cx : Cx) (pw : PropWhen) : Node :=
  match pw.toList? with
  | none => .binder none
  | some ps => .binder (some ((ps.map cx.recordParam).toArray.qsort (· < ·)))

/-- The reading's state: the sharing entries' variants (by node list) and
blocks, and the memo of share sites (entry, the types its variables can name,
the expectation, the source term). -/
structure RState where
  variants : Std.HashMap Nat (Std.HashMap (Array Node) Nat) := {}
  blocks : Array Block := #[]
  memo : Std.HashMap (Nat × List (Option Address) × Option PropWhen × Address) Nat := {}

/-- A reading fails at the first binder it cannot read, saying what stands there. -/
abbrev RM := StateT RState (Except String)
/-- An entry's reading: its nodes' data, by ordinal. -/
abbrev NM := StateT (Array Node) RM

/-- What the reading expects of a term's type: the zero-ness of its sort, or why
it does not know it (the reason is built only where a reading fails on it). -/
abbrev Expect := Except (Unit → String) PropWhen

/-- An expectation not known, for the reason `why`. -/
def unknown (why : String) : Expect := .error fun _ => why

private def reserve : NM Nat :=
  modifyGet fun nodes => (nodes.size, nodes.push (.binder none))

private def setNode (ord : Nat) (n : Node) : NM Unit :=
  modify fun nodes => nodes.set! ord n

private def variantOf (n : Nat) (nodes : Array Node) : RM Nat := do
  let st ← get
  let table := st.variants.getD n {}
  match table[nodes]? with
  | some v => pure v
  | none =>
    let v := table.size
    set { st with variants := st.variants.insert n (table.insert nodes v)
                  blocks := st.blocks.push ⟨1, n, v, nodes⟩ }
    pure v

/-- A run of binders of one kind in the record's tree and its source: each
binder's domain in both, then both bodies. -/
def binderRun (pi : Bool) : Ixon.Expr → Ix.Expr → Array (Ixon.Expr × Ix.Expr) →
    Ixon.Expr × Ix.Expr × Array (Ixon.Expr × Ix.Expr)
  | e@(.lam _ t b), x, acc => match unmeta x with
    | .lam _ ty body _ _ => if pi then (e, x, acc) else binderRun pi b body (acc.push (t, ty))
    | _ => (e, x, acc)
  | e@(.all _ _ t b), x, acc => match unmeta x with
    | .forallE _ ty body _ _ => if pi then binderRun pi b body (acc.push (t, ty)) else (e, x, acc)
    | _ => (e, x, acc)
  | e, x, acc => (e, x, acc)

/-- A source node's kind, for the reasons. -/
def tag : Ix.Expr → String
  | .bvar .. => "a variable" | .fvar .. => "a free variable" | .mvar .. => "a metavariable"
  | .sort .. => "a sort" | .const .. => "a constant" | .app .. => "an application"
  | .lam .. => "a λ" | .forallE .. => "a ∀" | .letE .. => "a let" | .lit .. => "a literal"
  | .mdata _ e _ => tag e | .proj .. => "a projection"

/-- Why the sort of the type `t` (under `ctx`) is not read: its head's shape. -/
def shapeOf (find : Find) (ctx : List (Option Ix.Expr)) (t : Ix.Expr) : String :=
  let rec leaf : Nat → Ix.Expr → Ix.Expr
    | 0, t => t
    | n + 1, t => match unwrap find 8 t with
      | .forallE _ _ b _ _ => leaf n b
      | t => t
  let t := leaf 64 t
  let (h, n) := headArgs t
  match h with
  | .const c _ _ => match find c with
    | some ci => match peelN find n ci.getCnst.type with
      | some r => s!"{c.pretty} applied to {n}, whose type there is {tag (unwrap find 8 r)}"
      | none => s!"{c.pretty} applied to {n}, more than its type's ∀s"
    | none => s!"{c.pretty}, not found"
  | .bvar i _ => match (ctx[i]?).join with
    | some ty => match peelN find n ty with
      | some r => s!"a variable applied to {n}, whose type there is {tag (unwrap find 8 r)}"
      | none => s!"a variable applied to {n}, more than its type's ∀s"
    | none => "a let-bound variable"
  | h => s!"{tag h} applied to {n}"

/-- The expectation of an argument at `idx` of a spine headed by `h` (`args` the
arguments before it, outermost first). -/
def argExpect (find : Find) (σ : Ix.Name → Nat) (ctx : List (Option Ix.Expr)) (h : Ix.Expr)
    (args : Array Ix.Expr) (idx : Nat) : Expect :=
  match argPw find σ ctx h args idx with
  | some p => .ok p
  | none => .error fun _ =>
    let head := match h with
      | .const c _ _ => c.pretty
      | h => tag h
    let dom : Option (Ix.Expr × List (Option Ix.Expr)) := match h with
      | .const c _ _ => (find c).bind fun ci => domainAt find idx ci.getCnst.type []
      | .bvar i _ => (ctx[i]?).join.bind fun ty => domainAt find idx ty []
      | _ => none
    match dom with
    | some (d, before) => s!"argument {idx} of {head}, its domain headed by {shapeOf find before d}"
    | none => s!"argument {idx} of {head}, beyond its type's ∀s"

/-- The expectation of the next argument of the spine `xf`. -/
def argExpectOf (find : Find) (σ : Ix.Name → Nat) (ctx : List (Option Ix.Expr)) (xf : Ix.Expr) :
    Expect :=
  let (h, n) := headArgs xf
  argExpect find σ ctx h (spineArgs xf #[]).reverse n

/-- Bounds the reading's depth. -/
def readFuel : Nat := 1 <<< 24

/-- Whether the reading of a record node reads its expectation: a λ-run, a `let`
(its body), a share (its entry), and an application headed by one of those. -/
def readsExpect : Ixon.Expr → Bool
  | .lam .. | .letE .. | .share _ => true
  | .app f _ => readsExpect f
  | _ => false

/-- **The reading of one entry's tree `e` beside its source `x`**, under `ctx`
(the types of the bound variables, innermost first; `none` for a `let`'s), with
`ex` the zero-ness of the sort of `x`'s type where it is known. Every numbered
node of `e` gets its datum at its ordinal; the reading fails where a datum is not
read, saying what stands there. -/
def read : Nat → Cx → List (Option Ix.Expr) → Expect → Ixon.Expr → Ix.Expr → NM Unit
  | 0, _, _, _, _, _ => throw "the reading's depth bound"
  | fuel + 1, cx, ctx, ex, e, x =>
    match e, unmeta x with
    | .var _, .bvar .. => pure ()
    | .app f a, .app xf xa _ => do
      -- the function's type `∀ x⃗, B` has the zero-ness of the sort of `B`, which is
      -- the sort of the application's type `B[a⃗/x⃗]` (a level names no term variable):
      -- a β-redex's λ-run has the application's expectation
      read fuel cx ctx ex f xf
      -- the expectation is computed only for an argument that reads it
      let aex : Expect :=
        if readsExpect a then argExpectOf cx.find cx.σ.pos ctx xf
        else unknown "an argument that reads no expectation"
      read fuel cx ctx aex a xa
    | .lam .., .lam .. | .all .., .forallE .. => do
      let pi := e matches .all ..
      let (leafE, leafX, bs) := binderRun pi e x #[]
      let mut inner := ctx
      let mut ords : Array Nat := #[]
      for h : j in [:bs.size] do
        let (t, ty) := bs[j]
        ords := ords.push (← reserve)
        read fuel cx inner (unknown "a binder's domain") t ty
        inner := some ty :: inner
      read fuel cx inner (if pi then unknown "a ∀-body" else ex) leafE leafX
      let pw ← if pi then
          match sortPw cx.find cx.σ.pos id sortFuel inner leafX with
          | some p => pure p
          | none => throw s!"a ∀-body headed by {shapeOf cx.find inner leafX}"
        else match ex with
          | .ok p => pure p
          | .error why => throw s!"a λ-run as {why ()}"
      let node := cx.nodeOf pw
      for ord in ords do setNode ord node
    | .letE _ t v b, .letE _ ty val body _ _ => do
      read fuel cx ctx (unknown "a let's type") t ty
      let vex : Expect := match sortPw cx.find cx.σ.pos id sortFuel ctx ty with
        | some p => .ok p
        | none => .error fun _ => s!"a let's value, its type headed by {shapeOf cx.find ctx ty}"
      read fuel cx ctx vex v val
      read fuel cx (some ty :: ctx) ex b body
    | .prj _ _ v, .proj _ _ xv _ => read fuel cx ctx (unknown "a projection's subject") v xv
    | .share n, _ => do
      let ord ← reserve
      let n := n.toNat
      let key := (n, (ctx.take (cx.bounds[n]?.getD 0)).map (·.map Ix.Expr.getHash), ex.toOption,
        x.getHash)
      let variant ← match (← getThe RState).memo[key]? with
        | some v => pure v
        | none => do
          let some entry := cx.sharing[n]? | throw "a share without its entry"
          let ((), nodes) ← ((read fuel cx ctx ex entry x).run #[] : RM (Unit × Array Node))
          let v ← variantOf n nodes
          modifyThe RState fun st => { st with memo := st.memo.insert key v }
          pure v
      setNode ord (.share variant)
    | .sort _, .sort .. | .ref .., .const .. | .recur .., .const .. | .str _, .lit .. | .nat _, .lit .. =>
      pure ()
    | _, x => throw s!"a record node that is not its source's ({tag x})"

/-! ## A record's roots and their expectations -/

/-- A root's source, its numbering, and the zero-ness of its type's sort where
the reading needs it (a value's, a rule right-hand side's). -/
structure Root where
  σ : Numbering
  x : Ix.Expr
  ex : Expect := unknown "a type"

/-- The zero-ness of the sort of a definition's type `ty`, numbered by `σ`. -/
def typeExpect (find : Find) (σ : Numbering) (ty : Ix.Expr) : Expect :=
  match sortPw find σ.pos id sortFuel [] ty with
  | some p => .ok p
  | none => .error fun _ => s!"a definition's value, its type headed by {shapeOf find [] ty}"

/-- A recursor's roots: its type and its rules' right-hand sides, numbered as its
record numbers them (a large eliminator's motive universe first). A rule's
right-hand side has the sort of its motive's codomain: the elimination level. -/
def recRoots (find : Find) (v : Ix.RecursorVal) : Array Root :=
  let indLevels := match v.all[0]?.bind find with
    | some (.inductInfo i) => i.cnst.levelParams.size
    | _ => v.cnst.levelParams.size
  let σ : Numbering := ⟨v.cnst.levelParams, v.cnst.levelParams.size == indLevels + 1⟩
  let elim : Expect := match (do
      let (motive, _) ← domainAt find v.numParams v.cnst.type []
      let l ← leafSort motive
      let l' ← (ingressLevel σ.pos l).toOption
      pure (Ix.Kernel.Level.zeronessOf l') : Option PropWhen) with
    | some p => .ok p
    | none => unknown "a rule's right-hand side, its motive's sort not read"
  (#[⟨σ, v.cnst.type, unknown "a type"⟩] : Array Root) ++
    v.rules.map fun rule => (⟨σ, rule.rhs, elim⟩ : Root)

/-- A member's roots, in section order, when its kind is the record member's
(`IxVM.PwHints.roots`): a definition's type and value, an axiom's or a
quotient's type, an inductive's type and its constructors' types, a recursor's
type and its rules' right-hand sides. -/
def memberRoots (find : Find) (ci : Ix.ConstantInfo) :
    Ixon.MutConst ⊕ Ixon.ConstantInfo → Option (Array Root)
  | .inl (.defn _) | .inr (.defn _) =>
    let σ : Numbering := ⟨ci.getCnst.levelParams, false⟩
    match ci with
    | .defnInfo d => some #[⟨σ, d.cnst.type, unknown "a type"⟩, ⟨σ, d.value, typeExpect find σ d.cnst.type⟩]
    | .thmInfo t => some #[⟨σ, t.cnst.type, unknown "a type"⟩, ⟨σ, t.value, .ok (PropWhen.ifAllZero [])⟩]
    | .opaqueInfo o => some #[⟨σ, o.cnst.type, unknown "a type"⟩, ⟨σ, o.value, typeExpect find σ o.cnst.type⟩]
    | _ => none
  | .inr (.axio _) => match ci with
    | .axiomInfo a => some #[⟨⟨a.cnst.levelParams, false⟩, a.cnst.type, unknown "a type"⟩]
    | _ => none
  | .inr (.quot _) => match ci with
    | .quotInfo q => some #[⟨⟨q.cnst.levelParams, false⟩, q.cnst.type, unknown "a type"⟩]
    | _ => none
  | .inl (.recr r) | .inr (.recr r) => match ci with
    | .recInfo v => do
      guard (v.rules.size == r.rules.size)
      some (recRoots find v)
    | _ => none
  | .inl (.indc i) => match ci with
    | .inductInfo v => do
      let ctors ← v.ctors.mapM fun n => match find n with
        | some (.ctorInfo k) => some (⟨⟨k.cnst.levelParams, false⟩, k.cnst.type, unknown "a type"⟩ : Root)
        | _ => none
      guard (ctors.size == i.ctors.size)
      some ((#[⟨⟨v.cnst.levelParams, false⟩, v.cnst.type, unknown "a type"⟩] : Array Root) ++ ctors)
    | _ => none
  | _ => none

/-- The block's members, as the record lists them. -/
def members (c : Ixon.Constant) : Array (Ixon.MutConst ⊕ Ixon.ConstantInfo) :=
  match c.info with
  | .muts ms => ms.map .inl
  | info => #[.inr info]

/-- **The section of a block record, read off its members' sources** (`names`,
in the record's member order), or why some binder is not read. -/
def sectionWhy (find : Find) (names : Array Ix.Name) (c : Ixon.Constant) :
    Except String (Array Ixon.BinderBlock) := do
  let ms := members c
  unless ms.size == names.size do throw "members and names differ"
  let mut roots : Array Root := #[]
  for (m, n) in ms.zip names do
    let some ci := find n | throw s!"{n.pretty} has no source"
    let some rs := memberRoots find ci m | throw s!"{n.pretty}'s source is not its record's kind"
    roots := roots ++ rs
  let rs := IxVM.PwHints.roots c
  unless roots.size == rs.size do throw "roots and sources differ"
  let bounds := IxVM.PwHints.bounds c.sharing
  let act : RM (Array Block) := do
    let mut out := #[]
    for h : i in [:rs.size] do
      let some r := roots[i]? | throw "a root without its source"
      let cx : Cx := { find, σ := r.σ, sharing := c.sharing, bounds }
      let ((), nodes) ← (read readFuel cx [] r.ex rs[i] r.x).run #[]
      out := out.push ⟨0, i, 0, nodes⟩
    return out
  let (blocks, st) ← act.run {}
  Ix.Compile.BinderData.sectionOf c (blocks ++ st.blocks)

/-- `sectionWhy` without its reason. -/
def section? (find : Find) (names : Array Ix.Name) (c : Ixon.Constant) :
    Option (Array Ixon.BinderBlock) :=
  (sectionWhy find names c).toOption

/-! ## Whether a constant's source reads, without its record

A record's tree is its members' sources, compiled: its shares are entries of
them, and a share is read with the expectation at its site. So the reading of a
source alone, by the same rules, fails exactly where the reading of its record
does, and tells, before the compile, which records will be walked (and what the
walk's environment must hold). -/

/-- The terms read so far, under a context (its hash) and an expectation: a
subterm shared in the source is read once there. -/
abbrev SM := StateT (Std.HashSet (UInt64 × Address × Option PropWhen)) (Except Unit)

/-- Whether the reading of a source term reads its expectation (`readsExpect`'s
twin). -/
def readsExpectSrc : Ix.Expr → Bool
  | .lam .. | .letE .. => true
  | .app f _ _ => readsExpectSrc f
  | .mdata _ e _ => readsExpectSrc e
  | _ => false

/-- A run of binders of one kind in a source term (`pi`: ∀s): their domains,
outermost first, and the body. -/
def srcRun (pi : Bool) : Nat → Ix.Expr → Array Ix.Expr → Array Ix.Expr × Ix.Expr
  | 0, x, acc => (acc, unmeta x)
  | fuel + 1, x, acc =>
    let y := unmeta x
    match y with
    | .lam _ ty b _ _ => if pi then (acc, y) else srcRun pi fuel b (acc.push ty)
    | .forallE _ ty b _ _ => if pi then srcRun pi fuel b (acc.push ty) else (acc, y)
    | _ => (acc, y)

/-- **The reading of a source term alone** (`read` without the record), under
`ctx` (its hash `ch`) with the expectation `ex`: fails where a binder's datum is not
read. -/
def readSrc (find : Find) (σ : Ix.Name → Nat) : Nat → List (Option Ix.Expr) → UInt64 →
    Expect → Ix.Expr → SM Unit
  | 0, _, _, _, _ => throw ()
  | fuel + 1, ctx, ch, ex, x => do
    let x := unmeta x
    match x with
    | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. =>
      let key := (ch, x.getHash, ex.toOption)
      if (← get).contains key then return
      modify (·.insert key)
    | _ => pure ()
    match x with
    | .app xf xa _ =>
      readSrc find σ fuel ctx ch ex xf
      let aex : Expect :=
        if readsExpectSrc xa then argExpectOf find σ ctx xf
        else unknown "an argument that reads no expectation"
      readSrc find σ fuel ctx ch aex xa
    | .lam .. | .forallE .. =>
      let pi := x matches .forallE ..
      let (tys, leaf) := srcRun pi readFuel x #[]
      let mut inner := ctx
      let mut ich := ch
      for ty in tys do
        readSrc find σ fuel inner ich (unknown "a binder's domain") ty
        inner := some ty :: inner
        ich := mixHash ich (hash ty.getHash)
      readSrc find σ fuel inner ich (if pi then unknown "a ∀-body" else ex) leaf
      if pi then
        if (sortPw find σ id sortFuel inner leaf).isNone then throw ()
      else if ex.toOption.isNone then throw ()
    | .letE _ ty val body _ _ =>
      readSrc find σ fuel ctx ch (unknown "a let's type") ty
      let vex : Expect := match sortPw find σ id sortFuel ctx ty with
        | some p => .ok p
        | none => unknown "a let's value"
      readSrc find σ fuel ctx ch vex val
      readSrc find σ fuel (some ty :: ctx) (mixHash ch (hash ty.getHash)) ex body
    | .proj _ _ xv _ => readSrc find σ fuel ctx ch (unknown "a projection's subject") xv
    | _ => pure ()

/-- Whether a source constant's every root reads (`memberRoots`' roots, each with
its expectation; an inductive's constructors read as constants of their own). An
unsafe or partial constant reads: its record is not read but undecided. -/
def sourceReads (find : Find) (ci : Ix.ConstantInfo) : Bool :=
  let unsafeOrPartial : Bool := match ci with
    | .defnInfo d => !(d.safety matches .safe)
    | .opaqueInfo o => o.isUnsafe
    | .axiomInfo a => a.isUnsafe
    | .inductInfo i => i.isUnsafe
    | .ctorInfo c => c.isUnsafe
    | .recInfo r => r.isUnsafe
    | _ => false
  if unsafeOrPartial then true else
  let own : Numbering := ⟨ci.getCnst.levelParams, false⟩
  let roots : Array Root := match ci with
    | .defnInfo d => #[⟨own, d.cnst.type, unknown "a type"⟩, ⟨own, d.value, typeExpect find own d.cnst.type⟩]
    | .thmInfo t => #[⟨own, t.cnst.type, unknown "a type"⟩, ⟨own, t.value, .ok (PropWhen.ifAllZero [])⟩]
    | .opaqueInfo o => #[⟨own, o.cnst.type, unknown "a type"⟩, ⟨own, o.value, typeExpect find own o.cnst.type⟩]
    | .recInfo v => recRoots find v
    | ci => #[⟨own, ci.getCnst.type, unknown "a type"⟩]
  roots.all fun r =>
    match ((readSrc find r.σ.pos readFuel [] 0 r.ex r.x).run {}) with
    | .ok _ => true
    | .error _ => false

end Ix.Compile.BinderRead

end
