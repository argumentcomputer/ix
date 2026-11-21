module

public import Ix.Compile.BinderData
public import Ix.LeanIngress.Expr
public import Ix.IndFlags

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
  has the zero-ness of the sort of `B`, the sort of the application's type), a
  type (a constant's type, a binder's domain, a ∀-body: its type is a sort, whose
  sort is never zero; a λ-run is there only as a β-redex's head), an argument of a
  β-redex (its λ's domain; past its λs, an argument of the λs' body's spine).
  It passes unchanged into the run's body, a `let`'s body and a share.

A head's declared type is peeled through the definitions that return one of their
arguments (`outParam T` is `T`) and, where no ∀ is there, through the definition at
its head (δβ: `MorphismProperty C` is `∀ ⦃X Y⦄, (X ⟶ Y) → Prop`). A head is a
constant, a bound variable (its
declared type), or a field of a bound variable or of an application of a constant
whose declared type is a structure
(the field's declared type). An argument beyond its head's ∀s, where the head's
type ends in one of the head's own variables (a `casesOn`'s `motive t`), takes its
domain from the actual argument there, `λ y⃗, R` with as many λs as that variable
has arguments: the domain is `R`'s, and the type after all the arguments is `R`'s
past the rest. A `let` at the head of a type is read through
(its body has the sort of its ζ-reduct).

Anything else (a body headed by a projection of anything but a bound variable or an
application of a constant, a
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

/-- Lightweight hash-free level used inside `BinderRead`'s syntactic type reader
so universe-parameter substitution (`unfold1`, `subjectType`) never BLAKE3-hashes
intermediate level nodes. -/
inductive RLevel where
  | zero
  | succ (l : RLevel)
  | max (a b : RLevel)
  | imax (a b : RLevel)
  | param (n : Ix.Name)
  | mvar (n : Ix.Name)
  deriving Inhabited

/-- Convert an `Ix.Level` into a hash-free `RLevel`. -/
def rLevelOf : Ix.Level → RLevel
  | .zero _ => .zero
  | .succ l _ => .succ (rLevelOf l)
  | .max a b _ => .max (rLevelOf a) (rLevelOf b)
  | .imax a b _ => .imax (rLevelOf a) (rLevelOf b)
  | .param n _ => .param n
  | .mvar n _ => .mvar n

/-- Structural `RLevel` equality ignoring stored name digests. -/
def rLevelSameStructure : RLevel → RLevel → Bool
  | .zero, .zero => true
  | .succ a, .succ b => rLevelSameStructure a b
  | .max a b, .max c d => rLevelSameStructure a c && rLevelSameStructure b d
  | .imax a b, .imax c d => rLevelSameStructure a c && rLevelSameStructure b d
  | .param a, .param b => Ix.Name.beqRaw a b
  | .mvar a, .mvar b => Ix.Name.beqRaw a b
  | _, _ => false

/-- `(base, n)` with `l = succ^n base` and `base` not a successor. -/
def rLevelPeelSucc : RLevel → RLevel × Nat
  | .succ l => let (b, n) := rLevelPeelSucc l; (b, n + 1)
  | l => (l, 0)

/-- `some (base, n)` iff `l` is a numeral `succ^n zero`. -/
def rLevelExplicitOffset (l : RLevel) : Option (RLevel × Nat) :=
  let (base, n) := rLevelPeelSucc l
  match base with
  | .zero => some (base, n)
  | _ => none

/-- `max x y` with the kernel's simplifications, hash-free. -/
def rLevelMaxSmart (x y : RLevel) : RLevel :=
  match rLevelExplicitOffset x, rLevelExplicitOffset y with
  | some (_, ox), some (_, oy) => if ox >= oy then x else y
  | _, _ =>
    if rLevelSameStructure x y then x
    else match x with
      | .zero => y
      | _ => match y with
        | .zero => x
        | _ =>
          let yAbsorbs := match y with
            | .max bl br => rLevelSameStructure bl x || rLevelSameStructure br x
            | _ => false
          if yAbsorbs then y
          else
            let xAbsorbs := match x with
              | .max al ar => rLevelSameStructure al y || rLevelSameStructure ar y
              | _ => false
            if xAbsorbs then x
            else
              let (baseX, offX) := rLevelPeelSucc x
              let (baseY, offY) := rLevelPeelSucc y
              if rLevelSameStructure baseX baseY then
                if offX >= offY then x else y
              else .max x y

/-- `imax x y` with the kernel's simplifications, hash-free. -/
def rLevelImaxSmart (x y : RLevel) : RLevel :=
  match y with
  | .succ _ => rLevelMaxSmart x y
  | .zero => y
  | _ => match x with
    | .zero => y
    | .succ .zero => y
    | _ => if rLevelSameStructure x y then x else .imax x y

/-- Substitute universe parameters in an `RLevel`, hash-free and total. -/
def substRLevel (lvl : RLevel) (params : Array Ix.Name) (univs : Array RLevel) : RLevel :=
  match lvl with
  | .zero | .mvar _ => lvl
  | .succ l => .succ (substRLevel l params univs)
  | .max a b => rLevelMaxSmart (substRLevel a params univs) (substRLevel b params univs)
  | .imax a b => rLevelImaxSmart (substRLevel a params univs) (substRLevel b params univs)
  | .param name => Id.run do
    for h : i in [0:params.size] do
      if hu : Ix.Name.beqRaw params[i] name ∧ i < univs.size then
        return univs[i]'hu.2
    return lvl

/-- Ingress an `RLevel` under parameter numbering `σ`. -/
def ingressRLevel (σ : Ix.Name → Ix.Kernel.LevelParam) : RLevel → Option Ix.Kernel.Level
  | .zero => some .zero
  | .succ u => Ix.Kernel.Level.succ <$> ingressRLevel σ u
  | .max u v => do pure (.max (← ingressRLevel σ u) (← ingressRLevel σ v))
  | .imax u v => do pure (.imax (← ingressRLevel σ u) (← ingressRLevel σ v))
  | .param n => some (.param (σ n))
  | .mvar _ => none

/-- Lightweight hash-free expression with lazy explicit substitutions
(`shift`, `instRev`, `substLvls`), used inside `BinderRead`'s syntactic type
reader. Eliminates BLAKE3 hashing and exponential DAG expansion in `unfold1`
and `subjectType`: substitutions are pushed one head constructor at a time only
along nodes actually inspected. -/
inductive RExpr where
  | raw (e : Ix.Expr)
  | bvar (idx : Nat)
  | sort (l : RLevel)
  | const (name : Ix.Name) (us : Array RLevel)
  | app (f a : RExpr)
  | lam (ty body : RExpr)
  | forallE (ty body : RExpr)
  | letE (ty body : RExpr)
  | proj (sName : Ix.Name) (idx : Nat) (v : RExpr)
  | other (tagStr : String)
  | shift (e : RExpr) (amount cutoff : Nat)
  | instRev (body : RExpr) (args : Array RExpr) (depth : Nat)
  | substLvls (e : RExpr) (params : Array Ix.Name) (univs : Array RLevel)
  deriving Inhabited

/-- Push a single shift step onto an already-forced `RExpr` head node. -/
def shiftHead (e : RExpr) (amount cutoff : Nat) : RExpr :=
  if amount == 0 then e
  else match e with
    | .bvar i => if i >= cutoff then .bvar (i + amount) else e
    | .app f a => .app (.shift f amount cutoff) (.shift a amount cutoff)
    | .lam ty b => .lam (.shift ty amount cutoff) (.shift b amount (cutoff + 1))
    | .forallE ty b => .forallE (.shift ty amount cutoff) (.shift b amount (cutoff + 1))
    | .letE ty b => .letE (.shift ty amount cutoff) (.shift b amount (cutoff + 1))
    | .proj s i v => .proj s i (.shift v amount cutoff)
    | e => e

/-- Expose the concrete top constructor of an `RExpr`, stripping `.raw`/`mdata`
and pushing lazy `.shift`/`.instRev`/`.substLvls` wrappers one constructor down.
Structurally terminating on `RExpr` (total). -/
def force : RExpr → RExpr
  | .raw e =>
    match unmeta e with
    | .bvar i _ => .bvar i
    | .sort l _ => .sort (rLevelOf l)
    | .const c us _ => .const c (us.map rLevelOf)
    | .app f a _ => .app (.raw f) (.raw a)
    | .lam _ ty b _ _ => .lam (.raw ty) (.raw b)
    | .forallE _ ty b _ _ => .forallE (.raw ty) (.raw b)
    | .letE _ ty _ b _ _ => .letE (.raw ty) (.raw b)
    | .proj s i v _ => .proj s i (.raw v)
    | .fvar .. => .other "a free variable"
    | .mvar .. => .other "a metavariable"
    | .lit .. => .other "a literal"
    | .mdata _ inner _ => .other (match inner with | _ => "an expression")
  | .shift e amount cutoff =>
    if amount == 0 then force e
    else shiftHead (force e) amount cutoff
  | .instRev body args depth =>
    if args.isEmpty then force body
    else match force body with
      | .bvar i =>
        if i >= depth then
          if h : i - depth < args.size then shiftHead (force args[i - depth]) depth 0
          else .bvar (i - args.size)
        else .bvar i
      | .app f a => .app (.instRev f args depth) (.instRev a args depth)
      | .lam ty b => .lam (.instRev ty args depth) (.instRev b args (depth + 1))
      | .forallE ty b => .forallE (.instRev ty args depth) (.instRev b args (depth + 1))
      | .letE ty b => .letE (.instRev ty args depth) (.instRev b args (depth + 1))
      | .proj s i v => .proj s i (.instRev v args depth)
      | x => x
  | .substLvls e params univs =>
    if params.isEmpty || univs.isEmpty then force e
    else match force e with
      | .sort l => .sort (substRLevel l params univs)
      | .const c us => .const c (us.map (substRLevel · params univs))
      | .app f a => .app (.substLvls f params univs) (.substLvls a params univs)
      | .lam ty b => .lam (.substLvls ty params univs) (.substLvls b params univs)
      | .forallE ty b => .forallE (.substLvls ty params univs) (.substLvls b params univs)
      | .letE ty b => .letE (.substLvls ty params univs) (.substLvls b params univs)
      | .proj s i v => .proj s i (.substLvls v params univs)
      | x => x
  | e => e
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := Array.sizeOf_lt_of_mem (Array.getElem_mem ‹_›); omega)

/-- Bounds application spine traversal in `RExpr`. -/
def spineFuel : Nat := 1 <<< 16

/-- A spine's forced head and its arguments (innermost first), in one pass. -/
def headSpineRevR : Nat → RExpr → Array RExpr → RExpr × Array RExpr
  | 0, e, acc => (force e, acc)
  | fuel + 1, e, acc =>
    match force e with
    | .app f a => headSpineRevR fuel f (acc.push a)
    | h => (h, acc)

/-- `t` with argument-returning definitions at its head unfolded (δβ, exact):
`outParam T ↦ T`, hash-free on `RExpr`. -/
def unwrapR (find : Find) : Nat → RExpr → RExpr
  | 0, t => force t
  | fuel + 1, t =>
    let t := force t
    let (h, argsRev) := headSpineRevR spineFuel t #[]
    match h with
    | .const c _ =>
      match (find c).bind wrapperOf with
      | some (m, i) =>
        let n := argsRev.size
        if m ≤ n && i < n then
          match argsRev[n - 1 - i]? with
          | some a =>
            let res := Id.run do
              let mut res := a
              for j in [:n - m] do
                res := .app res argsRev[n - m - 1 - j]!
              return res
            unwrapR find fuel res
          | none => t
        else t
      | none => t
    | _ => t

/-- A definition's value as the count of its leading λs and the body under them. -/
def lamBody : Nat → Ix.Expr → Nat × Ix.Expr
  | k, .lam _ _ b _ _ => lamBody (k + 1) b
  | k, .mdata _ e _ => lamBody k e
  | k, e => (k, e)

/-- **One δβ step at the head of `t`** (exact: a definition is its value), lazy and
hash-free on `RExpr`: a safe definition `D.{us} a⃗` whose value is `λ x₁…xₖ, b`,
`k ≤ |a⃗|`, as `b` at `us` and `a₁…aₖ`, applied to the rest. -/
def unfold1R (find : Find) (t : RExpr) : Option RExpr := do
  let (h, argsRev) := headSpineRevR spineFuel t #[]
  let .const c us := h | none
  let .defnInfo d ← find c | none
  guard (d.safety matches .safe)
  guard (us.size == d.cnst.levelParams.size)
  let (k, body) := lamBody 0 d.value
  let n := argsRev.size
  guard (k ≤ n)
  let bodyR : RExpr := .raw body
  let bodyR := if d.cnst.levelParams.isEmpty || us.isEmpty then bodyR
    else .substLvls bodyR d.cnst.levelParams us
  let bodyR := if k == 0 then bodyR
    else .instRev bodyR (argsRev.extract (n - k) n) 0
  let mut res := bodyR
  for j in [:n - k] do
    res := .app res argsRev[n - k - 1 - j]!
  pure res

/-- The unfoldings a type is read through (`unfold1R`), at most. -/
def unfoldFuel : Nat := 16

/-- `t` past exactly `n` leading ∀s, each found after unfolding argument-returning
definitions at the head (`unwrapR`) and, where none is there, a definition
(`unfold1R`, at most `unfoldFuel` times). -/
def peelNR (find : Find) (n : Nat) (t : RExpr) : Option RExpr :=
  go (n + unfoldFuel + 1) n t
where
  go : Nat → Nat → RExpr → Option RExpr
    | 0, _, _ => none
    | _ + 1, 0, t => some (force t)
    | fuel + 1, n + 1, t => match unwrapR find 8 t with
      | .forallE _ b => go fuel n b
      | t => match unfold1R find t with
        | some u => go fuel (n + 1) u
        | none => none

/-- A context entry for syntactic type reading: its type (`RExpr`) paired with
its absolute ambient binder depth (`some d`, `0` = outermost) when it comes
from the ambient reading context, or `none` for temporary local domains inside
`sortPwR`/`argPwR`. -/
abbrev RCtxEntry := Option (RExpr × Option Nat)

/-- Context-tracking monad for syntactic type reading: records the bitmask of
ambient binder depths actually inspected via `lookupCtx`, even when the
reading returns `none`. -/
abbrev CtxM := OptionT (StateM Nat)

/-- Run a `CtxM` computation, returning its optional result and the bitmask of
ambient binder depths inspected. -/
@[inline] def runCtxM {α : Type} (act : CtxM α) : Option α × Nat :=
  act.run.run 0

/-- Lift an `Option` into `CtxM` without touching the bitmask. -/
@[inline] def liftOpt {α : Type} (o : Option α) : CtxM α :=
  OptionT.mk (pure o)

/-- Look up bound variable `i` in `ctx`, recording its ambient binder depth
into the bitmask when present. -/
@[inline] def lookupCtx (ctx : List RCtxEntry) (i : Nat) : CtxM RExpr := do
  match (ctx[i]?).join with
  | some (ty, tag?) =>
    if let some d := tag? then
      modify (· ||| (1 <<< d))
    pure ty
  | none => failure

/-- Extract relative `ctx` indices (`0` = innermost) from an ambient depth
bitmask at context depth `depth`, discarding bits `≥ depth` (binders local to
the subterm). -/
def relIndicesOf (depth : Nat) (absMask : Nat) : Array Nat :=
  let outer := absMask &&& ((1 <<< depth) - 1)
  if outer == 0 then #[]
  else Id.run do
    let mut out : Array Nat := #[]
    let mut m := outer
    let mut d := 0
    for _ in [:depth] do
      if m == 0 then break
      if (m &&& 1) == 1 then
        out := out.push (depth - 1 - d)
      m := m >>> 1
      d := d + 1
    return out

/-- Map relative `ctx` indices back to an ambient depth bitmask at depth `depth`. -/
def absMaskOf (depth : Nat) (idxs : Array Nat) : Nat :=
  idxs.foldl (init := 0) fun acc i =>
    if i < depth then acc ||| (1 <<< (depth - 1 - i)) else acc

/-- Hash of the `ctx` entries at the relative indices `idxs`. -/
def maskHash (hs : List UInt64) (idxs : Array Nat) : UInt64 :=
  idxs.foldl (init := 11) fun acc i => mixHash acc (hs[i]?.getD 0)

/-- Addresses of the `ctx` entries at the relative indices `idxs`. -/
def maskAddrs (hs : List (Option Address)) (idxs : Array Nat) : Array (Option Address) :=
  idxs.map fun i => (hs[i]?).join

/-- The `n`-th ∀-domain of `t`, with the domains before it, innermost first; each ∀
found as `peelNR` finds it. -/
def domainAtR (find : Find) (n : Nat) (t : RExpr) (acc : List RCtxEntry) :
    Option (RExpr × List RCtxEntry) :=
  go (n + unfoldFuel + 1) n t acc
where
  go : Nat → Nat → RExpr → List RCtxEntry → Option (RExpr × List RCtxEntry)
    | 0, _, _, _ => none
    | fuel + 1, n, t, acc => match unwrapR find 8 t, n with
      | .forallE d _, 0 => some (d, acc)
      | .forallE d b, n + 1 => go fuel n b (some (d, none) :: acc)
      | t, n => match unfold1R find t with
        | some u => go fuel n u acc
        | none => none

/-- Bounds the ∀s and `let`s a sort is read through. -/
def sortFuel : Nat := 1 <<< 12

/-- The final sort of a ∀-telescope `t`, if it is syntactically a sort. -/
def leafSortR : Nat → RExpr → Option RLevel
  | 0, _ => none
  | fuel + 1, t => match force t with
    | .sort l => some l
    | .forallE _ b => leafSortR fuel b
    | _ => none

/-- The level of `a` when it is `Sort l` under exactly `k` λs. -/
def lamSortR : Nat → RExpr → Option RLevel
  | 0, a => match force a with
    | .sort l => some l
    | _ => none
  | k + 1, a => match force a with
    | .lam _ b => lamSortR k b
    | _ => none

/-- `a` as exactly `k` λs: their binder types (innermost first, before `acc`) and
the body. -/
def lamsExactR : Nat → RExpr → List RCtxEntry → Option (List RCtxEntry × RExpr)
  | 0, a, acc => some (acc, force a)
  | k + 1, a, acc => match force a with
    | .lam ty b => lamsExactR k b (some (ty, none) :: acc)
    | _ => none

/-- The number of ∀s of `t`, each found as `peelNR` finds it. -/
def piCountR (find : Find) : Nat → RExpr → Nat
  | 0, _ => 0
  | fuel + 1, t => match unwrapR find 8 t with
    | .forallE _ b => piCountR find fuel b + 1
    | _ => 0

/-- **The type of a projection's subject `v`, read syntactically** (lazy and
hash-free on `RExpr`): a bound variable's declared type (under `ctx`), or, for
an application `g a⃗` of a constant, `g`'s declared type past `|a⃗|` ∀s (each
found as `peelNR` finds it) with `a⃗` for them, at `g`'s levels. -/
def subjectTypeR (find : Find) (ctx : List RCtxEntry) (v : RExpr) : CtxM RExpr :=
  match force v with
  | .bvar k => lookupCtx ctx k
  | v => do
    let (h, argsRev) := headSpineRevR spineFuel v #[]
    let .const g us := h | failure
    let cv := (← liftOpt (find g)).getCnst
    guard (us.size == cv.levelParams.size)
    let n := argsRev.size
    let r ← liftOpt (peelNR find n (.raw cv.type))
    let r := if cv.levelParams.isEmpty || us.isEmpty then r
      else .substLvls r cv.levelParams us
    let r := if n == 0 then r else .instRev r argsRev 0
    pure r

/-- **The field a projection `.proj S i v` reads**, when the type of `v` (a bound
variable, or an application of a constant: `subjectTypeR`) is `S.{us} p⃗`, `S` a
structure (one constructor, no indices): the field's type in its constructor's
telescope, the constructor's domains before it (innermost first), the
constructor's level parameters, `us`, and `p⃗` (innermost first). -/
def projFieldR (find : Find) (ctx : List RCtxEntry) (sName : Ix.Name) (i : Nat)
    (v : RExpr) :
    CtxM (RExpr × List RCtxEntry × Array Ix.Name × Array RLevel × Array RExpr) := do
  let vty := unwrapR find 8 (← subjectTypeR find ctx v)
  let (vh, pargsRev) := headSpineRevR spineFuel vty #[]
  let .const S us := vh | failure
  guard (Ix.Name.beqRaw S sName)
  let .inductInfo ind ← liftOpt (find S) | failure
  let np := pargsRev.size
  guard (ind.numIndices == 0 && np == ind.numParams)
  let #[c] := ind.ctors | failure
  let .ctorInfo ctor ← liftOpt (find c) | failure
  let (d, before) ← liftOpt (domainAtR find (ind.numParams + i) (.raw ctor.cnst.type) [])
  pure (d, before, ctor.cnst.levelParams, us, pargsRev)

/-- **The type after `n` arguments, beyond the head's ∀s**: the head's type `ty`
has `m < n` ∀s and ends in one of the head's own variables applied to `k`
arguments (`DFunLike.coe`'s `β a`, `Eq.mp`'s `β`); the actual argument there
(`argsRev`, the spine's, innermost first, of length `n`) is `λ y⃗, R` with
exactly `k` λs, so the type there is `R` with the arguments for `y⃗`, and the
type after the `n` arguments is `R` past `n - m` ∀s. -/
def beyondTypeR (find : Find) (ty : RExpr) (argsRev : Array RExpr) (n : Nat) : Option RExpr := do
  let m := piCountR find sortFuel ty
  guard (m < n)
  let r ← peelNR find m ty
  let (rh, rArgsRev) := headSpineRevR spineFuel (unwrapR find 8 r) #[]
  let .bvar j := rh | none
  guard (j < m)
  let k := rArgsRev.size
  let a ← argsRev[n - m + j]?
  let (_, body) ← lamsExactR k a []
  peelNR find (n - m) body

/-- **The zero-ness of the sort of the type `t`, read syntactically.** `σ`
numbers the level parameters `t` and `ctx` (the types of `t`'s loose variables,
innermost first) are written over, and `sub` maps levels in that numbering to
the reader's. A `let` at the head is read through (its body has the sort of its
ζ-reduct). `none` where the reading does not apply. -/
def sortPwR (find : Find) (σ : Ix.Name → Nat) (sub : Ix.Kernel.Level → Ix.Kernel.Level) :
    Nat → List RCtxEntry → RExpr → CtxM PropWhen
  | 0, _, _ => failure
  | fuel + 1, ctx, t =>
    match unwrapR find 8 t with
    | .sort _ => pure .never
    | .forallE d b => sortPwR find σ sub fuel (some (d, none) :: ctx) b
    | .letE ty b => sortPwR find σ sub fuel (some (ty, none) :: ctx) b
    | t => do
      let (h, argsRev) := headSpineRevR spineFuel t #[]
      let n := argsRev.size
      let lvl? : Option Ix.Kernel.Level ← match h with
        | .const c us =>
          pure <| (do
            let ci ← find c
            let cv := ci.getCnst
            let headLevel (l : RLevel) : Option Ix.Kernel.Level := do
              let lc ← ingressRLevel (posIn cv.levelParams) l
              let us' ← us.toList.mapM (ingressRLevel σ)
              pure (Ix.Kernel.Level.subst (List.range cv.levelParams.size) us' lc)
            match peelNR find n (.raw cv.type) with
            | some r =>
              match unwrapR find 8 r with
              | .sort l => headLevel l
              | r =>
                let (rh, rArgsRev) := headSpineRevR spineFuel r #[]
                match rh with
                | .bvar j =>
                  guard (j < n)
                  let a ← argsRev[j]?
                  let l ← lamSortR rArgsRev.size a
                  ingressRLevel σ l
                | _ =>
                  let .sort l := unwrapR find 8 (← unfold1R find r) | none
                  headLevel l
            | none =>
              let .sort l := unwrapR find 8 (← beyondTypeR find (.raw cv.type) argsRev n) | none
              ingressRLevel σ l)
        | .bvar i =>
          OptionT.mk do
            let st ← get
            let (ty?, st') := (lookupCtx ctx i).run.run st
            set st'
            pure <| ty?.bind fun ty =>
              match peelNR find n ty with
              | some r =>
                match unwrapR find 8 r with
                | .sort l => ingressRLevel σ l
                | r => do
                  let .sort l := unwrapR find 8 (← unfold1R find r) | none
                  ingressRLevel σ l
              | none => do
                let .sort l := unwrapR find 8 (← beyondTypeR find ty argsRev n) | none
                ingressRLevel σ l
        | .proj sName i v =>
          OptionT.mk do
            let st ← get
            let (pf?, st') := (projFieldR find ctx sName i v).run.run st
            set st'
            pure <| pf?.bind fun (fty, _, lps, us, pargsRev) => do
              match unwrapR find 8 (← peelNR find n fty) with
              | .sort l =>
                let lc ← ingressRLevel (posIn lps) l
                let us' ← us.toList.mapM (ingressRLevel σ)
                pure (Ix.Kernel.Level.subst (List.range lps.size) us' lc)
              | r =>
                let (rh, rArgsRev) := headSpineRevR spineFuel r #[]
                let .bvar j := rh | none
                guard (n + i ≤ j && j < n + i + pargsRev.size)
                let a ← pargsRev[j - n - i]?
                let l ← lamSortR rArgsRev.size a
                ingressRLevel σ l
        | _ => pure none
      match lvl? with
      | some l => pure (Ix.Kernel.Level.zeronessOf (sub l))
      | none =>
        -- a β-redex at the head, its λs consumed exactly: the body's sort (a level
        -- names no term variable)
        match h with
        | .lam .. => do
          let (ys, body) ← liftOpt (lamsExactR n h [])
          sortPwR find σ sub fuel (ys ++ ctx) body
        | _ => failure

/-- **The domain of the argument at `idx` beyond its head's ∀s**: the head's type
`ty` has `m ≤ idx` ∀s and ends in one of the head's own variables applied to `k`
arguments (a `casesOn`'s `motive t`); the actual argument there (`args`, the
spine's, outermost first) is `λ y⃗, R` with exactly `k` λs, so the type there is
`R` with the arguments for `y⃗`, and the domain is `R`'s at `idx - m`. The domain
and the types of its loose variables (innermost first, the spine's `ctx` last),
its levels in the spine's numbering. -/
def beyondDomainR (find : Find) (ctx : List RCtxEntry) (ty : RExpr)
    (args : Array Ix.Expr) (idx : Nat) : Option (RExpr × List RCtxEntry) := do
  let m := piCountR find sortFuel ty
  guard (m ≤ idx)
  let r ← peelNR find m ty
  let (rh, rArgsRev) := headSpineRevR spineFuel (unwrapR find 8 r) #[]
  let .bvar j := rh | none
  guard (j < m)
  let a ← args[m - 1 - j]?
  let (ys, body) ← lamsExactR rArgsRev.size (.raw a) []
  let (d, before) ← domainAtR find (idx - m) body []
  pure (d, before ++ ys ++ ctx)

/-- The domain of the `n`-th λ of `t`, with the domains before it, innermost first. -/
def lamDomainAtR : Nat → Ix.Expr → List RCtxEntry → Option (RExpr × List RCtxEntry)
  | n, t, acc => match unmeta t, n with
    | .lam _ d _ _ _, 0 => some (.raw d, acc)
    | .lam _ d b _ _, n + 1 => lamDomainAtR n b (some (.raw d, none) :: acc)
    | _, _ => none

/-- `argPwR` at a spine head that is a constant, a bound variable under `ctx`, or a
field of a structure-typed bound variable or constant application (`projFieldR`). -/
def argPwHeadR (find : Find) (σ : Ix.Name → Nat) (ctx : List RCtxEntry) (h : Ix.Expr)
    (args : Array Ix.Expr) (idx : Nat) : CtxM PropWhen :=
  match h with
  | .const c us _ => do
    let ci ← liftOpt (find c)
    let cv := ci.getCnst
    match domainAtR find idx (.raw cv.type) [] with
    | some (d, before) =>
      let us' ← liftOpt (us.toList.mapM (ingressLevel σ)).toOption
      sortPwR find (posIn cv.levelParams)
        (Ix.Kernel.Level.subst (List.range cv.levelParams.size) us') sortFuel before d
    | none =>
      let (d, dctx) ← liftOpt (beyondDomainR find ctx (.raw cv.type) args idx)
      sortPwR find σ id sortFuel dctx d
  | .bvar i _ => do
    let ty ← lookupCtx ctx i
    match domainAtR find idx ty [] with
    | some (d, before) => sortPwR find σ id sortFuel (before ++ ctx.drop (i + 1)) d
    | none =>
      let (d, dctx) ← liftOpt (beyondDomainR find ctx ty args idx)
      sortPwR find σ id sortFuel dctx d
  | .proj sName j v _ => do
    let (fty, fctx, lps, us, _) ← projFieldR find ctx sName j (.raw v)
    let (d, before) ← liftOpt (domainAtR find idx fty [])
    let us' ← liftOpt (us.toList.mapM (ingressRLevel σ))
    sortPwR find (posIn lps) (Ix.Kernel.Level.subst (List.range lps.size) us') sortFuel
      (before ++ fctx) d
  | _ => failure

/-- The zero-ness of the sort of the domain at `idx` of the type of the spine
head `h` (a constant, a bound variable under `ctx`, a field (`projFieldR`),
or a β-redex's λs; `args` the spine's arguments before `idx`, outermost
first): what an argument there has as its type's sort.

At a β-redex's head `λ y₁…yₖ, b`, an argument at `idx < k` has the domain of the
`idx`-th λ. One past the λs is an argument of `b`'s spine `g b⃗` (the redex's type
after its first `k` arguments is `b`'s with those arguments for `y⃗`), at
`|b⃗| + idx - k`, read under the λs' domains: a level names no term variable, so the
sort of the domain there has the same zero-ness with the arguments for `y⃗`. -/
def argPwR (find : Find) (σ : Ix.Name → Nat) (ctx : List RCtxEntry) (h : Ix.Expr)
    (args : Array Ix.Expr) (idx : Nat) : CtxM PropWhen :=
  match h with
  | .lam .. =>
    match lamDomainAtR idx h [] with
    | some (d, before) => sortPwR find σ id sortFuel (before ++ ctx) d
    | none => do
      let k := (lamBody 0 h).1
      guard (k ≤ idx)
      let (ys, body) ← liftOpt (lamsExactR k (.raw h) [])
      let (g, bArgsRev) := headSpineRevR spineFuel body #[]
      let m := bArgsRev.size
      let bArgs := bArgsRev.reverse
      match g with
      | .const c us =>
        let ci ← liftOpt (find c)
        let cv := ci.getCnst
        match domainAtR find (m + (idx - k)) (.raw cv.type) [] with
        | some (d, before) =>
          let us' ← liftOpt (us.toList.mapM (ingressRLevel σ))
          sortPwR find (posIn cv.levelParams)
            (Ix.Kernel.Level.subst (List.range cv.levelParams.size) us') sortFuel before d
        | none =>
          let dctx := ys ++ ctx
          let mm := piCountR find sortFuel (.raw cv.type)
          guard (mm ≤ m + (idx - k))
          let r ← liftOpt (peelNR find mm (.raw cv.type))
          let (rh, rArgsRev) := headSpineRevR spineFuel (unwrapR find 8 r) #[]
          let .bvar j := rh | failure
          guard (j < mm)
          let a ← liftOpt bArgs[mm - 1 - j]?
          let (ys', bd) ← liftOpt (lamsExactR rArgsRev.size a [])
          let (d, before) ← liftOpt (domainAtR find ((m + (idx - k)) - mm) bd [])
          sortPwR find σ id sortFuel (before ++ ys' ++ dctx) d
      | .bvar i =>
        let dctx := ys ++ ctx
        let ty ← lookupCtx dctx i
        match domainAtR find (m + (idx - k)) ty [] with
        | some (d, before) => sortPwR find σ id sortFuel (before ++ dctx.drop (i + 1)) d
        | none =>
          let mm := piCountR find sortFuel ty
          guard (mm ≤ m + (idx - k))
          let r ← liftOpt (peelNR find mm ty)
          let (rh, rArgsRev) := headSpineRevR spineFuel (unwrapR find 8 r) #[]
          let .bvar j := rh | failure
          guard (j < mm)
          let a ← liftOpt bArgs[mm - 1 - j]?
          let (ys', bd) ← liftOpt (lamsExactR rArgsRev.size a [])
          let (d, before) ← liftOpt (domainAtR find ((m + (idx - k)) - mm) bd [])
          sortPwR find σ id sortFuel (before ++ ys' ++ dctx) d
      | .proj sName j v =>
        let dctx := ys ++ ctx
        let (fty, fctx, lps, us, _) ← projFieldR find dctx sName j v
        let (d, before) ← liftOpt (domainAtR find (m + (idx - k)) fty [])
        let us' ← liftOpt (us.toList.mapM (ingressRLevel σ))
        sortPwR find (posIn lps) (Ix.Kernel.Level.subst (List.range lps.size) us') sortFuel
          (before ++ fctx) d
      | _ => failure
  | h => argPwHeadR find σ ctx h args idx

/-! ## The reading of a record -/

/-- What a record's reading reads. -/
structure Cx where
  find : Find
  /-- the root's numbering of level parameters -/
  σ : Numbering
  sharing : Array Ixon.Expr
  bounds : Array Nat
  /-- whether each sharing entry has a binder (`IxVM.PwHints.binderful`) -/
  full : Array Bool := #[]

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

/-- Cached variant(s) of a share site `(entry, source hash, used expectation)`:
either independent of `ctx` (`.indep`) or keyed by the exact relative `ctx`
indices actually inspected during the read (`.dep`). -/
inductive MemoVal where
  | indep (variant : Nat)
  | dep (entries : Array (Array Nat × Std.HashMap (Array (Option Address)) Nat))

/-- The reading's state: the sharing entries' variants (by node list) and
blocks, and the demand-driven memo of share sites. -/
structure RState where
  variants : Std.HashMap Nat (Std.HashMap (Array Node) Nat) := {}
  blocks : Array Block := #[]
  memo : Std.HashMap (Nat × Address × Option (Option PropWhen)) MemoVal := {}

/-- A reading fails at the first binder it cannot read, saying what stands there. -/
abbrev RM := StateT RState (Except String)
/-- An entry's reading: its nodes' data, by ordinal. -/
abbrev NM := StateT (Array Node) RM

/-- What the reading expects of a term's type: the zero-ness of its sort, or why
it does not know it (the reason is built only where a reading fails on it). -/
abbrev Expect := Except (Unit → String) PropWhen

/-- An expectation not known, for the reason `why`. -/
def unknown (why : String) : Expect := .error fun _ => why

/-- The expectation of a type (a constant's type, a binder's domain, a ∀-body, a
`let`'s type): its type is a sort, whose sort is never zero. A λ-run stands there
only as a β-redex's head (`λ y⃗, T` applied, `T` a type), and so has that datum. -/
def asType : Expect := .ok .never

private def reserve : NM Nat :=
  modifyGet fun nodes => (nodes.size, nodes.push (.binder none))

private def setNode (ord : Nat) (n : Node) : NM Unit :=
  modify fun nodes => nodes.set! ord n

private def variantOf (n : Nat) (nodes : Array Node) : RM Nat :=
  -- one update of the state, so that its tables change in place
  modifyGet fun st =>
    let table := st.variants.getD n {}
    match table[nodes]? with
    | some v => (v, st)
    | none =>
      let v := table.size
      (v, { st with variants := st.variants.insert n (table.insert nodes v)
                    blocks := st.blocks.push ⟨1, n, v, nodes⟩ })

private def findMemo (memo : Std.HashMap (Nat × Address × Option (Option PropWhen)) MemoVal)
    (k : Nat × Address × Option (Option PropWhen)) (ctxHashes : List (Option Address)) :
    Option (Array Nat × Nat) :=
  match memo[k]? with
  | none => none
  | some (.indep v) => some (#[], v)
  | some (.dep entries) => Id.run do
    for (idxs, tbl) in entries do
      if let some v := tbl[maskAddrs ctxHashes idxs]? then
        return some (idxs, v)
    return none

private def insertMemo (memo : Std.HashMap (Nat × Address × Option (Option PropWhen)) MemoVal)
    (k : Nat × Address × Option (Option PropWhen)) (idxs : Array Nat)
    (ctxHashes : List (Option Address)) (v : Nat) :
    Std.HashMap (Nat × Address × Option (Option PropWhen)) MemoVal :=
  if idxs.isEmpty then
    memo.insert k (.indep v)
  else
    let key := maskAddrs ctxHashes idxs
    match memo[k]? with
    | some (.dep entries) =>
      match entries.findIdx? (fun (i, _) => i == idxs) with
      | some pos =>
        let (i, tbl) := entries[pos]!
        memo.insert k (.dep (entries.set! pos (i, tbl.insert key v)))
      | none =>
        memo.insert k (.dep (entries.push (idxs, ({} : Std.HashMap _ _).insert key v)))
    | _ =>
      memo.insert k (.dep #[(idxs, ({} : Std.HashMap _ _).insert key v)])

/-- A run of binders of one kind in the record's tree and its source: each
binder's domain in both, then both bodies. -/
def binderRun (pi : Bool) : Ixon.Expr → Ix.Expr → Array (Ixon.Expr × Ix.Expr) →
    Ixon.Expr × Ix.Expr × Array (Ixon.Expr × Ix.Expr)
  | e@(.lam t b), x, acc => match unmeta x with
    | .lam _ ty body _ _ => if pi then (e, x, acc) else binderRun pi b body (acc.push (t, ty))
    | _ => (e, x, acc)
  | e@(.all t b), x, acc => match unmeta x with
    | .forallE _ ty body _ _ => if pi then binderRun pi b body (acc.push (t, ty)) else (e, x, acc)
    | _ => (e, x, acc)
  | e, x, acc => (e, x, acc)

/-- A source node's kind, for the reasons. -/
def tag : Ix.Expr → String
  | .bvar .. => "a variable" | .fvar .. => "a free variable" | .mvar .. => "a metavariable"
  | .sort .. => "a sort" | .const .. => "a constant" | .app .. => "an application"
  | .lam .. => "a λ" | .forallE .. => "a ∀" | .letE .. => "a let" | .lit .. => "a literal"
  | .mdata _ e _ => tag e | .proj .. => "a projection"

/-- A forced `RExpr` node's kind, for failure reasons. -/
def tagR (e : RExpr) : String :=
  match force e with
  | .bvar _ => "a variable" | .sort _ => "a sort" | .const .. => "a constant"
  | .app .. => "an application" | .lam .. => "a λ" | .forallE .. => "a ∀"
  | .letE .. => "a let" | .proj .. => "a projection" | .other s => s
  | _ => "an expression"

/-- Why the sort of the type `t` (under `ctx`) is not read: its head's shape. -/
def shapeOfR (find : Find) (ctx : List RCtxEntry) (t : RExpr) : String :=
  let rec leaf : Nat → RExpr → RExpr
    | 0, t => t
    | n + 1, t => match unwrapR find 8 t with
      | .forallE _ b => leaf n b
      | t => t
  let t := leaf 64 t
  let (h, argsRev) := headSpineRevR spineFuel t #[]
  let n := argsRev.size
  match h with
  | .const c _ => match find c with
    | some ci => match peelNR find n (.raw ci.getCnst.type) with
      | some r => s!"{c.pretty} applied to {n}, whose type there is {tagR (unwrapR find 8 r)}"
      | none => s!"{c.pretty} applied to {n}, more than its type's ∀s"
    | none => s!"{c.pretty}, not found"
  | .bvar i => match (ctx[i]?).join with
    | some (ty, _) => match peelNR find n ty with
      | some r => s!"a variable applied to {n}, whose type there is {tagR (unwrapR find 8 r)}"
      | none => s!"a variable applied to {n}, more than its type's ∀s"
    | none => "a let-bound variable"
  | h => s!"{tagR h} applied to {n}"

/-- The expectation of an argument at `idx` of a spine headed by `h` (`args` the
arguments before it, outermost first), paired with the ambient binder depth
bitmask inspected. -/
def argExpect (find : Find) (σ : Ix.Name → Nat) (ctx : List RCtxEntry) (h : Ix.Expr)
    (args : Array Ix.Expr) (idx : Nat) : Expect × Nat :=
  let (pw?, used) := runCtxM (argPwR find σ ctx h args idx)
  match pw? with
  | some p => (.ok p, used)
  | none =>
    (.error fun _ =>
      let head := match h with
        | .const c _ _ => c.pretty
        | h => tag h
      let dom : Option (RExpr × List RCtxEntry) := match h with
        | .const c _ _ => (find c).bind fun ci => domainAtR find idx (.raw ci.getCnst.type) []
        | .bvar i _ => (ctx[i]?).join.bind fun (ty, _) => domainAtR find idx ty []
        | _ => none
      match dom with
      | some (d, before) => s!"argument {idx} of {head}, its domain headed by {shapeOfR find before d}"
      | none => s!"argument {idx} of {head}, beyond its type's ∀s",
     used)

/-- The expectation of the next argument of the spine `xf`, with the ambient
binder depth bitmask inspected. -/
def argExpectOf (find : Find) (σ : Ix.Name → Nat) (ctx : List RCtxEntry) (xf : Ix.Expr) :
    Expect × Nat :=
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
(length `depth`, innermost first; `ctxHashes` their cached addresses), with `ex`
the zero-ness of the sort of `x`'s type where it is known. Returns `(usedAbs,
usedEx)`: the bitmask of ambient binder depths inspected and whether `ex` was
inspected. Every numbered node of `e` gets its datum at its ordinal; the reading
fails where a datum is not read, saying what stands there. -/
def read : Nat → Cx → List RCtxEntry → List (Option Address) → Nat → Expect →
    Ixon.Expr → Ix.Expr → NM (Nat × Bool)
  | 0, _, _, _, _, _, _, _ => throw "the reading's depth bound"
  | fuel + 1, cx, ctx, ctxHashes, depth, ex, e, x =>
    match e, unmeta x with
    | .var _, .bvar .. => pure (0, false)
    | .app f a, .app xf xa _ => do
      -- the function's type `∀ x⃗, B` has the zero-ness of the sort of `B`, which is
      -- the sort of the application's type `B[a⃗/x⃗]` (a level names no term variable):
      -- a β-redex's λ-run has the application's expectation
      let (uf, ef) ← read fuel cx ctx ctxHashes depth ex f xf
      -- the expectation is computed only for an argument that reads it
      let (aex, uArg) : Expect × Nat :=
        if readsExpect a then argExpectOf cx.find cx.σ.pos ctx xf
        else (unknown "an argument that reads no expectation", 0)
      let (ua, _) ← read fuel cx ctx ctxHashes depth aex a xa
      pure (uf ||| uArg ||| ua, ef)
    | .lam .., .lam .. | .all .., .forallE .. => do
      let pi := e matches .all ..
      let (leafE, leafX, bs) := binderRun pi e x #[]
      let mut inner := ctx
      let mut innerHashes := ctxHashes
      let mut ords : Array Nat := #[]
      let mut u := 0
      for h : j in [:bs.size] do
        let (t, ty) := bs[j]
        ords := ords.push (← reserve)
        let (ut, _) ← read fuel cx inner innerHashes (depth + j) (asType) t ty
        u := u ||| ut
        inner := some (.raw ty, some (depth + j)) :: inner
        innerHashes := some ty.getHash :: innerHashes
      let (ul, _) ← read fuel cx inner innerHashes (depth + bs.size) (if pi then asType else ex) leafE leafX
      u := u ||| ul
      let pw ← if pi then
          let (pw?, upw) := runCtxM (sortPwR cx.find cx.σ.pos id sortFuel inner (.raw leafX))
          u := u ||| upw
          match pw? with
          | some p => pure p
          | none => throw s!"a ∀-body headed by {shapeOfR cx.find inner (.raw leafX)}"
        else match ex with
          | .ok p => pure p
          | .error why => throw s!"a λ-run as {why ()}"
      let node := cx.nodeOf pw
      for ord in ords do setNode ord node
      pure (u, !pi)
    | .letE _ _ t v b, .letE _ ty val body _ _ => do
      let (ut, _) ← read fuel cx ctx ctxHashes depth (asType) t ty
      let (pw?, upw) := runCtxM (sortPwR cx.find cx.σ.pos id sortFuel ctx (.raw ty))
      let vex : Expect := match pw? with
        | some p => .ok p
        | none => .error fun _ => s!"a let's value, its type headed by {shapeOfR cx.find ctx (.raw ty)}"
      let (uv, _) ← read fuel cx ctx ctxHashes depth vex v val
      let (ub, eb) ← read fuel cx (some (.raw ty, some depth) :: ctx)
        (some ty.getHash :: ctxHashes) (depth + 1) ex b body
      pure (ut ||| upw ||| uv ||| ub, eb)
    | .prj _ _ v, .proj _ _ xv _ => do
      let (uv, _) ← read fuel cx ctx ctxHashes depth (unknown "a projection's subject") v xv
      pure (uv, false)
    | .share n, _ => do
      let ord ← reserve
      let n := n.toNat
      -- an entry without a binder has no data (its share node leaves the section)
      if !(cx.full[n]?.getD true) then
        setNode ord (.share 0)
        return (0, false)
      let hx := x.getHash
      let eOpt := ex.toOption
      let hit ← modifyGetThe RState fun st =>
        match findMemo st.memo (n, hx, none) ctxHashes with
        | some (idxs, v) => (some (idxs, v, false), st)
        | none =>
          match findMemo st.memo (n, hx, some eOpt) ctxHashes with
          | some (idxs, v) => (some (idxs, v, true), st)
          | none => (none, st)
      match hit with
      | some (idxs, variant, usedEx) =>
        setNode ord (.share variant)
        pure (absMaskOf depth idxs, usedEx)
      | none => do
        let some entry := cx.sharing[n]? | throw "a share without its entry"
        let ((cu, ce), nodes) ← ((read fuel cx ctx ctxHashes depth ex entry x).run #[] :
          RM ((Nat × Bool) × Array Node))
        let v ← variantOf n nodes
        let idxs := relIndicesOf depth cu
        let k := (n, hx, if ce then some eOpt else none)
        modifyThe RState fun st => { st with memo := insertMemo st.memo k idxs ctxHashes v }
        setNode ord (.share v)
        pure (cu, ce)
    | .sort _, .sort .. | .ref .., .const .. | .recur .., .const .. | .str _, .lit .. | .nat _, .lit .. =>
      pure (0, false)
    | _, x => throw s!"a record node that is not its source's ({tag x})"

/-! ## A record's roots and their expectations -/

/-- A root's source, its numbering, and the zero-ness of its type's sort where
the reading needs it (a value's, a rule right-hand side's). -/
structure Root where
  σ : Numbering
  x : Ix.Expr
  ex : Expect := asType

/-- The zero-ness of the sort of a definition's type `ty`, numbered by `σ`. -/
def typeExpect (find : Find) (σ : Numbering) (ty : Ix.Expr) : Expect :=
  match (runCtxM (sortPwR find σ.pos id sortFuel [] (.raw ty))).1 with
  | some p => .ok p
  | none => .error fun _ => s!"a definition's value, its type headed by {shapeOfR find [] (.raw ty)}"

/-- A recursor's roots: its type and its rules' right-hand sides, numbered as its
record numbers them (a large eliminator's motive universe first). A rule's
right-hand side has the sort of its motive's codomain: the elimination level. -/
def recRoots (find : Find) (v : Ix.RecursorVal) : Array Root :=
  let indLevels := match v.all[0]?.bind find with
    | some (.inductInfo i) => i.cnst.levelParams.size
    | _ => v.cnst.levelParams.size
  let σ : Numbering := ⟨v.cnst.levelParams, v.cnst.levelParams.size == indLevels + 1⟩
  let elim : Expect := match (do
      let (motive, _) ← domainAtR find v.numParams (.raw v.cnst.type) []
      let l ← leafSortR sortFuel motive
      let l' ← ingressRLevel σ.pos l
      pure (Ix.Kernel.Level.zeronessOf l') : Option PropWhen) with
    | some p => .ok p
    | none => unknown "a rule's right-hand side, its motive's sort not read"
  (#[⟨σ, v.cnst.type, asType⟩] : Array Root) ++
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
    | .defnInfo d => some #[⟨σ, d.cnst.type, asType⟩, ⟨σ, d.value, typeExpect find σ d.cnst.type⟩]
    | .thmInfo t => some #[⟨σ, t.cnst.type, asType⟩, ⟨σ, t.value, .ok (PropWhen.ifAllZero [])⟩]
    | .opaqueInfo o => some #[⟨σ, o.cnst.type, asType⟩, ⟨σ, o.value, typeExpect find σ o.cnst.type⟩]
    | _ => none
  | .inr (.axio _) => match ci with
    | .axiomInfo a => some #[⟨⟨a.cnst.levelParams, false⟩, a.cnst.type, asType⟩]
    | _ => none
  | .inr (.quot _) => match ci with
    | .quotInfo q => some #[⟨⟨q.cnst.levelParams, false⟩, q.cnst.type, asType⟩]
    | _ => none
  | .inl (.recr r) | .inr (.recr r) => match ci with
    | .recInfo v => do
      guard (v.rules.size == r.rules.size)
      some (recRoots find v)
    | _ => none
  | .inl (.indc i) => match ci with
    | .inductInfo v => do
      let ctors ← v.ctors.mapM fun n => match find n with
        | some (.ctorInfo k) => some (⟨⟨k.cnst.levelParams, false⟩, k.cnst.type, asType⟩ : Root)
        | _ => none
      guard (ctors.size == i.ctors.size)
      some ((#[⟨⟨v.cnst.levelParams, false⟩, v.cnst.type, asType⟩] : Array Root) ++ ctors)
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
  let full := IxVM.PwHints.binderful c.sharing
  let act : RM (Array Block) := do
    let mut out := #[]
    for h : i in [:rs.size] do
      let some r := roots[i]? | throw "a root without its source"
      let cx : Cx := { find, σ := r.σ, sharing := c.sharing, bounds, full }
      let (_, nodes) ← (read readFuel cx [] [] 0 r.ex rs[i] r.x).run #[]
      out := out.push ⟨0, i, 0, nodes⟩
    return out
  let (blocks, st) ← act.run {}
  let cWithModes := { c with binders := Ix.Compile.BinderData.sourceModeSection find names c }
  Ix.Compile.BinderData.sectionOf cWithModes (blocks ++ st.blocks)

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

/-- Cached source reads of `(address, used expectation)`: either independent of
`ctx` (`.indep`) or keyed by the exact relative `ctx` indices actually inspected
during the read (`.dep`). -/
inductive SeenVal where
  | indep
  | dep (entries : Array (Array Nat × Std.HashSet UInt64))

/-- The terms read so far, demand-keyed on only the `ctx` entries and
expectation actually inspected: avoids exponential blowup on DAG-shared proof
subterms appearing under distinct unused binders. -/
abbrev Seen := Std.HashMap (Address × Option (Option PropWhen)) SeenVal

/-- The source reading's state, updated in place. -/
abbrev SM := StateT Seen (Except Unit)

private def findSeen (seen : Seen) (k : Address × Option (Option PropWhen)) (hs : List UInt64) :
    Option (Array Nat) :=
  match seen[k]? with
  | none => none
  | some .indep => some #[]
  | some (.dep entries) => Id.run do
    for (idxs, hashes) in entries do
      if hashes.contains (maskHash hs idxs) then
        return some idxs
    return none

private def insertSeen (seen : Seen) (k : Address × Option (Option PropWhen))
    (idxs : Array Nat) (hs : List UInt64) : Seen :=
  if idxs.isEmpty then
    seen.insert k .indep
  else
    let h := maskHash hs idxs
    match seen[k]? with
    | some (.dep entries) =>
      match entries.findIdx? (fun (i, _) => i == idxs) with
      | some pos =>
        let (i, hashes) := entries[pos]!
        seen.insert k (.dep (entries.set! pos (i, hashes.insert h)))
      | none =>
        seen.insert k (.dep (entries.push (idxs, ({} : Std.HashSet UInt64).insert h)))
    | _ =>
      seen.insert k (.dep #[(idxs, ({} : Std.HashSet UInt64).insert h)])

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
`ctx` (length `depth`, with hashes `hs`, innermost first) with the expectation
`ex`: fails where a binder's datum is not read, and otherwise returns
`(usedAbs, usedEx)`. -/
def readSrc (find : Find) (σ : Ix.Name → Nat) : Nat → List RCtxEntry → List UInt64 → Nat →
    Expect → Ix.Expr → SM (Nat × Bool)
  | 0, _, _, _, _, _ => throw ()
  | fuel + 1, ctx, hs, depth, ex, x => do
    let x := unmeta x
    match x with
    | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. =>
      let hx := x.getHash
      let e := ex.toOption
      let hit ← modifyGet fun s =>
        match findSeen s (hx, none) hs with
        | some idxs => (some (idxs, false), s)
        | none =>
          match findSeen s (hx, some e) hs with
          | some idxs => (some (idxs, true), s)
          | none => (none, s)
      match hit with
      | some (idxs, usedEx) => return (absMaskOf depth idxs, usedEx)
      | none =>
        let (u, usedEx) ← match x with
          | .app .. => do
            -- the whole spine at once: its head (a β-redex's λ-run takes the
            -- application's expectation), then each argument with the expectation its
            -- head gives it
            let h := (headArgs x).1
            let args := (spineArgs x #[]).reverse
            let (uh, eh) ← readSrc find σ fuel ctx hs depth ex h
            let mut u := uh
            for h' : i in [:args.size] do
              let a := args[i]
              let (aex, uArg) : Expect × Nat :=
                if readsExpectSrc a then argExpect find σ ctx h args i
                else (unknown "an argument that reads no expectation", 0)
              let (ua, _) ← readSrc find σ fuel ctx hs depth aex a
              u := u ||| uArg ||| ua
            pure (u, eh)
          | .lam .. | .forallE .. => do
            let pi := x matches .forallE ..
            let (tys, leaf) := srcRun pi readFuel x #[]
            let mut inner := ctx
            let mut ihs := hs
            let mut u := 0
            for h' : j in [:tys.size] do
              let ty := tys[j]
              let (ut, _) ← readSrc find σ fuel inner ihs (depth + j) asType ty
              u := u ||| ut
              inner := some (.raw ty, some (depth + j)) :: inner
              ihs := hash ty.getHash :: ihs
            let (ul, _) ← readSrc find σ fuel inner ihs (depth + tys.size) (if pi then asType else ex) leaf
            u := u ||| ul
            if pi then
              let (pw?, upw) := runCtxM (sortPwR find σ id sortFuel inner (.raw leaf))
              u := u ||| upw
              if pw?.isNone then throw ()
            else if ex.toOption.isNone then throw ()
            pure (u, !pi)
          | .letE _ ty val body _ _ => do
            let (ut, _) ← readSrc find σ fuel ctx hs depth asType ty
            let (pw?, upw) := runCtxM (sortPwR find σ id sortFuel ctx (.raw ty))
            let vex : Expect := match pw? with
              | some p => .ok p
              | none => unknown "a let's value"
            let (uv, _) ← readSrc find σ fuel ctx hs depth vex val
            let (ub, eb) ← readSrc find σ fuel (some (.raw ty, some depth) :: ctx)
              (hash ty.getHash :: hs) (depth + 1) ex body
            pure (ut ||| upw ||| uv ||| ub, eb)
          | .proj _ _ xv _ => do
            let (uv, _) ← readSrc find σ fuel ctx hs depth (unknown "a projection's subject") xv
            pure (uv, false)
          | _ => pure (0, false)
        let idxs := relIndicesOf depth u
        let k := (hx, if usedEx then some e else none)
        modify fun s => insertSeen s k idxs hs
        return (u, usedEx)
    | _ => return (0, false)

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
    | .defnInfo d => #[⟨own, d.cnst.type, asType⟩, ⟨own, d.value, typeExpect find own d.cnst.type⟩]
    | .thmInfo t => #[⟨own, t.cnst.type, asType⟩, ⟨own, t.value, .ok (PropWhen.ifAllZero [])⟩]
    | .opaqueInfo o => #[⟨own, o.cnst.type, asType⟩, ⟨own, o.value, typeExpect find own o.cnst.type⟩]
    | .recInfo v => recRoots find v
    | ci => #[⟨own, ci.getCnst.type, asType⟩]
  roots.all fun r =>
    match ((readSrc find r.σ.pos readFuel [] [] 0 r.ex r.x).run {}) with
    | .ok _ => true
    | .error _ => false

end Ix.Compile.BinderRead

end
