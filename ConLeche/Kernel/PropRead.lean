module

public import ConLeche.Kernel.Env
public import ConLeche.Kernel.ExprOps

@[expose] public section

/-!
# Fast prop-ness off the head symbol (task #168)

Two pure readers that answer "is this type a proposition?" / "is this
term a proof?" from the **head symbol, the arity and the validated
`pw` annotations** — no inference, no reduction, no memo.

Prop-ness is invariant under application: `zeronessOf (imax u v) =
zeronessOf v`, so the zero-ness of the sort of the type of `c a⃗` is
that of `c`'s *stored* type at every arity, over-application included.
The datum a head-symbol reader needs is therefore **one `PropWhen` per
constant** — the zero-ness of the sort of its type, read off the
stored (annotated, validated) type and instantiated at the use's
levels by `substPW`.

Both readers are three-valued (`some pw` = the datum, `none` = unknown,
fall back to inference).  The kernel's verdict on a datum is exactly the
slow path's `Level.isEquiv u .zero`: `pw == (.ifAllZero [])` ⟺ the
sort is zero at every valuation.

Trust: the readers consume annotations the checker validates
(`(forall-cod)`, `(lam-cod-leaf)`/`(lam-cod-chain)` in `inferBody`;
the stored types were validated at install), so they may only be
*consulted* at the verified modes (`mode.verifiedChecks`) — the trusted core
writes no data and the parser default stays.  The **"definitely not a
proof" arm** (`notProofFast`) needs no model theorem: refusing the
proof-irrelevance shortcut is always sound; its obligation is
kernel-level agreement with the slow path, which the landing census
records (DESIGN.md, task #168).  The **"definitely a proof" arm** is a
squash-regime licence (`prf_of_isProofFast`, `ConLeche/Model/Rules/DefEqSoundKit.lean`).
-/

namespace ConLeche

namespace Expr

/-- The residual after peeling `k` *syntactic* ∀ binders whose data
are all `.never` (no substitution — the residual may mention the
peeled binders; the readers only look at its head shape).  The
`.never` requirement costs no coverage on validated types — the
binders of a type former `∀ p⃗, Sort u` all carry the datum of a
`succ` codomain sort — and it is what licenses the "yes" arm's
telescope walk without a certificate (`neverChain_of_peel`,
`ConLeche/Model/Rules/DefEqSoundKit.lean`: every slot is in the graph
regime, `io_domain_transfer`). -/
def peelNeverPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ b m => if m.pw.isNever then peelNeverPis k b else none
  | _ + 1, _ => none

/-- The number of arguments of an application spine. -/
def numArgs : Expr → Nat
  | .app f _ => numArgs f + 1
  | _ => 0

end Expr

/-- The zero-ness datum of the sort of a *residual type*: a `Sort u`
residual says the type inhabits `Sort u`.  (A ∀ residual would mean
the applied head is a function, not a type — unreachable on
well-typed input, and unknown here.) -/
def residualPW : Option Expr → Option PropWhen
  | some (.sort u) => some (Level.zeronessOf u)
  | _ => none

/-- The datum of a type-former application's *head* at `n` arguments:
a constant head reads its stored type (level-instantiated), an fvar
head its declared type; the residual after `n` syntactic binders is
read by `residualPW`. -/
def headTypePW (find? : Name → Option ConstantInfo) : Expr → Nat →
    Option PropWhen
  | .const I us, n =>
    match find? I with
    | some ci =>
      if ci.isTowerEntry then none else
      let cv := ci.toConstantVal
      if us.length = cv.levelParams.length then
        (residualPW (cv.type.peelNeverPis n)).map
          (Level.substPW cv.levelParams us)
      else none
    | none => none
  | .fvar _ ty, n => residualPW (ty.peelNeverPis n)
  | _, _ => none

/-- The zero-ness datum of the sort of the *type* `T` ("is `T` a
proposition?"), read off `T`'s head symbol and the annotations: a ∀
carries it on its binder (`(forall-cod)`); a sort's sort is never zero;
a constant- or fvar-headed type-former application reads the head's
stored/declared type, peels the arity syntactically and reads the
residual, level-instantiated for a constant.  `none` = unknown. -/
def typeSortPW (find? : Name → Option ConstantInfo) (T : Expr) :
    Option PropWhen :=
  match T with
  | .forallE _ _ m => some m.pw
  | .sort _ => some .never
  | T => headTypePW find? T.getAppFn T.numArgs

/-- The datum of a term's *head* (any arity): a constant head answers
from its stored type (prop-ness is invariant under application), an
fvar head from its declared type; sorts, ∀s and literals are never
proofs. -/
def headProofPW (find? : Name → Option ConstantInfo) : Expr →
    Option PropWhen
  | .const c us =>
    match find? c with
    | some ci =>
      if ci.isTowerEntry then none else
      let cv := ci.toConstantVal
      if us.length = cv.levelParams.length then
        (typeSortPW find? cv.type).map (Level.substPW cv.levelParams us)
      else none
    | none => none
  | .fvar _ ty => typeSortPW find? ty
  | .sort _ | .forallE .. | .lit _ => some .never
  | _ => none

/-- The zero-ness datum of the sort of the *type* of `a` ("is `a` a
proof?"), read off `a`'s head symbol at any arity: a constant or fvar
head answers from its stored/declared type; an unapplied λ answers from
its own datum (the zero-ness of the sort of the body's type,
`(lam-cod-leaf)`); sorts, ∀s and literals are never proofs.  `none` =
unknown. -/
def proofPW (find? : Name → Option ConstantInfo) (a : Expr) :
    Option PropWhen :=
  match a with
  | .lam _ _ m => some m.pw
  | a => headProofPW find? a.getAppFn

/-- Is the datum "always zero" — the sort is `Prop` at every
valuation? -/
@[inline] def PropWhen.isProp (pw : PropWhen) : Bool :=
  pw == (.ifAllZero [])

/-- **Definitely not a proof** (the no arm): the datum is known and is
not always-zero. -/
def notProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool :=
  match proofPW find? a with
  | some pw => !pw.isProp
  | none => false

/-- **Definitely a proof** (the yes arm): the datum is known and
always-zero. -/
def isProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool :=
  match proofPW find? a with
  | some pw => pw.isProp
  | none => false

end ConLeche
