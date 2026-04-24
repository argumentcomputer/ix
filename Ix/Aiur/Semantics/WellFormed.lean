module
public import Ix.Aiur.Compiler

/-!
`WellFormed` — the computable precondition for `compile_progress`.

Every conjunct is a `.ok` observation on `t`. No ghost predicates. A user
proves `WellFormed t` by literally running `mkDecls`, `checkAndSimplify`, the
monomorphization-termination check, and the constrained-call-graph acyclicity
check, and observing that all four succeed. `decide` discharges it for concrete
programs.
-/

public section
@[expose] section

namespace Aiur

open Source

/-- Monomorphization terminates: the worklist algorithm bottoms out. Formally,
there is no polymorphic recursion at a strictly larger type. Checking this is
part of the static check on `Concretize`.

`abbrev` so downstream proofs can `obtain` the witnesses without an explicit
`unfold`. -/
abbrev MonoTerminates (t : Source.Toplevel) : Prop :=
  ∃ typedDecls, t.checkAndSimplify = .ok typedDecls ∧
    ∃ concDecls, typedDecls.concretize = .ok concDecls

/-- Fully-monomorphic programs: every function and datatype has empty
`params`. Under this condition, concretize is a no-op on names (no mangling),
so source decls and concrete decls share a name space.

Decidable, dispatchable by `decide` for any concrete toplevel. Polymorphism
would require threading a `concretizeName` correspondence through every
per-pass preservation claim.

**No longer a `WellFormed` field** (2026-04-26): the source language forbids
polymorphic entry points by construction (`Source.Function.notPolyEntry`),
so `entry = true ⟹ params = []`. `compile_correct`'s preservation clause is
restricted to entries (`_hentry : f.entry = true`), making the per-entry
monomorphism derivable. `FullyMonomorphic` is retained as a helper definition
consumed by internal `_under_fullymono` lemmas; downstream theorems that
require global monomorphism now take it as a separate hypothesis. -/

def FullyMonomorphic (t : Source.Toplevel) : Prop :=
  (∀ f ∈ t.functions, f.params = []) ∧
  (∀ d ∈ t.dataTypes, d.params = [])

/-- A type is *first-order* iff it contains no `.function` constructor.
Excludes first-class function values. -/
inductive Typ.FirstOrder : Typ → Prop
  | unit : Typ.FirstOrder .unit
  | field : Typ.FirstOrder .field
  | mvar (n) : Typ.FirstOrder (.mvar n)
  | ref (g) : Typ.FirstOrder (.ref g)
  | tuple {ts} : (∀ t ∈ ts, Typ.FirstOrder t) → Typ.FirstOrder (.tuple ts)
  | array {t n} : Typ.FirstOrder t → Typ.FirstOrder (.array t n)
  | pointer {t} : Typ.FirstOrder t → Typ.FirstOrder (.pointer t)
  | app {g args} : (∀ t ∈ args, Typ.FirstOrder t) → Typ.FirstOrder (.app g args)

/-- **Typed-side first-order returns.** Every typed function's return
type is first-order. Parallel to `Typed.Decls.NoDirectDatatypeCycles`:
quantifies directly over the post-`checkAndSimplify` decls (the shape
relevant to compilation), avoiding the alias-expansion mismatch between
source `t.functions` and typed decls. -/

def Typed.Decls.FirstOrderReturn (tds : Typed.Decls) : Prop :=
  ∀ g f, tds.getByKey g = some (.function f) → Typ.FirstOrder f.output

/-- First-order returns: for every `typedDecls` produced by
`t.checkAndSimplify`, every typed function's return type is first-order.
Under this condition, return values are `Value.FnFree`, so `flattenValue`
is funcIdx-independent on returns — resolves the remaining
pre-dedup/post-dedup `funcIdx` transport residual in the top-level
preservation composition.

Stating this on the post-`checkAndSimplify` shape (parallel to
`DirectDatatypeDAGAcyclic`) eliminates the alias-FO prerequisite at
`mkDecls` level: FO is semantically stated where it matters (compiled
program), and the bridge into concretize becomes a single hypothesis
application. -/

def FirstOrderReturn (t : Source.Toplevel) : Prop :=
  ∀ typedDecls, t.checkAndSimplify = .ok typedDecls →
    Typed.Decls.FirstOrderReturn typedDecls

/-- Predicate: constructor argtype does not mention a type-parameter bare at
top level. Prevents `data T<α> = Mk(α)`. Params may still appear inside
`.pointer`/`.array`/`.tuple`/`.function` (indirect positions — those don't
create datatype-DAG edges).

Required for `concretize_preserves_direct_dag`: without this, specialization
`T<Int>` creates `.ref Int` ctor argtype with no source bound for
`rank Int < rank T`. Semantically: users write `.pointer α` for recursive
parameters. -/

def Typed.Typ.ParamSafe (params : List String) : Typ → Prop
  | .ref g' => toString g' ∉ params
  | .app g' _ => toString g' ∉ params
  | _ => True

/-- Every `.ref g'` / `.app g' _` appearing in the non-`.pointer`/`.function`
spine of a typed type has `rank g' < bd`. `.pointer`/`.function` break the
spine (they do not create direct datatype-DAG edges — `sizeBound` returns 1
immediately on both). -/
inductive Typed.Typ.SpineRefsBelow (rank : Global → Nat) (bd : Nat) : Typ → Prop
  | unit : SpineRefsBelow rank bd .unit
  | field : SpineRefsBelow rank bd .field
  | pointer (t) : SpineRefsBelow rank bd (.pointer t)
  | function (ins out) : SpineRefsBelow rank bd (.function ins out)
  | tuple {ts} (h : ∀ t ∈ ts.toList, SpineRefsBelow rank bd t) :
      SpineRefsBelow rank bd (.tuple ts)
  | array {t n} (h : SpineRefsBelow rank bd t) : SpineRefsBelow rank bd (.array t n)
  | ref {g} (h : rank g < bd) : SpineRefsBelow rank bd (.ref g)
  | app {g args} (h : rank g < bd) : SpineRefsBelow rank bd (.app g args)
  | mvar (n) : SpineRefsBelow rank bd (.mvar n)

/-- **Direct datatype-DAG acyclicity on typed decls.** Typed datatype
reference graph is a DAG. The rank witness bounds every `.ref`-edge and every
`.app`-edge anywhere in a constructor's argTypes non-`.pointer`/`.function`
spine (nested refs inside `.tuple`/`.array` also bounded — they are direct
DAG edges for `sizeBound`), plus `Typ.ParamSafe` prevents bare-param
top-level ctor argtypes.

Consumed by `concretize_preserves_direct_dag` to lift rank from source to
cd. Moved here from `Proofs/ConcretizeSound.lean` so `WellFormed` can state
the acyclicity obligation on the post-`checkAndSimplify` shape (where ctor
argTypes have been alias-expanded by `mkDecls`). -/

def Typed.Decls.NoDirectDatatypeCycles (tds : Typed.Decls) : Prop :=
  ∃ rank : Global → Nat,
    ∀ g dt, tds.getByKey g = some (.dataType dt) →
      ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
        Typed.Typ.SpineRefsBelow rank (rank g) t ∧
        Typed.Typ.ParamSafe dt.params t

/-- **Direct datatype-DAG acyclicity.** The user-facing obligation: for every
`typedDecls` produced by `t.checkAndSimplify`, the typed decls' datatype
reference graph is acyclic (i.e. admits a rank witness).

Stating this on the post-`checkAndSimplify` shape — rather than on the raw
source `t.dataTypes` array — avoids the alias-expansion mismatch: `mkDecls`
calls `expandTypeM` on every ctor argType, which can turn a source `.ref
alias` into an arbitrary typ. The acyclicity property is about the edges
that actually appear in the compiled datatype graph; those edges live in
the typed decls.

Required by `compile_progress` (via `concretize_produces_sizeBoundOk`): even
under `FullyMonomorphic`, `data T = ctor T` is a direct cycle that would make
`typSizeBound` diverge. This conjunct rules it out. -/

def DirectDatatypeDAGAcyclic (t : Source.Toplevel) : Prop :=
  ∀ typedDecls, t.checkAndSimplify = .ok typedDecls →
    Typed.Decls.NoDirectDatatypeCycles typedDecls

/-- **Per-drain uniqueness of `concretizeName` preimages.** Under `WellFormed`, the
source toplevel is restricted so that `concretizeName` is injective on the set of
`(g, args)` pairs that actually appear during `concretize`'s drain. Required because
`concretizeName` is NOT globally injective (string concatenation can collide), and
without this restriction the rank witness `rank_cd g := rank_src (templateOf g)` in
`concretize_preserves_direct_dag` is ambiguous.

Decidable at concrete call sites via `decide`. -/

def Typed.Decls.ConcretizeUniqueNames (tds : Typed.Decls) : Prop :=
  ∀ {cd : Concrete.Decls}, tds.concretize = .ok cd →
    ∀ (g₁ g₂ : Global) (args₁ args₂ : Array Typ),
      concretizeName g₁ args₁ = concretizeName g₂ args₂ →
      (∃ d, cd.getByKey (concretizeName g₁ args₁) = some d) →
      g₁ = g₂ ∧ args₁ = args₂

/-- Lifted to source toplevel via the `checkAndSimplify_ok` witness. -/

def NoNameCollisions (t : Source.Toplevel) : Prop :=
  ∀ typedDecls, t.checkAndSimplify = .ok typedDecls →
    Typed.Decls.ConcretizeUniqueNames typedDecls

/-- Every `.ref g` **term** subterm of a `Typed.Term` has `g` keyed to
a `.dataType _` or `.constructor _ _` in `tds` — NOT a function. Parallels
`Concrete.Term.RefsDt` on the typed IR. Required to rule out the
`.ref g ↦ .fn g` counterexample at the typed level; preserved to
`Concrete.Term.RefsDt` by `concretize_preserves_TermRefsDt`. -/
inductive Typed.Term.RefsDt (tds : Typed.Decls) : Typed.Term → Prop
  | unit  {typ e} : RefsDt tds (.unit typ e)
  | var   {typ e l} : RefsDt tds (.var typ e l)
  | ref   {typ e g tArgs}
      (hdt : (∃ dt, tds.getByKey g = some (.dataType dt)) ∨
             (∃ dt c, tds.getByKey g = some (.constructor dt c))) :
      RefsDt tds (.ref typ e g tArgs)
  | field {typ e g} : RefsDt tds (.field typ e g)
  | tuple {typ e ts} (h : ∀ sub ∈ ts, RefsDt tds sub) :
      RefsDt tds (.tuple typ e ts)
  | array {typ e ts} (h : ∀ sub ∈ ts, RefsDt tds sub) :
      RefsDt tds (.array typ e ts)
  | ret   {typ e sub} (h : RefsDt tds sub) : RefsDt tds (.ret typ e sub)
  | «let» {typ e pat v b}
      (hv : RefsDt tds v) (hb : RefsDt tds b) : RefsDt tds (.let typ e pat v b)
  | «match» {typ e scrut cases}
      (hscrut : RefsDt tds scrut)
      (hcases : ∀ pc ∈ cases, RefsDt tds pc.2) :
      RefsDt tds (.match typ e scrut cases)
  | app {typ e g tArgs args u} (hargs : ∀ a ∈ args, RefsDt tds a) :
      RefsDt tds (.app typ e g tArgs args u)
  | add {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) :
      RefsDt tds (.add typ e a b)
  | sub {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) :
      RefsDt tds (.sub typ e a b)
  | mul {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) :
      RefsDt tds (.mul typ e a b)
  | eqZero {typ e a} (ha : RefsDt tds a) : RefsDt tds (.eqZero typ e a)
  | proj {typ e a n} (ha : RefsDt tds a) : RefsDt tds (.proj typ e a n)
  | get {typ e a n} (ha : RefsDt tds a) : RefsDt tds (.get typ e a n)
  | slice {typ e a i j} (ha : RefsDt tds a) : RefsDt tds (.slice typ e a i j)
  | «set» {typ e a n v} (ha : RefsDt tds a) (hv : RefsDt tds v) :
      RefsDt tds (.set typ e a n v)
  | store {typ e a} (ha : RefsDt tds a) : RefsDt tds (.store typ e a)
  | load {typ e a} (ha : RefsDt tds a) : RefsDt tds (.load typ e a)
  | ptrVal {typ e a} (ha : RefsDt tds a) : RefsDt tds (.ptrVal typ e a)
  | assertEq {typ e a b r} (ha : RefsDt tds a) (hb : RefsDt tds b) (hr : RefsDt tds r) :
      RefsDt tds (.assertEq typ e a b r)
  | ioGetInfo {typ e k} (hk : RefsDt tds k) : RefsDt tds (.ioGetInfo typ e k)
  | ioSetInfo {typ e k i l r}
      (hk : RefsDt tds k) (hi : RefsDt tds i) (hl : RefsDt tds l) (hr : RefsDt tds r) :
      RefsDt tds (.ioSetInfo typ e k i l r)
  | ioRead {typ e i n} (hi : RefsDt tds i) : RefsDt tds (.ioRead typ e i n)
  | ioWrite {typ e d r} (hd : RefsDt tds d) (hr : RefsDt tds r) :
      RefsDt tds (.ioWrite typ e d r)
  | u8BitDecomposition {typ e a} (ha : RefsDt tds a) : RefsDt tds (.u8BitDecomposition typ e a)
  | u8ShiftLeft  {typ e a} (ha : RefsDt tds a) : RefsDt tds (.u8ShiftLeft typ e a)
  | u8ShiftRight {typ e a} (ha : RefsDt tds a) : RefsDt tds (.u8ShiftRight typ e a)
  | u8Xor {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) : RefsDt tds (.u8Xor typ e a b)
  | u8Add {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) : RefsDt tds (.u8Add typ e a b)
  | u8Sub {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) : RefsDt tds (.u8Sub typ e a b)
  | u8And {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) : RefsDt tds (.u8And typ e a b)
  | u8Or  {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) : RefsDt tds (.u8Or typ e a b)
  | u8LessThan  {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) :
      RefsDt tds (.u8LessThan typ e a b)
  | u32LessThan {typ e a b} (ha : RefsDt tds a) (hb : RefsDt tds b) :
      RefsDt tds (.u32LessThan typ e a b)
  | debug {typ e label t r}
      (ht : ∀ tval, t = some tval → RefsDt tds tval) (hr : RefsDt tds r) :
      RefsDt tds (.debug typ e label t r)

/-- Every function body in `tds` syntactically respects typed-side `RefsDt`. -/
def Typed.Decls.TermRefsDt (tds : Typed.Decls) : Prop :=
  ∀ g f, tds.getByKey g = some (.function f) → Typed.Term.RefsDt tds f.body

/-- **Source-side term-ref well-formedness**: every `Typed.Term.ref g`
subterm has `g` resolving to a `.dataType _` or `.constructor _ _` in the
post-`checkAndSimplify` typed decls — NOT a function key.

Rules out the `.ref g ↦ .fn g` counterexample for the concrete
`runFunction_preserves_FnFree` (sig-fix 2026-04-24,
`FnFreeSigFixScratch`). Paralleling `FirstOrderReturn`, quantified over
the post-`checkAndSimplify` shape so the bridge into concretize collapses
to a single hypothesis application. -/

def NoTermRefsToFunctions (t : Source.Toplevel) : Prop :=
  ∀ typedDecls, t.checkAndSimplify = .ok typedDecls →
    Typed.Decls.TermRefsDt typedDecls

/-- Seven-conjunct well-formedness predicate. Every conjunct is a computable
`.ok` observation (or a decidable structural property for `FirstOrderReturn`
/ `DirectDatatypeDAGAcyclic` / `NoNameCollisions` / `NoTermRefsToFunctions`).

Note (2026-04-26): the previous `fullyMonomorphic : FullyMonomorphic t` field
has been removed — it rejected polymorphic source (e.g., IxVM's `List<T>`).
The source language forbids polymorphic entry points by construction
(`Source.Function.notPolyEntry`), so the per-entry monomorphism that
`compile_correct`'s preservation clause needs is derivable from
`_hentry : f.entry = true`, not from a global obligation. -/
structure WellFormed (t : Source.Toplevel) : Prop where
  mkDecls_ok : ∃ decls, t.mkDecls = .ok decls
  checkAndSimplify_ok : ∃ typedDecls, t.checkAndSimplify = .ok typedDecls
  monoTerminates : MonoTerminates t
  firstOrderReturn : FirstOrderReturn t
  directDatatypeDAGAcyclic : DirectDatatypeDAGAcyclic t
  noNameCollisions : NoNameCollisions t
  noTermRefsToFunctions : NoTermRefsToFunctions t

-- TODO: a `WellFormed.empty` sanity lemma would be nice, but
-- `IndexMap`'s `default` doesn't unfold cleanly inside the goal —
-- `decide` would require massive `Decidable` instances that aren't
-- yet derived. Defer until the proof infrastructure is more mature.

end Aiur

end -- @[expose] section
end -- public section
