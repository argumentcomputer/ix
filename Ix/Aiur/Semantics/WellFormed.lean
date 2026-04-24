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
  -- Sig amendment 2026-05-04: `.ref g tArgs` only emerges from `refLookup`'s
  -- `.constructor` arm (Check.lean:421), so the dt case is structurally
  -- unreachable. Tightening the predicate to require `.constructor` lets
  -- `concretize_preserves_TermRefsDt`'s bridge dispatch a smaller arm set.
  --
  -- Sig amendment 2026-05-04 (RefsDt-defect): also require
  -- `dt.params.isEmpty ∨ ¬ tArgs.isEmpty`. Source of truth: `refLookup`
  -- (Check.lean:421-441) emits `.ref g #[]` only when `dt.params.isEmpty`
  -- (mono ctor at line 435-436) and `.ref g mvars` with `mvars.size =
  -- dt.params.length > 0` for poly ctor (line 437-439). So a `.ref g tArgs`
  -- node with `tArgs.isEmpty` AND `dt.params.length > 0` cannot arise from
  -- `checkAndSimplify` outputs. The added disjunct rules out that
  -- structurally-impossible shape and unblocks the `BLOCKED-RefsDt-Bridge-A-ctor`
  -- arm of `concretize_preserves_TermRefsDt`, which needs `dt.params = []`
  -- to apply `concretizeBuild_preserves_ctor_kind_fwd` (CtorKind.lean:422).
  | ref   {typ e g tArgs}
      (hdt : ∃ dt c, tds.getByKey g = some (.constructor dt c) ∧
        (dt.params.isEmpty ∨ ¬ tArgs.isEmpty)) :
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

/-- **Typed-side carrier-type non-function**: every `.load` term carrier type
is `Typ.FirstOrder` (no `.function` constructor anywhere in its spine), and
recurses through every typed term subterm.

Mirrors `Concrete.Term.TypesNotFunction` at the typed level. The relevant
constraint at the typed `.load` is that the loaded value's type is free of
`.function` leaves; everything else just propagates through subterms. -/
inductive Typed.Term.TypesNotFunction : Typed.Term → Prop
  | unit  {typ e} : TypesNotFunction (.unit typ e)
  | var   {typ e l} : TypesNotFunction (.var typ e l)
  | ref   {typ e g tArgs} : TypesNotFunction (.ref typ e g tArgs)
  | field {typ e g} : TypesNotFunction (.field typ e g)
  | tuple {typ e ts} (h : ∀ sub ∈ ts, TypesNotFunction sub) :
      TypesNotFunction (.tuple typ e ts)
  | array {typ e ts} (h : ∀ sub ∈ ts, TypesNotFunction sub) :
      TypesNotFunction (.array typ e ts)
  | ret   {typ e sub} (h : TypesNotFunction sub) : TypesNotFunction (.ret typ e sub)
  | «let» {typ e pat v b}
      (hv : TypesNotFunction v) (hb : TypesNotFunction b) :
      TypesNotFunction (.let typ e pat v b)
  | «match» {typ e scrut cases}
      (hscrut : TypesNotFunction scrut)
      (hcases : ∀ pc ∈ cases, TypesNotFunction pc.2)
      (hcasesTyp : ∀ pc ∈ cases, pc.2.typ = typ) :
      TypesNotFunction (.match typ e scrut cases)
  | app {typ e g tArgs args u} (hargs : ∀ a ∈ args, TypesNotFunction a) :
      TypesNotFunction (.app typ e g tArgs args u)
  | add {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.add typ e a b)
  | sub {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.sub typ e a b)
  | mul {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.mul typ e a b)
  | eqZero {typ e a} (ha : TypesNotFunction a) : TypesNotFunction (.eqZero typ e a)
  | proj {typ e a n} (ha : TypesNotFunction a) : TypesNotFunction (.proj typ e a n)
  | get {typ e a n} (ha : TypesNotFunction a) : TypesNotFunction (.get typ e a n)
  | slice {typ e a i j} (ha : TypesNotFunction a) :
      TypesNotFunction (.slice typ e a i j)
  | «set» {typ e a n v} (ha : TypesNotFunction a) (hv : TypesNotFunction v) :
      TypesNotFunction (.set typ e a n v)
  | store {typ e a} (ha : TypesNotFunction a) : TypesNotFunction (.store typ e a)
  | load {typ e a}
      (htyp : Typ.FirstOrder typ)
      (haty : Typ.FirstOrder a.typ)
      (ha : TypesNotFunction a) :
      TypesNotFunction (.load typ e a)
  | ptrVal {typ e a} (ha : TypesNotFunction a) : TypesNotFunction (.ptrVal typ e a)
  | assertEq {typ e a b r}
      (ha : TypesNotFunction a) (hb : TypesNotFunction b) (hr : TypesNotFunction r) :
      TypesNotFunction (.assertEq typ e a b r)
  | ioGetInfo {typ e k} (hk : TypesNotFunction k) : TypesNotFunction (.ioGetInfo typ e k)
  | ioSetInfo {typ e k i l r}
      (hk : TypesNotFunction k) (hi : TypesNotFunction i)
      (hl : TypesNotFunction l) (hr : TypesNotFunction r) :
      TypesNotFunction (.ioSetInfo typ e k i l r)
  | ioRead {typ e i n} (hi : TypesNotFunction i) : TypesNotFunction (.ioRead typ e i n)
  | ioWrite {typ e d r} (hd : TypesNotFunction d) (hr : TypesNotFunction r) :
      TypesNotFunction (.ioWrite typ e d r)
  | u8BitDecomposition {typ e a} (ha : TypesNotFunction a) :
      TypesNotFunction (.u8BitDecomposition typ e a)
  | u8ShiftLeft  {typ e a} (ha : TypesNotFunction a) :
      TypesNotFunction (.u8ShiftLeft typ e a)
  | u8ShiftRight {typ e a} (ha : TypesNotFunction a) :
      TypesNotFunction (.u8ShiftRight typ e a)
  | u8Xor {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.u8Xor typ e a b)
  | u8Add {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.u8Add typ e a b)
  | u8Sub {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.u8Sub typ e a b)
  | u8And {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.u8And typ e a b)
  | u8Or  {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.u8Or typ e a b)
  | u8LessThan  {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.u8LessThan typ e a b)
  | u32LessThan {typ e a b} (ha : TypesNotFunction a) (hb : TypesNotFunction b) :
      TypesNotFunction (.u32LessThan typ e a b)
  | debug {typ e label t r}
      (ht : ∀ tval, t = some tval → TypesNotFunction tval) (hr : TypesNotFunction r) :
      TypesNotFunction (.debug typ e label t r)

/-- Every typed function body in `tds` syntactically respects
`Typed.Term.TypesNotFunction`. Mirrors `Concrete.Decls.TypesNotFunction`. -/
def Typed.Decls.TypesNotFunction (tds : Typed.Decls) : Prop :=
  ∀ g f, tds.getByKey g = some (.function f) → Typed.Term.TypesNotFunction f.body

/-- **Source-side carrier-type non-function**: every `.load` carrier type in
the post-`checkAndSimplify` typed decls is `Typ.FirstOrder`. Required for
`compile_correct`'s per-entry `FnFree` discharge: `concretize` lowers typed
`.load` to concrete `.letLoad` / `.load` whose carrier-type freeness comes
from the typed origin via `typToConcrete`. -/

def NoTypesAreFunctions (t : Source.Toplevel) : Prop :=
  ∀ typedDecls, t.checkAndSimplify = .ok typedDecls →
    Typed.Decls.TypesNotFunction typedDecls

/-- Every `Typ.app` and `Typed.Term.{ref,app}` `tArgs` appearing anywhere
in `tds` (function bodies, dt argTypes, type annotations) has all FO
type-args. Required by `concretize_PendingArgsFO_bridge` to discharge the
substitution-FO side condition of the FO drain leaf.

For polymorphic source, this asserts that every type-application carries
FO type arguments — true for source whose monomorphic instantiations are
all FO (the case for IxVM's `List<G>`, `Tree<G>` etc.). -/
inductive Typed.Typ.AppRefTArgsFO : Typ → Prop
  | unit  : AppRefTArgsFO .unit
  | field : AppRefTArgsFO .field
  | mvar (n) : AppRefTArgsFO (.mvar n)
  | ref (g) : AppRefTArgsFO (.ref g)
  | tuple {ts} (h : ∀ t ∈ ts, AppRefTArgsFO t) : AppRefTArgsFO (.tuple ts)
  | array {t n} (h : AppRefTArgsFO t) : AppRefTArgsFO (.array t n)
  | pointer {t} (h : AppRefTArgsFO t) : AppRefTArgsFO (.pointer t)
  | app {g args}
      (hargsFO : ∀ t ∈ args, Typ.FirstOrder t)
      (hargsRec : ∀ t ∈ args, AppRefTArgsFO t) :
      AppRefTArgsFO (.app g args)
  | function {ins out}
      (h_ins : ∀ t ∈ ins, AppRefTArgsFO t)
      (h_out : AppRefTArgsFO out) :
      AppRefTArgsFO (.function ins out)

/-- Term-level analogue: every `.app/.ref tArgs` in a typed term has FO
type-args (and structural recursion through subterms). -/
inductive Typed.Term.AppRefTArgsFO : Typed.Term → Prop
  | unit  {typ e} (htyp : Typ.AppRefTArgsFO typ) :
      AppRefTArgsFO (.unit typ e)
  | var   {typ e l} (htyp : Typ.AppRefTArgsFO typ) :
      AppRefTArgsFO (.var typ e l)
  | ref   {typ e g tArgs}
      (htyp : Typ.AppRefTArgsFO typ)
      (hArgsFO : ∀ t ∈ tArgs, Typ.FirstOrder t)
      (hArgsRec : ∀ t ∈ tArgs, Typ.AppRefTArgsFO t) :
      AppRefTArgsFO (.ref typ e g tArgs)
  | field {typ e g} (htyp : Typ.AppRefTArgsFO typ) :
      AppRefTArgsFO (.field typ e g)
  | tuple {typ e ts}
      (htyp : Typ.AppRefTArgsFO typ)
      (h : ∀ sub ∈ ts, AppRefTArgsFO sub) :
      AppRefTArgsFO (.tuple typ e ts)
  | array {typ e ts}
      (htyp : Typ.AppRefTArgsFO typ)
      (h : ∀ sub ∈ ts, AppRefTArgsFO sub) :
      AppRefTArgsFO (.array typ e ts)
  | ret {typ e sub}
      (htyp : Typ.AppRefTArgsFO typ)
      (h : AppRefTArgsFO sub) :
      AppRefTArgsFO (.ret typ e sub)
  | «let» {typ e pat v b}
      (htyp : Typ.AppRefTArgsFO typ)
      (hv : AppRefTArgsFO v) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.let typ e pat v b)
  | «match» {typ e scrut cases}
      (htyp : Typ.AppRefTArgsFO typ)
      (hscrut : AppRefTArgsFO scrut)
      (hcases : ∀ pc ∈ cases, AppRefTArgsFO pc.2) :
      AppRefTArgsFO (.match typ e scrut cases)
  | app {typ e g tArgs args u}
      (htyp : Typ.AppRefTArgsFO typ)
      (hArgsFO : ∀ t ∈ tArgs, Typ.FirstOrder t)
      (hArgsRec : ∀ t ∈ tArgs, Typ.AppRefTArgsFO t)
      (hargs : ∀ a ∈ args, AppRefTArgsFO a) :
      AppRefTArgsFO (.app typ e g tArgs args u)
  | add {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.add typ e a b)
  | sub {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.sub typ e a b)
  | mul {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.mul typ e a b)
  | eqZero {typ e a} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.eqZero typ e a)
  | proj {typ e a n} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.proj typ e a n)
  | get {typ e a n} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.get typ e a n)
  | slice {typ e a i j} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.slice typ e a i j)
  | «set» {typ e a n v} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hv : AppRefTArgsFO v) :
      AppRefTArgsFO (.set typ e a n v)
  | store {typ e a} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.store typ e a)
  | load {typ e a} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.load typ e a)
  | ptrVal {typ e a} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.ptrVal typ e a)
  | assertEq {typ e a b r} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) (hr : AppRefTArgsFO r) :
      AppRefTArgsFO (.assertEq typ e a b r)
  | ioGetInfo {typ e k} (htyp : Typ.AppRefTArgsFO typ)
      (hk : AppRefTArgsFO k) : AppRefTArgsFO (.ioGetInfo typ e k)
  | ioSetInfo {typ e k i l r} (htyp : Typ.AppRefTArgsFO typ)
      (hk : AppRefTArgsFO k) (hi : AppRefTArgsFO i)
      (hl : AppRefTArgsFO l) (hr : AppRefTArgsFO r) :
      AppRefTArgsFO (.ioSetInfo typ e k i l r)
  | ioRead {typ e i n} (htyp : Typ.AppRefTArgsFO typ)
      (hi : AppRefTArgsFO i) : AppRefTArgsFO (.ioRead typ e i n)
  | ioWrite {typ e d r} (htyp : Typ.AppRefTArgsFO typ)
      (hd : AppRefTArgsFO d) (hr : AppRefTArgsFO r) :
      AppRefTArgsFO (.ioWrite typ e d r)
  | u8BitDecomposition {typ e a} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.u8BitDecomposition typ e a)
  | u8ShiftLeft {typ e a} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.u8ShiftLeft typ e a)
  | u8ShiftRight {typ e a} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) : AppRefTArgsFO (.u8ShiftRight typ e a)
  | u8Xor {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.u8Xor typ e a b)
  | u8Add {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.u8Add typ e a b)
  | u8Sub {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.u8Sub typ e a b)
  | u8And {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.u8And typ e a b)
  | u8Or {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.u8Or typ e a b)
  | u8LessThan {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.u8LessThan typ e a b)
  | u32LessThan {typ e a b} (htyp : Typ.AppRefTArgsFO typ)
      (ha : AppRefTArgsFO a) (hb : AppRefTArgsFO b) :
      AppRefTArgsFO (.u32LessThan typ e a b)
  | debug {typ e label t r} (htyp : Typ.AppRefTArgsFO typ)
      (ht : ∀ tval, t = some tval → AppRefTArgsFO tval)
      (hr : AppRefTArgsFO r) :
      AppRefTArgsFO (.debug typ e label t r)

/-- Decls-level: every function body satisfies `Typed.Term.AppRefTArgsFO`,
every dt argType satisfies `Typed.Typ.AppRefTArgsFO`, and every typed
function input/output type does. -/
def Typed.Decls.AppRefTArgsFO (tds : Typed.Decls) : Prop :=
  (∀ g f, tds.getByKey g = some (.function f) →
    (∀ t ∈ f.inputs.map Prod.snd, Typed.Typ.AppRefTArgsFO t) ∧
    Typed.Typ.AppRefTArgsFO f.output ∧
    Typed.Term.AppRefTArgsFO f.body) ∧
  (∀ g dt, tds.getByKey g = some (.dataType dt) →
    ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes, Typed.Typ.AppRefTArgsFO t) ∧
  (∀ g dt c, tds.getByKey g = some (.constructor dt c) →
    ∀ t ∈ c.argTypes, Typed.Typ.AppRefTArgsFO t)

/-- Source-side obligation: every `tArgs` in source decls is FO at the
typed level. -/
def NoPolyAppRefTArgs (t : Source.Toplevel) : Prop :=
  ∀ typedDecls, t.checkAndSimplify = .ok typedDecls →
    Typed.Decls.AppRefTArgsFO typedDecls

/-! ### `Typed.Typ.AppRefToDt` / `Typed.Term.AppRefToDt`.

Typed-side analog of `SrcTypRefsAreDtKeys`: every `.app g args` and `.ref g`
in a typed type/term has `g` resolving to a `.dataType` in `tds`, modulo
type-parameter `.ref α` (`α ∈ params`) which is treated as a leaf. Lifted
to the typed side via the existing `checkAndSimplify` chain.

The `params` argument tracks the local type-parameter context. Existing
call sites that operated under a monomorphic context pass `params = []`,
in which case the `.refTypeParam` arm is unreachable.

Moved upstream from `Ix/Aiur/Proofs/ConcretizeSound/RefClosed.lean`
(2026-05-04) so that `WellFormed` can host a body-position obligation
parallel to `noPolyAppRefTArgs`. Downstream consumers in
`ConcretizeSound/RefClosed.lean` reference these via fully qualified
names. -/
inductive Typed.Typ.AppRefToDt (tds : Typed.Decls) (params : List String) : Typ → Prop
  | unit : AppRefToDt tds params .unit
  | field : AppRefToDt tds params .field
  | mvar (n) : AppRefToDt tds params (.mvar n)
  | ref {g} (hdt : ∃ dt, tds.getByKey g = some (.dataType dt) ∧ dt.params = []) :
      AppRefToDt tds params (.ref g)
  | refTypeParam {g} (hin : ∃ p ∈ params, g = Global.init p) :
      AppRefToDt tds params (.ref g)
  | app {g args}
      (hdt : ∃ dt, tds.getByKey g = some (.dataType dt))
      (hargs : ∀ t ∈ args, AppRefToDt tds params t) :
      AppRefToDt tds params (.app g args)
  | tuple {ts} (h : ∀ t ∈ ts, AppRefToDt tds params t) : AppRefToDt tds params (.tuple ts)
  | array {t n} (h : AppRefToDt tds params t) : AppRefToDt tds params (.array t n)
  | pointer {t} (h : AppRefToDt tds params t) : AppRefToDt tds params (.pointer t)
  | function {ins out}
      (h_ins : ∀ t ∈ ins, AppRefToDt tds params t)
      (h_out : AppRefToDt tds params out) :
      AppRefToDt tds params (.function ins out)

/-- Term-level analogue of `Typed.Typ.AppRefToDt`. Every `Typ` annotation
inside `term` is `AppRefToDt tds params`-safe, and every type-argument array
on `.ref`/`.app` sites is element-wise `AppRefToDt tds params`-safe. Mirrors
`Typed.Term.AppRefTArgsFO` with `AppRefToDt` in place of `AppRefTArgsFO`. -/
inductive Typed.Term.AppRefToDt
    (tds : Typed.Decls) (params : List String) : Typed.Term → Prop
  | unit  {typ e} (htyp : Typ.AppRefToDt tds params typ) :
      AppRefToDt tds params (.unit typ e)
  | var   {typ e l} (htyp : Typ.AppRefToDt tds params typ) :
      AppRefToDt tds params (.var typ e l)
  | ref   {typ e g tArgs}
      (htyp : Typ.AppRefToDt tds params typ)
      (hArgs : ∀ t ∈ tArgs, Typ.AppRefToDt tds params t) :
      AppRefToDt tds params (.ref typ e g tArgs)
  | field {typ e g} (htyp : Typ.AppRefToDt tds params typ) :
      AppRefToDt tds params (.field typ e g)
  | tuple {typ e ts}
      (htyp : Typ.AppRefToDt tds params typ)
      (h : ∀ sub ∈ ts, AppRefToDt tds params sub) :
      AppRefToDt tds params (.tuple typ e ts)
  | array {typ e ts}
      (htyp : Typ.AppRefToDt tds params typ)
      (h : ∀ sub ∈ ts, AppRefToDt tds params sub) :
      AppRefToDt tds params (.array typ e ts)
  | ret {typ e sub}
      (htyp : Typ.AppRefToDt tds params typ)
      (h : AppRefToDt tds params sub) :
      AppRefToDt tds params (.ret typ e sub)
  | «let» {typ e pat v b}
      (htyp : Typ.AppRefToDt tds params typ)
      (hv : AppRefToDt tds params v) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.let typ e pat v b)
  | «match» {typ e scrut cases}
      (htyp : Typ.AppRefToDt tds params typ)
      (hscrut : AppRefToDt tds params scrut)
      (hcases : ∀ pc ∈ cases, AppRefToDt tds params pc.2) :
      AppRefToDt tds params (.match typ e scrut cases)
  | app {typ e g tArgs args u}
      (htyp : Typ.AppRefToDt tds params typ)
      (hArgs : ∀ t ∈ tArgs, Typ.AppRefToDt tds params t)
      (hargs : ∀ a ∈ args, AppRefToDt tds params a) :
      AppRefToDt tds params (.app typ e g tArgs args u)
  | add {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.add typ e a b)
  | sub {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.sub typ e a b)
  | mul {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.mul typ e a b)
  | eqZero {typ e a} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.eqZero typ e a)
  | proj {typ e a n} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.proj typ e a n)
  | get {typ e a n} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.get typ e a n)
  | slice {typ e a i j} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.slice typ e a i j)
  | «set» {typ e a n v} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hv : AppRefToDt tds params v) :
      AppRefToDt tds params (.set typ e a n v)
  | store {typ e a} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.store typ e a)
  | load {typ e a} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.load typ e a)
  | ptrVal {typ e a} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.ptrVal typ e a)
  | assertEq {typ e a b r} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b)
      (hr : AppRefToDt tds params r) :
      AppRefToDt tds params (.assertEq typ e a b r)
  | ioGetInfo {typ e k} (htyp : Typ.AppRefToDt tds params typ)
      (hk : AppRefToDt tds params k) :
      AppRefToDt tds params (.ioGetInfo typ e k)
  | ioSetInfo {typ e k i l r} (htyp : Typ.AppRefToDt tds params typ)
      (hk : AppRefToDt tds params k) (hi : AppRefToDt tds params i)
      (hl : AppRefToDt tds params l) (hr : AppRefToDt tds params r) :
      AppRefToDt tds params (.ioSetInfo typ e k i l r)
  | ioRead {typ e i n} (htyp : Typ.AppRefToDt tds params typ)
      (hi : AppRefToDt tds params i) :
      AppRefToDt tds params (.ioRead typ e i n)
  | ioWrite {typ e d r} (htyp : Typ.AppRefToDt tds params typ)
      (hd : AppRefToDt tds params d) (hr : AppRefToDt tds params r) :
      AppRefToDt tds params (.ioWrite typ e d r)
  | u8BitDecomposition {typ e a} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.u8BitDecomposition typ e a)
  | u8ShiftLeft {typ e a} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.u8ShiftLeft typ e a)
  | u8ShiftRight {typ e a} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) :
      AppRefToDt tds params (.u8ShiftRight typ e a)
  | u8Xor {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.u8Xor typ e a b)
  | u8Add {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.u8Add typ e a b)
  | u8Sub {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.u8Sub typ e a b)
  | u8And {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.u8And typ e a b)
  | u8Or {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.u8Or typ e a b)
  | u8LessThan {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.u8LessThan typ e a b)
  | u32LessThan {typ e a b} (htyp : Typ.AppRefToDt tds params typ)
      (ha : AppRefToDt tds params a) (hb : AppRefToDt tds params b) :
      AppRefToDt tds params (.u32LessThan typ e a b)
  | debug {typ e label t r} (htyp : Typ.AppRefToDt tds params typ)
      (ht : ∀ tval, t = some tval → AppRefToDt tds params tval)
      (hr : AppRefToDt tds params r) :
      AppRefToDt tds params (.debug typ e label t r)

/-- Source-side obligation: for every typed function (extracted via
`t.checkAndSimplify`), the body is `Typed.Term.AppRefToDt`-safe under
the function's own type-parameter context. Mirrors the body conjunct of
`Typed.Decls.AppRefTArgsFO` with `AppRefToDt` in place of `AppRefTArgsFO`.

Discharges `AllFnBodyAppRefToDt`'s body-position obligation in
`AllAppRefToDt_of_wellFormed`. -/
def BodyAppRefToDt (t : Source.Toplevel) : Prop :=
  ∀ typedDecls, t.checkAndSimplify = .ok typedDecls →
    ∀ g f, typedDecls.getByKey g = some (.function f) →
      Typed.Term.AppRefToDt typedDecls f.params f.body

/-- Eight-conjunct well-formedness predicate. Every conjunct is a computable
`.ok` observation (or a decidable structural property for `FirstOrderReturn`
/ `DirectDatatypeDAGAcyclic` / `NoNameCollisions` / `NoTermRefsToFunctions` /
`NoTypesAreFunctions`).

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
  noTypesAreFunctions : NoTypesAreFunctions t
  noPolyAppRefTArgs : NoPolyAppRefTArgs t
  bodyAppRefToDt : BodyAppRefToDt t

-- TODO: a `WellFormed.empty` sanity lemma would be nice, but
-- `IndexMap`'s `default` doesn't unfold cleanly inside the goal —
-- `decide` would require massive `Decidable` instances that aren't
-- yet derived. Defer until the proof infrastructure is more mature.

end Aiur

end -- @[expose] section
end -- public section
