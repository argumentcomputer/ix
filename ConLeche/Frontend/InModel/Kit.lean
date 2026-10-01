module

public import ConLeche.Kernel.Inductives.NativeParts

@[expose] public section

/-!
# The in-process modeller's kit (task #200)

Shared pieces of the in-process construction of `_model` families for
nested and mutual inductive blocks (`ConLeche/Frontend/InModel/*`):

* the naming scheme (lean-inductive-models' `_impl` names, so the two
  generators' streams are diffable — none of these names is special to
  the checker: only the public `_model` slots are consumed, and only
  by the modeled install);
* telescope helpers over `ConLeche.Expr` (de Bruijn frames spelled out at
  every use);
* `specFam`, the syntactic rewrite of every member occurrence
  `T_m p⃗` into the auxiliary family at its tag, `aux p⃗ (tag.m p⃗ ı⃗)`;
* the **kernel-shape recursor** of an indexed recursive family with
  inductive hypotheses — the direct fixpoint route's own generators
  `structRecTyR`/`structRecRhsR`
  (`ConLeche/Kernel/Inductives/NativeParts.lean`), which read a
  recursive field's own `∀`-telescope off the constructor, so a
  REFLEXIVE field `f : ∀ a⃗, T p⃗ e⃗(a⃗)` gets the hypothesis
  `∀ a⃗, motive e⃗(a⃗) (f a⃗)` and the rule passes
  `λ a⃗, T.rec … e⃗(a⃗) (f a⃗)` (official `mk_rec_infos`); the route
  regenerates and compares the recursor of the auxiliary family
  against exactly these generators by one `isDefEq`, so emitting
  their output makes that comparison hold by construction (a private
  copy without the telescopes was what declined every mutual block
  with a reflexive member, 2026-09-21);
* a **syntactic sort inferer** over the parsed declaration table (no
  environment, no `whnf`): the sort of a field's or index's type, for
  the `Eq` level of a `proj_i.iota` artifact and the tag's universe.
  Where it fails the artifact is skipped or the block declines —
  never a wrong accept: everything generated is checked by the fold;
* definitional heights, computed as the kernel does (one above the
  highest constant the value mentions).
-/

namespace ConLeche.Frontend.InModel

open ConLeche

/-! ## Names -/

/-- `T._model._impl.<s>`. -/
def implName (T : Name) (s : String) : Name := ((T.str "_model").str "_impl").str s

/-- The tag family `T._model._impl.tag` of the block owned by `T`. -/
def tagName (T : Name) : Name := implName T "tag"

/-- The tag constructor of member `k`: `T._model._impl.tag.k`. -/
def tagCtorName (T : Name) (k : Nat) : Name := (tagName T).num k

/-- The auxiliary family `T._model._impl.aux`. -/
def auxName (T : Name) : Name := implName T "aux"

/-- The auxiliary constructor of member `k`'s constructor `C`:
`T._model._impl.aux.k.<last component of C>`. -/
def auxCtorName (T : Name) (k : Nat) (C : Name) : Name :=
  match C with
  | .str _ s => ((auxName T).num k).str s
  | .num _ n => ((auxName T).num k).num n
  | .anonymous => (auxName T).num k

/-- The model companion of a block member: `X._model`. -/
def modelName (n : Name) : Name := n.str "_model"

/-- The iota theorem of rule `j` of a modeled recursor `R`:
`R._model.iota_j` (`ConLeche/Kernel/Inductives/Modeled.lean`'s lookup). -/
def iotaName (R : Name) (j : Nat) : Name := (modelName R).str s!"iota_{j}"

/-- A level-parameter name not among `lps`: `u`, then `u_1`, `u_2`, …
— the official kernel's `mk_fresh_lvl_name` convention for a
recursor's elimination level (`inductive.cpp`), so a generated
recursor's level parameters are the ones Lean's own kernel would
mint for the same block. -/
partial def freshLevelName (lps : List Name) (base : String := "u") : Name :=
  if lps.contains (Name.str .anonymous base) then go 1 else Name.str .anonymous base
where
  go (i : Nat) : Name :=
    let n := Name.str .anonymous s!"{base}_{i}"
    if lps.contains n then go (i + 1) else n

/-! ## Binders and frames -/

/-- The default binder datum of a generated binder: `.never` — what the
frontend gives every parsed binder (task #161; the annotate pass
recomputes the datum before it is validated). -/
def bm : BinderMeta := ⟨.never⟩

/-- `λ`-telescope over domains (outermost first). -/
def mkLams (bs : List Expr) (body : Expr) : Expr :=
  bs.foldr (fun d acc => .lam d acc bm) body

/-- `∀`-telescope over domains (outermost first). -/
def mkPis (bs : List Expr) (body : Expr) : Expr :=
  bs.foldr (fun d acc => .forallE d acc bm) body

/-- The variables `bvar (o + n - 1 - k)`, `k < n`: a telescope of `n`
binders seen from `o` binders below it (`structPsAt`). -/
def varsAt (o n : Nat) : List Expr := structPsAt o n

/-- A constant at its level parameters. -/
def constP (n : Name) (lps : List Name) : Expr := .const n (lps.map .param)

/-- The domains of a `∀`-telescope's binder list. -/
def piBinders (bs : List (Expr × BinderMeta)) : List Expr :=
  bs.map (·.1)

/-- A member's or constructor's telescope `ty` re-spelled over the
FIRST member's parameter binders: the first `nP` binders of `former`
(the first member's type) with `ty`'s residual after its own `nP`
parameter binders under them.  Task #218: official compares the
members' (and constructors') parameter domains with `is_def_eq`, so a
member may spell a domain differently from the first (`id Type` for
`Type`); the auxiliary family is built over the first's telescope, and
this is where every generated constructor of it gets that telescope.
The re-spelling is checked, not trusted: the residual was typed under
the member's own domains, and the fold's typing of the generated record
is what compares them (a genuinely different domain makes the record
ill-typed and the fold rejects it). -/
def overFirstParams (nP : Nat) (former ty : Expr) : Option Expr :=
  (ty.stripPis nP).bind fun q => Expr.replacePiBody nP former q.2

/-! ## Family occurrences -/

mutual

/-- Rewrite every occurrence `T_m a⃗` (exactly `nP + nIdx_m` arguments)
of a member of the block into `aux a⃗_P (tag.m a⃗_P a⃗_I)` — the
auxiliary family at the member's tag constructor carrying the index
arguments.  `members` lists `(T_m, m, nIdx_m)`.  An occurrence with any
other arity is left alone (the caller's field classification rejects
such blocks).

One memoized DAG walk (keyed by the node — the rewrite reads no binder
cursor), and, like `mentionsAnyGo`, with no spec lemma: the modeller
is untrusted.  Without it the rebuild runs once per path, which is what
`tests/e2e/tower_mutual.ndjson` exposes. -/
partial def specFamGo (T : Name) (lps : List Name) (nP : Nat)
    (members : List (Name × Nat × Nat)) (memo : Std.HashMap Expr Expr) :
    Expr → Expr × Std.HashMap Expr Expr
  | .bvar i => (.bvar i, memo)
  | .sort u => (.sort u, memo)
  | .fvar i t => (.fvar i t, memo)
  | .lit l => (.lit l, memo)
  | .const n us =>
    match members.find? (·.1 == n) with
    | some (_, m, nIdx) =>
      if nP + nIdx == 0 && us == lps.map .param then
        (Expr.mkAppN (constP (auxName T) lps) [constP (tagCtorName T m) lps], memo)
      else (.const n us, memo)
    | none => (.const n us, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | e@(.app _ _) =>
          let f := e.getAppFn
          let args := e.getAppArgs
          match f with
          | .const n us =>
            match members.find? (·.1 == n) with
            | some (_, m, nIdx) =>
              if args.length == nP + nIdx && us == lps.map .param then
                let (ps, memo) := specFamGoList T lps nP members memo (args.take nP)
                let (is, memo) := specFamGoList T lps nP members memo (args.drop nP)
                (Expr.mkAppN (constP (auxName T) lps)
                  (ps ++ [Expr.mkAppN (constP (tagCtorName T m) lps) (ps ++ is)]), memo)
              else
                let (f', memo) := specFamGo T lps nP members memo f
                let (as, memo) := specFamGoList T lps nP members memo args
                (Expr.mkAppN f' as, memo)
            | none =>
              let (as, memo) := specFamGoList T lps nP members memo args
              (Expr.mkAppN f as, memo)
          | _ =>
            let (f', memo) := specFamGo T lps nP members memo f
            let (as, memo) := specFamGoList T lps nP members memo args
            (Expr.mkAppN f' as, memo)
        | .lam d b m =>
          let (d', memo) := specFamGo T lps nP members memo d
          let (b', memo) := specFamGo T lps nP members memo b
          (.lam d' b' m, memo)
        | .forallE d b m =>
          let (d', memo) := specFamGo T lps nP members memo d
          let (b', memo) := specFamGo T lps nP members memo b
          (.forallE d' b' m, memo)
        | .letE t v b =>
          let (t', memo) := specFamGo T lps nP members memo t
          let (v', memo) := specFamGo T lps nP members memo v
          let (b', memo) := specFamGo T lps nP members memo b
          (.letE t' v' b', memo)
        | .proj s i x =>
          let (x', memo) := specFamGo T lps nP members memo x
          (.proj s i x', memo)
        | e => (e, memo)
      (r, memo.insert e r)

@[inherit_doc specFamGo]
partial def specFamGoList (T : Name) (lps : List Name) (nP : Nat)
    (members : List (Name × Nat × Nat)) (memo : Std.HashMap Expr Expr) :
    List Expr → List Expr × Std.HashMap Expr Expr
  | [] => ([], memo)
  | x :: xs =>
    let (y, memo) := specFamGo T lps nP members memo x
    let (ys, memo) := specFamGoList T lps nP members memo xs
    (y :: ys, memo)

end

@[inherit_doc specFamGo]
def specFam (T : Name) (lps : List Name) (nP : Nat)
    (members : List (Name × Nat × Nat)) (e : Expr) : Expr :=
  (specFamGo T lps nP members {} e).1

/-- Simultaneous substitution of a parameter block: under `d` binders,
`bvar (d + j)` (`j < n`, innermost first) becomes `vals[n - 1 - j]`
(`vals` outermost first, spelled at the frame `d` binders below the
block's, lifted past the binders passed on the way), and every loose
`bvar ≥ d + n` is lowered by `n`.  Unlike `instantiateList` the
replacements are never re-traversed, so they may mention variables of
the surrounding frame. -/
partial def substParams (d n : Nat) (vals : List Expr) (e : Expr) : Expr :=
  (go {} 0 e).1
where
  /-- The memoized rebuild, keyed by the node and the binder cursor
  `k` (which shifts under binders).  As everywhere in the modeller,
  no spec lemma: it is untrusted, and what it emits is checked. -/
  go (memo : Std.HashMap (Expr × Nat) Expr) (k : Nat) :
      Expr → Expr × Std.HashMap (Expr × Nat) Expr
    | .bvar i =>
      (if i < d + k then .bvar i
       else if i < d + k + n then (vals.getD (n - 1 - (i - d - k)) default).liftLooseBVars k 0
       else .bvar (i - n), memo)
    | .sort u => (.sort u, memo)
    | .const nm us => (.const nm us, memo)
    | .lit l => (.lit l, memo)
    | e =>
      match memo[(e, k)]? with
      | some r => (r, memo)
      | none =>
        let (r, memo) : Expr × Std.HashMap (Expr × Nat) Expr :=
          match e with
          | .app f a =>
            let (f', memo) := go memo k f
            let (a', memo) := go memo k a
            (.app f' a', memo)
          | .lam t b m =>
            let (t', memo) := go memo k t
            let (b', memo) := go memo (k + 1) b
            (.lam t' b' m, memo)
          | .forallE t b m =>
            let (t', memo) := go memo k t
            let (b', memo) := go memo (k + 1) b
            (.forallE t' b' m, memo)
          | .letE t v b =>
            let (t', memo) := go memo k t
            let (v', memo) := go memo k v
            let (b', memo) := go memo (k + 1) b
            (.letE t' v' b', memo)
          | .proj s i x =>
            let (x', memo) := go memo k x
            (.proj s i x', memo)
          | .fvar i t =>
            let (t', memo) := go memo k t
            (.fvar i t', memo)
          | e => (e, memo)
        (r, memo.insert (e, k) r)

/-- Does `e` mention any of the names?  One memoized DAG walk: the
answer at a node is a function of the node and `ns`, and `ns` is fixed
for the walk, so the memo is keyed by the node alone and dropped after
each call.

**No spec lemma, and none is owed**: the modeller is untrusted (the
`_model` family it emits is checked at install like any other
declaration), so a memo here needs no `@[csimp]` twin — unlike
`Expr.mentionsFvar` or `lowerBVars`, whose answers a proof consumes.
`tests/e2e/tower_mutual.ndjson` is what walks it: `classifyCtor` asks
this of every ordinary field domain, and a domain carrying a depth-60
shared tower mentions no member, so nothing short-circuits. -/
def mentionsAnyGo (ns : List Name) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .const n _ => (ns.contains n, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .fvar _ ty => mentionsAnyGo ns memo ty
        | .app f a =>
          match mentionsAnyGo ns memo f with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsAnyGo ns memo a
        | .lam ty b _ | .forallE ty b _ =>
          match mentionsAnyGo ns memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsAnyGo ns memo b
        | .letE ty v b =>
          match mentionsAnyGo ns memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) =>
            match mentionsAnyGo ns memo v with
            | (true, memo) => (true, memo)
            | (false, memo) => mentionsAnyGo ns memo b
        | .proj s _ x =>
          if ns.contains s then (true, memo) else mentionsAnyGo ns memo x
        | _ => (false, memo)
      (r, memo.insert e r)

@[inherit_doc mentionsAnyGo]
def mentionsAny (ns : List Name) (e : Expr) : Bool := (mentionsAnyGo ns {} e).1

/-! ## The kernel-shape recursor of an indexed recursive family

The direct fixpoint route's generators (`structRecTyR`/`structRecRhsR`,
`ConLeche/Kernel/Inductives/NativeParts.lean`): a minor premise binds the
constructor's fields, then one `ih` per recursive field in field order —
`∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)` over the field's own telescope `a⃗`
(empty at a finitary field: `motive e⃗_i f_i`), the index expressions
read off its domain `∀ a⃗, T p⃗ e⃗_i(a⃗)` — and concludes
`motive e⃗_C (C p⃗ f⃗)`; rule `j` is
`λ p⃗ motive m⃗ f⃗, minor_j f⃗ (λ a⃗, T.rec p⃗ motive m⃗ e⃗_i(a⃗) (f_i a⃗))…`.
A constructor is `(C, nF, cty, recIdx)` with `recIdx` the recursive
field positions (ascending), finitary or reflexive alike.  The modeller
emits the auxiliary family's recursor as exactly these generators'
output, and the route's comparison of the stream's record against them
holds by construction. -/

/-- **The recursor type** of a recursive family (`structRecTyR`). -/
def recTy (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) : Option Expr :=
  structRecTyR T lps elim large nP nIdx tty ctors

/-- **The rule** of constructor `j` (`structRecRhsR`; `recC`, `rlvls`:
the recursor's name and its level parameters as levels), at the parse
placeholder's binder data throughout (`Expr.resetMeta`): the route
compares a stream rule's body SYNTACTICALLY with the generator's output
reset to the placeholder (`nativeRulesOk`), as a parsed stream carries
it everywhere — and a reflexive hypothesis `λ a⃗, T.rec … (f a⃗)` is
where a generated body has binders of its own. -/
def recRhs (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat))
    (recC : Name) (rlvls : List Level) (j : Nat) : Option Expr :=
  (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j).map Expr.resetMeta

/-! ## A syntactic sort inferer

`inferTy tbl ctx e` computes the type of `e` from the declared types
of the constants it mentions (`tbl`) and the binder domains of the
context (`ctx`, innermost first, each spelled at its own frame),
β-reducing only what instantiating a `∀` produces.  No `whnf`, no
definitional unfolding: an application whose function type is not
syntactically a `∀` after instantiation fails.  `sortOf` reads the
result as a sort. -/

/-- The declared type of a constant: its level parameters and type. -/
abbrev ConstTable := Name → Option (List Name × Expr)

/-- Head β-reduction only. -/
partial def betaHead : Expr → Expr
  | .app f a =>
    match betaHead f with
    | .lam _ b _ => betaHead (b.instantiate1 a)
    | f' => .app f' a
  | e => e

partial def inferTy (tbl : ConstTable) (ctx : List Expr) : Expr → Option Expr
  | .bvar i => (ctx[i]?).map (·.liftLooseBVars (i + 1) 0)
  | .sort u => some (.sort (.succ u))
  | .const n us =>
    (tbl n).bind fun (lps, ty) =>
      if lps.length == us.length then some (ty.instantiateLevelParams lps us) else none
  | .app f a =>
    (inferTy tbl ctx f).bind fun ft =>
      match betaHead ft with
      | .forallE _ b _ => some (b.instantiate1 a)
      | _ => none
  | .lam d b m => (inferTy tbl (d :: ctx) b).map fun bt => .forallE d bt m
  | .forallE d b _ =>
    (sortOf tbl ctx d).bind fun u =>
      (sortOf tbl (d :: ctx) b).map fun v => .sort (.imax u v)
  | .letE _ v b => inferTy tbl ctx (b.instantiate1 v)
  | .lit (.natVal _) => some (.const natName [])
  | .lit (.strVal _) => some (.const stringName [])
  | _ => none
where
  /-- The sort of a type. -/
  sortOf (tbl : ConstTable) (ctx : List Expr) (e : Expr) : Option Level :=
    (inferTy tbl ctx e).bind fun t =>
      match betaHead t with
      | .sort u => some u
      | _ => none

/-- The sort of a type at a context. -/
def sortOf (tbl : ConstTable) (ctx : List Expr) (e : Expr) : Option Level :=
  inferTy.sortOf tbl ctx e

/-! ### The sort ceiling (task #227)

A mutual or nested member's index telescope becomes the FIELDS of a tag
constructor (`tag.m : ∀ p⃗ ı⃗_m, tag p⃗`), so the tag family's own
universe has to dominate every index domain's sort — a level the
modeller must emit, with no environment and no `whnf` to compute it.
`sortOf` reads that sort only where the domain's type is SYNTACTICALLY
a sort, and an index `(x : α)` at a member binding `α : id Type`, or one
at a constant whose declared type is that same stuck application, has no
such reading: task #200 declined the block there (the #218 finding).

The tag does not need the LEAST universe, only one above every index
domain's sort: the install checks `field level ≤ result level`
(`Level.leq`, `ConLeche/Kernel/Inductives/SumInstall.lean`), never
equality, and the tag's universe is read nowhere else — the auxiliary
family takes `tag p⃗` as an INDEX domain, which constrains no universe,
and the public slots are spelled at the members' own declared types.
So `sortCeil ctx D` returns a level at least the sort of `D`:

* where `sortOf` reads a sort, exactly that sort — so no block that
  installed before this function existed moves;
* where `D`'s type `T` is inferable but stuck: `T ≡ Sort ℓ` for the ℓ we
  want, hence `T` itself lives at `ℓ+1`, and a ceiling for `T` bounds
  `ℓ`;
* where `D` is a `∀`: its sort is `imax` of the parts' sorts, and
  `imax a b ≤ max a b`, so the parts' ceilings bound it — the domain's
  sort may be unreadable while the `∀`'s is wanted;
* where `D`'s type is not inferable at all — `D = h a⃗` at a head whose
  own declared type is stuck (`def FamW : id (Type → Type)`): the head's
  type is `∀ x⃗, B` with `B ≡ Sort ℓ`, so its own sort `imax … (ℓ+1)`
  has a non-zero right argument, is therefore a `max`, and is above `ℓ`;
  a ceiling for the head's type bounds `ℓ` too.

Nothing here is trusted: a ceiling for an ill-sorted domain (a "type"
that is not one) is a level like any other, and the tag family the
modeller then emits fails the fold's own type check.  `fuel` bounds the
walk — up the type tower and down a `∀` telescope — and only keeps the
function total. -/
def sortCeil (tbl : ConstTable) : Nat → List Expr → Expr → Option Level
  | 0, _, _ => none
  | fuel + 1, ctx, d =>
    match inferTy tbl ctx d with
    | some t =>
      match betaHead t with
      | .sort u => some u
      | t' => sortCeil tbl fuel ctx t'
    | none =>
      match betaHead d with
      | .forallE dom body _ =>
        (sortCeil tbl fuel ctx dom).bind fun a =>
          (sortCeil tbl fuel (dom :: ctx) body).map fun b => .max a b
      | .letE _ v b => sortCeil tbl fuel ctx (b.instantiate1 v)
      | d' =>
        match inferTy tbl ctx d'.getAppFn with
        | some f => sortCeil tbl fuel ctx f
        | none => none

/-- A ceiling for the sort of an index domain at a context
(`sortCeil`), at a fuel no `∀` telescope or type tower of a real stream
reaches. -/
def idxSort (tbl : ConstTable) (ctx : List Expr) (e : Expr) : Option Level :=
  sortCeil tbl 128 ctx e

/-! ## Definitional heights -/

/-- The highest definitional height of a constant mentioned by `e`
(`heights`: the height of every definition declared so far; `0` for
anything else).  One memoized DAG walk, keyed by the node — and, like
`mentionsAnyGo`, with no spec lemma, since the modeller is untrusted
and the hint it computes is checked with the declaration it rides on.
Every generated value embeds the block's constructor domains, so a
tower in one of them is walked here once per path without it. -/
def maxHeightGo (heights : Name → Nat) (memo : Std.HashMap Expr Nat) :
    Expr → Nat × Std.HashMap Expr Nat
  | .const n _ => (heights n, memo)
  | .bvar _ => (0, memo)
  | .sort _ => (0, memo)
  | .lit _ => (0, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Nat × Std.HashMap Expr Nat :=
        match e with
        | .fvar _ ty => maxHeightGo heights memo ty
        | .app f a =>
          let (rf, memo) := maxHeightGo heights memo f
          let (ra, memo) := maxHeightGo heights memo a
          (max rf ra, memo)
        | .lam ty b _ | .forallE ty b _ =>
          let (rt, memo) := maxHeightGo heights memo ty
          let (rb, memo) := maxHeightGo heights memo b
          (max rt rb, memo)
        | .letE ty v b =>
          let (rt, memo) := maxHeightGo heights memo ty
          let (rv, memo) := maxHeightGo heights memo v
          let (rb, memo) := maxHeightGo heights memo b
          (max rt (max rv rb), memo)
        | .proj _ _ x => maxHeightGo heights memo x
        | _ => (0, memo)
      (r, memo.insert e r)

@[inherit_doc maxHeightGo]
def maxHeight (heights : Name → Nat) (e : Expr) : Nat :=
  (maxHeightGo heights {} e).1

/-- The reducibility hint of a generated definition: one above the
highest constant its value mentions (the kernel's `getMaxHeight`
rule). -/
def hintFor (heights : Name → Nat) (value : Expr) : ReducibilityHint :=
  .regular (maxHeight heights value + 1)

/-- The height a hint records. -/
def hintHeight : ReducibilityHint → Nat
  | .regular n => n
  | _ => 0

end ConLeche.Frontend.InModel
