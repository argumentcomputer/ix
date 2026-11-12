import IxCC.Lam.Erase.Term
import IxCC.Lam.Erase.ProgWF
import IxCC.Lam.ModesOk

/-! # Erasure Src → Lam

`Lam.erase : Src.Program → Checked → Except EraseError (Program × Stats)`
(D17–D19). Demand-driven from the roots (MetaCoq's
`erase_global_deps`): a global is erased when a relevant position first
references its key, so theorems, types and axioms reached only through
irrelevant positions are never visited. Keys carry the universe profile, so
a constant reached at two profiles becomes two globals (`unitBoth`); one
constructor key with two kept-field layouts is declined instead
(`erase-ctor-layout`).

The globals, by key:
* `const c q`: `c`'s δ body at `q` (the `eqn` body, the `csimp` target, or a
  safe or allowlisted value); result contract from `c`'s Π.
* `byName c q`: the same body with the leading binders of the `lazy`
  arity marked `name` where relevant at `q`.
* `recStar r q`: `λ` over every recursor argument (minors `name` where
  relevant), then `case (var 0)` whose alternatives are the rule bodies
  (ordinary), the only rule body with index fields (subsingleton), or `trap`
  (empty).
* `wrapper h q`: `λ^arity` strict over the saturated form of special head
  `h`, for unsaturated occurrences.

Kernel-evaluable style (D17): persistent `NatMap`s and lists, a two-list
queue on fuel, structural recursion or fuel everywhere; no `HashMap`, array
indexing or well-founded recursion. -/

namespace IxCC.Lam

namespace Erase

open IxCC.Src IxCC.Src.Relevance

/-- Erasure's size statistics. -/
structure Stats where
  globals : Nat
  nodes : Nat
  ctors : Nat
  deriving Repr, Inhabited

/-- Nesting fuel for terms, and the queue budget. Erasure recurses natively once
per unit of `termFuel`, and overflows an 8 MiB stack on a constructor chain
about 8,960 deep, so the fuel is `Src.maxTermDepth`, a quarter of that, checked
again here because erasure also walks what the certificate's table
substitutes. -/
def termFuel : Nat := Src.maxTermDepth
def loopFuel : Nat := 1 <<< 24

section

variable (I : Input)

def rec_ : Rec := term I termFuel

/-- The δ body of `c` at `q`. -/
def constBody (c : CId) (q : Profile) : M Term := do
  let cx : Cx := { prof := q, ctx := [], depth := 0 }
  match I.resolve.get? c with
  | some (.csimp g vs _) => rec_ I cx (.const g vs)
  | some (.eqn _ body) => rec_ I cx body
  | some _ => decline "erase-const-kind" "a special head has no δ body" c
  | none =>
    match I.decl? c with
    | some (.defn .defn .safe _ _ v) => rec_ I cx v
    | some (.defn .opaq .safe _ _ v) =>
      if I.isOpaqueByValue c then rec_ I cx v
      else decline "erase-const-kind" "an opaque outside the allowlist" c
    | some d => decline "erase-const-kind" s!"a {d.kindName} has no δ body" c
    | none => decline "erase-const-kind" "no declaration" c

/-- The body of recursor rule `rule` at `q` under the `r⋆` telescope of
`pre` binders, its fields at the given levels, at Lam depth `depth`. The
minor application is erased with its by-name IH arguments. -/
def ruleBody (r : CId) (q : Profile) (pre depth : Nat) (minors : List (Nat × List Mode))
    (rule : Rule) (fields : List (Option Nat)) : M Term := do
  let total := pre + rule.fields
  let (n, body) := peelUpTo total rule.rhs
  unless n == total && fields.length == rule.fields do
    decline "erase-recursor" s!"a rule of {r} is not a λ over its parameters and fields" r
  let cx : Cx := { prof := q, ctx := [], depth, minors }
  let cx := cx.under ((List.range pre).map some ++ fields)
  let (head, args) := body.spineL
  match head with
  | .var v =>
    let h ← rec_ I cx head
    let args ← args.mapM fun (a, m, rl) => do
      if rl.irrP q then pure (Term.box, Mode.strict)
      else if m == .byName then return (← rec_ I cx a, Mode.name)
      else return (← rec_ I cx a, Mode.strict)
    -- By-name IH arguments reach only a minor binder with exactly this
    -- dispatch, which holds a λ-telescope, never a wrapper.
    let modes := args.map (·.2)
    if hasName modes then
      match cx.ctx[v]? with
      | some (some l) =>
        unless cx.minors.lookup l == some modes do
          decline "erase-minor" s!"a rule of {r} applies a binder by name outside its dispatch" r
      | _ => decline "erase-minor" s!"a rule of {r} applies a non-minor by name" r
    return Term.apps h args
  | _ => rec_ I cx body

/-- `r⋆` at `q`. -/
def recStarBody (r : CId) (q : Profile) : M Term := do
  let some (.recr _ _ _ np nmot nmin ni ind rules _) := I.decl? r
    | decline "erase-recursor" "not a recursor" r
  let pre := np + nmot + nmin
  let arity := pre + ni + 1
  let modes := (List.range arity).map fun i =>
    if np + nmot ≤ i && i < pre && !I.paramIrr r q i then Mode.name else .strict
  let minors := ((List.range nmin).filter fun j => modes.getD (np + nmot + j) .strict == .name).map
    fun j => (np + nmot + j, minorSig I r q j)
  let body ← match I.kindAt r q with
    | some .empty => pure .trap
    | some (.subsingleton _ srcs) =>
      let some rule := (I.rulesOf r).head?
        | decline "erase-recursor" "a subsingleton recursor without a rule" r
      let fields := srcs.map fun
        | .index i => some (pre + i)
        | .proof => none
      ruleBody I r q pre arity minors rule fields
    | some .ordinary =>
      if (I.unbox? ind q).isSome then
        decline "erase-unbox-elim" "an eliminator of an unboxed structure" r
      let alts ← (rules.zipIdx).mapM fun (rule, j) => do
        let (k, n, fields) ← ruleAlt I r q arity ind j rule
        return Alt.mk k n (← ruleBody I r q pre (arity + n) minors rule fields)
      pure (.case (.var 0) alts none)
    | none => decline "erase-recursor" "a recursor without a derived kind" r
  return Term.lams modes body

/-- The wrapper of special head `h` at `q`: its saturated form over strict
binders. An argument the head reads (`headReads`) is relevant, since its
slot arrives as the applying site built it (□ or a value); another argument
takes the head's parameter class. So a constructor wrapper with a dropped
field is declined (`erase-S2`): a later application could supply a
relevant value there. -/
def wrapperBody (h : Head) (q : Profile) : M Term := do
  let a := headArity I h
  let modes := List.replicate a Mode.strict
  let cx : Cx := { prof := q, ctx := (List.range a).reverse.map some, depth := a }
  match h with
  | .prim op =>
    return Term.lams modes (.prim (Prim.ofSrc op) ((List.range a).map fun i => cx.lvl i))
  | .word w op => decline "erase-word" s!"{op.leanName w}: fixed-width words are not lowered yet"
  | .ctor c | .quotMk c | .quotLift c | .recr c | .cases c =>
    unless I.headOf c == some h do
      decline "erase-key" s!"a wrapper of a head that {c} is not" c
    let args := (List.range a).map fun i =>
      (Src.Term.var (a - 1 - i), Src.Mode.strict,
        if headReads I h i then Rel.rel else (I.params c).getD i .rel)
    return Term.lams modes (← saturated I (rec_ I) cx h q args)

/-- Erase the global of one key. -/
def keyBody (key : Key.GKey) : M (Term × Ixon.V3.ValueContract) := do
  match key with
  | .const c q => return (← constBody I c q, I.resultContract c)
  | .byName c q =>
    let some a := I.lazy.get? c | decline "erase-lazy" "a by-name variant of a non-lazy constant" c
    -- The by-name binders are the δ body's own leading λs.
    unless ((I.deltaBody c).map fun b => decide (a ≤ b.lamCount)).getD false do
      decline "erase-lazy" s!"the δ body has fewer than {a} leading λs" c
    let body ← constBody I c q
    match Term.setModes (lazyModes I c q a) body with
    | some t => return (t, I.resultContract c)
    | none => decline "erase-lazy" s!"the δ body has fewer than {a} leading λs" c
  | .recStar r q => return (← recStarBody I r q, .shared)
  | .wrapper h q => return (← wrapperBody I h q, .shared)
  | _ => decline "erase-key" s!"erasure does not make {key.render}"

/-- Erase queued keys until the queue is empty (a two-list queue on fuel). -/
def loop : Nat → M Unit
  | 0 => decline "erase-budget" "more globals than the erasure budget"
  | fuel + 1 => do
    let s ← get
    match s.front with
    | (key, g) :: rest =>
      set { s with front := rest, current := some key }
      let (body, result) ← keyBody I key
      modify fun s => { s with globals := s.globals.insert g { key, body, result }
                               nodes := s.nodes + body.nodes }
      loop fuel
    | [] =>
      match s.back with
      | [] => pure ()
      | back =>
        set { s with front := back.reverse, back := [] }
        loop fuel

/-! ## The rows a root's result needs

Erasure registers a constructor's row where a term constructs, matches or
projects it, so a program that never builds one constructor of its root's
result type has no row for it, and the readback of that result type (the
pinned `Bool`'s, or one found by discovery, which needs a row for every
constructor) is incomplete. After the queue is empty, erasure registers the
rows of every constructor a root's result can hold that has none. A key
that already has a row keeps it, so a program whose table was complete is
erased as before. -/

/-- The constants heading a type's application spine and, recursively, its
arguments' (to depth `fuel`). -/
def typeHeads : Nat → Src.Term → List CId
  | 0, _ => []
  | fuel + 1, t =>
    match t.spine with
    | (.const c _, args) => c :: args.flatMap fun (a, _, _) => typeHeads fuel a
    | _ => []

/-- The field types of constructor `k`: its Π-telescope after the
parameters. -/
def fieldTypes (k : CId) : List Src.Term :=
  match I.decl? k with
  | some (.ctor _ _ _ _ np _ ty) => (ty.pis.1.drop np).map (·.2)
  | _ => []

/-- The inductives reachable from the constants `todo`: each inductive among
them and, in turn, among the heads of its constructors' field types, within
`fuel` steps (readback discovery visits no inductive outside this set). -/
def resultInds : Nat → List CId → List CId → List CId
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, t :: todo, seen =>
    if seen.contains t then resultInds fuel todo seen
    else
      match I.decl? t with
      | some (.induct _ _ _ _ _ ctors) =>
        resultInds fuel (todo ++ ctors.flatMap fun k => (fieldTypes I k).flatMap (typeHeads 128))
          (t :: seen)
      | _ => resultInds fuel todo seen

/-- The constructors whose rows root `c`'s result needs: the pinned `Bool`
constructors when `c` returns the pinned `Bool`, and the constructors of every
inductive its result can hold, except the pinned `Nat` (its values are
literals) and an unboxed structure (which has no row). -/
def resultCtors (c : CId) : List CId :=
  match I.decl? c with
  | none => []
  | some d =>
    let res := d.type.pis.2
    let pins := match res.spine.1 with
      | .const B _ =>
        if I.known.bool == some B then [I.known.boolFalse, I.known.boolTrue].filterMap id else []
      | _ => []
    pins ++ (resultInds I 1024 (typeHeads 128 res) []).flatMap fun t =>
      if I.known.nat == some t || (I.unbox? t []).isSome then [] else I.ctorsOf t

/-- Register constructor `k`'s row (its key, index and kept-field count)
unless its key has one. -/
def registerResultRow (k : CId) : M Unit := do
  let some (.ctor _ _ _ cidx _ nf _) := I.decl? k | pure ()
  if ((← get).ctors.get? (I.alias k)).isSome then pure ()
  else registerCtor (I.alias k) cidx (I.keptCount k [] nf)

/-- `registerResultRow` on each constructor of a list. -/
def registerRows : List CId → M Unit
  | [] => pure ()
  | k :: ks => do
    registerResultRow I k
    registerRows ks

/-- The global of a root at the empty profile (every universe parameter
zero, as `Src.run` instantiates it): a constant with a δ body, or the
wrapper of a special head. -/
def rootId (c : CId) : M GlobalId := do
  let q := Profile.normalize [] (I.lvls c)
  match I.resolve.get? c, I.decl? c with
  | some (.csimp ..), _ | some (.eqn ..), _ | none, some (.defn .defn .safe ..) =>
    globalId (.const c q)
  | none, some (.defn .opaq .safe ..) =>
    if I.isOpaqueByValue c then globalId (.const c q)
    else decline "erase-root" "an opaque root" c
  | some (.prim op), _ => globalId (.wrapper (.prim op) q)
  | some (.word w op _), _ =>
    decline "erase-word" s!"{op.leanName w}: fixed-width words are not lowered yet" c
  | some (.case _), _ => globalId (.wrapper (.cases c) q)
  | none, some (.ctor ..) => globalId (.wrapper (.ctor c) q)
  | none, some (.recr ..) => globalId (.wrapper (.recr c) q)
  | none, some (.quot .ctor ..) => globalId (.wrapper (.quotMk c) q)
  | none, some (.quot .lift ..) => globalId (.wrapper (.quotLift c) q)
  | _, _ => decline "erase-root" "a root without a δ body or a special head" c

/-- The whole erasure. -/
def run : M (List GlobalId) := do
  -- `Nat` literals peel into `Nat.succ` with one field, so its field must
  -- be kept (an annotation fact the checker does not state).
  if let some s := I.known.natSucc then
    unless I.kept s [] 0 do decline "erase-pin" "Nat.succ's field is not kept" s
  let roots ← I.roots.mapM (rootId I)
  loop I loopFuel
  registerRows I (I.roots.flatMap (resultCtors I))
  return roots

end

end Erase

open Erase in
/-- Erase a checked Src program. Its declarations must be structurally well
formed (`Input.progWF`, as the kernel's acceptance at ingress ensures), which the correctness proof
assumes, and the erased program must be `ModesOk` (ANF's precondition). -/
def erase (p : Src.Program) (c : Src.Relevance.Checked) : Except EraseError (Program × Stats) :=
  let I := Input.ofProgram p c
  if !I.progWF then
    .error { code := "erase-progwf",
             message := "the declarations are not structurally well formed (ProgWF)" }
  else
  match (run I).run {} with
  | .error e => .error e
  | .ok (roots, s) =>
    let ctors := s.ctorOrder.reverse.filterMap s.ctors.get?
    let L : Program := { globals := s.globals, size := s.next, roots, ctors, known := I.lamKnown }
    -- A by-name binder's dispatches depend on how the δ body of a `lazy`
    -- constant applies its parameters, which erasure does not constrain, so
    -- ANF's precondition is checked here.
    if !modesOk L then
      .error { code := "erase-modes", message := "the erased program is not ModesOk" }
    else
      .ok (L, { globals := s.next, nodes := s.nodes, ctors := ctors.length })

end IxCC.Lam
