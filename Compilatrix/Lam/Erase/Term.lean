import Compilatrix.Lam.Erase.Input

/-! # Erasing terms

Src → Lam per form (design note 02 §5.1, as revised in
`plans/x86-phase1/f3/status.md`), level-exact (D18) and keyed (D19). A term
is erased at a universe profile under a **context map**: each Src de Bruijn
index maps to a Lam binder level, or to □ (`none`). Lam-only binders (the
lets that keep SrcEval's evaluation order, `case`-bound kept fields) only
raise the Lam depth, so `casesOn` minors, recursor rule bodies and
subsingleton index fields are erased in place, without shifting.

Clock exactness. SrcEval's clock is a depth bound; Lam charges `glob`,
closure entry, `name` reads and `tick`. Erasure keeps every SrcEval charge
at the same depth: δ is `glob`, β is closure entry, E1 is a `name` read,
and where a charge has no Lam counterpart erasure emits a `tick` — the ι
of `casesOn` **before** its `case` (SrcEval charges ι before looking at the
major), the minor force of `casesOn`, `Quot.lift`'s charge, and an empty
eliminator's charge before `trap`. An erased recursor `r⋆` is exact because
the last application's closure entry is its ι. Only wrappers of unsaturated
special heads add charges (SrcEval accumulates a `pap` for free).

SrcEval evaluates every relevant strict argument of a spine before its head
fires (E7), including constructor parameters, `casesOn` parameters and
indices, and a strict minor; erasure therefore `let`-binds them in order
(and discards the ones the form does not read), so a timeout or trap in
any of them is kept.

Every form is decided locally; a form outside the Phase 1 fragment is
**declined** with a named code (`EraseError.code`). -/

namespace Compilatrix.Lam.Erase

open Compilatrix.Src Compilatrix.Src.Relevance

/-- A named decline. -/
structure EraseError where
  /-- `erase-const-kind`, `erase-string`, `erase-mode`, `erase-minor` (S25),
  `erase-lazy`, `erase-proj`, `erase-ctor-layout`,
  `erase-C2`, `erase-C4`, `erase-S2`, `erase-scope`, `erase-recursor`, `erase-root`,
  `erase-record`, `erase-fuel`, `erase-budget`, `erase-progwf`. -/
  code : String
  const : Option CId := none
  key : Option Key.GKey := none
  message : String := ""
  deriving Inhabited

def EraseError.render (e : EraseError) : String :=
  let at_ := match e.const with
    | some c => s!" at constant {c}"
    | none => ""
  let in_ := match e.key with
    | some k => s!" in {k.render}"
    | none => ""
  s!"[{e.code}]{at_}{in_}: {e.message}"

instance : ToString EraseError := ⟨EraseError.render⟩

/-- Erasure state: the key table (bucketed by source constant), the pending
queue (two lists), the erased globals and the constructor table. -/
structure St where
  ids : NatMap (List (Key.GKey × GlobalId)) := .leaf
  next : Nat := 0
  front : List (Key.GKey × GlobalId) := []
  back : List (Key.GKey × GlobalId) := []
  globals : NatMap Global := .leaf
  /-- By (aliased) constructor. -/
  ctors : NatMap CtorInfo := .leaf
  /-- Constructor-table order (newest first). -/
  ctorOrder : List CId := []
  nodes : Nat := 0
  /-- The global being erased, for diagnostics. -/
  current : Option Key.GKey := none
  deriving Inhabited

abbrev M := StateT St (Except EraseError)

def decline (code : String) (message : String) (const : Option CId := none) : M α := do
  throw { code, const, key := (← get).current, message }

/-- The id of a key, allocating it (and queueing its erasure) on first use. -/
def globalId (key : Key.GKey) : M GlobalId := do
  let s ← get
  let bucket := (s.ids.get? key.bucket).getD []
  match bucket.lookup key with
  | some g => pure g
  | none =>
    let g := s.next
    set { s with ids := s.ids.insert key.bucket ((key, g) :: bucket), next := g + 1
                 back := (key, g) :: s.back }
    pure g

/-- Record a constructor-table row; one key has one layout. -/
def registerCtor (c : CId) (tag arity : Nat) : M Unit := do
  let s ← get
  match s.ctors.get? c with
  | some info =>
    unless info.tag == tag && info.arity == arity do
      decline "erase-ctor-layout"
        s!"constructor {c} needs {arity} kept fields (tag {tag}), already {info.arity} \
          (tag {info.tag})" c
  | none =>
    set { s with ctors := s.ctors.insert c { key := .src c, tag, arity }
                 ctorOrder := c :: s.ctorOrder }

/-- Where the Src variables of a term live in Lam. -/
structure Cx where
  prof : Profile
  /-- Src de Bruijn index ↦ Lam binder level, or □. -/
  ctx : List (Option Nat)
  depth : Nat
  /-- Levels of an erased recursor's minor binders with their dispatch modes. -/
  minors : List (Nat × List Mode) := []

namespace Cx

/-- The Lam variable at a binder level. -/
def lvl (cx : Cx) (l : Nat) : Term := .var (cx.depth - 1 - l)

/-- Enter a Src binder that is also a Lam binder. -/
def bind (cx : Cx) : Cx := { cx with ctx := some cx.depth :: cx.ctx, depth := cx.depth + 1 }

/-- `n` Lam-only binders. -/
def extra (cx : Cx) (n : Nat) : Cx := { cx with depth := cx.depth + n }

/-- Src binders mapped to the given levels (outermost first). -/
def under (cx : Cx) (slots : List (Option Nat)) : Cx :=
  { cx with ctx := slots.reverse ++ cx.ctx }

end Cx

/-- A spine argument after `let`-binding: □, a let-bound value, or a
by-name term erased later. -/
inductive Ref where
  | box
  | lvl (l : Nat)
  | name (t : Src.Term)
  deriving Inhabited

def Ref.level? : Ref → Option Nat
  | .lvl l => some l
  | _ => none

/-- A Lam-only `let`. -/
def letC : Ixon.V3.LetContract := { nonDep := true }

def wrapLets (lets : List Term) (body : Term) : Term :=
  lets.foldr (fun v acc => .letE letC v acc) body

/-- Peel up to `n` leading λs: how many, and the body. -/
def peelUpTo : Nat → Src.Term → Nat × Src.Term
  | 0, t => (0, t)
  | n + 1, .lam _ _ b => let (k, body) := peelUpTo n b; (k + 1, body)
  | _ + 1, t => (0, t)

/-- The recursive call erasure's helpers receive. -/
abbrev Rec := Cx → Src.Term → M Term

section

variable (I : Input) (rec : Rec)

/-- An argument in a strict position: □ where irrelevant, else erased; a
`byName` argument outside Lazify's positions is declined. -/
def strictArg (cx : Cx) : Src.Term.Arg → M (Term × Mode)
  | (a, m, r) =>
    if r.irrP cx.prof then pure (.box, .strict)
    else match m with
      | .strict => return (← rec cx a, .strict)
      | .byName => decline "erase-mode" "a by-name argument outside Lazify's positions"

def strictArgs (cx : Cx) (args : List Src.Term.Arg) : M (List (Term × Mode)) :=
  args.mapM (strictArg rec cx)

/-- `let`-bind the relevant strict arguments of a spine in order; `byName`
arguments are allowed where the flag is set. Returns the let values, one
`Ref` per argument, and the context under the lets. -/
def bindArgs : Cx → List (Src.Term.Arg × Bool) → M (List Term × List Ref × Cx)
  | cx, [] => pure ([], [], cx)
  | cx, ((a, m, r), nameOk) :: rest => do
    if r.irrP cx.prof then
      let (ls, rs, cx') ← bindArgs cx rest
      return (ls, .box :: rs, cx')
    match m with
    | .byName =>
      unless nameOk do decline "erase-mode" "a by-name argument outside Lazify's positions"
      let (ls, rs, cx') ← bindArgs cx rest
      return (ls, .name a :: rs, cx')
    | .strict =>
      let v ← rec cx a
      let (ls, rs, cx') ← bindArgs (cx.extra 1) rest
      return (v :: ls, .lvl cx.depth :: rs, cx')

/-- A bound argument in a strict position (a by-name one is erased in
place, which only the callers that allow it reach). -/
def refTerm (cx : Cx) : Ref → M Term
  | .box => pure .box
  | .lvl l => pure (cx.lvl l)
  | .name t => rec cx t

/-- The application of a `casesOn` minor to its fields (`none`: □), after
the ι tick: a strict minor is applied; a by-name minor that is a
λ-telescope is peeled (up to the field count) to `tick body`, the
remaining fields applied; □ stays □ (and is stuck if applied). The `tick`
is SrcEval's minor force; the peeled binders' closure entries sit at the
same depth as SrcEval's β. -/
def minorApp (cx : Cx) (minor : Ref) (fields : List (Option Nat)) : M Term := do
  let fieldArgs := fields.map fun
    | some l => (cx.lvl l, Mode.strict)
    | none => (Term.box, Mode.strict)
  match minor with
  | .box => pure (Term.apps .box fieldArgs)
  | .lvl l => pure (Term.apps (cx.lvl l) fieldArgs)
  | .name m =>
    let (p, body) := peelUpTo fields.length m
    let body' ← rec (cx.under (fields.take p)) body
    pure (Term.apps (.tick body') (fieldArgs.drop p))

/-- The shape of a recursor rule's minor application at profile `q`: the
minor it dispatches and the modes of its arguments (`name` for a relevant
by-name IH). -/
def ruleShape (r : CId) (q : Profile) (rule : Rule) : Option (Nat × List Mode) := do
  let .recr _ _ _ np nmot nmin _ _ _ _ ← I.decl? r | none
  let total := np + nmot + nmin + rule.fields
  let (n, body) := peelUpTo total rule.rhs
  unless n == total do none
  let (head, args) := body.spineL
  let .var i := head | none
  unless i < total do none
  let pos := total - 1 - i
  unless np + nmot ≤ pos && pos < np + nmot + nmin do none
  let modes := args.map fun (_, m, rl) =>
    if rl.irrP q then Mode.strict else if m == .byName then .name else .strict
  return (pos - (np + nmot), modes)

/-- The dispatch modes of minor `j` of recursor `r` at `q` (`[]` when no rule
of `r` dispatches it). -/
def minorSig (r : CId) (q : Profile) (j : Nat) : List Mode :=
  ((I.rulesOf r).findSome? fun rule =>
    match ruleShape I r q rule with
    | some (j', ms) => if j' == j then some ms else none
    | none => none).getD []

def hasName (ms : List Mode) : Bool := ms.any (· == .name)

/-- The case alternative of rule `j` of `r` at the recursor profile `q`: its
key and kept arity, registered in the constructor table, and the level of
each field (kept fields bound by the alternative from level `base`). -/
def ruleAlt (r : CId) (q : Profile) (base : Nat) (ind : CId) (j : Nat) (rule : Rule) :
    M (Key.CtorKey × Nat × List (Option Nat)) := do
  let some (.ctor _ _ ind' cidx _ nf _) := I.decl? rule.ctor
    | decline "erase-recursor" s!"rule {j} of {r} does not name a constructor" r
  unless ind' == ind && cidx == j && nf == rule.fields do
    decline "erase-recursor" s!"rule {j} of {r} is not constructor {j} of its inductive" r
  let qc := I.ctorProfile r q
  let arity := I.keptCount rule.ctor qc nf
  registerCtor (I.alias rule.ctor) cidx arity
  let fields := (List.range nf).map fun i =>
    if I.kept rule.ctor qc i then some (base + I.rank rule.ctor qc i) else none
  return (I.ctorKey rule.ctor, arity, fields)

/-- Register the pinned `Bool` constructors (Boolean primitive results). -/
def registerBool : M Unit := do
  for c in [I.known.boolFalse, I.known.boolTrue] do
    if let some c := c then
      if let some (.ctor _ _ _ cidx _ _ _) := I.decl? c then registerCtor c cidx 0

end

/-! ## Saturated special heads -/

section

variable (I : Input) (rec : Rec)

/-- A saturated primitive: all arguments strict (□ where irrelevant, stuck
as in SrcEval). -/
def primForm (cx : Cx) (op : PrimOp) (args : List Src.Term.Arg) : M Term := do
  if op.isPredicate then registerBool I
  return .prim (Prim.ofSrc op) ((← strictArgs rec cx args).map (·.1))

/-- A saturated constructor: relevant strict parameters `let`-bound and
discarded (SrcEval evaluates them, E7); kept fields in order (S2: dropped
fields are built from irrelevant arguments); `Nat.zero`/`Nat.succ` as
literals; an unboxed structure as its kept field. -/
def ctorForm (cx : Cx) (c : CId) (q : Profile) (args : List Src.Term.Arg) : M Term := do
  let some (.ctor _ _ ind cidx np nf _) := I.decl? c
    | decline "erase-const-kind" "not a constructor" c
  if some c == I.known.natZero then return .lit (.nat 0)
  let (lets, _, cx') ← bindArgs rec cx ((args.take np).map (·, false))
  let fieldArgs := args.drop np
  if some c == I.known.natSucc then
    let fs ← strictArgs rec cx' fieldArgs
    return wrapLets lets (.prim .natAdd (fs.map (·.1) ++ [.lit (.nat 1)]))
  let fields ← (fieldArgs.zipIdx).filterMapM fun ((a, m, r), j) => do
    if I.kept c q j then return some (← strictArg rec cx' (a, m, r)).1
    if !r.irrP cx.prof then
      decline "erase-S2" s!"field {j} of {c} is dropped but built from a relevant argument" c
    return none
  match I.unbox? ind q with
  | some _ =>
    match fields with
    | [f] => return wrapLets lets f
    | _ => decline "erase-S2" s!"unboxed {ind} with {fields.length} kept fields" c
  | none =>
    registerCtor (I.alias c) cidx (I.keptCount c q nf)
    return wrapLets lets (.con (I.ctorKey c) fields)

/-- `Quot.mk α r a`: the unboxed `a`, after its relevant strict arguments. -/
def quotMkForm (cx : Cx) (args : List Src.Term.Arg) : M Term := do
  let (lets, refs, cx') ← bindArgs rec cx (args.map (·, false))
  return wrapLets lets (← refTerm rec cx' (refs.getD 2 .box))

/-- `Quot.lift α r β f h q`: the arguments in order, then `tick (f q)` (F8's
charge; `q` is unboxed). -/
def quotLiftForm (cx : Cx) (args : List Src.Term.Arg) : M Term := do
  let (lets, refs, cx') ← bindArgs rec cx (args.map (·, false))
  let f ← refTerm rec cx' (refs.getD 3 .box)
  let q ← refTerm rec cx' (refs.getD 5 .box)
  return wrapLets lets (.tick (.app f q .strict))

/-- A saturated `T.casesOn` over recursor `r` (F5): every relevant strict
argument `let`-bound in order (minors may be by name), then the ι tick and
the dispatch: a `case` on the major (ordinary), the only minor applied to
index fields (subsingleton), or `trap` (empty). -/
def casesForm (cx : Cx) (key r : CId) (q : Profile) (args : List Src.Term.Arg) : M Term := do
  let some (.recr _ _ _ np _ _ ni ind rules _) := I.decl? r
    | decline "erase-recursor" "a case key without a recursor" key
  let minorAt := fun i => decide (np + 1 + ni + 1 ≤ i)
  let (lets, refs, cx') ← bindArgs rec cx (args.zipIdx.map fun (a, i) => (a, minorAt i))
  let minor := fun j => refs.getD (np + 1 + ni + 1 + j) .box
  let body ← match I.kindAt r q with
    | some .empty => pure (.tick .trap)
    | some (.subsingleton _ srcs) =>
      let fields := srcs.map fun
        | .index i => (refs.getD (np + 1 + i) .box).level?
        | .proof => none
      return wrapLets lets (.tick (← minorApp rec cx' (minor 0) fields))
    | some .ordinary =>
      let major := refs.getD (np + 1 + ni) .box
      if major matches .box then
        decline "erase-C4" "an ordinary eliminator with an irrelevant major" r
      if (I.unbox? ind q).isSome then
        decline "erase-unbox-elim" "an eliminator of an unboxed structure" r
      let scrut ← refTerm rec cx' major
      let alts ← (rules.zipIdx).mapM fun (rule, j) => do
        let (k, arity, fields) ← ruleAlt I r q cx'.depth ind j rule
        let body ← minorApp rec (cx'.extra arity) (minor j) fields
        return Alt.mk k arity body
      pure (.tick (.case scrut alts none))
    | none => decline "erase-recursor" "a recursor without a derived kind" r
  return wrapLets lets body

/-- A saturated recursor (F2–F4): the relevant strict arguments `let`-bound,
then `r⋆` applied to every argument, minors by name. A minor dispatched
with a `name` IH must be a λ-telescope (its leading binder modes are set to
the dispatch) or a forwarded minor binder with the same dispatch;
otherwise the spine is declined (S25). -/
def recForm (cx : Cx) (r : CId) (q : Profile) (args : List Src.Term.Arg) : M Term := do
  let some (.recr _ _ _ np nmot nmin ni _ _ _) := I.decl? r
    | decline "erase-recursor" "not a recursor" r
  let isMinor := fun i => decide (np + nmot ≤ i ∧ i < np + nmot + nmin)
  let (lets, refs, cx') ← bindArgs rec cx (args.zipIdx.map fun (a, i) => (a, isMinor i))
  if I.kindAt r q matches some .ordinary && refs.getD (np + nmot + nmin + ni) .box matches .box then
    decline "erase-C4" "an ordinary eliminator with an irrelevant major" r
  let argTerms ← (refs.zipIdx).mapM fun (ref, i) => do
    if !isMinor i then return (← refTerm rec cx' ref, Mode.strict)
    let j := i - (np + nmot)
    let binderName := !I.paramIrr r q i
    let sig := minorSig I r q j
    match ref with
    | .box =>
      if binderName then decline "erase-C2" s!"an irrelevant minor {j} for a relevant binder" r
      return (Term.box, Mode.strict)
    | .lvl l =>
      if !binderName then decline "erase-C2" s!"a relevant minor {j} for an irrelevant binder" r
      if hasName sig then decline "erase-minor" s!"a strict minor {j} dispatched by name (S25)" r
      return (cx'.lvl l, Mode.name)
    | .name m =>
      if !binderName then decline "erase-C2" s!"a relevant minor {j} for an irrelevant binder" r
      if !hasName sig then return (← rec cx' m, Mode.name)
      match m with
      | .var v =>
        match cx'.ctx[v]? with
        | some (some l) =>
          if cx'.minors.lookup l == some sig then return (cx'.lvl l, Mode.name)
          decline "erase-minor" s!"minor {j} forwards a binder with another dispatch (S25)" r
        | _ => decline "erase-minor" s!"minor {j} is a variable, not a λ-telescope (S25)" r
      | _ =>
        if m.lamCount < sig.length then
          decline "erase-minor" s!"minor {j} is not a λ-telescope of {sig.length} binders (S25)" r
        match Term.setModes sig (← rec cx' m) with
        | some t => return (t, Mode.name)
        | none => decline "erase-minor" s!"minor {j} lost its λs (S25)" r
  let g ← globalId (.recStar r q)
  return wrapLets lets (Term.apps (.glob g) argTerms)

end

/-! ## Spines -/

section

variable (I : Input) (rec : Rec)

/-- A special head's arity (as SrcEval's `headArity`). -/
def headArity : Head → Nat
  | .ctor c =>
    match I.decl? c with
    | some (.ctor _ _ _ _ np nf _) => np + nf
    | _ => 0
  | .quotMk _ => 3
  | .quotLift _ => 6
  | .recr r =>
    match I.decl? r with
    | some (.recr _ _ _ np nmot nmin ni _ _ _) => np + nmot + nmin + ni + 1
    | _ => 0
  | .cases c =>
    match I.resolve.get? c with
    | some (.case r) =>
      match I.decl? r with
      | some (.recr _ _ _ np _ nmin ni _ _ _) => np + 1 + ni + 1 + nmin
      | _ => 0
    | _ => 0
  | .prim op => op.arity

/-- Whether firing a special head reads argument `i` (SrcEval F1–F8): the
fields of a constructor, `Quot.mk`'s element, `Quot.lift`'s function and
quotient, every argument of a recursor (its rule receives them), and a
`casesOn`'s indices, major and minors. A wrapper passes such an argument
through as it arrives, whatever the head's parameter class says, because
the application that supplied it decided its relevance. -/
def headReads : Head → Nat → Bool
  | .ctor c, i =>
    match I.decl? c with
    | some (.ctor _ _ _ _ np _ _) => np ≤ i
    | _ => true
  | .quotMk _, i => i == 2
  | .quotLift _, i => i == 3 || i == 5
  | .recr _, _ => true
  | .cases c, i =>
    match I.resolve.get? c with
    | some (.case r) =>
      match I.decl? r with
      | some (.recr _ _ _ np _ _ _ _ _ _) => np + 1 ≤ i
      | _ => true
    | _ => true
  | .prim _, _ => true

/-- A special head applied to exactly its arity. -/
def saturated (cx : Cx) (h : Head) (q : Profile) (args : List Src.Term.Arg) : M Term :=
  match h with
  | .prim op => primForm I rec cx op args
  | .ctor c => ctorForm I rec cx c q args
  | .quotMk _ => quotMkForm rec cx args
  | .quotLift _ => quotLiftForm rec cx args
  | .cases c =>
    match I.resolve.get? c with
    | some (.case r) => casesForm I rec cx c r q args
    | _ => decline "erase-recursor" "a case key without a case entry" c
  | .recr r => recForm I rec cx r q args

/-- A special head applied to its arguments: saturated in place (extra
arguments applied to the result), or through its wrapper global. -/
def special (cx : Cx) (h : Head) (q : Profile) (args : List Src.Term.Arg) : M Term := do
  let a := headArity I h
  if args.length < a then
    let g ← globalId (.wrapper h q)
    return Term.apps (.glob g) (← strictArgs rec cx args)
  let t ← saturated I rec cx h q (args.take a)
  return Term.apps t (← strictArgs rec cx (args.drop a))

/-- Binder modes of `f`'s by-name variant at `q`: `name` at each of the
first `a` parameters relevant at `q`. -/
def lazyModes (f : CId) (q : Profile) (a : Nat) : List Mode :=
  (List.range a).map fun i => if I.paramIrr f q i then .strict else .name

/-- A spine headed by a constant with a δ body: `glob (const f q)`, or for a
saturated `lazy` spine with a relevant by-name position, `glob (byName f
q)` with `name` arguments. C2 is checked locally at the by-name positions. -/
def plainConst (cx : Cx) (f : CId) (q : Profile) (args : List Src.Term.Arg) : M Term := do
  let variant := match I.lazy.get? f with
    | some a => if args.length ≥ a && hasName (lazyModes I f q a) then some a else none
    | none => none
  match variant with
  | some a =>
    let modes := lazyModes I f q a
    let lazyArgs ← (args.take a).zipIdx.mapM fun ((x, m, r), i) => do
      match modes.getD i .strict, r.irrP cx.prof, m with
      | .strict, true, _ => pure (Term.box, Mode.strict)
      | .name, false, .byName => return (← rec cx x, Mode.name)
      | .name, false, .strict =>
        decline "erase-mode" s!"lazy argument {i} of {f} is not by name" f
      | _, _, _ => decline "erase-C2" s!"lazy argument {i} of {f} disagrees with its parameter" f
    let g ← globalId (.byName f q)
    return Term.apps (.glob g) (lazyArgs ++ (← strictArgs rec cx (args.drop a)))
  | none =>
    let g ← globalId (.const f q)
    return Term.apps (.glob g) (← strictArgs rec cx args)

/-- A spine headed by constant `c` with universe arguments `us`. -/
def constSpine (cx : Cx) (c : CId) (us : List Ixon.Univ) (args : List Src.Term.Arg) : M Term := do
  if us.length > I.lvls c then
    decline "erase-univs" s!"{us.length} universe arguments for {I.lvls c} parameters" c
  let q := I.profileOf c cx.prof us
  match I.resolve.get? c with
  | some (.prim op) => special I rec cx (.prim op) q args
  | some (.case _) => special I rec cx (.cases c) q args
  | some (.csimp ..) | some (.eqn ..) => plainConst I rec cx c q args
  | none =>
    match I.decl? c with
    | some (.ctor ..) => special I rec cx (.ctor c) q args
    | some (.recr ..) => special I rec cx (.recr c) q args
    | some (.quot .ctor ..) => special I rec cx (.quotMk c) q args
    | some (.quot .lift ..) => special I rec cx (.quotLift c) q args
    | some (.defn .defn .safe ..) => plainConst I rec cx c q args
    | some (.defn .opaq .safe ..) =>
      if I.isOpaqueByValue c then plainConst I rec cx c q args
      else decline "erase-const-kind" "an opaque outside the allowlist in a relevant position" c
    | some d => decline "erase-const-kind" s!"a {d.kindName} in a relevant position" c
    | none => decline "erase-const-kind" "a reference without a declaration" c

/-- `proj S i e`. A constructor has one layout at every profile (conditional
field classes are kept, `Input.layoutClass`), so a projection, which carries
no universe arguments, needs no profile: a field dropped at every profile
still evaluates `e` (06 S41); an unboxed structure is its field; otherwise a
keyed projection of the kept rank. -/
def projForm (cx : Cx) (s i : Nat) (e : Src.Term) : M Term := do
  let e' ← rec cx e
  let [k] := I.ctorsOf s | decline "erase-proj" s!"projection out of {s}, not a structure" s
  let some fields := I.fields? k | decline "erase-record" "a structure without field classes" k
  let some cls := fields[i]? | decline "erase-proj" s!"projection of field {i} beyond the fields" s
  if cls.dropP [] then return .letE letC e' .box
  if (I.unbox? s []).isSome then return e'
  let some (.ctor _ _ _ cidx _ nf _) := I.decl? k | decline "erase-proj" "not a constructor" k
  registerCtor (I.alias k) cidx (I.keptCount k [] nf)
  return .proj (I.ctorKey k) (I.rank k [] i) e'

end

/-- Erase a term (fuel bounds the nesting depth). -/
def term (I : Input) : Nat → Rec
  | 0, _, _ => decline "erase-fuel" "term nesting exceeds the erasure fuel"
  | fuel + 1, cx, t =>
    let rec_ := term I fuel
    match t with
    | .var i =>
      match cx.ctx[i]? with
      | some (some l) => pure (cx.lvl l)
      | some none => pure .box
      | none => decline "erase-scope" s!"variable #{i} out of scope"
    | .sort _ | .pi .. => pure .box
    | .natLit n => pure (.lit (.nat n))
    | .strLit _ =>
      decline "erase-string" "a string literal in a relevant position (declined before K4)"
    | .lam b _ body => return .lam .strict b.contract (← rec_ cx.bind body)
    | .letE c r _ v b => do
      let v' ← if r.irrP cx.prof then pure .box else rec_ cx v
      return .letE c v' (← rec_ cx.bind b)
    | .proj s i e => projForm I rec_ cx s i e
    | .const .. | .app .. =>
      let (head, args) := t.spineL
      match head with
      | .const c us => constSpine I rec_ cx c us args
      | _ => do
        let h ← rec_ cx head
        return Term.apps h (← strictArgs rec_ cx args)

end Compilatrix.Lam.Erase
