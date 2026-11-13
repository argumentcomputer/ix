import IxCC.Src.Relevance.Syntax
import IxCC.Src.NatMap
import IxCC.Src.Value

/-! # The relevance checker

Decides an installed annotation in one pass over the
runtime closure, level-exact (D18): the closure is a set of *instances*
`(constant, profile)`, reached from the roots at the empty profile through
positions relevant at the reaching instance's profile (`Src.Runtime`), and
every rule is decided at the instance's profile. It is executable here; its
soundness theorem is `Relevance.Proof.check_sound` (tier S). The checker reads
only syntax: the tags installed in the terms, the `ConstRel`/`CtorRel`
tables and the derived `RecKind`s. It never calls the type checker.

`Level.holds_profile` and `Level.inst_holds` make a profile decide every
condition exactly as SrcEval decides it at the concrete levels it carries,
so the closure walked here is the one SrcEval can reach.

**Tier S** (soundness facts, premises of erasure):
* S1 shape: every runtime term of the closure is annotated and its tags
  cover it exactly (`install`); every condition names parameters below its
  constant's `lvls`; every `CtorRel` has the constructor's field count; every
  `ConstRel` has at most the telescope's length of parameters; every
  constant and constructor the closure reaches has its record.
* S2 dropped fields are built from `irr`: a constructor spine passes an
  argument irrelevant at the instance at every field dropped at the
  constructor's profile.
* S3 `unbox?`, derived per profile: one constructor, exactly one field kept
  at the profile, the type's result not literally `sort 0`, the type not in
  the kept field's type.
* S4 `RecKind` agreement: at a profile where a recursor is a subsingleton
  eliminator, its constructor keeps only fields that `RecKind` reads from an
  index.

**Tier C** (consistency; early rejection with a precise diagnostic):
* C0 a binder written `erased` is irrelevant at the instance.
* C1 no relevant use of a binder irrelevant at the instance.
* C2 at a constant head, an argument is irrelevant at the instance exactly
  when its parameter is irrelevant at the callee's profile (the parameter's
  condition instantiated at the call's universe arguments). This equality
  replaces an earlier one-way rule, under which `Function.comp` at `Sort 0`
  received □ in a parameter its body treats as relevant. It also rejects a
  *type* passed to a relevant parameter of a type-polymorphic callee, which
  no universe condition covers and which SrcEval gets stuck on if the callee
  applies it. The same holds between a β-redex's arguments and its λ
  binders (`have` and `let_fun` elaborate to such redexes).
* C3 fields dropped at the constructor's profile are bound by irrelevant
  minor binders, and a minor's λs cover every field written erased (the
  dispatch passes □ for it). Each minor meets the constructor whose fields it
  receives: at a `case` entry minor `j` meets constructor `j`; at a recursor
  each rule meets the minor it dispatches (`ruleDispatch`), which at a mutual
  or nested block's recursor is not minor `j` for rule `j`. C3 sees the minors
  only at a saturated spine, so an eliminator with a rule for a constructor that
  writes a field erased (`erasedMinors`) occurs only there: applied to fewer
  arguments (`knownHead`), bare (`bareHead`) or as a `csimp` target
  (`checkCanonical`) it is refused, since its minors would arrive later at a head
  C3 does not see. A projection in a
  relevant position does not read a field
  dropped at every instance (a projection carries no universe arguments, so
  the structure's profile is not known there).
* C4 a saturated eliminator whose major is irrelevant is a subsingleton or
  empty eliminator at its profile.
* C5 relevant positions reference only constants whose result is relevant
  at the callee's profile.
* C6 a λ in a relevant position is not a proof at the instance (so SrcEval's
  β guard, rule A1, never fires on it).
* C7 no type (a sort or Π) in a relevant position, a spine's head included:
  SrcEval evaluates one to the irrelevance marker (E2) and erasure to □, so
  a type there would be read as a value. Only the kernel's typing refused
  one before (`def main : E := Sort 0` is ill typed and passes every other
  check); the relevance checks do not assume the kernel's acceptance.

**Style (D17).** The closure loop, the term walk and the per-instance rules
recurse structurally (the loop on a fuel; the term walk is a mutual
structural recursion over `Term`, fixed by `termination_by structural`, so
the kernel never unfolds a well-founded fixpoint), keep their state in lists
and a persistent `NatMap`, and read the program and the annotation through
their `NatMap`s and lists: no array or hash map on the path. -/

namespace IxCC.Src.Relevance

structure RelError where
  /-- `S1`–`S4` or `C0`–`C7`. -/
  rule : String
  key : Option TermKey := none
  const : Option CId := none
  message : String
  deriving Inhabited

def RelError.of (rule message : String) (const : Option CId := none)
    (key : Option TermKey := none) : RelError :=
  { rule, key, const, message }

def RelError.tier (e : RelError) : String := (e.rule.take 1).toString

def RelError.render (p : Program) (e : RelError) : String :=
  let at_ := match e.key with
    | some (.value c) => s!" in the value of {p.short c}"
    | some (.eqn c) => s!" in the eqn body of {p.short c}"
    | some (.rule r j) => s!" in rule {j} of {p.short r}"
    | none => ""
  let of_ := match e.const with
    | some c => s!" ({p.short c})"
    | none => ""
  s!"[relevance {e.rule}]{at_}{of_}: {e.message}"

/-- S3 `unbox?` at a profile, derived: a structure-like inductive with
exactly one field kept at `prof`, whose result is not literally `sort 0`
and whose kept field's type does not mention it. -/
def unboxOf (p : Program) (ctorRel? : CId → Option CtorRel) (t : CId) (prof : Profile) :
    Option Nat := do
  let .induct _ _ np _ ty [k] ← p.decl? t | none
  let rel ← ctorRel? k
  let kept := (rel.fields.zipIdx).filter fun (c, _) => !c.dropP prof
  let [(_, j)] := kept | none
  let resultProp := match ty.pis.2 with
    | .sort .zero => true
    | _ => false
  if resultProp then none
  let .ctor _ _ _ _ _ _ cty ← p.decl? k | none
  let (_, fieldTy) ← cty.pis.1[np + j]?
  if fieldTy.mentions t then none
  return j

/-- The checker's verdict: the runtime closure with its records (lists and
`NatMap`s, D17). -/
structure Checked where
  keys : List TermKey
  /-- Distinct reached constants, in discovery order. -/
  reached : List CId
  /-- Every reached instance `(constant, profile)`, in discovery order. -/
  instances : List Inst
  consts : NatMap ConstRel
  ctors : NatMap CtorRel
  deriving Inhabited

namespace Checked

def ctorRel? (c : Checked) (k : CId) : Option CtorRel := c.ctors.get? k
def constRel? (c : Checked) (k : CId) : Option ConstRel := c.consts.get? k

/-- Whether field `i` of constructor `k` is kept at profile `prof`
(unannotated: kept). -/
def keepsP (c : Checked) (k : CId) (prof : Profile) (i : Nat) : Bool :=
  match c.ctorRel? k with
  | some r =>
    match r.fields[i]? with
    | some cls => !cls.dropP prof
    | none => false
  | none => true

/-- Whether field `i` of a constructor value built at levels `ls` is kept. -/
def keeps (c : Checked) (k : CId) (ls : Levels) (i : Nat) : Bool :=
  c.keepsP k (profileOf ls) i

/-- S3: the kept field of an unboxed structure at a profile. -/
def unbox? (c : Checked) (p : Program) (t : CId) (prof : Profile) : Option Nat :=
  unboxOf p c.ctorRel? t prof

/-- Constants reached at more than one profile (erasure's `profile-split`). -/
def profileSplit (c : Checked) : List CId :=
  c.reached.filter fun k => (c.instances.filter (·.1 == k)).length > 1

end Checked

namespace Check

/-- One instance's term: its key, the owning constant's level count and the
instance's profile. -/
structure Ctx where
  p : Program
  ann : Ann
  key : TermKey
  lvls : Nat
  prof : Profile

def err (ctx : Ctx) (rule : String) (msg : String) (const : Option CId := none) : RelError :=
  { rule, key := some ctx.key, const, message := msg }

/-- S1: every parameter a condition names is below the level count. -/
def pwOk (lvls : Nat) (c : PropWhen) : Bool := c.params.all (· < lvls)

def relOk (lvls : Nat) : Rel → Bool
  | .rel => true
  | .proof .never => false
  | .proof w => pwOk lvls w
  | .type => true

def relName : Rel → String
  | .rel => "relevant"
  | .proof w => s!"proof ({repr w})"
  | .type => "type"

/-- The single constructor of a structure-like inductive. -/
def onlyCtor? (p : Program) (s : CId) : Option CId :=
  match p.decl? s with
  | some (.induct _ _ _ _ _ [k]) => some k
  | _ => none

/-- Peel exactly `n` leading λs (structural). -/
def peelLamsN : Nat → Term → Option Term
  | 0, t => some t
  | n + 1, .lam _ _ t => peelLamsN n t
  | _ + 1, _ => none

/-- The minor premise that rule `rule` of recursor `r` dispatches, as SrcEval's
F2 runs it: the rule's body, under its `np + nmot + nmin` leading λs and one
per field, is an application headed by the variable bound at a minor position.
`none` for a body of any other shape. This is erasure's reading
(`Lam.Erase.ruleShape`). A recursor of a mutual block (and of a nested one,
stored as a mutual block with auxiliary types) takes the minors of every
constructor of the block and has rules only for its own inductive's
constructors, so its minor `j` is not in general the minor of its rule `j`. -/
def ruleDispatch (p : Program) (r : CId) (rule : Rule) : Option Nat :=
  match p.decl? r with
  | some (.recr _ _ _ np nmot nmin _ _ _ _) =>
    let total := np + nmot + nmin + rule.fields
    match peelLamsN total rule.rhs with
    | some body =>
      match body.spineL.1 with
      | .var i =>
        if i < total && np + nmot ≤ total - 1 - i && total - 1 - i < np + nmot + nmin then
          some (total - 1 - i - (np + nmot))
        else none
      | _ => none
    | none => none
  | _ => none

/-- Positional roles of a saturated eliminator spine: its minors as
(argument position, minor index, rule index), the major position, and the
recursor. A `case` entry applies minor `j` to the fields of constructor `j`
(SrcEval's F5), so there minor `j` meets rule `j`; a recursor runs the rule
of the major's constructor, which applies the minor it dispatches (F2), so
there each rule meets the minor it dispatches (`ruleDispatch`), and a minor
no rule dispatches meets none. A `case` key has the recursor's universe
parameters (`Table.checkCase`), so both are decided at the head's
profile. -/
structure ElimShape where
  recr : CId
  minors : List (Nat × Nat × Nat)
  major : Nat
  arity : Nat

def elimShape? (p : Program) (c : CId) : Option ElimShape :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ np _ nmin ni _ _ _) =>
      some { recr := r, minors := (List.range nmin).map fun j => (np + 1 + ni + 1 + j, j, j)
             major := np + 1 + ni, arity := np + 1 + ni + 1 + nmin }
    | _ => none
  | none =>
    match p.decl? c with
    | some (.recr _ _ _ np nmot nmin ni _ rules _) =>
      some { recr := c
             minors := rules.zipIdx.filterMap fun (rule, k) =>
               (ruleDispatch p c rule).map fun j => (np + nmot + j, j, k)
             major := np + nmot + nmin + ni, arity := np + nmot + nmin + ni + 1 }
    | _ => none
  | _ => none

/-- Field classes of the constructor selected by rule `j` of `r`. -/
def ruleCtorFields (p : Program) (ann : Ann) (r : CId) (j : Nat) :
    Option (CId × List FieldClass) := do
  let .recr _ _ _ _ _ _ _ _ rules _ ← p.decl? r | none
  let rule ← rules[j]?
  let rel ← ann.ctorRel? rule.ctor
  return (rule.ctor, rel.fields)

/-- The profile of a recursor's constructors (the major inductive's
universe arguments) from the recursor's profile. -/
def ctorProfile (p : Program) (r : CId) (qRec : Profile) : Profile :=
  match p.majorUnivs r with
  | some us => qRec.inst us
  | none => qRec

/-- The leading binder classes of a λ-telescope (structural). -/
def lamRels : Term → List Rel
  | .lam b _ t => b.rel :: lamRels t
  | _ => []

/-- A constant in a relevant position (C5, and S1's record presence). -/
def constHead (ctx : Ctx) (c : CId) (us : List Ixon.Univ) (errs : List RelError) :
    List RelError :=
  match ctx.ann.constRel? c with
  | some rel =>
    if rel.result.irrP (ctx.prof.inst us) then
      err ctx "C5" s!"relevant reference to a {relName rel.result} constant at this instance"
        (some c) :: errs
    else errs
  | none => err ctx "S1" "constant without a record" (some c) :: errs

/-- C2 over the leading arguments and parameters. -/
def paramArgs (ctx : Ctx) (c : CId) (q : Profile) :
    List Term.Arg → List Rel → List RelError → List RelError
  | (_, _, a) :: args, r :: params, errs =>
    let errs :=
      if r.irrP q && !a.irrP ctx.prof then
        err ctx "C2" s!"a {relName r} parameter gets a relevant argument" (some c) :: errs
      else if a.irrP ctx.prof && !r.irrP q then
        err ctx "C2" s!"a {relName a} argument for a parameter relevant at this instance"
          (some c) :: errs
      else errs
    paramArgs ctx c q args params errs
  | _, _, errs => errs

/-- S2 over a constructor's fields at the constructor's profile `q`. -/
def fieldArgs (ctx : Ctx) (c : CId) (q : Profile) :
    Nat → List Term.Arg → List FieldClass → List RelError → List RelError
  | j, (_, _, a) :: args, cls :: fields, errs =>
    let errs :=
      if cls.dropP q && !a.irrP ctx.prof then
        err ctx "S2" s!"field {j} is dropped but built from a relevant argument" (some c) :: errs
      else errs
    fieldArgs ctx c q (j + 1) args fields errs
  | _, _, _, errs => errs

/-- Whether field `i` of constructor `k` is written erased in its type. -/
def fieldWrittenErased (p : Program) (k : CId) (i : Nat) : Bool :=
  match p.decl? k with
  | some (.ctor _ _ _ _ np _ ty) => (ty.pis.1[np + i]?).any (·.1.contract.uses == .erased)
  | _ => false

/-- Whether the eliminator `shape` has a rule for a constructor that writes a field erased (the
rules of its recursor; a `case` entry dispatches the same constructors). Its minors must then
meet C3, which compares them with the constructors only at a saturated spine: elsewhere the
eliminator is refused (`knownHead` on a shorter spine, `bareHead` on a bare occurrence,
`Canonical.redirectsErased?` on a `csimp` redirect). Minors no rule of the recursor dispatches
receive no field of its own rules (`Canonical.forwardsErased?`). -/
def erasedMinors (p : Program) (shape : ElimShape) : Bool :=
  match p.decl? shape.recr with
  | some (.recr _ _ _ _ _ _ _ _ rules _) =>
    rules.any fun rule =>
      match p.decl? rule.ctor with
      | some (.ctor _ _ _ _ _ nf _) => (List.range nf).any (fieldWrittenErased p rule.ctor ·)
      | _ => false
  | _ => false

/-- C3 over a minor's binders at the constructor's profile `qc`. The minor's
leading λs must also cover every field written erased: the dispatch passes □
for it (a field written erased is dropped at every instance), so a minor with
fewer λs, an η-short one, would be applied to □ where it may need a value. A
field irrelevant only by its sort needs no λ: the minor's own header classifies
it from the same sort facts. -/
def minorBinders (ctx : Ctx) (k : CId) (j : Nat) (qc : Profile) :
    Nat → List Rel → List FieldClass → List RelError → List RelError
  | i, b :: bs, cls :: fields, errs =>
    let errs :=
      if cls.dropP qc && !b.irrP ctx.prof then
        err ctx "C3" s!"minor {j} binds dropped field {i} relevantly" (some k) :: errs
      else errs
    minorBinders ctx k j qc (i + 1) bs fields errs
  | i, [], _ :: fields, errs =>
    if fieldWrittenErased ctx.p k i then
      err ctx "C3" s!"minor {j} does not bind field {i}, which is written erased (an η-short \
        minor): it must bind every field up to the last one written erased" (some k) :: errs
    else minorBinders ctx k j qc (i + 1) [] fields errs
  | _, _, _, errs => errs

/-- C3's refusal of an eliminator applied to fewer arguments than its arity, or not applied, when
it has a rule for a constructor that writes a field erased (`erasedMinors`): its minors would
arrive later at a head C3 does not see. -/
def partialElim (ctx : Ctx) (shape : ElimShape) (errs : List RelError) : List RelError :=
  if erasedMinors ctx.p shape then
    err ctx "C3" "an eliminator over a constructor that writes a field erased is applied to fewer \
      arguments than its arity: its minor premises would meet no check" (some shape.recr) :: errs
  else errs

/-- A constant in a relevant position that is not the head of an application spine: C5 and S1
(`constHead`), and C3 on a bare eliminator (`partialElim`). -/
def bareHead (ctx : Ctx) (c : CId) (us : List Ixon.Univ) (errs : List RelError) : List RelError :=
  let errs := constHead ctx c us errs
  match elimShape? ctx.p c with
  | some shape => partialElim ctx shape errs
  | none => errs

/-- Rules at a constant head: C2, S2, and C3/C4 at eliminators (C3 on the minors at a saturated
spine, `partialElim` on a shorter one). -/
def knownHead (ctx : Ctx) (errs : List RelError) (c : CId) (us : List Ixon.Univ)
    (args : List Term.Arg) : List RelError :=
  let p := ctx.p
  let q := ctx.prof.inst us
  let errs := match ctx.ann.constRel? c with
    | some rel => paramArgs ctx c q args rel.params errs
    | none => errs
  let errs := match p.decl? c, ctx.ann.ctorRel? c with
    | some (.ctor _ _ _ _ np _ _), some rel => fieldArgs ctx c q 0 (args.drop np) rel.fields errs
    | some (.ctor ..), none => err ctx "S1" "constructor without a record" (some c) :: errs
    | _, _ => errs
  match elimShape? p c with
  | none => errs
  | some shape =>
    if args.length < shape.arity then partialElim ctx shape errs else
    let kind := ((p.table.recKindOf shape.recr).map (fun k => RecKind.atProfile q k)).getD .ordinary
    let errs := match args[shape.major]? with
      | some (_, _, a) =>
        if a.irrP ctx.prof && !kind.allowsIrrMajor then
          err ctx "C4" "an ordinary eliminator with an irrelevant major" (some shape.recr) :: errs
        else errs
      | none => errs
    let qc := ctorProfile p shape.recr q
    shape.minors.foldl (init := errs) fun errs (pos, j, rule) =>
      match args[pos]?, ruleCtorFields p ctx.ann shape.recr rule with
      | some (minor, _, a), some (k, fields) =>
        if a.irrP ctx.prof then errs
        else minorBinders ctx k j qc 0 (lamRels minor) fields errs
      | _, _ => errs

/-- C2 at a β-redex head (`have`/`let_fun` style): each argument against the
λ binder it meets, at the instance's own profile. -/
def lamHead (ctx : Ctx) (errs : List RelError) (head : Term) (args : List Term.Arg) :
    List RelError :=
  let go : List Term.Arg → List Rel → List RelError → List RelError :=
    fun args binders errs => (args.zip binders).foldl (init := errs) fun errs ((_, _, a), r) =>
      if r.irrP ctx.prof && !a.irrP ctx.prof then
        err ctx "C2" s!"a {relName r} λ binder gets a relevant argument" :: errs
      else if a.irrP ctx.prof && !r.irrP ctx.prof then
        err ctx "C2" s!"a {relName a} argument for a λ binder relevant at this instance"
          :: errs
      else errs
  go args (lamRels head) errs

/-- C1/S1 at a variable. -/
def varRule (ctx : Ctx) (binders : List Rel) (errs : List RelError) (i : Nat) :
    List RelError :=
  match binders[i]? with
  | some r =>
    if r.irrP ctx.prof then err ctx "C1" s!"relevant use of a {relName r} binder (#{i})" :: errs
    else errs
  | none => err ctx "S1" s!"variable #{i} out of scope" :: errs

/-- S1 and C0 at a λ, then C6: the errors, and whether to enter the body. -/
def lamRule (ctx : Ctx) (errs : List RelError) (b : Binder) : List RelError × Bool :=
  let errs := if pwOk ctx.lvls b.propWhen && relOk ctx.lvls b.rel then errs
    else err ctx "S1" "a condition names a parameter beyond the constant's levels" :: errs
  let errs := if b.contract.uses == .erased && !b.rel.irrP ctx.prof then
      err ctx "C0" "a binder written erased is annotated relevant" :: errs
    else errs
  if b.propWhen.holdsP ctx.prof then
    (err ctx "C6" "a λ in a relevant position is a proof at this instance" :: errs, false)
  else (errs, true)

/-- C7 at a sort or Π in a relevant position: it has no value at run time. -/
def sortRule (ctx : Ctx) (errs : List RelError) : List RelError :=
  err ctx "C7" "a type (a sort or Π) in a relevant position: SrcEval yields the irrelevance \
    marker for it and erasure □" :: errs

/-- S1 and C0 at a let. -/
def letRule (ctx : Ctx) (errs : List RelError) (c : Ixon.V3.LetContract) (r : Rel) :
    List RelError :=
  let errs := if relOk ctx.lvls r then errs
    else err ctx "S1" "a condition names a parameter beyond the constant's levels" :: errs
  if c.binder.uses == .erased && !r.irrP ctx.prof then
    err ctx "C0" "a let written erased is annotated relevant" :: errs
  else errs

/-- C3/S1 at a projection. -/
def projRule (ctx : Ctx) (errs : List RelError) (s i : Nat) : List RelError :=
  match onlyCtor? ctx.p s with
  | some k =>
    match ctx.ann.ctorRel? k with
    | some rel =>
      match rel.fields[i]? with
      | some cls =>
        if cls.alwaysDropped then
          err ctx "C3" s!"field {i} is never kept but is projected relevantly" (some k) :: errs
        else errs
      | none => err ctx "C3" s!"projection of field {i} beyond the fields" (some k) :: errs
    | none =>
      err ctx "S1" "projection of a structure without a constructor record" (some k) :: errs
  | none => err ctx "C3" "projection out of a type that is not a structure" (some s) :: errs

/-- S1 on an argument's class. -/
def argRule (ctx : Ctx) (errs : List RelError) (r : Rel) : List RelError :=
  if relOk ctx.lvls r then errs
  else err ctx "S1" "a condition names a parameter beyond the constant's levels" :: errs

/-- The rules at an application node `t`: C2/S2/C3/C4 at its spine's head,
then S1 on its argument's class `r`. -/
def appRule (ctx : Ctx) (errs : List RelError) (t : Term) (r : Rel) : List RelError :=
  let (head, args) := t.spineL
  let errs := match head with
    | .const c us => knownHead ctx errs c us args
    | .lam .. => lamHead ctx errs head args
    | _ => errs
  argRule ctx errs r

mutual

/-- Check the relevant positions of a term under binder classes `binders`
(innermost first). -/
def term (ctx : Ctx) (binders : List Rel) (errs : List RelError) : Term → List RelError
  | .var i => varRule ctx binders errs i
  | .const c us => bareHead ctx c us errs
  | .lam b _ t =>
    let (errs, enter) := lamRule ctx errs b
    if enter then term ctx (b.rel :: binders) errs t else errs
  | .letE c r _ v b =>
    let errs := letRule ctx errs c r
    let errs := if r.irrP ctx.prof then errs else term ctx binders errs v
    term ctx (r :: binders) errs b
  | .proj s i e => term ctx binders (projRule ctx errs s i) e
  | .app f a m r =>
    let errs := appRule ctx errs (.app f a m r) r
    let errs := rest ctx binders errs f
    if r.irrP ctx.prof then errs else term ctx binders errs a
  | .sort _ | .pi .. => sortRule ctx errs
  | _ => errs
termination_by structural t => t

/-- The rest of an application spine: its relevant arguments and its head,
which is checked as `term` checks it (the cases are repeated so that both
functions recurse structurally on `Term`). -/
def rest (ctx : Ctx) (binders : List Rel) (errs : List RelError) : Term → List RelError
  | .app f a _ r =>
    let errs := argRule ctx errs r
    let errs := rest ctx binders errs f
    if r.irrP ctx.prof then errs else term ctx binders errs a
  | .var i => varRule ctx binders errs i
  | .const c us => constHead ctx c us errs
  | .lam b _ t =>
    let (errs, enter) := lamRule ctx errs b
    if enter then term ctx (b.rel :: binders) errs t else errs
  | .letE c r _ v b =>
    let errs := letRule ctx errs c r
    let errs := if r.irrP ctx.prof then errs else term ctx binders errs v
    term ctx (r :: binders) errs b
  | .proj s i e => term ctx binders (projRule ctx errs s i) e
  | .sort _ | .pi .. => sortRule ctx errs
  | _ => errs
termination_by structural t => t

end

/-- S4 at one recursor instance. -/
def subsingletonFields (p : Program) (ann : Ann) (r : CId) (q : Profile)
    (errs : List RelError) : List RelError :=
  match p.decl? r, (p.table.recKindOf r).map (fun k => RecKind.atProfile q k) with
  | some (.recr _ _ _ _ _ _ _ _ rules _), some (.subsingleton _ srcs) =>
    match rules.head? with
    | some rule =>
      match ann.ctorRel? rule.ctor with
      | some rel =>
        let qc := ctorProfile p r q
        (rel.fields.zipIdx).foldl (init := errs) fun errs (cls, j) =>
          if cls.dropP qc then errs
          else match srcs[j]? with
            | some (.index _) => errs
            | _ => RelError.of "S4" s!"subsingleton field {j} is kept but not read from an index"
                (some r) :: errs
      | none => errs
    | none => errs
  | _, _ => errs

/-- The closure walk's state: instances seen per constant, discovery
order, runtime keys and errors (all lists newest first). -/
structure St where
  seen : NatMap (List Profile) := .leaf
  order : List Inst := []
  keys : List TermKey := []
  errs : List RelError := []

/-- One runtime key of an instance's visit: on the constant's first visit
an unannotated key is reported and an annotated one recorded; an annotated
key's term is checked at the instance. -/
def visitKey (p : Program) (ann : Ann) (marked : List TermKey) (prof : Profile) (lvls : Nat)
    (first : Bool) (s : St) (key : TermKey) : St :=
  if !marked.contains key then
    if first then
      { s with errs := RelError.of "S1" "runtime term not annotated" none (some key) :: s.errs }
    else s
  else
    let s := if first then { s with keys := key :: s.keys } else s
    match p.termOf key with
    | some t => { s with errs := term { p, ann, key, lvls, prof } [] s.errs t }
    | none => s

/-- Visit one new instance: check its runtime terms at its profile, and
return the instances they reach. `first` is the constant's first visit
(its keys are recorded once). -/
def visit (p : Program) (ann : Ann) (annotated : NatMap (List TermKey)) (c : CId)
    (prof : Profile) (lvls : Nat) (first : Bool) (s : St) : St × List Inst :=
  let marked := (annotated.get? c).getD []
  let s := if first && (ann.constRel? c).isNone then
      { s with errs := RelError.of "S1" "reached constant without a record" (some c) :: s.errs }
    else s
  let s := (p.runtimeKeys c).foldl (init := s) (visitKey p ann marked prof lvls first)
  let s := { s with errs := subsingletonFields p ann c prof s.errs }
  -- Unannotated terms carry ingress defaults; the closure follows them anyway,
  -- as SrcEval would.
  (s, p.instRefs c prof)

/-- The closure loop over a two-list queue (`front`, then `back` reversed),
structural on `fuel`. -/
def loop (p : Program) (ann : Ann) (annotated : NatMap (List TermKey)) :
    Nat → St → List Inst → List Inst → St
  | 0, s, _, _ => { s with errs := RelError.of "S1" "closure budget exhausted" :: s.errs }
  | fuel + 1, s, front, back =>
    match front with
    | [] =>
      match back with
      | [] => s
      | _ => loop p ann annotated fuel s back.reverse []
    | (c, prof0) :: front =>
      let lvls := ((p.decl? c).map Decl.lvls).getD 0
      let prof := prof0.normalize lvls
      let seen := (s.seen.get? c).getD []
      if c ≥ p.size || seen.contains prof then loop p ann annotated fuel s front back
      else
        let s := { s with seen := s.seen.insert c (prof :: seen), order := (c, prof) :: s.order }
        let (s, next) := visit p ann annotated c prof lvls seen.isEmpty s
        loop p ann annotated fuel s front (next.reverse ++ back)

/-- S1 on the records: parameter and field counts, and condition ranges. -/
def records (p : Program) (ann : Ann) : List RelError :=
  (List.range p.size).foldl (init := []) fun errs c =>
    let lvls := ((p.decl? c).map Decl.lvls).getD 0
    let errs := match ann.constRel? c with
      | some rel =>
        let telescope := ((p.decl? c).map fun d => d.type.piCount).getD 0
        let errs := if rel.params.length ≤ telescope then errs
          else RelError.of "S1" "more parameter classes than binders" (some c) :: errs
        if (rel.result :: rel.params).all (relOk lvls) then errs
        else RelError.of "S1" "a parameter class names a level beyond the constant's" (some c) :: errs
      | none => errs
    match ann.ctorRel? c with
    | some rel =>
      match p.decl? c with
      | some (.ctor _ _ _ _ _ nf _) =>
        let errs := if rel.fields.length == nf then errs
          else RelError.of "S1" "field classes differ from the field count" (some c) :: errs
        if rel.fields.all (fun cls => pwOk lvls cls.dropWhen) then errs
        else RelError.of "S1" "a field class names a level beyond the constructor's" (some c) :: errs
      | _ => RelError.of "S1" "constructor record on a non-constructor" (some c) :: errs
    | none => errs

/-- The closure budget: far above any K1 closure (instances plus queue
reversals). -/
def fuel : Nat := 1 <<< 24

end Check

open Check in
/-- Check an installed program against its annotation (`install` must have
run first). All violations are collected; any one rejects. -/
def check (p : Program) (ann : Ann) : Except (Array RelError) Checked :=
  let annotated : NatMap (List TermKey) := ann.nodes.foldl (init := .leaf) fun m (key, _) =>
    let c := match key with
      | .value c | .eqn c | .rule c _ => c
    m.insert c (key :: (m.get? c).getD [])
  let roots := p.roots.map fun (_, c) => p.instOf c []
  let s := loop p ann annotated fuel {} roots []
  let errs := s.errs.reverse ++ (records p ann).reverse
  if !errs.isEmpty then .error errs.toArray
  else
    let instances := s.order.reverse
    let reached := instances.foldl (init := ([] : List CId)) (fun acc (c, _) =>
      if acc.contains c then acc else c :: acc) |>.reverse
    .ok { keys := s.keys.reverse, reached, instances, consts := ann.consts, ctors := ann.ctors }

namespace Check.Canonical

open IxCC.Ixon

def instUniv (us : List Univ) : Univ → Univ
  | .zero => .zero
  | .succ u => .succ (instUniv us u)
  | .max a b => .max (instUniv us a) (instUniv us b)
  | .imax a b => .imax (instUniv us a) (instUniv us b)
  | .var i => us.getD i.toNat .zero

def liftTerm (byN : Nat) : Nat → Term → Term
  | _, .sort u => .sort u
  | _, .const c us => .const c us
  | _, .natLit n => .natLit n
  | _, .strLit s => .strLit s
  | k, .var i => if i >= k then .var (i + byN) else .var i
  | k, .app f a m r => .app (liftTerm byN k f) (liftTerm byN k a) m r
  | k, .lam b d t => .lam b (liftTerm byN k d) (liftTerm byN (k + 1) t)
  | k, .pi b r d t => .pi b r (liftTerm byN k d) (liftTerm byN (k + 1) t)
  | k, .letE c r t v b => .letE c r (liftTerm byN k t) (liftTerm byN k v) (liftTerm byN (k + 1) b)
  | k, .proj s i e => .proj s i (liftTerm byN k e)

def substTerm (arg : Term) : Nat → Term → Term
  | _, .sort u => .sort u
  | _, .const c us => .const c us
  | _, .natLit n => .natLit n
  | _, .strLit s => .strLit s
  | k, .var i =>
    if i == k then liftTerm k 0 arg
    else if i > k then .var (i - 1)
    else .var i
  | k, .app f a m r => .app (substTerm arg k f) (substTerm arg k a) m r
  | k, .lam b d t => .lam b (substTerm arg k d) (substTerm arg (k + 1) t)
  | k, .pi b r d t => .pi b r (substTerm arg k d) (substTerm arg (k + 1) t)
  | k, .letE c r t v b => .letE c r (substTerm arg k t) (substTerm arg k v) (substTerm arg (k + 1) b)
  | k, .proj s i e => .proj s i (substTerm arg k e)

def instUnivsTerm (us : List Univ) : Term → Term
  | .var i => .var i
  | .sort u => .sort (instUniv us u)
  | .const c vs => .const c (vs.map (instUniv us))
  | .app f a m r => .app (instUnivsTerm us f) (instUnivsTerm us a) m r
  | .lam b d t => .lam b (instUnivsTerm us d) (instUnivsTerm us t)
  | .pi b r d t => .pi b r (instUnivsTerm us d) (instUnivsTerm us t)
  | .letE c r t v b => .letE c r (instUnivsTerm us t) (instUnivsTerm us v) (instUnivsTerm us b)
  | .proj s i e => .proj s i (instUnivsTerm us e)
  | .natLit n => .natLit n
  | .strLit s => .strLit s

def betaApps : Term → List (Term × Mode × Rel) → Term
  | t, [] => t
  | .lam _ _ body, (a, _, _) :: rest => betaApps (substTerm a 0 body) rest
  | t, args => Term.mkApps t args

def whnfType (p : Program) : Nat → Term → Term
  | 0, t => t
  | fuel + 1, .letE _ _ _ v body => whnfType p fuel (substTerm v 0 body)
  | fuel + 1, t =>
    let (head, args) := t.spine
    match head with
    | .lam .. =>
      if args.isEmpty then t
      else whnfType p fuel (betaApps head args)
    | .const c us =>
      match p.decl? c with
      | some (.defn .defn .safe _ _ val) =>
        whnfType p fuel (betaApps (instUnivsTerm us val) args)
      | _ => t
    | _ => t

def isTypeFormerP (p : Program) (ctx : List (Term × Option Univ)) : Nat → Term → Bool
  | 0, _ => false
  | fuel + 1, t =>
    match whnfType p 8 t with
    | .sort _ => true
    | .pi _ _ d body => isTypeFormerP p ((d, none) :: ctx) fuel body
    | _ => false

def applyPis (p : Program) : Nat → Term → List Term.Arg → Option Univ
  | 0, _, _ => none
  | _ + 1, .sort u, [] => some u
  | k + 1, .pi _ _ _ body, (a, _, _) :: rest =>
    applyPis p k (substTerm a 0 body) rest
  | k + 1, ty, rest =>
    let ty' := whnfType p 4 ty
    if ty' == ty then none else applyPis p k ty' rest

def univClosed : Univ → Bool
  | .zero => true
  | .succ u => univClosed u
  | .max a b | .imax a b => univClosed a && univClosed b
  | .var _ => false

/-- The sort of a fully applied structure field whose type ends in a closed sort.
Only closed sorts qualify: a field's universe parameters are the structure's,
which a projection does not name. -/
def projFieldSort? (p : Program) (s i nargs : Nat) : Option Univ := do
  let k ← onlyCtor? p s
  let .ctor _ _ _ _ np _ cty ← p.decl? k | none
  let (_, fieldTy) ← cty.pis.1[np + i]?
  let (ps, concl) := fieldTy.pis
  let .sort u := concl | none
  if ps.length == nargs && univClosed u then some u else none

def inferTypeSort (p : Program) (ctx : List (Term × Option Univ)) : Nat → Term → Option Univ
  | 0, _ => none
  | fuel + 1, t =>
    match t with
    | .sort u => some (.succ u)
    | .pi _ _ d body => do
      let s1 ← inferTypeSort p ctx fuel d
      let dSort : Option Univ :=
        match (whnfType p 8 d).pis.2 with
        | .sort u => some u
        | _ => none
      let s2 ← inferTypeSort p ((d, dSort) :: ctx) fuel body
      some (.imax s1 s2)
    | .letE _ _ _ v body => inferTypeSort p ctx fuel (substTerm v 0 body)
    | _ =>
      let (head, args) := t.spine
      match head with
      | .var idx =>
        match ctx[idx]? with
        | some (varTy, u?) =>
          if args.isEmpty then u?
          else applyPis p 16 (liftTerm (idx + 1) 0 varTy) args
        | _ => none
      | .const c us =>
        match p.decl? c with
        | some d =>
          let (pis, concl) := d.type.pis
          match concl with
          | .sort u =>
            if args.length == pis.length then some (instUniv us u)
            else
              match d with
              | .defn .defn .safe _ _ val =>
                inferTypeSort p ctx fuel (betaApps (instUnivsTerm us val) args)
              | _ => none
          | _ =>
            match d with
            | .defn .defn .safe _ _ val =>
              inferTypeSort p ctx fuel (betaApps (instUnivsTerm us val) args)
            | _ => none
        | none => none
      | .proj s i _ => projFieldSort? p s i args.length
      | _ => none

def classifyDomain (p : Program) (ctx : List (Term × Option Univ)) (b : Binder) (dom : Term) : Option Rel :=
  match inferTypeSort p ctx 16 dom with
  | some s =>
    let w := (zeroCond s).dedup
    if w != .never then some (.proof w)
    else if isTypeFormerP p ctx 16 dom then some .type
    else if b.contract.uses == .erased then some .type
    else some .rel
  | none =>
    if b.contract.uses == .erased then some .type else none

def classifyTelescope (p : Program) (ctx : List (Term × Option Univ)) :
    Nat → Term → List (Binder × Option Rel) × Option Rel
  | 0, _ => ([], none)
  | fuel + 1, .pi b _ d body =>
    let r := classifyDomain p ctx b d
    let dSort : Option Univ :=
      match (whnfType p 8 d).pis.2 with
      | .sort u => some u
      | _ => none
    let (rs, concl) := classifyTelescope p ((d, dSort) :: ctx) fuel body
    ((b, r) :: rs, concl)
  | _ + 1, concl =>
    ([], classifyDomain p ctx {} concl)

/-- Whether a certificate's class for a position agrees with the declaration
types. A binder written `erased` must be irrelevant (C0 fixes that per instance,
so any irrelevant class will do). Where the position cannot be classified, an
irrelevant tag needs another justification: `covered` says C1 or C2 already
constrains it; otherwise it must be relevant. -/
def tagOk (b : Binder) (exp? : Option Rel) (covered : Bool) (actual : Rel) : Bool :=
  actual != .proof .never &&
    if b.contract.uses == .erased then actual.alwaysIrr
    else
      match exp? with
      | some exp => actual == exp
      | none => covered || actual == .rel

/-- The argument tags of a spine. C2 also compares the first `covered` arguments
with a checked record (a constant's parameter classes, a β-redex's binders); past
those, only the argument's type can justify an irrelevant tag. -/
def checkSpineArgs (p : Program) (ctx : List (Term × Option Univ)) :
    Nat → Term → List Term.Arg → Bool
  | _, _, [] => true
  | covered, fnTy, (a, _, r) :: rest =>
    match whnfType p 8 fnTy with
    | .pi b _ d body =>
      let b' : Binder := if covered > 0 then b else {}
      tagOk b' (classifyDomain p ctx b' d) (covered > 0) r &&
        checkSpineArgs p ctx (covered - 1) (substTerm a 0 body) rest
    | _ =>
      (covered > 0 || r == .rel) && checkSpineArgs p ctx (covered - 1) fnTy rest

/-- All arguments relevant: for heads whose callee is unknown here and which C2
does not constrain (projections, `let`s). -/
def argsRelevant (args : List Term.Arg) : Bool :=
  args.all fun (_, _, r) => r == .rel

def peelSubstPis (p : Program) : List Term → Term → Option Term
  | [], ty =>
    match whnfType p 8 ty with
    | .pi _ _ d _ => some d
    | _ => none
  | a :: rest, ty =>
    match whnfType p 8 ty with
    | .pi _ _ _ body => peelSubstPis p rest (substTerm a 0 body)
    | _ => none

def applyTypeArgs (p : Program) : Term → List Term.Arg → Option Term
  | ty, [] => some ty
  | ty, (a, _, _) :: rest =>
    match whnfType p 8 ty with
    | .pi _ _ _ body => applyTypeArgs p (substTerm a 0 body) rest
    | _ => none

def inferSimpleType (p : Program) (ctx : List (Term × Option Univ)) : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, .letE _ _ _ v body => inferSimpleType p ctx fuel (substTerm v 0 body)
  | fuel + 1, t =>
    let (head, args) := t.spine
    let headTy? : Option Term :=
      match head with
      | .var idx => ctx[idx]?.map fun (varTy, _) => liftTerm (idx + 1) 0 varTy
      | .const c us => (p.decl? c).map fun d => instUnivsTerm us d.type
      | .proj s i e => do
        let k ← onlyCtor? p s
        let .ctor _ lvls _ _ np nf ctorTy ← p.decl? k | none
        if i ≥ nf then none else
        let flds := (List.range i).map (Term.proj s · e)
        match inferSimpleType p ctx fuel e with
        | some eTy =>
          let (sHead, sArgs) := (whnfType p 8 eTy).spine
          match sHead with
          | .const s' us =>
            if s' == s && sArgs.length ≥ np then
              peelSubstPis p ((sArgs.take np).map (·.1) ++ flds) (instUnivsTerm us ctorTy)
            else if lvls == 0 then
              peelSubstPis p (List.replicate np (.natLit 0) ++ flds) ctorTy
            else none
          | _ =>
            if lvls == 0 then peelSubstPis p (List.replicate np (.natLit 0) ++ flds) ctorTy
            else none
        | none =>
          if lvls == 0 then peelSubstPis p (List.replicate np (.natLit 0) ++ flds) ctorTy
          else none
      | _ => none
    match headTy? with
    | some hTy => applyTypeArgs p hTy args
    | none => none

/-- Arguments of a β-redex against its leading λ binders. -/
def checkBetaArgs (p : Program) (ctx : List (Term × Option Univ)) :
    Term → List Term.Arg → Bool
  | _, [] => true
  | .lam b d body, (a, _, r) :: rest =>
    tagOk b (classifyDomain p ctx b d) false r &&
      checkBetaArgs p ctx (substTerm a 0 body) rest
  | _, _ => false

/-- Arguments left over after a β-redex's binders are consumed: C2 covers only the
binders, so they are judged against the head the reduced body applies. `inner`
counts as covered because the body's own walk already checks those arguments. -/
def checkReducedSpine (p : Program) (ctx : List (Term × Option Univ)) (t : Term)
    (extra : List Term.Arg) : Bool :=
  extra.isEmpty ||
    let (head, inner) := t.spine
    match head with
    | .const c us =>
      match p.decl? c with
      | some d => checkSpineArgs p ctx inner.length (instUnivsTerm us d.type) (inner ++ extra)
      | none => false
    | .var idx =>
      match ctx[idx]? with
      | some (varTy, _) => checkSpineArgs p ctx inner.length (liftTerm (idx + 1) 0 varTy) (inner ++ extra)
      | none => false
    | .proj s i e =>
      match inferSimpleType p ctx 8 (.proj s i e) with
      | some fieldTy => checkSpineArgs p ctx inner.length fieldTy (inner ++ extra)
      | none => argsRelevant extra
    | _ => argsRelevant extra

def checkTermBinders (p : Program) (ann : Ann) (ctx : List (Term × Option Univ)) :
    Term → List Term.Arg → Bool
  | .app f a m r, args =>
    let okA := if r.alwaysIrr then true else checkTermBinders p ann ctx a []
    okA && checkTermBinders p ann ctx f ((a, m, r) :: args)
  | .lam b d body, args =>
    let n := (lamRels (.lam b d body)).length
    let okSpine := checkBetaArgs p ctx (.lam b d body) (args.take n) &&
      checkReducedSpine p ctx (betaApps (.lam b d body) (args.take n)) (args.drop n)
    let okB := tagOk b (classifyDomain p ctx b d) false b.rel
    let dSort : Option Univ :=
      match (whnfType p 8 d).pis.2 with
      | .sort u => some u
      | _ => none
    if b.propWhen == .always then okSpine && okB
    else okSpine && okB && checkTermBinders p ann ((d, dSort) :: ctx) body []
  | .letE lc r ty val body, args =>
    let lb : Binder := { contract := lc.binder }
    let okR := tagOk lb (classifyDomain p ctx lb ty) false r
    let tySort : Option Univ :=
      match (whnfType p 8 ty).pis.2 with
      | .sort u => some u
      | _ => none
    let okVal := if r.alwaysIrr then true else checkTermBinders p ann ctx val []
    argsRelevant args && okR && okVal && checkTermBinders p ann ((ty, tySort) :: ctx) body []
  | .const c us, args =>
    match p.decl? c with
    | some d =>
      let covered := ((ann.constRel? c).map (·.params.length)).getD 0
      checkSpineArgs p ctx covered (instUnivsTerm us d.type) args
    | none => false
  | .var idx, args =>
    match ctx[idx]? with
    | some (varTy, _) => checkSpineArgs p ctx 0 (liftTerm (idx + 1) 0 varTy) args
    | none => false
  | .proj s i e, args =>
    let okArgs :=
      if args.isEmpty then true
      else match inferSimpleType p ctx 8 (.proj s i e) with
        | some fieldTy => checkSpineArgs p ctx 0 fieldTy args
        | none => argsRelevant args
    okArgs && checkTermBinders p ann ctx e []
  | _, args => argsRelevant args

/-- The run bodies `c` is compiled by: its equation's body, or its value (a
safe definition, or an opaque on the allowlist); none for another special head. -/
def runBodies (p : Program) (c : CId) : List (TermKey × Term) :=
  match p.table.resolveOf c with
  | some (.eqn _ body) => [(.eqn c, body)]
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => [(.value c, v)]
    | some (.defn .opaq .safe _ _ v) => if p.table.isOpaqueByValue c then [(.value c, v)] else []
    | _ => []
  | _ => []

/-- The positions of a type's leading Π telescope written erased (`0`): the
arguments every caller drops (`KernelFront.erasedAt`, C2 against the
constant's parameter classes). -/
def erasedParams (ty : Term) : List Nat :=
  (ty.pis.1.zipIdx.filter fun ((b, _), _) => b.contract.uses == .erased).map (·.2)

/-- Whether firing special head `h` reads its argument `i`: `Lam.Erase.headReads`
over the declarations `decl?` and the resolution `resolve?`, copied here because
the relevance check comes before Lam; `IxCCTests.Src.Relevance.Checker` does not
build if the two differ. -/
def headReadsWith (decl? : CId → Option Decl) (resolve? : CId → Option Resolve) :
    Head → Nat → Bool
  | .ctor c, i =>
    match decl? c with
    | some (.ctor _ _ _ _ np _ _) => np ≤ i
    | _ => true
  | .quotMk _, i => i == 2
  | .quotLift _, i => i == 3 || i == 5
  | .recr _, _ => true
  | .cases c, i =>
    match resolve? c with
    | some (.case r) =>
      match decl? r with
      | some (.recr _ _ _ np _ _ _ _ _ _) => np + 1 ≤ i
      | _ => true
    | _ => true
  | .prim _, _ => true
  | .word .., _ => true

/-- The special head `c` is, as SrcEval's δ dispatches it (`evalConst`, E8): a
`prim`, `word` or `case` entry, else a constructor, recursor or quotient
declaration. -/
def specialHead? (p : Program) (c : CId) : Option Head :=
  match p.table.resolveOf c with
  | some (.prim op) => some (.prim op)
  | some (.word w op _) => some (.word w op)
  | some (.case _) => some (.cases c)
  | some _ => none
  | none =>
    match p.decl? c with
    | some (.ctor ..) => some (.ctor c)
    | some (.recr ..) => some (.recr c)
    | some (.quot .ctor ..) => some (.quotMk c)
    | some (.quot .lift ..) => some (.quotLift c)
    | _ => none

/-- The number of arguments special head `h` fires at: SrcEval's `Program.headArity`,
copied here because the relevance check comes before the evaluator
(`IxCC.Src.Relevance.Proof.headArityOf_eq` proves the two equal). -/
def headArityOf (p : Program) : Head → Nat
  | .ctor c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np nf _) => np + nf
    | _ => 0
  | .quotMk _ => 3
  | .quotLift _ => 6
  | .recr r => ((p.decl? r).bind Decl.recArity).getD 0
  | .cases c =>
    match p.table.resolveOf c with
    | some (.case r) =>
      match p.decl? r with
      | some (.recr _ _ _ np _ nmin ni _ _ _) => np + 1 + ni + 1 + nmin
      | _ => 0
    | _ => 0
  | .prim op => op.arity
  | .word _ op => op.arity

/-- What special head `h` (the run behaviour of `c`) reads at argument `i`:
`headReadsWith`, except a constructor field dropped at every instance, which a
constructor does not store (`Lam.Erase.ctorForm`; SrcEval stores the `irr` it is
given), and with the pinned `Nat.succ`, which reads its field always. A position
at or past the head's arity is read: the head fires before it, and the value it
fires to receives that argument as any function would (`Quot.lift` fires to its
function's result; an argument the type writes erased there would reach that
result as `irr`). -/
def readsAt (p : Program) (ann : Ann) (c : CId) (h : Head) (i : Nat) : Bool :=
  decide (headArityOf p h ≤ i) ||
  (headReadsWith p.decl? p.table.resolveOf h i &&
    match h, p.decl? c with
    | .ctor _, some (.ctor _ _ _ _ np _ _) =>
      some c == p.known.natSucc ||
        !((((ann.ctorRel? c).bind (·.fields[i - np]?)).map FieldClass.alwaysDropped).getD false)
    | _, _ => true)

/-- Argument `pos` of `c` is one its special head forces and applies: a `case` key's minor (F5
applies minor `j` to the fields) or `Quot.lift`'s function (F8 applies it to the element). A
marker there would be applied (stuck) or returned (F5 on a constructor with no fields), so such a
position must be relevant at every instance the head is reached at. -/
def appliedAt (p : Program) (c : CId) (pos : Nat) : Bool :=
  match specialHead? p c with
  | some (.cases _) =>
    match p.table.resolveOf c with
    | some (.case r) =>
      match p.decl? r with
      | some (.recr _ _ _ np _ nmin ni _ _ _) => np + 1 + ni + 1 ≤ pos && pos < np + 1 + ni + 1 + nmin
      | _ => false
    | _ => false
  | some (.quotLift _) => pos == 3
  | _ => false

def headName : Head → String
  | .ctor _ => "the constructor"
  | .quotMk _ => "Quot.mk"
  | .quotLift _ => "Quot.lift"
  | .recr _ => "the recursor (its rules receive every argument)"
  | .cases _ => "its case entry (the recursor's dispatch)"
  | .prim op => s!"the primitive Nat.{op.name}"
  | .word w op => s!"the word operation {op.leanName w}"

/-- Who reads argument `i` of special head `h`: the head, or (at or past its
arity) the value it fires to. -/
def readerName (p : Program) (h : Head) (i : Nat) : String :=
  if headArityOf p h ≤ i then
    s!"the value {headName h} fires to (it is at or past the arity {headArityOf p h})"
  else headName h

/-- A constant whose run behaviour is a special head: the positions its type
writes erased are disjoint from those the head reads. `none` when they are;
otherwise the first position both erased and read. -/
def readsErased? (p : Program) (ann : Ann) (c : CId) : Option String := do
  let h ← specialHead? p c
  let d ← p.decl? c
  let i ← (erasedParams d.type).find? (readsAt p ann c h)
  some s!"parameter {i} is written erased, but {readerName p h i} reads it"

/-- Whether de Bruijn variable `k` occurs in `t` (structural). -/
def mentionsVar : Nat → Term → Bool
  | k, .var i => i == k
  | k, .app f a _ _ => mentionsVar k f || mentionsVar k a
  | k, .lam _ d b => mentionsVar k d || mentionsVar (k + 1) b
  | k, .pi _ _ d b => mentionsVar k d || mentionsVar (k + 1) b
  | k, .letE _ _ ty v b => mentionsVar k ty || mentionsVar k v || mentionsVar (k + 1) b
  | k, .proj _ _ e => mentionsVar k e
  | _, _ => false

/-- A recursor's rules against its constructors' interfaces. A field its
constructor writes erased is dropped (`okCtors`), so its slot holds `irr` when
the rule runs (F2), and the rule may use it only where it is never read: as
that field's argument to the minor premise the rule dispatches, whose binder
for it C3 holds irrelevant at every call. Any other occurrence of the field's
variable in the stored rule term refuses, a type or an irrelevant argument
included; the major of an induction hypothesis is one (SrcEval would force
`irr` there; the hypothesis may be another member's recursor, whose C3 check
concerns that member's constructors). Decided on the rule term as stored, not
on the kernel's generated shape, which IxCC does not check. A rule that
dispatches no minor (`ruleDispatch`), or is not a λ over its parameters,
motives, minors and fields, or binds a number of fields other than its
constructor's (SrcEval passes as many as the constructor has), refuses when its
constructor writes any field erased. Fields dropped only by their sort are not written erased and are not
constrained here. `none` when every rule agrees; otherwise the first
disagreement. -/
def forwardsErased? (p : Program) (r : CId) : Option String := do
  let .recr _ _ _ np nmot nmin _ _ rules _ ← p.decl? r | none
  rules.zipIdx.findSome? fun (rule, k) =>
    -- SrcEval passes the constructor value's fields, as many as the constructor has
    let nf := match p.decl? rule.ctor with
      | some (.ctor _ _ _ _ _ nf _) => nf
      | _ => rule.fields
    match (List.range nf).filter (fieldWrittenErased p rule.ctor ·) with
    | [] => none
    | i₀ :: rest =>
      if nf != rule.fields then
        some s!"rule {k} of the recursor binds {rule.fields} fields, {p.short rule.ctor} has {nf} \
          and writes field {i₀} erased"
      else match peelLamsN (np + nmot + nmin + rule.fields) rule.rhs, ruleDispatch p r rule with
      | some body, some _ =>
        let (head, args) := body.spineL
        (i₀ :: rest).findSome? fun i =>
          let v := rule.fields - 1 - i
          let ok := !mentionsVar v head && args.zipIdx.all fun ((a, _, _), n) =>
            (n == i && a == Term.var v) || !mentionsVar v a
          if ok then none
          else some s!"rule {k} of the recursor uses field {i} of {p.short rule.ctor}, which is \
            written erased, other than as that field's argument to the minor premise it dispatches"
      | some _, none =>
        some s!"rule {k} of the recursor dispatches no minor premise, and {p.short rule.ctor} \
          writes field {i₀} erased"
      | none, _ =>
        some s!"rule {k} of the recursor is not a λ over its parameters, motives, minors and \
          fields, and {p.short rule.ctor} writes field {i₀} erased"

/-- A run body `t` (`what`, for the message) against the header of its
constant, whose type is `ty` and whose parameter classes are `params`. Its
leading λ telescope must cover every parameter written erased in `ty`, and
each covered λ must have its parameter's class. A caller drops the argument of
a parameter written erased (C2 holds it to `params`), so a body with fewer
leading λs, an η-short value, would be applied to □ where it may need a value.
Until the format change the certified kernel refused such a body, because its
conversion compared binder contracts; this check does not rely on that. A
parameter irrelevant only by its sort needs no λ: the callee's own header
classifies it from the same sort facts as the caller's. `none` when the body
agrees; otherwise the first disagreement. -/
def headerAgreement (ty t : Term) (params : List Rel) (what : String := "the body") :
    Option String :=
  let lams := lamRels t
  match (erasedParams ty).find? (lams.length ≤ ·) with
  | some i => some s!"parameter {i} is written erased, but {what} has {lams.length} leading λs \
      (η-short): {what} must bind every parameter up to the last one written erased"
  | none =>
    match (lams.zip params).zipIdx.find? (fun ((b, r), _) => b != r) with
    | some ((b, r), i) => some s!"the body's λ {i} is {relName b}, its parameter {relName r}"
    | none => none

/-- A `csimp` redirect of `c` to an eliminator with a rule for a constructor that writes a field
erased (`erasedMinors`). The redirect is reached through the table, not a walked term, and the
subject is no eliminator to C3, so the minors its callers pass would meet no check (the
complement of `partialElim`, which sees the walked terms). `none` when `c` has no such
redirect. -/
def redirectsErased? (p : Program) (c : CId) : Option String :=
  match p.table.resolveOf c with
  | some (.csimp g _ _) =>
    match elimShape? p g with
    | some shape =>
      if erasedMinors p shape then
        some s!"the csimp redirect to {p.short g}, an eliminator over a constructor that writes a \
          field erased: the minor premises its callers pass would meet no check"
      else none
    | none => none
  | _ => none

/-! ### Structure the kernel ensures, checked here

Facts about the program's shape that relevance preservation reads and that erasure enforced only
where it erased (`ruleAlt`, `erase-univs`) or ingress ensured. Each is decided here so that the
relevance checks' facts do not rest on erasure's success or on ingress. -/

/-- Rule `j` of the recursor `r` is for constructor `j` of `r`'s inductive and binds as many
fields as that constructor has (erasure's `ruleAlt` test). SrcEval's F2 runs rule `cidx` on a
major built by constructor `cidx`, F5 applies minor `cidx` to its fields, and C3 and the
forwarding clause compare minor and rule with the rule's named constructor, so the two must be
one. `none` when every rule is; otherwise the first that is not. -/
def rulesShape? (p : Program) (r : CId) : Option String := do
  let .recr _ _ _ _ _ _ _ ind rules _ ← p.decl? r | none
  rules.zipIdx.findSome? fun (rule, j) =>
    match p.decl? rule.ctor with
    | some (.ctor _ _ ind' cidx _ nf _) =>
      if ind' == ind && cidx == j && nf == rule.fields then none
      else some s!"rule {j} of the recursor is not for constructor {j} of its inductive with \
        its fields ({p.short rule.ctor}: index {cidx}, {nf} fields; the rule binds {rule.fields})"
    | _ => some s!"rule {j} of the recursor is not for constructor {j} of its inductive: \
        {p.short rule.ctor} is no constructor"

/-- The universe-argument counts of a runtime term (erasure's `erase-univs` test): every
constant in a position relevant at some profile has at most as many universe arguments as its
declaration has universe parameters, so the levels SrcEval instantiates at a reference agree with
the profile the checks decide the callee at (`Erase.Proof.Agree.inst`). Deliberately not every
position: an argument or a `let` irrelevant at every profile (a type, a proof), a λ's domain, a Π
and a `let`'s type are never evaluated, so a count there matters neither to SrcEval nor to
erasure, and the walk does not look into the proofs and types only the kernel checks. -/
def univsOk (p : Program) : Term → Bool
  | .const c us => decide (us.length ≤ ((p.decl? c).map Decl.lvls).getD 0)
  | .app f a _ r => univsOk p f && (r.alwaysIrr || univsOk p a)
  | .lam _ _ t => univsOk p t
  | .letE _ r _ v b => (r.alwaysIrr || univsOk p v) && univsOk p b
  | .proj _ _ e => univsOk p e
  | _ => true

/-- `univsOk` on the runtime terms of `c` and on its `csimp` redirect's target. -/
def univsErrs (p : Program) (c : CId) : List RelError :=
  let terms := (p.runtimeKeys c).filterMap fun key =>
    match p.termOf key with
    | some t =>
      if univsOk p t then none
      else some (RelError.of "S1" "a constant has more universe arguments than its declaration \
        has universe parameters" (some c) (some key))
    | none => none
  let redirect := match p.table.resolveOf c with
    | some (.csimp g us _) =>
      if univsOk p (.const g us) then []
      else [RelError.of "S1" s!"the csimp redirect gives {p.short g} more universe arguments than \
        its declaration has universe parameters" (some c)]
    | _ => []
  terms ++ redirect

/-- A subsingleton recursor (F3) passes its rule one field slot per source of its kind
(`RecKind.subsingleton`), which must be as many as the fields of the constructor of its rule 0
(the forwarding clause and C3 speak of that many). `Table.deriveRecKind` builds the sources that
way; this decides it of the table the program carries. `none` when it holds. -/
def subsingletonSrcs? (p : Program) (r : CId) : Option String :=
  match p.decl? r, p.table.recKindOf r with
  | some (.recr _ _ _ _ _ _ _ _ rules _), some (.subsingleton _ srcs) =>
    match rules[0]? with
    | some rule =>
      let nf := match p.decl? rule.ctor with
        | some (.ctor _ _ _ _ _ nf _) => nf
        | _ => rule.fields
      if srcs.length == nf then none
      else some s!"the subsingleton recursor takes {srcs.length} field sources, and the \
        constructor of its rule has {nf} fields"
    | none => none
  | _, _ => none

/-- `c` is a constructor of exactly `n` fields. F6w builds `Fin.mk`'s value with two fields
(`Program.mkWord?`) whatever the pinned declaration says, and F2 binds a rule's field λs by the
value's field count. -/
def ctorFieldsIs (p : Program) (c : CId) (n : Nat) : Bool :=
  match p.decl? c with
  | some (.ctor _ _ _ _ _ nf _) => nf == n
  | _ => false

end Check.Canonical

open Check Check.Canonical in
/-- Verify that the relevance certificate's parameter counts, constant/constructor
records, and runtime binder/argument classifications match the canonical
re-derivation from the declaration types in `p`, and that at every reached
constant the arguments a caller drops (the parameters its type writes erased)
are ones its run behaviour never reads: its run bodies and a csimp redirect
cover them with λs of their classes (`headerAgreement`), and a special head
does not read them (`readsErased?`); and that a reached recursor's rules use a
field its constructor writes erased only as that field's argument to the minor
they dispatch (`forwardsErased?`). Minor premises are held to the same rule by
C3 (`Check.minorBinders`), which sees them only at a saturated spine; a `csimp`
redirect to an eliminator with a rule for a constructor writing a field erased
is refused (`redirectsErased?`), as C3 refuses such an eliminator's partial and
bare occurrences in the walked terms (`Check.partialElim`). And the structure
the kernel ensures that relevance preservation reads, which erasure enforced
only where it erased or ingress ensured: no constant or table entry at or above
the program's size; rule `j` of a reached eliminator's recursor is for
constructor `j` (`rulesShape?`); universe-argument counts (`univsOk`); a record
for every reached constructor; F3's field sources as many as the rule's
constructor's fields (`subsingletonSrcs?`); and, at a reached word entry, the
pinned `Fin.mk` drops its proof field. -/
def checkCanonical (p : Program) (ann : Ann) (ch : Checked) : List RelError :=
  let okConsts := ann.consts.toList.all fun (c, cr) =>
    match p.decl? c with
    | some d =>
      let (ps, res) := classifyTelescope p [] (d.type.piCount + 1) d.type
      let okPrim := match p.table.resolveOf c with
        | some (.prim op) => cr.result == .rel && cr.params == List.replicate op.arity .rel
        | some (.word _ op _) => cr.result == .rel && cr.params == List.replicate op.arity .rel
        | _ => true
      okPrim &&
      cr.params.length == ps.length &&
      (cr.params.zip ps).all (fun (actual, (b, exp)) =>
        tagOk b exp false actual) &&
      (match res with | some e => cr.result == e | none => cr.result == .rel)
    | none => false
  let okCtors := ann.ctors.toList.all fun (c, kr) =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np nf ty) =>
      let (ps, _) := classifyTelescope p [] (ty.piCount + 1) ty
      let flds := ps.drop np
      let okWithConst := match ann.constRel? c with
        | some cr => (cr.params.drop np).map FieldClass.ofRel == kr.fields
        | none => true
      okWithConst &&
      kr.fields.length == nf &&
      flds.length == nf &&
      (kr.fields.zip flds).all (fun (actual, (b, exp)) =>
        actual != .proof .never &&
          if b.contract.uses == .erased then actual.alwaysDropped
          else match exp with | some e => actual == FieldClass.ofRel e | none => actual == .keep)
    | _ => false
  -- A `csimp` redirect's run body is its target `g`, a body of no λ: refused
  -- when `c` writes a parameter erased (the strict form of "the two headers
  -- agree on every mode", which needs modes read from records).
  let headerErrs : List RelError := ch.reached.flatMap fun c =>
    match ann.constRel? c, p.decl? c with
    | some cr, some d =>
      let redirect := match p.table.resolveOf c with
        | some (.csimp g us _) =>
          (headerAgreement d.type (.const g us) cr.params s!"the csimp redirect to {p.short g}").toList.map
            fun msg => RelError.of "S1" msg (some c)
        | _ => []
      redirect ++ (runBodies p c).filterMap fun (key, t) =>
        (headerAgreement d.type t cr.params).map fun msg => RelError.of "S1" msg none (some key)
    | _, _ => []
  -- A special head (a `case`, `prim` or `word` entry, a constructor, recursor
  -- or quotient) reads no argument its type writes erased.
  let readErrs : List RelError := ch.reached.filterMap fun c =>
    (readsErased? p ann c).map fun msg => RelError.of "S1" msg (some c)
  -- A recursor's rule uses a field its constructor writes erased only as that
  -- field's argument to the minor it dispatches.
  let forwardErrs : List RelError := ch.reached.filterMap fun c =>
    (forwardsErased? p c).map fun msg => RelError.of "S1" msg (some c)
  -- A `csimp` redirect to an eliminator whose minors C3 must see: refused (C3 sees
  -- only walked terms; `partialElim` refuses the partial and bare occurrences there).
  let redirectErrs : List RelError := ch.reached.filterMap fun c =>
    (redirectsErased? p c).map fun msg => RelError.of "C3" msg (some c)
  let okReached := ch.reached.all fun c =>
    match ann.constRel? c with
    | none => false
    | some _ =>
      let ruleTerms : List Term :=
        match p.decl? c with
        | some (.recr _ _ _ _ _ _ _ _ rules _) => rules.map (·.rhs)
        | _ => []
      ((runBodies p c).all fun (_, t) => checkTermBinders p ann [] t []) &&
      (ruleTerms.all fun t => checkTermBinders p ann [] t [])
  -- No constant and no table entry at or above `size`: the closure loop skips an
  -- instance there (`Handled`), so SrcEval must find none.
  let denseErrs : List RelError :=
    if p.consts.toList.all (·.1 < p.size) && p.table.resolve.toList.all (·.1 < p.size) then []
    else [RelError.of "S1" "a constant or table entry at or above the program's size: the \
      closure walk skips it, and SrcEval would run it unchecked"]
  -- Rule `j` of a reached eliminator's recursor is for constructor `j` (erasure's `ruleAlt`).
  let ruleErrs : List RelError := ch.reached.filterMap fun c =>
    match elimShape? p c with
    | some shape => (rulesShape? p shape.recr).map fun msg => RelError.of "S1" msg (some shape.recr)
    | none => none
  -- Universe-argument counts at the constants SrcEval may evaluate (erasure's `erase-univs`).
  let univErrs : List RelError := ch.reached.flatMap (univsErrs p)
  -- A reached constructor has a record (unannotated, every field would read as kept).
  let recordErrs : List RelError := ch.reached.filterMap fun c =>
    match p.decl? c, ann.ctorRel? c with
    | some (.ctor ..), none =>
      some (RelError.of "S1" "a reached constructor without a constructor record" (some c))
    | _, _ => none
  -- F3's field sources are as many as the fields of the rule's constructor.
  let srcsErrs : List RelError := ch.reached.filterMap fun c =>
    match elimShape? p c with
    | some shape =>
      (subsingletonSrcs? p shape.recr).map fun msg => RelError.of "S1" msg (some shape.recr)
    | none => none
  -- F6w builds a word's tower with `irr` as `Fin.mk`'s proof field and with two fields: the
  -- pinned `Fin.mk` is a constructor of two fields and drops the proof field at the empty profile
  -- wherever a word entry is reached.
  let finErrs : List RelError := ch.reached.filterMap fun c =>
    match p.table.resolveOf c, p.known.finMk with
    | some (.word ..), some fin =>
      if !Check.Canonical.ctorFieldsIs p fin 2 then
        some (RelError.of "S1" "a word operation builds Fin.mk's value with two fields, but the \
          pinned Fin.mk is not a constructor of two fields" (some fin))
      else if ch.keepsP fin [] 1 then
        some (RelError.of "S1" "a word operation builds its tower with `irr` as Fin.mk's proof \
          field, which the pinned Fin.mk's record keeps at the empty profile" (some fin))
      else none
    | _, _ => none
  -- F5 applies a `case` key's minor and F8 `Quot.lift`'s function: at every reached instance of
  -- such a head, those positions are relevant (a marker there is irrelevant by its sort, never
  -- written erased, since the head reads them).
  let appliedErrs : List RelError := ch.instances.filterMap fun (c, q) =>
    match ann.constRel? c with
    | some cr =>
      (cr.params.zipIdx.find? fun (r, pos) => appliedAt p c pos && r.irrP q).map fun (r, pos) =>
        RelError.of "S1" s!"argument {pos} is forced and applied (a case key's minor, Quot.lift's \
          function), but its class ({relName r}) is irrelevant at a reached instance" (some c)
    | none => none
  readErrs ++ forwardErrs ++ redirectErrs ++ headerErrs ++ denseErrs ++ ruleErrs ++ univErrs ++
    recordErrs ++ srcsErrs ++ finErrs ++ appliedErrs ++
    if okConsts && okCtors && okReached then []
    else [RelError.of "S1" "non-canonical relevance annotation"]

end IxCC.Src.Relevance
