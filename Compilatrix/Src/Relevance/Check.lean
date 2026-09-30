import Compilatrix.Src.Relevance.Syntax
import Compilatrix.Src.NatMap

/-! # The relevance checker

Decides an installed annotation (design note 02 §3.3) in one pass over the
runtime closure, level-exact (D18): the closure is a set of *instances*
`(constant, profile)`, reached from the roots at the empty profile through
positions relevant at the reaching instance's profile (`Src.Runtime`), and
every rule is decided at the instance's profile. It is executable here; its
theorems (`check_sound`, `check_consistent`) are M2 items. The checker reads
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
  replaces M1.F2's one-way rule, under which `Function.comp` at `Sort 0`
  received □ in a parameter its body treats as relevant. It also rejects a
  *type* passed to a relevant parameter of a type-polymorphic callee, which
  no universe condition covers and which SrcEval gets stuck on if the callee
  applies it. The same holds between a β-redex's arguments and its λ
  binders (`have` and `let_fun` elaborate to such redexes).
* C3 fields dropped at the constructor's profile are bound by irrelevant
  minor binders; a projection in a relevant position does not read a field
  dropped at every instance (a projection carries no universe arguments, so
  the structure's profile is not known there).
* C4 a saturated eliminator whose major is irrelevant is a subsingleton or
  empty eliminator at its profile.
* C5 relevant positions reference only constants whose result is relevant
  at the callee's profile.
* C6 a λ in a relevant position is not a proof at the instance (so SrcEval's
  β guard, rule A1, never fires on it).

**Style (D17).** The closure loop, the term walk and the per-instance rules
recurse structurally (the loop on a fuel), keep their state in lists and a
persistent `NatMap`, and index no array on the hot path. The `Program` and
`Ann` tables they consult are still arrays (M1.K1). -/

namespace Compilatrix.Src.Relevance

structure RelError where
  /-- `S1`–`S4` or `C0`–`C6`. -/
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
  let .induct _ _ np _ ty ctors ← p.decl? t | none
  unless ctors.size == 1 do none
  let k ← ctors[0]?
  let rel ← ctorRel? k
  let kept := (rel.fields.zipIdx).filter fun (c, _) => !c.dropP prof
  unless kept.size == 1 do none
  let j := kept[0]!.2
  let resultProp := match ty.pis.2 with
    | .sort .zero => true
    | _ => false
  if resultProp then none
  let .ctor _ _ _ _ _ _ cty ← p.decl? k | none
  let (_, fieldTy) ← cty.pis.1[np + j]?
  if fieldTy.mentions t then none
  return j

/-- The checker's verdict: the runtime closure with its records. -/
structure Checked where
  keys : Array TermKey
  /-- Distinct reached constants, in discovery order. -/
  reached : Array CId
  /-- Every reached instance `(constant, profile)`, in discovery order. -/
  instances : Array Inst
  consts : Array (Option ConstRel)
  ctors : Array (Option CtorRel)
  deriving Inhabited

namespace Checked

def ctorRel? (c : Checked) (k : CId) : Option CtorRel := (c.ctors[k]?).join
def constRel? (c : Checked) (k : CId) : Option ConstRel := (c.consts[k]?).join

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
def profileSplit (c : Checked) : Array CId :=
  c.reached.filter fun k => (c.instances.filter (·.1 == k)).size > 1

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

def relOk (lvls : Nat) (r : Rel) : Bool := pwOk lvls r.irrWhen

def relName : Rel → String
  | .rel => "relevant"
  | .proof w => s!"proof ({repr w})"
  | .type => "type"

/-- The single constructor of a structure-like inductive. -/
def onlyCtor? (p : Program) (s : CId) : Option CId :=
  match p.decl? s with
  | some (.induct _ _ _ _ _ ctors) => if ctors.size == 1 then ctors[0]? else none
  | _ => none

/-- Positional roles of a saturated eliminator spine: minors with their rule
index, the major position, and the recursor. A `case` key has the
recursor's universe parameters (`Table.checkCase`), so both are decided at
the head's profile. -/
structure ElimShape where
  recr : CId
  minors : List (Nat × Nat)
  major : Nat
  arity : Nat

def elimShape? (p : Program) (c : CId) : Option ElimShape :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ np _ nmin ni _ _ _) =>
      some { recr := r, minors := (List.range nmin).map fun j => (np + 1 + ni + 1 + j, j)
             major := np + 1 + ni, arity := np + 1 + ni + 1 + nmin }
    | _ => none
  | none =>
    match p.decl? c with
    | some (.recr _ _ _ np nmot nmin ni _ _ _) =>
      some { recr := c, minors := (List.range nmin).map fun j => (np + nmot + j, j)
             major := np + nmot + nmin + ni, arity := np + nmot + nmin + ni + 1 }
    | _ => none
  | _ => none

/-- Field classes of the constructor selected by rule `j` of `r`. -/
def ruleCtorFields (p : Program) (ann : Ann) (r : CId) (j : Nat) :
    Option (CId × Array FieldClass) := do
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

/-- C3 over a minor's binders at the constructor's profile `qc`. -/
def minorBinders (ctx : Ctx) (k : CId) (j : Nat) (qc : Profile) :
    Nat → List Rel → List FieldClass → List RelError → List RelError
  | i, b :: bs, cls :: fields, errs =>
    let errs :=
      if cls.dropP qc && !b.irrP ctx.prof then
        err ctx "C3" s!"minor {j} binds dropped field {i} relevantly" (some k) :: errs
      else errs
    minorBinders ctx k j qc (i + 1) bs fields errs
  | _, _, _, errs => errs

/-- Rules at a constant head: C2, S2, and C3/C4 at saturated eliminators. -/
def knownHead (ctx : Ctx) (errs : List RelError) (c : CId) (us : List Ixon.Univ)
    (args : List Term.Arg) : List RelError :=
  let p := ctx.p
  let q := ctx.prof.inst us
  let errs := match ctx.ann.constRel? c with
    | some rel => paramArgs ctx c q args rel.params.toList errs
    | none => errs
  let errs := match p.decl? c, ctx.ann.ctorRel? c with
    | some (.ctor _ _ _ _ np _ _), some rel => fieldArgs ctx c q 0 (args.drop np) rel.fields.toList errs
    | some (.ctor ..), none => err ctx "S1" "constructor without a record" (some c) :: errs
    | _, _ => errs
  match elimShape? p c with
  | none => errs
  | some shape =>
    if args.length < shape.arity then errs else
    let kind := ((p.table.recKindOf shape.recr).map (fun k => RecKind.atProfile q k)).getD .ordinary
    let errs := match args[shape.major]? with
      | some (_, _, a) =>
        if a.irrP ctx.prof && !kind.allowsIrrMajor then
          err ctx "C4" "an ordinary eliminator with an irrelevant major" (some shape.recr) :: errs
        else errs
      | none => errs
    let qc := ctorProfile p shape.recr q
    shape.minors.foldl (init := errs) fun errs (pos, j) =>
      match args[pos]?, ruleCtorFields p ctx.ann shape.recr j with
      | some (minor, _, a), some (k, fields) =>
        if a.irrP ctx.prof then errs
        else minorBinders ctx k j qc 0 (lamRels minor) fields.toList errs
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

mutual

/-- Check the relevant positions of a term under binder classes `binders`
(innermost first). -/
def term (ctx : Ctx) (binders : List Rel) (errs : List RelError) : Term → List RelError
  | .var i =>
    match binders[i]? with
    | some r =>
      if r.irrP ctx.prof then err ctx "C1" s!"relevant use of a {relName r} binder (#{i})" :: errs
      else errs
    | none => err ctx "S1" s!"variable #{i} out of scope" :: errs
  | .const c us => constHead ctx c us errs
  | .lam b _ t =>
    let errs := if pwOk ctx.lvls b.propWhen && relOk ctx.lvls b.rel then errs
      else err ctx "S1" "a condition names a parameter beyond the constant's levels" :: errs
    let errs := if b.contract.uses == .erased && !b.rel.irrP ctx.prof then
        err ctx "C0" "a binder written erased is annotated relevant" :: errs
      else errs
    if b.propWhen.holdsP ctx.prof then
      err ctx "C6" "a λ in a relevant position is a proof at this instance" :: errs
    else term ctx (b.rel :: binders) errs t
  | .letE c r _ v b =>
    let errs := if relOk ctx.lvls r then errs
      else err ctx "S1" "a condition names a parameter beyond the constant's levels" :: errs
    let errs := if c.binder.uses == .erased && !r.irrP ctx.prof then
        err ctx "C0" "a let written erased is annotated relevant" :: errs
      else errs
    let errs := if r.irrP ctx.prof then errs else term ctx binders errs v
    term ctx (r :: binders) errs b
  | .proj s i e =>
    let errs := match onlyCtor? ctx.p s with
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
    term ctx binders errs e
  | .app f a m r =>
    let (head, args) := (Term.app f a m r).spineL
    let errs := match head with
      | .const c us => knownHead ctx errs c us args
      | .lam .. => lamHead ctx errs head args
      | _ => errs
    let errs := if relOk ctx.lvls r then errs
      else err ctx "S1" "a condition names a parameter beyond the constant's levels" :: errs
    let errs := rest ctx binders errs f
    if r.irrP ctx.prof then errs else term ctx binders errs a
  | _ => errs

/-- The rest of an application spine: its relevant arguments and its head. -/
def rest (ctx : Ctx) (binders : List Rel) (errs : List RelError) : Term → List RelError
  | .app f a _ r =>
    let errs := if relOk ctx.lvls r then errs
      else err ctx "S1" "a condition names a parameter beyond the constant's levels" :: errs
    let errs := rest ctx binders errs f
    if r.irrP ctx.prof then errs else term ctx binders errs a
  | h => term ctx binders errs h

end

/-- S4 at one recursor instance. -/
def subsingletonFields (p : Program) (ann : Ann) (r : CId) (q : Profile)
    (errs : List RelError) : List RelError :=
  match p.decl? r, (p.table.recKindOf r).map (fun k => RecKind.atProfile q k) with
  | some (.recr _ _ _ _ _ _ _ _ rules _), some (.subsingleton _ srcs) =>
    match rules[0]? with
    | some rule =>
      match ann.ctorRel? rule.ctor with
      | some rel =>
        let qc := ctorProfile p r q
        (rel.fields.toList.zipIdx).foldl (init := errs) fun errs (cls, j) =>
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

/-- Visit one new instance: check its runtime terms at its profile, and
return the instances they reach. `first` is the constant's first visit
(its keys are recorded once). -/
def visit (p : Program) (ann : Ann) (annotated : NatMap (List TermKey)) (c : CId)
    (prof : Profile) (lvls : Nat) (first : Bool) (s : St) : St × List Inst :=
  let marked := (annotated.get? c).getD []
  let s := if first && (ann.constRel? c).isNone then
      { s with errs := RelError.of "S1" "reached constant without a record" (some c) :: s.errs }
    else s
  let s := (p.runtimeKeys c).toList.foldl (init := s) fun s key =>
    if !marked.contains key then
      if first then
        { s with errs := RelError.of "S1" "runtime term not annotated" none (some key) :: s.errs }
      else s
    else
      let s := if first then { s with keys := key :: s.keys } else s
      match p.termOf key with
      | some t => { s with errs := term { p, ann, key, lvls, prof } [] s.errs t }
      | none => s
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
        let telescope := ((p.decl? c).map fun d => d.type.pis.1.size).getD 0
        let errs := if rel.params.size ≤ telescope then errs
          else RelError.of "S1" "more parameter classes than binders" (some c) :: errs
        if (rel.result :: rel.params.toList).all (relOk lvls) then errs
        else RelError.of "S1" "a parameter class names a level beyond the constant's" (some c) :: errs
      | none => errs
    match ann.ctorRel? c with
    | some rel =>
      match p.decl? c with
      | some (.ctor _ _ _ _ _ nf _) =>
        let errs := if rel.fields.size == nf then errs
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
  let roots := p.roots.toList.map fun (_, c) => p.instOf c []
  let s := loop p ann annotated fuel {} roots []
  let errs := s.errs.reverse ++ (records p ann).reverse
  if !errs.isEmpty then .error errs.toArray
  else
    let instances := s.order.reverse
    let reached := instances.foldl (init := ([] : List CId)) (fun acc (c, _) =>
      if acc.contains c then acc else c :: acc) |>.reverse
    .ok { keys := s.keys.reverse.toArray, reached := reached.toArray
          instances := instances.toArray, consts := ann.consts, ctors := ann.ctors }

end Compilatrix.Src.Relevance
