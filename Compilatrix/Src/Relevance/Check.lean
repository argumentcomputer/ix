import Compilatrix.Src.Relevance.Syntax

/-! # The relevance checker

Decides an installed annotation (design note 02 §3.3) in one pass over the
runtime closure: the terms reached from the roots through relevant
positions (`Src.Runtime`). It is executable here; its theorems
(`check_sound`, `check_consistent`) are M2 items. The checker reads only
syntax: the tags installed in the terms, the `ConstRel`/`CtorRel` tables and
the derived `RecKind`s. It never calls the type checker.

**Tier S** (soundness facts, premises of erasure):
* S1 shape: every runtime term of the closure is annotated and its tags
  cover it exactly (`install`); every `propWhen` names parameters below the
  constant's `lvls`; every `CtorRel` has the constructor's field count; every
  `ConstRel` has at most the telescope's length of parameters; every
  constant and constructor the closure reaches has its record.
* S2 dropped fields are built from `irr`: a constructor spine passes an
  `irr` argument at every non-`keep` field.
* S3 `unbox?`, derived: one constructor, exactly one `keep` field, the type's
  result not literally `sort 0`, the type not in the kept field's type.
* S4 `RecKind` agreement: a subsingleton recursor's constructor keeps only
  fields that `RecKind` reads from an index.

**Tier C** (consistency; early rejection with a precise diagnostic):
* C0 a binder written `erased` is irrelevant.
* C1 no relevant use of an irrelevant λ or let binder.
* C2 at a constant head, an irrelevant parameter gets an irrelevant argument.
* C3 non-`keep` fields are bound by irrelevant minor binders and never
  projected in a relevant position.
* C4 a saturated eliminator whose major is irrelevant has a subsingleton or
  empty `RecKind`.
* C5 relevant positions reference only constants whose result is `rel`. -/

namespace Compilatrix.Src.Relevance

structure RelError where
  /-- `S1`–`S4` or `C0`–`C5`. -/
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

/-- The checker's verdict: the runtime closure with its records. -/
structure Checked where
  keys : Array TermKey
  reached : Array CId
  consts : Array (Option ConstRel)
  ctors : Array (Option CtorRel)
  /-- Per inductive: the kept field of an unboxed structure (S3). -/
  unbox : Array (Option Nat)
  deriving Inhabited

namespace Checked

def ctorRel? (c : Checked) (k : CId) : Option CtorRel := (c.ctors[k]?).join
def constRel? (c : Checked) (k : CId) : Option ConstRel := (c.consts[k]?).join
def unbox? (c : Checked) (t : CId) : Option Nat := (c.unbox[t]?).join

/-- Whether field `i` of constructor `k` is kept (unannotated: kept). -/
def keeps (c : Checked) (k : CId) (i : Nat) : Bool :=
  match c.ctorRel? k with
  | some r => r.fields[i]? == some .keep
  | none => true

end Checked

namespace Check

/-- Pending work for one term: its key and the owning constant's level count. -/
structure Ctx where
  p : Program
  ann : Ann
  key : TermKey
  lvls : Nat

def err (ctx : Ctx) (rule : String) (msg : String) (const : Option CId := none) : RelError :=
  { rule, key := some ctx.key, const, message := msg }

def pwOk (lvls : Nat) : PropWhen → Bool
  | .never => true
  | .allZero ps => ps.all (· < lvls)

/-- The single constructor of a structure-like inductive. -/
def onlyCtor? (p : Program) (s : CId) : Option CId :=
  match p.decl? s with
  | some (.induct _ _ _ _ _ ctors) => if ctors.size == 1 then ctors[0]? else none
  | _ => none

/-- Positional roles of a saturated eliminator spine: minors with their rule
index, the major position, and the recursor. -/
structure ElimShape where
  recr : CId
  minors : Array (Nat × Nat)
  major : Nat
  arity : Nat

def elimShape? (p : Program) (c : CId) : Option ElimShape :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ np _ nmin ni _ _ _) =>
      some { recr := r, minors := (Array.range nmin).map fun j => (np + 1 + ni + 1 + j, j)
             major := np + 1 + ni, arity := np + 1 + ni + 1 + nmin }
    | _ => none
  | none =>
    match p.decl? c with
    | some (.recr _ _ _ np nmot nmin ni _ _ _) =>
      some { recr := c, minors := (Array.range nmin).map fun j => (np + nmot + j, j)
             major := np + nmot + nmin + ni, arity := np + nmot + nmin + ni + 1 }
    | _ => none
  | _ => none

/-- Field classes of the constructor selected by rule `j` of `r`. -/
def ruleCtorFields (p : Program) (ann : Ann) (r : CId) (j : Nat) : Option (CId × Array FieldClass) := do
  let .recr _ _ _ _ _ _ _ _ rules _ ← p.decl? r | none
  let rule ← rules[j]?
  let rel ← ann.ctorRel? rule.ctor
  return (rule.ctor, rel.fields)

/-- Check a constant in a relevant position (C5, and S1's record presence). -/
def constHead (ctx : Ctx) (c : CId) (errs : Array RelError) : Array RelError :=
  match ctx.ann.constRel? c with
  | some rel =>
    if rel.result == .rel then errs
    else errs.push (err ctx "C5" s!"relevant reference to a {repr rel.result} constant" (some c))
  | none => errs.push (err ctx "S1" "constant without a record" (some c))

/-- Rules at a constant head: C2, S2, and C3/C4 at saturated eliminators. -/
def knownHead (ctx : Ctx) (errs : Array RelError) (c : CId)
    (args : Array (Term × Mode)) : Array RelError :=
  let p := ctx.p
  -- C2: irrelevant parameters get irrelevant arguments.
  let errs := match ctx.ann.constRel? c with
    | some rel =>
      (args.zip rel.params).foldl (init := errs) fun errs ((_, m), r) =>
        if r != .rel && m != .irr then
          errs.push (err ctx "C2" s!"a {repr r} parameter gets a relevant argument" (some c))
        else errs
    | none => errs
  -- S2: dropped constructor fields are built from `irr`.
  let errs := match p.decl? c, ctx.ann.ctorRel? c with
    | some (.ctor _ _ _ _ np _ _), some rel =>
      (rel.fields.zipIdx).foldl (init := errs) fun errs (cls, j) =>
        match args[np + j]? with
        | some (_, m) =>
          if cls != .keep && m != .irr then
            errs.push (err ctx "S2" s!"field {j} is dropped but built from a relevant argument" (some c))
          else errs
        | none => errs
    | some (.ctor ..), none => errs.push (err ctx "S1" "constructor without a record" (some c))
    | _, _ => errs
  -- C3 and C4 at saturated eliminators.
  match elimShape? p c with
  | some shape =>
    if args.size < shape.arity then errs else
    let errs := match args[shape.major]?, p.table.recKindOf shape.recr with
      | some (_, .irr), some .ordinary =>
        errs.push (err ctx "C4" "an ordinary eliminator with an irrelevant major" (some shape.recr))
      | _, _ => errs
    shape.minors.foldl (init := errs) fun errs (pos, j) =>
      match args[pos]?, ruleCtorFields p ctx.ann shape.recr j with
      | some (minor, m), some (k, fields) =>
        if m == .irr then errs else
        let (bs, _) := minor.lams
        (fields.zipIdx).foldl (init := errs) fun errs (cls, i) =>
          match bs[i]? with
          | some (b, _) =>
            if cls != .keep && b.rel == .rel then
              errs.push (err ctx "C3" s!"minor {j} binds dropped field {i} relevantly" (some k))
            else errs
          | none => errs
      | _, _ => errs
  | none => errs

mutual

/-- Check the relevant positions of a term under binder classes `binders`. -/
def term (ctx : Ctx) (binders : List Rel) (errs : Array RelError) : Term → Array RelError
  | .var i =>
    match binders[i]? with
    | some .rel => errs
    | some r => errs.push (err ctx "C1" s!"relevant use of a {repr r} binder (#{i})")
    | none => errs.push (err ctx "S1" s!"variable #{i} out of scope")
  | .const c _ => constHead ctx c errs
  | .lam b _ t =>
    let errs := if pwOk ctx.lvls b.propWhen then errs
      else errs.push (err ctx "S1" "propWhen names a parameter beyond the constant's levels")
    let errs := if b.contract.uses == .erased && b.rel == .rel then
        errs.push (err ctx "C0" "a binder written erased is annotated relevant")
      else errs
    term ctx (b.rel :: binders) errs t
  | .letE c r _ v b =>
    let errs := if c.binder.uses == .erased && r == .rel then
        errs.push (err ctx "C0" "a let written erased is annotated relevant")
      else errs
    let errs := if r == .rel then term ctx binders errs v else errs
    term ctx (r :: binders) errs b
  | .proj s i e =>
    let errs := match onlyCtor? ctx.p s with
      | some k =>
        match ctx.ann.ctorRel? k with
        | some rel =>
          if rel.fields[i]? == some .keep then errs
          else errs.push (err ctx "C3" s!"field {i} is not kept but is projected relevantly" (some k))
        | none => errs.push (err ctx "S1" "projection of a structure without a constructor record" (some k))
      | none => errs.push (err ctx "C3" "projection out of a type that is not a structure" (some s))
    term ctx binders errs e
  | .app f a m =>
    let (head, args) := (Term.app f a m).spine
    let errs := match head with
      | .const c _ => knownHead ctx errs c args
      | _ => errs
    let errs := rest ctx binders errs f
    if m == .irr then errs else term ctx binders errs a
  | _ => errs

/-- The rest of an application spine: its relevant arguments and its head. -/
def rest (ctx : Ctx) (binders : List Rel) (errs : Array RelError) : Term → Array RelError
  | .app f a m =>
    let errs := rest ctx binders errs f
    if m == .irr then errs else term ctx binders errs a
  | h => term ctx binders errs h

end

end Check

/-- S3 `unbox?`, derived: a structure-like inductive with exactly one `keep`
field, whose result is not literally `sort 0` and whose kept field's type does
not mention it. -/
def unboxOf (p : Program) (ctorRel? : CId → Option CtorRel) (t : CId) : Option Nat := do
  let .induct _ _ np _ ty ctors ← p.decl? t | none
  unless ctors.size == 1 do none
  let k ← ctors[0]?
  let rel ← ctorRel? k
  let kept := (rel.fields.zipIdx).filter (·.1 == .keep)
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

open Check in
/-- Check an installed program against its annotation (`install` must have
run first). All violations are collected; any one rejects. -/
def check (p : Program) (ann : Ann) : Except (Array RelError) Checked := Id.run do
  let n := p.size
  let annotated : Std.HashSet TermKey := ann.nodes.foldl (fun s (k, _) => s.insert k) {}
  let mut errs : Array RelError := #[]
  let mut reached : Array Bool := .replicate n false
  let mut order : Array CId := #[]
  let mut keys : Array TermKey := #[]
  let mut queue : Array CId := p.roots.map (·.2)
  let mut qi := 0
  while qi < queue.size do
    let c := queue[qi]!
    qi := qi + 1
    if reached[c]?.getD true then continue
    reached := reached.set! c true
    order := order.push c
    if (ann.constRel? c).isNone then
      errs := errs.push (RelError.of "S1" "reached constant without a record" (some c))
    for key in p.runtimeKeys c do
      unless annotated.contains key do
        errs := errs.push (RelError.of "S1" "runtime term not annotated" none (some key))
        continue
      keys := keys.push key
      let some t := p.termOf key | continue
      let lvls := ((p.decl? c).map Decl.lvls).getD 0
      errs := term { p, ann, key, lvls } [] errs t
      queue := queue ++ t.relevantConsts #[]
    queue := queue ++ p.runtimeRefs c
  -- S1 on the records.
  for c in [0:n] do
    if let some rel := ann.constRel? c then
      let telescope := ((p.decl? c).map fun d => d.type.pis.1.size).getD 0
      unless rel.params.size ≤ telescope do
        errs := errs.push (RelError.of "S1" "more parameter classes than binders" (some c))
    if let some rel := ann.ctorRel? c then
      match p.decl? c with
      | some (.ctor _ _ _ _ _ nf _) =>
        unless rel.fields.size == nf do
          errs := errs.push (RelError.of "S1" "field classes differ from the field count" (some c))
      | _ => errs := errs.push (RelError.of "S1" "constructor record on a non-constructor" (some c))
  -- S4 on reached recursors.
  for c in order do
    if let some (.recr _ _ _ _ _ _ _ _ rules _) := p.decl? c then
      if let some (.subsingleton srcs) := p.table.recKindOf c then
        if let some rule := rules[0]? then
          if let some rel := ann.ctorRel? rule.ctor then
            for (cls, j) in rel.fields.zipIdx do
              if cls == .keep then
                match srcs[j]? with
                | some (.index _) => pure ()
                | _ => errs := errs.push (RelError.of "S4" s!"subsingleton field {j} is kept but not read from an index" (some c))
  if !errs.isEmpty then return .error errs
  -- S3: derived unboxing.
  let unbox := (Array.range n).map (unboxOf p ann.ctorRel?)
  return .ok { keys, reached := order, consts := ann.consts, ctors := ann.ctors, unbox }

end Compilatrix.Src.Relevance
