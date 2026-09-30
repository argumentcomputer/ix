import Compilatrix.Src.Relevance.Check
import Compilatrix.Lam.Syntax

/-! # Erasure input

What erasure reads from a checked Src program (design note 02 §2, §5.1),
built once into persistent `Nat`-keyed maps and lists (D17): the program's
tables are still arrays and hash maps (M1.K1), so erasure never indexes them
on its path. Every query decides relevance at a universe profile (D18):
recursor kinds at the recursor's profile, parameter classes at the
callee's. Constructor layouts are the exception: a field whose class
depends on the profile is kept at every profile (`layoutClass`), so each
constructor has one layout and projections, which carry no universe
arguments, need none.

`unbox?` is reimplemented here on lists; `tests-lam` checks it equal to
`Relevance.Checked.unbox?` on every inductive whose field classes do not
depend on the profile, at every profile. -/

namespace Compilatrix.Lam.Erase

open Compilatrix.Src Compilatrix.Src.Relevance

/-- A constant's relevance record, over lists. -/
structure ConstRec where
  result : Rel
  params : List Rel
  deriving Inhabited

structure Input where
  decls : NatMap Decl := .leaf
  resolve : NatMap Resolve := .leaf
  recKind : NatMap RecKind := .leaf
  lazy : NatMap Nat := .leaf
  opaqueByValue : NatMap Unit := .leaf
  consts : NatMap ConstRec := .leaf
  ctorFields : NatMap (List FieldClass) := .leaf
  /-- Recursor rules, by recursor. -/
  rules : NatMap (List Rule) := .leaf
  /-- Constructors, by inductive. -/
  indCtors : NatMap (List CId) := .leaf
  known : Src.Known := {}
  roots : List CId := []
  deriving Inhabited

/-- `(i, x)` for every `some x` at index `i`. -/
def indexed {α : Type} (xs : List (Option α)) : List (Nat × α) :=
  xs.zipIdx.filterMap fun (x, i) => x.map (i, ·)

/-- Build the input once from a program and its checked annotation. -/
def Input.ofProgram (p : Src.Program) (c : Checked) : Input :=
  let decls := p.consts.toList.map (·.decl)
  { decls := NatMap.ofList (indexed (decls.map some))
    resolve := NatMap.ofList (indexed p.table.resolve.toList)
    recKind := NatMap.ofList (indexed p.table.recKind.toList)
    lazy := NatMap.ofList (indexed p.table.lazy.toList)
    opaqueByValue := NatMap.ofList (indexed (p.table.opaqueByValue.toList.map
      fun b => if b then some () else none))
    consts := NatMap.ofList (indexed (c.consts.toList.map (·.map fun r =>
      { result := r.result, params := r.params.toList })))
    ctorFields := NatMap.ofList (indexed (c.ctors.toList.map (·.map (·.fields.toList))))
    rules := NatMap.ofList (indexed (decls.map fun
      | .recr _ _ _ _ _ _ _ _ rules _ => some rules.toList
      | _ => none))
    indCtors := NatMap.ofList (indexed (decls.map fun
      | .induct _ _ _ _ _ ctors => some ctors.toList
      | _ => none))
    known := p.known
    roots := p.roots.toList.map (·.2) }

namespace Input

variable (I : Input)

def decl? (c : CId) : Option Decl := I.decls.get? c

def lvls (c : CId) : Nat := ((I.decl? c).map Decl.lvls).getD 0

/-- A callee's profile, normalised to its level count. -/
def profileOf (c : CId) (prof : Profile) (us : List Ixon.Univ) : Profile :=
  (prof.inst us).normalize (I.lvls c)

def params (c : CId) : List Rel := ((I.consts.get? c).map (·.params)).getD []

/-- Parameter `i` of `c` is irrelevant at the callee's profile `q`
(a missing class reads as relevant). -/
def paramIrr (c : CId) (q : Profile) (i : Nat) : Bool := ((I.params c).getD i .rel).irrP q

/-- A field class for a constructor's **layout**: a class that depends on the
profile (a proof only where some universe parameters are zero) is kept, so
a constructor has one layout at every profile. Where such a field is a proof,
the construction site passes an irrelevant argument (S2) and Lam stores □
in its slot, as box-passing does for arguments. `CtorKey.src c` therefore
has one kept-field arity, and a projection needs no profile (`proj S i e`
carries none). -/
def layoutClass : FieldClass → FieldClass
  | .proof (.allZero (_ :: _)) => .keep
  | c => c

/-- Field classes of constructor `k`, for its layout. -/
def fields? (k : CId) : Option (List FieldClass) := (I.ctorFields.get? k).map (·.map layoutClass)

/-- Field `i` of constructor `k` is kept at profile `q` (unannotated: kept). -/
def kept (k : CId) (q : Profile) (i : Nat) : Bool :=
  match I.fields? k with
  | some fs => (fs[i]?.map fun cls => !cls.dropP q).getD false
  | none => true

/-- How many of the first `i` fields are kept. -/
def rank (k : CId) (q : Profile) (i : Nat) : Nat :=
  ((List.range i).filter (I.kept k q)).length

def keptCount (k : CId) (q : Profile) (nf : Nat) : Nat := I.rank k q nf

def kindAt (r : CId) (q : Profile) : Option RecKind := (I.recKind.get? r).map (·.atProfile q)

def rulesOf (r : CId) : List Rule := (I.rules.get? r).getD []

def ctorsOf (t : CId) : List CId := (I.indCtors.get? t).getD []

def isOpaqueByValue (c : CId) : Bool := I.opaqueByValue.contains c

/-- Every field of `k` is dropped at every profile. -/
def fieldless (k : CId) : Bool :=
  match I.fields? k with
  | some fs => fs.all (·.alwaysDropped)
  | none => false

/-- `Decidable.isFalse`/`isTrue` retagged as `Bool.false`/`true` (note 02
§4.1, D19) when all four constructors are pinned and the `Decidable` one
keeps no field (its proof), so both keys have the same layout. -/
def alias (c : CId) : CId :=
  match I.known.decIsFalse, I.known.decIsTrue, I.known.boolFalse, I.known.boolTrue with
  | some df, some dt, some bf, some bt =>
    if c == df && I.fieldless df then bf else if c == dt && I.fieldless dt then bt else c
  | _, _, _, _ => c

def ctorKey (c : CId) : Key.CtorKey := .src (I.alias c)

/-- The universe arguments of a recursor's major inductive. -/
def majorUnivs (r : CId) : Option (List Ixon.Univ) :=
  match I.decl? r with
  | some (.recr _ _ _ np nmot nmin ni _ _ ty) => ty.domainUnivs? (np + nmot + nmin + ni)
  | _ => none

/-- The profile of a recursor's constructors from the recursor's profile. -/
def ctorProfile (r : CId) (q : Profile) : Profile :=
  match I.majorUnivs r with
  | some us => q.inst us
  | none => q

/-- The Lam keys of the pinned constructors. -/
def lamKnown : Lam.Known :=
  { natZero := I.known.natZero.map (Key.CtorKey.src ∘ I.alias)
    natSucc := I.known.natSucc.map (Key.CtorKey.src ∘ I.alias)
    boolFalse := I.known.boolFalse.map .src
    boolTrue := I.known.boolTrue.map .src }

end Input

/-! ## Types, structurally -/

/-- The result of a Π-telescope. -/
def piResult : Src.Term → Src.Term
  | .pi _ _ _ b => piResult b
  | t => t

/-- The domain of the `i`-th binder of a Π-telescope. -/
def piDomain? : Nat → Src.Term → Option Src.Term
  | 0, .pi _ _ d _ => some d
  | i + 1, .pi _ _ _ b => piDomain? i b
  | _, _ => none

/-- The result contract of the innermost Π (`shared` if none). -/
def lastRes : Src.Term → Ixon.V3.ValueContract
  | .pi _ res _ b =>
    match b with
    | .pi .. => lastRes b
    | _ => res
  | _ => .shared

namespace Input

variable (I : Input)

/-- A constant's result contract (06 S35). -/
def resultContract (c : CId) : Ixon.V3.ValueContract :=
  ((I.decl? c).map (lastRes ·.type)).getD .shared

/-- S3 `unbox?` at a profile, on lists: the one constructor of `t` keeps
exactly one field at `prof`, `t`'s result is not literally `sort 0`, and
the kept field's type does not mention `t`. -/
def unbox? (t : CId) (prof : Profile) : Option Nat := do
  let .induct _ _ np _ ty _ ← I.decl? t | none
  let [k] := I.ctorsOf t | none
  let fields ← I.fields? k
  let keptIdx := (fields.zipIdx.filter fun (c, _) => !c.dropP prof).map (·.2)
  let [j] := keptIdx | none
  if piResult ty matches .sort .zero then none
  let .ctor _ _ _ _ _ _ cty ← I.decl? k | none
  let fieldTy ← piDomain? (np + j) cty
  if fieldTy.mentions t then none
  return j

end Input

end Compilatrix.Lam.Erase
