import Ix.CompileCert.Pj.Tele

/-!
# M7 L3-pj: reading an installed recursor (the generic reader, X2 §8 open item 4)

`nat_induction` (X2) reads the pinned `natRecA`. The generic reader reads **any** installed
recursor of a non-nested block (mutual, indexed, reflexive fields) against its constructors: it
extracts the block's data (`RecRd`: parameters, motives with their index telescopes and inductives,
minors with their constructors, fields and recursive fields) and then checks, decidably, that the
installed recursor type **is** the standard recursor type rebuilt from that data
(`RecRd.type`) and that every constructor's installed type is the one the data describes
(`MinorRd.ctorType`). The checks are equalities of `Kernel.Expr`; so a successful read
(`readRec_sound`) hands the semantic proofs (`Pj/RecInduction.lean`) a recursor type of a known
shape, built from lifts of the constructors' own field types. Binder annotations (`BinderMeta`)
are not predicted: they are read off the installed terms and carried in the data, except that the
motive telescopes' binders must be in the graph regime (`.never`), as every motive's codomain is a
sort.

A recursor that does not read (a nested block, a non-uniform parameter, a checker construction that
differs from the standard one in a detail) is a decline of the *theorem*, never of the compiler;
the `pj-census` runner reads every canonical recursor of every fixture where a proof-justified
pass fires.
-/

namespace Ix.CompileCert.Pj

/-! ## The data -/

/-- A constructor field: `plain`, or recursive into motive `j` (the field's type is the telescope
`ys` over motive `j`'s inductive at the block's parameters and the indices `idx`). -/
inductive FieldRd where
  | plain (ty : Kernel.Expr)
  | recur (j : Nat) (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
  deriving DecidableEq, Inhabited

/-- One motive: its inductive, the inductive's universe arguments, its index telescope (in the
parameters' context), the metas of its major binder and of the motive binder, its sort. -/
structure MotiveRd where
  ind : Kernel.Name
  indUs : List Kernel.Level
  idxs : List (Kernel.Expr × Kernel.BinderMeta)
  majMeta : Kernel.BinderMeta
  sort : Kernel.Level
  binderMeta : Kernel.BinderMeta
  deriving DecidableEq, Inhabited

/-- One minor premise: its constructor (and universe arguments), its motive, the constructor's
parameter metas, fields (with their metas in the constructor's type), result indices, and the metas
the minor's own telescope carries in the recursor type. -/
structure MinorRd where
  ctor : Kernel.Name
  ctorUs : List Kernel.Level
  motive : Nat
  paramMetas : List Kernel.BinderMeta
  fields : List (FieldRd × Kernel.BinderMeta)
  resIdx : List Kernel.Expr
  fieldMetas : List Kernel.BinderMeta
  ihMetas : List Kernel.BinderMeta
  binderMeta : Kernel.BinderMeta
  deriving DecidableEq, Inhabited

/-- A read recursor: the block's parameters, motives, minors, the recursor's own motive (`major`),
and the metas of its final index and major binders. -/
structure RecRd where
  params : List (Kernel.Expr × Kernel.BinderMeta)
  motives : List MotiveRd
  minors : List MinorRd
  major : Nat
  finalMetas : List Kernel.BinderMeta
  deriving DecidableEq, Inhabited

/-! ## Rebuilding the standard recursor type -/

/-- `bvar (d + n - 1 - i)` for `i < n`: `n` variables bound right above `d` others, outermost
first. -/
def bvarsAt (n d : Nat) : List Kernel.Expr := (List.range n).map fun i => .bvar (d + n - 1 - i)

/-- Pair types with metas. -/
def zipMetas : List Kernel.Expr → List Kernel.BinderMeta → List (Kernel.Expr × Kernel.BinderMeta)
  | t :: ts, m :: ms => (t, m) :: zipMetas ts ms
  | _, _ => []

/-- Lift a telescope: binder `i` by `n` at cutoff `c + i`. -/
def liftTele (n c : Nat) (bs : List (Kernel.Expr × Kernel.BinderMeta)) :
    List (Kernel.Expr × Kernel.BinderMeta) :=
  bs.mapIdx fun i p => (p.1.liftLooseBVars n (c + i), p.2)

namespace MotiveRd

/-- The major binder's type, in the context parameters, indices. -/
def majTy (np : Nat) (m : MotiveRd) : Kernel.Expr :=
  Kernel.Expr.mkAppN (.const m.ind m.indUs) (bvarsAt np m.idxs.length ++ bvarsAt m.idxs.length 0)

/-- The motive's telescope: the indices, then the major. -/
def tele (np : Nat) (m : MotiveRd) : List (Kernel.Expr × Kernel.BinderMeta) :=
  m.idxs ++ [(m.majTy np, m.majMeta)]

/-- The motive's type, in the parameters' context. -/
def type (np : Nat) (m : MotiveRd) : Kernel.Expr := piJoin (m.tele np) (.sort m.sort)

end MotiveRd

/-- A field's type, in the context parameters, earlier fields (`a` of them). -/
def FieldRd.ty (np : Nat) (motives : List MotiveRd) (a : Nat) : FieldRd → Kernel.Expr
  | .plain t => t
  | .recur j ys idx =>
    let m := motives.getD j default
    piJoin ys (Kernel.Expr.mkAppN (.const m.ind m.indUs) (bvarsAt np (a + ys.length) ++ idx))

namespace MinorRd

variable (np nm : Nat) (motives : List MotiveRd) (n : MinorRd)

/-- The constructor's fields' types, in the constructor's context. -/
def fieldTys : List (Kernel.Expr × Kernel.BinderMeta) :=
  n.fields.mapIdx fun a p => (p.1.ty np motives a, p.2)

/-- The constructor's type (instantiated at `ctorUs`), as the data describes it. -/
def ctorType (params : List (Kernel.Expr × Kernel.BinderMeta)) : Kernel.Expr :=
  let m := motives.getD n.motive default
  piJoin (zipMetas (params.map Prod.fst) n.paramMetas)
    (piJoin (n.fieldTys np motives)
      (Kernel.Expr.mkAppN (.const m.ind m.indUs) (bvarsAt np n.fields.length ++ n.resIdx)))

/-- The recursive fields, in order: `(a, j, ys, idx)`. -/
def recFields : List (Nat × Nat × List (Kernel.Expr × Kernel.BinderMeta) × List Kernel.Expr) :=
  (n.fields.mapIdx fun a p => (a, p.1)).filterMap fun (a, f) =>
    match f with
    | .plain _ => none
    | .recur j ys idx => some (a, j, ys, idx)

/-- The induction hypothesis type of the `r`-th recursive field `(a, j, ys, idx)`, in the context
parameters, motives, fields, earlier hypotheses. -/
def ihTy (r a j : Nat) (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr) :
    Kernel.Expr :=
  let nf := n.fields.length
  let sh := nf - a + r
  let ys' := liftTele sh 0 (liftTele nm a ys)
  let ky := ys.length
  piJoin ys'
    (Kernel.Expr.mkAppN (.bvar (ky + r + nf + (nm - 1 - j)))
      (idx.map (fun e => (e.liftLooseBVars nm (a + ky)).liftLooseBVars sh ky) ++
        [Kernel.Expr.mkAppN (.bvar (ky + r + (nf - 1 - a))) (bvarsAt ky 0)]))

/-- The minor's conclusion, in the context parameters, motives, fields, hypotheses. -/
def concl : Kernel.Expr :=
  let nf := n.fields.length
  let nih := (n.recFields).length
  Kernel.Expr.mkAppN (.bvar (nih + nf + (nm - 1 - n.motive)))
    (n.resIdx.map (fun e => (e.liftLooseBVars nm nf).liftLooseBVars nih 0) ++
      [Kernel.Expr.mkAppN (.const n.ctor n.ctorUs) (bvarsAt np (nih + nf + nm) ++ bvarsAt nf nih)])

/-- The induction hypotheses' types. -/
def ihTys : List Kernel.Expr :=
  (n.recFields).mapIdx fun r (a, j, ys, idx) => n.ihTy nm r a j ys idx

/-- The minor's type, in the context parameters, motives. -/
def type : Kernel.Expr :=
  piJoin (zipMetas ((n.fieldTys np motives).mapIdx fun a p => p.1.liftLooseBVars nm a) n.fieldMetas)
    (piJoin (zipMetas (n.ihTys nm) n.ihMetas) (n.concl np nm))

end MinorRd

namespace RecRd

variable (R : RecRd)

def np : Nat := R.params.length
def nm : Nat := R.motives.length
def nmin : Nat := R.minors.length

/-- The motive binders, in the recursor type. -/
def motiveBinders : List (Kernel.Expr × Kernel.BinderMeta) :=
  R.motives.mapIdx fun j m => ((m.type R.np).liftLooseBVars j 0, m.binderMeta)

/-- The minor binders, in the recursor type. -/
def minorBinders : List (Kernel.Expr × Kernel.BinderMeta) :=
  R.minors.mapIdx fun q n => ((n.type R.np R.nm R.motives).liftLooseBVars q 0, n.binderMeta)

/-- The recursor's own motive. -/
def majorMotive : MotiveRd := R.motives.getD R.major default

/-- The final index and major binders. -/
def finalBinders : List (Kernel.Expr × Kernel.BinderMeta) :=
  zipMetas ((liftTele (R.nm + R.nmin) 0 (R.majorMotive.tele R.np)).map Prod.fst) R.finalMetas

/-- The recursor type's conclusion. -/
def concl : Kernel.Expr :=
  let k := (R.majorMotive.tele R.np).length
  Kernel.Expr.mkAppN (.bvar (k + R.nmin + (R.nm - 1 - R.major))) (bvarsAt k 0)

/-- **The standard recursor type** the data describes. -/
def type : Kernel.Expr :=
  piJoin R.params (piJoin R.motiveBinders (piJoin R.minorBinders (piJoin R.finalBinders R.concl)))

end RecRd

/-! ## The check and the reader -/

/-- The installed recursor `r` has the rebuilt type. -/
def RecRd.RecOk (env : Kernel.Env) (r : Kernel.Name) (R : RecRd) : Prop :=
  match env.find? r with
  | some (.recInfo hdr _ _ _) => hdr.type = R.type
  | _ => False

instance (env : Kernel.Env) (r : Kernel.Name) (R : RecRd) : Decidable (R.RecOk env r) := by
  unfold RecRd.RecOk
  split
  · exact inferInstance
  · exact isFalse id

/-- The minor's constructor is installed with the type the data describes. -/
def MinorRd.CtorOk (env : Kernel.Env) (np : Nat) (motives : List MotiveRd)
    (params : List (Kernel.Expr × Kernel.BinderMeta)) (n : MinorRd) : Prop :=
  match env.find? n.ctor with
  | some (.ctorInfo cv cnp cnf) =>
    cnp = np ∧ cnf = n.fields.length ∧ n.ctorUs.length = cv.levelParams.length ∧
      cv.type.instantiateLevelParams cv.levelParams n.ctorUs = n.ctorType np motives params
  | _ => False

instance (env : Kernel.Env) (np : Nat) (motives : List MotiveRd)
    (params : List (Kernel.Expr × Kernel.BinderMeta)) (n : MinorRd) :
    Decidable (n.CtorOk env np motives params) := by
  unfold MinorRd.CtorOk
  split
  · exact inferInstance
  · exact isFalse id

/-- The decidable conditions a read must meet. -/
def RecRd.Check (env : Kernel.Env) (r : Kernel.Name) (R : RecRd) : Prop :=
  R.RecOk env r ∧
  R.major < R.nm ∧
  R.finalMetas.length = (R.majorMotive.tele R.np).length ∧
  (∀ m ∈ R.motives, ∀ p ∈ m.tele R.np, p.2 = ⟨.never⟩) ∧
  (∀ n ∈ R.minors, n.motive < R.nm ∧ n.paramMetas.length = R.np ∧
    n.fieldMetas.length = n.fields.length ∧ n.ihMetas.length = n.recFields.length ∧
    (∀ p ∈ n.recFields, p.2.1 < R.nm) ∧ n.CtorOk env R.np R.motives R.params)

instance (env : Kernel.Env) (r : Kernel.Name) (R : RecRd) : Decidable (R.Check env r) := by
  unfold RecRd.Check; exact inferInstance
/-- Every `∀`-binder of a term, outermost first, and the body. -/
def stripAllPis : Kernel.Expr → List (Kernel.Expr × Kernel.BinderMeta) × Kernel.Expr
  | .forallE t b m => let (bs, e) := stripAllPis b; ((t, m) :: bs, e)
  | e => ([], e)

/-- Read one motive binder (`j` motives above it). -/
def readMotive (j : Nat) (b : Kernel.Expr × Kernel.BinderMeta) : Option MotiveRd := do
  let (bs, body) := stripAllPis (b.1.lowerBVars j 0)
  let .sort s := body | none
  let (maj, mm) ← bs.getLast?
  let .const ind us := maj.getAppFn | none
  pure { ind, indUs := us, idxs := bs.dropLast, majMeta := mm, sort := s, binderMeta := b.2 }

/-- Read a constructor field's type (`a` earlier fields). -/
def readField (np : Nat) (motives : List MotiveRd) (a : Nat) (t : Kernel.Expr) : FieldRd :=
  let (ys, body) := stripAllPis t
  match body.getAppFn with
  | .const c us =>
    match motives.findIdx? (fun m => m.ind == c && m.indUs == us) with
    | some j =>
      let args := body.getAppArgs
      if args.take np == bvarsAt np (a + ys.length) then .recur j ys (args.drop np) else .plain t
    | none => .plain t
  | _ => .plain t

/-- Read one minor binder (`q` minors above it). -/
def readMinor (env : Kernel.Env) (np nm : Nat) (motives : List MotiveRd) (q : Nat)
    (b : Kernel.Expr × Kernel.BinderMeta) : Option MinorRd := do
  let (bs, body) := stripAllPis (b.1.lowerBVars q 0)
  let .bvar hv := body.getAppFn | none
  let major ← body.getAppArgs.getLast?
  let .const c cus := major.getAppFn | none
  let some (.ctorInfo cv cnp cnf) := env.find? c | none
  if cnp != np then none
  let cty := cv.type.instantiateLevelParams cv.levelParams cus
  let (cbs, cres) ← cty.stripPis (np + cnf)
  let nih := bs.length - cnf
  let k := nm - 1 - (hv - nih - cnf)
  let fields := (cbs.drop np).mapIdx fun a p => (readField np motives a p.1, p.2)
  pure { ctor := c, ctorUs := cus, motive := k, paramMetas := (cbs.take np).map Prod.snd,
         fields, resIdx := cres.getAppArgs.drop np,
         fieldMetas := (bs.take cnf).map Prod.snd, ihMetas := (bs.drop cnf).map Prod.snd,
         binderMeta := b.2 }

/-- Extract the block data of the installed recursor `r` with `np` parameters, `nm` motives and
`nmin` minors (unchecked). -/
def extractRec (env : Kernel.Env) (r : Kernel.Name) (np nm nmin : Nat) : Option RecRd := do
  let some (.recInfo hdr _ _ _) := env.find? r | none
  let (pbs, t1) ← hdr.type.stripPis np
  let (mbs, t2) ← t1.stripPis nm
  let motives ← (mbs.mapIdx fun j b => readMotive j b).mapM id
  let (nbs, t3) ← t2.stripPis nmin
  let minors ← (nbs.mapIdx fun q b => readMinor env np nm motives q b).mapM id
  let (fbs, concl) := stripAllPis t3
  let .bvar hv := concl.getAppFn | none
  let major := nm - 1 - (hv - fbs.length - nmin)
  pure { params := pbs, motives, minors, major, finalMetas := fbs.map Prod.snd }

/-- **The reader**: the extracted data, when it passes the check. -/
def readRec (env : Kernel.Env) (r : Kernel.Name) (np nm nmin : Nat) : Option RecRd :=
  (extractRec env r np nm nmin).bind fun R => if R.Check env r then some R else none

/-- **Soundness of the reader**: a successful read is checked. -/
theorem readRec_sound {env : Kernel.Env} {r : Kernel.Name} {np nm nmin : Nat} {R : RecRd}
    (h : readRec env r np nm nmin = some R) : R.Check env r := by
  simp only [readRec, Option.bind_eq_some_iff] at h
  obtain ⟨R', _, h⟩ := h
  by_cases hc : R'.Check env r
  · simp only [hc, ↓reduceIte, Option.some.injEq] at h
    exact h ▸ hc
  · simp [hc] at h

end Ix.CompileCert.Pj
