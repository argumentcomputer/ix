import IxVMRefinement.Binding.FamilyFlat
import IxVMRefinement.Core.Det

/-! # The family record's reconstruction: the recursor types and rules a family check compares

A family check of a block (`KernelModeled::check_recs`, member by member
`KernelCheck::check_recursor_canonical_at`) compares each recursor of a family record with the
block's reconstruction at the recursor's position in the flattened family
(`canonical_rules_at_pos`): its declared type with the reconstructed type (`build_rec_type`), and
each rule's body, under the λs its own type gives, with the reconstructed right-hand side
(`populate_rules`). This module models that reconstruction over a store, mirroring the circuit,
and states the record-level form a family check of a group's validation leaves a family record in.

* `ReconView`: what the reconstruction reads of a store (an inductive's level count, type,
  parameter, index and constructor counts, block and position; a constructor's type and
  parameter count and constant address; the key of an address and the address of a key; a
  definition's value at levels); `ReconView.ofStore t E`.
* `hnf`: the head normalization the reconstruction performs (`whnf` in `collect_n_doms_whnf`,
  `collect_index_doms`, `peel_ctor_params_subst`, `whnf_tele`), modelled as the δβ head
  strategy: a definition unfolded at a head constant, β at a λ applied, the function of an
  application, to a term with no such step. β substitutes by the circuit's lifting substitution
  (`instantiate1Lift`): the terms are open. Where the circuit's `whnf` takes another step on the
  reconstruction's inputs (ζ, ι, a projection, a primitive operation, a quotient, a literal) the
  model departs from it; that the circuit takes none there is the fidelity obligation of the head
  normalization.
* The reconstruction, mirroring the circuit function by function: `collectDoms`
  (`collect_n_doms_whnf`, `collect_index_doms`), `peelMotiveParams` (`peel_motive_params_subst`),
  `peelCtorParams` (`peel_ctor_params_subst`), `whnfTele`, `isRecField` (`is_rec_field_peel`,
  `flat_find_matching`), `fieldsClassify` (`walk_fields_classify`), `ihDoms` (`build_ih_doms`),
  `minorAt` (`build_minor_at_depth`), `minorDoms`, `allMinors` (`build_minor_doms`,
  `build_all_minors_walk`), `motiveType`, `allMotives` (`build_motive_type_flat`,
  `build_all_motives_walk`), **`recTypeAt`** (`build_rec_type`, `build_rec_type_from`),
  `applyIhs` (`apply_ihs_full`), `ruleBody` (`build_rule_rhs`), **`ruleBodiesAt`**
  (`populate_rules`, `ctors_before_pos`). Every head normalization takes one fuel.
* `LamsAlong`, `RuleFollows` (`compare_rules`, `rule_lam_doms`): a stored rule is the body under
  the λs of the recursor type's leading binders and of its minor premise's fields.
* `MemberRecon TyRel`: a recursor of the record, at its position `k`, relates its declared type to
  the reconstructed type by `TyRel` and each rule follows the reconstructed body, with the
  record's own recursors as the peers. **`RFormS`**: the record is the block's family over the
  flattened family derived from the block, and every recursor's declared type is the
  reconstructed one, up to the semantic equality of levels (`Core.ExprLvEq`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (KExpr KLevel KKey bmeta ExprLvEq)

set_option linter.unusedVariables false

/-! ## What the reconstruction reads of a store -/

/-- What `get_ci` gives of an inductive type: its level count, its type, its parameter, index and
constructor counts, its block and its position in the block. -/
structure IndData where
  nl : Nat
  ty : KExpr
  np : Nat
  ni : Nat
  nctors : Nat
  blk : _root_.Address
  idx : Nat

/-- **What the reconstruction reads of a store**: `get_ci` at an inductive's address, a
constructor's type and parameter count (`get_ci_cprj`), a constructor's constant address
(`projection_addr_ctor`), the key a constant's address reads as, the address a key names, and a
definition's value at given levels (the unfolding `whnf` performs). -/
structure ReconView where
  ind : _root_.Address → Option IndData
  ctor : _root_.Address → Nat → Nat → Option (KExpr × Nat)
  ctorAddr : _root_.Address → Nat → Nat → _root_.Address
  key : _root_.Address → KKey
  addr : KKey → Option _root_.Address
  unfold : KKey → List KLevel → Option KExpr

/-- `get_ci` at an inductive type's address of the store: through its projection record, the
member of its block, its type read over the block's tables. -/
def indDataAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (a : _root_.Address) : Option IndData :=
  match recordOf E a with
  | none => none
  | some c =>
    match c.info with
    | .iPrj p =>
      match recordOf E p.block with
      | none => none
      | some cb =>
        match cb.info with
        | .muts ms =>
          match ms[p.idx.toNat]? with
          | some (.indc ind) =>
            match ((exprReader t (fun x => E.blobs.get? x) cb id
                (blockSelf t p.block ms)).read ind.typ).toOption with
            | none => none
            | some ty =>
              some ⟨ind.lvls.toNat, ty, ind.params.toNat, ind.indices.toNat, ind.ctors.size,
                p.block, p.idx.toNat⟩
          | _ => none
        | _ => none
    | _ => none

/-- `get_ci_cprj blk i c`: constructor `c` of member `i` of the block at `b`, its type read over
the block's tables, and its parameter count. -/
def ctorAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (b : _root_.Address) (i c : Nat) :
    Option (KExpr × Nat) :=
  match recordOf E b with
  | none => none
  | some cb =>
    match cb.info with
    | .muts ms =>
      match ms[i]? with
      | some (.indc ind) =>
        match ind.ctors[c]? with
        | none => none
        | some ctor =>
          match ((exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t b ms)).read
              ctor.typ).toOption with
          | none => none
          | some ty => some (ty, ctor.params.toNat)
      | _ => none
    | _ => none

/-- A definition's level count and value at a constant address of the store (`get_ci`'s `Defn`,
read with positional level parameters): a standalone definition record, or a definition member
of a block. Theorems and opaque constants are not unfolded. -/
def defnAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (a : _root_.Address) : Option (Nat × KExpr) :=
  match recordOf E a with
  | none => none
  | some c =>
    match c.info with
    | .defn d =>
      match d.kind with
      | .defn =>
        ((exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value).toOption.map
          fun v => (d.lvls.toNat, v)
      | _ => none
    | .dPrj p =>
      match recordOf E p.block with
      | none => none
      | some cb =>
        match cb.info with
        | .muts ms =>
          match ms[p.idx.toNat]? with
          | some (.defn d) =>
            match d.kind with
            | .defn =>
              ((exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t p.block ms)).read
                d.value).toOption.map fun v => (d.lvls.toNat, v)
            | _ => none
          | _ => none
        | _ => none
    | _ => none

/-- `red_unfold` at a key: the definition's value with its level parameters instantiated, when the
levels' count is the definition's. -/
def unfoldAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (k : KKey) (us : List KLevel) :
    Option KExpr :=
  match keyAddr t k with
  | none => none
  | some a =>
    match defnAt t E a with
    | none => none
    | some (n, v) =>
      if us.length = n then some (v.instantiateLevelParams (List.range n) us) else none

/-- **The readings of the store `E`** under the role table `t`. -/
def ReconView.ofStore (t : Ix.Kernel.RoleTable) (E : Ixon.Env) : ReconView :=
  ⟨indDataAt t E, ctorAt t E, IxVM.Consistency.ctorAddr, keyOf t, keyAddr t, unfoldAt t E⟩

/-! ## Head normalization: the δβ head strategy -/

/-- One head step: a definition unfolded at a constant, β at a λ applied (the circuit's
substitution, which lifts the argument past the binders it crosses), or a step of an
application's function. -/
def headStep (V : ReconView) : KExpr → Option KExpr
  | .const k us => V.unfold k us
  | .app (.lam _ b _) a => some (Ix.Kernel.Expr.instantiate1Lift b a 0)
  | .app f a => (headStep V f).map fun f' => .app f' a
  | _ => none

/-- **Head normalization** at a fuel of steps: head steps until none applies. -/
def hnf (V : ReconView) : Nat → KExpr → Option KExpr
  | 0, _ => none
  | n + 1, e =>
    match headStep V e with
    | none => some e
    | some e' => hnf V n e'

/-! ## Building terms -/

/-- `wrap_foralls`: the binders `doms`, outermost first, each with the datum of `dl`. -/
def wrapForalls (body : KExpr) (doms : List KExpr) (dl : KLevel) : KExpr :=
  doms.foldr (fun d b => .forallE d b (bmeta dl)) body

/-- `wrap_lams`: the λs `doms`, outermost first, each with the datum of `dl`. -/
def wrapLams (body : KExpr) (doms : List KExpr) (dl : KLevel) : KExpr :=
  doms.foldr (fun d b => .lam d b (bmeta dl)) body

/-- `apply_spine_expr`: the head applied to the arguments in order. -/
def appSpine (head : KExpr) (args : List KExpr) : KExpr :=
  args.foldl .app head

/-- `build_apply_bvars_decreasing` (and `build_motive_apps`, `build_minor_apps`): the head applied
to `bvar (start - i)` for `i < n`. -/
def appBVarsDec (head : KExpr) (n start : Nat) : KExpr :=
  appSpine head ((List.range n).map fun i => .bvar (start - i))

/-- `build_major_indices`, `build_apply_xs`: the head applied to `bvar (n - 1 - i)` for `i < n`. -/
def appBVarsDown (head : KExpr) (n : Nat) : KExpr :=
  appSpine head ((List.range n).map fun i => .bvar (n - 1 - i))

/-- `build_major_params`: the head applied to `bvar ((n - 1 - i) + depth)` for `i < n`. -/
def majorParams (head : KExpr) (n depth : Nat) : KExpr :=
  appSpine head ((List.range n).map fun i => .bvar (n - 1 - i + depth))

/-- `apply_indices_in_conclusion`: the head applied to `bvar (n - i)` for `i < n`. -/
def conclIndices (head : KExpr) (n : Nat) : KExpr :=
  appSpine head ((List.range n).map fun i => .bvar (n - i))

/-- `build_apply_field_bvars`: the head applied to `bvar (nb - 1 - i)` for `i < nf`. -/
def fieldBVars (head : KExpr) (nf nb : Nat) : KExpr :=
  appSpine head ((List.range nf).map fun i => .bvar (nb - 1 - i))

/-- `apply_spec_params_lifted`: the head applied to the parameters, each lifted by `depth`. -/
def specParamsLifted (head : KExpr) (sp : List KExpr) (depth : Nat) : KExpr :=
  appSpine head (sp.map fun s => s.liftLooseBVars depth 0)

/-- `list_lift_indices doms shift 0`: domain `j` lifted by `shift` at the cutoff `j`. -/
def liftIndices (doms : List KExpr) (shift : Nat) : List KExpr :=
  doms.zipIdx.map fun p => p.1.liftLooseBVars shift p.2

/-- `peel_leading_foralls`: the leading binders' domains and the body. -/
def peelAll : KExpr → List KExpr × KExpr
  | .forallE d b _ => ((d :: (peelAll b).1), (peelAll b).2)
  | e => ([], e)

/-! ## Telescopes -/

/-- **`collect_n_doms_whnf`, `collect_index_doms`**: the first `n` binder domains of a telescope,
head-normalizing where it is not syntactically a binder, and what follows them; fewer domains when
the head normal form is no binder. -/
def collectDoms (V : ReconView) (f : Nat) : Nat → KExpr → Option (List KExpr × KExpr)
  | 0, ty => some ([], ty)
  | n + 1, .forallE d b _ => (collectDoms V f n b).map fun p => (d :: p.1, p.2)
  | n + 1, ty =>
    match hnf V f ty with
    | none => none
    | some (.forallE d b _) => (collectDoms V f n b).map fun p => (d :: p.1, p.2)
    | some _ => some ([], ty)

/-- `subst_param_for`: the term a type's parameter `j` is instantiated by in a motive: the
recursor's parameter, or at an auxiliary the entry's parameter. -/
def substParamFor (j nrp : Nat) (aux : Bool) (sp : List KExpr) : KExpr :=
  match aux with
  | true =>
    match sp[j]? with
    | some s => s
    | none => .bvar (nrp - 1 - j)
  | false => .bvar (nrp - 1 - j)

/-- **`peel_motive_params_subst`**: a type past its first `n` parameters, each instantiated
(`substParamFor`); no head normalization. -/
def peelMotiveParams (nrp : Nat) (aux : Bool) (sp : List KExpr) :
    Nat → Nat → KExpr → Option KExpr
  | 0, _, ty => some ty
  | n + 1, j, .forallE _ b _ =>
    peelMotiveParams nrp aux sp n (j + 1)
      (Ix.Kernel.Expr.instantiate1Lift b (substParamFor j nrp aux sp) 0)
  | _ + 1, _, _ => none

/-- `ctor_subst_param_for`: the term a constructor's parameter `j` is instantiated by. -/
def ctorSubstParamFor (j depth specLift : Nat) (aux : Bool) (sp : List KExpr) : KExpr :=
  match aux with
  | true =>
    match sp[j]? with
    | some s => s.liftLooseBVars specLift 0
    | none => .bvar (depth - 1 - j)
  | false => .bvar (depth - 1 - j)

/-- **`peel_ctor_params_subst`**: a constructor type past its first `n` parameters, each
instantiated (`ctorSubstParamFor`), head-normalizing where it is not syntactically a binder. -/
def peelCtorParams (V : ReconView) (f depth specLift : Nat) (aux : Bool) (sp : List KExpr) :
    Nat → Nat → KExpr → Option KExpr
  | 0, _, ty => some ty
  | n + 1, j, .forallE _ b _ =>
    peelCtorParams V f depth specLift aux sp n (j + 1)
      (Ix.Kernel.Expr.instantiate1Lift b (ctorSubstParamFor j depth specLift aux sp) 0)
  | n + 1, j, ty =>
    match hnf V f ty with
    | some (.forallE _ b _) =>
      peelCtorParams V f depth specLift aux sp n (j + 1)
        (Ix.Kernel.Expr.instantiate1Lift b (ctorSubstParamFor j depth specLift aux sp) 0)
    | _ => none

/-- **`whnf_tele`**: a term head-normalized, and the body of each binder it exposes in turn
(the domains are kept), at a fuel of binders. -/
def whnfTele (V : ReconView) (f : Nat) : Nat → KExpr → Option KExpr
  | 0, _ => none
  | n + 1, e =>
    match hnf V f e with
    | none => none
    | some (.forallE d b m) => (whnfTele V f n b).map fun b' => .forallE d b' m
    | some w => some w

/-! ## Fields and their inductive hypotheses -/

/-- `spec_params_dom_prefix_match`: the entry's parameters, lifted, are a prefix of the
arguments. -/
def specPrefix : List KExpr → List KExpr → Nat → Bool
  | [], _, _ => true
  | s :: sr, a :: ar, l => (s.liftLooseBVars l 0 == a) && specPrefix sr ar l
  | _ :: _, [], _ => false

/-- **`flat_find_matching`**: the first entry at the address, and at an auxiliary also with the
parameters and levels of the occurrence. -/
def flatFindMatching (es : List FlatEntry) (a : _root_.Address) (us : List KLevel)
    (args : List KExpr) (liftBy : Nat) : Option Nat :=
  es.findIdx? fun e =>
    e.addr == a && (!e.aux || (specPrefix e.params args liftBy && e.levels == us))

/-- **`is_rec_field_peel`**: a head-normalized field telescope ends in an entry of the flattened
family, at the position returned. -/
def isRecField (V : ReconView) (es : List FlatEntry) (liftBy : Nat) : KExpr → Option Nat
  | .forallE _ b _ => isRecField V es liftBy b
  | e =>
    match Ix.Kernel.Expr.getAppFn e with
    | .const k us =>
      match V.addr k with
      | some a => flatFindMatching es a us (Ix.Kernel.Expr.getAppArgs e) liftBy
      | none => none
    | _ => none

/-- **`walk_fields_classify`**: a constructor's fields after its parameters: their domains, the
recursive ones (field index, and the entry), the return type, and each field's type
head-normalized at every step of its telescope (`whnfTele`). -/
def fieldsClassify (V : ReconView) (f : Nat) (es : List FlatEntry) (liftBy : Nat) :
    Nat → KExpr → Option (List KExpr × List Nat × List Nat × KExpr × List KExpr)
  | fidx, .forallE d b _ =>
    match whnfTele V f f d with
    | none => none
    | some nd =>
      match fieldsClassify V f es liftBy (fidx + 1) b with
      | none => none
      | some (ds, ri, rm, ret, ns) =>
        match isRecField V es (liftBy + fidx) nd with
        | some m => some (d :: ds, fidx :: ri, m :: rm, ret, nd :: ns)
        | none => some (d :: ds, ri, rm, ret, nd :: ns)
  | _, ty => some ([], [], [], ty, [])

/-- **`build_ih_doms`**: the minor premise's inductive-hypothesis binders, one for each recursive
field, from the fields' head-normalized telescopes. -/
def ihDoms (rm : List Nat) (norm : List KExpr) (fop : List Nat)
    (motiveBase nFields minorSaved : Nat) (elim : KLevel) : Nat → List Nat → Option (List KExpr)
  | _, [] => some []
  | k, fieldIdx :: rest =>
    match norm[fieldIdx]? with
    | none => none
    | some dom =>
      let memIdx := (rm[k]?).getD 0
      let tnp := (fop[memIdx]?).getD 0
      let depth := minorSaved + nFields + k
      let domL := dom.liftLooseBVars (nFields - fieldIdx + k) 0
      let fds := (peelAll domL).1
      let inner := (peelAll domL).2
      let innerDepth := depth + fds.length
      let withIdx := appSpine (.bvar (innerDepth - 1 - (motiveBase + memIdx)))
        ((Ix.Kernel.Expr.getAppArgs inner).drop tnp)
      let fieldApp := appBVarsDown (.bvar (innerDepth - 1 - (minorSaved + fieldIdx))) fds.length
      (ihDoms rm norm fop motiveBase nFields minorSaved elim (k + 1) rest).map
        (wrapForalls (.app withIdx fieldApp) fds elim :: ·)

/-- `build_ctor_app_params`: the constructor applied to the recursor's parameters, or at an
auxiliary to the entry's parameters. -/
def ctorAppParams (head : KExpr) (nrp depthNow : Nat) (aux : Bool) (sp : List KExpr) : KExpr :=
  match aux with
  | false => appBVarsDec head nrp (depthNow - 1)
  | true => specParamsLifted head sp (depthNow - nrp)

/-! ## Minor premises and motives -/

/-- **`build_minor_at_depth`**: the minor premise of one constructor (its key `ck`, its type at
the entry's levels `us`, its parameter count `nOwn`), at the minors before it. -/
def minorAt (V : ReconView) (f : Nat) (es : List FlatEntry) (fop : List Nat) (ck : KKey)
    (cty : KExpr) (nOwn : Nat) (aux : Bool) (sp : List KExpr) (us : List KLevel)
    (nrp nMot prevMinors motiveBase selfMemIdx : Nat) (elim : KLevel) : Option KExpr :=
  let ctyI := cty.instantiateLevelParams (List.range us.length) us
  let minorSaved := nrp + nMot + prevMinors
  let below := nMot + prevMinors
  match peelCtorParams V f nrp 0 aux sp nOwn 0 ctyI with
  | none => none
  | some after =>
    match fieldsClassify V f es 0 0 after with
    | none => none
    | some (pfDoms, ri, rm, pfRet, pfNorm) =>
      let nFields := pfDoms.length
      let retTy := pfRet.liftLooseBVars below nFields
      let depthNow := minorSaved + (nFields + ri.length)
      let retIdx := ((Ix.Kernel.Expr.getAppArgs retTy).drop nOwn).map
        fun e => e.liftLooseBVars ri.length 0
      let withIdx := appSpine (.bvar (depthNow - 1 - (motiveBase + selfMemIdx))) retIdx
      let ctorApp := fieldBVars (ctorAppParams (.const ck us) nrp depthNow aux sp) nFields
        (nFields + ri.length)
      match ihDoms rm (liftIndices pfNorm below) fop motiveBase nFields minorSaved elim 0 ri with
      | none => none
      | some ih =>
        some (wrapForalls (wrapForalls (.app withIdx ctorApp) ih elim) (liftIndices pfDoms below)
          elim)

/-- **`build_minor_doms`**: the minor premises of the constructors `cs` of the inductive at `blk`,
position `idx` (the entry `selfMemIdx` of the flattened family), after `prev` minors. -/
def minorDoms (V : ReconView) (f : Nat) (es : List FlatEntry) (fop : List Nat) (aux : Bool)
    (sp : List KExpr) (us : List KLevel) (nrp nMot motiveBase selfMemIdx : Nat)
    (blk : _root_.Address) (idx : Nat) (elim : KLevel) : Nat → List Nat → Option (List KExpr)
  | _, [] => some []
  | prev, c :: cs =>
    match V.ctor blk idx c with
    | none => none
    | some (cty, np) =>
      match minorAt V f es fop (V.key (V.ctorAddr blk idx c)) cty np aux sp us nrp nMot prev
          motiveBase selfMemIdx elim with
      | none => none
      | some m =>
        (minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim (prev + 1)
          cs).map (m :: ·)

/-- **`build_all_minors_walk`**: every entry's minor premises, in order. -/
def allMinors (V : ReconView) (f : Nat) (fullEs : List FlatEntry) (fop : List Nat)
    (nrp nMot motiveBase : Nat) (elim : KLevel) :
    List FlatEntry → Nat → Nat → Option (List KExpr)
  | [], _, _ => some []
  | e :: rest, prev, pos =>
    match V.ind e.addr with
    | none => none
    | some i =>
      match minorDoms V f fullEs fop e.aux e.params e.levels nrp nMot motiveBase pos i.blk i.idx
          elim prev (List.range i.nctors) with
      | none => none
      | some ms =>
        (allMinors V f fullEs fop nrp nMot motiveBase elim rest (prev + ms.length) (pos + 1)).map
          (ms ++ ·)

/-- **`build_motive_type_flat`**: the motive's type of one entry: over its indices and major
premise, into the sort of the elimination level. -/
def motiveType (V : ReconView) (f : Nat) (memberAddr : _root_.Address) (indTy : KExpr)
    (nOwn nIdx : Nat) (us : List KLevel) (elim : KLevel) (nrp : Nat) (aux : Bool)
    (sp : List KExpr) : Option KExpr :=
  match peelMotiveParams nrp aux sp nOwn 0
      (indTy.instantiateLevelParams (List.range us.length) us) with
  | none => none
  | some after =>
    match collectDoms V f nIdx after with
    | none => none
    | some (idxDoms, _) =>
      let head : KExpr := .const (V.key memberAddr) us
      let withArgs := if aux then specParamsLifted head sp nIdx else majorParams head nrp nIdx
      let never : KLevel := .succ .zero
      some (wrapForalls (.forallE (appBVarsDown withArgs nIdx) (.sort elim) (bmeta never)) idxDoms
        never)

/-- **`build_all_motives_walk`**: every entry's motive type, the `j`-th lifted by `j`. -/
def allMotives (V : ReconView) (f : Nat) (elim : KLevel) (nrp : Nat) :
    List FlatEntry → Nat → Option (List KExpr)
  | [], _ => some []
  | e :: rest, j =>
    match V.ind e.addr with
    | none => none
    | some i =>
      match motiveType V f e.addr i.ty i.np i.ni e.levels elim nrp e.aux e.params with
      | none => none
      | some mt => (allMotives V f elim nrp rest (j + 1)).map (mt.liftLooseBVars j 0 :: ·)

/-- The elimination level of a recursor at the elimination offset `off` (`check_recursor_
canonical_at`): its first level parameter for a large eliminator, otherwise zero. -/
def elimLevel (off : Nat) : KLevel :=
  if off = 1 then .param 0 else .zero

/-- `build_flat_own_params`: each entry's parameter count. -/
def flatOwnParams (V : ReconView) (es : List FlatEntry) : List Nat :=
  es.map fun e => ((V.ind e.addr).map IndData.np).getD 0

/-! ## The reconstructed recursor type -/

/-- **`build_rec_type`** (with `build_rec_type_from`): the recursor type at entry `k` of the
flattened family `es`, at the elimination offset `off`, for a recursor over `nP` parameters:
the parameters (of the family's first type at the recursor's levels), the motives, the minor
premises, entry `k`'s indices and its major premise, into its motive applied. -/
def recTypeAt (V : ReconView) (f : Nat) (es : List FlatEntry) (off nP k : Nat) :
    Option KExpr :=
  let elim := elimLevel off
  match es[0]?, es[k]? with
  | some e0, some ek =>
    match V.ind e0.addr, V.ind ek.addr with
    | some prim, some self =>
      let nMot := es.length
      let nI := self.ni
      let pUs := (List.range prim.nl).map fun i => Ix.Kernel.Level.param (off + i)
      match collectDoms V f nP (prim.ty.instantiateLevelParams (List.range pUs.length) pUs) with
      | none => none
      | some (paramDoms, _) =>
        match allMotives V f elim nP es 0,
            allMinors V f es (flatOwnParams V es) nP nMot nP elim es 0 0 with
        | some motDoms, some minDoms =>
          let nMin := minDoms.length
          match peelMotiveParams nP ek.aux ek.params self.np 0
              (self.ty.instantiateLevelParams (List.range ek.levels.length) ek.levels) with
          | none => none
          | some selfAfter =>
            match collectDoms V f nI selfAfter with
            | none => none
            | some (idxRaw, _) =>
              let pre := nP + nMot + nMin + nI
              let head : KExpr := .const (V.key ek.addr) ek.levels
              let withArgs := if ek.aux then specParamsLifted head ek.params (nMot + nMin + nI)
                else appBVarsDec head nP (pre - 1)
              let concl : KExpr := .app (conclIndices (.bvar (pre - (nP + k))) nI) (.bvar 0)
              some (wrapForalls (wrapForalls (wrapForalls (wrapForalls
                (.forallE (appBVarsDown withArgs nI) concl (bmeta elim))
                (liftIndices idxRaw (nMot + nMin)) elim) minDoms elim) motDoms elim) paramDoms elim)
        | _, _ => none
    | _, _ => none
  | _, _ => none

/-! ## The reconstructed rules -/

/-- **`apply_ihs_full`**: the rule's right-hand side applies the minor premise to the fields and
then to each recursive field's inductive hypothesis, the peer recursor of the field's entry
applied to the parameters, motives, minors, the field type's indices and the field. -/
def applyIhs (V : ReconView) (rm : List Nat) (norm : List KExpr) (peers : List _root_.Address)
    (fop : List Nat) (nP nMot nMin nFields : Nat) (recLvls : List KLevel) (elim : KLevel) :
    KExpr → Nat → List Nat → Option KExpr
  | head, _, [] => some head
  | head, k, fieldIdx :: rest =>
    let memIdx := (rm[k]?).getD 0
    match peers[memIdx]?, norm[fieldIdx]? with
    | some target, some dom =>
      let tnp := (fop[memIdx]?).getD 0
      let domL := (dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields
      let fds := (peelAll domL).1
      let inner := (peelAll domL).2
      let innerDepth := nP + nMot + nMin + nFields + fds.length
      let withMin := appBVarsDec (appBVarsDec (appBVarsDec (.const (V.key target) recLvls) nP
        (innerDepth - 1)) nMot (innerDepth - 1 - nP)) nMin (innerDepth - 1 - nP - nMot)
      let withIdx := appSpine withMin ((Ix.Kernel.Expr.getAppArgs inner).drop tnp)
      let fieldApp := appBVarsDown (.bvar (nFields - 1 - fieldIdx + fds.length)) fds.length
      applyIhs V rm norm peers fop nP nMot nMin nFields recLvls elim
        (.app head (wrapLams (.app withIdx fieldApp) fds elim)) (k + 1) rest
    | _, _ => none

/-- **`build_rule_rhs`**: the body of the rule of one constructor (its type `cty` at the entry's
levels `us`, its parameter count `nOwn`), whose minor premise is the `minorIdx`-th. -/
def ruleBody (V : ReconView) (f : Nat) (es : List FlatEntry) (fop : List Nat)
    (peers : List _root_.Address) (cty : KExpr) (minorIdx nP nMot nMin nOwn : Nat)
    (us recLvls : List KLevel) (aux : Bool) (sp : List KExpr) (elim : KLevel) : Option KExpr :=
  let ctyI := cty.instantiateLevelParams (List.range us.length) us
  match peelForalls nOwn ctyI with
  | none => none
  | some raw =>
    let nFields := (peelAll raw).1.length
    match peelCtorParams V f nOwn 0 aux sp nOwn 0 ctyI with
    | none => none
    | some after =>
      match fieldsClassify V f es 0 0 after with
      | none => none
      | some (fds, ri, rm, _, norm) =>
        if fds.length = nFields then
          applyIhs V rm norm peers fop nP nMot nMin nFields recLvls elim
            (fieldBVars (.bvar (nP + nMot + nMin + nFields - 1 - (nP + nMot + minorIdx))) nFields
              nFields) 0 ri
        else none

/-- The rule bodies of the constructors `cs` of the inductive at `blk`, position `idx`
(`populate_rules`), the first one's minor premise the `off`-th. -/
def ruleBodies (V : ReconView) (f : Nat) (es : List FlatEntry) (fop : List Nat)
    (peers : List _root_.Address) (nP nMot nMin : Nat) (us recLvls : List KLevel) (aux : Bool)
    (sp : List KExpr) (elim : KLevel) (blk : _root_.Address) (idx off : Nat) :
    List Nat → Option (List KExpr)
  | [] => some []
  | c :: cs =>
    match V.ctor blk idx c with
    | none => none
    | some (cty, np) =>
      match ruleBody V f es fop peers cty (off + c) nP nMot nMin np us recLvls aux sp elim with
      | none => none
      | some b =>
        (ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs).map
          (b :: ·)

/-- `ctors_before_pos`: the constructors of the entries before position `k`. -/
def ctorsBefore (V : ReconView) (es : List FlatEntry) (k : Nat) : Nat :=
  ((es.take k).map fun e => ((V.ind e.addr).map IndData.nctors).getD 0).sum

/-- **`populate_rules`**: the rule bodies of the recursor at entry `k`, with `nP` parameters,
`nMot` motives, `nMin` minors and `nl` level parameters, whose peer recursors (one for each
entry) are `peers`. -/
def ruleBodiesAt (V : ReconView) (f : Nat) (es : List FlatEntry) (off nP nMot nMin nl k : Nat)
    (peers : List _root_.Address) : Option (List KExpr) :=
  match es[k]? with
  | none => none
  | some ek =>
    match V.ind ek.addr with
    | none => none
    | some self =>
      ruleBodies V f es (flatOwnParams V es) peers nP nMot nMin ek.levels
        ((List.range nl).map Ix.Kernel.Level.param) ek.aux ek.params (elimLevel off) self.blk
        self.idx (ctorsBefore V es k) (List.range self.nctors)

/-! ## A stored rule against the reconstruction -/

/-- **`rule_lam_doms`**: the term `l` under `n` λs, each with the domain of the corresponding
leading binder of `p` (up to the semantic equality of levels) and the datum of the elimination
level, is `r`. -/
inductive LamsAlong (elim : KLevel) : Nat → KExpr → KExpr → KExpr → Prop
  | zero {l p : KExpr} : LamsAlong elim 0 l p l
  | succ {n : Nat} {dl bl dp bp r : KExpr} {m mp : Ix.Kernel.BinderMeta} :
      m.pw = elim.zeronessOf → ExprLvEq dl dp → LamsAlong elim n bl bp r →
      LamsAlong elim (n + 1) (.lam dl bl m) (.forallE dp bp mp) r

/-- **`compare_rules` at one rule**: the stored right-hand side `rhs` of the rule with `nf`
fields, whose minor premise is the `minor`-th, is, under the λs of the recursor type `ty`'s
parameters, motives and minors and the λs of its minor premise's fields, the reconstructed body
`cb` (up to the semantic equality of levels). -/
def RuleFollows (ty : KExpr) (nP nMot nMin minor nf : Nat) (elim : KLevel) (rhs cb : KExpr) :
    Prop :=
  ∃ (afterPre mdom rest sb : KExpr) (mm : Ix.Kernel.BinderMeta),
    LamsAlong elim (nP + nMot + nMin) rhs ty afterPre ∧
    peelForalls (nP + nMot + minor) ty = some (.forallE mdom rest mm) ∧
    LamsAlong elim nf afterPre (mdom.liftLooseBVars (nMin - minor) 0) sb ∧ ExprLvEq sb cb

/-! ## The record-level form -/

/-- The constant addresses of a record's members, in order: the record's own recursors, the peers
of its rules. -/
def recAddrs (rb : _root_.Address) (rs : Array Ixon.MutConst) : List _root_.Address :=
  rs.toList.zipIdx.map fun p => memberAddr rb p.2 p.1

/-- **A recursor of the record `rb` against the reconstruction at its position `k`**: its type
reads (over the record's tables, positional level parameters) to `ty`, related by `TyRel` to the
reconstructed type at `k`; and each of its rules reads to a right-hand side that follows the
reconstructed body, under the λs `ty` gives, with the record's own recursors as the peers. -/
def MemberRecon (TyRel : KExpr → KExpr → Prop) (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry)
    (off fuel k : Nat) (r : Ixon.Recursor) : Prop :=
  ∃ (ty R : KExpr) (bodies : List KExpr),
    (exprReader t (fun x => E.blobs.get? x) crb id (blockSelf t rb rs)).read r.typ = .ok ty ∧
    recTypeAt (ReconView.ofStore t E) fuel es off r.params.toNat k = some R ∧ TyRel ty R ∧
    ruleBodiesAt (ReconView.ofStore t E) fuel es off r.params.toNat r.motives.toNat
      r.minors.toNat r.lvls.toNat k (recAddrs rb rs) = some bodies ∧
    ∀ (c : Nat) (ru : Ixon.RecursorRule), r.rules[c]? = some ru →
      ∃ rhs cb, (exprReader t (fun x => E.blobs.get? x) crb id (blockSelf t rb rs)).read ru.rhs =
          .ok rhs ∧ bodies[c]? = some cb ∧
        RuleFollows ty r.params.toNat r.motives.toNat r.minors.toNat
          (ctorsBefore (ReconView.ofStore t E) es k + c) ru.fields.toNat (elimLevel off) rhs cb

/-- **The family record's reconstruction, with a relation for the types**: the record `rb` of the
block `B` in the store `E` is a block of members over the flattened family `es` (`RecordFlat`),
`es` is derived from the block at the elimination offset `off` (`BlockDerivedFlat`), and, at one
fuel of head normalization, every recursor of the record is `MemberRecon TyRel` at its
position. -/
def RecordReconWith (TyRel : KExpr → KExpr → Prop) (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (B rb : _root_.Address) : Prop :=
  ∃ (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry) (off fuel : Nat),
    recordOf E rb = some crb ∧ crb.info = .muts rs ∧
    RecordFlat t E rb crb rs es ∧ BlockDerivedFlat t E B off es ∧
    ∀ (k : Nat) (r : Ixon.Recursor), rs[k]? = some (.recr r) →
      MemberRecon TyRel t E rb crb rs es off fuel k r

/-- **The record-level form a group's validation leaves a family record in**
(`canonical_rules_at_pos` with `rc_validates_group`: the state-2 arm is refused, so every
member's declared type is structurally the reconstruction): `RecordReconWith` at the semantic
equality of levels. The twin seam's canonical record is above every record the circuit accepts
for the block, which is the reconstruction or its full consumption at each member. -/
def RFormS (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B rb : _root_.Address) : Prop :=
  RecordReconWith ExprLvEq t E B rb

end IxVM.Refinement.Binding.FamilyRecon
