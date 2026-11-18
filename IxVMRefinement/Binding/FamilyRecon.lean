import IxVMRefinement.Binding.FamilyFlat
import IxVMRefinement.Core.Det
import IxVMRefinement.Callees.RouteDispatch

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
  definition's value at levels); `ReconView.ofStore t E`. Every term read off a record, on
  either side of the comparison, is the canonical reading (`FamilyFlat.loadedAt`): the form
  `get_ci` loads, with the binder data of the record's binder blocks at the expression's root and
  a `let` read as its reduct. (The raw reader gives every binder the datum `never`, which the
  reconstruction's binders, at the elimination level, never equal.)
* `hnf`: the head normalization the reconstruction performs (`whnf` in `collect_n_doms_whnf`,
  `collect_index_doms`, `peel_ctor_params_subst`, `whnf_tele`), modelled as the δβ head
  strategy with projections: a definition unfolded at a head constant, β at a λ applied, the
  function of an application, and at a projection its projected term normalized and then a
  constructor's field projected under `red_proj`'s gates (`projStep`; a stuck projection keeps its
  normalized term, as `whnf_proj_head` does), to a term with no such step. A projection
  definition applied to its arity (`try_reduce_projection_definition`, met in the census at
  Mathlib's `Lists.Equiv`) is δ and β to the projection, then the projection step. β substitutes
  by the circuit's lifting substitution (`instantiate1Lift`): the terms are open. Where the
  circuit's `whnf` takes another step on the reconstruction's inputs (ζ, ι, a primitive
  operation, a quotient, a literal, a string literal expanded under a projection) the model
  departs from it; that the circuit takes none there is the fidelity obligation of the head
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
* `MemberRecon TyRel`: a recursor of the record, at its position `k`, relates its declared type
  (canonical reading at the member's root) to the reconstructed type by `TyRel` and each rule
  (canonical reading at its root) follows the reconstructed body, with the record's own recursors
  as the peers. **`RFormS`**: the record is the block's family over the
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

/-- What `get_ci` gives of a constructor (`convert_constructor`): its level count, its block, its
inductive's position in the block, its parameter and field counts. -/
structure CtorData where
  nl : Nat
  blk : _root_.Address
  ind : Nat
  np : Nat
  nf : Nat

/-- **What the reconstruction reads of a store**: `get_ci` at an inductive's address, a
constructor's type and parameter count (`get_ci_cprj`), a constructor's constant address
(`projection_addr_ctor`), the key a constant's address reads as, the address a key names, a
definition's value at given levels (the unfolding `whnf` performs), `get_ci`'s constructor arm at
a constant address, and whether a block is on the modeled route (`block_is_modeled`; the last two
for `red_proj`). Each answer is `none` where the circuit's load fails, so a store that holds more
answers the same where the first answers. -/
structure ReconView where
  ind : _root_.Address → Option IndData
  ctor : _root_.Address → Nat → Nat → Option (KExpr × Nat)
  ctorAddr : _root_.Address → Nat → Nat → _root_.Address
  key : _root_.Address → KKey
  addr : KKey → Option _root_.Address
  unfold : KKey → List KLevel → Option (Option KExpr)
  ctorOf : _root_.Address → Option (Option CtorData)
  modeled : _root_.Address → Option Bool

/-- `get_ci` at an inductive type's address of the store: through its projection record, the
member of its block, its type in the canonical reading over the block's tables at the member's
root (`loadedAt`). -/
noncomputable def indDataAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (a : _root_.Address) :
    Option IndData :=
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
            match loadedAt t (fun x => E.blobs.get? x) cb (blockSelf t p.block ms)
                ind.lvls.toNat (mutsRoot ms p.idx.toNat) ind.typ with
            | none => none
            | some ty =>
              some ⟨ind.lvls.toNat, ty, ind.params.toNat, ind.indices.toNat, ind.ctors.size,
                p.block, p.idx.toNat⟩
          | _ => none
        | _ => none
    | _ => none

/-- `get_ci_cprj blk i c`: constructor `c` of member `i` of the block at `b`, its type in the
canonical reading over the block's tables at the constructor's root, and its parameter count. -/
noncomputable def ctorAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (b : _root_.Address)
    (i c : Nat) : Option (KExpr × Nat) :=
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
          match loadedAt t (fun x => E.blobs.get? x) cb (blockSelf t b ms) ctor.lvls.toNat
              (mutsRoot ms i + 1 + ((c : Nat) : IxVM.F)) ctor.typ with
          | none => none
          | some ty => some (ty, ctor.params.toNat)
      | _ => none
    | _ => none

/-- A definition's level count and value at a constant address of the store (`get_ci`'s `Defn`,
in the canonical reading with positional level parameters: a standalone record's value at root
`1`, a block member's at its root plus `1`): a standalone definition record, or a definition
member of a block. `none` where the circuit's load fails (no record, an unreadable value);
`some none` at a constant `whnf` does not unfold by a definition step (a theorem, an opaque
constant, any other kind). -/
noncomputable def defnAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (a : _root_.Address) :
    Option (Option (Nat × KExpr)) :=
  match recordOf E a with
  | none => none
  | some c =>
    match c.info with
    | .defn d =>
      match d.kind with
      | .defn =>
        (loadedAt t (fun x => E.blobs.get? x) c (soloSelf t a) d.lvls.toNat 1 d.value).map
          fun v => some (d.lvls.toNat, v)
      | _ => some none
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
              (loadedAt t (fun x => E.blobs.get? x) cb (blockSelf t p.block ms) d.lvls.toNat
                (mutsRoot ms p.idx.toNat + 1) d.value).map fun v => some (d.lvls.toNat, v)
            | _ => some none
          | _ => none
        | _ => none
    | _ => some none

/-- `red_unfold` at a key: the definition's value with its level parameters instantiated, when the
levels' count is the definition's (`some none` when no definition step applies, `none` where the
load fails). -/
noncomputable def unfoldAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (k : KKey)
    (us : List KLevel) :
    Option (Option KExpr) :=
  match keyAddr t k with
  | none => some none
  | some a =>
    match defnAt t E a with
    | none => none
    | some none => some none
    | some (some (n, v)) =>
      if us.length = n then some (some (v.instantiateLevelParams (List.range n) us))
      else some none

/-- `get_ci` at a constant address of the store, its constructor arm (`convert_constructor`):
through the constructor's projection record, the member of its block and the constructor, its
level count, block, inductive's position, parameter and field counts; `some none` at a constant of
another kind; `none` where the load fails. -/
def ctorOfAt (E : Ixon.Env) (a : _root_.Address) : Option (Option CtorData) :=
  match recordOf E a with
  | none => none
  | some c =>
    match c.info with
    | .cPrj p =>
      match recordOf E p.block with
      | none => none
      | some cb =>
        match cb.info with
        | .muts ms =>
          match ms[p.idx.toNat]? with
          | some (.indc ind) =>
            match ind.ctors[p.cidx.toNat]? with
            | some ctor =>
              some (some ⟨ctor.lvls.toNat, p.block, p.idx.toNat, ctor.params.toNat,
                ctor.fields.toNat⟩)
            | none => none
          | _ => none
        | _ => none
    | _ => some none

/-- **The readings of the store `E`** under the role table `t`; whether a block is on the modeled
route is the dispatch's answer (`Route.blockRoute`, the model of `block_is_modeled`). -/
noncomputable def ReconView.ofStore (t : Ix.Kernel.RoleTable) (E : Ixon.Env) : ReconView :=
  ⟨indDataAt t E, ctorAt t E, IxVM.Consistency.ctorAddr, keyOf t, keyAddr t, unfoldAt t E,
    ctorOfAt E, Route.blockRoute E⟩

/-! ## Head normalization: the δβ head strategy, with projections -/

/-- The body of a λ. -/
def lamBody : KExpr → Option KExpr
  | .lam _ b _ => some b
  | _ => none

/-- The binder at the head of a term: its domain, body and datum. -/
def isForall : KExpr → Option (KExpr × KExpr × Ix.Kernel.BinderMeta)
  | .forallE d b m => some (d, b, m)
  | _ => none

/-- **`type_sort_never`**: the sort a type former's telescope ends in, after `n` binders and at
the levels `us`, is never zero (`level_is_not_zero` after `level_inst_params`); `false` at another
shape. -/
def typeSortNever : KExpr → Nat → List KLevel → Bool
  | .forallE _ b _, n + 1, us => typeSortNever b n us
  | .sort l, 0, us => (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero
  | _, _, _ => false

/-- `red_proj`'s gates at a constructor `cd` applied at the levels `cus` to `args`, projected
through the structure `sd` at field `i`: the constructor is the structure's (its block, position
and level count), the structure has no index, one constructor and the constructor's parameter
count, the application is full at the constructor's levels, and the field exists. -/
def projGate (cd : CtorData) (sd : IndData) (cus : List KLevel) (args : List KExpr) (i : Nat) :
    Bool :=
  cd.blk == sd.blk && cd.ind == sd.idx && sd.nl == cd.nl && sd.ni == 0 && sd.nctors == 1 &&
    sd.np == cd.np && args.length == cd.np + cd.nf && cus.length == cd.nl && decide (i < cd.nf)

/-- **`red_proj`** on a head-normal projected term `e` (`whnf_proj_head`): where `e` is a
constructor applied, of the structure `s`, past `red_proj`'s gates (`projGate`), with the
structure's block off the modeled route and its sort never zero at the constructor's levels
(`type_sort_never`), the field `i`: argument `params + i`. `some none`: no step; `none`: a load
fails. (`str_lit_to_ctor_app_or_self`'s string literal is not modelled: there the model takes no
step.) -/
def projStep (V : ReconView) (s : KKey) (i : Nat) (e : KExpr) : Option (Option KExpr) :=
  match Ix.Kernel.Expr.getAppFn e with
  | .const ck cus =>
    match V.addr ck with
    | none => some none
    | some ca =>
      match V.ctorOf ca with
      | none => none
      | some none => some none
      | some (some cd) =>
        match V.addr s with
        | none => some none
        | some sa =>
          match V.ind sa with
          | none => none
          | some sd =>
            if projGate cd sd cus (Ix.Kernel.Expr.getAppArgs e) i then
              match V.modeled sd.blk with
              | none => none
              | some true => some none
              | some false =>
                if typeSortNever sd.ty sd.np cus then
                  some ((Ix.Kernel.Expr.getAppArgs e)[cd.np + i]?)
                else some none
            else some none
  | _ => some none

/-- A projection's step: a step of the projected term, else `red_proj` on it (`projStep`). -/
def projCase (V : ReconView) (s : KKey) (i : Nat) (e : KExpr) :
    Option (Option KExpr) → Option (Option KExpr)
  | none => none
  | some (some e') => some (some (.proj s i e'))
  | some none => projStep V s i e

/-- One head step: a definition unfolded at a constant, β at a λ applied (the circuit's
substitution, which lifts the argument past the binders it crosses), a step of an application's
function, or at a projection a step of the projected term and then `red_proj` (`whnf_proj_head`:
the projected term head-normalized, a constructor's field projected). A projection definition
applied to its arity (`try_reduce_projection_definition`) is the definition unfolded and its λs
applied, which these steps take. `some none`: no step applies; `none`: a load fails. -/
def headStep (V : ReconView) : KExpr → Option (Option KExpr)
  | .const k us => V.unfold k us
  | .app f a =>
    match lamBody f with
    | some b => some (some (Ix.Kernel.Expr.instantiate1Lift b a 0))
    | none => (headStep V f).map (Option.map fun f' => .app f' a)
  | .proj s i e => projCase V s i e (headStep V e)
  | _ => some none

/-- **Head normalization** at a fuel of steps: head steps until none applies. -/
def hnf (V : ReconView) : Nat → KExpr → Option KExpr
  | 0, _ => none
  | n + 1, e =>
    match headStep V e with
    | none => none
    | some none => some e
    | some (some e') => hnf V n e'

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

/-- The head binder of a telescope, head-normalizing where it is not syntactically one (`some none`
when the head normal form is no binder). -/
def binderOf (V : ReconView) (f : Nat) (ty : KExpr) :
    Option (Option (KExpr × KExpr × Ix.Kernel.BinderMeta)) :=
  match isForall ty with
  | some p => some (some p)
  | none => (hnf V f ty).map isForall

/-- **`collect_n_doms_whnf`, `collect_index_doms`**: the first `n` binder domains of a telescope,
head-normalizing where it is not syntactically a binder, and what follows them; fewer domains when
the head normal form is no binder. -/
def collectDoms (V : ReconView) (f : Nat) : Nat → KExpr → Option (List KExpr × KExpr)
  | 0, ty => some ([], ty)
  | n + 1, ty =>
    match binderOf V f ty with
    | none => none
    | some none => some ([], ty)
    | some (some (d, b, _)) => (collectDoms V f n b).map fun p => (d :: p.1, p.2)

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
  | n + 1, j, ty =>
    match isForall ty with
    | some (_, b, _) =>
      peelMotiveParams nrp aux sp n (j + 1)
        (Ix.Kernel.Expr.instantiate1Lift b (substParamFor j nrp aux sp) 0)
    | none => none

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
  | n + 1, j, ty =>
    match binderOf V f ty with
    | some (some (_, b, _)) =>
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
    | some w =>
      match isForall w with
      | some (d, b, m) => (whnfTele V f n b).map fun b' => .forallE d b' m
      | none => some w

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
def isRecField (V : ReconView) (es : List FlatEntry) (liftBy : Nat) (e : KExpr) : Option Nat :=
  match Ix.Kernel.Expr.getAppFn (peelAll e).2 with
  | .const k us =>
    match V.addr k with
    | some a => flatFindMatching es a us (Ix.Kernel.Expr.getAppArgs (peelAll e).2) liftBy
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

/-- `build_flat_own_params`: each entry's parameter count (every entry an inductive type). -/
def flatOwnParams (V : ReconView) : List FlatEntry → Option (List Nat)
  | [] => some []
  | e :: es =>
    match V.ind e.addr, flatOwnParams V es with
    | some i, some ns => some (i.np :: ns)
    | _, _ => none

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
        match allMotives V f elim nP es 0, flatOwnParams V es with
        | some motDoms, some fop =>
          match allMinors V f es fop nP nMot nP elim es 0 0 with
          | none => none
          | some minDoms =>
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
                  (liftIndices idxRaw (nMot + nMin)) elim) minDoms elim) motDoms elim)
                  paramDoms elim)
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
def ctorsBefore (V : ReconView) : List FlatEntry → Nat → Option Nat
  | _, 0 => some 0
  | [], _ + 1 => some 0
  | e :: es, k + 1 =>
    match V.ind e.addr, ctorsBefore V es k with
    | some i, some n => some (i.nctors + n)
    | _, _ => none

/-- **`populate_rules`**: the rule bodies of the recursor at entry `k`, with `nP` parameters,
`nMot` motives, `nMin` minors and `nl` level parameters, whose peer recursors (one for each
entry) are `peers`. -/
def ruleBodiesAt (V : ReconView) (f : Nat) (es : List FlatEntry) (off nP nMot nMin nl k : Nat)
    (peers : List _root_.Address) : Option (List KExpr) :=
  match es[k]? with
  | none => none
  | some ek =>
    match V.ind ek.addr, flatOwnParams V es, ctorsBefore V es k with
    | some self, some fop, some cb =>
      ruleBodies V f es fop peers nP nMot nMin ek.levels
        ((List.range nl).map Ix.Kernel.Level.param) ek.aux ek.params (elimLevel off) self.blk
        self.idx cb (List.range self.nctors)
    | _, _, _ => none

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
of its rules. The circuit's peer of an entry (`build_peer_recs`, `find_peer_recursor_with_spec`)
is the first recursor of the record whose major premise names the entry's address, and at an
auxiliary also its parameters and levels; `RecordFlat` ties recursor `k` to entry `k` with its
parameters and levels, so over entries that differ the peer of entry `k` is recursor `k`. -/
def recAddrs (rb : _root_.Address) (rs : Array Ixon.MutConst) : List _root_.Address :=
  rs.toList.zipIdx.map fun p => memberAddr rb p.2 p.1

/-- **A recursor of the record `rb` against the reconstruction at its position `k`**: its type,
in the canonical reading over the record's tables at the member's root (`loadedAt`, positional
level parameters, the binder data of the record's binder blocks: the form `check_recs` loads), is
`ty`, related by `TyRel` to the reconstructed type at `k`; and each rule `c`'s right-hand side, in
the canonical reading at the root after the type's plus `c`, follows the reconstructed body under
the λs `ty` gives, with the record's own recursors as the peers. -/
def MemberRecon (TyRel : KExpr → KExpr → Prop) (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry)
    (off fuel k : Nat) (r : Ixon.Recursor) : Prop :=
  ∃ (ty R : KExpr) (bodies : List KExpr) (cbk : Nat),
    loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat (mutsRoot rs k)
      r.typ = some ty ∧
    recTypeAt (ReconView.ofStore t E) fuel es off r.params.toNat k = some R ∧ TyRel ty R ∧
    ruleBodiesAt (ReconView.ofStore t E) fuel es off r.params.toNat r.motives.toNat
      r.minors.toNat r.lvls.toNat k (recAddrs rb rs) = some bodies ∧
    ctorsBefore (ReconView.ofStore t E) es k = some cbk ∧
    ∀ (c : Nat) (ru : Ixon.RecursorRule), r.rules[c]? = some ru →
      ∃ rhs cb, loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs k + 1 + ((c : Nat) : IxVM.F)) ru.rhs = some rhs ∧ bodies[c]? = some cb ∧
        RuleFollows ty r.params.toNat r.motives.toNat r.minors.toNat
          (cbk + c) ru.fields.toNat (elimLevel off) rhs cb

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
equality of levels, every term read off the store in the canonical reading (`loadedAt`), as the
circuit loads it. The twin seam's canonical record is above every record the circuit accepts
for the block, which is the reconstruction or its full consumption at each member. -/
def RFormS (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B rb : _root_.Address) : Prop :=
  RecordReconWith ExprLvEq t E B rb

end IxVM.Refinement.Binding.FamilyRecon
