import IxVMRefinement.Binding.FamilyReconModel
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
The store-free part (the view's structure, the normalizer, the reconstruction, `LamsAlong`,
`RuleFollows`) is `FamilyReconModel`; here the view at a store and the record-level form.

* `ReconView`: what the reconstruction reads of a store (an inductive's level count, type,
  parameter, index and constructor counts, block and position; a constructor's type and
  parameter count and constant address; the key of an address and the address of a key; a
  definition's value at levels); `ReconView.ofStore t E`. Every term read off a record, on
  either side of the comparison, is the canonical reading (`FamilyFlat.loadedAt`): the form
  `get_ci` loads, with the binder data of the record's binder blocks at the expression's root and
  a `let` read as its reduct. (The raw reader gives every binder the datum `never`, which the
  reconstruction's binders, at the elimination level, never equal.)
* `hnfSpine`, `hnf`: the head normalization the reconstruction performs in
  `collect_n_doms_whnf`, `collect_index_doms`, `peel_ctor_params_subst` and `whnf_tele`, the
  reconstruction's own normalizer (`recon_whnf`, `recon_whnf_spine`), mirrored call by call as a
  machine on a head and a spine: a definition unfolded at a head constant applied at its level
  count, β at a λ applied (every λ, by the circuit's lifting substitution `instantiate1Lift`: the
  terms are open), and at a projection its projected term normalized and then a constructor's field
  projected under `red_proj`'s gates (`projStep`; a stuck projection keeps its normalized term). A
  projection definition applied to its arity (met in the census at Mathlib's `Lists.Equiv`) is δ
  and β to the projection, then the projection step. The normalizer reads no role and no binder
  context and takes no certificate, so one block's reconstruction is one term under every context
  that checks it.
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
