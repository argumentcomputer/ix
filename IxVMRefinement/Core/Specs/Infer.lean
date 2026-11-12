import IxVMRefinement.Core.Specs.Common

/-! # Specs: type inference (`KernelInfer`, `KernelInferOnly`)

The front door `KernelInfer::k_infer` refines `Ix.Kernel.Rules.Infer` at the full grade, the
infer-only lane `KernelInferOnly::k_infer_only` at the io grade: on a represented term, the
result represents a type the rule derives, at the opening depth `d` and ghost context `Γ` at
which the inputs are represented (`c.types Γ h d types`). Inferred types land exactly on the
kernel's: levels are related up to semantic equality (`LvEq`), so a sort's or a constant's
level that IxVM simplifies (`level_reduce`, `level_imax`, `expr_inst_levels`) still represents
the level the rule writes (`Infer.sort`'s `.succ u`, `Infer.forallE`'s `.imax u v`,
`Infer.const`'s `instantiateLevelParams`); binder data are the zero-ness of the stored level,
which is semantic (`zeronessOf_congr`).

The helpers below are stated on their own terms; the kernel-side shapes they compute are the
definitions of this file (`instPis`, `fieldTypeAt`, `PropGuards`, `PeelRed`, `SortZero`,
`SortPw`, `LitRep`). -/

namespace IxVM.Refinement.Core.Specs.Infer

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer Grade)
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false

/-! ## Kernel-side shapes -/

/-- **A literal value** (`KernelTypes::KLiteral`, held by value) reads as the kernel literal `l`:
a `Nat` literal's limbs as their value, a `String` literal's bytes as the string they encode. -/
def LitRep (h : Heap F) (v : SourceValue F) (l : Ix.Kernel.Literal) : Prop :=
  (∃ (lp : SourceValue F) (n : Nat), v = .construct klitEnum "Nat" [lp] ∧ RepLimbs h n lp ∧
      l = .natVal n) ∨
  (∃ (bp : SourceValue F) (bytes : List UInt8) (s : String), v = .construct klitEnum "Str" [bp] ∧
      RepBytes h bytes bp ∧ StrBytes s bytes ∧ l = .strVal s)

/-- **`T` is a type whose sort is zero at every assignment**, at the grade `g`: its type
head-reduces to a sort `u` with `Level.eval φ u = 0` for every `φ`. -/
def SortZero (env : Ix.Kernel.Env .anon) (g : Grade) (d : Nat) (T : KExpr) : Prop :=
  ∃ (s : KExpr) (u : KLevel), Infer env g d T s ∧ Red env d s (.sort u) ∧
    ∀ φ, Ix.Kernel.Level.eval φ u = 0

/-- **`T`'s sort has the zero-ness `pw`**, at the io grade: its io-grade type head-reduces to a
sort `v` with `zeronessOf v = pw` (`Infer.lam`'s innermost-binder premises). -/
def SortPw (env : Ix.Kernel.Env .anon) (d : Nat) (T : KExpr) (pw : Ix.Kernel.PropWhen) : Prop :=
  ∃ (s : KExpr) (v : KLevel), Infer env .io d T s ∧ Red env d s (.sort v) ∧ v.zeronessOf = pw

/-- **The first `n` binders of a `∀`-telescope instantiated by `as`**, syntactically (no
reduction), the first argument for the outermost binder: `peel_params_subst`. -/
def instPis : Nat → KExpr → List KExpr → Option KExpr
  | 0, T, _ => some T
  | n + 1, .forallE _ body _, a :: as => instPis n (body.instantiate1 a) as
  | _, _, _ => none

/-- **The type of a structure field**: in a telescope `T` of the fields from field `cur` on,
the domain `n` binders in, every field passed instantiated by its projection `.proj S j pe`
(`peel_field_loop`). -/
def fieldTypeAt (S : KKey) (pe : KExpr) : Nat → Nat → KExpr → Option KExpr
  | 0, _, .forallE dom _ _ => some dom
  | n + 1, cur, .forallE _ body _ => fieldTypeAt S pe n (cur + 1) (body.instantiate1 (.proj S cur pe))
  | _, _, _ => none

/-- **The guards of a projection out of a `Prop` structure** along the telescope
`fieldTypeAt` walks (official `infer_proj`): the projected field is a proposition, and each
field passed is a proposition or no later field's type mentions it (the rest of the telescope
has no loose bound variable). -/
def PropGuards (env : Ix.Kernel.Env .anon) (d : Nat) (S : KKey) (pe : KExpr) :
    Nat → Nat → KExpr → Prop
  | 0, _, .forallE dom _ _ => SortZero env .full d dom
  | n + 1, cur, .forallE dom body _ =>
    (SortZero env .full d dom ∨ body.looseBVarsBounded 0 = true) ∧
      PropGuards env d S pe n (cur + 1) (body.instantiate1 (.proj S cur pe))
  | _, _, _ => False

/-- **`T` head-reduces through `n` `∀`-binders to `R`**, each binder opened at the next depth
as the variable whose type is the ghost context's entry there (`peel_n_alls_whnf`, which
head-normalizes before each binder and after the last). -/
inductive PeelRed (env : Ix.Kernel.Env .anon) (Γ : Nat → KExpr) :
    Nat → KExpr → Nat → KExpr → Prop where
  | done {d : Nat} {T R : KExpr} : Red env d T R → PeelRed env Γ d T 0 R
  | step {d n : Nat} {T body R : KExpr} {m : Ix.Kernel.BinderMeta} :
      Red env d T (.forallE (Γ d) body m) →
      PeelRed env Γ (d + 1) (body.instantiate1 (.fvar d (Γ d))) n R →
      PeelRed env Γ d T (n + 1) R

/-! ## `KernelInfer` -/

/-- `types_lookup(types, i)`: **the type of the opened variable `BVar i` stands for**. The
result represents `Γ (d - 1 - i)` at depth `d` — the annotation of `BVar i`'s image
`.fvar (d - 1 - i) _`, which `Infer.fvar` returns — and `i < d` (`Infer.fvar`'s premise; the
lookup fails beyond the segment). -/
def types_lookup : SpecFn := fun c args h r h' calls =>
  ∀ (types : SourceValue F) (i : F), args = [types, .field i] → Good c calls →
    ∀ d Γ, c.types Γ h d types →
      ZMod.val i < d ∧ c.tm d Γ h' (Γ (fvIdx d 0 (ZMod.val i))) r

/-- `const_num_lvls(ci)`: **the loaded constant's level count** (`Infer.const`'s arity
premise `us.length = levelParams.length`). Allocates nothing. -/
def const_num_lvls : SpecFn := fun c args h r h' calls =>
  ∀ (v : SourceValue F) (ci : Ix.Kernel.ConstantInfo .anon), args = [v] → Good c calls →
    c.ci h v ci → r = .field (ci.toConstantVal.levelParams.length : F) ∧ h' = h

/-- `const_type_of(ci)`: **the loaded constant's type**, a closed term (`Infer.const`).
Allocates nothing. -/
def const_type_of : SpecFn := fun c args h r h' calls =>
  ∀ (v : SourceValue F) (ci : Ix.Kernel.ConstantInfo .anon), args = [v] → Good c calls →
    c.ci h v ci → c.tmc h' ci.toConstantVal.type r ∧ h' = h

/-- `k_infer(rc, e, types)`: **full-grade inference** (`Infer env .full d E T`). A term with no
loose bound variable is inferred in the empty context (the spec holds at every depth for it), a
term with some through `k_infer_rebase`. -/
def k_infer : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ T, c.tm d Γ h' T r ∧ Infer c.env .full d E T

/-- `k_infer_rebase(rc, e, types, base)`: **full-grade inference after lowering the context**:
the innermost `g` opened variables, which `e` does not mention, are dropped (`expr_lower`,
`Lists::drop`, `ctx_trim`), the inner run is at depth `d - g`, and its type is lifted back
(`expr_lift`). Stated at the caller's depth; the proof moves the inner derivation up with
`Transport.lift`. Holds for every `base` (it only trims the segment the inner run reads). -/
def k_infer_rebase : SpecFn := fun c args h r h' calls =>
  ∀ rc e types base, args = [rc, e, types, base] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ T, c.tm d Γ h' T r ∧ Infer c.env .full d E T

/-- `k_infer_core(rc, e, types)`: **one step of full-grade inference by the head node**
(`Infer.fvar`, `sort`, `const`, `natLit`, `strLit`, `forallE`, `lam`, `app` through the spine
loop, `proj`; a `let` is inferred as its ζ-reduct, the image of the node). -/
def k_infer_core : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ T, c.tm d Γ h' T r ∧ Infer c.env .full d E T

/-- `k_infer_let_start(rc, ty, val, body, types)`: **a `let`'s type is its ζ-reduct's**. The
image of `Let(ty, val, body)` is `instShift V 0 B` (`Tm.letE`); the circuit also checks the
type's sort and the value against it, which no rule reads. -/
def k_infer_let_start : SpecFn := fun c args h r h' calls =>
  ∀ rc ty val body types, args = [rc, ty, val, body, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ Ty V B, c.tm d Γ h Ty ty → c.tm d Γ h V val →
      c.tmk d Γ 1 h B body →
        ∃ T, c.tm d Γ h' T r ∧ Infer c.env .full d (instShift V 0 B) T

/-- `inst_subs(e, subs_rev)`: **the delayed substitution of an application spine**: `e`, under
as many local binders as `subs_rev` has entries, instantiated with them, the head of
`subs_rev` (the last argument consumed) for the innermost binder (`instantiateList`). -/
def inst_subs : SpecFn := fun c args h r h' calls =>
  ∀ e subs, args = [e, subs] → Good c calls →
    ∀ d Γ Ss B, c.tml d Γ h Ss subs → c.tmk d Γ Ss.length h B e →
      c.tm d Γ h' (B.instantiateList Ss 0) r

/-- `k_infer_app_spine_loop(rc, t, args, subs_rev, types)`: **the application spine**. If a term
`Fe` has the type `t` instantiated with `subs_rev` (`inst_subs`), then `Fe` applied to `args`
has the type the loop returns (`Infer.app` once per argument, each argument checked against the
domain by `k_check`; the head's type is head-normalized only when it is not syntactically a
`∀`). -/
def k_infer_app_spine_loop : SpecFn := fun c args h r h' calls =>
  ∀ rc t sp subs types, args = [rc, t, sp, subs, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ (Ss As : List KExpr) (B Fe : KExpr),
      c.tml d Γ h Ss subs → c.tmk d Γ Ss.length h B t → c.tml d Γ h As sp →
      Infer c.env .full d Fe (B.instantiateList Ss 0) →
        ∃ T, c.tm d Γ h' T r ∧ Infer c.env .full d (Ix.Kernel.Expr.mkAppN Fe As) T

/-- `k_infer_lit(rc, lit)`: **a literal's type** (`Infer.natLit`, `Infer.strLit`): the bound
`Nat` role (`role_addr`), the bound `String` role (`role_used_implicitly`). The support guards
(`natLitSupported`, `strLitSupported`) come from `EnvFacts` and the table's bindings. -/
def k_infer_lit : SpecFn := fun c args h r h' calls =>
  ∀ rc lit, args = [rc, lit] → Good c calls → c.rc h rc → ∀ l, LitRep h lit l →
    ∀ d Γ, ∃ T, c.tm d Γ h' T r ∧ Infer c.env .full d (.lit l) T

/-- `peel_params_subst(ty, args, n_params)`: **a constructor type with its first `n` binders
instantiated by the structure's parameters**, syntactically (`instPis`). -/
def peel_params_subst : SpecFn := fun c args h r h' calls =>
  ∀ ty sp np, args = [ty, sp, np] → Good c calls → ∀ n : F, np = .field n →
    ∀ d Γ T As, c.tm d Γ h T ty → c.tml d Γ h As sp →
      ∃ T', c.tm d Γ h' T' r ∧ instPis (ZMod.val n) T As = some T'

/-- `is_inductive_prop(rc, ind_ty, lvls, n_skip, types)`: **whether a structure lives in
`Prop`**, decided both ways: the inductive's type at the levels head-reduces through at most
`n_skip` binders (`peel_n_alls_whnf`) to a sort `u`; answer `1` means `u` is zero at every
assignment (`level_equal(u, 0) = 1`), answer `0` that it is not (`level_may_be_nonzero(u) = 1`,
the positive certificate the circuit asserts). The two answers are the only results. -/
def is_inductive_prop : SpecFn := fun c args h r h' calls =>
  ∀ rc ity lvls ns types, args = [rc, ity, lvls, ns, types] → Good c calls → c.rc h rc →
    ∀ n : F, ns = .field n → ∀ d Γ, c.types Γ h d types →
      ∀ (I : KExpr) (us : List KLevel), c.tmc h I ity → LvListRep h us lvls →
        ∃ (k : Nat) (Γ' : Nat → KExpr) (u : KLevel), k ≤ ZMod.val n ∧ (∀ j, j < d → Γ' j = Γ j) ∧
          PeelRed c.env Γ' d (I.instantiateLevelParams (List.range us.length) us) k (.sort u) ∧
          (r = .field 1 ∨ r = .field 0) ∧
          (r = .field 1 → ∀ φ, Ix.Kernel.Level.eval φ u = 0) ∧
          (r = .field 0 → ¬ ∀ φ, Ix.Kernel.Level.eval φ u = 0)

/-- `level_may_be_nonzero(l)`: **a positive certificate of non-zero-ness**: answer `1` means the
level is not zero at every assignment (it replaces a negative reading of
`level_equal(l, 0) = 0`). Nothing is claimed for `0`. Allocates nothing. -/
def level_may_be_nonzero : SpecFn := fun c args h r h' calls =>
  ∀ (l : SourceValue F) (u : KLevel), args = [l] → Good c calls → LvRep h u l →
    h' = h ∧ (r = .field 1 → ¬ ∀ φ, Ix.Kernel.Level.eval φ u = 0)

/-- `proj_shape_ok(n_indices, args, n_params, lvls, n_lvls)` (unit; its run is the check):
**`Infer.proj`'s arity premises**: no indices, the scrutinee type's argument count is the
parameter count, its level count is the structure's. -/
def proj_shape_ok : SpecFn := fun c args h r h' calls =>
  ∀ ni sp np lvls nl, args = [ni, sp, np, lvls, nl] → Good c calls →
    ∀ d Γ (As : List KExpr) (us : List KLevel), c.tml d Γ h As sp → LvListRep h us lvls →
      ni = .field 0 ∧ np = .field (As.length : F) ∧ nl = .field (us.length : F) ∧ h' = h

/-- `peel_n_alls_whnf(rc, e, n, types)`: **head-reduce through at most `n` binders**
(`PeelRed`): the result is at depth `d + k`, `k ≤ n` (fewer when a head-normal form is not a
`∀`), under a ghost context extending `Γ` with the opened binders' domains. -/
def peel_n_alls_whnf : SpecFn := fun c args h r h' calls =>
  ∀ rc e ns types, args = [rc, e, ns, types] → Good c calls → c.rc h rc →
    ∀ n : F, ns = .field n → ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ (k : Nat) (Γ' : Nat → KExpr) (R : KExpr), k ≤ ZMod.val n ∧ (∀ j, j < d → Γ' j = Γ j) ∧
        c.tm (d + k) Γ' h' R r ∧ PeelRed c.env Γ' d E k R

/-- `check_prop_field_if_prop(rc, is_prop, dom, types)` (unit): **at a `Prop` structure the
projected field is a proposition** (full grade). Nothing is claimed when `is_prop` is `0`. -/
def check_prop_field_if_prop : SpecFn := fun c args h r h' calls =>
  ∀ rc ip dom types, args = [rc, ip, dom, types] → Good c calls → c.rc h rc → ip ≠ .field 0 →
    ∀ d Γ, c.types Γ h d types → ∀ D, c.tm d Γ h D dom → SortZero c.env .full d D

/-- `check_no_dep_data_field_if_prop(rc, is_prop, dom, body, types)` (unit): **at a `Prop`
structure a field passed is a proposition, or the rest of the telescope does not mention it**
(the circuit asks for no loose bound variable at all in the rest). Nothing is claimed when
`is_prop` is `0`. -/
def check_no_dep_data_field_if_prop : SpecFn := fun c args h r h' calls =>
  ∀ rc ip dom body types, args = [rc, ip, dom, body, types] → Good c calls → c.rc h rc →
    ip ≠ .field 0 → ∀ d Γ, c.types Γ h d types → ∀ D B, c.tm d Γ h D dom →
      c.tmk d Γ 1 h B body → SortZero c.env .full d D ∨ B.looseBVarsBounded 0 = true

/-- `peel_field_loop(rc, ty, target, current, struct_addr, val, is_prop, types)`: **a projected
field's type** (`fieldTypeAt`): `target - current` binders into the field telescope `ty`, the
fields passed instantiated by their projections of `val`; with the `Prop`-structure guards
(`PropGuards`) when `is_prop` is not `0`. -/
def peel_field_loop : SpecFn := fun c args h r h' calls =>
  ∀ rc ty tg cu sa val ip types, args = [rc, ty, tg, cu, sa, val, ip, types] → Good c calls →
    c.rc h rc → ∀ t0 c0 : F, tg = .field t0 → cu = .field c0 →
      ∀ d Γ, c.types Γ h d types → ∀ (T : KExpr) (a : Bytes.Address) (PE : KExpr),
        c.tm d Γ h T ty → RepAddr h a sa → c.tm d Γ h PE val →
          ∃ (n : Nat) (FT : KExpr), ZMod.val c0 + n = ZMod.val t0 ∧ c.tm d Γ h' FT r ∧
            fieldTypeAt (c.κ (ixAddr a)) PE n (ZMod.val c0) T = some FT ∧
            (ip ≠ .field 0 → PropGuards c.env d (c.κ (ixAddr a)) PE n (ZMod.val c0) T)

/-- `k_infer_proj(rc, struct_addr, fidx, e1, types)`: **a projection's type**
(`Infer.proj` at the full grade): the image of `Proj(s, i, e1)` is `.proj (κ s) i PE`. -/
def k_infer_proj : SpecFn := fun c args h r h' calls =>
  ∀ rc sa fi e1 types, args = [rc, sa, fi, e1, types] → Good c calls → c.rc h rc →
    ∀ i : F, fi = .field i → ∀ d Γ, c.types Γ h d types →
      ∀ (a : Bytes.Address) (PE : KExpr), RepAddr h a sa → c.tm d Γ h PE e1 →
        ∃ T, c.tm d Γ h' T r ∧ Infer c.env .full d (.proj (c.κ (ixAddr a)) (ZMod.val i) PE) T

/-- `k_ensure_sort(rc, e, types)`: **`e` is a type**: its full-grade type head-reduces to a sort
whose level the result represents (up to semantic equality). -/
def k_ensure_sort : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ (T : KExpr) (u : KLevel), Infer c.env .full d E T ∧ Red c.env d T (.sort u) ∧ LvRep h' u r

/-- `k_check(rc, e, expected, types)` (unit; its run is the check): **`e` has a full-grade type
definitionally equal to `expected`** (`k_is_def_eq(…) = 1`). -/
def k_check : SpecFn := fun c args h r h' calls =>
  ∀ rc e x types, args = [rc, e, x, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E X, c.tm d Γ h E e → c.tm d Γ h X x →
      ∃ T, Infer c.env .full d E T ∧ DefEq c.env d T X

/-! ## `KernelInferOnly` -/

/-- `io_types_lookup(types, i)`: as `types_lookup`. -/
def io_types_lookup : SpecFn := types_lookup

/-- `io_const_num_lvls(ci)`: as `const_num_lvls`. -/
def io_const_num_lvls : SpecFn := const_num_lvls

/-- `io_const_type_of(ci)`: as `const_type_of`. -/
def io_const_type_of : SpecFn := const_type_of

/-- `k_infer_only(rc, e, types)`: **io-grade inference** (`Infer env .io d E T`): the infer-only
lane, which checks no domain sort at a `λ` and no argument certificate at a binder whose datum
is `never` (`Infer.appSkip`). -/
def k_infer_only : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ T, c.tm d Γ h' T r ∧ Infer c.env .io d E T

/-- `k_infer_only_core(rc, e, types)`: **one step of io-grade inference by the head node**. -/
def k_infer_only_core : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ T, c.tm d Γ h' T r ∧ Infer c.env .io d E T

/-- `io_app_cod(rc, dom, cod, bl, a, types)`: **an application's io-grade type**, given the head's
type head-normalized to `∀ dom, cod` with the datum `bl`: the codomain instantiated by the
argument, and `Infer.appSkip`'s or `Infer.app`'s argument premise (the datum is `never`, or the
argument's io-grade type is definitionally equal to the domain). -/
def io_app_cod : SpecFn := fun c args h r h' calls =>
  ∀ rc dom cod bl a types, args = [rc, dom, cod, bl, a, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ (D C : KExpr) (ℓ : KLevel) (A : KExpr),
      c.tm d Γ h D dom → c.tmk d Γ 1 h C cod → RepKLevel h ℓ bl → c.tm d Γ h A a →
        c.tm d Γ h' (C.instantiate1 A) r ∧
          ((bmeta ℓ).pw.isNever = true ∨ ∃ TA, Infer c.env .io d A TA ∧ DefEq c.env d TA D)

/-- `forall_datum_ok(v, bl)` (unit): **`Infer.forallE`'s datum premise**: the binder's datum is
the zero-ness of the body's sort `v` (`pw_eq(v, bl) = 1`). -/
def forall_datum_ok : SpecFn := fun c args h r h' calls =>
  ∀ v bl, args = [v, bl] → Good c calls →
    ∀ (u ℓ : KLevel), LvRep h u v → RepKLevel h ℓ bl → u.zeronessOf = (bmeta ℓ).pw

/-- `lam_datum_ok(rc, body, body_ty, bl, types2)` (unit): **`Infer.lam`'s datum premises**, at the
depth of the opened body: at a `λ` whose body node is a `λ`, the two data agree; otherwise the
datum is the zero-ness of the sort of the body's type, at the io grade (`SortPw`). (A body that
is a `let` of a `λ` takes the second case; its image is a `λ`, and `Infer.lam`'s first premise
then follows from the inner `λ`'s own check.) -/
def lam_datum_ok : SpecFn := fun c args h r h' calls =>
  ∀ rc body bt bl types, args = [rc, body, bt, bl, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ (Bo Bt : KExpr) (ℓ : KLevel),
      c.tm d Γ h Bo body → c.tm d Γ h Bt bt → RepKLevel h ℓ bl →
        (∃ (T' B' : KExpr) (ℓ' : KLevel), Bo = .lam T' B' (bmeta ℓ') ∧ (bmeta ℓ).pw = (bmeta ℓ').pw) ∨
          SortPw c.env d Bt (bmeta ℓ).pw

/-- `ensure_sort_only(rc, e, types)`: **`e` is a type, at the io grade**: its io-grade type
(head-normalized when not syntactically a sort) is a sort whose level the result represents. -/
def ensure_sort_only : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ (T : KExpr) (u : KLevel), Infer c.env .io d E T ∧ Red c.env d T (.sort u) ∧ LvRep h' u r

/-- `io_prop_field_guard(rc, is_prop, field_ty, types)` (unit): **at a `Prop` structure the
projected field is a proposition**, at the io grade. Nothing is claimed when `is_prop` is `0`.
(Unlike the full grade, the fields passed are not checked.) -/
def io_prop_field_guard : SpecFn := fun c args h r h' calls =>
  ∀ rc ip ft types, args = [rc, ip, ft, types] → Good c calls → c.rc h rc → ip ≠ .field 0 →
    ∀ d Γ, c.types Γ h d types → ∀ FT, c.tm d Γ h FT ft → SortZero c.env .io d FT

/-- `io_peel_params_subst(ty, args, n_params)`: as `peel_params_subst`. -/
def io_peel_params_subst : SpecFn := peel_params_subst

/-- `io_peel_field_loop(ty, target, current, struct_addr, val)`: **a projected field's type**
(`fieldTypeAt`), without guards. -/
def io_peel_field_loop : SpecFn := fun c args h r h' calls =>
  ∀ ty tg cu sa val, args = [ty, tg, cu, sa, val] → Good c calls →
    ∀ t0 c0 : F, tg = .field t0 → cu = .field c0 →
      ∀ d Γ (T : KExpr) (a : Bytes.Address) (PE : KExpr),
        c.tm d Γ h T ty → RepAddr h a sa → c.tm d Γ h PE val →
          ∃ (n : Nat) (FT : KExpr), ZMod.val c0 + n = ZMod.val t0 ∧ c.tm d Γ h' FT r ∧
            fieldTypeAt (c.κ (ixAddr a)) PE n (ZMod.val c0) T = some FT

/-! ## The family -/

/-- The functions of `KernelInfer` and `KernelInferOnly`. -/
inductive Fn where
  | types_lookup | const_num_lvls | const_type_of | k_infer | k_infer_rebase | k_infer_core
  | k_infer_let_start | inst_subs | k_infer_app_spine_loop | k_infer_lit | peel_params_subst
  | is_inductive_prop | level_may_be_nonzero | proj_shape_ok | peel_n_alls_whnf
  | check_prop_field_if_prop | check_no_dep_data_field_if_prop | peel_field_loop | k_infer_proj
  | k_ensure_sort | k_check
  | io_types_lookup | io_const_num_lvls | io_const_type_of | k_infer_only | k_infer_only_core
  | io_app_cod | forall_datum_ok | lam_datum_ok | ensure_sort_only | io_prop_field_guard
  | io_peel_params_subst | io_peel_field_loop
  deriving DecidableEq, Repr

/-- The function's symbol. -/
def Fn.name : Fn → String
  | .types_lookup => "KernelInfer::types_lookup"
  | .const_num_lvls => "KernelInfer::const_num_lvls"
  | .const_type_of => "KernelInfer::const_type_of"
  | .k_infer => "KernelInfer::k_infer"
  | .k_infer_rebase => "KernelInfer::k_infer_rebase"
  | .k_infer_core => "KernelInfer::k_infer_core"
  | .k_infer_let_start => "KernelInfer::k_infer_let_start"
  | .inst_subs => "KernelInfer::inst_subs"
  | .k_infer_app_spine_loop => "KernelInfer::k_infer_app_spine_loop"
  | .k_infer_lit => "KernelInfer::k_infer_lit"
  | .peel_params_subst => "KernelInfer::peel_params_subst"
  | .is_inductive_prop => "KernelInfer::is_inductive_prop"
  | .level_may_be_nonzero => "KernelInfer::level_may_be_nonzero"
  | .proj_shape_ok => "KernelInfer::proj_shape_ok"
  | .peel_n_alls_whnf => "KernelInfer::peel_n_alls_whnf"
  | .check_prop_field_if_prop => "KernelInfer::check_prop_field_if_prop"
  | .check_no_dep_data_field_if_prop => "KernelInfer::check_no_dep_data_field_if_prop"
  | .peel_field_loop => "KernelInfer::peel_field_loop"
  | .k_infer_proj => "KernelInfer::k_infer_proj"
  | .k_ensure_sort => "KernelInfer::k_ensure_sort"
  | .k_check => "KernelInfer::k_check"
  | .io_types_lookup => "KernelInferOnly::io_types_lookup"
  | .io_const_num_lvls => "KernelInferOnly::io_const_num_lvls"
  | .io_const_type_of => "KernelInferOnly::io_const_type_of"
  | .k_infer_only => "KernelInferOnly::k_infer_only"
  | .k_infer_only_core => "KernelInferOnly::k_infer_only_core"
  | .io_app_cod => "KernelInferOnly::io_app_cod"
  | .forall_datum_ok => "KernelInferOnly::forall_datum_ok"
  | .lam_datum_ok => "KernelInferOnly::lam_datum_ok"
  | .ensure_sort_only => "KernelInferOnly::ensure_sort_only"
  | .io_prop_field_guard => "KernelInferOnly::io_prop_field_guard"
  | .io_peel_params_subst => "KernelInferOnly::io_peel_params_subst"
  | .io_peel_field_loop => "KernelInferOnly::io_peel_field_loop"

/-- The function's spec. -/
def Fn.spec : Fn → SpecFn
  | .types_lookup => Specs.Infer.types_lookup
  | .const_num_lvls => Specs.Infer.const_num_lvls
  | .const_type_of => Specs.Infer.const_type_of
  | .k_infer => Specs.Infer.k_infer
  | .k_infer_rebase => Specs.Infer.k_infer_rebase
  | .k_infer_core => Specs.Infer.k_infer_core
  | .k_infer_let_start => Specs.Infer.k_infer_let_start
  | .inst_subs => Specs.Infer.inst_subs
  | .k_infer_app_spine_loop => Specs.Infer.k_infer_app_spine_loop
  | .k_infer_lit => Specs.Infer.k_infer_lit
  | .peel_params_subst => Specs.Infer.peel_params_subst
  | .is_inductive_prop => Specs.Infer.is_inductive_prop
  | .level_may_be_nonzero => Specs.Infer.level_may_be_nonzero
  | .proj_shape_ok => Specs.Infer.proj_shape_ok
  | .peel_n_alls_whnf => Specs.Infer.peel_n_alls_whnf
  | .check_prop_field_if_prop => Specs.Infer.check_prop_field_if_prop
  | .check_no_dep_data_field_if_prop => Specs.Infer.check_no_dep_data_field_if_prop
  | .peel_field_loop => Specs.Infer.peel_field_loop
  | .k_infer_proj => Specs.Infer.k_infer_proj
  | .k_ensure_sort => Specs.Infer.k_ensure_sort
  | .k_check => Specs.Infer.k_check
  | .io_types_lookup => Specs.Infer.io_types_lookup
  | .io_const_num_lvls => Specs.Infer.io_const_num_lvls
  | .io_const_type_of => Specs.Infer.io_const_type_of
  | .k_infer_only => Specs.Infer.k_infer_only
  | .k_infer_only_core => Specs.Infer.k_infer_only_core
  | .io_app_cod => Specs.Infer.io_app_cod
  | .forall_datum_ok => Specs.Infer.forall_datum_ok
  | .lam_datum_ok => Specs.Infer.lam_datum_ok
  | .ensure_sort_only => Specs.Infer.ensure_sort_only
  | .io_prop_field_guard => Specs.Infer.io_prop_field_guard
  | .io_peel_params_subst => Specs.Infer.io_peel_params_subst
  | .io_peel_field_loop => Specs.Infer.io_peel_field_loop

end IxVM.Refinement.Core.Specs.Infer
