import IxVMRefinement.Core.Specs.Common

/-! # Registry specs: substitution (`KernelSubst`), spines, level instantiation

The spec of every in-scope `KernelSubst` function, of `KernelTypes::collect_spine` and of
`KernelLevels::expr_inst_levels(_walk)`, the substitution package's functions.

**Readings.** A heap term `e` is read at a local binder depth `k` and an opening depth `d`
(`c.tmk d Γ k h E e`). IxVM's de Bruijn arithmetic moves a term between readings without
changing its image:

* lifting by `s` at the cutoff `k` (`expr_lift`) reads the result at local depth `k + s₁` and
  opening depth `d + s₂`, for any split `s = s₁ + s₂` (`types_lookup` lifts a context entry from
  the depth it was opened at, `s₁ = 0`; `expr_inst1` lifts the argument under the binders it
  passed, `s₂ = 0`);
* lowering by `s` at the cutoff `k` (`expr_lower`) is the inverse, given that the removed
  indices do not occur: no loose `bvar` at or above `k - s₁` (`looseBVarsBounded`) and no
  opened variable at or above `d - s₂` (`fvarRange`) in the image;
* instantiation (`expr_inst1`, `expr_inst_many`) at the cutoff `j` reads the term at local depth
  `j + n` and the result at local depth `j`, with the kernel's `instantiate1`/`instantiateList`
  at index `j` (the arguments are top-level terms, so they have no loose `bvar` and the kernel's
  non-lifting substitution is the right one).

**Index bounds.** The term seam bounds every de Bruijn index by `2^63` (`Tm`). IxVM compares
indices with `UInt32::less_than_fields`, which fails above `2^32`, everywhere except
`expr_lbr`'s `BVar(i) ↦ i + 1`; so an index IxVM computes stays below `2^63` when it adds at
most `2^62` to an index that passed a comparison. The one hypothesis this needs is on
`expr_lift`'s shift (`s < 2^62`, below); `expr_inst1` and `expr_inst_many` lift by their depth,
which their own comparisons bound by `2^32`. Binder nesting is bounded through `Good` (a
represented term has at most as many nested nodes as the ROM has addresses), so `depth + 1`
under a binder does not wrap. -/

namespace IxVM.Refinement.Core.Specs.Subst

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-! ## Vocabulary -/

/-- The bound on de Bruijn indices of the term seam. -/
abbrev idxBound : Nat := 9223372036854775808

/-- **A de Bruijn index read as a kernel term**: the index `i`, at local depth `k` and opening
depth `d`, is the local `.bvar i` or the opened variable `fvIdx d k i` with its type (as `Tm`'s
two `BVar` constructors). -/
def BVarIm (d : Nat) (Γ : Nat → KExpr) (k i : Nat) (E : KExpr) : Prop :=
  i < idxBound ∧
    ((i < k ∧ E = .bvar i) ∨ (k ≤ i ∧ i - k < d ∧ E = .fvar (fvIdx d k i) (Γ (fvIdx d k i))))

/-- **No loose bound variable of `E` in `[lo, hi)`** (shifted under binders). -/
def noBVarIn (lo hi : Nat) : KExpr → Bool
  | .bvar i => !(decide (lo ≤ i) && decide (i < hi))
  | .fvar _ _ | .sort _ | .const _ _ | .lit _ => true
  | .app f a => noBVarIn lo hi f && noBVarIn lo hi a
  | .lam ty b _ | .forallE ty b _ => noBVarIn lo hi ty && noBVarIn (lo + 1) (hi + 1) b
  | .letE ty v b _ => noBVarIn lo hi ty && noBVarIn lo hi v && noBVarIn (lo + 1) (hi + 1) b
  | .proj _ _ e => noBVarIn lo hi e

/-- **No opened variable of `E` with an index in `[lo, hi)`** (an `fvar`'s type annotation is
not entered). -/
def noFvarIn (lo hi : Nat) : KExpr → Bool
  | .fvar j _ => !(decide (lo ≤ j) && decide (j < hi))
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .app f a => noFvarIn lo hi f && noFvarIn lo hi a
  | .lam ty b _ | .forallE ty b _ => noFvarIn lo hi ty && noFvarIn lo hi b
  | .letE ty v b _ => noFvarIn lo hi ty && noFvarIn lo hi v && noFvarIn lo hi b
  | .proj _ _ e => noFvarIn lo hi e

/-- **No index in `[lo, hi)` occurs** in the image `E` of a heap term read at local depth `k`
and opening depth `d`: neither a local one as a loose `bvar`, nor a free one as the opened
variable it stands for (index `i ≥ k` is the opened variable `d + k - 1 - i`). -/
def Avoids (d k lo hi : Nat) (E : KExpr) : Prop :=
  noBVarIn lo hi E = true ∧ noFvarIn (d + k - hi) (d + k - max lo k) E = true

/-- **`b` bounds the indices of the heap term `p`** read at local depth `k` as `E`: when
`b ≤ k`, the image has no loose `bvar` at or above `b`, no opened variable, and the heap term
reads as the same `E` at every opening depth and context and every local depth `≥ b`. -/
def LbrLe (c : Ctx) (h : Heap F) (p : SourceValue F) (k : Nat) (E : KExpr) (b : Nat) : Prop :=
  b ≤ k → E.looseBVarsBounded b = true ∧ E.hasFvar = false ∧
    ∀ d' Γ' k', b ≤ k' → c.tmk d' Γ' k' h E p

/-! ## Loose-bound ranges -/

/-- `KernelSubst::expr_lbr(e)`: **one more than the largest loose index**, as a natural `b`
(`r = b`, `b ≤ 2^63`, no wrap: the term seam's bound), with `b ≤ k + d` and `LbrLe`. Allocates
nothing. Read by the rebases (`k_infer`, `k_is_def_eq`: `0` runs under an empty context), by
`ctx_trim`, and by the closedness assertions of inference. -/
def expr_lbr : SpecFn := fun c args h r h' calls =>
  ∀ e, args = [e] → Good c calls → h' = h ∧
    ∀ d Γ k E, c.tmk d Γ k h E e →
      ∃ b : Nat, r = .field (b : F) ∧ b ≤ idxBound ∧ b ≤ k + d ∧ LbrLe c h e k E b

/-- `KernelSubst::expr_lbr_let(ty, val, body)`: `expr_lbr` of `Let(ty, val, body)` from its
components (the body under one more binder). -/
def expr_lbr_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body, args = [ty, val, body] → Good c calls → h' = h ∧
    ∀ d Γ k T V B, c.tmk d Γ k h T ty → c.tmk d Γ k h V val → c.tmk d Γ (k + 1) h B body →
      ∃ b : Nat, r = .field (b : F) ∧ b ≤ idxBound ∧ b ≤ k + d ∧
        LbrLe c h ty k T b ∧ LbrLe c h val k V b ∧ LbrLe c h body (k + 1) B (b + 1)

/-- `KernelSubst::lbr_max(a, b)`: the maximum of two counts below `2^32` (the comparison fails
otherwise). -/
def lbr_max : SpecFn := fun c args h r h' calls =>
  ∀ x y : F, args = [.field x, .field y] → Good c calls → h' = h ∧
    ZMod.val x < 4294967296 ∧ ZMod.val y < 4294967296 ∧
    r = .field (if ZMod.val x < ZMod.val y then y else x)

/-- `KernelSubst::lbr_dec(n)`: the predecessor, truncated at `0`. -/
def lbr_dec : SpecFn := fun c args h r h' calls =>
  ∀ x : F, args = [.field x] → Good c calls → h' = h ∧ r = .field ((ZMod.val x - 1 : Nat) : F)

/-- `KernelSubst::lbr_min(a, b)`: the minimum of two counts below `2^32`. -/
def lbr_min : SpecFn := fun c args h r h' calls =>
  ∀ x y : F, args = [.field x, .field y] → Good c calls → h' = h ∧
    ZMod.val x < 4294967296 ∧ ZMod.val y < 4294967296 ∧
    r = .field (if ZMod.val x < ZMod.val y then x else y)

/-! ## Occurrence tests -/

/-- `KernelSubst::has_bvar_in_range(e, lo, hi)`: answers `0` or `1`; **`0` claims that no index
in `[lo, hi)` occurs** (`Avoids`: neither a local one nor the opened variable a free one stands
for); `1` claims nothing. `expr_inst_many` lowers instead of substituting on `0`; the
declaration checks assert `0` of parameters that must not mention the first indices. -/
def has_bvar_in_range : SpecFn := fun c args h r h' calls =>
  ∀ e (lo hi : F), args = [e, .field lo, .field hi] → Good c calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k E, c.tmk d Γ k h E e → Avoids d k (ZMod.val lo) (ZMod.val hi) E)

/-- `KernelSubst::has_bvar_in_range_bvar(i, lo, hi)`: `0` claims `i ∉ [lo, hi)`. -/
def has_bvar_in_range_bvar : SpecFn := fun c args h r h' calls =>
  ∀ i lo hi : F, args = [.field i, .field lo, .field hi] → Good c calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ZMod.val i < ZMod.val lo ∨ ZMod.val hi ≤ ZMod.val i)

/-- `KernelSubst::has_bvar_in_range_binder(ty, body, lo, hi)`: `has_bvar_in_range` of a binder
node from its components (the body one binder deeper, at `[lo + 1, hi + 1)`). -/
def has_bvar_in_range_binder : SpecFn := fun c args h r h' calls =>
  ∀ ty body (lo hi : F), args = [ty, body, .field lo, .field hi] → Good c calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T B, c.tmk d Γ k h T ty → c.tmk d Γ (k + 1) h B body →
      Avoids d k (ZMod.val lo) (ZMod.val hi) T ∧
      Avoids d (k + 1) (ZMod.val lo + 1) (ZMod.val hi + 1) B)

/-- `KernelSubst::has_bvar_in_range_let(ty, val, body, lo, hi)`: from the let's components. -/
def has_bvar_in_range_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body (lo hi : F), args = [ty, val, body, .field lo, .field hi] → Good c calls →
    h' = h ∧ (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T V B, c.tmk d Γ k h T ty → c.tmk d Γ k h V val →
      c.tmk d Γ (k + 1) h B body →
      Avoids d k (ZMod.val lo) (ZMod.val hi) T ∧ Avoids d k (ZMod.val lo) (ZMod.val hi) V ∧
      Avoids d (k + 1) (ZMod.val lo + 1) (ZMod.val hi + 1) B)

/-- `KernelSubst::expr_has_bvar_at(e, depth)`: answers `0` or `1`; **`0` claims that the index
`depth` does not occur** (`Avoids` at `[depth, depth + 1)`). `expr_inst1` lowers instead of
substituting on `0`. -/
def expr_has_bvar_at : SpecFn := fun c args h r h' calls =>
  ∀ e (j : F), args = [e, .field j] → Good c calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k E, c.tmk d Γ k h E e → Avoids d k (ZMod.val j) (ZMod.val j + 1) E)

/-- `KernelSubst::expr_has_bvar_at_binder(ty, body, depth)`: from a binder's components. -/
def expr_has_bvar_at_binder : SpecFn := fun c args h r h' calls =>
  ∀ ty body (j : F), args = [ty, body, .field j] → Good c calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T B, c.tmk d Γ k h T ty → c.tmk d Γ (k + 1) h B body →
      Avoids d k (ZMod.val j) (ZMod.val j + 1) T ∧
      Avoids d (k + 1) (ZMod.val j + 1) (ZMod.val j + 2) B)

/-- `KernelSubst::expr_has_bvar_at_let(ty, val, body, depth)`: from a let's components. -/
def expr_has_bvar_at_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body (j : F), args = [ty, val, body, .field j] → Good c calls → h' = h ∧
    (r = .field 0 ∨ r = .field 1) ∧
    (r = .field 0 → ∀ d Γ k T V B, c.tmk d Γ k h T ty → c.tmk d Γ k h V val →
      c.tmk d Γ (k + 1) h B body →
      Avoids d k (ZMod.val j) (ZMod.val j + 1) T ∧ Avoids d k (ZMod.val j) (ZMod.val j + 1) V ∧
      Avoids d (k + 1) (ZMod.val j + 1) (ZMod.val j + 2) B)

/-! ## The smallest free index -/

/-- `KernelSubst::expr_glb(e, cutoff)`, read at local depth `cutoff`: **a lower bound `g` on the
free indices**, relative to the cutoff (`4294967295` if there is none): every opened variable of
the image is below `d - g`, so the innermost `g` opened variables do not occur (what
`k_infer_rebase` and `k_def_eq_rebase` lower by). `g < 2^32`. Allocates nothing. -/
def expr_glb : SpecFn := fun c args h r h' calls =>
  ∀ e (cut : F), args = [e, .field cut] → Good c calls → h' = h ∧
    ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ E, c.tmk d Γ (ZMod.val cut) h E e → E.fvarRange ≤ d - g

/-- `KernelSubst::expr_glb_walk(e, cutoff)`: as `expr_glb`, without the early exit. -/
def expr_glb_walk : SpecFn := fun c args h r h' calls =>
  ∀ e (cut : F), args = [e, .field cut] → Good c calls → h' = h ∧
    ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ E, c.tmk d Γ (ZMod.val cut) h E e → E.fvarRange ≤ d - g

/-- `KernelSubst::expr_glb_binder(ty, body, cutoff)`: from a binder's components (the body at
`cutoff + 1`). -/
def expr_glb_binder : SpecFn := fun c args h r h' calls =>
  ∀ ty body (cut : F), args = [ty, body, .field cut] → Good c calls → h' = h ∧
    ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ T B, c.tmk d Γ (ZMod.val cut) h T ty → c.tmk d Γ (ZMod.val cut + 1) h B body →
        T.fvarRange ≤ d - g ∧ B.fvarRange ≤ d - g

/-- `KernelSubst::expr_glb_let(ty, val, body, cutoff)`: from a let's components. -/
def expr_glb_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body (cut : F), args = [ty, val, body, .field cut] → Good c calls → h' = h ∧
    ∃ g : Nat, r = .field (g : F) ∧ g < 4294967296 ∧
      ∀ d Γ T V B, c.tmk d Γ (ZMod.val cut) h T ty → c.tmk d Γ (ZMod.val cut) h V val →
        c.tmk d Γ (ZMod.val cut + 1) h B body →
        T.fvarRange ≤ d - g ∧ V.fvarRange ≤ d - g ∧ B.fvarRange ≤ d - g

/-! ## Lifting and lowering -/

/-- `KernelSubst::expr_lift(e, shift, cutoff)`, read at local depth `cutoff`: **the same image
under `s` more binders**, split as `s₁` local and `s₂` opened ones (module docstring). Hypothesis:
`s < 2^62`, so the lifted indices (below `2^32` before: `expr_lift_bvar` compares them) stay
below the seam's bound; the callers lift by a context index plus one, a depth below `2^32`, or
`1`. -/
def expr_lift : SpecFn := fun c args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Good c calls →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E, c.tmk d Γ (ZMod.val cut) h E e →
      c.tmk (d + s₂) Γ (ZMod.val cut + s₁) h' E r

/-- `KernelSubst::expr_lift_walk(e, shift, cutoff)`: as `expr_lift`, without the early exits. -/
def expr_lift_walk : SpecFn := fun c args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Good c calls →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E, c.tmk d Γ (ZMod.val cut) h E e →
      c.tmk (d + s₂) Γ (ZMod.val cut + s₁) h' E r

/-- `KernelSubst::expr_lift_bvar(i, shift, cutoff)`: the index `i`, lifted. -/
def expr_lift_bvar : SpecFn := fun c args _ r h' calls =>
  ∀ i s cut : F, args = [.field i, .field s, .field cut] → Good c calls →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ E, BVarIm d Γ (ZMod.val cut) (ZMod.val i) E →
      c.tmk (d + s₂) Γ (ZMod.val cut + s₁) h' E r

/-- `KernelSubst::expr_lift_let(ty, val, body, shift, cutoff)`: the lifted let, whose image is
the ζ-reduct of its components' (`instShift`). -/
def expr_lift_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body (s cut : F), args = [ty, val, body, .field s, .field cut] → Good c calls →
    ZMod.val s < 4611686018427387904 →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → ∀ d Γ T V B, c.tmk d Γ (ZMod.val cut) h T ty →
      c.tmk d Γ (ZMod.val cut) h V val → c.tmk d Γ (ZMod.val cut + 1) h B body →
      c.tmk (d + s₂) Γ (ZMod.val cut + s₁) h' (instShift V 0 B) r

/-- `KernelSubst::expr_lower(e, shift, cutoff)`, read at local depth `cutoff`: **the same image
with `s` fewer binders**, split as `s₁` local and `s₂` opened ones, given that the removed
indices do not occur: the image's loose `bvar`s are below `cutoff - s₁` and its opened variables
below `d - s₂` (`expr_inst1`/`expr_inst_many` remove local binders, after `expr_has_bvar_at` /
`has_bvar_in_range` answered `0`; the rebases remove opened variables, after `expr_glb`). -/
def expr_lower : SpecFn := fun c args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Good c calls →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val cut → ∀ d Γ E, s₂ ≤ d →
      c.tmk d Γ (ZMod.val cut) h E e → E.looseBVarsBounded (ZMod.val cut - s₁) = true →
      E.fvarRange ≤ d - s₂ → c.tmk (d - s₂) Γ (ZMod.val cut - s₁) h' E r

/-- `KernelSubst::expr_lower_walk(e, shift, cutoff)`: as `expr_lower`, without the early
exits. -/
def expr_lower_walk : SpecFn := fun c args h r h' calls =>
  ∀ e (s cut : F), args = [e, .field s, .field cut] → Good c calls →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val cut → ∀ d Γ E, s₂ ≤ d →
      c.tmk d Γ (ZMod.val cut) h E e → E.looseBVarsBounded (ZMod.val cut - s₁) = true →
      E.fvarRange ≤ d - s₂ → c.tmk (d - s₂) Γ (ZMod.val cut - s₁) h' E r

/-- `KernelSubst::expr_lower_let(ty, val, body, shift, cutoff)`: the lowered let, from its
components, under the same hypotheses on each (the body one binder deeper). -/
def expr_lower_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body (s cut : F), args = [ty, val, body, .field s, .field cut] → Good c calls →
    ∀ s₁ s₂, ZMod.val s = s₁ + s₂ → s₁ ≤ ZMod.val cut → ∀ d Γ T V B, s₂ ≤ d →
      c.tmk d Γ (ZMod.val cut) h T ty → c.tmk d Γ (ZMod.val cut) h V val →
      c.tmk d Γ (ZMod.val cut + 1) h B body →
      T.looseBVarsBounded (ZMod.val cut - s₁) = true →
      V.looseBVarsBounded (ZMod.val cut - s₁) = true →
      B.looseBVarsBounded (ZMod.val cut + 1 - s₁) = true →
      T.fvarRange ≤ d - s₂ → V.fvarRange ≤ d - s₂ → B.fvarRange ≤ d - s₂ →
      c.tmk (d - s₂) Γ (ZMod.val cut - s₁) h' (instShift V 0 B) r

/-! ## Instantiation -/

/-- `KernelSubst::expr_inst1(e, arg, depth)`: **the kernel's `instantiate1` at index `depth`**:
`e` read at local depth `depth + 1`, the top-level `arg`, the result at local depth `depth`
(L3's `Terms` is the case `depth = 0`). No hypothesis on indices: the argument is lifted by
`depth`, which the function's comparisons bound by `2^32`. -/
def expr_inst1 : SpecFn := fun c args h r h' calls =>
  ∀ e arg (j : F), args = [e, arg, .field j] → Good c calls →
    ∀ d Γ B A, c.tmk d Γ (ZMod.val j + 1) h B e → c.tm d Γ h A arg →
      c.tmk d Γ (ZMod.val j) h' (B.instantiate1 A (ZMod.val j)) r

/-- `KernelSubst::expr_inst1_walk(e, arg, depth)`: as `expr_inst1`, without the early exits. -/
def expr_inst1_walk : SpecFn := fun c args h r h' calls =>
  ∀ e arg (j : F), args = [e, arg, .field j] → Good c calls →
    ∀ d Γ B A, c.tmk d Γ (ZMod.val j + 1) h B e → c.tm d Γ h A arg →
      c.tmk d Γ (ZMod.val j) h' (B.instantiate1 A (ZMod.val j)) r

/-- `KernelSubst::expr_inst1_bvar(i, arg, depth)`: the index `i`, instantiated. -/
def expr_inst1_bvar : SpecFn := fun c args h r h' calls =>
  ∀ (i : F) arg (j : F), args = [.field i, arg, .field j] → Good c calls →
    ∀ d Γ B A, BVarIm d Γ (ZMod.val j + 1) (ZMod.val i) B → c.tm d Γ h A arg →
      c.tmk d Γ (ZMod.val j) h' (B.instantiate1 A (ZMod.val j)) r

/-- `KernelSubst::expr_inst1_let(ty, val, body, arg, depth)`: the instantiated let, whose image
is the ζ-reduct of its components' (`instShift`), instantiated. -/
def expr_inst1_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body arg (j : F), args = [ty, val, body, arg, .field j] → Good c calls →
    ∀ d Γ T V B A, c.tmk d Γ (ZMod.val j + 1) h T ty → c.tmk d Γ (ZMod.val j + 1) h V val →
      c.tmk d Γ (ZMod.val j + 2) h B body → c.tm d Γ h A arg →
      c.tmk d Γ (ZMod.val j) h' ((instShift V 0 B).instantiate1 A (ZMod.val j)) r

/-- `KernelSubst::expr_inst_many(e, substs, depth)`: **the kernel's `instantiateList` at index
`depth`** (`substs[0]` replaces the innermost index `depth`): `e` read at local depth
`depth + |substs|`, the top-level arguments, the result at local depth `depth`. -/
def expr_inst_many : SpecFn := fun c args h r h' calls =>
  ∀ e substs (j : F), args = [e, substs, .field j] → Good c calls →
    ∀ d Γ B As, c.tmk d Γ (ZMod.val j + As.length) h B e → c.tml d Γ h As substs →
      c.tmk d Γ (ZMod.val j) h' (B.instantiateList As (ZMod.val j)) r

/-- `KernelSubst::expr_inst_many_bvar(i, substs, depth)`: the index `i`, instantiated. -/
def expr_inst_many_bvar : SpecFn := fun c args h r h' calls =>
  ∀ (i : F) substs (j : F), args = [.field i, substs, .field j] → Good c calls →
    ∀ d Γ B As, BVarIm d Γ (ZMod.val j + As.length) (ZMod.val i) B → c.tml d Γ h As substs →
      c.tmk d Γ (ZMod.val j) h' (B.instantiateList As (ZMod.val j)) r

/-- `KernelSubst::expr_inst_many_walk(e, substs, depth)`: as `expr_inst_many`, without the early
exits. -/
def expr_inst_many_walk : SpecFn := fun c args h r h' calls =>
  ∀ e substs (j : F), args = [e, substs, .field j] → Good c calls →
    ∀ d Γ B As, c.tmk d Γ (ZMod.val j + As.length) h B e → c.tml d Γ h As substs →
      c.tmk d Γ (ZMod.val j) h' (B.instantiateList As (ZMod.val j)) r

/-- `KernelSubst::expr_inst_many_let(ty, val, body, substs, depth)`: the instantiated let. -/
def expr_inst_many_let : SpecFn := fun c args h r h' calls =>
  ∀ ty val body substs (j : F), args = [ty, val, body, substs, .field j] → Good c calls →
    ∀ d Γ T V B As, c.tmk d Γ (ZMod.val j + As.length) h T ty →
      c.tmk d Γ (ZMod.val j + As.length) h V val →
      c.tmk d Γ (ZMod.val j + As.length + 1) h B body → c.tml d Γ h As substs →
      c.tmk d Γ (ZMod.val j) h' ((instShift V 0 B).instantiateList As (ZMod.val j)) r

/-! ## Context cuts -/

/-- `KernelSubst::ctx_trim(types, base)`: **a segment of the same ghost context ending at the
same depth** (the innermost entries of `types`, or none). What it keeps is chosen for the
inference to succeed; nothing else is claimed. -/
def ctx_trim : SpecFn := fun c args h r h' calls =>
  ∀ types base, args = [types, base] → Good c calls →
    ∀ Γ d, c.types Γ h d types → c.types Γ h' d r

/-- `KernelSubst::ctx_reachable(types, base)`: a count. Allocates nothing. -/
def ctx_reachable : SpecFn := fun c args h r h' calls =>
  ∀ types base, args = [types, base] → Good c calls → h' = h ∧ ∃ x : F, r = .field x

/-- `KernelSubst::ctx_seek_cut(types, need)`: a count. Allocates nothing. -/
def ctx_seek_cut : SpecFn := fun c args h r h' calls =>
  ∀ types need, args = [types, need] → Good c calls → h' = h ∧ ∃ x : F, r = .field x

/-- `KernelSubst::ctx_next_cut(types)`: a count. Allocates nothing. -/
def ctx_next_cut : SpecFn := fun c args h r h' calls =>
  ∀ types, args = [types] → Good c calls → h' = h ∧ ∃ x : F, r = .field x

/-- `KernelSubst::ctx_close_cut(rest, l)`: a count. Allocates nothing. -/
def ctx_close_cut : SpecFn := fun c args h r h' calls =>
  ∀ rest l, args = [rest, l] → Good c calls → h' = h ∧ ∃ x : F, r = .field x

/-! ## Spines and level instantiation -/

/-- `KernelTypes::collect_spine(e)`: **the head and the spine** of a term under any number `k`
of local binders, `E = mkAppN H As` (its callers include walks under binders:
`KernelCheck::rec_to_parent_addr`, `KernelModeled::rec_major_pins`). -/
def collect_spine : SpecFn := fun c args h r h' calls =>
  ∀ e, args = [e] → Good c calls → ∀ d Γ k E, c.tmk d Γ k h E e →
    ∃ hd sp H As, r = .tuple [hd, sp] ∧ c.tmk d Γ k h' H hd ∧ c.tmlk d Γ k h' As sp ∧
      E = Ix.Kernel.Expr.mkAppN H As

/-- `KernelLevels::expr_inst_levels(e, params)`: **the kernel's level instantiation at the
positional parameters**, `instantiateLevelParams (List.range n) us` with `us` the levels the
list holds (`n = |us|`). The term is read at opening depth `0` (no opened variable: the kernel's
instantiation would also rewrite an opened variable's type, IxVM's does not; every caller
instantiates a stored constant's closed type, value or rule). The levels of the result are
related up to semantic equality, as the term seam relates every level; the binder data are
exactly the kernel's (zero-ness commutes with substitution). -/
def expr_inst_levels : SpecFn := fun c args h r h' calls =>
  ∀ e params, args = [e, params] → Good c calls →
    ∀ Γ k E us, c.tmk 0 Γ k h E e → LvListRep h us params →
      c.tmk 0 Γ k h' (E.instantiateLevelParams (List.range us.length) us) r

/-- `KernelLevels::expr_inst_levels_walk(e, params)`: as `expr_inst_levels`, at a nonempty
list. -/
def expr_inst_levels_walk : SpecFn := fun c args h r h' calls =>
  ∀ e params, args = [e, params] → Good c calls →
    ∀ Γ k E us, c.tmk 0 Γ k h E e → LvListRep h us params →
      c.tmk 0 Γ k h' (E.instantiateLevelParams (List.range us.length) us) r

/-! ## The family -/

/-- The functions of the family. -/
inductive Fn where
  | expr_lbr | expr_lbr_let | lbr_max | lbr_dec | lbr_min
  | has_bvar_in_range | has_bvar_in_range_bvar | has_bvar_in_range_binder | has_bvar_in_range_let
  | expr_has_bvar_at | expr_has_bvar_at_binder | expr_has_bvar_at_let
  | expr_glb | expr_glb_walk | expr_glb_binder | expr_glb_let
  | expr_lift | expr_lift_walk | expr_lift_bvar | expr_lift_let
  | expr_lower | expr_lower_walk | expr_lower_let
  | expr_inst1 | expr_inst1_walk | expr_inst1_bvar | expr_inst1_let
  | expr_inst_many | expr_inst_many_bvar | expr_inst_many_walk | expr_inst_many_let
  | ctx_trim | ctx_reachable | ctx_seek_cut | ctx_next_cut | ctx_close_cut
  | collect_spine | expr_inst_levels | expr_inst_levels_walk
  deriving DecidableEq, Repr

/-- The symbol `ObsFn` names each function by. -/
def Fn.name : Fn → String
  | .expr_lbr => "KernelSubst::expr_lbr"
  | .expr_lbr_let => "KernelSubst::expr_lbr_let"
  | .lbr_max => "KernelSubst::lbr_max"
  | .lbr_dec => "KernelSubst::lbr_dec"
  | .lbr_min => "KernelSubst::lbr_min"
  | .has_bvar_in_range => "KernelSubst::has_bvar_in_range"
  | .has_bvar_in_range_bvar => "KernelSubst::has_bvar_in_range_bvar"
  | .has_bvar_in_range_binder => "KernelSubst::has_bvar_in_range_binder"
  | .has_bvar_in_range_let => "KernelSubst::has_bvar_in_range_let"
  | .expr_has_bvar_at => "KernelSubst::expr_has_bvar_at"
  | .expr_has_bvar_at_binder => "KernelSubst::expr_has_bvar_at_binder"
  | .expr_has_bvar_at_let => "KernelSubst::expr_has_bvar_at_let"
  | .expr_glb => "KernelSubst::expr_glb"
  | .expr_glb_walk => "KernelSubst::expr_glb_walk"
  | .expr_glb_binder => "KernelSubst::expr_glb_binder"
  | .expr_glb_let => "KernelSubst::expr_glb_let"
  | .expr_lift => "KernelSubst::expr_lift"
  | .expr_lift_walk => "KernelSubst::expr_lift_walk"
  | .expr_lift_bvar => "KernelSubst::expr_lift_bvar"
  | .expr_lift_let => "KernelSubst::expr_lift_let"
  | .expr_lower => "KernelSubst::expr_lower"
  | .expr_lower_walk => "KernelSubst::expr_lower_walk"
  | .expr_lower_let => "KernelSubst::expr_lower_let"
  | .expr_inst1 => "KernelSubst::expr_inst1"
  | .expr_inst1_walk => "KernelSubst::expr_inst1_walk"
  | .expr_inst1_bvar => "KernelSubst::expr_inst1_bvar"
  | .expr_inst1_let => "KernelSubst::expr_inst1_let"
  | .expr_inst_many => "KernelSubst::expr_inst_many"
  | .expr_inst_many_bvar => "KernelSubst::expr_inst_many_bvar"
  | .expr_inst_many_walk => "KernelSubst::expr_inst_many_walk"
  | .expr_inst_many_let => "KernelSubst::expr_inst_many_let"
  | .ctx_trim => "KernelSubst::ctx_trim"
  | .ctx_reachable => "KernelSubst::ctx_reachable"
  | .ctx_seek_cut => "KernelSubst::ctx_seek_cut"
  | .ctx_next_cut => "KernelSubst::ctx_next_cut"
  | .ctx_close_cut => "KernelSubst::ctx_close_cut"
  | .collect_spine => "KernelTypes::collect_spine"
  | .expr_inst_levels => "KernelLevels::expr_inst_levels"
  | .expr_inst_levels_walk => "KernelLevels::expr_inst_levels_walk"

/-- Each function's spec. -/
def Fn.spec : Fn → SpecFn
  | .expr_lbr => Specs.Subst.expr_lbr
  | .expr_lbr_let => Specs.Subst.expr_lbr_let
  | .lbr_max => Specs.Subst.lbr_max
  | .lbr_dec => Specs.Subst.lbr_dec
  | .lbr_min => Specs.Subst.lbr_min
  | .has_bvar_in_range => Specs.Subst.has_bvar_in_range
  | .has_bvar_in_range_bvar => Specs.Subst.has_bvar_in_range_bvar
  | .has_bvar_in_range_binder => Specs.Subst.has_bvar_in_range_binder
  | .has_bvar_in_range_let => Specs.Subst.has_bvar_in_range_let
  | .expr_has_bvar_at => Specs.Subst.expr_has_bvar_at
  | .expr_has_bvar_at_binder => Specs.Subst.expr_has_bvar_at_binder
  | .expr_has_bvar_at_let => Specs.Subst.expr_has_bvar_at_let
  | .expr_glb => Specs.Subst.expr_glb
  | .expr_glb_walk => Specs.Subst.expr_glb_walk
  | .expr_glb_binder => Specs.Subst.expr_glb_binder
  | .expr_glb_let => Specs.Subst.expr_glb_let
  | .expr_lift => Specs.Subst.expr_lift
  | .expr_lift_walk => Specs.Subst.expr_lift_walk
  | .expr_lift_bvar => Specs.Subst.expr_lift_bvar
  | .expr_lift_let => Specs.Subst.expr_lift_let
  | .expr_lower => Specs.Subst.expr_lower
  | .expr_lower_walk => Specs.Subst.expr_lower_walk
  | .expr_lower_let => Specs.Subst.expr_lower_let
  | .expr_inst1 => Specs.Subst.expr_inst1
  | .expr_inst1_walk => Specs.Subst.expr_inst1_walk
  | .expr_inst1_bvar => Specs.Subst.expr_inst1_bvar
  | .expr_inst1_let => Specs.Subst.expr_inst1_let
  | .expr_inst_many => Specs.Subst.expr_inst_many
  | .expr_inst_many_bvar => Specs.Subst.expr_inst_many_bvar
  | .expr_inst_many_walk => Specs.Subst.expr_inst_many_walk
  | .expr_inst_many_let => Specs.Subst.expr_inst_many_let
  | .ctx_trim => Specs.Subst.ctx_trim
  | .ctx_reachable => Specs.Subst.ctx_reachable
  | .ctx_seek_cut => Specs.Subst.ctx_seek_cut
  | .ctx_next_cut => Specs.Subst.ctx_next_cut
  | .ctx_close_cut => Specs.Subst.ctx_close_cut
  | .collect_spine => Specs.Subst.collect_spine
  | .expr_inst_levels => Specs.Subst.expr_inst_levels
  | .expr_inst_levels_walk => Specs.Subst.expr_inst_levels_walk

end IxVM.Refinement.Core.Specs.Subst
