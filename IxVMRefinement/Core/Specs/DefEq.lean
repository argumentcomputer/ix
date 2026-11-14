import IxVMRefinement.Core.Specs.Common

/-! # The registry's specs: `KernelDefEq`

One spec per in-scope function of `KernelDefEq` (55). The target is the rules tier's
definitional equality `Ix.Kernel.Rules.DefEq` (no transitivity): every tier's answer `1` lands in
a rule whose premises the circuit establishes, chaining "reduce, then continue" through `redL`
and its derived right-hand variants (`IxC/Kernel/Rules/Derived.lean`). Nothing is claimed for an
answer `0`.

**A yes is any answer other than `0`.** The circuit tests several of these answers against `0`
(`match f(…) { 0 => 0, _ => … }`: `de_args`, `compare_struct_fields`, `try_eta_struct`,
`try_proof_irrel`, the application case of `k_is_def_eq_struct_go`) and multiplies others
(`is_nat_zero`), so every claim below is stated for every answer other than `0` (`r ≠ .field 0`),
which is what "answer `1`" means in the docstrings; a claim at `1` alone could not be carried
through those tests. Every such answer is `0` or `1` in fact. A step lemma therefore needs the
same form (or the exact value) from each yes/no callee whose answer it returns, tests against `0`
or multiplies.

Shapes:

* **Comparisons** `f(rc, a, b, types) -> Field` (`DeClaim`): at every opening depth `d` and ghost
  context `Γ` at which the role context, the context list and both terms are represented, answer
  `1` is `DefEq c.env d A B`.
* **Comparisons continuing from reducts** `f(rc, orig_a, orig_b, a, b, types) -> Field`
  (`DeFromReductsClaim`): `a`, `b` represent reducts of the originals' images (a hypothesis), and
  answer `1` is `DefEq` of the originals.
* **Lazy-δ steps** `-> (tag, fa, fb)` (`LoopResult`): `fa`, `fb` represent reducts of the inputs'
  images whatever the tag (every path returns the inputs or reducts of them), and tag `1` is
  `DefEq` of the inputs.
* **Pairs** `(decided, answer)` (`try_def_eq_nat`, `de_rescue_tier`) and `(answer, credit)`
  (`k_is_def_eq_struct_bounded`, `k_is_def_eq_struct_spend`): a claim for the "decided and
  equal" combination only.

Binder congruence (`DefEq.lam`, `forallE`, `eta`) asks for equal input contracts; every binder
the term seam relates carries `bmeta`, the default contracts, so that premise holds by `rfl` on
images. IxVM opens both bodies under the **left** domain; `DefEq.symm` puts it on the right, as
the rule reads it. -/

namespace IxVM.Refinement.Core.Specs.DefEq

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel.Rules (Red DefEqList Infer Certs)

/-! ## Shared shapes -/

/-- **A yes/no comparison of two terms** (`f(rc, a, b, types) -> Field`): answer `1` is
`DefEq`, at every opening depth and ghost context at which its inputs are represented. -/
def DeClaim (c : Ctx) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
    (calls : List (Call F)) : Prop :=
  ∀ rc a b types, args = [rc, a, b, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      r ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A B

/-- **A comparison continuing from reducts** (`f(rc, orig_a, orig_b, a, b, types) -> Field`): for
`a`, `b` representing reducts of the originals' images, answer `1` is `DefEq` of the originals. -/
def DeFromReductsClaim (c : Ctx) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
    (calls : List (Call F)) : Prop :=
  ∀ rc oa ob a b types, args = [rc, oa, ob, a, b, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A0 B0 A B, c.tm d Γ h A0 oa → c.tm d Γ h B0 ob →
      c.tm d Γ h A a → c.tm d Γ h B b → Red c.env d A0 A → Red c.env d B0 B →
        r ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A0 B0

/-- **The result of a lazy-δ step** `(tag, fa, fb)` on terms whose images are `A`, `B`: `fa`, `fb`
represent reducts of `A`, `B` (for every tag), and a tag other than `0` is `DefEq A B`. -/
def LoopResult (c : Ctx) (d : Nat) (Γ : Nat → KExpr) (h' : Heap F) (r : SourceValue F)
    (A B : KExpr) : Prop :=
  ∀ tag fa fb, r = .tuple [tag, fa, fb] →
    ∃ FA FB, c.tm d Γ h' FA fa ∧ c.tm d Γ h' FB fb ∧ Red c.env d A FA ∧ Red c.env d B FB ∧
      (tag ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A B)

/-- **A `Nat` offset split as IxVM reads one** (`nat_offset_of`): `E` is `B` plus `k`, read
through a `Nat` literal (base the literal `0`), `Nat.succ x` at no levels (one step of `1`) and
`Nat.add x (lit m)` (one step of `m`), where the split may stop at any `Nat.succ`/`Nat.add`
layer: IxVM stops where its role lookup does not answer, as it does for a role not in force
during the validation of a group. Each `Nat.succ` step carries `ps` and each `Nat.add` step `pa`
(for `nat_offset_of`: the role is in force, `Ctx.inForce`, which the lookup that peeled the
layer establishes). The kernel's `natOffsetOf` is the split that stops only where no layer is
left, at any levels; where IxVM stops earlier, a proof reduces both sides to `Nat.succ` towers
(`Red.natLit`, `Red.natAddSucc`, `Red.natAddZero` under `Red.appArg`), whose heads are at no
levels. A `Nat.add` head's level list is not read (`natAddSucc` and `natAddZero` read none). -/
inductive OffsetSplit (ps pa : Prop) : KExpr → KExpr → Nat → Prop where
  | lit {n : Nat} : OffsetSplit ps pa (.lit (.natVal n)) (.lit (.natVal 0)) n
  | succStop {x : KExpr} (hs : ps) :
      OffsetSplit ps pa (.app (.const Ix.Kernel.natSuccName []) x) x 1
  | succ {x B : KExpr} {k : Nat} (hs : ps) :
      OffsetSplit ps pa x B k →
        OffsetSplit ps pa (.app (.const Ix.Kernel.natSuccName []) x) B (k + 1)
  | addStop {us : List KLevel} {x : KExpr} {m : Nat} (ha : pa) :
      OffsetSplit ps pa (.app (.app (.const Ix.Kernel.natAddName us) x) (.lit (.natVal m))) x m
  | add {us : List KLevel} {x B : KExpr} {m k : Nat} (ha : pa) :
      OffsetSplit ps pa x B k →
        OffsetSplit ps pa (.app (.app (.const Ix.Kernel.natAddName us) x) (.lit (.natVal m)))
          B (k + m)

/-- `n` leading `∀`s, syntactically. -/
def HasPis : Nat → KExpr → Prop
  | 0, _ => True
  | n + 1, .forallE _ b _ => HasPis n b
  | _ + 1, _ => False

/-! ## Entry, rebase, fast path -/

/-- `k_is_def_eq(rc, a, b, types)`: **answer `1` is `DefEq`** (`DeClaim`). The statement's `Core`
conjunct. Closed inputs (`expr_lbr = 0` on both sides) run `k_is_def_eq_core` under the empty
context list, a segment of every ghost context; the others run `k_def_eq_rebase`. -/
def k_is_def_eq : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_def_eq_rebase(rc, a, b, types, base)`: **answer `1` is `DefEq` at the caller's depth.**
The inner run compares the inputs lowered past their unused innermost `g` opened variables, at
depth `d - g` under the trimmed context; its `DefEq` is moved back to depth `d` by
`DefEq.lift` (`IxC/Kernel/Rules/Transport.lean`), which reads that the stored terms are closed
(`EnvFacts.storeClosed`) and fixes the images because the ghost context is scoped
(`GhostScoped`, in `c.types`). `base` is unconstrained (`ctx_trim` keeps a segment with the same
top end whatever it is). -/
def k_def_eq_rebase : SpecFn := fun c args h r _ calls =>
  ∀ rc a b types base, args = [rc, a, b, types, base] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      r ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A B

/-- `k_is_def_eq_core(rc, a, b, types)`: answer `1` is `DefEq` (`DeClaim`). -/
def k_is_def_eq_core : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_is_def_eq_ordered(rc, a, b, types)`: the same-head spine fast path, then the slow tiers;
answer `1` is `DefEq` (`DeClaim`). -/
def k_is_def_eq_ordered : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `try_def_eq_app(rc, a, b, types)`: **same-head spine congruence**; answer `1` is `DefEq`
(`DeClaim`). Heads: two variables of one index (equal images), or one constant address at
levels `level_list_eq` accepts (`DefEq.const`), then the arguments pairwise (`de_args`, whose
answer `1` also fixes the lengths), by `DefEq.app` along the spine. -/
def try_def_eq_app : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `de_args(rc, aa, bb, types)`: **answer `1` is `DefEqList`** of the two argument lists (equal
lengths, pairwise `DefEq`). -/
def de_args : SpecFn := fun c args h r _ calls =>
  ∀ rc aa bb types, args = [rc, aa, bb, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ As Bs, c.tml d Γ h As aa → c.tml d Γ h Bs bb →
      r ≠ .field 0 → DefEqList c.env d As Bs

/-- `level_list_eq(a, b)`: **answer `1` is pointwise semantic equality** (`LvEqList`) of the two
level lists, the premise of `DefEq.const` (the lengths agree). -/
def level_list_eq : SpecFn := fun c args h r _ calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ us vs, LvListRep h us a → LvListRep h vs b → r ≠ .field 0 → LvEqList us vs

/-! ## `Nat` literals and offsets -/

/-- `is_nat_zero(rc, e)`: **answer `1` means the image is the literal `0` or `Nat.zero`** (a
literal whose limbs are zero, or a level-free constant at an address the table binds to
`Nat.zero`). -/
def is_nat_zero : SpecFn := fun c args h r _ calls =>
  ∀ rc e, args = [rc, e] → Good c calls → c.rc h rc → r ≠ .field 0 →
    ∀ d Γ E, c.tm d Γ h E e → E = .lit (.natVal 0) ∨ E = .const Ix.Kernel.natZeroName []

/-- `nat_offset_of(rc, e) -> (tag, base, limbs)`: **a tag other than `0` is an offset split**
(`OffsetSplit` at the roles in force: every `Nat.succ` step's role `Nat.succ` and every `Nat.add`
step's role `Nat.add` is in force, which `role_is` gives where it peels the layer): the image is
the base's image plus the limbs' value. A `Nat.succ` head is peeled only at no levels
(`KernelNatPrim::lvls_empty`). Tag `0` returns the input and the empty limbs (decided by the code;
IxVM's own recursion reads the base of a tag-`0` result). The split is IxVM's: it stops at a head
its role lookup does not answer, where the kernel's `natOffsetOf` (the reading
`DefEq.natOffset` asks for) may go on. -/
def nat_offset_of : SpecFn := fun c args h r h' calls =>
  ∀ rc e, args = [rc, e] → Good c calls → c.rc h rc →
    (∀ x y, r = .tuple [.field 0, x, y] → x = e ∧ RepLimbs h' 0 y) ∧
    (∀ tag x y, r = .tuple [tag, x, y] → tag ≠ .field 0 → ∀ d Γ E, c.tm d Γ h E e →
      ∃ B k, OffsetSplit (c.inForce .natSucc) (c.inForce .natAdd) E B k ∧
        c.tm d Γ h' B x ∧ RepLimbs h' k y)

/-- `try_def_eq_nat(rc, a, b, types) -> (decided, answer)`: **`(1, x)` with `x` other than `0`
is `DefEq`**: both images are zero readings (`DefEq.refl`, `DefEq.natZero`, `DefEq.symm`), or
both split at the same offset (`nat_offset_of`, `klimbs_eq`) with definitionally equal bases.
Where both splits are the kernel's `natOffsetOf`, that is `DefEq.natOffset`; where IxVM stopped
earlier, both sides reduce to `Nat.succ` towers over their bases (`Red.natLit`,
`Red.natAddSucc`, `Red.natAddZero`, under `Red.appArg`; the towers' heads are at no levels, as
the split's `Nat.succ` steps are), which compare by congruence, and `DefEq.redBoth` carries the
comparison back. The rules' guards come from `EnvFacts` at the roles in force: `natAddTyOk` from
`natAdd` where a split has a `Nat.add` step, `natLitSupported` from `natLit` where a split has
any step (`Nat`, `Nat.zero` and `Nat.succ` are one block, the first group, and `Nat.add`
depends on `Nat`, so they are in force whenever `Nat.succ` or `Nat.add` is). Two literals at
one offset are one term (`DefEq.refl`). `(1, 0)` and `(0, _)` claim nothing. -/
def try_def_eq_nat : SpecFn := fun c args h r _ calls =>
  ∀ rc a b types, args = [rc, a, b, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      ∀ x, r = .tuple [.field 1, x] → x ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A B

/-! ## `String` literals -/

/-- `try_string_lit_one(rc, t, s, types)`: at a string literal `t`, its constructor form, one δ
step on (`str_lit_delta_step`), compared with `s`: **answer `1` is `DefEq T S`** (`Red.strLit`
and the δ step, then `redL`). -/
def try_string_lit_one : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `try_string_lit_pair(rc, a, b, types)`: `try_string_lit_one` both ways; answer `1` is
`DefEq` (the second way by `DefEq.symm`). -/
def try_string_lit_pair : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-! ## The slow tiers -/

/-- `k_is_def_eq_slow(rc, a, b, types)`: string literals, then `k_is_def_eq_slow_nd`; answer `1`
is `DefEq` (`DeClaim`). -/
def k_is_def_eq_slow : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_is_def_eq_slow_nd(rc, a, b, types)`: both sides head-normalized by `whnf_struct_core`
(`Red`), compared structurally and by spines, then `k_is_def_eq_slow_nd_after_core`; answer `1`
is `DefEq` (reduct comparisons carried back by `redL` and its right-hand variant). -/
def k_is_def_eq_slow_nd : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_is_def_eq_slow_nd_after_core(rc, orig_a, orig_b, a, b, types)`: `a`, `b` are the
`whnf_struct_core` reducts; both are head-normalized further (`whnf_nd`), compared, then
`k_is_def_eq_slow2`. **Answer `1` is `DefEq` of the originals** (`DeFromReductsClaim`). -/
def k_is_def_eq_slow_nd_after_core : SpecFn := fun c args h r _ calls =>
  DeFromReductsClaim c args h r calls

/-- `k_is_def_eq_struct_safe(rc, a, b, types)`: equal variables (equal images), sorts at levels
`level_equal` accepts (`DefEq.sort`), binders (`de_binder`); answer `1` is `DefEq`
(`DeClaim`). -/
def k_is_def_eq_struct_safe : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_is_def_eq_slow2(rc, orig_a, orig_b, aw, bw, types)`: the rescue tier, the lazy-δ loop,
then `slow2_after_delta` on the loop's reducts. **Answer `1` is `DefEq` of the originals**
(`DeFromReductsClaim`; `aw`, `bw` represent reducts of the originals). -/
def k_is_def_eq_slow2 : SpecFn := fun c args h r _ calls => DeFromReductsClaim c args h r calls

/-- `de_rescue_tier(rc, aw, bw, types) -> (decided, answer)`: proof irrelevance, unit-like types,
structure η both ways, `Nat` offsets. **`(1, x)` with `x` other than `0` is `DefEq`**; nothing
else is claimed. -/
def de_rescue_tier : SpecFn := fun c args h r _ calls =>
  ∀ rc a b types, args = [rc, a, b, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      ∀ x, r = .tuple [.field 1, x] → x ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A B

/-- `slow2_after_delta(rc, orig_a, orig_b, fa, fb, types)`: the bounded structural tier and the
structure tree on the lazy-δ reducts `fa`, `fb`, then the eager fallback on the originals.
**Answer `1` is `DefEq` of the originals** (`DeFromReductsClaim`). -/
def slow2_after_delta : SpecFn := fun c args h r _ calls => DeFromReductsClaim c args h r calls

/-- `try_same_proj_head_app(rc, a, b, types)`: two applications of projections, with at least
one argument and as many on both sides, at the same structure and field (`de_proj`), then the
arguments pairwise: answer `1` is `DefEq` (`DefEq.proj`, then `DefEq.app` along the spine). -/
def try_same_proj_head_app : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_is_def_eq_structure_tree(rc, a, b, types)`: the bounded structural tier, projection-headed
spines, then application nodes component-wise; answer `1` is `DefEq` (`DeClaim`). -/
def k_is_def_eq_structure_tree : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_is_def_eq_structure_tree_app(rc, a, b, types)`: two applications whose functions and
arguments compare by the structure tree: answer `1` is `DefEq` (`DefEq.app`). -/
def k_is_def_eq_structure_tree_app : SpecFn := fun c args h r _ calls =>
  DeClaim c args h r calls

/-- `k_is_def_eq_struct_bounded(rc, a, b, credit, types) -> (answer, credit')`: the structural
comparison with a credit of head normalizations (`k_is_def_eq_struct_spend`). **An answer other
than `0` is `DefEq`**; nothing is claimed for `0`, so the credit is harmless. Binder bodies are
compared under the left domain (`DefEq.lam`/`forallE` by symmetry). -/
def k_is_def_eq_struct_bounded : SpecFn := fun c args h r _ calls =>
  ∀ rc a b credit types, args = [rc, a, b, credit, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      ∀ ans rest, r = .tuple [ans, rest] → ans ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A B

/-- `k_is_def_eq_struct_spend(rc, a, b, credit, types) -> (answer, credit')`: one credit spent on
head-normalizing both sides (`whnf_nd`), then `Nat` offsets, the lazy-δ loop, or the bounded
structural comparison of the loop's reducts. **An answer other than `0` is `DefEq`**. -/
def k_is_def_eq_struct_spend : SpecFn := fun c args h r _ calls =>
  ∀ rc a b credit types, args = [rc, a, b, credit, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      ∀ ans rest, r = .tuple [ans, rest] → ans ≠ .field 0 → Ix.Kernel.Rules.DefEq c.env d A B

/-- `slow2_eager_fallback(rc, a, b, types)`: both sides head-normalized (`whnf`), the rescue
tier, η both ways, then the structural comparison; answer `1` is `DefEq` (`DeClaim`). -/
def slow2_eager_fallback : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-! ## The rescue tier -/

/-- `try_proof_irrel(rc, a, b, types)`: `a`'s io-inferred type is a proposition (`is_prop_type`)
and `b`'s io-inferred type is definitionally equal to it: **answer `1` is `DefEq`** by
`DefEq.proofIrrelTy`. -/
def try_proof_irrel : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `is_prop_type(rc, ty, types)`: **answer `1` means `ty`'s image has an io-inferred type that
reduces to a sort at a level zero at every assignment** (the middle premises of
`DefEq.proofIrrelTy`). -/
def is_prop_type : SpecFn := fun c args h r _ calls =>
  ∀ rc ty types, args = [rc, ty, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ T, c.tm d Γ h T ty → r ≠ .field 0 →
      ∃ S u, Infer c.env .io d T S ∧ Red c.env d S (.sort u) ∧
        ∀ φ, Ix.Kernel.Level.eval φ u = 0

/-- `try_unit_like(rc, a, b, types)`: `a`'s io-inferred type head-normalizes to a unit-like
family applied to its parameters (`is_unit_like_type`), and `b`'s io-inferred type is
definitionally equal to `a`'s: **answer `1` is `DefEq`** by `DefEq.unitLikeTy`. -/
def try_unit_like : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `is_unit_like_type(rc, ty, types)`: **answer `1` gives `DefEq.unitLikeTy`'s premises on
`ty`'s image**: its head is a stored inductive whose capabilities say unit-like, applied to
exactly its unit-like parameter count, with the family's telescope certified against the
arguments (licensed), and, at a reserved basis name, the basis unit (`isUnitLikeTy`). IxVM reads
the shape off the loaded records (no indices, one block member, one constructor without fields,
not recursive) and certifies the parameters (`family_params`). The capability record is the
kernel's install computation, so a proof needs an environment fact: a stored inductive whose
loaded record has no index and one constructor without fields has `caps.unitlike = true` and
`caps.unitParams` its parameter count (the native install's `nativeCapsAt`; the pinned `PUnit`,
whose key is reserved, with `isUnitLikeTy`). -/
def is_unit_like_type : SpecFn := fun c args h r _ calls =>
  ∀ rc ty types, args = [rc, ty, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ T, c.tm d Γ h T ty → r ≠ .field 0 →
      ∃ (K : KKey) (us : List KLevel) (cvT : Ix.Kernel.ConstantVal .anon)
        (caps : Ix.Kernel.IndCaps .anon),
        T.getAppFn = .const K us ∧ c.env.find? K = some (.indInfo cvT caps) ∧
        caps.unitlike = true ∧ T.getAppArgs.length = caps.unitParams ∧
        Certs c.env d true (cvT.type.instantiateLevelParams cvT.levelParams us) T.getAppArgs ∧
        (Ix.Kernel.reservedBasisNames.contains K = false ∨ Ix.Kernel.isUnitLikeTy c.env T = true)

/-- `family_params(rc, ind_nl, ind_ty, ind_np, lvls, args, types)`: **answer `1` means `args`
are exactly `ind_np` parameters at `ind_nl` levels, certified against the family's telescope**
(`Certs`, licensed: a slot whose datum is never zero skips; `slots_never`, or `leading_foralls`
and `certs_all`). `ind_ty` is the family's closed type, whose level parameters are positional
(`ValRep`). -/
def family_params : SpecFn := fun c args h r _ calls =>
  ∀ rc nl ty np lvls xs types, args = [rc, nl, ty, np, lvls, xs, types] → Good c calls →
    c.rc h rc → ∀ (n p : F), nl = .field n → np = .field p →
    ∀ d Γ, c.types Γ h d types → ∀ T us As, c.tmc h T ty → LvListRep h us lvls →
      c.tml d Γ h As xs → r ≠ .field 0 →
        As.length = ZMod.val p ∧ us.length = ZMod.val n ∧
        Certs c.env d true (T.instantiateLevelParams (List.range us.length) us) As

/-- `leading_foralls(t, n)`: **answer `1` means `t`'s image begins with `n` syntactic `∀`s**
(at any local depth). -/
def leading_foralls : SpecFn := fun c args h r _ calls =>
  ∀ t (n : F), args = [t, .field n] → Good c calls → r ≠ .field 0 →
    ∀ d Γ k T, c.tmk d Γ k h T t → HasPis (ZMod.val n) T

/-- `try_eta_struct(rc, t, s, types)`: `s` is a fully applied constructor of a non-recursive,
index-free, single-constructor structure with at least one field, of a native block (whose
fields read as projections), whose sort is never zero; its parameters are certified
(`family_params`); the io-inferred types of `t` and `s` are definitionally equal; and each
projection of `t` is definitionally equal to the corresponding field of `s`
(`compare_struct_fields`). **Answer `1` is `DefEq T S`** by `DefEq.structEtaTy` (its `b` is `t`,
its `a` is `s`). A proof needs environment facts for the premises IxVM does not compute: for a
stored inductive whose loaded record has no index, one constructor, a sort never zero and no
recursive field, in a native block, `caps.eta = true`, `caps.etaCtor` the key of its constructor
record and `towerSlotsAll` at the constructor's field count (the native install's
`nativeCapsAt` and projection tables); and the stored constructor's type is a telescope of its
parameters and fields ending in the structure at the constructor's level parameters applied to
the parameters, which gives `Red ta (mkAppN (.const T us) (a.getAppArgs.take cnP))` for the
io-inferred type of the constructor application. -/
def try_eta_struct : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `compare_struct_fields(rc, struct_addr, nparams, nfields, t, s_args, i, types)`: **answer `1`
means, for every field `j` from `i` below `nfields`, the projection `.proj S j t` is
definitionally equal to the argument of `s_args` at `nparams + j`** (`S` the key of
`struct_addr`), as `DefEq.structEtaTy`'s last premise reads them. The start `i` is at most
`nfields` (the caller starts at `0`). -/
def compare_struct_fields : SpecFn := fun c args h r _ calls =>
  ∀ rc sp np nf t sargs ip types, args = [rc, sp, np, nf, t, sargs, ip, types] → Good c calls →
    c.rc h rc → ∀ (sa : Bytes.Address) (p n i : F), RepAddr h sa sp → np = .field p →
    nf = .field n → ip = .field i → ZMod.val i ≤ ZMod.val n →
    ∀ d Γ, c.types Γ h d types → ∀ T Ss, c.tm d Γ h T t → c.tml d Γ h Ss sargs → r ≠ .field 0 →
      ∀ j, ZMod.val i ≤ j → j < ZMod.val n →
        ∃ S, Ss[ZMod.val (p + (j : F))]? = some S ∧
          Ix.Kernel.Rules.DefEq c.env d (.proj (c.κ (ixAddr sa)) j T) S

/-- `compute_iprj_addr(block_addr, idx)`: **the address of the inductive-projection record of
member `idx` of the block** (`iprjAddr`), computed by serializing the record and hashing it
(`IxonSerialize::put_constant`, `Blake3::bytes_to_addr`); and a record of `c.E` at that address is
that inductive projection: the run hashed its serialization, so a held record there has those raw
bytes (`Good`, `load_escape`), and its decoding is then that record (`LoadFacts.canonical`). -/
def compute_iprj_addr : SpecFn := fun c args h r h' calls =>
  ∀ bp ip, args = [bp, ip] → Good c calls → ∀ (b : Bytes.Address) (i : F), RepAddr h b bp →
    ip = .field i → ∃ a, RepAddr h' a r ∧ ixAddr a = iprjAddr (ixAddr b) (ZMod.val i) ∧
      ∀ cm, Ix.Cert.recordAt c.E (ixAddr a) = some cm →
        cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩

/-- `try_eta_swap(rc, a, b, types)`: exactly one side a `λ`, η-expanded against the other
(`try_eta_expand`); answer `1` is `DefEq` (`DefEq.eta`, by `DefEq.symm` when the `λ` is on the
right). -/
def try_eta_swap : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `try_eta_expand(rc, ty_a, body_a, la, b, types)`: `b`'s io-inferred type head-normalizes to a
`∀` of the same binder datum (`pw_eq`) whose domain is definitionally equal to `ty_a`, and the
`λ`'s body (opened with `ty_a`) is definitionally equal to `b` applied to the opened variable.
**Answer `1` is `DefEq (λ ty_a, body_a) b`** by `DefEq.eta` (the binder's contract is the
default on both sides). -/
def try_eta_expand : SpecFn := fun c args h r _ calls =>
  ∀ rc ta ba la b types, args = [rc, ta, ba, la, b, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ TA BA (ℓ : KLevel) B, c.tm d Γ h TA ta →
      c.tmk d Γ 1 h BA ba → RepKLevel h ℓ la → c.tm d Γ h B b → r ≠ .field 0 →
        Ix.Kernel.Rules.DefEq c.env d (.lam TA BA (bmeta ℓ)) B

/-! ## The structural tier and the congruences -/

/-- `k_is_def_eq_struct(rc, a, b, types)`: `k_is_def_eq_struct_go`; answer `1` is `DefEq`
(`DeClaim`). -/
def k_is_def_eq_struct : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `k_is_def_eq_struct_go(rc, a, b, types)`: node by node: equal variables, sorts
(`DefEq.sort`), one constant (`DefEq.const`), applications (`DefEq.app`), binders
(`de_binder`), a `λ` against a non-`λ` (`try_eta_expand`), equal literals, a `Nat` literal
expanded one layer (`Red.natLit`, then `redL`), projections (`de_proj`), and the lazy-δ
application fallback; answer `1` is `DefEq` (`DeClaim`). -/
def k_is_def_eq_struct_go : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `de_binder(rc, ty_a, body_a, la, ty_b, body_b, lb, types)`: binder congruence: equal binder
data (`pw_eq`), equal domains, equal bodies opened under the left domain. **Answer `1` is
`DefEq` of the two `λ`s and of the two `∀`s** (`DefEq.lam`, `DefEq.forallE` by symmetry: the
rule opens under the right domain; contracts are the defaults). -/
def de_binder : SpecFn := fun c args h r _ calls =>
  ∀ rc ta ba la tb bb lb types, args = [rc, ta, ba, la, tb, bb, lb, types] → Good c calls →
    c.rc h rc → ∀ d Γ, c.types Γ h d types →
    ∀ TA BA (ℓa : KLevel) TB BB (ℓb : KLevel), c.tm d Γ h TA ta → c.tmk d Γ 1 h BA ba →
      RepKLevel h ℓa la → c.tm d Γ h TB tb → c.tmk d Γ 1 h BB bb → RepKLevel h ℓb lb →
      r ≠ .field 0 →
        Ix.Kernel.Rules.DefEq c.env d (.lam TA BA (bmeta ℓa)) (.lam TB BB (bmeta ℓb)) ∧
        Ix.Kernel.Rules.DefEq c.env d (.forallE TA BA (bmeta ℓa)) (.forallE TB BB (bmeta ℓb))

/-- `de_proj(rc, struct_a, fidx_a, ea, struct_b, fidx_b, eb, types)`: one structure address,
one field, equal scrutinees. **Answer `1` is `DefEq` of the two projections** (`DefEq.proj`). -/
def de_proj : SpecFn := fun c args h r _ calls =>
  ∀ rc sa ia ea sb ib eb types, args = [rc, sa, ia, ea, sb, ib, eb, types] → Good c calls →
    c.rc h rc → ∀ (a b : Bytes.Address) (i j : F), RepAddr h a sa → RepAddr h b sb →
    ia = .field i → ib = .field j →
    ∀ d Γ, c.types Γ h d types → ∀ EA EB, c.tm d Γ h EA ea → c.tm d Γ h EB eb → r ≠ .field 0 →
      Ix.Kernel.Rules.DefEq c.env d (.proj (c.κ (ixAddr a)) (ZMod.val i) EA)
        (.proj (c.κ (ixAddr b)) (ZMod.val j) EB)

/-! ## Lazy δ -/

/-- `lazy_delta_loop(rc, a, b, fuel, types) -> (tag, fa, fb)`: `Nat` offsets, then one δ step
on the side(s) the heads select, while fuel lasts (`LoopResult`). -/
def lazy_delta_loop : SpecFn := fun c args h r h' calls =>
  ∀ rc a b fuel types, args = [rc, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `delta_rank(ci)`: a definition's reducibility rank (its hint field), else `0`. It only
orders unfolding; no kernel fact is claimed. It allocates nothing. -/
def delta_rank : SpecFn := fun _ args h r h' _ =>
  ∀ v, args = [v] → h' = h ∧
    ((∃ nl ty val sf, v = .construct kciEnum "Defn" [nl, ty, val, sf, r]) ∨ r = .field 0)

/-- `lazy_delta_step_const_const(rc, a_addr, b_addr, a, b, fuel, types)`: both heads constants
(at `a_addr`, `b_addr`): unfold the side(s) whose constant is a definition or theorem, the higher
rank first (`LoopResult`). The addresses only select; the unfoldings reload the heads. -/
def lazy_delta_step_const_const : SpecFn := fun c args h r h' calls =>
  ∀ rc aa ba a b fuel types, args = [rc, aa, ba, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `unfold_a_and_loop(rc, a, b, fuel, types)`: one δ step on `a` (`delta_unfold`, `whnf_nd`),
then the loop (`LoopResult`). -/
def unfold_a_and_loop : SpecFn := fun c args h r h' calls =>
  ∀ rc a b fuel types, args = [rc, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `unfold_b_and_loop(rc, a, b, fuel, types)`: one δ step on `b`, then the loop
(`LoopResult`). -/
def unfold_b_and_loop : SpecFn := fun c args h r h' calls =>
  ∀ rc a b fuel types, args = [rc, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `unfold_both_and_loop(rc, a, b, fuel, types)`: one δ step on each side, then the loop
(`LoopResult`). -/
def unfold_both_and_loop : SpecFn := fun c args h r h' calls =>
  ∀ rc a b fuel types, args = [rc, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `lazy_delta_a_const_b_proj(rc, a_addr, a, b, fuel, types)`: `b` projection-headed: unfold it
(`try_unfold_proj_app`), else unfold `a`'s head (`try_unfold_head`), then the loop
(`LoopResult`). -/
def lazy_delta_a_const_b_proj : SpecFn := fun c args h r h' calls =>
  ∀ rc aa a b fuel types, args = [rc, aa, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `lazy_delta_b_const_a_proj(rc, b_addr, a, b, fuel, types)`: the mirror image
(`LoopResult`). -/
def lazy_delta_b_const_a_proj : SpecFn := fun c args h r h' calls =>
  ∀ rc ba a b fuel types, args = [rc, ba, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `lazy_delta_both_proj(rc, a, b, fuel, types)`: neither head a constant: unfold the
projection-headed side(s), then the loop (`LoopResult`). -/
def lazy_delta_both_proj : SpecFn := fun c args h r h' calls =>
  ∀ rc a b fuel types, args = [rc, a, b, fuel, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ A B, c.tm d Γ h A a → c.tm d Γ h B b →
      LoopResult c d Γ h' r A B

/-- `is_defn_or_thm(ci)`: **answer `1` means the loaded constant is a definition or a theorem**
(of the constants `CIRep` relates it to). It allocates nothing. -/
def is_defn_or_thm : SpecFn := fun c args h r h' _ =>
  ∀ v, args = [v] → h' = h ∧
    (r ≠ .field 0 → ∀ ci, c.ci h v ci →
      (∃ cv V hn, ci = .defnInfo cv V hn) ∨ ∃ cv V, ci = .thmInfo cv V)

/-- `try_unfold_proj_app(rc, e, types) -> (tag, e')`: at a projection-headed spine, the reduct
`whnf_nd` reaches, or, when that is still projection-headed, the spine with the projection's
scrutinee unfolded one δ step. **Tag `1` is a reduct** (`Red`: the δ step under `Red.projArg`
and `Red.appFn`). -/
def try_unfold_proj_app : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∀ x, r = .tuple [.field 1, x] → ∃ E', c.tm d Γ h' E' x ∧ Red c.env d E E'

/-- `delta_unfold(e) -> (tag, e')`: at a constant-headed spine, the head's definition or theorem
value at the head's levels, applied to the spine (every tag of `KernelWhnf::red_unfold` other
than `0`: `1` a definition, `2` a theorem). **Tag `1` is a reduct** (`Red.delta`,
`Red.deltaThm` with `EnvFacts.thmTyped`, then `Red.appFn`). -/
def delta_unfold : SpecFn := fun c args h r h' calls =>
  ∀ e, args = [e] → Good c calls → ∀ d Γ E, c.tm d Γ h E e →
    ∀ x, r = .tuple [.field 1, x] → ∃ E', c.tm d Γ h' E' x ∧ Red c.env d E E'

/-- `try_lazy_delta_app(rc, a, b, types)`: both heads constants: unfold each head that is a
definition or theorem (`try_unfold_head`), and compare what was unfolded with the other side.
**Answer `1` is `DefEq`** (`redL` and its right-hand variant). -/
def try_lazy_delta_app : SpecFn := fun c args h r _ calls => DeClaim c args h r calls

/-- `head_addr(e) -> (addr, tag)`: **a tag other than `0` means `e`'s spine head is a constant
at `addr`**: the image is that constant applied to a spine. Tag `0` returns the zero address
(nothing claimed). -/
def head_addr : SpecFn := fun c args h r h' calls =>
  ∀ e, args = [e] → Good c calls → ∀ p tag, r = .tuple [p, tag] → tag ≠ .field 0 →
    ∀ d Γ E, c.tm d Γ h E e →
      ∃ (ad : Bytes.Address) (us : List KLevel) (As : List KExpr), RepAddr h' ad p ∧
        E = Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr ad)) us) As

/-- `try_unfold_head(rc, e, ci, types) -> (tag, e')`: at a definition or theorem `ci`, one δ step
on `e` (`delta_unfold`), head-normalized (`whnf_nd`). **Tag `1` is a reduct** (`Red`). `ci`
only selects: the δ step reloads the head. -/
def try_unfold_head : SpecFn := fun c args h r h' calls =>
  ∀ rc e v types, args = [rc, e, v, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∀ x, r = .tuple [.field 1, x] → ∃ E', c.tm d Γ h' E' x ∧ Red c.env d E E'

/-! ## The family -/

/-- The functions of the family. -/
inductive Fn where
  | compare_struct_fields | compute_iprj_addr | de_args | de_binder | de_proj | de_rescue_tier
  | delta_rank | delta_unfold | family_params | head_addr | is_defn_or_thm | is_nat_zero
  | is_prop_type | is_unit_like_type | k_def_eq_rebase | k_is_def_eq | k_is_def_eq_core
  | k_is_def_eq_ordered | k_is_def_eq_slow | k_is_def_eq_slow2 | k_is_def_eq_slow_nd
  | k_is_def_eq_slow_nd_after_core | k_is_def_eq_struct | k_is_def_eq_struct_bounded
  | k_is_def_eq_struct_go | k_is_def_eq_struct_safe | k_is_def_eq_struct_spend
  | k_is_def_eq_structure_tree | k_is_def_eq_structure_tree_app | lazy_delta_a_const_b_proj
  | lazy_delta_b_const_a_proj | lazy_delta_both_proj | lazy_delta_loop
  | lazy_delta_step_const_const | leading_foralls | level_list_eq | nat_offset_of
  | slow2_after_delta | slow2_eager_fallback | try_def_eq_app | try_def_eq_nat | try_eta_expand
  | try_eta_struct | try_eta_swap | try_lazy_delta_app | try_proof_irrel
  | try_same_proj_head_app | try_string_lit_one | try_string_lit_pair | try_unfold_head
  | try_unfold_proj_app | try_unit_like | unfold_a_and_loop | unfold_b_and_loop
  | unfold_both_and_loop
  deriving DecidableEq, Repr

/-- The function's symbol, as `ObsFn` names it. -/
def Fn.name : Fn → String
  | .compare_struct_fields => "KernelDefEq::compare_struct_fields"
  | .compute_iprj_addr => "KernelDefEq::compute_iprj_addr"
  | .de_args => "KernelDefEq::de_args"
  | .de_binder => "KernelDefEq::de_binder"
  | .de_proj => "KernelDefEq::de_proj"
  | .de_rescue_tier => "KernelDefEq::de_rescue_tier"
  | .delta_rank => "KernelDefEq::delta_rank"
  | .delta_unfold => "KernelDefEq::delta_unfold"
  | .family_params => "KernelDefEq::family_params"
  | .head_addr => "KernelDefEq::head_addr"
  | .is_defn_or_thm => "KernelDefEq::is_defn_or_thm"
  | .is_nat_zero => "KernelDefEq::is_nat_zero"
  | .is_prop_type => "KernelDefEq::is_prop_type"
  | .is_unit_like_type => "KernelDefEq::is_unit_like_type"
  | .k_def_eq_rebase => "KernelDefEq::k_def_eq_rebase"
  | .k_is_def_eq => "KernelDefEq::k_is_def_eq"
  | .k_is_def_eq_core => "KernelDefEq::k_is_def_eq_core"
  | .k_is_def_eq_ordered => "KernelDefEq::k_is_def_eq_ordered"
  | .k_is_def_eq_slow => "KernelDefEq::k_is_def_eq_slow"
  | .k_is_def_eq_slow2 => "KernelDefEq::k_is_def_eq_slow2"
  | .k_is_def_eq_slow_nd => "KernelDefEq::k_is_def_eq_slow_nd"
  | .k_is_def_eq_slow_nd_after_core => "KernelDefEq::k_is_def_eq_slow_nd_after_core"
  | .k_is_def_eq_struct => "KernelDefEq::k_is_def_eq_struct"
  | .k_is_def_eq_struct_bounded => "KernelDefEq::k_is_def_eq_struct_bounded"
  | .k_is_def_eq_struct_go => "KernelDefEq::k_is_def_eq_struct_go"
  | .k_is_def_eq_struct_safe => "KernelDefEq::k_is_def_eq_struct_safe"
  | .k_is_def_eq_struct_spend => "KernelDefEq::k_is_def_eq_struct_spend"
  | .k_is_def_eq_structure_tree => "KernelDefEq::k_is_def_eq_structure_tree"
  | .k_is_def_eq_structure_tree_app => "KernelDefEq::k_is_def_eq_structure_tree_app"
  | .lazy_delta_a_const_b_proj => "KernelDefEq::lazy_delta_a_const_b_proj"
  | .lazy_delta_b_const_a_proj => "KernelDefEq::lazy_delta_b_const_a_proj"
  | .lazy_delta_both_proj => "KernelDefEq::lazy_delta_both_proj"
  | .lazy_delta_loop => "KernelDefEq::lazy_delta_loop"
  | .lazy_delta_step_const_const => "KernelDefEq::lazy_delta_step_const_const"
  | .leading_foralls => "KernelDefEq::leading_foralls"
  | .level_list_eq => "KernelDefEq::level_list_eq"
  | .nat_offset_of => "KernelDefEq::nat_offset_of"
  | .slow2_after_delta => "KernelDefEq::slow2_after_delta"
  | .slow2_eager_fallback => "KernelDefEq::slow2_eager_fallback"
  | .try_def_eq_app => "KernelDefEq::try_def_eq_app"
  | .try_def_eq_nat => "KernelDefEq::try_def_eq_nat"
  | .try_eta_expand => "KernelDefEq::try_eta_expand"
  | .try_eta_struct => "KernelDefEq::try_eta_struct"
  | .try_eta_swap => "KernelDefEq::try_eta_swap"
  | .try_lazy_delta_app => "KernelDefEq::try_lazy_delta_app"
  | .try_proof_irrel => "KernelDefEq::try_proof_irrel"
  | .try_same_proj_head_app => "KernelDefEq::try_same_proj_head_app"
  | .try_string_lit_one => "KernelDefEq::try_string_lit_one"
  | .try_string_lit_pair => "KernelDefEq::try_string_lit_pair"
  | .try_unfold_head => "KernelDefEq::try_unfold_head"
  | .try_unfold_proj_app => "KernelDefEq::try_unfold_proj_app"
  | .try_unit_like => "KernelDefEq::try_unit_like"
  | .unfold_a_and_loop => "KernelDefEq::unfold_a_and_loop"
  | .unfold_b_and_loop => "KernelDefEq::unfold_b_and_loop"
  | .unfold_both_and_loop => "KernelDefEq::unfold_both_and_loop"

/-- The function's spec. -/
def Fn.spec : Fn → SpecFn
  | .compare_struct_fields => Specs.DefEq.compare_struct_fields
  | .compute_iprj_addr => Specs.DefEq.compute_iprj_addr
  | .de_args => Specs.DefEq.de_args
  | .de_binder => Specs.DefEq.de_binder
  | .de_proj => Specs.DefEq.de_proj
  | .de_rescue_tier => Specs.DefEq.de_rescue_tier
  | .delta_rank => Specs.DefEq.delta_rank
  | .delta_unfold => Specs.DefEq.delta_unfold
  | .family_params => Specs.DefEq.family_params
  | .head_addr => Specs.DefEq.head_addr
  | .is_defn_or_thm => Specs.DefEq.is_defn_or_thm
  | .is_nat_zero => Specs.DefEq.is_nat_zero
  | .is_prop_type => Specs.DefEq.is_prop_type
  | .is_unit_like_type => Specs.DefEq.is_unit_like_type
  | .k_def_eq_rebase => Specs.DefEq.k_def_eq_rebase
  | .k_is_def_eq => Specs.DefEq.k_is_def_eq
  | .k_is_def_eq_core => Specs.DefEq.k_is_def_eq_core
  | .k_is_def_eq_ordered => Specs.DefEq.k_is_def_eq_ordered
  | .k_is_def_eq_slow => Specs.DefEq.k_is_def_eq_slow
  | .k_is_def_eq_slow2 => Specs.DefEq.k_is_def_eq_slow2
  | .k_is_def_eq_slow_nd => Specs.DefEq.k_is_def_eq_slow_nd
  | .k_is_def_eq_slow_nd_after_core => Specs.DefEq.k_is_def_eq_slow_nd_after_core
  | .k_is_def_eq_struct => Specs.DefEq.k_is_def_eq_struct
  | .k_is_def_eq_struct_bounded => Specs.DefEq.k_is_def_eq_struct_bounded
  | .k_is_def_eq_struct_go => Specs.DefEq.k_is_def_eq_struct_go
  | .k_is_def_eq_struct_safe => Specs.DefEq.k_is_def_eq_struct_safe
  | .k_is_def_eq_struct_spend => Specs.DefEq.k_is_def_eq_struct_spend
  | .k_is_def_eq_structure_tree => Specs.DefEq.k_is_def_eq_structure_tree
  | .k_is_def_eq_structure_tree_app => Specs.DefEq.k_is_def_eq_structure_tree_app
  | .lazy_delta_a_const_b_proj => Specs.DefEq.lazy_delta_a_const_b_proj
  | .lazy_delta_b_const_a_proj => Specs.DefEq.lazy_delta_b_const_a_proj
  | .lazy_delta_both_proj => Specs.DefEq.lazy_delta_both_proj
  | .lazy_delta_loop => Specs.DefEq.lazy_delta_loop
  | .lazy_delta_step_const_const => Specs.DefEq.lazy_delta_step_const_const
  | .leading_foralls => Specs.DefEq.leading_foralls
  | .level_list_eq => Specs.DefEq.level_list_eq
  | .nat_offset_of => Specs.DefEq.nat_offset_of
  | .slow2_after_delta => Specs.DefEq.slow2_after_delta
  | .slow2_eager_fallback => Specs.DefEq.slow2_eager_fallback
  | .try_def_eq_app => Specs.DefEq.try_def_eq_app
  | .try_def_eq_nat => Specs.DefEq.try_def_eq_nat
  | .try_eta_expand => Specs.DefEq.try_eta_expand
  | .try_eta_struct => Specs.DefEq.try_eta_struct
  | .try_eta_swap => Specs.DefEq.try_eta_swap
  | .try_lazy_delta_app => Specs.DefEq.try_lazy_delta_app
  | .try_proof_irrel => Specs.DefEq.try_proof_irrel
  | .try_same_proj_head_app => Specs.DefEq.try_same_proj_head_app
  | .try_string_lit_one => Specs.DefEq.try_string_lit_one
  | .try_string_lit_pair => Specs.DefEq.try_string_lit_pair
  | .try_unfold_head => Specs.DefEq.try_unfold_head
  | .try_unfold_proj_app => Specs.DefEq.try_unfold_proj_app
  | .try_unit_like => Specs.DefEq.try_unit_like
  | .unfold_a_and_loop => Specs.DefEq.unfold_a_and_loop
  | .unfold_b_and_loop => Specs.DefEq.unfold_b_and_loop
  | .unfold_both_and_loop => Specs.DefEq.unfold_both_and_loop

end IxVM.Refinement.Core.Specs.DefEq
