/- # O8: `casesOn` (and so matchers) over a collapsed or lifted member

## Contract
Input: an occurrence `x.casesOn.{u,us} ps motive is t mins e` (`n = np + 1 +
ni + 1 + |ctors x|` arguments, then `e`) in the value of a definition `c`
(`Occ.site`), where `x` is a member of a changed block `b` with a collapsed
class (Pass 1), so that `img(x.rec)` is packed (`Opt.Packed`): `x`'s slot
in its eliminator `ρ` is a tuple (`x` collapsed with other members) or
lifted (`x` alone next to a tuple). Matchers (`f.match_k`) and the other
helpers Lean builds over `casesOn` are definitions whose values contain
such occurrences, so O8 makes them single-member too.

Output: `ρ.casesOn.{u,us} ps motive is t mins e`, the Ix `casesOn` of
`x`'s class (the display name next to `ρ`, D14), with the **same
arguments**, at Lean's motive universe `u` (`singleLevels`). The output is
written into the canonical form `c._ix` of the definition; `c` keeps the
baseline (decision 5, D1, below).

## Faithfulness (proof-justified; the statement Phase B formalises)
Write `L := img(x.casesOn)` (Def 3.5: Lean's `casesOn` value over
`img(x.rec)`) and `R := ρ.casesOn`. **Lemma O8.** For all `ps`, `motive`,
`is`, `t : x ps is` and `mins`:

    L ps motive is t mins = R ps motive is t mins        (in `motive is t`)

*Proof*, by case analysis on `t` (the recursor `ρ` at the Prop motive
`λ is t. L … t … = R … t …`; `ρ` eliminates into Prop because every
inductive does). Case `t = c_q fs` (`c_q` the `q`-th constructor of `x`'s
class, `fs` its fields):
* `L … (c_q fs) mins` →δβ `unwrap_p (ρ.{max 1 u} ps M⃗ N⃗ is (c_q fs))` where
  Lean's `casesOn` puts `motive` at `x`'s position of the slot and
  `λ fs ihs. minᵢ fs` at `x`'s constructors (Def 3.5: Lean's construction,
  the hypotheses discarded); →ι `unwrap_p (N_q fs ihs⃗)` with `N_q` the
  packed minor of the slot (§4.2 step 4: a `PProd.mk`/`And.intro` tuple,
  or `⟨v, True.intro⟩` for a lifted slot, whose component `p` is
  `(λ fs ihs. min_q fs) fs ihs⃗`); →proj, β `min_q fs`;
* `R … (c_q fs) mins` →δβι `min_q fs` (Pass 2's `casesOn`, Lean's
  construction on the canonical class).
Both sides are convertible to `min_q fs`, so the case closes by `Eq.refl`.
No hypothesis is used, so no induction is needed. ∎

**Corollary (the rewritten constant).** If `c` is `base(c)` with the
occurrences `o₁ … o_k` replaced by their O8 outputs, then `c = base(c)`,
by `funext` over the binders above each occurrence and `congrArg` with
Lemma O8 at each `oⱼ` (the occurrences are disjoint subterms; the
arguments are copied). Phase B states this per constant as
`N(c) = base(c)` and derives it from Lemma O8 by congruence.

**Where the output goes (decision 5, D1).** `c._ix` (Lean's `c` renamed,
with `c`'s type) is only propositionally equal to `base(c)`, so the output
is written there and the Lean name `c` keeps its baseline (the faithful
image, convertible to Lean's term by δβ); `c` is recorded non-canonical
with the cause O8. The proof term of `c._ix = c` is the Corollary (`funext`,
`congrArg` with Lemma O8, a case analysis with `ρ` whose cases close by
`Eq.refl`). The forms are not convertible at an open major (the packed
`casesOn` is stuck on `unwrap_p`), only at constructors (ι on both sides,
which the value pins check). No caller is read. A matcher keeps its Lean
form, so the equation compiler's outputs over it (`f`, `q._f`,
`q._sunfold`, `q._unsafe_rec`, the equation lemmas) are ordinary callers of a
name whose form did not change; the canonical `f._ix`, where one exists,
refers to the matcher's `_ix` form (`Driver.compileCanon`).

## Canonicity
For the canonical twin (one member per class, `b`'s universes and
parameters kept), `x′.casesOn` *is* the Ix `casesOn` of the class and the
user's arguments are the same terms up to the renaming: the output is the
twin's term. It depends on `x`'s class (canonical) and the arguments only;
addresses enter through `ρ.casesOn`, i.e. through the canonical block.

## Side condition and fallback
Decidable: `classify` gives `casesOn`; `b` has a collapsed class; the image
of `x.rec` reads as packed (`readPacked`); Lean's `casesOn` has the
recursor's universe parameters and `np + 1 + ni + 1 + |ctors x|` binders;
`m ≥ n`; `ρ.casesOn` resolves in `E`; `singleLevels` accepts the levels;
`pjAllowed` (the value of a definition). Otherwise no `c._ix` is emitted
for the occurrence, which keeps the baseline, the faithful image.

## Non-canonical set and evidence
The Lean name of every definition with an O8 rewrite (an explicit `casesOn`
user, a matcher, Lean's `noConfusionType` of a collapsed member): cause O8;
its callers that are not rewritten themselves (a function over its matcher):
`INHERITED`. Evidence: `O8Cases` (an explicit `casesOn` and matcher-based
functions over a collapsed pair, and over a lifted member next to a
collapsed class; a definition with an open unfolding against Lean's
`casesOn`, which keeps checking; with the switch on the `_ix` forms
byte-equal to the twins; value pins by `rfl`, checked by the three kernels). Library load
0 (no collapsed block in Init+Std or Mathlib).
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O3
public import Ix.Compile.Pass.Opt.Packed
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (mkAppN)

def O8.apply (env : OptEnv) (o : Occ) : Option Expr := do
  if !pjAllowed o then none
  let (k, r) ← classify o.head
  if k != .kCasesOn then none
  let x ← casesOnMember o.head
  let b ← env.blockOf o.head
  if !b.change.collapse then none
  let s ← b.packed? env r
  let some (.inductInfo iv) := env.const? x | none
  let ci ← env.const? o.head
  if ci.getCnst.levelParams != s.levelParams then none
  let n := s.np + 1 + s.ni + 1 + iv.ctors.size
  if forallArity ci.getCnst.type != n then none
  if o.args.size < n then none
  let ixCases ← ixAuxOf s.ixRec .kCasesOn
  if !env.resolves ixCases then none
  let ls ← singleLevels env s o.us
  return mkAppN (Expr.mkConst ixCases ls) o.args

end Ix.Compile.Pass.Opt

end

