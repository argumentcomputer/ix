/- # O6: an image that is an Ix recursor applied to (a selection of) its own arguments

## Contract
Input: an occurrence `r.{us} a₁ … a_m` or `r.recOn.{us} a₁ … a_m` of a Lean
recursor `r` of a changed block whose image has a **selection shape** `ρ`
(every Ix minor a bare minor variable, `RecShape.isSelection`), whatever the
block's change kind: `img(r) = λ ps ms mins is t. ρ.{ℓs} ps (ms ∘ σ)
(mins ∘ σ′) is t` with `σ`, `σ′` injective (`motiveSrc`, `minorSrc`). This
covers the cases O1 leaves: a component of a split block whose constructors
have no field into another component (the motives and minors of the other
components are not used by `ρ`, so `σ`, `σ′` drop them), and the nested
auxiliaries' recursors `all₀.rec_j` of such a component.

Output, `n` the telescope and `e` the arguments beyond it:
* `rec`: `ρ.{ℓs[us]} ps (ms ∘ σ) (mins ∘ σ′) is t e`;
* `recOn` (`ps ms is t mins`): `ρ.recOn.{ℓs[us]} ps (ms ∘ σ) is t
  (mins ∘ σ′) e`, the Ix `recOn` of the class.

## Faithfulness (definitional)
`rec`: the output is `img(r)`'s body at the arguments: one δ (img) and `n`
β-steps. The arguments `σ` and `σ′` drop are not used by the body (they
belong to members of other components, which cannot occur in the major's
type, design document §4.5): β discards them. Nothing used is dropped.
`recOn`: as O1's `recOn` (`img(r.recOn) ≡δβ img(r) ps ms mins is t`, and
`ρ.recOn ≡δβ ρ` with its arguments reordered), with the unused arguments
discarded by β. Levels: O5.

## Canonicity
For the canonical twin (the component declared alone) the user's occurrence
is `ρ` (or `ρ.recOn`) applied to the kept arguments in canonical order: the
output is the twin's term, depending on the image (canonical) and the
arguments only.

## Side condition and fallback
Decidable: `classify` gives `rec` or `recOn`; `img(r)` has a selection
shape; Lean's auxiliary has the standard telescope and the recursor's
universe parameters; O5 accepts the levels; for `recOn` the Ix `recOn`
resolves; `m ≥ n`. Otherwise the baseline (which, for a `rec` with such an
image, is the same term: O6 makes the pass explicit and independent of the
development, design document §1.4 "O6 overlaps O1, O3 and O4 … both
rewrites produce the same term").

## Non-canonical set and evidence
None for full applications. Evidence: `Tests/Ix/Compile/Pass/O2Split.lean`
(`SB.viaRec`, and the relocated calls of `SA.viaRec`) and
`O5PropSplit.lean` (`Q.elim` at universe `0`).
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O4
public import Ix.Compile.Pass.Opt.O5
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr)
open Ix.Compile.Canon (mkAppN)

def O6.apply (env : OptEnv) (o : Occ) : Option Expr := do
  let (k, r) ← classify o.head
  if k != .kRec && k != .kRecOn then none
  let b ← env.blockOf o.head
  let s ← b.shapes.get? r
  if !s.isSelection then none
  let n ← standardTelescope env s k o.head
  if o.args.size < n then none
  let ls ← O5.levels s o.us
  let a := o.args
  let ps := a.extract 0 s.np
  let ms ← pick (a.extract s.np (s.np + s.nm)) s.motiveSrc
  let minSrc := s.minorSrc.filterMap id
  let extra := a.extract n a.size
  if k == .kRec then
    let mins ← pick (a.extract (s.np + s.nm) (s.np + s.nm + s.nmin)) minSrc
    let tail := a.extract (s.np + s.nm + s.nmin) n
    return mkAppN (Expr.mkConst s.ixRec ls) (ps ++ ms ++ mins ++ tail ++ extra)
  else
    let ixRecOn ← ixAuxOf s.ixRec .kRecOn
    if !env.resolves ixRecOn then none
    let tail := a.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1)
    let mins ← pick (a.extract (s.np + s.nm + s.ni + 1) n) minSrc
    return mkAppN (Expr.mkConst ixRecOn ls) (ps ++ ms ++ tail ++ mins ++ extra)

end Ix.Compile.Pass.Opt

end
