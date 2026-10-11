/- # O1: the recursor of a permuted block

## Contract
Input: an occurrence `r.{us} a₁ … a_m` or `r.recOn.{us} a₁ … a_m` (design
document §1.3) where `r` is a Lean recursor (`x.rec`, or `all₀.rec_j` of a
nested auxiliary) of a changed block `b` whose canonicalisation is a **pure
permutation** (Pass 1: one component, every class a singleton, no
evaporation; only the member order and/or the discovery order of nested
auxiliaries differ), with `img(r)` of shape `ρ` (`RecShape`): `img(r) = λ ps
ms mins is t. ρ.{ℓs} ps (ms ∘ π⁻¹) (mins ∘ π′⁻¹) is t`, `π` the motive
bijection and `π′` the minor bijection the image generator chose by motive
type (`motiveSrc`, `minorSrc`).

Output, with `n = np + nm + nmin + ni + 1`, `ps, ms, mins, is, t` the first
`n` arguments in Lean's order (for `recOn`: `ps ms is t mins`) and `e` the
rest:
* `rec`:   `ρ.{ℓs[us]} ps (ms ∘ π⁻¹) (mins ∘ π′⁻¹) is t e`;
* `recOn`: `ρ.recOn.{ℓs[us]} ps (ms ∘ π⁻¹) is t (mins ∘ π′⁻¹) e`, the Ix
  `recOn` of the class (the display name next to `ρ`, D14).
The arguments are copied unchanged; the result references no image.

## Faithfulness (definitional)
`rec`: by Def 3.4 with singleton classes there is no tuple, no lift and no
relocation (one component), so each Ix minor is the Lean minor, η-contracted
(§1.3): `img(r) ≡ λ ps ms mins is t. ρ ps (ms∘π⁻¹) (mins∘π′⁻¹) is t`, which is
exactly the shape read off the image. Conversion steps from the baseline
`img(r) a₁ … a_m`: one δ (img), `n` β. When a Lean minor is
λ-wrapped in the image (a reflexive field's `fun a => ih a`, kept by A3), the
step is η: `λ fs ihs. m fs (λ a. ih a) ≡η m`; the shape requires bare
variables, so that case declines (see below).
`recOn`: Lean's `r.recOn := λ ps ms is t mins. r ps ms mins is t`, and Pass 2
builds the Ix `recOn` by the same construction on the canonical block:
`ρ.recOn := λ ps ms′ is t mins′. ρ ps ms′ mins′ is t`. So
`img(r.recOn) a⃗ ≡δβ img(r) ps ms mins is t ≡δβ ρ ps (ms∘π⁻¹) (mins∘π′⁻¹) is t
≡δβ ρ.recOn ps (ms∘π⁻¹) is t (mins∘π′⁻¹)` (δ of `img(r.recOn)` and of
`ρ.recOn`, β; O5 for the levels).

## Canonicity
For the canonical twin `b′` of `b`, `r′.rec` is the Ix recursor itself and
the user's arguments are already in canonical order: `ρ ps ms′ mins′ is t`
with `ms′ = ms ∘ π⁻¹` term for term. The output depends on `π, π′` (functions
of the canonical order, §2.3, and the discovery order, §2.5, read through the
image), the canonical levels and the arguments, and not on Lean's member
order beyond `π`. `recOn` goes to the Ix `recOn` (not to `ρ`) because the
twin's `recOn` occurrence denotes the Ix `recOn`: this is the twin's term.
Addresses enter only through `ρ`'s.

## Side condition and fallback
Decidable: `classify` gives `rec` or `recOn`; the block's change kind is
permutation-only; `img(r)` has a shape that is a permutation (`isPerm`: every
Lean motive and minor passed once, as a bare variable); Lean's auxiliary has
the standard telescope and the recursor's universe parameters; O5 accepts the
levels; for `recOn` the Ix `recOn` resolves in `E`; `m ≥ n`. Otherwise the
occurrence keeps its baseline (the inline image), which is faithful by Def 3.6.

## Non-canonical set and evidence
None for full applications; bare or partial occurrences are `BARE` (§7.2).
Evidence: `Tests/Ix/Compile/Pass/O1Perm.lean` (fires: permuted pair and a
nested-order block; declines: a collapsed block); the library: 6 permuted
blocks, the `Ring` functions and the `_sparseCasesOn` helpers over
nested-order blocks (CEN: 206 `rec`-plan call sites).
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O5
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr)
open Ix.Compile.Canon (mkAppN BlockChange)

/-- Pass 1's change kind is a pure permutation (member order and/or nested
discovery order). -/
def permutationOnly (c : BlockChange) : Bool := !c.split && !c.collapse && !c.evaporation

def O1.apply (env : OptEnv) (o : Occ) : Option Expr := do
  let (k, r) ← classify o.head
  if k != .kRec && k != .kRecOn then none
  let b ← env.blockOf o.head
  if !permutationOnly b.change then none
  let s ← b.shapes.get? r
  if !s.isPerm then none
  let n ← standardTelescope env s k o.head
  if o.args.size < n then none
  let ls ← O5.levels s o.us
  let a := o.args
  let ps := a.extract 0 s.np
  let extra := a.extract n a.size
  match k with
  | .kRec =>
    let ms := a.extract s.np (s.np + s.nm)
    let mins := a.extract (s.np + s.nm) (s.np + s.nm + s.nmin)
    let tail := a.extract (s.np + s.nm + s.nmin) n
    let ms' ← pick ms s.motiveSrc
    let mins' ← pick mins (s.minorSrc.filterMap id)
    return mkAppN (Expr.mkConst s.ixRec ls) (ps ++ ms' ++ mins' ++ tail ++ extra)
  | _ =>
    let ixRecOn ← ixAuxOf s.ixRec .kRecOn
    if !env.resolves ixRecOn then none
    let ms := a.extract s.np (s.np + s.nm)
    let tail := a.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1)
    let mins := a.extract (s.np + s.nm + s.ni + 1) n
    let ms' ← pick ms s.motiveSrc
    let mins' ← pick mins (s.minorSrc.filterMap id)
    return mkAppN (Expr.mkConst ixRecOn ls) (ps ++ ms' ++ tail ++ mins' ++ extra)

end Ix.Compile.Pass.Opt

end
