/- # O3: `casesOn` over a permuted or split block

## Contract
Input: an occurrence `x.casesOn.{us} a₁ … a_m` where `x` is a member of a
changed block `b` with no collapsed class (Pass 1: every class a singleton;
the block may be permuted, split, nested-reordered or have evaporated nested
auxiliaries), and `img(x.rec)` has a head shape (`RecShape`): `ρ` applied to
the image's parameters, motive variables, some minors, its indices and major.
Lean's `x.casesOn` has the telescope `ps motive is t minorsₓ`, one minor per
constructor of `x` (`n = np + 1 + ni + 1 + |ctors x|`).

Output: `ρ.casesOn.{ℓs[us]} a₁ … a_m`, the Ix `casesOn` of `x`'s class (the
display name next to `ρ`, D14) with the **same arguments**.

## Faithfulness (definitional)
Lean's `x.casesOn := λ ps motive is t mins. x.rec ps M⃗ N⃗ is t` where `M⃗`
puts `motive` at `x`'s slot and a constant motive at every other slot, and
`N⃗` puts `λ fs ihs. minᵢ fs` (IHs discarded) at `x`'s constructors and a
constant at every other. Pass 2 builds `ρ.casesOn` by the same construction
on `x`'s canonical component: `ρ.casesOn := λ ps motive is t mins. ρ ps M⃗′ N⃗′
is t`. The baseline `img(x.casesOn) a⃗` is Lean's value over `img(x.rec)`
(Def 3.5). Conversion steps: δ (img(x.casesOn)), β (its λs), δ+β
(img(x.rec)): `ρ ps M⃗″ N⃗″ is t` where `M⃗″, N⃗″` are `M⃗, N⃗` permuted to the
Ix slots of `ρ`, with the slots of other components dropped (they are absent
from `ρ`) and, for a split block, relocated hypotheses at the fields into
other components — which the casesOn minors discard (β). The constant motives
and minors of the other members are Lean's and Pass 2's same terms (they
depend only on the member's type), so `M⃗″ = M⃗′` and `N⃗″ ≡β N⃗′`; the
η-wrappers `λ fs ihs. minᵢ fs` are the same on both sides. Hence
`img(x.casesOn) a⃗ ≡ ρ ps M⃗′ N⃗′ is t ≡δβ ρ.casesOn a⃗` (δ of `ρ.casesOn`, β).
Levels: O5.

## Canonicity
`ρ.casesOn` is the twin's `casesOn` (the canonical twin's `x′.casesOn` *is*
the Ix `casesOn`), with the same arguments: the output depends on the
canonical class of `x` and the arguments only.

## Side condition and fallback
Decidable: `classify` gives `casesOn`; the block has no collapsed class;
`img(x.rec)` has a shape (head `ρ`, parameters, indices and major in order,
motives as variables); Lean's `casesOn` has the standard telescope with
`|ctors x|` minors and the recursor's universe parameters; O5 accepts the
levels; `ρ.casesOn` resolves in `E`; `m ≥ n`. Otherwise the baseline.
A collapsed component declines: there the image lifts or pairs motives at
`max 1 u`, and `ρ.{max 1 u} …` projected is not definitionally the Ix
`casesOn` at `u` without induction (O8's territory, A6).

## Non-canonical set and evidence
None. Evidence: `Tests/Ix/Compile/Pass/O3Cases.lean` (fires: permuted and
split blocks; declines: a collapsed block); the library's matchers and
`_sparseCasesOn` helpers that go through `casesOn`.
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O5
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (mkAppN)

/-- The member a `x.casesOn` belongs to. -/
def casesOnMember : Name → Option Name
  | .str x "casesOn" _ => some x
  | _ => none

def O3.apply (env : OptEnv) (o : Occ) : Option Expr := do
  let (k, r) ← classify o.head
  if k != .kCasesOn then none
  let x ← casesOnMember o.head
  let b ← env.blockOf o.head
  if b.change.collapse then none
  let cls ← b.classOf.get? x
  if cls.size != 1 then none
  let s ← b.shapes.get? r
  let some (.inductInfo iv) := env.const? x | none
  let n ← standardTelescope env s .kCasesOn o.head iv.ctors.size
  if o.args.size < n then none
  let ls ← O5.levels s o.us
  let ixCases ← ixAuxOf s.ixRec .kCasesOn
  if !env.resolves ixCases then none
  return mkAppN (Expr.mkConst ixCases ls) o.args

end Ix.Compile.Pass.Opt

end
