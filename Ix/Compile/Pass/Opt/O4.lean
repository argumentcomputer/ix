/- # O4: `below`, `brecOn`, `.go`, `.eq` over a permuted block or a cross-field-free component

## Contract
Input: an occurrence `a.{us} a₁ … a_m` where `a` is `x.below`, `x.brecOn`,
`x.brecOn.go`, `x.brecOn.eq` or the nested `all₀.below_j`, `all₀.brecOn_j`
(`.go`, `.eq`) of a changed block `b` with no collapsed class, whose related
recursor `r` (`x.rec`, `all₀.rec_j`) has an image of **selection shape**
`ρ` (`RecShape` with every Ix minor a bare Lean minor variable): `img(r) =
λ ps ms mins is t. ρ ps (ms ∘ σ) (mins ∘ σ′) is t`. This holds for every
member of a permuted block (`σ, σ′` bijections, O1's `π, π′`) and for every
member of a component of a split block whose constructors have no field
into another component (`σ, σ′` select the component's motives and minors).
Lean's telescopes: `below`: `ps ms is t`; `brecOn`, `.go`, `.eq`:
`ps ms is t Fs`, one handler per motive.

Output, `ρ.S` the Ix auxiliary of the same kind next to `ρ` (`ρ.below`,
`ρ.brecOn`, `ρ.brecOn.go`, `ρ.brecOn.eq`; `P.below_k` … for `ρ = P.rec_k`,
D14), `e` the arguments beyond the telescope:
* `below`: `ρ.below.{ℓs[us]} ps (ms ∘ σ) is t e`;
* `brecOn`, `.go`, `.eq`: `ρ.S.{ℓs[us]} ps (ms ∘ σ) is t (Fs ∘ σ) e`.

## Faithfulness (definitional)
Lean builds `below`, `brecOn`, `.go`, `.eq` from `r` by `mkBelow`/`mkBRecOn`:
`r` applied to motives and minors that are functions of the user's motives
(and handlers), slot by slot, each slot's minor built from its constructor's
fields and IHs. Pass 2 builds `ρ.S` by the same construction on the
canonical component. The baseline `img(a) a⃗` is Lean's value over `img(r)`
(Def 3.5); with the selection shape, `img(r)` passes slot `i`'s motive and
minors to Ix slot `σ⁻¹ i` unchanged and does not use the slots outside the
component (their constructors are not fields of the component's types, so no
IH mentions them). Lean's slot term for a slot in the component is Pass 2's
slot term for the corresponding Ix slot with the motives and handlers
renamed by `σ` (same construction, same member, same fields). Conversion
steps: δ (img(a)), β, δ+β (img(r)), β (the slots outside the component are
discarded), then δ+β of `ρ.S` backwards: `img(a) a⃗ ≡ ρ.S ps (ms∘σ) is t
(Fs∘σ)`. For `.eq` (a theorem) the statement is the same equation with both
sides rewritten this way; the proof term is immaterial (proof irrelevance).
Levels: O5.

## Canonicity
For the canonical twin (the block in canonical order, or the component
declared alone), `x′.below`/`x′.brecOn` … *are* the Ix auxiliaries and the
user's motives and handlers are already the selected ones in canonical
order: the output is the twin's term, depending on `σ` (read through the
image: canonical order and discovery order), the canonical levels and the
arguments.

## Side condition and fallback
Decidable: `classify` gives one of the kinds; the block has no collapsed
class; `img(r)` has a selection shape; Lean's auxiliary has the standard
telescope and the recursor's universe parameters; O5 accepts the levels;
`ρ.S` resolves in `E`; for the `brecOn` family, Lean's `below` is a
definition (a Prop block's `IndPredBelow` is an inductive, which Lean's
`brecOn` and the user's handlers mention: the Ix `brecOn` is over the Ix
family, a different inductive, so the rewrite would not typecheck, measured
on the twins' `Cliques.IP`); `m ≥ n`. Otherwise the baseline. A component with a
field into another component declines: the Ix `below` of the component has no
slot for the cross field while Lean's has one, so the two are not
definitionally equal; that is O9's re-pathing (proof-justified, A6).

## Non-canonical set and evidence
None for full applications. Evidence: `Tests/Ix/Compile/Pass/O4BRecOn.lean`
(structural recursion over a permuted pair and over the lower component of a
split block: fires; over the upper component, with the cross field:
declines); the library's `Ring` functions and their `_f` (26 `below`, 16
`brecOn` call sites, CEN).
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O5
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr)
open Ix.Compile.Canon (mkAppN)

/-- `x.rec ↦ x.below`, `all₀.rec_j ↦ all₀.below_j`. -/
def belowNameOf : Name → Name
  | .str p s _ => Name.mkStr p ("below" ++ (s.drop 3).toString)
  | n => n

/-- Every Ix minor is a bare Lean minor variable (no relocation, no
wrapper): the image selects and permutes its arguments. -/
def RecShape.isSelection (s : RecShape) : Bool := s.minorSrc.all Option.isSome

def O4.apply (env : OptEnv) (o : Occ) : Option Expr := do
  let (k, r) ← classify o.head
  if !(k == .kBelow || k == .kBRecOn || k == .kGo || k == .kEq) then none
  let b ← env.blockOf o.head
  if b.change.collapse then none
  let s ← b.shapes.get? r
  if !s.isSelection then none
  let n ← standardTelescope env s k o.head
  if o.args.size < n then none
  let ls ← O5.levels s o.us
  let ixA ← ixAuxOf s.ixRec k
  if !env.resolves ixA then none
  -- the `brecOn` family of a block whose `below` is Lean's `IndPredBelow` inductive
  -- (a Prop block) is over that inductive, not over the Ix `below`: decline
  if k != .kBelow then
    let some (.defnInfo _) := env.const? (belowNameOf r) | none
    pure ()
  let a := o.args
  let ps := a.extract 0 s.np
  let ms ← pick (a.extract s.np (s.np + s.nm)) s.motiveSrc
  let tail := a.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1)
  let rest := a.extract n a.size
  let hs ← if k == .kBelow then pure #[]
    else pick (a.extract (s.np + s.nm + s.ni + 1) n) s.motiveSrc
  return mkAppN (Expr.mkConst ixA ls) (ps ++ ms ++ tail ++ hs ++ rest)

end Ix.Compile.Pass.Opt

end
