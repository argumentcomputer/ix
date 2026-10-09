/- # O2: the recursor of a split block (relocated minors)

## Contract
Input: an occurrence `r.{us} ps ms mins is t e` of a Lean recursor `r`
(`x.rec`, or `all₀.rec_j`) of a changed block `b` that is **split** (Pass 1:
several components) with no collapsed class, and `img(r)` of head shape `ρ`
(`RecShape`): `ρ` is the recursor of `r`'s component `c`, its motives are
the motive variables of `c`'s Lean motives (`motiveSrc`, the others are not
used), and each Ix minor is either a Lean minor variable or a term whose head
is one (a minor with relocated hypotheses, Def 3.4 step 4.2, or a reflexive
wrapper).

Output: `ρ.{ℓs[us]} ps (ms ∘ σ) mins′ is t e`, where `σ` is `motiveSrc` and
Ix minor `k`, for the Lean minor `mⱼ` it is built from (constructor `c` with
fields `fs`), is
* `mⱼ` itself when no field of `c` is recursive into another component;
* otherwise the **adapted minor** `λ fs ihsᶜ. mⱼ fs ih₁ … ih_q`, the binders
  `fs` and `ihsᶜ` (one per field recursive into `c`) with the domains of
  Lean's minor type instantiated at the occurrence's parameters, motives and
  preceding minors, and, per Lean IH binder `ihₗ` over field `f` of type
  `∀ ys, T idx`: the wrapper's own binder when `T` is in `c`, else the
  **relocated call** `λ ys. ρ_T …`, the engine's rewrite of the occurrence
  `r_T.{us} ps ms mins idx (f ys)` of `T`'s Lean recursor (O2 again, or O6
  for a component with no further cross field).
The user's minor `mⱼ` is applied, not substituted: the β-redex is left, as
the old call-site surgery left it (the bytes the library has today), and no
other redex is created.

## Faithfulness (definitional, up to η)
By Def 3.4 the image's Ix minor for `c` is `λ fs ihs. mⱼ fs h₁ … h_q` with
`hₗ` the unwrapped Ix hypothesis for a field in `c` and the image of `T`'s
recursor applied to the field for a field outside `c` (step 4.2), developed.
The adapted minor is that term with (i) the relocated hypothesis
`img(r_T) ps ms mins idx (f ys)` in place of its development, which is the
same term after δ (img) and β, and which the engine rewrites by a pass that is
itself definitional; (ii) the binder domains as Lean's minor type gives them
(`motive fs` with the user's motive applied, a β-redex of the user's motive),
equal to the image's developed domains up to β; (iii) `mⱼ` applied rather
than substituted into, equal up to β. A reflexive wrapper `λ a. ih a` of the
image is `ih` by η. So `img(r) ps ms mins is t ≡ ρ ps (ms∘σ) mins′ is t` by
δ, β and η; the motives and minors of the other components are not used by
`ρ` (they vanish by β, design document §4.5).

## Canonicity
The output depends on the component's canonical recursor `ρ` and its motive
and minor order (read off the image), on Lean's minor types (the domains),
which are functions of the member's constructors and of the user's motives,
and on the arguments. Under a member reorder of the Lean block the same
component, the same constructors and the same user terms give the same term.
Against a *separate declaration* of the components the term differs where
Lean's separate `_sizeOf_N` goes through the instance (`sizeOf h`) and the
mutual one through the relocated recursor: that is O11a's question. O11a
runs before O2 (`Engine.passes`, with its scheduling edges, `O11a.lean`) and
gives the instance form when its side condition holds; where it declines on
the recursion of Lean's `sizeOf` family, O2's relocated form stays and O11a
records the decline with its cause (`O11a.declineCause?`, cause
`O11A-PENDING` in the twins' records).

The minor's constructor, type and binders are read with the split-minor
helpers (`Ix/AuxSource.lean`: `auxMotiveSigs`, `sourceCtorForMinor`,
`sourceMinorType`, `peelBinders`, `findSourceRecTarget`; Rust
`compile/aux_source.rs`), shared with O11a. They were the legacy call-site
surgery's and stayed when M6R slice 6 deleted it.

## Side condition and fallback
Decidable: `classify` gives `rec`; the block is split and has no collapsed
class; `img(r)` has a head shape; every Ix minor names a Lean minor; a Lean
minor that needs adaptation (a field recursive into another component) is one
the image wraps; every relocated occurrence is rewritten by the engine (it
declines otherwise); Lean's recursor has the standard telescope; O5 accepts
the levels; at least the full telescope is applied. Otherwise the baseline
(the inline image, developed), which is faithful.

## Non-canonical set and evidence
Against the separately declared components, where O11a declines:
`O11A-PENDING` (O11a's record).
Evidence: `Tests/Ix/Compile/Pass/O2Split.lean` (fires: a split block with a
cross field; declines: a bare occurrence); the library: the 7
`Linear.EqCnstr._sizeOf_N` (byte-identical with the switch-off output when
O2 fires).
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O5
public import Ix.AuxSource
public import Ix.AuxGen.ExprUtils
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.Compile.Canon (mkAppN getAppFnArgs)

/-- Strip leading λs, counting them. -/
def stripLamsCount : Expr → Nat → Expr × Nat
  | .lam _ _ b _ _, d => stripLamsCount b (d + 1)
  | e, d => (e, d)

/-- The Lean minor a wrapped Ix minor of an image is built from: the head
variable of its body, as a minor index (`arity` the image's λ count, `np nm
nmin` Lean's counts). -/
def wrappedMinorSrc (arity np nm nmin : Nat) (t : Expr) : Option Nat := do
  let (body, d) := stripLamsCount t 0
  let .bvar k _ := (getAppFnArgs body).1 | none
  if k < d then none
  let j := k - d
  if j ≥ arity then none
  let p := arity - 1 - j
  if p < np + nm || p ≥ np + nm + nmin then none
  return p - np - nm

/-- The relocated call for an IH binder over a field outside the component:
the Lean recursor of the field's type applied to the occurrence's telescope,
the field's indices and the field (under its own binders), rewritten by the
engine (`recur`). Mirrors the deleted legacy surgery's `synthesizeExternalIh`, with
the inner occurrence rewritten here instead of by a second surgery. -/
def relocatedIh (recur : Occ → Option Expr) (target : Ix.AuxGen.SourceRecTarget)
    (field : Expr) (all : Array Name) (us : Array Level)
    (ps ms mins : Array Expr) : Option Expr := do
  let some all0 := all[0]? | none
  let targetRec :=
    match all[target.sourcePos]? with
    | some x => Name.mkStr x "rec"
    | none => Name.mkStr all0 s!"rec_{target.sourcePos - all.size + 1}"
  let fieldApp := target.xsFvars.foldl Expr.mkApp field
  let inner ← recur { head := targetRec, us, args := ps ++ ms ++ mins ++ target.idxArgs ++ #[fieldApp] }
  return Ix.AuxGen.mkLambda inner target.xsDecls

/-- The adapted minor of Lean minor `j`: `some (some w)` for the wrapper,
`some none` when no field of its constructor is recursive into another
component (the minor is passed as it is), `none` on failure. -/
def adaptMinor (recur : Occ → Option Expr) (env : Ix.Environment) (rv : RecursorVal)
    (inBlock : Array Bool) (us : Array Level) (ps ms mins : Array Expr) (j : Nat) :
    Option (Option Expr) := do
  let initial := (Ix.AuxGen.FreshFVars.protectExpr {} rv.cnst.type).protectExprs (ps ++ ms ++ mins)
  let (auxSigs, supply) := (Ix.AuxGen.auxMotiveSigsWith rv us ps ms env).run initial
  let (_, ctor) ← Ix.AuxGen.sourceCtorForMinor j rv env auxSigs
  let minorTy ← Ix.AuxGen.sourceMinorType rv us ps ms mins j
  let (fields?, supply) :=
    (Ix.AuxGen.peelBindersWith minorTy ctor.numFields "split_field" 0).run supply
  let (fieldDecls, fieldFVars, afterFields) ← fields?
  let mut supply := supply
  let mut recFields : Array (Nat × Ix.AuxGen.SourceRecTarget) := #[]
  for (decl, fieldIdx) in fieldDecls.zipIdx do
    let (target?, nextSupply) := (Ix.AuxGen.findSourceRecTargetWith decl.domain rv.all
      ps env "split_xs" fieldIdx auxSigs).run supply
    supply := nextSupply
    if let some target := target? then
      recFields := recFields.push (fieldIdx, target)
  if !recFields.any (fun (_, t) => !(inBlock.getD t.sourcePos false)) then
    return none
  let (ihs?, _) :=
    (Ix.AuxGen.peelBindersWith afterFields recFields.size "split_ih" 0).run supply
  let (ihDecls, ihFVars, _) ← ihs?
  if ihDecls.size != recFields.size then none
  let mut decls := fieldDecls
  let m ← mins[j]?
  let mut body := fieldFVars.foldl Expr.mkApp m
  for ((fieldIdx, target), ihIdx) in recFields.zipIdx do
    if inBlock.getD target.sourcePos false then
      decls := decls.push ihDecls[ihIdx]!
      body := Expr.mkApp body ihFVars[ihIdx]!
    else
      let ih ← relocatedIh recur target fieldFVars[fieldIdx]! rv.all us ps ms mins
      body := Expr.mkApp body ih
  return some (Ix.AuxGen.mkLambda body decls)

def O2.apply (recur : Occ → Option Expr) (env : OptEnv) (o : Occ) :
    Option Expr := do
  let (k, r) ← classify o.head
  if k != .kRec then none
  let b ← env.blockOf o.head
  if !b.change.split || b.change.collapse then none
  let s ← b.shapes.get? r
  let some (.recInfo rv) := env.const? r | none
  let n ← standardTelescope env s .kRec o.head
  if o.args.size < n then none
  let ls ← O5.levels s o.us
  let a := o.args
  let ps := a.extract 0 s.np
  let ms := a.extract s.np (s.np + s.nm)
  let mins := a.extract (s.np + s.nm) (s.np + s.nm + s.nmin)
  let tail := a.extract (s.np + s.nm + s.nmin) n
  let inBlock : Array Bool := (Array.range s.nm).map s.motiveSrc.contains
  let ms' ← pick ms s.motiveSrc
  let mut mins' : Array Expr := #[]
  for (src?, t) in s.minorSrc.zip s.minorTerms do
    let j ← match src? with
      | some j => pure j
      | none => wrappedMinorSrc s.arity s.np s.nm s.nmin t
    match ← adaptMinor recur env.ienv rv inBlock o.us ps ms mins j with
    | some w =>
      -- the image relocates here too (it wraps this minor)
      if src?.isSome then none
      mins' := mins'.push w
    | none => mins' := mins'.push (← mins[j]?)
  return mkAppN (Expr.mkConst s.ixRec ls) (ps ++ ms' ++ mins' ++ tail ++ a.extract n a.size)

end Ix.Compile.Pass.Opt

end
