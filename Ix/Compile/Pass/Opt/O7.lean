/- # O7: `rec`/`recOn` over a collapsed block with identical motives and minors per class

## Contract
Input: an occurrence `r.{u,us} ps ms mins is t e` of a Lean recursor
`r = x.rec` (or `x.recOn.{u,us} ps ms is t mins e`) in the value of a
definition `c` (`Occ.site`), where `x` is a member of a changed block `b`
that is **collapsed and not split**: one component, some class of two or
more members, no nested auxiliary, no evaporation (Pass 1). The image of
`r` is packed (`Opt.Packed`): `img(r) = λ ps ms mins is t. unwrap_p
(ρ.{ℓ} ps M⃗ N⃗ is t)` with Ix slot `k` packing the Lean motives `C_k` (Lean
order). Lean's minors are member by member (`all` order), constructor by
constructor; Ix slot `k`'s constructors are those of any member of `C_k`,
by position (members of a class are structurally equal).

Output, when for every slot `k` the user's motives `m_i` (`i ∈ C_k`) agree
after compilation (`agreeAfterCompile`: α-equal under the collapse
renaming), and for every constructor position `q` so do the user's minors
`min_{i,q}` (`i ∈ C_k`), with `rep_k` the first member of `C_k`:

    ρ.{u,us} ps (m_{rep_k})_k (min_{rep_k, q})_{k,q} is t e

(`recOn`: the Ix `recOn` of the class, `ps (m_{rep_k})_k is t
(min_{rep_k,q})_{k,q} e`), at Lean's motive universe `u`
(`singleLevels`). The duplicates are dropped: `X.rec P mins x`.

## Faithfulness (proof-justified; the statement Phase B formalises)
Fix the occurrence's arguments and write `P_k := m_{rep_k}`, `N′` for the
Ix minors of the output (`N′_{k,q} := min_{rep_k,q}`), `S t := ρ.{u} ps P⃗ N⃗′
is t` (the output) and `D t := ρ.{ℓ} ps M⃗ N⃗ is t` (the packed recursion
inside the baseline, `M⃗, N⃗` the image's motives and minors at the
arguments). **Lemma O7** (the old plan's `(pairRec P P mins mins x).1 =
X.rec P mins x`, for any number of slots and class sizes). Under the side
condition, for every slot `k`, position `p` of `C_k`, indices `is` and
`t : T_k ps is`:

    unwrap_p (D t) = S t                                   (in `P_k is t`)

*Proof*, by induction on `t` with `ρ` itself (all slots at once), at the
Prop motives `Q_k := λ is t. ∀ p < |C_k|, unwrap_p (D t) = S t`. Case
`t = c_q fs` of slot `k` (fields `fs`, hypotheses `ih_f : Q_{k_f} … f` for
the recursive fields `f`, of slot `k_f`):
* `unwrap_p (D (c_q fs))` →ι `unwrap_p (N_{k,q} fs (D f)⃗)` →β,proj
  `min_{i_p,q} fs (unwrap_{p_f} (D f))⃗` (§4.2 step 4: the component of the
  packed minor for member `i_p`, each Lean hypothesis the projection of the
  Ix one at the position `p_f` of the field's Lean motive in its slot);
* `S (c_q fs)` →ι `min_{rep_k,q} fs (S f)⃗`.
By the side condition `min_{i_p,q}` and `min_{rep_k,q}` agree after
compilation (they *are* one term of `E`: the renaming is what compilation
does to the block's names), and by `ih_f` each `unwrap_{p_f} (D f) = S f`.
So the case closes by `congrArg (min_{rep_k,q} fs) ih⃗` (one `congr` per
hypothesis). The motives agree, `m_{i_p} = P_k`, by the side condition, so
both sides have type `P_k is (c_q fs)`. The one-component, no-nesting
condition makes every Lean hypothesis an Ix hypothesis of the same field
(no relocated call), so the arities match. ∎

The baseline occurrence is `img(r) a⃗ ≡δβ unwrap_{pos(x)} (D t) e`, so by
Lemma O7 at `x`'s slot, `img(r) a⃗ = S t e` (congruence for `e`). For
`recOn`: `img(r.recOn) ≡δβ img(r)` with the arguments reordered (Def 3.5)
and `ρ.recOn ≡δβ ρ` likewise. **Corollary** (the rewritten constant): `c =
base(c)` by `funext` and `congrArg`, as for O8.

**Dependents.** As O8: the dependents rule (`pjAllowed`). Closed values
still compute (`D` and `S` agree by ι on constructors, which is what the
value pins check).

## Canonicity
For the canonical twin (one member per class) the user writes `X.rec P mins
t` with `P`, `mins` the same terms up to the renaming: the output is the
twin's term. It depends on the slot classes (read off the image:
canonical), `ρ` (canonical block) and the arguments; which member of a class
supplies `P_k` and `min_{k,q}` does not matter, they agree after
compilation (same bytes).

## Side condition and fallback
Decidable: `classify` gives `rec`/`recOn`; `b` collapsed, not split, no
evaporation, Lean's recursor has one motive per member (no nested
auxiliary); the image reads as packed and its slot classes partition Lean's
motives; Lean's auxiliary has the recursor's universe parameters and the
standard telescope; the member constructor counts give Lean's minor count
and the Ix minor count; `m ≥ n`; the motives and minors agree per class
after compilation; `singleLevels` accepts the levels; for `recOn` the Ix
`recOn` resolves; `pjAllowed`. Otherwise the baseline (the faithful paired
image).

## Non-canonical set and evidence
Distinct motives or minors in a class (the user distinguishes members a
collapse identifies, `SurgCollapse.f`): the baseline, faithful only; the
pair-valued form is O12's. Evidence: `Tests/Ix/Compile/Pass/O7Collapse.lean`
(identical arguments over a collapsed pair, over a collapsed class next to
a lifted member, `recOn`; distinct arguments decline; twin pairs byte-equal
with the switch on; value pins by `rfl`). Library load 0.
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.Packed
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (mkAppN)

def O7.apply (env : OptEnv) (o : Occ) : Option Expr := do
  let (k, r) ← classify o.head
  if k != .kRec && k != .kRecOn then none
  let b ← env.blockOf o.head
  let ch := b.change
  if !ch.collapse || ch.split || ch.evaporation then none
  let some (.recInfo rv) := env.const? r | none
  if rv.numMotives != b.all.size then none
  let s ← b.packed? env r
  -- the slot classes partition Lean's motives
  let flat := s.slots.foldl (· ++ ·) #[]
  if flat.size != s.nm || (List.range s.nm).any (!flat.contains ·) then none
  let ci ← env.const? o.head
  if ci.getCnst.levelParams != s.levelParams then none
  let n := s.arity
  if forallArity ci.getCnst.type != n then none
  if o.args.size < n then none
  -- Lean's minors, member by member
  let counts ← b.all.mapM fun m => match env.const? m with
    | some (.inductInfo iv) => some iv.ctors.size
    | _ => none
  if counts.foldl (· + ·) 0 != s.nmin then none
  let offsets : Array Nat := counts.foldl (fun acc c => acc.push (acc.back?.getD 0 + c)) #[0]
  let a := o.args
  let ps := a.extract 0 s.np
  let ms := a.extract s.np (s.np + s.nm)
  let (mins, tail) := if k == .kRec then
      (a.extract (s.np + s.nm) (s.np + s.nm + s.nmin), a.extract (s.np + s.nm + s.nmin) n)
    else (a.extract (s.np + s.nm + s.ni + 1) n, a.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1))
  let extra := a.extract n a.size
  let ren := collapseRenaming env b
  let mut ms' : Array Expr := #[]
  let mut mins' : Array Expr := #[]
  for cls in s.slots do
    let rep ← cls[0]?
    let mr ← ms[rep]?
    let nc ← counts[rep]?
    for i in cls do
      let mi ← ms[i]?
      if !agreeAfterCompile ren mi mr then none
      if counts[i]? != some nc then none
    for q in [0:nc] do
      let vr ← mins[offsets[rep]! + q]?
      for i in cls do
        let vi ← mins[offsets[i]! + q]?
        if !agreeAfterCompile ren vi vr then none
      mins' := mins'.push vr
    ms' := ms'.push mr
  if mins'.size != s.ixMinors then none
  let ls ← singleLevels env s o.us
  if !pjAllowed env b o then none
  if k == .kRec then
    return mkAppN (Expr.mkConst s.ixRec ls) (ps ++ ms' ++ mins' ++ tail ++ extra)
  else
    let ixRecOn ← ixAuxOf s.ixRec .kRecOn
    if !env.resolves ixRecOn then none
    return mkAppN (Expr.mkConst ixRecOn ls) (ps ++ ms' ++ tail ++ mins' ++ extra)

end Ix.Compile.Pass.Opt

end
