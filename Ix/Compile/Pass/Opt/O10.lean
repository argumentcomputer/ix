/- # O10: structural recursion over a collapsed block with equal arms (the twin's single function)

## Contract
Input: an occurrence `x.brecOn.{u,us} ps ms is t Fs e` over a collapsed,
unsplit block `b` (`Opt.CollapseRec`) in the value of a definition `c`
(`Occ.site`): structural recursion `fᵢ := λ t. Mᵢ.brecOn ms t F⃗` over the
block, one handler per member (`Fᵢ = fᵢ._f`). Ix slot `k` packs the
members `C_k` (Pass 1's class, read off the image).

Output, when for every slot `k` the motives `m_i` (`i ∈ C_k`) agree after
compilation and the handlers `F_i` (`i ∈ C_k`), **re-typed** (every Lean
`M.below ps ms is s` replaced by `ρ_M.below ps P⃗ is s`, `P_k := m_{rep_k}`,
`rep_k` the first member of `C_k`), agree after compilation
(`agreeAddr`):

    ρ_x.brecOn.{u,us} ps P⃗ is t F⃗′ e

with `ρ_x.brecOn` the Ix `brecOn` of `x`'s slot and `F′_k` the re-typed
handler of `rep_k`: the canonical constant `p._ix.s` for a constant
handler `p.s` (emitted with the block), the re-typed term otherwise. Every
member function of a slot (`A.h`, `B.k`) becomes the same term: the twin's
single function `X.h := λ t. X.brecOn P t X.h._f`. A collapse keeps every
field, so the below layouts agree leaf for leaf and no path changes.

## Faithfulness (proof-justified; the statement Phase B formalises)
Write `B_i t := M_i.brecOn ps ms is t F⃗` (Lean's, over the images, Def 3.5)
and `B′_k t := ρ_k.brecOn ps P⃗ is t F⃗′` (the Ix `brecOn` of slot `k`).
**Lemma O10.** Under the side condition, for every slot `k`, `i ∈ C_k`,
`is`, `t : T_k ps is`: `B_i is t = B′_k is t` (in `P_k is t = m_i is t`).

*Proof*, by simultaneous induction on `t` with `ρ` (all slots), at the Prop
motives `Q_k := λ is t. ∀ i ∈ C_k, B_i is t = B′_k is t` — the induction of
O7, with both `brecOn` equation lemmas (Lean's `Mᵢ.brecOn.eq`, Pass 2's
`ρ_k.brecOn.eq`): `B_i t = F_i t (L_i t)` and `B′_k t = F′_k t (L′_k t)`,
`L`, `L′` the below values. Case `t = c fs`: `L_i (c fs)` is the tuple of
leaves `⟨B_j f, L_j f⟩` (one per field `f` of member `j`'s type), `L′_k (c fs)`
the tuple `⟨B′_{slot j} f, L′ f⟩` with the same shape (same fields). By the
induction hypotheses `B_j f = B′_{slot j} f`, and the nested below values
are related the same way (induction on the leaf's structure, the same
lemma at the field), so `L_i (c fs)` and `L′_k (c fs)` are equal after
re-typing; `F_i` and `F′_k` agree after compilation (side condition: the
re-typed `F_i` *is* `F′_k` in `E`), so `F_i t (L_i t) = F′_k t (L′_k t)` by
`congrArg`. ∎ The baseline occurrence is `img(x.brecOn) a⃗ ≡δβ B_x t e`; the
output is `B′_{slot x} t e`. **Corollary**: the rewritten `c` equals
`base(c)` by `funext` and `congrArg`. The canonical handler is `F_{rep}`
re-typed (a new constant); Lean's `fᵢ._f` keep their Lean names and types.

**Where the output goes (decision 5, D1).** The output is written into the
canonical form `fᵢ._ix` of each member function (Lean's `fᵢ` renamed, with
its type): every member function of a slot gets the same `_ix` term; the
Lean names `fᵢ` keep their baselines (the image's `brecOn`, convertible to
Lean's term) and are recorded non-canonical with the cause O10. The proof
term of `fᵢ._ix = fᵢ` is the Corollary (`funext`, `congrArg` with Lemma O10,
the simultaneous induction with `ρ` and both `brecOn` equation lemmas); not
convertible at open terms, equal by ι at closed ones. The handlers'
comparison reads the canonical forms of the handlers' references (a
matcher's `_ix` form, `OptEnv.canonAddrOf`), never a caller.

## Canonicity
For the canonical twin (one member per class) Lean elaborates the single
function to `ρ.brecOn P⃗ t X.h._f` with `X.h._f`'s body the members'
common body over the Ix below: the output is the twin's term, depending on
the classes, the images and the arguments (agreeing members give the same
bytes whichever is `rep_k`).

## Side condition and fallback
Decidable: `readCollapseRec` (collapsed, unsplit, no nesting, packed image,
standard telescope, `m ≥ n`); for every slot the motives agree
(`agreeAfterCompile`) and the re-typed handlers agree (`agreeAddr`); every
constructor field is a member or does not mention the block; the Ix
`brecOn` and `below`s resolve; `singleLevels` accepts the levels;
`pjAllowed` (the value of a definition). Otherwise no `_ix` form is
emitted for the occurrence (O12 handles one slot with different arms).

## Non-canonical set and evidence
The Lean names `fᵢ` (cause O10; canonical form `fᵢ._ix`). Lean's `fᵢ._f`
keep their Lean types over Lean's `below` (faithful; their canonical
counterpart is `rep._ix._f`). Evidence:
`Tests/Ix/Compile/Pass/O10O12Collapse.lean` (C5's `A.h`/`B.k`, C8's
`A.h`/`B.h`/`C.h` with a lifted member: the `_ix` forms byte-equal to the
twins with the switch on, the Lean names recorded; value pins). Library load 0.
-/
module
public import Ix.Compile.Pass.Opt.CollapseRec
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (mkAppN)

def O10.apply (env : OptEnv) (o : Occ) : Option (Expr × Array ConstantInfo) := do
  let cr ← readCollapseRec env o
  let s := cr.s
  let ren := collapseRenaming env cr.b
  let addr? := env.canonAddrOf
  -- the motives agree per slot
  let mut ps' : Array Expr := #[]
  for cls in s.slots do
    let rep ← cls[0]?
    let mr ← cr.ms[rep]?
    for i in cls do
      if !agreeAfterCompile ren (← cr.ms[i]?) mr then none
    ps' := ps'.push mr
  let ls ← singleLevels env s o.us
  let rt ← cr.retype env ps' (singleLevels env s) none
  -- the re-typed handlers agree per slot
  let mut hs' : Array Expr := #[]
  let mut canon : Array ConstantInfo := #[]
  for cls in s.slots do
    let rep ← cls[0]?
    let (hr, cr') ← retypeHandler env rt (← cr.hs[rep]?)
    let vr := (cr'[0]?.bind fun c => match c with | .defnInfo d => some d.value | _ => none).getD hr
    for i in cls do
      if i == rep then continue
      let (hi, ci) ← retypeHandler env rt (← cr.hs[i]?)
      let vi := (ci[0]?.bind fun c => match c with | .defnInfo d => some d.value | _ => none).getD hi
      if !agreeAddr ren addr? vi vr then none
    hs' := hs'.push hr
    canon := canon ++ cr'
  let ixBRecOn ← ixAuxOf s.ixRec .kBRecOn
  if !env.resolves ixBRecOn then none
  if !pjAllowed o then none
  return (mkAppN (Expr.mkConst ixBRecOn ls) (cr.ps ++ ps' ++ cr.tail ++ hs' ++ cr.rest), canon)

end Ix.Compile.Pass.Opt

end
