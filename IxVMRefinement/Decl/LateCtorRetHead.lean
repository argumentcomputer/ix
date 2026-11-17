import IxVMRefinement.Decl.LateNatCtorT
import IxVMRefinement.L1.Ingress

/-! # The literal return position of a family's constructors, as a fact about its block record

The native recursor comparison (`late_nat_rec_check_specT`) needs `NatCtorRetHeadT`: at every
`get_ci_cprj` load of a constructor of the parent's member, the loaded type's first
`nP + nF` binders are literal `Forall` cells ending in a literal application spine over a literal
`Const` cell. The recursor's own run does not check this (`nat_ctor` reads only the arguments of
the spine). The shape is what `check_ctor_return_type` asserts when the native block's step
admits the constructor, on that step's own load.

Every load converts the same Ixon expression (`L1.RawConvExpr`, which follows the record's
sharing table and maps `all`, `app`, `ref`/`recur` to `Forall`, `App`, `Const` cells), so the
shape is a fact about the block record: `CtorRetHeadAt cb ind` says that constructor `j`'s Ixon
type is, through the sharing table, `ind.params + fields` literal `all` binders and then an
application spine over a reference (`IxonRetHead`). `natCtorRetHeadT_of_ixon` turns it into
`NatCtorRetHeadT` at any good run. `FamCtorRetHead` states it at a registry entry: at the
member record the family's name is the key of.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

/-! ## The shape on the Ixon expression -/

/-- An Ixon expression that is, through the sharing table, an application spine over a
reference (`ref` or `recur`). -/
inductive IxonAppHeadRef (sharing : List Ixon.Expr) : Ixon.Expr → Prop
  | ref {i : UInt64} {us : Array UInt64} : IxonAppHeadRef sharing (.ref i us)
  | recur {i : UInt64} {us : Array UInt64} : IxonAppHeadRef sharing (.recur i us)
  | app {f a : Ixon.Expr} : IxonAppHeadRef sharing f → IxonAppHeadRef sharing (.app f a)
  | share {idx : UInt64} {s : Ixon.Expr} : sharing[idx.toNat]? = some s →
      IxonAppHeadRef sharing s → IxonAppHeadRef sharing (.share idx)

/-- An Ixon expression that is, through the sharing table, `n` literal `all` binders and then an
application spine over a reference. -/
inductive IxonRetHead (sharing : List Ixon.Expr) : Nat → Ixon.Expr → Prop
  | zero {e : Ixon.Expr} : IxonAppHeadRef sharing e → IxonRetHead sharing 0 e
  | all {n : Nat} {ty body : Ixon.Expr} : IxonRetHead sharing n body →
      IxonRetHead sharing (n + 1) (.all ty body)
  | share {n : Nat} {idx : UInt64} {s : Ixon.Expr} : sharing[idx.toNat]? = some s →
      IxonRetHead sharing n s → IxonRetHead sharing n (.share idx)

/-- **The constructors of member `ind` of the block record `cb` return literally**: the type of
each constructor `ct` of `ind` is, through `cb`'s sharing table, `ind.params + ct.fields` literal
binders and then an application spine over a reference. -/
def CtorRetHeadAt (cb : Ixon.Constant) (ind : Ixon.Inductive) : Prop :=
  ∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
    IxonRetHead cb.sharing.toList (ind.params.toNat + ct.fields.toNat) ct.typ

/-! ## The shape on every load -/

/-- A converted application spine over a reference is a literal application spine over a
literal `Const` cell. -/
theorem natAppHeadConstT_of_ixon {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    (he : IxonAppHeadRef sharing e) :
    ∀ {bound : Nat} {p : SourceValue F},
      L1.RawConvExpr refs recurAddrs univs sharing blobs h bound e p → NatAppHeadConstT h p := by
  induction he with
  | ref =>
    intro bound p raw
    cases raw with
    | ref _ _ _ _ _ _ cell => exact .const cell
  | recur =>
    intro bound p raw
    cases raw with
    | recur _ _ _ _ _ _ cell => exact .const cell
  | app _ ih =>
    intro bound p raw
    cases raw with
    | app rf _ cell => exact .app cell (ih rf)
  | share hs _ ih =>
    intro bound p raw
    cases raw with
    | share _ hsh rs =>
      rw [hs] at hsh
      cases hsh
      exact ih rs

/-- A converted `IxonRetHead` term is `n` literal `Forall` cells, then a literal application
spine over a literal `Const` cell. -/
theorem natRetHeadT_of_ixon {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {n : Nat} {e : Ixon.Expr}
    (he : IxonRetHead sharing n e) :
    ∀ {bound : Nat} {p : SourceValue F},
      L1.RawConvExpr refs recurAddrs univs sharing blobs h bound e p → NatRetHeadT h n p := by
  induction he with
  | zero ha =>
    intro bound p raw
    exact .zero (natAppHeadConstT_of_ixon ha raw)
  | all _ ih =>
    intro bound p raw
    cases raw with
    | all _ _ rb cell => exact .succ cell (ih rb)
  | share hs _ ih =>
    intro bound p raw
    cases raw with
    | share _ hsh rs =>
      rw [hs] at hsh
      cases hsh
      exact ih rs

/-- **`NatCtorRetHeadT` from the block record**: if the constructors of member `idx` of the
block record at `b₀` return literally (`CtorRetHeadAt`), then at every good `get_ci_cprj` load
the loaded type has the literal return shape. The field count of the load witness is the
record's (`hload`, under a bound). -/
theorem natCtorRetHeadT_of_ixon {c : Ctx} {b₀ : Bytes.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {ind : Ixon.Inductive} {idx k nP : Nat}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)} {x_block : SourceValue F}
    {cs : List (Call F)} {κ : _root_.Address → KKey}
    (hrecB : IxVM.Consistency.recordOf c.E (ixAddr b₀) = some cb)
    (hcb : cb.info = .muts ms) (hms : ms[idx]? = some (.indc ind))
    (hhead : CtorRetHeadAt cb ind) (hnP : nP = ind.params.toNat)
    (hidx : idx < 4294967296) (hlen : ctors_info.length < 4294967296)
    (hnf_lt : ∀ j info, ctors_info[j]? = some info → info.2.1 < 4294967296)
    (hload : NatCtorLoadT κ b₀ idx k ctors_info x_block cs)
    (hg : Good c cs) :
    NatCtorRetHeadT b₀ idx nP ctors_info x_block cs := by
  intro j hj p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hsub hb ev hld info hinfo
  have hg15 : Good c cs15 := hg.sub hsub
  obtain ⟨_, _, _, blkBytes, cb', ms', ind', ct, blobs, v, hhB, haB, hexB, _, hcb', hms', hct,
    _, hldv, raw⟩ := L1.get_ci_cprj_spec hg15.2 hb ev
  -- the block record the load decoded is `cb`
  unfold IxVM.Consistency.recordOf at hrecB
  cases hgetB : c.E.consts.get? (ixAddr b₀) with
  | none => rw [hgetB] at hrecB; cases hrecB
  | some lc =>
    rw [hgetB] at hrecB
    have hdec : Ixon.deConstantExact lc.rawBytes = .ok cb := by
      cases hd : Ixon.deConstantExact lc.rawBytes with
      | error e => rw [hd] at hrecB; cases hrecB
      | ok cb'' =>
        rw [hd] at hrecB
        cases hrecB
        rfl
    have hesc := load_escape hgetB hg15.1 blkBytes hhB haB
    rw [hesc, hdec] at hexB
    injection hexB with hcb_eq
    subst hcb_eq
    rw [hcb] at hcb'
    injection hcb' with hms_eq
    subst hms_eq
    have hidxv : ((idx : Nat) : F).val = idx :=
      ZMod.val_natCast_of_lt (Nat.lt_trans hidx (by decide))
    have hjv : ((j : Nat) : F).val = j :=
      ZMod.val_natCast_of_lt (Nat.lt_trans (Nat.lt_trans hj hlen) (by decide))
    rw [hidxv, Array.getElem?_toList, hms] at hms'
    injection hms' with hind_eq
    injection hind_eq with hind_eq
    subst hind_eq
    rw [hjv, Array.getElem?_toList] at hct
    -- the loaded value
    obtain ⟨_, _, _, hfl, _, tyPtr, blkPtr, b, _, _, hv, hraw⟩ := raw
    have hld0 := hld
    rw [hldv, hv] at hld
    injection hld with hld
    injection hld with _ _ hargs
    injection hargs with _ hargs
    injection hargs with htyEq hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hnfEq _
    -- the field count of the load witness is the record's
    obtain ⟨-, hxnf, -⟩ := hload j hj p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hsub hb ev
      hld0 info hinfo
    subst htyEq
    have hnf : info.2.1 = ct.fields.toNat := by
      rw [← hnfEq] at hxnf
      have h' := congrArg ZMod.val (Value.field.inj hxnf)
      rwa [ZMod.val_natCast_of_lt (Nat.lt_trans hfl (by decide)),
        ZMod.val_natCast_of_lt (Nat.lt_trans (hnf_lt j info hinfo) (by decide)), eq_comm] at h'
    rw [hnP, hnf]
    exact natRetHeadT_of_ixon (hhead j ct hct) hraw

end IxVM.Refinement.Decl
