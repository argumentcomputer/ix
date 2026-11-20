import IxVMRefinement.Assembly.NativeBlockRetHeadIxon
import IxVMRefinement.Assembly.NativeBlockReadsLim

/-! # The constructors' literal return, from the store fact and the member check at either context

`blockCtorIxonRetHead_of_member` reads the constructors' literal return off the member check of
a block whose former is declared at its telescope, under a role context at a group limit. Its
last step uses only two things: the fact about the store that every constructor's raw image
returns literally (`BlockRawRetHead`), and a load of each constructor slot by the member check.

* `blockCtorIxonRetHead_of_raw`: that last step by itself, for a member check under the role
  context of either validator. The slot loads are the member check's
  (`ctorSlots_of_member_lim`). It serves any one-type block: the fact about the store is the
  only input that depends on how the former is declared. At a former declared at a definition
  it is a conclusion of `aliasOuts_of_member_traced`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency

/-- **The constructors of a one-type block return literally**, from the fact about the store
and the member check's load of each constructor slot (module docstring). -/
theorem blockCtorIxonRetHead_of_raw {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hR : BlockRawRetHead t E B ind cb) : BlockCtorIxonRetHead cb ind := by
  have hgood : Core.Good ⟨E, ⟨[]⟩, t, none⟩ calls := hst.good ⟨[]⟩ none
  obtain ⟨b, hbB, -, -, -, hslots⟩ := ctorSlots_of_member_lim hgood.2 hS hrec hchk
  intro j ct hct
  have hj : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  obtain ⟨bp, ptr, h, h', cs, nl, ty, pb, mi, sl, np, nf, us, ev, hsub, hrep, -, -, -, -⟩ :=
    hslots j hj
  rw [Nat.cast_zero] at ev
  have hg : Core.Good ⟨E, ⟨[]⟩, t, none⟩ cs := hgood.sub hsub
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb', hms', hct',
    -, hldv, raw⟩ := Ingress.get_ci_cprj_spec hg.2 hrep ev
  -- the block record the load decoded is `cb`
  have hblock : recordOf E (Core.ixAddr b) = some cb := by
    rw [hbB]
    exact hR.block
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbytes : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg.1 blkBytes hhB haB
  have hcbEq : cb = cb' := by
    rw [hbytes, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcbEq
  have hmsEq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hR.muts)
  subst hmsEq
  have hindEq : ind' = ind := by
    rw [ZMod.val_zero] at hms'
    have e : (some (.indc ind) : Option Ixon.MutConst) = some (.indc ind') := hms'
    exact (Ixon.MutConst.indc.inj (Option.some.inj e)).symm
  subst hindEq
  have hjval : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (Nat.lt_trans hj hR.size) (by decide))
  have hctEq : ct' = ct := by
    rw [hjval, Array.getElem?_toList] at hct'
    exact Option.some.inj (hct'.symm.trans hct)
  obtain ⟨-, -, -, -, -, tyPtr, blkPtr, b'', -, -, hv, hconv⟩ := raw
  rw [hctEq] at hconv
  subst hv
  obtain ⟨ct'', hct'', -, hret⟩ := hR.load ht hg.1 hg.2 hbB hj hrep ev hldv
  have hc2 : ct'' = ct := Option.some.inj (hct''.symm.trans hct)
  rw [hc2] at hret
  exact blockIxonRetHead_of_conv hconv hret

end IxVM.Refinement.Typing
