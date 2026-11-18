import IxVMRefinement.FamilyAlias.BlockRow

/-! # A member at a claimed family record's address is a recursor

`familyClaimRow : FamilyClaimRow`: a member of a block's declaration as read, at the key of a
constant address of a family record the run claims, is a recursor. The member is the reading of
one of the two records' constant addresses (`FamDeclReads`); the table's keying is injective, so
that address is the claimed record's; the record there is a recursor projection of the claimed
family record (`FamRecRecord.members`, from the graph's `famRecord`); and a reading of a
recursor projection record is a recursor (`isRecursor_of_reads_rPrj`). -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Ix.Kernel (ConstantInfo)
open IxVM.Refinement.Decl.FamilyAlias (isRecursor)

set_option linter.unusedVariables false

/-- **A reading of a recursor projection record is a recursor.** -/
theorem isRecursor_of_reads_rPrj {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {x : _root_.Address}
    {ci : ConstantInfo .anon} {c : Ixon.Constant} {p : Ixon.RecursorProj}
    (hr : Reads t E₀ x ci) (hc : recordOf E₀ x = some c) (hinfo : c.info = .rPrj p) :
    isRecursor ci = true := by
  obtain ⟨c', hc', hR⟩ := hr
  have e : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst e
  rw [hinfo] at hR
  obtain ⟨cb, ms, rc, -, hrr⟩ := hR
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, -, -, -, -, -, -, -, -, -, rfl⟩ :=
    hrr
  rfl

/-- **`hclaim` of the family row** (module docstring). -/
theorem familyClaimRow : FamilyClaimRow.{u} := by
  intro calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb crb rs
    hTop hc hlog hkind hfam hrb blk hreads B' rb' x crb' hfam' hcrb' hx ci hci hname
  obtain ⟨bAddr, hW, -⟩ := hTW
  have ht : t.check = .ok () := hW.check_ok
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci hci
  have hxy : y = x := IxVM.Refinement.Core.keyOf_inj htwf (hy.symm.trans hname)
  rw [hxy] at hry
  obtain ⟨crb'', rs', hF⟩ := hrun.graph.famRecord B' rb' hfam'
  have e : crb'' = crb' := Option.some.inj (hF.record.symm.trans hcrb')
  subst e
  rcases hx with ⟨-, hs⟩ | ⟨ms, i, m, hms, hm, hxm | ⟨ind, j, hind, -, -⟩⟩
  · exact (standalone_not_block hs ⟨rs', hF.muts⟩).elim
  · have hrs : rs' = ms := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hms)
    subst hrs
    obtain ⟨r, rfl⟩ := hF.recrs m (by simpa using Array.mem_of_getElem? hm)
    have hrec : recordOf E₀ x = some (memberProjection rb' i (.recr r)) := by
      rw [hxm]
      exact hF.members i _ hm
    exact isRecursor_of_reads_rPrj (p := ⟨i.toUInt64, rb'⟩) hry hrec rfl
  · have hrs : rs' = ms := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hms)
    subst hrs
    obtain ⟨r, hr⟩ := hF.recrs m (by simpa using Array.mem_of_getElem? hm)
    rw [hind] at hr
    exact nomatch hr

end IxVM.Refinement.Typing.FamilyAlias
