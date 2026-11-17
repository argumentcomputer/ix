import IxVMRefinement.Core.CallScope
import IxVMRefinement.Obs.KernelCheck
/-! # The peer recursor of a standalone recursor record

`KernelCheck::nat_rec_check` names the recursor its generated rules apply by
`find_peer_recursor_with_spec(rec_block, parent, [], 0, addr)`, with `rec_block` the block field
of the loaded recursor. For a recursor record that is not a block member, the loader sets that
field to the record's own address; the record there is a recursor, not a block, so the search
answers `addr`, the recursor itself. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

/-- **At a record that is a recursor, the peer search answers the recursor's own address.** -/
theorem find_peer_standalone_spec {c : ScopedCtx} (hlf : ScopedLoadFacts c)
    {cst : Ixon.Constant} {rc : Ixon.Recursor} {b : Bytes.Address}
    {x_block x_t x_sp x_aux x_self r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrec_at : Ix.Cert.recordAt c.E (ixAddr b) = some cst) (hcst : cst.info = .recr rc)
    (hgood : Good c.toCtx cs) (hb : Bytes.RepAddressRef addrTy h b x_block)
    (ev : ObsFn W "KernelCheck::find_peer_recursor_with_spec"
      [x_block, x_t, x_sp, x_aux, x_self] h r h' cs) :
    r = x_self ∧ Heap.Extends h h' := by
  match Obs.«KernelCheck::find_peer_recursor_with_spec».obs ev with
  | .other (ev14 := ev_ld) (he164 := hr) (he165 := hh) .. =>
    subst hr hh
    exact ⟨rfl, ev_ld.heap_extends⟩
  | .Muts (cs12 := cs12) (ev14 := ev_ld) (hc158 := hc_cs) .. =>
    subst hc_cs
    have hgood_ld : Good c.toCtx cs12 := hgood.sub (fun x hx => by simp [hx])
    have hshape := hlf.recordShape _ _ _ _ cs12 b cst ev_ld hgood_ld hb hrec_at
    rcases hshape with ⟨info_v, sh, rf, un, bd, hv_mk, hinfo⟩
    injection hv_mk with _ _ hv_args
    injection hv_args with hinfo_eq _
    subst hinfo_eq
    rw [hcst] at hinfo
    rcases hinfo with ⟨x, hx⟩
    injection hx with _ hname _
    have hname' : ("Muts" : String) = "Recr" := hname
    exact absurd hname' (by decide)

end IxVM.Refinement.Decl
