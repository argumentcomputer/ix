import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Rt.Rc.Proof.Readback.View

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc.Procs

variable {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
  {origin : Own.Heap} {originAddresses : AddressMap} {external : Nat → Nat}
  {context base limit : Lir.Word} {regionBytes : Nat} {logical : Fir.Val}

/-- Execute the actual outermost return, using the exact memory produced by
the physical code. This closes a finite code trace without a new ABI premise. -/
theorem Returned.finish
    (returned : Returned P pairs lp origin originAddresses external context base limit regionBytes logical)
    {initial : Lir.State} {cost : Nat}
    (trace : Sem.Star (Lir.semStep lp) initial cost
      {mem := returned.memory, ctx := context, stack := [returned.frame]}) :
    Sem.Reaches (Lir.semStep lp) initial cost (.ok ([returned.word], returned.memory)) := by
  have final := Lir.semStep_done.2 (return_final returned.terminator returned.memory context)
  exact .of_final trace (final ▸ .done) (Nat.le_refl _)

/-- Result typing and constructor provenance come from the retained source
value relation and the actual accepted tree view. Heap layout, acyclicity,
fuel sufficiency and represented result are supplied by the returned state. -/
theorem Returned.observe
    (returned : Returned P pairs lp origin originAddresses external context base limit regionBytes logical)
    {A : Anf.Program} {signature : Rt.Sig} {type : Rt.FoTy} {anfValue : Anf.Val}
    {source target : Sem.Obs} (related : Fir.Proof.VR A anfValue logical)
    (observed : Fir.obsV logical = some source)
    (viewed : Readback.treeView A.ctors signature type source = some target) :
    Rt.readback signature (regionBytes / 8) returned.memory type returned.word = some target :=
  Readback.viewed_readback_region related observed viewed
    returned.state.ready.idle.live returned.state.ready.idle.partition
    returned.state.ordered returned.state.extent returned.den returned.represented



end IxCC.Cfg.Rc.Native.Spec
