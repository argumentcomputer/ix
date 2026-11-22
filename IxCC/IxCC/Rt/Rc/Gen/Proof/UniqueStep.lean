import IxCC.Rt.Rc.Gen.Proof.DetachInvariant
import IxCC.Rt.Rc.Gen.Proof.UniqueDispatch

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ReleaseInvariant.unique_step
    {heap addresses mem external location frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external (some (.loc location)) frames
      context base bump limit slots lists)
    {body address} (hc : heap.cell? location = some (.live 1 .dyn body))
    (ha : addresses location = some address) (hn : 0 < body.ctor.nobj) {child suffix}
    (hfields : body.fields = child :: suffix) (env : Env)
    (h1 : env[1]? = some address) (h2 : env[2]? = some (cursorHead frames)) :
    ∃ parent ∈ slots, ∃ childWord,
      valueWord addresses child = some childWord ∧
      Sem.Star (semStep releaseProgram) (releaseState mem context env 1 0) 1
        (releaseState (detachParent mem address (cursorHead frames) body.ctor.nobj) context
          (((detachEnv (env.insert 3 0) body.ctor.nobj childWord).insert 1 childWord).insert 2 address) 1 0) ∧
      ReleaseInvariant cmax (setCell heap location .dead) addresses
        (detachParent mem address (cursorHead frames) body.ctor.nobj)
        external (some child) (detachFrame location address body mem :: frames)
        context base bump limit
        (advanceSlots parent.address location suffix (cursorHead frames) slots) lists := by
  obtain ⟨_, a, ham, cell⟩ := h.live.cell location 1 .dyn body hc
  have hae : a = address := by rw [ha] at ham; exact (Option.some.inj ham).symm
  subst a
  obtain ⟨parent, hp, hi⟩ := h.detach_complete hc ha hn hfields
  obtain ⟨word, hv, hw⟩ := cell.first_child hn (child := child) (by simp [hfields])
  have hwlink : ∀ j < 8, mem.writable ((address+8)+UInt64.ofNat j) = true := by
    intro j hj
    have hr := cell.writable (8+j) (by have := cell.bytes; omega)
    have he : (address+8)+UInt64.ofNat j = address+UInt64.ofNat (8+j) := by
      rw [UInt64.ofNat_add]; simp [UInt64.add_assoc]
    simpa only [he] using hr
  have hwcount : ∀ j < 4, mem.writable ((address+4)+UInt64.ofNat j) = true := cell.count_writable
  have hr1 : (env.insert 3 0)[1]? = some address := by
    simp only [Std.HashMap.getElem?_insert]
    exact h1
  have hr2 : (env.insert 3 0)[2]? = some (cursorHead frames) := by
    simp only [Std.HashMap.getElem?_insert]
    exact h2
  refine ⟨parent, hp, word, hv, ?_, hi⟩
  have hs := unique_detach mem context address (cursorHead frames) word (env.insert 3 0)
    body.ctor.nobj hn (classOf_lt cell.layout).2.1 hr1 hr2 cell.scan_load hw hwlink hwcount
  simpa using (cell.unique_dispatch context env h1).trans hs


end IxCC.Rt.Rc.Gen
