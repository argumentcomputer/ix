import IxCC.Rt.Rc.Proof.RecycleStep
import IxCC.Rt.Rc.Proof.ObjectFrame

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof

/-- The two actual recycle stores preserve every surviving live cell. Store
separation follows from pending/live slot kinds and context/object separation. -/
theorem ReleaseInvariant.recycle_live
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor) (oldHead : Word) :
    HeapLive heap addresses (recycleParent mem context (UInt64.ofNat parent.cls) parent.address oldHead) := by
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  have hcls : 1 ≤ parent.cls ∧ parent.cls ≤ 32 := ⟨vp.1, vp.2.1⟩
  have hparent : parent.address.toNat+8 ≤ 2^64 := by omega
  have hhead := h.head_fit parent.cls hcls.1 hcls.2
  refine { h.live with cell := ?_ }
  intro loc refs mode body hc
  obtain ⟨hmode, addr, haddr, hcell⟩ := h.live.cell loc refs mode body hc
  subst mode
  obtain ⟨slot, hm, hkind⟩ := h.partition.placed loc refs body hc
  obtain ⟨refs', body', hc', haddr', hclass⟩ := h.partition.live slot hm loc hkind
  rw [hc] at hc'
  have eqs : refs = refs' ∧ body = body' := by simpa using hc'
  have hbody : body' = body := eqs.2.symm
  subst body'
  have had : slot.address = addr := by
    rw [haddr] at haddr'
    exact (Option.some.inj haddr').symm
  have hne : slot ≠ parent := by
    intro he
    subst slot
    rw [hk] at hkind
    cases hkind
  have hd := h.partition.disjoint_members hm hp hne
  have vs := h.partition.valid slot hm
  have hctx := h.head_disjoint parent.cls hcls.1 hcls.2 slot hm
  rw [had, hclass] at hd vs hctx
  have hfit : addr.toNat+cellBytes body.fields.length ≤ 2^64 := by
    have hf := hcell.fit
    omega
  have hs : addr.toNat+cellBytes body.fields.length ≤ parent.address.toNat ∨
      parent.address.toNat+8 ≤ addr.toNat := by
    simp only [cellBytes, smallClass] at *
    rcases hd with hd | hd <;> omega
  have hh : addr.toNat+cellBytes body.fields.length ≤
      (freeHeadAddress context (UInt64.ofNat parent.cls)).toNat ∨
      (freeHeadAddress context (UInt64.ofNat parent.cls)).toNat+8 ≤ addr.toNat := by
    simp only [cellBytes, smallClass] at *
    simpa only [Nat.add_comm] using hctx.symm
  refine ⟨rfl, addr, haddr, ?_⟩
  apply hcell.frame
  exact (objectFrame_write mem addr parent.address oldHead _ .w64 hfit hparent hs).trans
    (objectFrame_write (mem.write .w64 parent.address oldHead) addr
      (freeHeadAddress context (UInt64.ofNat parent.cls)) parent.address _ .w64 hfit hhead hh)



/-- A composed real block9 path: obtain loads and write permissions from the
loop invariant, execute its charged edge, and preserve live cells, the region
partition, and the changed class chain. Remaining-cursor/head-table framing
is still required before this becomes a complete invariant transition. -/
theorem ReleaseInvariant.finished_parent_step
    {heap addresses mem external frame tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external none (frame :: tail)
      context base bump limit slots lists)
    (hfinished : frame.visited = frame.original.fields.length)
    (env : Env) (ha : env[8]? = some frame.address)
    (hc : env[10]? = some (UInt64.ofNat (smallClass frame.original.fields.length))) :
    ∃ parent ∈ slots,
      let cls := UInt64.ofNat parent.cls
      let newMem := recycleParent mem context cls parent.address ((lists parent.cls).headD 0)
      Sem.Star (semStep releaseProgram) (releaseState mem context env 9 0) 1
        (releaseState newMem context
          (((env.insert 15 (cursorHead tail)).insert 16 ((lists parent.cls).headD 0)).insert 8
            (cursorHead tail)) 6 0) ∧
      HeapLive heap addresses newMem ∧
      ArenaPartition heap addresses base bump limit (recycleSlots parent.address slots) ∧
      FreeChain newMem (parent.address :: lists parent.cls) ∧
      Balance heap external (cursorTokens tail) := by
  obtain ⟨parent, hp, haddr, hcls, hkind⟩ := h.cursors_placed [] frame tail (by rfl)
  have hcursor := h.cursors.2.1
  have vp := h.partition.valid parent hp
  have hread : ∀ j < 8, mem.readable (parent.address+UInt64.ofNat j) = true := by
    intro j hj
    rw [haddr]
    apply (h.cursor_access frame (by simp) j ?_).1
    have := hcursor.visited_positive
    have := hcursor.visited_le
    simp only [cellBytes]
    omega
  have hwrite : ∀ j < 8, mem.writable (parent.address+UInt64.ofNat j) = true := by
    intro j hj
    rw [haddr]
    apply (h.cursor_access frame (by simp) j ?_).2
    have := hcursor.visited_positive
    have := hcursor.visited_le
    simp only [cellBytes]
    omega
  have hpred : loadWord mem .w64 .zero (parent.address+8) = some (cursorHead tail) := by
    rw [haddr]
    simp only [loadWord, hcursor.link.read64]
  have hhead := h.free_heads parent.cls vp.1 vp.2.1
  have hload : loadWord mem .w64 .zero (freeHeadAddress context (UInt64.ofNat parent.cls)) =
      some ((lists parent.cls).headD 0) := by
    simp only [loadWord, hhead.read64]
  have hrun := finished_parent_recycle mem context (UInt64.ofNat parent.cls) parent.address
    (cursorHead tail) ((lists parent.cls).headD 0) env (by simpa only [haddr] using ha)
    (by simpa only [hcls] using hc) hpred hload hwrite
    (h.head_writable parent.cls vp.1 vp.2.1)
  have hchain := h.recycle_chain hp hkind hread
  refine ⟨parent, hp, hrun, h.recycle_live hp hkind _, hchain.2, hchain.1, ?_⟩
  simpa [cursorTokens, CursorFrame.suffix, flattenPending, hfinished] using h.balance


end IxCC.Rt.Rc.Procs
