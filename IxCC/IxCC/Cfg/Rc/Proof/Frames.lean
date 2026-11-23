import IxCC.Cfg.Rc.Proof.Coverage
import IxCC.Cfg.Rc.Proof.Lower
import IxCC.Cfg.Proof.Sim

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Cfg.Proof (Impl spine)

/-- Existing layout witnesses place the actual marker in the complete checked
instruction inventory, even after arbitrary earlier bindings in the block. -/
theorem impl_marker_member {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {a : Action} {k : Own.Plain.Code} {ctors : List Lam.CtorInfo} {slotBase : Nat}
    (h : Impl fd.block? self J cur params acc next (skeleton limit first (.act a k) ctors slotBase)) :
    marker limit first a ∈ instructions fd := by
  obtain ⟨term, hb⟩ := Cfg.Proof.impl_head h
  apply List.mem_flatMap.mpr
  refine ⟨_, List.mem_of_getElem? hb, ?_⟩
  simp [spine, skeleton, markerRhs_eq]

/-- The checked complete function table and actual block layout derive the
action lookup. No caller-supplied per-marker interpretation is assumed. -/
theorem checked_frame_action {P : Program} {fd : Cfg.Fun} {fr : Frame}
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap} {first lower next : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {a : Action} {k : Own.Plain.Code} {table : ActionTable}
    {ctors : List Lam.CtorInfo} {slotBase : Nat}
    (layout : Impl fd.block? fr.fn J fr.blk params acc next
      (skeleton P.base.size first (.act a k) ctors slotBase))
    (cursor : fr.rest = spine (skeleton P.base.size first (.act a k) ctors slotBase))
    (checked : checkFunction P.base.size lower fd table = true)
    (tableLookup : P.actions.get? fr.fn = some table)
    (effect : Own.Plain.evalAction fr.env H a = .ok H') :
    step P (.run fr stk H) =
      .next (.run { fr with rest := spine (skeleton P.base.size (first + 1) k ctors slotBase) } stk H') false := by
  have member := impl_marker_member layout
  obtain ⟨slot, action, decoded, _, found⟩ := collect_member
    ((checkMarkers_iff ..).mp checked) member (reserved_marker ..)
  simp only [decode_marker, Option.some.injEq, Prod.mk.injEq] at decoded
  rcases decoded with ⟨rfl, rfl⟩
  apply step_action_success ?_ tableLookup found effect
  simpa only [skeleton, spine, markerRhs_eq] using cursor

theorem impl_after_action {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {a : Action} {k : Own.Plain.Code} {ctors : List Lam.CtorInfo} {slotBase : Nat}
    (h : Impl fd.block? self J cur params acc next (skeleton limit first (.act a k) ctors slotBase)) :
    Impl fd.block? self J cur params (marker limit first a :: acc) next
      (skeleton limit (first + 1) k ctors slotBase) := by
  simpa only [skeleton, Impl, markerRhs_eq] using h

theorem impl_dropSlot_member {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {s : Nat} {k : Own.Plain.Code} {ctors : List Lam.CtorInfo} {slotBase : Nat}
    (h : Impl fd.block? self J cur params acc next (skeleton limit first (.dropSlot s k) ctors slotBase)) :
    marker limit first (.dec (slotBase + s)) ∈ instructions fd := by
  obtain ⟨term, hb⟩ := Cfg.Proof.impl_head h
  apply List.mem_flatMap.mpr
  refine ⟨_, List.mem_of_getElem? hb, ?_⟩
  simp [spine, skeleton, markerRhs_eq]

theorem checked_frame_dropSlot {P : Program} {fd : Cfg.Fun} {fr : Frame}
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap} {first lower next : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {s : Nat} {k : Own.Plain.Code} {table : ActionTable}
    {ctors : List Lam.CtorInfo} {slotBase : Nat}
    (layout : Impl fd.block? fr.fn J fr.blk params acc next
      (skeleton P.base.size first (.dropSlot s k) ctors slotBase))
    (cursor : fr.rest = spine (skeleton P.base.size first (.dropSlot s k) ctors slotBase))
    (checked : checkFunction P.base.size lower fd table = true)
    (tableLookup : P.actions.get? fr.fn = some table)
    (effect : Own.Plain.evalAction fr.env H (.dec (slotBase + s)) = .ok H') :
    step P (.run fr stk H) =
      .next (.run { fr with rest := spine (skeleton P.base.size (first + 1) k ctors slotBase) } stk H') false := by
  have member := impl_dropSlot_member layout
  obtain ⟨slot, action, decoded, _, found⟩ := collect_member
    ((checkMarkers_iff ..).mp checked) member (reserved_marker ..)
  simp only [decode_marker, Option.some.injEq, Prod.mk.injEq] at decoded
  rcases decoded with ⟨rfl, rfl⟩
  apply step_action_success ?_ tableLookup found effect
  simpa only [skeleton, spine, markerRhs_eq] using cursor

theorem impl_after_dropSlot {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {s : Nat} {k : Own.Plain.Code} {ctors : List Lam.CtorInfo} {slotBase : Nat}
    (h : Impl fd.block? self J cur params acc next (skeleton limit first (.dropSlot s k) ctors slotBase)) :
    Impl fd.block? self J cur params (marker limit first (.dec (slotBase + s)) :: acc) next
      (skeleton limit (first + 1) k ctors slotBase) := by
  simpa only [skeleton, Impl, markerRhs_eq] using h

theorem heapCtorAt_heapCtorIndex {ctors : List Lam.CtorInfo} {ctor : Fir.CtorInfo}
    (hof : Fir.CtorInfo.ofKey ctors ctor.key = some ctor) (hpos : 0 < ctor.arity) :
    heapCtorAt ctors (heapCtorIndex ctors ctor.key) = some ctor := by
  simp only [Fir.CtorInfo.ofKey, Option.map_eq_some_iff] at hof
  obtain ⟨r, hfind, hctor⟩ := hof
  have hmem : r ∈ ctors := List.mem_of_find?_eq_some hfind
  have hkey : (r.key == ctor.key) = true := List.find?_some (p := fun c : Lam.CtorInfo => c.key == ctor.key) hfind
  have harity : r.arity > 0 := by
    have : ctor.arity = r.arity := by rw [← hctor]; simp [Fir.CtorInfo.arity]
    omega
  let hs := ctors.filter (fun c => decide (c.arity > 0))
  have hmemF : r ∈ hs := List.mem_filter.mpr ⟨hmem, decide_eq_true harity⟩
  have hne : (hs.zipIdx.find? fun p => p.1.key == ctor.key).isSome := by
    rw [List.find?_isSome]
    obtain ⟨idx, hlt, hget⟩ := List.mem_iff_getElem.mp hmemF
    refine ⟨(r, idx), ?_, hkey⟩
    rw [List.mem_iff_getElem]
    exact ⟨idx, by simp [hlt], by simp [hget]⟩
  cases hf : hs.zipIdx.find? (fun p => p.1.key == ctor.key) with
  | none => simp [hf] at hne
  | some p =>
    obtain ⟨c', idx⟩ := p
    have hc'key : (c'.key == ctor.key) = true :=
      List.find?_some (p := fun p : Lam.CtorInfo × Nat => p.1.key == ctor.key) hf
    have hc'mem : (c', idx) ∈ hs.zipIdx := List.mem_of_find?_eq_some hf
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hc'mem
    simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq] at hj hget
    obtain ⟨hgetElem, hjEq⟩ := hget
    subst hjEq
    have hidx : heapCtorIndex ctors ctor.key = j := by
      unfold heapCtorIndex
      change ((hs.zipIdx.find? fun p => p.1.key == ctor.key).map (·.2)).getD 0 = j
      rw [hf]; rfl
    rw [hidx]
    unfold heapCtorAt
    change ((hs[j]? : Option Lam.CtorInfo).bind fun c => Fir.CtorInfo.ofKey ctors c.key) = some ctor
    rw [List.getElem?_eq_getElem hj, hgetElem]
    simp only [Option.bind_some]
    have hkeq : c'.key = ctor.key := eq_of_beq hc'key
    rw [hkeq]
    simp only [Fir.CtorInfo.ofKey, hfind, Option.map_some, hctor]


end IxCC.Cfg.Rc
