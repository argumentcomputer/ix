import IxCC.Cfg.Rc.Proof.Native.Pipeline

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

private theorem suffix_at {α : Type} (before after : List α) (i : Nat) :
    (before ++ after)[before.length + i]? = after[i]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem wrappers_length (l : Layout) : (wrappers l).length = 2 + l.ctors.length := by
  simp [wrappers]
  omega

theorem procedures_length (l : Layout) : (procedures l).length = 2 + l.ctors.length := by
  simp [procedures]
  omega

theorem raw_inc_wrapper {l : Layout} {funcs : List Lir.Func} (hlen : funcs.length = l.sourceCount)
    (main : Nat) :
    (rawProgram l funcs main).funcs[l.incWrapper]? = some (incrementWrapper l.incProc) := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc, Layout.incWrapper]
  rw [← hlen, show funcs.length = funcs.length + 0 by omega, suffix_at]
  simp [wrappers]

theorem raw_dec_wrapper {l : Layout} {funcs : List Lir.Func} (hlen : funcs.length = l.sourceCount)
    (main : Nat) :
    (rawProgram l funcs main).funcs[l.decWrapper]? = some (decrementWrapper l.decProc) := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc, Layout.decWrapper]
  rw [← hlen, suffix_at]
  simp [wrappers]

theorem raw_inc_proc {l : Layout} {funcs : List Lir.Func} (hlen : funcs.length = l.sourceCount)
    (main : Nat) :
    (rawProgram l funcs main).funcs[l.incProc]? = some Rt.Rc.Procs.inc := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc]
  rw [show l.incProc = funcs.length + (wrappers l).length by rw [hlen, wrappers_length]; simp [Layout.incProc]; omega,
    suffix_at]
  rw [show (wrappers l).length = (wrappers l).length + 0 by omega, suffix_at]
  simp [procedures]

theorem raw_dec_proc {l : Layout} {funcs : List Lir.Func} (hlen : funcs.length = l.sourceCount)
    (main : Nat) :
    (rawProgram l funcs main).funcs[l.decProc]? = some Rt.Rc.Gen.dec := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc]
  rw [show l.decProc = funcs.length + ((wrappers l).length + 1) by
    rw [hlen, wrappers_length]; simp [Layout.decProc, Layout.incProc]; omega, suffix_at, suffix_at]
  simp [procedures]

theorem raw_alloc_proc {l : Layout} {funcs : List Lir.Func} (hlen : funcs.length = l.sourceCount)
    (main i : Nat) {c : Lam.CtorInfo} (hc : l.ctors[i]? = some c) :
    (rawProgram l funcs main).funcs[l.allocProc i]? = some (Rt.Rc.Gen.alloc (Rt.Rc.CellLayout.ofFields c.arity c.tag)) := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc]
  rw [show l.allocProc i = funcs.length + ((wrappers l).length + (2 + i)) by
    rw [hlen, wrappers_length]; simp [Layout.allocProc, Layout.incProc]; omega, suffix_at, suffix_at]
  simp only [procedures, List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp hc).1)]
  simp [hc]

theorem raw_alloc_wrapper {l : Layout} {funcs : List Lir.Func} (hlen : funcs.length = l.sourceCount)
    (main i : Nat) {c : Lam.CtorInfo} (hc : l.ctors[i]? = some c) :
    (rawProgram l funcs main).funcs[l.allocWrapper i]? =
      some (allocationWrapper (l.allocProc i) c.arity) := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc]
  rw [show l.allocWrapper i = funcs.length + (2 + i) by
    rw [hlen]; simp [Layout.allocWrapper]; omega, suffix_at]
  have hi : 2 + i < (wrappers l).length := by
    rw [wrappers_length]
    have := (List.getElem?_eq_some_iff.mp hc).1
    omega
  rw [List.getElem?_append_left hi]
  simp only [wrappers]
  rw [List.getElem?_append_right (by simp)]
  simp [List.getElem?_zipIdx, hc]

theorem raw_source {l : Layout} {funcs : List Lir.Func} (main f : Nat)
    (hf : f < funcs.length) : (rawProgram l funcs main).funcs[f]? = funcs[f]? := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc]
  exact List.getElem?_append_left hf

theorem raw_init {l : Layout} {funcs : List Lir.Func} (hlen : funcs.length = l.sourceCount)
    (main : Nat) : (rawProgram l funcs main).funcs[l.init]? = some Rt.Procs.cxInit := by
  simp only [rawProgram, List.getElem?_toArray, List.append_assoc]
  rw [show l.init = funcs.length + ((wrappers l).length + (procedures l).length) by
    rw [hlen, wrappers_length, procedures_length]; simp [Layout.init, Layout.incProc]; omega,
    suffix_at, suffix_at]
  rw [show (procedures l).length = (procedures l).length + 0 by omega, suffix_at]
  rfl









end IxCC.Cfg.Rc.Native.Spec
