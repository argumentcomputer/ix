import IxCC.Rt.Rc.Proof.Readback.Header
import IxCC.Rt.Proof.Readback

set_option autoImplicit false
namespace IxCC.Rt.Rc.Procs.Readback
open IxCC.Lir (Word)
open IxCC.Rt.Proof

theorem ctor0_rep {addresses : AddressMap} {c : Fir.CtorInfo} {w : Word}
    (h : valueWord addresses (.ctor0 c) = some w) :
    c.arity = 0 ∧ c.tag ≤ maxTag ∧ w = ctor0Word c.tag := by
  simp only [valueWord] at h
  split at h
  · next hc =>
    have facts : c.arity = 0 ∧ c.tag ≤ maxTag := by simpa using hc
    exact ⟨facts.1, facts.2, (Option.some.inj h).symm⟩
  · cases h

/-- Equal-fuel agreement for complete typed constructor trees in the actual
dynamic heap representation. Dead and recycled historical locations need no
placement obligation. -/
theorem readback_toFir {H : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {sig : Sig} (heap : HeapLive H addresses mem) :
    ∀ fuel {ty : FoTy} {v : Own.RVal} {w : Word},
      Typed sig H ty v → valueWord addresses v = some w →
      Rt.readback sig fuel mem ty w = (Own.toFir H fuel v).bind Fir.readback := by
  intro fuel
  induction fuel with
  | zero =>
    intro ty v w typed represented
    cases typed with
    | nat => simpa [Own.toFir, Fir.readback] using readback_nat represented
    | @ctor0 i c signature =>
      obtain ⟨arity, tag, rfl⟩ := ctor0_rep represented
      have ht : c.tag < natLimit := Nat.lt_of_le_of_lt tag (by decide)
      simp [readback_ctor0 ht signature, Own.toFir, Fir.readback, arity, Fir.readbackList]
    | @cell i location refs mode body tys cell signature length fields =>
      obtain ⟨_, address, placement, physical⟩ := heap.cell location refs mode body cell
      have equal : address = w := Option.some.inj (placement.symm.trans represented)
      subst address
      have even := cell_even physical.aligned
      simp [Rt.readback, even, Own.toFir]
  | succ fuel ih =>
    intro ty v w typed represented
    cases typed with
    | nat => simpa [Own.toFir, Fir.readback] using readback_nat represented
    | @ctor0 i c signature =>
      obtain ⟨arity, tag, rfl⟩ := ctor0_rep represented
      have ht : c.tag < natLimit := Nat.lt_of_le_of_lt tag (by decide)
      simp [readback_ctor0 ht signature, Own.toFir, Fir.readback, arity, Fir.readbackList]
    | @cell i location refs mode body tys cell signature length fields =>
      obtain ⟨_, address, placement, physical⟩ := heap.cell location refs mode body cell
      have equal : address = w := Option.some.inj (placement.symm.trans represented)
      subst address
      have hn := physical.fields_small
      have ht := physical.tag
      have hr := physical.bounded
      unfold maxTag at ht
      unfold maxCount at hr
      rw [Rc.readback_cell_header (cell_even physical.aligned) (live_header physical)
        (by omega) (by unfold smallClass; omega) (by omega) (by omega)
        signature length physical.fields_positive]
      rw [fields_readback tys body.fields 0 length fun j t v ht hv => ?_]
      · simp only [Own.toFir, Own.Heap.cell?, cell]
        cases hfs : Own.toFirList H fuel body.fields with
        | none => simp
        | some fs =>
          have len := toFirList_length hfs
          have arity : body.ctor.arity = body.fields.length := by
            simp [Fir.CtorInfo.arity, physical.nobj, physical.nscalar]
          simp [Fir.readback, len, arity]
      · obtain ⟨word, value, memory⟩ := physical.fields j v hv
        simp only [Nat.zero_add]
        have loaded : mem.read64? (w + UInt64.ofNat (8+8*j)) = .ok word := memory.read64
        rw [loaded]
        exact ih (fields j t v ht hv) value


end IxCC.Rt.Rc.Procs.Readback
