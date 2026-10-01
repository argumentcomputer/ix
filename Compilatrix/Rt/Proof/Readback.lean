import Compilatrix.Rt.Proof.Heap
import Compilatrix.Rt.Readback

/-!
# `Rt.readback_sound`

The runtime's type-directed readback of a result word agrees with Own's
readback of the related value, for a value of the read type
(`Typed`): a `Nat` literal, a field-less constructor of the inductive, or a
cell whose constructor the signature lists with its fields' types. The
signature is consistent with Cfg's constructor table exactly where `Typed`
asks: at each constructor the value holds. Both readbacks spend their fuel
at cells only, so they agree at every fuel (`readback_toFir`), and at Own's
(`readback_sound`).
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower

/-- **A Cfg value of a first-order result type** under signature `sig`. -/
inductive Typed (sig : Sig) (H : Own.Heap) : FoTy → Own.RVal → Prop
  | nat {n : Nat} : Typed sig H .nat (.lit (.nat n))
  | ctor0 {i : Nat} {c : Fir.CtorInfo} : sig.ctor? i c.tag = some [] → Typed sig H (.ind i) (.ctor0 c)
  | cell {i ℓ rc : Nat} {mode : Own.OMode} {b : Own.Body} {tys : List FoTy} :
      H.cells[ℓ]? = some (.live rc mode b) → sig.ctor? i b.ctor.tag = some tys → tys.length = b.fields.length →
      (∀ (j : Nat) (t : FoTy) (v : Own.RVal), tys[j]? = some t → b.fields[j]? = some v → Typed sig H t v) →
      Typed sig H (.ind i) (.loc ℓ)

theorem toFirList_length {H : Own.Heap} {k : Nat} :
    ∀ {vs : List Own.RVal} {fs : List Fir.Val}, Own.toFirList H k vs = some fs → fs.length = vs.length
  | [], fs, h => by simp [Own.toFirList] at h; subst h; rfl
  | v :: vs, fs, h => by
    simp only [Own.toFirList] at h
    split at h
    · rename_i w ws _ hws
      simp only [Option.some.injEq] at h
      subst h
      simp [toFirList_length hws]
    · cases h

/-- The fields of a cell, read back at their types. -/
theorem fields_readback {H : Own.Heap} {k : Nat} {F : FoTy × Nat → Option Sem.Obs} :
    ∀ (tys : List FoTy) (fields : List Own.RVal) (j₀ : Nat), tys.length = fields.length →
      (∀ (j : Nat) (t : FoTy) (f : Own.RVal), tys[j]? = some t → fields[j]? = some f →
        F (t, j₀ + j) = (Own.toFir H k f).bind Fir.readback) →
      (tys.zipIdx j₀).mapM F = (Own.toFirList H k fields).bind Fir.readbackList
  | [], [], _, _, _ => by simp [Own.toFirList, Fir.readbackList]
  | t :: tys, f :: fields, j₀, hlen, hfs => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have h0 := hfs 0 t f rfl rfl
    have ih := fields_readback tys fields (j₀ + 1) hlen fun j t' f' ht hf => by
      rw [show j₀ + 1 + j = j₀ + (j + 1) by omega]
      exact hfs (j + 1) t' f' (by simpa using ht) (by simpa using hf)
    rw [List.zipIdx_cons, List.mapM_cons]
    simp only [Nat.add_zero] at h0
    rw [h0, ih]
    simp only [Own.toFirList]
    cases hf : Own.toFir H k f with
    | none => simp
    | some fv =>
      cases hfs' : Own.toFirList H k fields with
      | none => simp
      | some fvs =>
        simp only [Option.bind_some, Fir.readbackList]
        cases Fir.readback fv <;> cases Fir.readbackList fvs <;> rfl

/-- **The two readbacks agree at every fuel.** -/
theorem readback_toFir {T : Tables} {P : List Word} {H : Own.Heap} {ctx : Word} {m : X86.Memory} {sig : Sig}
    (hheap : HeapInv T P H ctx m) :
    ∀ (k : Nat) {ty : FoTy} {v : Own.RVal} {w : Word}, Typed sig H ty v → ValRel T P v w →
      readback sig k m ty w = (Own.toFir H k v).bind Fir.readback := by
  obtain ⟨bump, limit, hA⟩ := hheap
  intro k
  induction k with
  | zero =>
    intro ty v w hty hrel
    cases hty with
    | nat => simp [readback_nat hrel, Own.toFir, Fir.readback]
    | @ctor0 i c hc =>
      obtain ⟨rfl, hok, hfl⟩ := hrel
      have ht : c.tag < natLimit := Nat.lt_of_le_of_lt hok.tag (by decide)
      simp only [readback_ctor0 ht hc, Own.toFir, Option.bind_some, Fir.readback]
      have : c.arity = 0 := by simpa [Fir.CtorInfo.fieldless] using hfl
      simp [this, Fir.readbackList]
    | cell hcell hc hlen hfs =>
      obtain ⟨-, hca, -, -⟩ := hA.cell hrel hcell
      have hw : w &&& 1 ≠ 1 := cell_even hca.aligned
      unfold readback
      simp [hw, Own.toFir]
  | succ k ih =>
    intro ty v w hty hrel
    cases hty with
    | nat => simp [readback_nat hrel, Own.toFir, Fir.readback]
    | @ctor0 i c hc =>
      obtain ⟨rfl, hok, hfl⟩ := hrel
      have ht : c.tag < natLimit := Nat.lt_of_le_of_lt hok.tag (by decide)
      simp only [readback_ctor0 ht hc, Own.toFir, Option.bind_some, Fir.readback]
      have : c.arity = 0 := by simpa [Fir.CtorInfo.fieldless] using hfl
      simp [this, Fir.readbackList]
    | @cell i ℓ rc mode b tys hcell hc hlen hfs =>
      obtain ⟨-, hca, -, -⟩ := hA.cell hrel hcell
      have hw : w &&& 1 ≠ 1 := cell_even hca.aligned
      have hpos : 0 < b.fields.length := by
        have := hca.fieldless
        simp only [Fir.CtorInfo.fieldless, beq_eq_false_iff_ne] at this
        rw [hca.arity]
        omega
      rw [readback_cell hw hca.header.read64 hca.small hca.ctor.tag hc hlen hpos]
      rw [fields_readback tys b.fields 0 hlen fun j t f ht hf => ?_]
      · simp only [Own.toFir, Own.Heap.cell?, hcell]
        cases hfs' : Own.toFirList H k b.fields with
        | none => simp
        | some fs =>
          have hfl := toFirList_length hfs'
          simp [Fir.readback, hfl, ← hca.arity]
      · obtain ⟨wv, hwv, hrv⟩ := hca.fields j f hf
        simp only [Nat.zero_add]
        have h64 : m.read64? (w + UInt64.ofNat (8 + 8 * j)) = .ok wv := hwv.read64
        rw [h64]
        exact ih (hfs j t f ht hf) hrv

/-- **`Rt.readback_sound`**: under the heap invariant, the runtime readback
of a word related to a value of the read type is Own's readback of the
value. -/
theorem readback_sound {T : Tables} {P : List Word} {H : Own.Heap} {ctx : Word} {m : X86.Memory} {sig : Sig}
    {ty : FoTy} {v : Own.RVal} {w : Word} (hheap : HeapInv T P H ctx m) (hty : Typed sig H ty v)
    (hrel : ValRel T P v w) : readback sig (H.size + 1) m ty w = H.readback v :=
  readback_toFir hheap (H.size + 1) hty hrel

end Compilatrix.Rt.Proof
