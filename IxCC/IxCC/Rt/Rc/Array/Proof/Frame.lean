import IxCC.Rt.Rc.Array.Invariant
import IxCC.Rt.Rc.Proof.CountPreserve

/-! # Memory frames for the array runtime

`MemFrame m m' touched`: `m'` has `m`'s permissions and `m`'s bytes wherever `touched` does not
hold. Every path specification of a runtime procedure concludes one, naming the byte ranges the
path writes (`Span`), so that a fact about any other cell is carried across the call by one lemma:
a word (`MemFrame.wordAt`), a byte, a load, a live array cell (`MemFrame.liveArrayCell`), a free
chain. Frames compose (`trans`) and weaken (`mono`); a store frames its own bytes (`write`). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open IxCC.Lir (Word loadWord)
open IxCC.Rt.Proof
open IxCC.Rt.Rc (maxClass classBytes)
open IxCC.Rt.Rc.Procs (FreeChain storeCount countAddress)
open IxCC.X86 (Memory Width)

/-- The byte range `[a, a + n)`. -/
def Span (a n : Nat) : Nat → Prop := fun k => a ≤ k ∧ k < a + n

/-- `m'` is `m` with the same permissions, except for the bytes at addresses in `touched`. -/
structure MemFrame (m m' : Memory) (touched : Nat → Prop) : Prop where
  readable : m'.readable = m.readable
  writable : m'.writable = m.writable
  bytes : ∀ a : Word, ¬ touched a.toNat → m'.bytes a = m.bytes a

namespace MemFrame

theorem refl (m : Memory) (t : Nat → Prop) : MemFrame m m t := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem mono {m m' : Memory} {t t' : Nat → Prop} (h : MemFrame m m' t) (ht : ∀ k, t k → t' k) :
    MemFrame m m' t' :=
  ⟨h.readable, h.writable, fun a ha => h.bytes a (fun hta => ha (ht _ hta))⟩

theorem trans {m₁ m₂ m₃ : Memory} {t : Nat → Prop} (h₁ : MemFrame m₁ m₂ t)
    (h₂ : MemFrame m₂ m₃ t) : MemFrame m₁ m₃ t :=
  ⟨h₂.readable.trans h₁.readable, h₂.writable.trans h₁.writable,
    fun a ha => (h₂.bytes a ha).trans (h₁.bytes a ha)⟩

/-- A store touches its own bytes. -/
theorem write (m : Memory) (w : Width) (a v : Word) (ha : a.toNat + w.bytes ≤ 2 ^ 64) :
    MemFrame m (m.write w a v) (Span a.toNat w.bytes) where
  readable := by simp [Memory.write]
  writable := by simp [Memory.write]
  bytes b hb := by
    have hw : w.bytes ≤ 8 := by cases w <;> simp [Width.bytes]
    simp only [Memory.write]
    apply writeLittle_bytes_out hw ha
    unfold Span at hb
    omega

/-- A word whose eight bytes are untouched. -/
theorem wordAt {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {b v : Word}
    (hw : WordAt m b v) (hb : b.toNat + 8 ≤ 2 ^ 64)
    (hout : ∀ k, b.toNat ≤ k → k < b.toNat + 8 → ¬ t k) : WordAt m' b v where
  bytes i hi := by
    have hi' : (b + UInt64.ofNat i).toNat = b.toNat + i := addr_toNat (by omega)
    rw [h.bytes _ (hout _ (by rw [hi']; omega) (by rw [hi']; omega))]
    exact hw.bytes i hi
  readable i hi := by rw [h.readable]; exact hw.readable i hi

/-- An untouched byte. -/
theorem byteAt {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {b : Word} {v : UInt8}
    (hb : ByteAt m b v) (hout : ¬ t b.toNat) : ByteAt m' b v :=
  ⟨by rw [h.bytes _ hout]; exact hb.byte, by rw [h.readable]; exact hb.readable⟩

/-- A read of untouched bytes. -/
theorem read? {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) (w : Width) (a : Word)
    (ha : a.toNat + w.bytes ≤ 2 ^ 64)
    (hout : ∀ k, a.toNat ≤ k → k < a.toNat + w.bytes → ¬ t k) :
    m'.read? w a = m.read? w a := by
  have hrd : m'.read w a = m.read w a := by
    simp only [Memory.read]
    apply Memory.readLittle_congr
    intro i hi
    have hi' : (a + UInt64.ofNat i).toNat = a.toNat + i := addr_toNat (by omega)
    exact h.bytes _ (hout _ (by rw [hi']; omega) (by rw [hi']; omega))
  simp only [Memory.read?, h.readable, hrd]

/-- A load of untouched bytes. -/
theorem load {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {w : Width}
    {e : IxCC.Lir.Ext} {a v : Word} (hl : loadWord m w e a = some v)
    (ha : a.toNat + w.bytes ≤ 2 ^ 64)
    (hout : ∀ k, a.toNat ≤ k → k < a.toNat + w.bytes → ¬ t k) :
    loadWord m' w e a = some v := by
  simpa only [loadWord, h.read? w a ha hout] using hl

/-- A store that succeeded before the frame succeeds after it. -/
theorem write?_ok {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {w : Width} {a v u : Word}
    {m₁ : Memory} (hw : m.write? w a v = .ok m₁) : m'.write? w a u = .ok (m'.write w a u) := by
  unfold Memory.write? at hw ⊢
  rw [h.writable]
  split at hw
  · rename_i hok; simp [hok]
  · cases hw

/-- A live array cell none of whose bytes is touched. -/
theorem liveArrayCell {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t)
    {addr : Word} {refs cls cap : Nat} {val : ArrayVal}
    (hc : LiveArrayCell m addr refs cls cap val)
    (hout : ∀ k, addr.toNat ≤ k → k < addr.toNat + classBytes cls → ¬ t k) :
    LiveArrayCell m' addr refs cls cap val := by
  have h24 := hc.classBytes_ge_24
  have hfit := hc.fit
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  have hbytes := arrayBytes_eq_classBytes hc.cls_lo hc.cls_hi
  refine ⟨hc.aligned, hc.nonzero, hc.cls_lo, hc.cls_hi, hc.refs_pos, hc.refs_le, hc.fit,
    hc.size_le, hc.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [h.readable, h.writable]; exact hc.access j hj
  · exact h.wordAt hc.header_word (by omega) (fun k h1 h2 => hout k h1 (by omega))
  · exact h.wordAt hc.size_word (by rw [h8]; omega)
      (fun k h1 h2 => hout k (by rw [h8] at h1; omega) (by rw [h8] at h2; omega))
  · exact h.wordAt hc.cap_word (by rw [h16]; omega)
      (fun k h1 h2 => hout k (by rw [h16] at h1; omega) (by rw [h16] at h2; omega))
  · cases val with
    | boxed elems =>
      intro j hj
      have hcap : cap ≤ wordCapOfClass cls := hc.cap_fit
      have hsz : elems.length ≤ cap := hc.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact h.wordAt (hc.payload j hj) (by rw [hja]; omega)
        (fun k h1 h2 => hout k (by rw [hja] at h1; omega) (by rw [hja] at h2; omega))
    | limbs elems =>
      intro j hj
      have hcap : cap ≤ wordCapOfClass cls := hc.cap_fit
      have hsz : elems.length ≤ cap := hc.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact h.wordAt (hc.payload j hj) (by rw [hja]; omega)
        (fun k h1 h2 => hout k (by rw [hja] at h1; omega) (by rw [hja] at h2; omega))
    | bytes data =>
      intro j hj
      have hcap : cap ≤ byteCapOfClass cls := hc.cap_fit
      have hsz : data.length ≤ cap := hc.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + j)).toNat =
          addr.toNat + (arrayPayloadOffset + j) := addr_toNat (by omega)
      exact h.byteAt (hc.payload j hj) (hout _ (by rw [hja]; omega) (by rw [hja]; omega))

/-- A free chain none of whose link words is touched. -/
theorem freeChain {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) :
    ∀ (chain : List Word), FreeChain m chain →
      (∀ a ∈ chain, a.toNat + 8 ≤ 2 ^ 64 ∧ ∀ k, a.toNat ≤ k → k < a.toNat + 8 → ¬ t k) →
      FreeChain m' chain := by
  intro chain
  induction chain with
  | nil => intro _ _; trivial
  | cons a tail ih =>
    intro hc hs
    exact ⟨h.wordAt hc.1 (hs a (by simp)).1 (hs a (by simp)).2,
      ih hc.2 (fun b hb => hs b (by simp [hb]))⟩

end MemFrame

/-- A 32-bit load of a 32-bit store of a value below `2^32`. -/
theorem load32_write32 {m : Memory} {a v : Word}
    (hr : ∀ i < 4, m.readable (a + UInt64.ofNat i) = true) (hv : v.toNat < 2 ^ 32) :
    loadWord (m.write .w32 a v) .w32 .zero a = some v := by
  have hr' : ∀ i < Width.w32.bytes, (m.write .w32 a v).readable (a + UInt64.ofNat i) = true := by
    intro i hi
    have hi4 : i < 4 := by simpa [Width.bytes] using hi
    simpa [Memory.write] using hr i hi4
  have h1 := read?_ok hr'
  rw [IxCC.Rt.Rc.Procs.read32_write32, IxCC.Rt.Rc.Procs.truncate32_small hv] at h1
  simp [loadWord, h1]

/-- A store succeeds on writable bytes given by an offset range of a cell. -/
theorem write?_ok_of_access {m : Memory} {base : Word} {n off : Nat} {w : Width} (v : Word)
    (hacc : ∀ j < n, m.writable (base + UInt64.ofNat j) = true)
    (hfit : base.toNat + n < 2 ^ 64) (hoff : off + w.bytes ≤ n) :
    m.write? w (base + UInt64.ofNat off) v = .ok (m.write w (base + UInt64.ofNat off) v) := by
  apply write?_ok
  intro k hk
  have ho : (base + UInt64.ofNat off).toNat = base.toNat + off := addr_toNat (by omega)
  have hka : (base + UInt64.ofNat off) + UInt64.ofNat k = base + UInt64.ofNat (off + k) := by
    apply UInt64.toNat_inj.mp
    rw [addr_toNat (by rw [ho]; omega), ho, addr_toNat (by omega)]
    omega
  rw [hka]
  exact hacc (off + k) (by omega)

end IxCC.Rt.Rc.Array
