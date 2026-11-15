import IxVMRefinement.L1.Records
import Ix.IxVM.Refinement.Claim

/-! # A reader store constructed from bytes

Admission can first rebuild the reader's store from exact-decoded bytes, then compute its
closure and blob selection. The resulting caches are coherent independently of the input
caches, and every retained record has the input's bytes at the same address.
-/

namespace IxVM.Refinement.Assembly

/-- Retain exactly the records whose byte windows decode, caching the decoded value. -/
def decodeReaderConsts : List (_root_.Address × Ixon.LazyConstant) →
    Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => {}
  | (a, lc) :: rest =>
    match Ixon.deConstantExact lc.rawBytes with
    | .ok c => (decodeReaderConsts rest).insert a (L1.mkLazyConst lc.rawBytes c)
    | .error _ => decodeReaderConsts rest

theorem decodeReaderConsts_get?_inv :
    ∀ (rows : List (_root_.Address × Ixon.LazyConstant))
      {a : _root_.Address} {lc' : Ixon.LazyConstant},
      (decodeReaderConsts rows).get? a = some lc' →
      ∃ lc c, (a, lc) ∈ rows ∧ Ixon.deConstantExact lc.rawBytes = .ok c ∧
        lc' = L1.mkLazyConst lc.rawBytes c
  | [], _, _, h => by
    rw [decodeReaderConsts, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h
    cases h
  | (key, lc) :: rest, a, lc', h => by
    cases hdec : Ixon.deConstantExact lc.rawBytes with
    | error e =>
      simp only [decodeReaderConsts, hdec] at h
      obtain ⟨old, c, hm, hd, heq⟩ := decodeReaderConsts_get?_inv rest h
      exact ⟨old, c, List.mem_cons_of_mem _ hm, hd, heq⟩
    | ok c =>
      simp only [decodeReaderConsts, hdec] at h
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      cases hkey : key == a with
      | true =>
        have hka : key = a := beq_iff_eq.mp hkey
        subst a
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
        exact ⟨lc, c, List.mem_cons_self, hdec, h.symm⟩
      | false =>
        simp only [hkey, Bool.false_eq_true, ↓reduceIte,
          ← Std.HashMap.get?_eq_getElem?] at h
        obtain ⟨old, c, hm, hd, heq⟩ := decodeReaderConsts_get?_inv rest h
        exact ⟨old, c, List.mem_cons_of_mem _ hm, hd, heq⟩

/-- A fresh coherent record cache over the same input bytes, blobs, hints, and binding. -/
def decodeReaderEnv (E : Ixon.Env) : Ixon.Env :=
  { E with consts := decodeReaderConsts E.consts.toList }

theorem decodeReaderEnv_exact (E : Ixon.Env) {a : _root_.Address} {lc : Ixon.LazyConstant}
    (hget : (decodeReaderEnv E).consts.get? a = some lc) :
    ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c := by
  obtain ⟨old, c, _, hdec, rfl⟩ := decodeReaderConsts_get?_inv E.consts.toList hget
  exact ⟨c, L1.mkLazyConst_get? _ _, by simpa only [L1.mkLazyConst_rawBytes] using hdec⟩

theorem decodeReaderEnv_coherent (E : Ixon.Env) {a : _root_.Address} {lc : Ixon.LazyConstant}
    (hget : (decodeReaderEnv E).consts.get? a = some lc) :
    lc.get? = (Ixon.deConstantExact lc.rawBytes).toOption := by
  obtain ⟨c, hcache, hdec⟩ := decodeReaderEnv_exact E hget
  rw [hcache, hdec]
  rfl

/-- Decoding the view itself preserves raw-byte provenance without any assumption on its
original cache. This is different from mutating a separately supplemented admission witness. -/
theorem decodeReaderEnv_draws (E : Ixon.Env) : IxVM.Refinement.Draws (decodeReaderEnv E) E := by
  constructor
  · intro a lc hget
    obtain ⟨old, c, hm, _, rfl⟩ := decodeReaderConsts_get?_inv E.consts.toList hget
    have hsource : E.consts.get? a = some old := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm
    exact .inl ⟨old, hsource, (L1.mkLazyConst_rawBytes _ _).symm⟩
  · intro a bytes hget
    exact hget

end IxVM.Refinement.Assembly
