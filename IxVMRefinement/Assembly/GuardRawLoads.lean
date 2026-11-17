import IxVMRefinement.Assembly.GuardRawLookup

/-! # Dictionary type readings produced by actual raw constant loads

A raw loaded constant either exposes the loader's explicit internal-collision alternative or
supplies its address-keyed declared-type reading. No InLogic, typed-environment, closedness or
model-lookup premise is used. Projection kinds resolve their actual stored owner blocks.
-/

namespace IxVM.Refinement.GuardRaw

open Aiur
open IxVM.Consistency
open Ix.Kernel (Expr)

private theorem solo_self_ok (a : _root_.Address) (d : Ixon.Definition) :
    ∀ i x, (L1.defnRecurAddrs d a)[i]? = some x →
      ∃ m k, soloSelf addressTable a i = some m ∧ m = .ok k := by
  unfold L1.defnRecurAddrs
  split
  · exact LoadedReads.soloSelf_ok addressTable a
  · intro i x hx; simp at hx

private theorem member_self_ok (B : _root_.Address) (ms : Array Ixon.MutConst)
    (d : Ixon.Definition) :
    ∀ i x, (L1.defnMemberRecurAddrs d B ms.toList)[i]? = some x →
      ∃ m k, blockSelf addressTable B ms i = some m ∧ m = .ok k := by
  unfold L1.defnMemberRecurAddrs
  split
  · exact LoadedReads.blockSelf_ok addressTable B ms
  · intro i x hx; simp at hx

/-- Every raw loaded constant has a bounded declared-type root that the dictionary reads,
unless the loader has already found an internal hash collision. -/
theorem type_read_of_rawCI {E : Ixon.Env} {h : Heap IxVM.F} {a : _root_.Address}
    {c : Ixon.Constant} {v : SourceValue IxVM.F}
    (hc : recordOf E a = some c) (raw : L1.RawCIRep E h a c v) :
    L1.EnvInternalCollision E ∨
      ∃ root e, typeRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
        readRoot (fun x => E.blobs.get? x) root = some e := by
  cases hi : c.info with
  | defn d =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨blobs, hb, hn, tp, vp, hint, _, rt, _⟩ := raw
    rcases hb with hb | hcol
    · let root : Root := ⟨c, soloSelf addressTable a, 0, d.lvls.toNat, d.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt (solo_self_ok a d)
        (fun x b hmem => (hb x b hmem).1)
      exact Or.inr ⟨root, e, by simp [typeRoot, hc, hi, root], hn, he⟩
    · exact Or.inl hcol
  | axio ax =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨blobs, hb, hn, tp, _, rt⟩ := raw
    rcases hb with hb | hcol
    · let root : Root := ⟨c, fun _ => none, 0, ax.lvls.toNat, ax.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt
        (fun i x hx => by simp at hx) (fun x b hmem => (hb x b hmem).1)
      exact Or.inr ⟨root, e, by simp [typeRoot, hc, hi, root], hn, he⟩
    · exact Or.inl hcol
  | quot q =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨blobs, hb, hn, tp, _, rt⟩ := raw
    rcases hb with hb | hcol
    · let root : Root := ⟨c, fun _ => none, 0, q.lvls.toNat, q.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt
        (fun i x hx => by simp at hx) (fun x b hmem => (hb x b hmem).1)
      exact Or.inr ⟨root, e, by simp [typeRoot, hc, hi, root], hn, he⟩
    · exact Or.inl hcol
  | recr rc =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨blobs, hb, hn, _, _, _, _, _, tp, rp, bp, b, _, _, _, rt, _⟩ := raw
    rcases hb with hb | hcol
    · let root : Root := ⟨c, soloSelf addressTable a, 0, rc.lvls.toNat, rc.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt
        (fun i x hx => by simp at hx) (fun x b hmem => (hb x b hmem).1)
      exact Or.inr ⟨root, e, by simp [typeRoot, hc, hi, root], hn, he⟩
    · exact Or.inl hcol
  | dPrj p =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨_, lc, cb, ms, d, blobs, hget, _, _, hdec, _, hms, hm, hb,
      hn, tp, vp, hint, _, rt, _⟩ := raw
    have hcb := Typing.recordOf_of_get hget hdec
    have hm' : ms[p.idx.toNat]? = some (.defn d) := by simpa only [Array.getElem?_toList] using hm
    rcases hb with hb | hcol
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
        L1.mutsRootOffset ms.toList p.idx.toNat, d.lvls.toNat, d.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt (member_self_ok p.block ms d)
        (fun x b hmem => (hb x b hmem).1)
      refine Or.inr ⟨root, e, ?_, hn, he⟩
      simp [typeRoot, hc, hi, memberRoot, hcb, hms, hm', definitionType, root]
    · exact Or.inl hcol
  | iPrj p =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨_, lc, cb, ms, ind, blobs, hget, _, _, hdec, _, hms, hm, hb,
      hn, _, _, _, _, tp, bp, b, _, _, _, rt⟩ := raw
    have hcb := Typing.recordOf_of_get hget hdec
    have hm' : ms[p.idx.toNat]? = some (.indc ind) := by simpa only [Array.getElem?_toList] using hm
    rcases hb with hb | hcol
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
        L1.mutsRootOffset ms.toList p.idx.toNat, ind.lvls.toNat, ind.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt
        (LoadedReads.blockSelf_ok addressTable p.block ms) (fun x b hmem => (hb x b hmem).1)
      refine Or.inr ⟨root, e, ?_, hn, he⟩
      simp [typeRoot, hc, hi, memberRoot, hcb, hms, hm', inductiveType, root]
    · exact Or.inl hcol
  | cPrj p =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨_, _, lc, cb, ms, ind, ct, blobs, hget, _, _, hdec, _, hms, hm, hct, hb,
      hn, _, _, _, _, tp, bp, b, _, _, _, rt⟩ := raw
    have hcb := Typing.recordOf_of_get hget hdec
    have hm' : ms[p.idx.toNat]? = some (.indc ind) := by simpa only [Array.getElem?_toList] using hm
    have hct' : ind.ctors[p.cidx.toNat]? = some ct := by simpa only [Array.getElem?_toList] using hct
    rcases hb with hb | hcol
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
        L1.mutsRootOffset ms.toList p.idx.toNat + (1 + p.cidx.toNat), ct.lvls.toNat, ct.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt
        (LoadedReads.blockSelf_ok addressTable p.block ms) (fun x b hmem => (hb x b hmem).1)
      refine Or.inr ⟨root, e, ?_, hn, he⟩
      simp [typeRoot, hc, hi, memberRoot, hcb, hms, hm', constructorType, hct', root]
    · exact Or.inl hcol
  | rPrj p =>
    rw [L1.RawCIRep, hi] at raw
    obtain ⟨_, lc, cb, ms, rc, blobs, hget, _, _, hdec, _, hms, hm, hb,
      hn, _, _, _, _, _, tp, rp, bp, b, _, _, _, rt, _⟩ := raw
    have hcb := Typing.recordOf_of_get hget hdec
    have hm' : ms[p.idx.toNat]? = some (.recr rc) := by simpa only [Array.getElem?_toList] using hm
    rcases hb with hb | hcol
    · let root : Root := ⟨cb, blockSelf addressTable p.block ms,
        L1.mutsRootOffset ms.toList p.idx.toNat, rc.lvls.toNat, rc.typ⟩
      obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rt
        (fun i x hx => by simp at hx) (fun x b hmem => (hb x b hmem).1)
      refine Or.inr ⟨root, e, ?_, hn, he⟩
      simp [typeRoot, hc, hi, memberRoot, hcb, hms, hm', recursorType, root]
    · exact Or.inl hcol
  | muts ms =>
    rw [L1.RawCIRep, hi] at raw
    exact False.elim raw

/-- From its actual converted payload, a standalone definition supplies the dictionary value
at every arity-correct universe application, or the loader's explicit collision alternative. -/
theorem value_read_of_raw_defn {E : Ixon.Env} {h : Heap IxVM.F} {a : _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} {v : SourceValue IxVM.F}
    (hc : recordOf E a = some c) (hi : c.info = .defn d) (hk : d.kind = .defn)
    (raw : L1.RawCIRep E h a c v) :
    L1.EnvInternalCollision E ∨
      ∃ root e, valueRoot (recordOf E) a = some root ∧ root.levels < 4294967296 ∧
        readRoot (fun x => E.blobs.get? x) root = some e := by
  rw [L1.RawCIRep, hi] at raw
  obtain ⟨blobs, hb, hn, tp, vp, hint, _, _, rv⟩ := raw
  rcases hb with hb | hcol
  · let root : Root := ⟨c, soloSelf addressTable a, 1, d.lvls.toNat, d.value⟩
    obtain ⟨e, he⟩ := readRoot_of_rawConv (root := root) rv (solo_self_ok a d)
      (fun x b hmem => (hb x b hmem).1)
    exact Or.inr ⟨root, e, by simp [valueRoot, hc, hi, hk, root], hn, he⟩
  · exact Or.inl hcol

end IxVM.Refinement.GuardRaw
