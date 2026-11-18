import IxVMRefinement.RoleVal.TableParseEvidence

/-! # `KernelRoles::load_role_table`, parsed

From the load's observation alone: the bytes it read and hashed are the binding section of a
table (`parsedTable`, its version the specification's, `wireWF`), whose hash is the binding
address; the node it returned holds exactly that table's pairs and evidence (`LoadedNode`); and
the observation of `evidence_roles_have_equations` over the evidence map it built.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- **The table the load parses**: its version, the pairs read (at their addresses), the
evidence read. -/
def parsedTable (ver : Nat) (lb : List (Ix.Kernel.Role × Bytes.Address))
    (le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address))) :
    Ix.Kernel.RoleTable :=
  ⟨ver, (lb.map fun p => (p.1, ixAddr p.2)).toArray, (le.map fun p => (p.1, p.2.toArray)).toArray⟩

/-- **The loaded table node, exactly**: the node at `tbl`, its binding pointer at `a`, its role
map with exactly the pairs `lb`, its address index with exactly one entry per pair, its evidence
map with exactly the entries `le`. -/
def LoadedNode (h : Heap F) (tbl : SourceValue F) (a : _root_.Address)
    (lb : List (Ix.Kernel.Role × Bytes.Address))
    (le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address))) : Prop :=
  ∃ (bp byRole byAddr ev : SourceValue F) (ents : List (Nat × SourceValue F))
    (es : List (Bytes.Address × SourceValue F)) (evEnts : List (Nat × SourceValue F)),
    loadValue h tbl = .ok (.construct rtEnum "Mk" [bp, byRole, byAddr, ev]) ∧
    S0.addr h bp a ∧
    RoleMapEntries roleAddrMapEnum h ents byRole ∧ BoundEntriesOf h lb ents ∧
    Claim.RBTreeBST .field h es byAddr ∧ IndexEntriesOf [] lb es ∧
    RoleMapEntries roleEvMapEnum h evEnts ev ∧ EvidenceEntriesOf h le evEnts

theorem LoadedNode.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂) {tbl : SourceValue F}
    {a : _root_.Address} {lb : List (Ix.Kernel.Role × Bytes.Address)}
    {le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address))}
    (hn : LoadedNode h₁ tbl a lb le) : LoadedNode h₂ tbl a lb le := by
  obtain ⟨bp, byRole, byAddr, ev, ents, es, evEnts, hl, hbp, hent, hbnd, hbst, hidx, hevm,
    hev⟩ := hn
  exact ⟨bp, byRole, byAddr, ev, ents, es, evEnts, ext.loadValue_eq hl, S0.addr_mono ext hbp,
    hent.mono ext, hbnd.mono ext, hbst.mono ext, hidx, hevm.mono ext, hev.mono ext⟩

theorem flatMap_map' {α β γ : Type} (f : α → β) (g : β → List γ) :
    ∀ l : List α, (l.map f).flatMap g = l.flatMap (fun a => g (f a))
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.flatMap_cons, flatMap_map' f g l]

theorem ascending_of_pairwise {α : Type} :
    ∀ {l : List (Ix.Kernel.Role × α)}, l.Pairwise (fun p q => p.1.idx < q.1.idx) →
      Ix.Kernel.RoleTable.Ascending (l.map (·.1)) = true
  | [], _ => rfl
  | [_], _ => rfl
  | p :: q :: l, h => by
    rw [List.pairwise_cons] at h
    simp only [List.map_cons, Ix.Kernel.RoleTable.Ascending, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨h.1 q List.mem_cons_self, ascending_of_pairwise h.2⟩

/-- **`KernelRoles::load_role_table`, parsed.** -/
theorem load_role_table_parse {x_a x_tbl : SourceValue F} {h h₁ : Heap F}
    {cs : List (Call F)} {a : _root_.Address} (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::load_role_table" [x_a] h x_tbl h₁ cs) :
    ∃ (bytes : List UInt8) (lb : List (Ix.Kernel.Role × Bytes.Address))
      (le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address)))
      (hE : Heap F) (evMap v : SourceValue F) (hE' : Heap F) (csE : List (Call F))
      (evEnts : List (Nat × SourceValue F)),
      Hashed cs ⟨bytes.toArray⟩ ∧ Address.blake3Pure ⟨bytes.toArray⟩ = a ∧
      (parsedTable Ix.Kernel.specVersion lb le).wireWF = true ∧
      (parsedTable Ix.Kernel.specVersion lb le).encode = bytes ∧
      lb.Pairwise (fun p q => p.1.idx < q.1.idx) ∧ le.Pairwise (fun p q => p.1.idx < q.1.idx) ∧
      LoadedNode h₁ x_tbl a lb le ∧
      Heap.Extends hE h₁ ∧
      RoleMapEntries roleEvMapEnum hE evEnts evMap ∧ EvidenceEntriesOf hE le evEnts ∧
      ObsFn W "KernelRoles::evidence_roles_have_equations" [evMap] hE v hE' csE := by
  have hext : Heap.Extends h h₁ := ev.heap_extends
  have ha₁ : S0.addr h₁ x_a a := S0.addr_mono hext ha
  obtain ⟨v1, m14, cs24, x_idx, x_len, v55, m56, cs66, v92, m93, cs103,
    m123, cs133, x_t0, x_s, v168, m171, cs179, m198, cs208, x_t1, x_s_222,
    v244, m247, cs255, m274, cs284, x_version, x_s_298, v320, v321, m323, cs331,
    m343, cs351, m356, cs366, x_n, x_s_380, m392, cs402, v406, m417, cs425,
    x_by_role, x_by_addr, x__next, x_s_454, m476, cs486, x_m, x_s_500,
    m512, cs522, v526, m536, cs544, x_evidence, x__next_564, x_s_565,
    v581, m582, cs592, m619, v665, m666, cs676,
    ld11, ev26, ev68, ev105, ev135, ev181, heq196, ev210, ev257, heq272,
    ev286, ev333, ev353, heq354, ev368, ev427, ev404, ev488, ev546, ev524,
    ev594, ld613, hm629, ev678, rfl, rfl, hc636⟩ := Obs.«KernelRoles::load_role_table».obs ev
  obtain ⟨ab, hab, hix_b⟩ := ha
  have hv1 : v1 = L1.digestV ab := L1.load_repAddressRef hab ld11
  obtain ⟨bytes, _, ext1, ext2, hst, hcall, hproj⟩ := L1.checked_read ev26 ev68 ev105
  have hhashed : Hashed cs ⟨bytes.toArray⟩ :=
    L1.hashed_of_call (by rw [hc636]; simp [hcall]) hst
  have hblk : Address.blake3Pure ⟨bytes.toArray⟩ = a := by
    rw [L1.blake3Pure_eq, L1.digest_eq_of_proj hv1 hproj]
    exact hix_b
  have hst0 : L1.Stream m93 bytes v55 := hst.mono ext2
  -- the header
  obtain ⟨rfl, b0, r0, p0, rfl, hs0, ht0⟩ := Deserialize.readByte_refines hst0 ev135.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht0
  obtain ⟨rfl, rfl⟩ := ht0
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev181
  have hb0 : b0 = (232 : Nat).toUInt8 :=
    byte_eq_of_toNat (byte_of_field (n := 232) (by decide) (by simpa using heq196.symm))
  obtain ⟨rfl, b1, r1, p1, rfl, hs1, ht1⟩ := Deserialize.readByte_refines hs0 ev210.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht1
  obtain ⟨rfl, rfl⟩ := ht1
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev257
  have hb1 : b1 = (3 : Nat).toUInt8 :=
    byte_eq_of_toNat (byte_of_field (n := 3) (by decide) (by simpa using heq272.symm))
  obtain ⟨rfl, b2, r2, p2, rfl, hs2, ht2⟩ := Deserialize.readByte_refines hs1 ev286.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht2
  obtain ⟨rfl, rfl⟩ := ht2
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev333
  obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::spec_version».obs ev353
  have hb2 : b2 = (4 : Nat).toUInt8 :=
    byte_eq_of_toNat (byte_of_field (n := 4) (by decide) (by simpa using heq354.symm))
  obtain ⟨rfl, b3, r3, p3, rfl, hs3, ht3⟩ := Deserialize.readByte_refines hs2 ev368.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht3
  obtain ⟨rfl, rfl⟩ := ht3
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev427
  -- the bindings
  have hbst0 : ∀ hh : Heap F, Claim.RBTreeBST .field hh []
      (.construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []) := by
    intro hh
    change Claim.RBTreeBST .field _ [] (.construct addrMapEnum "Nil" [])
    rw [← Claim.rbtreeEnum_field]
    exact Claim.RBTreeBST.nil .field _
  obtain ⟨extB, lb, restB, roleMap, byAddr', restPtr, nxt', ents, es', htup, hlenB, hbsB, hsB,
    hascB, -, -, -, hent, hbnd, hbst, hidx⟩ :=
    read_role_bindings_parse b3.toNat (UInt8.toNat_lt b3) 0 [] (by omega) (hbst0 _) (by simp) hs3
      (by rw [Nat.cast_zero]; exact ev404)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  obtain ⟨rfl, rfl, -, rfl⟩ := htup
  subst hbsB
  -- the evidence
  obtain ⟨rfl, b4, r4, p4, rfl, hs4, ht4⟩ := Deserialize.readByte_refines hsB ev488.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht4
  obtain ⟨rfl, rfl⟩ := ht4
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev546
  obtain ⟨extE, le, restE, evMap, restPtrE, nxtE, evEnts, htupE, hlenE, hbsE, hsE, hascE, -, -,
    -, hokE, hentE, hevE⟩ :=
    read_role_evidence_parse b4.toNat (UInt8.toNat_lt b4) 0 (by omega) hs4
      (by rw [Nat.cast_zero]; exact ev524)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupE
  obtain ⟨rfl, -, rfl⟩ := htupE
  subst hbsE
  -- the end of the stream
  rcases L1.stream_inv (hsE.mono ev594.heap_extends) ld613 with ⟨rfl, -⟩ | ⟨x, xs, tl, -, hv, -⟩
  swap
  · injection hv with _ hc _
    exact absurd hc (by decide)
  -- the node
  subst hm629
  have extN : Heap.Extends (m582 ++ [.construct rtEnum "Mk" [x_a, x_by_role, x_by_addr,
      x_evidence]]) m666 := ev678.heap_extends
  have extEv : Heap.Extends m512 m666 :=
    ev594.heap_extends.trans ((Heap.Extends.snoc m582 _).trans extN)
  have extBn : Heap.Extends m392 m666 :=
    ev488.heap_extends.trans (ev546.heap_extends.trans (ev524.heap_extends.trans extEv))
  have hlenB' : lb.length.toUInt8 = b3 := by
    rw [hlenB, Ix.Kernel.RoleTable.toNat_toUInt8]
  have hlenE' : le.length.toUInt8 = b4 := by
    rw [hlenE, Ix.Kernel.RoleTable.toNat_toUInt8]
  refine ⟨_, lb, le, m512, x_evidence, v581, m582, cs592, evEnts, hhashed, hblk, ?_, ?_, hascB,
    hascE, ⟨x_a, x_by_role, x_by_addr, x_evidence, ents, es', evEnts,
      extN.loadValue_eq (Claim.loadValue_snoc_construct m582 rtEnum "Mk"
        [x_a, x_by_role, x_by_addr, x_evidence]),
      ha₁, hent.mono extBn, hbnd.mono extBn, hbst.mono extBn, hidx, hentE.mono extEv,
      hevE.mono extEv⟩, extEv, hentE, hevE, ev594⟩
  · rw [Ix.Kernel.RoleTable.wireWF_iff]
    refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [parsedTable, List.size_toArray, List.length_map, hlenB]
      exact UInt8.toNat_lt b3
    · simp only [parsedTable, List.size_toArray, List.length_map, hlenE]
      exact UInt8.toNat_lt b4
    · intro p hp
      simp only [parsedTable, List.toList_toArray, List.mem_map] at hp
      obtain ⟨q, -, rfl⟩ := hp
      simp [ixAddr, ByteArray.size]
    · intro p hp
      simp only [parsedTable, List.toList_toArray, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      obtain ⟨hq1, hq2⟩ := hokE q hq
      refine ⟨by simpa using hq1, ?_⟩
      intro e he
      simp only [List.toList_toArray] at he
      exact hq2 e he
    · simp only [parsedTable, List.toList_toArray]
      exact ascending_of_pairwise (List.pairwise_map.mpr hascB)
    · simp only [parsedTable, List.toList_toArray]
      exact ascending_of_pairwise (List.pairwise_map.mpr hascE)
  · rw [hb0, hb1, hb2, ← hlenB', ← hlenE']
    simp only [parsedTable, Ix.Kernel.RoleTable.encode, List.size_toArray, List.length_map,
      List.toList_toArray, flatMap_map', List.append_nil]
    rfl

end IxVM.Refinement.RoleVal
