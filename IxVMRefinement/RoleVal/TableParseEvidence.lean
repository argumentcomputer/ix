import IxVMRefinement.RoleVal.TableParse

/-! # The evidence readers of `KernelRoles::load_role_table`, parsed

`read_evidence_entries` and `read_role_evidence` in the parse direction: the stream begins with
the encodings of the entries read, and the evidence map returned has exactly those entries
(`RoleMapEntries`, each value representing the entry's evidence list).
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

/-- A byte whose number is `n` is `n`'s byte. -/
theorem byte_eq_of_toNat {b : UInt8} {n : Nat} (h : b.toNat = n) : b = n.toUInt8 := by
  rw [← Ix.Kernel.RoleTable.toNat_toUInt8 b, h]

/-- The byte read under `UInt8::to_field` equal to a small literal. -/
theorem byte_of_field {b : UInt8} {n : Nat} (hn : n < 256)
    (h : (Value.field (n : F) : SourceValue F) = .field (b.toNat : F)) : b.toNat = n := by
  have hb := UInt8.toNat_lt b
  exact (Claim.natCast_inj_of_lt_u32 (by omega) (by omega) (Value.field.inj h)).symm

/-- **`KernelRoles::read_evidence_entries(s, k)`, parsed**: the stream begins with the
encodings of `k` evidence entries (each `defeq`, or `proof` at a 32-byte address), and the list
returned represents them. -/
theorem read_evidence_entries_parse :
    ∀ (k : Nat), k < 256 →
      ∀ {bs : List UInt8} {x_s r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        Ingress.Stream h bs x_s →
        ObsFn W "KernelRoles::read_evidence_entries" [x_s, .field (k : F)] h r h' calls →
        Heap.Extends h h' ∧
        ∃ (es : List (Ix.Kernel.Evidence _root_.Address)) (rest : List UInt8)
          (entriesPtr restPtr : SourceValue F),
          r = .tuple [entriesPtr, restPtr] ∧ es.length = k ∧
          (∀ e ∈ es, Ix.Kernel.RoleTable.Evidence.wide e = true) ∧
          bs = es.flatMap Ix.Kernel.RoleTable.encEvidence ++ rest ∧
          RepList evListEnum EvRep h' es entriesPtr ∧ Ingress.Stream h' rest restPtr := by
  intro k
  induction k with
  | zero =>
    intro hk bs x_s r h h' calls hs ev
    rcases Obs.«KernelRoles::read_evidence_entries».obs ev with
      ⟨m21, _, rfl, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hne42, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hne42, -⟩
    · have ext := Heap.Extends.snoc h (.construct evListEnum "Nil" [])
      exact ⟨ext, [], bs, _, x_s, rfl, rfl, by simp, by simp, .nil (by simp), hs.mono ext⟩
    · simp at hne42
    · simp at hne42
  | succ k' ih =>
    intro hk bs x_s r h h' calls hs ev
    have hcnt_ne : (.field ((k' + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
      intro heq
      have h0 : ((k' + 1 : Nat) : F) = ((0 : Nat) : F) := by simpa using Value.field.inj heq
      have := Claim.natCast_inj_of_lt_u32 (by omega) (by decide) h0
      omega
    have hv : (((k' + 1 : Nat) : F) - 1) = (k' : F) := by push_cast; ring
    rcases Obs.«KernelRoles::read_evidence_entries».obs ev with
      ⟨_, hv14, -⟩ |
      ⟨m47, cs57, x_tag, x_s_71, m83, cs94, m110, cs120, v124, x_rest, x_s_150, m167,
        _, ev59, ev96, op145, ev122, rfl, rfl, rfl, -⟩ |
      ⟨m47, cs57, x_tag, x_s_71, m83, cs94, m212, cs222, x_a, x_s_236, m248, cs258,
        v262, x_rest, x_s_288, m305, _, ev59, ev96, ev224, op283, ev260, rfl, rfl, rfl, -⟩
    · exact absurd hv14 hcnt_ne
    · obtain ⟨rfl, b, bs1, sPtr1, rfl, hs1, htag⟩ := Deserialize.readByte_refines hs ev59.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htag
      obtain ⟨rfl, rfl⟩ := htag
      obtain ⟨h0, rfl⟩ := Lib.u8_to_field_spec ev96
      have hb : b = (0 : Nat).toUInt8 :=
        byte_eq_of_toNat (byte_of_field (n := 0) (by decide) (by simpa using h0))
      simp only [evalBinOp, Except.ok.injEq] at op145
      subst op145
      rw [hv] at ev122
      obtain ⟨ext1, es', rest, entriesPtr, restPtr', htuple, hlen, hwide, hbs, hrep, hs'⟩ :=
        ih (by omega) hs1 ev122
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htuple
      obtain ⟨rfl, rfl⟩ := htuple
      let node := Value.construct evListEnum "Cons" [.construct evEnum "Defeq" [], x_rest]
      have ext2 := Heap.Extends.snoc m110 node
      refine ⟨ext1.trans ext2, .defeq :: es', rest, _, x_s_150, rfl, by simp [hlen], ?_, ?_,
        ?_, hs'.mono ext2⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact hwide e he
      · rw [hb, hbs]
        rfl
      · exact .cons (by simp [node, List.getElem?_concat_length]) (.inl ⟨rfl, rfl⟩)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext2 hrep)
    · obtain ⟨rfl, b, bs1, sPtr1, rfl, hs1, htag⟩ := Deserialize.readByte_refines hs ev59.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htag
      obtain ⟨rfl, rfl⟩ := htag
      obtain ⟨h1, rfl⟩ := Lib.u8_to_field_spec ev96
      have hb : b = (1 : Nat).toUInt8 :=
        byte_eq_of_toNat (byte_of_field (n := 1) (by decide) (by simpa using h1))
      obtain ⟨ext_addr, hlen_a, addrPtr, sPtr2, haddr_tup, haddr_rep, hs2⟩ :=
        Deserialize.getAddress_refines hs1 ev224.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
      obtain ⟨rfl, rfl⟩ := haddr_tup
      obtain ⟨a', ha'⟩ : ∃ a', Deserialize.takeAddress bs1 hlen_a = a' := ⟨_, rfl⟩
      rw [ha'] at haddr_rep
      simp only [evalBinOp, Except.ok.injEq] at op283
      subst op283
      rw [hv] at ev260
      obtain ⟨ext1, es', rest, entriesPtr, restPtr', htuple, hlen, hwide, hbs, hrep, hs'⟩ :=
        ih (by omega) hs2 ev260
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htuple
      obtain ⟨rfl, rfl⟩ := htuple
      let node := Value.construct evListEnum "Cons" [.construct evEnum "Proof" [x_a], x_rest]
      have ext2 := Heap.Extends.snoc m248 node
      refine ⟨ext_addr.trans (ext1.trans ext2), .proof (ixAddr a') :: es', rest, _, x_s_288, rfl,
        by simp [hlen], ?_, ?_, ?_, hs'.mono ext2⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · simp [Ix.Kernel.RoleTable.Evidence.wide, ixAddr, ByteArray.size]
        · exact hwide e he
      · have hb1 : bs1 = a'.toList ++ bs1.drop 32 := by
          rw [← ha', takeAddress_toList hlen_a, List.take_append_drop]
        rw [hb, hb1, hbs]
        simp only [List.flatMap_cons, Ix.Kernel.RoleTable.encEvidence, encAddr_ixAddr,
          List.cons_append, List.append_assoc]
        rfl
      · exact .cons List.getElem?_concat_length (.inr ⟨a', x_a, rfl, rfl,
          Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) haddr_rep⟩)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext2 hrep)

/-- The evidence map's entries are the entries read, in order, each representing its list. -/
def EvidenceEntriesOf (h : Heap F)
    (le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address)))
    (ents : List (Nat × SourceValue F)) : Prop :=
  List.Forall₂ (fun p q => q.1 = p.1.idx ∧ RepList evListEnum EvRep h p.2 q.2) le ents

theorem EvidenceEntriesOf.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address))}
    {ents : List (Nat × SourceValue F)}
    (hb : EvidenceEntriesOf h₁ le ents) : EvidenceEntriesOf h₂ le ents :=
  forall₂_imp (fun _ _ ⟨hk, hl⟩ => ⟨hk, repList_heapMono₂ evListEnum evRep_heapMono₂ ext hl⟩) hb

/-- **`KernelRoles::read_role_evidence(s, n, next)`, parsed**: the stream begins with the
encodings of `n` entries of strictly ascending roles from `next` on, each with fewer than 256
wide evidence entries; the evidence map returned has exactly those entries, in order. -/
theorem read_role_evidence_parse :
    ∀ (n : Nat), n < 256 →
    ∀ (nxt : Nat) {bs : List UInt8} {x_s r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      nxt ≤ 108 → Ingress.Stream h bs x_s →
      ObsFn W "KernelRoles::read_role_evidence" [x_s, .field (n : F), .field (nxt : F)] h r h'
        calls →
      Heap.Extends h h' ∧
      ∃ (le : List (Ix.Kernel.Role × List (Ix.Kernel.Evidence _root_.Address)))
        (rest : List UInt8) (evMap restPtr : SourceValue F) (nxt' : Nat)
        (ents : List (Nat × SourceValue F)),
        r = .tuple [evMap, .field (nxt' : F), restPtr] ∧ le.length = n ∧
        bs = le.flatMap (fun p => Ix.Kernel.RoleTable.encEntry (p.1, p.2.toArray)) ++ rest ∧
        Ingress.Stream h' rest restPtr ∧
        le.Pairwise (fun p q => p.1.idx < q.1.idx) ∧
        nxt ≤ nxt' ∧ nxt' ≤ 108 ∧ (∀ p ∈ le, nxt ≤ p.1.idx ∧ p.1.idx < nxt') ∧
        (∀ p ∈ le, p.2.length < 256 ∧ ∀ e ∈ p.2, Ix.Kernel.RoleTable.Evidence.wide e = true) ∧
        RoleMapEntries roleEvMapEnum h' ents evMap ∧ EvidenceEntriesOf h' le ents := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn nxt bs x_s r h h' calls hnxt hs ev
    cases n with
    | zero =>
      rcases Obs.«KernelRoles::read_role_evidence».obs ev with
        ⟨_, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hne46, -⟩
      · exact ⟨Heap.Extends.refl _, [], bs, _, x_s, nxt, [], rfl, rfl, by simp, hs,
          List.Pairwise.nil, le_refl _, hnxt, by simp, by simp, .nil, List.Forall₂.nil⟩
      · simp at hne46
    | succ n' =>
      rcases Obs.«KernelRoles::read_role_evidence».obs ev with
        ⟨hv14, -⟩ |
        ⟨m51, cs61, x_b0, w75, w76, w77, w78, w79, w80, w81, v122, x130, m149, cs159,
          x_left, x_next_189, x_s_190, m207, cs217, x_rb, x_s_231, v242, m243, cs253,
          v275, m278, cs286, v290, m299, cs307, v328, m331, cs339, m366, cs376,
          x_kb, x_s_390, m402, cs412, v416, m425, cs433, x_entries, x_s_447, m459, cs469,
          v473, v474, y489, x_right, x_next_524, x_s_525, m582, m593,
          _, ev63, op145, op137, ev161, ev219, ev255, ev309, ev288, heqA, ev341, heqB,
          ev378, ev435, ev414, op504, op495, op519, ev471, rfl, rfl, rfl, rfl, -⟩
      · exfalso
        have h0 : ((n' + 1 : Nat) : F) = ((0 : Nat) : F) := by
          simpa using Value.field.inj hv14
        have := Claim.natCast_inj_of_lt_u32 (by omega) (by decide) h0
        omega
      · obtain ⟨rfl, rfl, rfl⟩ := count_halves (by omega) hn ev63 op145 op137 op504 op495
        obtain ⟨extL, leL, restL, evL, sL, nxtL, entsL, htupL, hlenL, hbsL, hsL, hascL, hnxtL1,
          hnxtL2, hrangeL, hokL, hentL, hevL⟩ :=
          ih ((n' + 1) / 2) (by omega) (by omega) nxt hnxt hs ev161
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupL
        obtain ⟨rfl, rfl, rfl⟩ := htupL
        -- the role byte
        obtain ⟨rfl, rb, bs1, sPtr1, rfl, hs1, htag⟩ := Deserialize.readByte_refines hsL ev219.erase
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htag
        obtain ⟨rfl, rfl⟩ := htag
        obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev255
        obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_count».obs ev309
        have hrb256 : rb.toNat < 256 := UInt8.toNat_lt rb
        obtain ⟨h108, -, rfl⟩ := lt_fields_nat (a := rb.toNat) (b := 108) (by omega) (by decide)
          (by rw [Nat.cast_ofNat]; exact ev288)
        have hrb108 : rb.toNat < 108 := h108 heqA
        obtain ⟨-, hgeN, rfl⟩ := lt_fields_nat (a := rb.toNat) (b := nxtL) (by omega) (by omega)
          ev341
        have hge : nxtL ≤ rb.toNat := Nat.le_of_not_lt (hgeN heqB)
        obtain ⟨ro, hro⟩ := exists_role_of_lt hrb108
        -- the evidence count and the entries
        obtain ⟨rfl, kb, bs2, sPtr2, rfl, hs2, htag2⟩ := Deserialize.readByte_refines hs1 ev378.erase
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htag2
        obtain ⟨rfl, rfl⟩ := htag2
        obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev435
        obtain ⟨extE, es, restE, entriesPtr, restPtrE, htupE, hlenE, hwideE, hbsE, hrepE, hsE⟩ :=
          read_evidence_entries_parse kb.toNat (UInt8.toNat_lt kb) hs2 ev414
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupE
        obtain ⟨rfl, rfl⟩ := htupE
        -- the right subtree
        obtain rfl := RolesAux.evalBinOp_add_field_inv op519
        have hnext_eq : ((rb.toNat : F) + 1) = ((ro.idx + 1 : Nat) : F) := by
          rw [← hro, Nat.cast_add, Nat.cast_one]
        rw [hnext_eq] at ev471
        obtain ⟨extR, leR, restR, evR, sR, nxtR, entsR, htupR, hlenR, hbsR, hsR, hascR, hnxtR1,
          hnxtR2, hrangeR, hokR, hentR, hevR⟩ :=
          ih ((n' + 1) - ((n' + 1) / 2 + 1)) (by omega) (by omega) (ro.idx + 1) (by omega) hsE
            ev471
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupR
        obtain ⟨rfl, rfl, rfl⟩ := htupR
        -- the node
        have extSnoc1 := Heap.Extends.snoc m459 x_left
        have extSnoc2 := Heap.Extends.snoc (m459 ++ [x_left]) x_right
        have extPost := extSnoc1.trans extSnoc2
        have extMid := extE.trans (extR.trans extPost)
        have ldL : loadValue ((m459 ++ [x_left]) ++ [x_right]) (.ptr x_left.type m459.length) =
            .ok x_left := extSnoc2.loadValue_eq (Ingress.loadValue_snoc m459 x_left)
        have ldR : loadValue ((m459 ++ [x_left]) ++ [x_right])
            (.ptr x_right.type (m459 ++ [x_left]).length) = .ok x_right :=
          Ingress.loadValue_snoc (m459 ++ [x_left]) x_right
        refine ⟨extL.trans extMid, leL ++ [(ro, es)] ++ leR, restR, _, _, nxtR,
          entsL ++ [(rb.toNat, x_entries)] ++ entsR, rfl, ?_, ?_, hsR.mono extPost, ?_,
          by omega, hnxtR2, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton, hlenL, hlenR]
          omega
        · have hrb : ro.idx.toUInt8 = rb := by
            rw [hro, Ix.Kernel.RoleTable.toNat_toUInt8]
          have hkb : es.length.toUInt8 = kb := by
            rw [hlenE, Ix.Kernel.RoleTable.toNat_toUInt8]
          rw [hbsL, hbsE, hbsR]
          simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            Ix.Kernel.RoleTable.encEntry, List.size_toArray, List.toList_toArray, hrb, hkb,
            List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
        · rw [List.pairwise_append, List.pairwise_append]
          refine ⟨⟨hascL, List.pairwise_singleton _ _, ?_⟩, hascR, ?_⟩
          · intro p hp q hq
            rw [List.mem_singleton] at hq
            subst hq
            have := (hrangeL p hp).2
            show p.1.idx < ro.idx
            omega
          · intro p hp q hq
            have hq' := (hrangeR q hq).1
            rcases List.mem_append.mp hp with hp | hp
            · have := (hrangeL p hp).2
              omega
            · rw [List.mem_singleton] at hp
              subst hp
              show ro.idx < q.1.idx
              omega
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · rcases List.mem_append.mp hp with hp | hp
            · have := hrangeL p hp
              omega
            · rw [List.mem_singleton] at hp
              subst hp
              show nxt ≤ ro.idx ∧ ro.idx < nxtR
              omega
          · have := hrangeR p hp
            omega
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · rcases List.mem_append.mp hp with hp | hp
            · exact hokL p hp
            · rw [List.mem_singleton] at hp
              subst hp
              refine ⟨?_, hwideE⟩
              show es.length < 256
              rw [hlenE]
              exact UInt8.toNat_lt kb
          · exact hokR p hp
        · exact .node ldL ldR (hentL.mono extMid) (hentR.mono extPost)
        · refine forall₂_append (forall₂_append (hevL.mono extMid) ?_) (hevR.mono extPost)
          exact .cons ⟨hro.symm,
            repList_heapMono₂ evListEnum evRep_heapMono₂ (extR.trans extPost) hrepE⟩ .nil

end IxVM.Refinement.RoleVal
