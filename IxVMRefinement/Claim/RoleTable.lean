import IxVMRefinement.Claim.RBTree
import IxVMRefinement.Core.Roles
import IxVMRefinement.Core.Seams
import IxVMRefinement.L1.Hashed
import IxVMRefinement.Obs.KernelRoles
import IxVMRefinement.Obs.KernelRoleSpec0
import Ix.IxVM.Consistency.Statement
import Ix.Cert.RoleClosure
import IxC.Kernel.Ixon.RoleTableInj

/-! # Role-table decoding, context loading, and role lookups for L6

Refinement of `KernelRoles` and `KernelRoleSpec` operations exercised during `ClaimPhase`:
* `admitBinding_inv` and `readerTable_admits`: an admitted binding `b` has
  `Address.blake3Pure b.bytes = b.address`, `t.wireWF = true`, `b.bytes = t.toBytes`
  (`b.bytes.data.toList = t.encode`), and `t.wf = true`.
* `TableFullRep` / `RCFullRep`: enriches `Core.TableRep` and `Core.RCRep` with the exact
  `RBTreeBST` address-to-role map so both soundness (`t.addressOf? ro = some a`) and
  completeness (`(ro, a) ∈ t.bound.toList → found`) hold.
* `load_role_table_spec`, `load_role_ctx_spec`, `role_ctx_for_validator_spec`.
* `role_ctx_table_spec`, `role_ctx_binding_spec`, `role_ctx_validator_spec`,
  `role_ctx_axioms_spec`, `role_ctx_limit_spec`, `role_addr_index_spec`, `role_index_of_spec`,
  `role_is_inert_spec` (`r = .field 0 → ¬ InertAt t a`), `walk_covered_spec`, `walk_ctx_spec`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

/-! ## Call-list monotonicity for `Hashed` and `View.HashedCollision` -/

theorem hashed_mono {cs₁ cs₂ : List (Call F)} (hsub : ∀ c ∈ cs₁, c ∈ cs₂) {bytes : ByteArray}
    (hh : Hashed cs₁ bytes) : Hashed cs₂ bytes := by
  obtain ⟨c, hc, hn, inp, ha, hs⟩ := hh
  exact ⟨c, hsub c hc, hn, inp, ha, hs⟩

theorem hashedCollision_mono {V : View} {extra : List ByteArray} {cs₁ cs₂ : List (Call F)}
    (hsub : ∀ c ∈ cs₁, c ∈ cs₂) (hc : V.HashedCollision extra cs₁) :
    V.HashedCollision extra cs₂ := by
  rcases hc with ⟨x, held, bytes, hsrc, hh, hne, hblk⟩ | ⟨bytes, hsrc, hpad⟩
  · refine .inl ⟨x, held, bytes, ?_, hashed_mono hsub hh, hne, hblk⟩
    rcases hsrc with hp | hex | ⟨hh0, hb0⟩
    · exact .inl hp
    · exact .inr (.inl hex)
    · exact .inr (.inr ⟨hashed_mono hsub hh0, hb0⟩)
  · refine .inr ⟨bytes, ?_, hpad⟩
    rcases hsrc with hp | hh
    · exact .inl hp
    · exact .inr (hashed_mono hsub hh)

/-! ## Admission & canonical encoding facts -/

theorem admitBinding_inv {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    Address.blake3Pure b.bytes = b.address ∧
    t.wireWF = true ∧
    b.bytes = t.toBytes ∧
    b.bytes.data.toList = t.encode ∧
    t.check = .ok () ∧
    t.wf = true := by
  unfold Ix.Kernel.Admission.admitBinding at hadm
  by_cases hh : Address.admissionHash b.bytes = b.address
  case neg =>
    simp [hh, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hadm
  simp only [hh, decide_true, Bool.true_eq_false, ↓reduceIte, pure, Except.pure,
    bind, Except.bind] at hadm
  cases hof : Ix.Kernel.RoleTable.ofBytes b.bytes with
  | none =>
    simp [hof, throw, throwThe, MonadExceptOf.throw] at hadm
  | some t' =>
    simp only [hof] at hadm
    cases hchk : t'.check with
    | error e =>
      simp [hchk, Except.mapError] at hadm
    | ok u =>
      cases u
      simp only [hchk, Except.mapError, Except.ok.injEq] at hadm
      subst hadm
      obtain ⟨hwf_wire, hto⟩ := (Ix.Kernel.RoleTable.ofBytes_eq_some_iff b.bytes t').mp hof
      have hlist : b.bytes.data.toList = t'.encode := by
        rw [← hto, Ix.Kernel.RoleTable.toBytes]
      have hwf : t'.wf = true := by
        unfold Ix.Kernel.RoleTable.wf
        rw [hchk]
        rfl
      exact ⟨hh, hwf_wire, hto.symm, hlist, hchk, hwf⟩

theorem readerTable_admits {c : Claim} {V : View} {b : Ix.Kernel.Admission.Binding}
    (hDef : Ix.Cert.RoleClosure.DefaultAdmits)
    (hRT : IxVM.Consistency.ReaderTable c V b) :
    ∃ t : Ix.Kernel.RoleTable,
      Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t := by
  rcases hRT.2 with hdef | ⟨t, hadm, -, -⟩
  · obtain ⟨b', t, hdef', hadm⟩ := hDef
    rw [hdef] at hdef'
    injection hdef' with hb
    subst hb
    exact ⟨t, hadm⟩
  · exact ⟨t, hadm⟩

theorem check_roles_nodup {t : Ix.Kernel.RoleTable} (hchk : t.check = .ok ()) :
    (t.bound.toList.map (·.1)).Nodup := by
  unfold Ix.Kernel.RoleTable.check at hchk
  by_cases hv : (t.version == Ix.SpecDigest.specVersion) = true
  case neg =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at hchk
    obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hchk
    simp [throw, throwThe, MonadExceptOf.throw] at h1
  by_cases hn : (List.map (fun x => x.fst) t.bound.toList).Nodup
  · exact hn
  · simp only [hv, hn, ↓reduceIte] at hchk
    obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hchk
    simp [throw, throwThe, MonadExceptOf.throw] at h1

private theorem find_fst_of_mem_nodup {l : List (Ix.Kernel.Role × _root_.Address)}
    (hnd : (l.map (·.1)).Nodup) {ro : Ix.Kernel.Role} {a : _root_.Address}
    (hm : (ro, a) ∈ l) :
    (l.find? (·.1 == ro)).map (·.2) = some a := by
  induction l with
  | nil => cases hm
  | cons p ls ih =>
    rcases p with ⟨r', a'⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.find?]
    by_cases heq : (r' == ro) = true
    · rw [heq]
      have hr : r' = ro := beq_iff_eq.mp heq
      subst hr
      rcases List.mem_cons.mp hm with hhead | htail
      · injection hhead with _ ha
        subst ha
        rfl
      · exact absurd (List.mem_map_of_mem (f := (·.1)) htail) hnd.1
    · have hfalse : (r' == ro) = false := Bool.eq_false_iff.mpr heq
      rw [hfalse]
      rcases List.mem_cons.mp hm with hhead | htail
      · injection hhead with hr _
        subst hr
        exact absurd (beq_self_eq_true r') heq
      · exact ih hnd.2 htail

theorem addressOf_eq_some_of_mem_bound {t : Ix.Kernel.RoleTable}
    (hchk : t.check = .ok ()) {ro : Ix.Kernel.Role} {a : _root_.Address}
    (hm : (ro, a) ∈ t.bound.toList) :
    t.addressOf? ro = some a := by
  unfold Ix.Kernel.RoleTable.addressOf?
  rw [← Array.find?_toList]
  exact find_fst_of_mem_nodup (check_roles_nodup hchk) hm

theorem mem_bound_of_addressOf_eq_some {t : Ix.Kernel.RoleTable}
    {ro : Ix.Kernel.Role} {a : _root_.Address}
    (ha : t.addressOf? ro = some a) :
    (ro, a) ∈ t.bound.toList := by
  unfold Ix.Kernel.RoleTable.addressOf? at ha
  rw [← Array.find?_toList] at ha
  cases hf : t.bound.toList.find? (·.1 == ro) with
  | none => rw [hf] at ha; cases ha
  | some p =>
    rw [hf] at ha
    rcases p with ⟨r', a'⟩
    simp only [Option.map, Option.some.injEq] at ha
    subst ha
    have hmem := List.mem_of_find?_eq_some hf
    have heq : (r' == ro) = true := List.find?_some hf
    have hr : r' = ro := beq_iff_eq.mp heq
    subst hr
    exact hmem

/-! ## Enriched role-table and role-context representations -/

/-- `byAddr` holds a valid `RBTreeBST` of `IndexEntry t` pairs covering `seen`. -/
def ByAddrInv (t : Ix.Kernel.RoleTable) (seen : List (Ix.Kernel.Role × _root_.Address))
    (h : Heap F) (byAddr : SourceValue F) : Prop :=
  ∃ es : List (Bytes.Address × SourceValue F),
    RBTreeBST .field h es byAddr ∧
    (∀ p ∈ es, IndexEntry t h p.1 p.2) ∧
    (∀ ro a, (ro, a) ∈ seen →
      ∃ b : Bytes.Address, ixAddr b = a ∧ (b, .field (roleNum ro + 1)) ∈ es)

theorem ByAddrInv.mono {t : Ix.Kernel.RoleTable} {seen : List (Ix.Kernel.Role × _root_.Address)}
    {h₁ h₂ : Heap F} {byAddr : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hinv : ByAddrInv t seen h₁ byAddr) :
    ByAddrInv t seen h₂ byAddr := by
  obtain ⟨es, hbst, hie, hmem⟩ := hinv
  exact ⟨es, hbst.mono ext, fun p hp => hie p hp, hmem⟩

theorem addrMapAll_of_rbtreeEntries {t : Ix.Kernel.RoleTable} {h : Heap F}
    {es : List (Bytes.Address × SourceValue F)} {tree : SourceValue F}
    (hent : RBTreeEntries .field h es tree)
    (hie : ∀ p ∈ es, IndexEntry t h p.1 p.2) :
    AddrMapAll addrMapEnum (IndexEntry t) h tree := by
  induction hent with
  | nil =>
    rw [rbtreeEnum_field]
    exact .nil
  | @node _ ak vk _ _ _ _ ls rs hk hl hr _ _ ihl ihr =>
    rw [rbtreeEnum_field]
    refine .node hk (hie (ak, vk) (by simp)) hl hr (ihl ?_) (ihr ?_)
    · intro p hp; exact hie p (by simp [hp])
    · intro p hp; exact hie p (by simp [hp])

/-- Full representation of a loaded `KernelRoles::RoleTable` node: `TableRep t`, plus the
binding pointer `bp` representing `bAddr`, `t.wf = true`, and full `ByAddrInv` coverage. -/
def TableFullRep (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (h : Heap F) (tbl : SourceValue F) : Prop :=
  t.wf = true ∧
  ∃ bp byRole byAddr ev,
    loadValue h tbl = .ok (.construct rtEnum "Mk" [bp, byRole, byAddr, ev]) ∧
    S0.addr h bp bAddr ∧
    RoleMapAll roleAddrMapEnum (BoundEntry t) h byRole ∧
    ByAddrInv t t.bound.toList h byAddr ∧
    RoleMapAll roleEvMapEnum (EvidenceEntry t) h ev

theorem TableFullRep.toTableRep {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {h : Heap F} {tbl : SourceValue F} (ht : TableFullRep t bAddr h tbl) :
    TableRep t h tbl := by
  obtain ⟨_, bp, byRole, byAddr, ev, hl, _, hbr, ⟨es, ⟨hent, _⟩, hie, _⟩, hev⟩ := ht
  exact ⟨bp, byRole, byAddr, ev, hl, hbr, addrMapAll_of_rbtreeEntries hent hie, hev⟩

theorem TableFullRep.mono {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {h₁ h₂ : Heap F} {tbl : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (ht : TableFullRep t bAddr h₁ tbl) :
    TableFullRep t bAddr h₂ tbl := by
  obtain ⟨hwf, bp, byRole, byAddr, ev, hl, ⟨ab, hab, hix⟩, hbr, hba, hev⟩ := ht
  refine ⟨hwf, bp, byRole, byAddr, ev, ext.loadValue_eq hl,
    ⟨ab, Bytes.repAddressRef_heapMono₂ addrTy ext hab, hix⟩, ?_, hba.mono ext, ?_⟩
  · refine RoleMapAll.mono ?_ ext hbr
    intro _ _ _ _ ext' ⟨r, a, hk, ha, hb⟩
    exact ⟨r, a, hk, Bytes.repAddressRef_heapMono₂ addrTy ext' ha, hb⟩
  · refine RoleMapAll.mono ?_ ext hev
    intro _ _ _ _ ext' ⟨r, es, hk, hm, hl'⟩
    exact ⟨r, es, hk, hm, repList_heapMono₂ evListEnum evRep_heapMono₂ ext' hl'⟩

/-- Full representation of a validating `KernelRoles::RoleCtx` (`Mk(tbl, lim, Nil)` with
`lim < 2^32`, empty user-axiom map `Nil`, and `TableFullRep t bAddr`). -/
def RCFullRep (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address) (lim : Nat)
    (h : Heap F) (rc : SourceValue F) : Prop :=
  lim < 4294967296 ∧
  ∃ tbl,
    loadValue h rc = .ok (.construct rcEnum "Mk"
      [tbl, .field (lim : F), .construct addrMapEnum "Nil" []]) ∧
    TableFullRep t bAddr h tbl

theorem RCFullRep.toRCRep {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {h : Heap F} {rc : SourceValue F} (hrc : RCFullRep t bAddr lim h rc) :
    RCRep t (some lim) h rc := by
  obtain ⟨hlim, tbl, hl, htbl⟩ := hrc
  exact ⟨tbl, .construct addrMapEnum "Nil" [], _, hl, .inl ⟨lim, rfl, hlim, rfl⟩, htbl.toTableRep⟩

theorem RCFullRep.mono {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {h₁ h₂ : Heap F} {rc : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hrc : RCFullRep t bAddr lim h₁ rc) :
    RCFullRep t bAddr lim h₂ rc := by
  obtain ⟨hlim, tbl, hl, htbl⟩ := hrc
  exact ⟨hlim, tbl, ext.loadValue_eq hl, htbl.mono ext⟩

/-! ## Arithmetic & stream helpers for balanced-tree decoding -/

private theorem twoF_ne_zero : (2 : F) ≠ 0 := by decide

private theorem toUInt8_toNat_of_lt {n : Nat} (hn : n < 256) : n.toUInt8.toNat = n := by
  change n % 256 = n
  exact Nat.mod_eq_of_lt hn

private theorem encAddr_length {a : _root_.Address} (hsz : a.hash.size = 32) :
    (Ix.Kernel.RoleTable.encAddr a).length = 32 := by
  unfold Ix.Kernel.RoleTable.encAddr
  simpa [ByteArray.size] using hsz

private theorem drop32_encAddr_append {a : _root_.Address} (hsz : a.hash.size = 32)
    (tail : List UInt8) :
    (Ix.Kernel.RoleTable.encAddr a ++ tail).drop 32 = tail := by
  have hl := encAddr_length hsz
  rw [← hl]
  exact List.drop_left' rfl

private theorem ixAddr_takeAddress_encAddr {a : _root_.Address} (hsz : a.hash.size = 32)
    (tail : List UInt8)
    (hlen : 32 ≤ (Ix.Kernel.RoleTable.encAddr a ++ tail).length) :
    ixAddr (Deserialize.takeAddress (Ix.Kernel.RoleTable.encAddr a ++ tail) hlen) = a := by
  have hl := encAddr_length hsz
  unfold ixAddr Deserialize.takeAddress
  dsimp only
  have htake : (Ix.Kernel.RoleTable.encAddr a ++ tail).take 32 = a.hash.data.toList := by
    rw [← hl, List.take_left' rfl]
    rfl
  rw [htake]
  cases a with
  | mk bs =>
    cases bs with
    | mk arr =>
      simp

private theorem count_halves {count : Nat} (hpos : 0 < count) (hlt : count < 256)
    {h m59 : Heap F} {cs69 : List (Call F)}
    {x_b0 w83 w84 w85 w86 w87 w88 w89 x138 v130 y556 v539 : SourceValue F}
    (ev71 : ObsFn W "UInt8::raw_bit_decomposition" [.field (count : F)] h
      (.tuple [x_b0, w83, w84, w85, w86, w87, w88, w89]) m59 cs69)
    (op153 : evalBinOp .sub (.field (count : F)) x_b0 = .ok x138)
    (op145 : evalBinOp .div x138 (.field 2) = .ok v130)
    (op571 : evalBinOp .add v130 (.field 1) = .ok y556)
    (op562 : evalBinOp .sub (.field (count : F)) y556 = .ok v539) :
    m59 = h ∧
    v130 = .field ((count / 2 : Nat) : F) ∧
    v539 = .field ((count - (count / 2 + 1) : Nat) : F) := by
  let b : UInt8 := UInt8.ofNatLT count hlt
  have hrep : Lib.RepU8 h b (.field (count : F)) := by
    show Value.field (count : F) = .field (b.toNat : F)
    rw [UInt8.toNat_ofNatLT]
  obtain ⟨htup, hm59⟩ := Lib.u8_raw_bit_decomposition_spec hrep ev71
  simp only [b, UInt8.toNat_ofNatLT, Value.tuple.injEq, List.cons.injEq] at htup
  obtain ⟨rfl, -⟩ := htup
  simp only [evalBinOp, Except.ok.injEq] at op153
  subst op153
  simp only [evalBinOp, twoF_ne_zero, ↓reduceIte, Except.ok.injEq] at op145
  subst op145
  have hdiv : ((count : F) - ((count % 2 : Nat) : F)) / 2 = ((count / 2 : Nat) : F) := by
    have e := congrArg (Nat.cast : Nat → F) (Nat.div_add_mod count 2)
    push_cast at e
    rw [div_eq_iff twoF_ne_zero]
    linear_combination -e
  rw [hdiv] at op571 ⊢
  simp only [evalBinOp, Except.ok.injEq] at op571
  subst op571
  simp only [evalBinOp, Except.ok.injEq] at op562
  subst op562
  have hrem : (count : F) - (((count / 2 : Nat) : F) + 1) =
      ((count - (count / 2 + 1) : Nat) : F) := by
    have hle : count / 2 + 1 ≤ count := by omega
    have e := congrArg (Nat.cast : Nat → F) (Nat.sub_add_cancel hle)
    push_cast at e
    linear_combination -e
  exact ⟨hm59, rfl, hrem.symm⟩

private theorem mem_insSorted_of_ne {a b : Bytes.Address} {v w : SourceValue F}
    {es : List (Bytes.Address × SourceValue F)}
    (hbw : (b, w) ∈ es) (hne : b ≠ a) :
    (b, w) ∈ insSorted a v es := by
  induction es with
  | nil => cases hbw
  | cons kw rest ih =>
    rcases kw with ⟨k, w0⟩
    unfold insSorted
    by_cases hlt : addrRank a < addrRank k
    · rw [ite_eq_left hlt]
      exact List.mem_cons_of_mem _ hbw
    · rw [ite_eq_right hlt]
      by_cases heq : a = k
      · rw [ite_eq_left heq]
        subst heq
        rcases List.mem_cons.mp hbw with hhead | htail
        · injection hhead with hbk _
          exact absurd hbk hne
        · exact List.mem_cons_of_mem _ htail
      · rw [ite_eq_right heq]
        rcases List.mem_cons.mp hbw with hhead | htail
        · rw [hhead]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih htail)

private theorem roleNum_add_one_ne_zero (ro : Ix.Kernel.Role) :
    (roleNum ro + 1 : F) ≠ 0 := by
  have hlt : ro.idx + 1 < 4294967296 := by
    have := ro.idx_lt
    omega
  intro heq
  have hcast : ((ro.idx + 1 : Nat) : F) = (0 : Nat) := by
    push_cast at *
    exact heq
  have := natCast_inj_of_lt_u32 hlt (by decide) hcast
  omega

/-! ## Specs for `read_evidence_entries`, `read_role_evidence`, `read_role_bindings` -/

theorem read_evidence_entries_spec (es : List (Ix.Kernel.Evidence _root_.Address))
    (hwide : ∀ e ∈ es, Ix.Kernel.RoleTable.Evidence.wide e = true)
    (hlt : es.length < 256)
    {rest : List UInt8} {x_s r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hs : L1.Stream h (es.flatMap Ix.Kernel.RoleTable.encEvidence ++ rest) x_s)
    (ev : ObsFn W "KernelRoles::read_evidence_entries"
      [x_s, .field (es.length : F)] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ entriesPtr restPtr,
      r = .tuple [entriesPtr, restPtr] ∧
      RepList evListEnum EvRep h' es entriesPtr ∧
      L1.Stream h' rest restPtr := by
  induction es generalizing h x_s r h' calls with
  | nil =>
    rcases Obs.«KernelRoles::read_evidence_entries».obs ev with
      ⟨m21, _, rfl, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hne42, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hne42, -⟩
    · simp only [List.flatMap_nil, List.nil_append] at hs
      have ext := Heap.Extends.snoc h (.construct evListEnum "Nil" [])
      exact ⟨ext, _, x_s, rfl, .nil (by simp [List.getElem?_concat_length]), hs.mono ext⟩
    · simp at hne42
    · simp at hne42
  | cons e es' ih =>
    have hwide_e : e.wide = true := hwide e List.mem_cons_self
    have hwide_es' : ∀ e' ∈ es', e'.wide = true :=
      fun e' hm => hwide e' (List.mem_cons_of_mem _ hm)
    have hlt' : es'.length < 256 := by simp at hlt; omega
    have hcnt_ne : (.field ((es'.length + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
      intro heq
      have h0 : ((es'.length + 1 : Nat) : F) = ((0 : Nat) : F) := by simpa using Value.field.inj heq
      have := natCast_inj_of_lt_u32 (by omega) (by decide) h0
      omega
    cases e with
    | defeq =>
      simp only [List.flatMap_cons, Ix.Kernel.RoleTable.encEvidence, List.singleton_append,
        List.length_cons] at hs ev
      rcases Obs.«KernelRoles::read_evidence_entries».obs ev with
        ⟨_, hv14, -⟩ |
        ⟨m47, cs57, x_tag, x_s_71, m83, cs94, m110, cs120, v124, x_rest, x_s_150, m167,
          _, ev59, ev96, op145, ev122, rfl, rfl, rfl, -⟩ |
        ⟨m47, cs57, x_tag, x_s_71, m83, cs94, _, _, _, _, _, _, _, _, _, _,
          _, ev59, ev96, -⟩
      · exact absurd hv14 hcnt_ne
      · obtain ⟨rfl, b, rest1, restPtr, hb, hs1, htag⟩ := Deserialize.readByte_refines hs ev59.erase
        injection htag with htag'
        simp only [List.cons.injEq, and_true] at htag'
        obtain ⟨rfl, rfl⟩ := htag'
        simp only [List.cons.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨_, rfl⟩ := Lib.u8_to_field_spec ev96
        simp only [evalBinOp, Except.ok.injEq] at op145
        subst op145
        have hv124 : (((es'.length + 1 : Nat) : F) - 1) = (es'.length : F) := by
          push_cast; ring
        rw [hv124] at ev122
        obtain ⟨ext1, entriesPtr, restPtr', htuple, hrep', hs'⟩ :=
          ih hwide_es' hlt' hs1 ev122
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htuple
        obtain ⟨rfl, rfl⟩ := htuple
        let node := Value.construct evListEnum "Cons"
          [.construct evEnum "Defeq" [], x_rest]
        have ext2 := Heap.Extends.snoc m110 node
        refine ⟨ext1.trans ext2, _, x_s_150, rfl, ?_, hs'.mono ext2⟩
        exact .cons (by simp [node, List.getElem?_concat_length]) (.inl ⟨rfl, rfl⟩)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext2 hrep')
      · obtain ⟨rfl, b, _, _, hb, _, htag⟩ := Deserialize.readByte_refines hs ev59.erase
        injection htag with htag'
        simp only [List.cons.injEq, and_true] at htag'
        obtain ⟨rfl, rfl⟩ := htag'
        simp only [List.cons.injEq] at hb
        obtain ⟨rfl, _⟩ := hb
        obtain ⟨heq, _⟩ := Lib.u8_to_field_spec ev96
        simp at heq
    | proof a =>
      have hsz : a.hash.size = 32 := by
        simpa [Ix.Kernel.RoleTable.Evidence.wide] using hwide_e
      simp only [List.flatMap_cons, Ix.Kernel.RoleTable.encEvidence, List.cons_append,
        List.length_cons] at hs ev
      rcases Obs.«KernelRoles::read_evidence_entries».obs ev with
        ⟨_, hv14, -⟩ |
        ⟨m47, cs57, x_tag, x_s_71, m83, cs94, _, _, _, _, _, _,
          _, ev59, ev96, -⟩ |
        ⟨m47, cs57, x_tag, x_s_71, m83, cs94, m212, cs222, x_a, x_s_236, m248, cs258,
          v262, x_rest, x_s_288, m305,
          _, ev59, ev96, ev224, op283, ev260, rfl, rfl, rfl, -⟩
      · exact absurd hv14 hcnt_ne
      · obtain ⟨rfl, b, _, _, hb, _, htag⟩ := Deserialize.readByte_refines hs ev59.erase
        injection htag with htag'
        simp only [List.cons.injEq, and_true] at htag'
        obtain ⟨rfl, rfl⟩ := htag'
        simp only [List.cons.injEq] at hb
        obtain ⟨rfl, _⟩ := hb
        obtain ⟨heq, _⟩ := Lib.u8_to_field_spec ev96
        simp at heq
      · obtain ⟨rfl, b, rest1, restPtr, hb, hs1, htag⟩ := Deserialize.readByte_refines hs ev59.erase
        injection htag with htag'
        simp only [List.cons.injEq, and_true] at htag'
        obtain ⟨rfl, rfl⟩ := htag'
        simp only [List.cons.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨_, rfl⟩ := Lib.u8_to_field_spec ev96
        obtain ⟨ext_addr, hlen, addrPtr, restPtr2, haddr_tup, haddr_rep, hs2⟩ :=
          Deserialize.getAddress_refines hs1 ev224.erase
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
        obtain ⟨rfl, rfl⟩ := haddr_tup
        rw [drop32_encAddr_append hsz] at hs2
        have hix : ixAddr (Deserialize.takeAddress _ hlen) = a :=
          ixAddr_takeAddress_encAddr hsz _ hlen
        simp only [evalBinOp, Except.ok.injEq] at op283
        subst op283
        have hv262 : (((es'.length + 1 : Nat) : F) - 1) = (es'.length : F) := by
          push_cast; ring
        rw [hv262] at ev260
        obtain ⟨ext_rec, entriesPtr, restPtr', htuple, hrep', hs'⟩ :=
          ih hwide_es' hlt' hs2 ev260
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htuple
        obtain ⟨rfl, rfl⟩ := htuple
        let node := Value.construct evListEnum "Cons"
          [.construct evEnum "Proof" [x_a], x_rest]
        have ext2 := Heap.Extends.snoc m248 node
        have haddr_rep' : Bytes.RepAddressRef addrTy (m248 ++ [node])
            (Deserialize.takeAddress _ hlen) x_a :=
          Bytes.repAddressRef_heapMono₂ addrTy (ext_rec.trans ext2) haddr_rep
        refine ⟨ext_addr.trans (ext_rec.trans ext2), _, x_s_288, rfl, ?_, hs'.mono ext2⟩
        refine .cons (by simp [node, List.getElem?_concat_length]) ?_
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext2 hrep')
        exact .inr ⟨_, x_a, by rw [hix], rfl, haddr_rep'⟩

private theorem read_role_evidence_aux (t : Ix.Kernel.RoleTable) :
    ∀ (n : Nat) (l : List (Ix.Kernel.Role × Array (Ix.Kernel.Evidence _root_.Address))),
      l.length = n → n < 256 →
      (∀ p ∈ l, p ∈ t.evidence.toList) →
      (∀ p ∈ l, p.2.size < 256 ∧ ∀ e ∈ p.2.toList, e.wide = true) →
      ∀ {rest : List UInt8} {x_s x_next r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        L1.Stream h (l.flatMap Ix.Kernel.RoleTable.encEntry ++ rest) x_s →
        ObsFn W "KernelRoles::read_role_evidence" [x_s, .field (n : F), x_next] h r h' calls →
        Heap.Extends h h' ∧
        ∃ evMap next' restPtr,
          r = .tuple [evMap, next', restPtr] ∧
          RoleMapAll roleEvMapEnum (EvidenceEntry t) h' evMap ∧
          L1.Stream h' rest restPtr := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hlen hn hsub hok rest x_s x_next r h h' calls hs ev
    cases n with
    | zero =>
      have hl0 : l = [] := List.eq_nil_of_length_eq_zero hlen
      subst hl0
      simp only [List.flatMap_nil, List.nil_append] at hs
      rcases Obs.«KernelRoles::read_role_evidence».obs ev with
        ⟨_, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hne46, -⟩
      · exact ⟨Heap.Extends.refl h, _, x_next, x_s, rfl, .nil, hs⟩
      · simp at hne46
    | succ n' =>
      let m := (n' + 1) / 2
      have hm_lt_len : m < l.length := by rw [hlen]; omega
      let l₁ := l.take m
      let p := l[m]'hm_lt_len
      let l₂ := l.drop (m + 1)
      have hl_split : l = l₁ ++ (p :: l₂) := by
        rw [← List.take_append_drop m l, List.drop_eq_getElem_cons hm_lt_len]
      have hp_mem : p ∈ l := List.getElem_mem hm_lt_len
      have hl1_len : l₁.length = m := by simp [l₁, hlen]; omega
      have hl2_len : l₂.length = (n' + 1) - (m + 1) := by simp [l₂, hlen]
      have hcnt_ne : (.field ((n' + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
        intro heq
        have h0 : ((n' + 1 : Nat) : F) = ((0 : Nat) : F) := by simpa using Value.field.inj heq
        have := natCast_inj_of_lt_u32 (by omega) (by decide) h0
        omega
      rcases Obs.«KernelRoles::read_role_evidence».obs ev with
        ⟨hv14, -⟩ |
        ⟨m51, cs61, x_b0, w75, w76, w77, w78, w79, w80, w81, v122, x130, m149, cs159,
          x_left, x_next_189, x_s_190, m207, cs217, x_rb, x_s_231, v242, m243, cs253,
          v275, m278, cs286, v290, m299, cs307, v328, m331, cs339, m366, cs376,
          x_kb, x_s_390, m402, cs412, v416, m425, cs433, x_entries, x_s_447, m459, cs469,
          v473, v474, y489, x_right, x_next_524, x_s_525, m582, m593,
          _, ev63, op145, op137, ev161, ev219, ev255, ev309, ev288, _, ev341, _,
          ev378, ev435, ev414, op504, op495, op519, ev471, rfl, rfl, rfl, rfl, -⟩
      · exact absurd hv14 hcnt_ne
      · obtain ⟨rfl, rfl, hv473⟩ := count_halves (by omega) hn ev63 op145 op137 op504 op495
        subst hv473
        have hs_split : L1.Stream h
            (l₁.flatMap Ix.Kernel.RoleTable.encEntry ++
              (Ix.Kernel.RoleTable.encEntry p ++
                (l₂.flatMap Ix.Kernel.RoleTable.encEntry ++ rest))) x_s := by
          simpa [hl_split, List.flatMap_append, List.flatMap_cons, List.append_assoc] using hs
        obtain ⟨extL, evL, nextL, sL, htupL, hmapL, hsL⟩ :=
          ih m (by omega) l₁ hl1_len (by omega)
            (fun q hq => hsub q (by rw [hl_split]; simp [hq]))
            (fun q hq => hok q (by rw [hl_split]; simp [hq]))
            hs_split ev161
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupL
        obtain ⟨rfl, rfl, rfl⟩ := htupL
        rcases p with ⟨ro, arr⟩
        obtain ⟨harr_sz, harr_wide⟩ := hok (ro, arr) hp_mem
        simp only [Ix.Kernel.RoleTable.encEntry, List.cons_append] at hsL
        obtain ⟨rfl, rb, _, _, hrb, hs_rb, htag_rb⟩ := Deserialize.readByte_refines hsL ev219.erase
        injection htag_rb with htag_rb'
        simp only [List.cons.injEq, and_true] at htag_rb'
        obtain ⟨rfl, rfl⟩ := htag_rb'
        simp only [List.cons.injEq] at hrb
        obtain ⟨rfl, rfl⟩ := hrb
        rw [toUInt8_toNat_of_lt (Nat.lt_trans ro.idx_lt (by decide))] at ev255 op519 ⊢
        obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev255
        obtain ⟨_, rfl, -⟩ := Obs.«KernelRoleSpec::role_count».obs ev309
        obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Lib.less_than_fields_spec ev288
        obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Lib.less_than_fields_spec ev341
        obtain ⟨rfl, kb, _, _, hkb, hs_kb, htag_kb⟩ :=
          Deserialize.readByte_refines hs_rb ev378.erase
        injection htag_kb with htag_kb'
        simp only [List.cons.injEq, and_true] at htag_kb'
        obtain ⟨rfl, rfl⟩ := htag_kb'
        simp only [List.cons.injEq] at hkb
        obtain ⟨rfl, rfl⟩ := hkb
        rw [toUInt8_toNat_of_lt harr_sz] at ev435
        obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev435
        have harr_len : arr.toList.length = arr.size := Array.length_toList
        rw [← harr_len] at ev414
        obtain ⟨extE, entriesPtr, restPtrE, htupE, hrepE, hsE⟩ :=
          read_evidence_entries_spec arr.toList harr_wide (by rw [harr_len]; exact harr_sz)
            hs_kb ev414
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupE
        obtain ⟨rfl, rfl⟩ := htupE
        obtain ⟨extR, evR, nextR, sR, htupR, hmapR, hsR⟩ :=
          ih ((n' + 1) - (m + 1)) (by omega) l₂ hl2_len (by omega)
            (fun q hq => hsub q (by rw [hl_split]; simp [hq]))
            (fun q hq => hok q (by rw [hl_split]; simp [hq]))
            hsE ev471
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupR
        obtain ⟨rfl, rfl, rfl⟩ := htupR
        have extSnoc1 := Heap.Extends.snoc m459 x_left
        have extSnoc2 := Heap.Extends.snoc (m459 ++ [x_left]) x_right
        have extPost := extSnoc1.trans extSnoc2
        let hfinal := (m459 ++ [x_left]) ++ [x_right]
        have ldL : loadValue hfinal (.ptr x_left.type m459.length) = .ok x_left :=
          extSnoc2.loadValue_eq (L1.loadValue_snoc m459 x_left)
        have ldR : loadValue hfinal (.ptr x_right.type (m459 ++ [x_left]).length) = .ok x_right :=
          L1.loadValue_snoc (m459 ++ [x_left]) x_right
        have hmapL' : RoleMapAll roleEvMapEnum (EvidenceEntry t) hfinal x_left := by
          refine RoleMapAll.mono ?_ (extE.trans (extR.trans extPost)) hmapL
          intro _ _ _ _ ext' ⟨r', es', hk, hm, hl'⟩
          exact ⟨r', es', hk, hm, repList_heapMono₂ evListEnum evRep_heapMono₂ ext' hl'⟩
        have hmapR' : RoleMapAll roleEvMapEnum (EvidenceEntry t) hfinal x_right := by
          refine RoleMapAll.mono ?_ extPost hmapR
          intro _ _ _ _ ext' ⟨r', es', hk, hm, hl'⟩
          exact ⟨r', es', hk, hm, repList_heapMono₂ evListEnum evRep_heapMono₂ ext' hl'⟩
        have hentry : EvidenceEntry t hfinal (ro.idx : F) x_entries :=
          ⟨ro, arr, rfl, hsub (ro, arr) hp_mem,
            repList_heapMono₂ evListEnum evRep_heapMono₂ (extR.trans extPost) hrepE⟩
        exact ⟨extL.trans (extE.trans (extR.trans extPost)),
          _, x_next_524, x_s_525, rfl, .node hentry ldL ldR hmapL' hmapR', hsR.mono extPost⟩

private theorem read_role_bindings_aux (t : Ix.Kernel.RoleTable) (hchk : t.check = .ok ()) :
    ∀ (n : Nat) (l : List (Ix.Kernel.Role × _root_.Address)),
      l.length = n → n < 256 →
      (∀ p ∈ l, p ∈ t.bound.toList) →
      (∀ p ∈ l, p.2.hash.size = 32) →
      ∀ (seen : List (Ix.Kernel.Role × _root_.Address)) {rest : List UInt8}
        {x_s x_next x_by_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        ByAddrInv t seen h x_by_addr →
        L1.Stream h (l.flatMap Ix.Kernel.RoleTable.encBound ++ rest) x_s →
        ObsFn W "KernelRoles::read_role_bindings"
          [x_s, .field (n : F), x_next, x_by_addr] h r h' calls →
        Heap.Extends h h' ∧
        ∃ roleMap byAddr' next' restPtr,
          r = .tuple [roleMap, byAddr', next', restPtr] ∧
          RoleMapAll roleAddrMapEnum (BoundEntry t) h' roleMap ∧
          ByAddrInv t (seen ++ l) h' byAddr' ∧
          L1.Stream h' rest restPtr := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hlen hn hsub hsz seen rest x_s x_next x_by_addr r h h' calls hinv hs ev
    cases n with
    | zero =>
      have hl0 : l = [] := List.eq_nil_of_length_eq_zero hlen
      subst hl0
      simp only [List.flatMap_nil, List.nil_append, List.append_nil] at hs ⊢
      rcases Obs.«KernelRoles::read_role_bindings».obs ev with
        ⟨_, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, hne54, -⟩
      · exact ⟨Heap.Extends.refl h, _, x_by_addr, x_next, x_s, rfl, .nil, hinv, hs⟩
      · simp at hne54
    | succ n' =>
      let m := (n' + 1) / 2
      have hm_lt_len : m < l.length := by rw [hlen]; omega
      let l₁ := l.take m
      let p := l[m]'hm_lt_len
      let l₂ := l.drop (m + 1)
      have hl_split : l = l₁ ++ (p :: l₂) := by
        rw [← List.take_append_drop m l, List.drop_eq_getElem_cons hm_lt_len]
      have hp_mem : p ∈ l := List.getElem_mem hm_lt_len
      have hl1_len : l₁.length = m := by simp [l₁, hlen]; omega
      have hl2_len : l₂.length = (n' + 1) - (m + 1) := by simp [l₂, hlen]
      have hcnt_ne : (.field ((n' + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
        intro heq
        have h0 : ((n' + 1 : Nat) : F) = ((0 : Nat) : F) := by simpa using Value.field.inj heq
        have := natCast_inj_of_lt_u32 (by omega) (by decide) h0
        omega
      rcases Obs.«KernelRoles::read_role_bindings».obs ev with
        ⟨hv14, -⟩ |
        ⟨m59, cs69, x_b0, w83, w84, w85, w86, w87, w88, w89, v130, x138, m157, cs167,
          x_left, x_by_addr_205, x_next_206, x_s_207, m229, cs239, x_rb, x_s_253,
          v264, m265, cs275, v297, m300, cs308, v312, m321, cs329, v350, m353, cs361,
          m388, cs398, x_a, x_s_412, v434, m437, cs445, v478, m479, cs489, v493,
          m525, cs535, v539, v540, y556, x_right, x_by_addr_598, x_next_599, x_s_600,
          m663, m674,
          _, ev71, op153, op145, ev169, ev241, ev277, ev331, ev310, _, ev363, _,
          ev400, ev447, heq477, op515, ev491, op571, op562, op586, ev537,
          rfl, rfl, rfl, rfl, -⟩
      · exact absurd hv14 hcnt_ne
      · obtain ⟨rfl, rfl, hv539⟩ := count_halves (by omega) hn ev71 op153 op145 op571 op562
        subst hv539
        have hs_split : L1.Stream h
            (l₁.flatMap Ix.Kernel.RoleTable.encBound ++
              (Ix.Kernel.RoleTable.encBound p ++
                (l₂.flatMap Ix.Kernel.RoleTable.encBound ++ rest))) x_s := by
          simpa [hl_split, List.flatMap_append, List.flatMap_cons, List.append_assoc] using hs
        obtain ⟨extL, roleL, byAddrL, nextL, sL, htupL, hmapL, hinvL, hsL⟩ :=
          ih m (by omega) l₁ hl1_len (by omega)
            (fun q hq => hsub q (by rw [hl_split]; simp [hq]))
            (fun q hq => hsz q (by rw [hl_split]; simp [hq]))
            seen hinv hs_split ev169
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupL
        obtain ⟨rfl, rfl, rfl, rfl⟩ := htupL
        rcases p with ⟨ro, a⟩
        have ha_sz : a.hash.size = 32 := hsz (ro, a) hp_mem
        have ha_of : t.addressOf? ro = some a :=
          addressOf_eq_some_of_mem_bound hchk (hsub (ro, a) hp_mem)
        simp only [Ix.Kernel.RoleTable.encBound, List.cons_append] at hsL
        obtain ⟨rfl, rb, _, _, hrb, hs_rb, htag_rb⟩ := Deserialize.readByte_refines hsL ev241.erase
        injection htag_rb with htag_rb'
        simp only [List.cons.injEq, and_true] at htag_rb'
        obtain ⟨rfl, rfl⟩ := htag_rb'
        simp only [List.cons.injEq] at hrb
        obtain ⟨rfl, rfl⟩ := hrb
        rw [toUInt8_toNat_of_lt (Nat.lt_trans ro.idx_lt (by decide))] at ev277 op515 op586 ⊢
        obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev277
        obtain ⟨_, rfl, -⟩ := Obs.«KernelRoleSpec::role_count».obs ev331
        obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Lib.less_than_fields_spec ev310
        obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Lib.less_than_fields_spec ev363
        obtain ⟨ext_addr, hlen_a, addrPtr, restPtr2, haddr_tup, haddr_rep, hs2⟩ :=
          Deserialize.getAddress_refines hs_rb ev400.erase
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
        obtain ⟨rfl, rfl⟩ := haddr_tup
        rw [drop32_encAddr_append ha_sz] at hs2
        let a' := Deserialize.takeAddress _ hlen_a
        have hix : ixAddr a' = a := ixAddr_takeAddress_encAddr ha_sz _ hlen_a
        have hinvL' : ByAddrInv t (seen ++ l₁) m388 x_by_addr_205 := hinvL.mono ext_addr
        obtain ⟨esL, hbstL, hieL, hmemL⟩ := hinvL'
        have hsym_lk : (Instance.mk "RBTreeMap::rbtree_map_lookup_or_default" [.field]).symbol =
            Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>» := rfl
        rw [← hsym_lk] at ev447
        obtain ⟨hlk_eq, rfl⟩ := rbtree_map_lookup_or_default_spec haddr_rep hbstL ev447
        rw [heq477] at hlk_eq
        have hnot_in : ∀ w, (a', w) ∉ esL := by
          intro w hw
          have heq_w := lookupEntries_eq_of_mem (dflt := .field 0) hbstL.2 hw
          rw [← hlk_eq] at heq_w
          obtain ⟨r', hwf, -⟩ := hieL (a', w) hw
          rw [← heq_w] at hwf
          exact roleNum_add_one_ne_zero r' (Value.field.inj hwf).symm
        simp only [evalBinOp, Except.ok.injEq] at op515
        subst op515
        have hsym_ins : (Instance.mk "RBTreeMap::rbtree_map_insert" [.field]).symbol =
            Obs.Names.«RBTreeMap::rbtree_map_insert<Field>» := rfl
        rw [← hsym_ins] at ev491
        obtain ⟨ext_ins, hbstM⟩ := rbtree_map_insert_spec haddr_rep hbstL ev491
        have hinvM : ByAddrInv t (seen ++ l₁ ++ [(ro, a)]) m479 v478 := by
          refine ⟨insSorted a' (.field (roleNum ro + 1)) esL, hbstM, ?_, ?_⟩
          · intro q hq
            rcases mem_insSorted hq with rfl | hq'
            · exact ⟨ro, rfl, by rw [hix]; exact ha_of⟩
            · exact hieL q hq'
          · intro r0 a0 hm0
            rw [List.mem_append] at hm0
            rcases hm0 with hm0 | hm0
            · obtain ⟨b0, hix0, hb0⟩ := hmemL r0 a0 hm0
              have hne0 : b0 ≠ a' := fun e => hnot_in _ (e ▸ hb0)
              exact ⟨b0, hix0, mem_insSorted_of_ne hb0 hne0⟩
            · simp only [List.mem_singleton, Prod.mk.injEq] at hm0
              obtain ⟨rfl, rfl⟩ := hm0
              exact ⟨a', hix, mem_insSorted_self a' _ esL⟩
        obtain ⟨extR, roleR, byAddrR, nextR, sR, htupR, hmapR, hinvR, hsR⟩ :=
          ih ((n' + 1) - (m + 1)) (by omega) l₂ hl2_len (by omega)
            (fun q hq => hsub q (by rw [hl_split]; simp [hq]))
            (fun q hq => hsz q (by rw [hl_split]; simp [hq]))
            (seen ++ l₁ ++ [(ro, a)]) hinvM (hs2.mono ext_ins) ev537
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupR
        obtain ⟨rfl, rfl, rfl, rfl⟩ := htupR
        have extSnoc1 := Heap.Extends.snoc m525 x_left
        have extSnoc2 := Heap.Extends.snoc (m525 ++ [x_left]) x_right
        have extPost := extSnoc1.trans extSnoc2
        let hfinal := (m525 ++ [x_left]) ++ [x_right]
        have ldL : loadValue hfinal (.ptr x_left.type m525.length) = .ok x_left :=
          extSnoc2.loadValue_eq (L1.loadValue_snoc m525 x_left)
        have ldR : loadValue hfinal (.ptr x_right.type (m525 ++ [x_left]).length) = .ok x_right :=
          L1.loadValue_snoc (m525 ++ [x_left]) x_right
        have hmapL' : RoleMapAll roleAddrMapEnum (BoundEntry t) hfinal x_left := by
          refine RoleMapAll.mono ?_ (ext_addr.trans (ext_ins.trans (extR.trans extPost))) hmapL
          intro _ _ _ _ ext' ⟨r', ab, hk, hab, hbof⟩
          exact ⟨r', ab, hk, Bytes.repAddressRef_heapMono₂ addrTy ext' hab, hbof⟩
        have hmapR' : RoleMapAll roleAddrMapEnum (BoundEntry t) hfinal x_right := by
          refine RoleMapAll.mono ?_ extPost hmapR
          intro _ _ _ _ ext' ⟨r', ab, hk, hab, hbof⟩
          exact ⟨r', ab, hk, Bytes.repAddressRef_heapMono₂ addrTy ext' hab, hbof⟩
        have hbound_mid : BoundEntry t hfinal (ro.idx : F) x_a :=
          ⟨ro, a', rfl,
            Bytes.repAddressRef_heapMono₂ addrTy (ext_ins.trans (extR.trans extPost)) haddr_rep,
            by rw [hix]; exact ha_of⟩
        have hinv_final : ByAddrInv t (seen ++ l) hfinal x_by_addr_598 := by
          have heq_seen : seen ++ l₁ ++ [(ro, a)] ++ l₂ = seen ++ l := by
            simp [hl_split, List.append_assoc]
          rw [← heq_seen]
          exact hinvR.mono extPost
        exact ⟨extL.trans (ext_addr.trans (ext_ins.trans (extR.trans extPost))),
          _, x_by_addr_598, x_next_599, x_s_600, rfl,
          .node hbound_mid ldL ldR hmapL' hmapR', hinv_final, hsR.mono extPost⟩

/-! ## `load_role_table`, `load_role_ctx`, `role_ctx_for_validator` -/

theorem load_role_table_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra)
    {x_binding r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : S0.addr h x_binding b.address)
    (ev : ObsFn W "KernelRoles::load_role_table" [x_binding] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧ TableFullRep t b.address h' r) := by
  obtain ⟨hhash_b, hwire, hto, hlist, hchk, hwf⟩ := admitBinding_inv hadm
  obtain ⟨hv_lt, hn_lt, hm_lt, hb_sz, he_ok, -, -⟩ :=
    (Ix.Kernel.RoleTable.wireWF_iff t).mp hwire
  obtain ⟨ab, hab, hix_b⟩ := hb
  obtain ⟨v1, m14, cs24, x_idx, x_len, v55, m56, cs66, v92, m93, cs103,
    m123, cs133, x_t0, x_s, v168, m171, cs179, m198, cs208, x_t1, x_s_222,
    v244, m247, cs255, m274, cs284, x_version, x_s_298, v320, v321, m323, cs331,
    m343, cs351, m356, cs366, x_n, x_s_380, m392, cs402, v406, m417, cs425,
    x_by_role, x_by_addr, x__next, x_s_454, m476, cs486, x_m, x_s_500,
    m512, cs522, v526, m536, cs544, x_evidence, x__next_564, x_s_565,
    ld11, ev26, ev68, ev105, ev135, ev181, _, ev210, ev257, _,
    ev286, ev333, ev353, _, ev368, ev427, ev404, ev488, ev546, ev524,
    ld591, rfl, rfl, hc636⟩ := Obs.«KernelRoles::load_role_table».obs ev
  have hv1 : v1 = L1.digestV ab := L1.load_repAddressRef hab ld11
  obtain ⟨bytes, _, ext1, ext2, hst, hcall, hproj⟩ := L1.checked_read ev26 ev68 ev105
  have hhashed : Hashed calls ⟨bytes.toArray⟩ :=
    L1.hashed_of_call (by rw [hc636]; simp [hcall]) hst
  have hblk : Address.blake3Pure ⟨bytes.toArray⟩ = b.address := by
    rw [L1.blake3Pure_eq, L1.digest_eq_of_proj hv1 hproj]
    exact hix_b
  by_cases heq_bytes : (⟨bytes.toArray⟩ : ByteArray) = b.bytes
  case neg =>
    exact .inl (.inl ⟨b.address, b.bytes, ⟨bytes.toArray⟩,
      .inr (.inl ⟨hb_extra, hhash_b⟩), hhashed, heq_bytes, hblk⟩)
  right
  have hbytes_eq : bytes = t.encode := by
    have : (⟨bytes.toArray⟩ : ByteArray).data.toList = b.bytes.data.toList :=
      congrArg (fun x : ByteArray => x.data.toList) heq_bytes
    simpa [hlist] using this
  subst hbytes_eq
  have hst0 : L1.Stream m93 t.encode v55 := hst.mono ext2
  unfold Ix.Kernel.RoleTable.encode at hst0
  obtain ⟨rfl, _, _, _, hb0, hst1, ht0⟩ := Deserialize.readByte_refines hst0 ev135.erase
  injection ht0 with ht0'; simp only [List.cons.injEq, and_true] at ht0'; obtain ⟨rfl, rfl⟩ := ht0'
  simp only [List.cons.injEq] at hb0; obtain ⟨rfl, rfl⟩ := hb0
  obtain ⟨_, rfl⟩ := Lib.u8_to_field_spec ev181
  obtain ⟨rfl, _, _, _, hb1, hst2, ht1⟩ := Deserialize.readByte_refines hst1 ev210.erase
  injection ht1 with ht1'; simp only [List.cons.injEq, and_true] at ht1'; obtain ⟨rfl, rfl⟩ := ht1'
  simp only [List.cons.injEq] at hb1; obtain ⟨rfl, rfl⟩ := hb1
  obtain ⟨_, rfl⟩ := Lib.u8_to_field_spec ev257
  obtain ⟨rfl, _, _, _, hb2, hst3, ht2⟩ := Deserialize.readByte_refines hst2 ev286.erase
  injection ht2 with ht2'; simp only [List.cons.injEq, and_true] at ht2'; obtain ⟨rfl, rfl⟩ := ht2'
  simp only [List.cons.injEq] at hb2; obtain ⟨rfl, rfl⟩ := hb2
  obtain ⟨_, rfl⟩ := Lib.u8_to_field_spec ev333
  obtain ⟨_, rfl, -⟩ := Obs.«KernelRoleSpec::spec_version».obs ev353
  obtain ⟨rfl, _, _, _, hb3, hst4, ht3⟩ := Deserialize.readByte_refines hst3 ev368.erase
  injection ht3 with ht3'; simp only [List.cons.injEq, and_true] at ht3'; obtain ⟨rfl, rfl⟩ := ht3'
  simp only [List.cons.injEq] at hb3; obtain ⟨rfl, rfl⟩ := hb3
  rw [toUInt8_toNat_of_lt hn_lt] at ev427
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev427
  have hinv0 : ByAddrInv t [] m14 (.construct addrMapEnum "Nil" []) := by
    refine ⟨[], ?_, by simp, by simp⟩
    rw [← rbtreeEnum_field]
    exact RBTreeBST.nil .field m14
  have hinv0' : ByAddrInv t [] m93 (.construct addrMapEnum "Nil" []) :=
    hinv0.mono (ext1.trans ext2)
  obtain ⟨extB, roleMap, byAddr', nextB, sB, htupB, hmapRole, hinvB, hst5⟩ :=
    read_role_bindings_aux t hchk t.bound.size t.bound.toList Array.length_toList hn_lt
      (fun _ hp => hp) hb_sz [] hinv0' hst4 ev404
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupB
  obtain ⟨rfl, rfl, rfl, rfl⟩ := htupB
  simp only [List.nil_append] at hinvB
  obtain ⟨rfl, _, _, _, hb4, hst6, ht4⟩ := Deserialize.readByte_refines hst5 ev488.erase
  injection ht4 with ht4'; simp only [List.cons.injEq, and_true] at ht4'; obtain ⟨rfl, rfl⟩ := ht4'
  simp only [List.cons.injEq] at hb4; obtain ⟨rfl, rfl⟩ := hb4
  rw [toUInt8_toNat_of_lt hm_lt] at ev546
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev546
  have hst6' : L1.Stream m392 (t.evidence.toList.flatMap Ix.Kernel.RoleTable.encEntry ++ [])
      x_s_500 := by
    simpa using hst6
  have he_ok' : ∀ p ∈ t.evidence.toList, p.2.size < 256 ∧ ∀ e ∈ p.2.toList, e.wide = true := by
    intro p hp
    have := he_ok p hp
    simpa [Ix.Kernel.RoleTable.EntryOk] using this
  obtain ⟨extE, evMap, nextE, sE, htupE, hmapEv, hst7⟩ :=
    read_role_evidence_aux t t.evidence.size t.evidence.toList Array.length_toList hm_lt
      (fun _ hp => hp) he_ok' hst6' ev524
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupE
  obtain ⟨rfl, rfl, rfl⟩ := htupE
  let rtNode := Value.construct rtEnum "Mk" [x_binding, x_by_role, x_by_addr, x_evidence]
  have extSnoc := Heap.Extends.snoc m512 rtNode
  have extAll := ext1.trans (ext2.trans (extB.trans (extE.trans extSnoc)))
  refine ⟨extAll, hwf, x_binding, x_by_role, x_by_addr, x_evidence,
    L1.loadValue_snoc m512 rtNode,
    ⟨ab, Bytes.repAddressRef_heapMono₂ addrTy extAll hab, hix_b⟩, ?_,
    hinvB.mono (extE.trans extSnoc), ?_⟩
  · refine RoleMapAll.mono ?_ (extE.trans extSnoc) hmapRole
    intro _ _ _ _ ext' ⟨ro', ab', hk, hab', hbof⟩
    exact ⟨ro', ab', hk, Bytes.repAddressRef_heapMono₂ addrTy ext' hab', hbof⟩
  · refine RoleMapAll.mono ?_ extSnoc hmapEv
    intro _ _ _ _ ext' ⟨ro', es', hk, hm, hl'⟩
    exact ⟨ro', es', hk, hm, repList_heapMono₂ evListEnum evRep_heapMono₂ ext' hl'⟩

theorem load_role_ctx_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra)
    {x_binding r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : S0.addr h x_binding b.address)
    (ev : ObsFn W "KernelRoles::load_role_ctx"
      [x_binding, .field 3,
       .construct Obs.Names.«Options::Option<&[Field; 32]>» "None" []] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧ RCFullRep t b.address 77 h' r) := by
  rcases Obs.«KernelRoles::load_role_ctx».obs ev with
    ⟨v1, m2, cs12, v126, m127, cs129, v158, m168, cs176,
      ev14, sg134, _, rfl, rfl, ev178, hc186⟩ |
    ⟨_, _, _, _, _, _, _, _, hne187, -⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, hne187, -⟩
  · rcases load_role_table_spec (V := V) hadm hb_extra hb ev14 with hcoll | ⟨ext1, htbl⟩
    · exact .inl (hashedCollision_mono (by intro c hc; rw [hc186]; simp [hc]) hcoll)
    · rcases sg134 with ⟨_, rfl, rfl, _⟩ | ⟨_, hne45, -⟩
      · obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::group_count».obs ev178
        let rcNode := Value.construct rcEnum "Mk"
          [v1, .field (77 : F), .construct addrMapEnum "Nil" []]
        have extSnoc := Heap.Extends.snoc m2 rcNode
        exact .inr ⟨ext1.trans extSnoc, by decide, v1,
          L1.loadValue_snoc m2 rcNode, htbl.mono extSnoc⟩
      · exact absurd rfl (hne45 [] rfl)
  · exact absurd rfl hne187
  · exact absurd rfl hne187

theorem role_ctx_for_validator_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra)
    {x_binding r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : S0.addr h x_binding b.address)
    (ev : ObsFn W "KernelRoles::role_ctx_for_validator" [x_binding, .field 3] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧ RCFullRep t b.address 77 h' r) := by
  obtain ⟨cs4, ev6, hc33⟩ := Obs.«KernelRoles::role_ctx_for_validator».obs ev
  rcases load_role_ctx_spec (V := V) hadm hb_extra hb ev6 with hcoll | hok
  · exact .inl (hashedCollision_mono (by intro c hc; rw [hc33]; simp [hc]) hcoll)
  · exact .inr hok

/-! ## Accessors and lookups on `RCFullRep` / `TableFullRep` -/

theorem role_ctx_table_full_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_table" [x_rc] h r h' calls) :
    h' = h ∧ TableFullRep t bAddr h r := by
  obtain ⟨_, tbl, hl_rc, htbl⟩ := hrc
  rcases Obs.«KernelRoles::role_ctx_table».obs ev with
    ⟨x_tbl, _, _, ld12, rfl, rfl, -⟩ | ⟨x_tbl, _, ld12, -⟩
  · rw [hl_rc] at ld12
    injection ld12 with hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨rfl, -⟩ := hargs
    exact ⟨rfl, htbl⟩
  · rw [hl_rc] at ld12
    cases ld12

theorem role_ctx_binding_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_binding" [x_rc] h r h' calls) :
    h' = h ∧ S0.addr h r bAddr := by
  obtain ⟨m2, p10, _, x_binding, _, _, _, ev18, ld12, rfl, rfl, -⟩ :=
    Obs.«KernelRoles::role_ctx_binding».obs ev
  obtain ⟨rfl, _, bp, _, _, _, hl_tbl, hbp, -, -, -⟩ := role_ctx_table_full_spec hrc ev18
  rw [hl_tbl] at ld12
  injection ld12 with hv
  injection hv with _ _ hargs
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, -⟩ := hargs
  exact ⟨rfl, hbp⟩

theorem role_ctx_validator_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_validator" [x_rc] h r h' calls) :
    r = .field 3 ∧ h' = h := by
  obtain ⟨_, tbl, hl_rc, _⟩ := hrc
  obtain ⟨y2, _, ev14, op8, -⟩ := Obs.«KernelRoles::role_ctx_validator».obs ev
  rcases Obs.«KernelRoles::role_ctx_is_assumed».obs ev14 with
    ⟨_, _, _, ld12, rfl, rfl, -⟩ | ⟨_, _, ld12, -⟩
  · simp only [evalBinOp, add_zero, Except.ok.injEq] at op8
    exact ⟨op8.symm, rfl⟩
  · rw [hl_rc] at ld12
    cases ld12

theorem role_ctx_axioms_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_axioms" [x_rc] h r h' calls) :
    r = .construct addrMapEnum "Nil" [] ∧ h' = h := by
  obtain ⟨_, tbl, hl_rc, _⟩ := hrc
  rcases Obs.«KernelRoles::role_ctx_axioms».obs ev with
    ⟨_, _, x_axioms, ld12, rfl, rfl, -⟩ | ⟨_, _, ld12, -⟩
  · rw [hl_rc] at ld12
    injection ld12 with hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    exact ⟨hargs.2.2.symm, rfl⟩
  · rw [hl_rc] at ld12
    cases ld12

theorem role_ctx_limit_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_limit" [x_rc] h r h' calls) :
    r = .field (lim : F) ∧ h' = h := by
  obtain ⟨_, tbl, hl_rc, _⟩ := hrc
  rcases Obs.«KernelRoles::role_ctx_limit».obs ev with
    ⟨_, _, ld12, -⟩ | ⟨_, x_limit, _, ld12, rfl, rfl, -⟩
  · rw [hl_rc] at ld12
    cases ld12
  · rw [hl_rc] at ld12
    injection ld12 with hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    exact ⟨hargs.2.1.symm, rfl⟩

theorem role_addr_index_full_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (htbl : TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::role_addr_index" [x_tbl] h r h' calls) :
    h' = h ∧ ByAddrInv t t.bound.toList h r := by
  obtain ⟨_, _, _, byAddr, _, hl_tbl, _, _, hba, _⟩ := htbl
  obtain ⟨_, _, x_by_addr, _, ld12, rfl, rfl, -⟩ := Obs.«KernelRoles::role_addr_index».obs ev
  rw [hl_tbl] at ld12
  injection ld12 with hv
  injection hv with _ _ hargs
  simp only [List.cons.injEq] at hargs
  obtain ⟨_, _, rfl, _⟩ := hargs
  exact ⟨rfl, hba⟩

theorem role_index_of_full_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address} {lim : Nat}
    {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::role_index_of" [x_rc, x_a] h r h' calls) :
    h' = h ∧
    ((r = .field 0 ∧ ∀ ro, t.addressOf? ro ≠ some a) ∨
      ∃ ro : Ix.Kernel.Role, r = .field (roleNum ro + 1) ∧ t.addressOf? ro = some a) := by
  obtain ⟨ab, hab, hix⟩ := ha
  obtain ⟨_, v8, m18, _, v29, m31, _, ev41, ev28, ev6, -⟩ :=
    Obs.«KernelRoles::role_index_of».obs ev
  obtain ⟨rfl, htbl⟩ := role_ctx_table_full_spec hrc ev41
  obtain ⟨rfl, ⟨es, hbst, hie, hmem⟩⟩ := role_addr_index_full_spec htbl ev28
  have hsym_lk : (Instance.mk "RBTreeMap::rbtree_map_lookup_or_default" [.field]).symbol =
      Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>» := rfl
  rw [← hsym_lk] at ev6
  obtain ⟨hlk, rfl⟩ := rbtree_map_lookup_or_default_spec hab hbst ev6
  refine ⟨rfl, ?_⟩
  by_cases hex : ∃ w, (ab, w) ∈ es
  · obtain ⟨w, hw⟩ := hex
    rw [lookupEntries_eq_of_mem hbst.2 hw] at hlk
    obtain ⟨ro, hw_eq, hof⟩ := hie (ab, w) hw
    rw [hix] at hof
    exact .inr ⟨ro, hlk.trans hw_eq, hof⟩
  · have hno : ∀ w, (ab, w) ∉ es := fun w hw => hex ⟨w, hw⟩
    rw [lookupEntries_eq_dflt_of_not_mem hno] at hlk
    refine .inl ⟨hlk, ?_⟩
    intro ro hof
    have hm_bound := mem_bound_of_addressOf_eq_some hof
    obtain ⟨b0, hix0, hb0⟩ := hmem ro a hm_bound
    have hb_eq : b0 = ab := ixAddr_injective (hix0.trans hix.symm)
    subst hb_eq
    exact hno _ hb0

/-! ## `role_spec_kind` on inert roles and `role_is_inert` -/

private def findLitArm (x : F) : List (Pattern F × Expr F) → Option (Expr F)
  | (.literal k, b) :: rest => if ZMod.val x == ZMod.val k then some b else findLitArm x rest
  | _ => none

private theorem findLitArm_sound {x : F} {arms : List (Pattern F × Expr F)} {res : Expr F}
    (hf : findLitArm x arms = some res)
    {h : Heap F} {bs : Environment F Nat} {body : Expr F}
    (hsel : selectArm W [] h (.field x) arms = .ok (some (bs, body))) :
    body = res := by
  induction arms with
  | nil => simp [findLitArm] at hf
  | cons arm rest ih =>
    rcases arm with ⟨pat, b⟩
    cases pat with
    | literal k =>
      simp only [findLitArm] at hf
      by_cases hxk : (ZMod.val x == ZMod.val k) = true
      · rw [ite_eq_left hxk] at hf
        injection hf with hf
        have hx_eq : x = k := ZMod.val_injective (beq_iff_eq.mp hxk)
        subst hx_eq hf
        rcases selectArm_cons_inv hsel with ⟨_, rfl⟩ | ⟨nm, _⟩
        · rfl
        · exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal x) nm)
      · rw [ite_eq_right hxk] at hf
        have hx_ne : x ≠ k := fun e => hxk (beq_iff_eq.mpr (congrArg ZMod.val e))
        rcases selectArm_cons_inv hsel with ⟨mt, _⟩ | ⟨_, hsel'⟩
        · obtain ⟨hv, _⟩ := MatchesConst.some_inv (MatchesConst.literal k) mt
          exact absurd (Value.field.inj hv) hx_ne
        · exact ih hf hsel'
    | _ => simp [findLitArm] at hf

private theorem inert_idx_cases {ro : Ix.Kernel.Role} (hinert : ro.inert = true) :
    ro.idx = 58 ∨ ro.idx = 103 ∨ ro.idx = 106 ∨ ro.idx = 107 := by
  cases ro <;> first | exact absurd hinert (by decide) | decide

theorem role_spec_kind_inert_eq {ro : Ix.Kernel.Role} (hinert : ro.inert = true)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::role_spec_kind" [.field (roleNum ro)] h r h' calls) :
    r = .field 4 ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_spec_kind.lookup
    (by simp [IxVM.KernelRoleSpec.role_spec_kind, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_spec_kind] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  have hbody : body4 = .literal 4 := by
    unfold roleNum at sel8
    rcases inert_idx_cases hinert with hidx | hidx | hidx | hidx
    · rw [hidx] at sel8; exact findLitArm_sound (by decide) sel8
    · rw [hidx] at sel8; exact findLitArm_sound (by decide) sel8
    · rw [hidx] at sel8; exact findLitArm_sound (by decide) sel8
    · rw [hidx] at sel8; exact findLitArm_sound (by decide) sel8
  subst hbody
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

private def allBodiesLit : List (Pattern F × Expr F) → Bool
  | [] => true
  | (_, .literal _) :: rest => allBodiesLit rest
  | _ => false

private theorem selectArm_all_lit {arms : List (Pattern F × Expr F)} (hall : allBodiesLit arms = true)
    {env : Environment F Nat} {h : Heap F} {v : SourceValue F} {bs : Environment F Nat} {body : Expr F}
    (hsel : selectArm W env h v arms = .ok (some (bs, body))) :
    ∃ k : F, body = .literal k := by
  induction arms with
  | nil => simp [selectArm] at hsel
  | cons arm rest ih =>
    rcases arm with ⟨pat, b⟩
    cases b with
    | literal k =>
      simp only [allBodiesLit] at hall
      rcases selectArm_cons_inv hsel with ⟨_, rfl⟩ | ⟨_, hsel'⟩
      · exact ⟨k, rfl⟩
      · exact ih hall hsel'
    | _ => simp [allBodiesLit] at hall

private theorem role_spec_kind_heap_eq {v r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::role_spec_kind" [v] h r h' calls) :
    h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_spec_kind.lookup
    (by simp [IxVM.KernelRoleSpec.role_spec_kind, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_spec_kind] at d0
  obtain ⟨_, m2, _, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨_, rfl, -⟩ := d7.var_inv
  obtain ⟨k, rfl⟩ := selectArm_all_lit (by decide) sel8
  obtain ⟨_, rfl, -⟩ := d9.literal_inv
  rfl

theorem role_is_inert_zero_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address} {lim : Nat}
    {x_rc x_a : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::role_is_inert" [x_rc, x_a] h (.field 0) h' calls) :
    h' = h ∧ ¬ IxVM.Consistency.InertAt t a := by
  rcases Obs.«KernelRoles::role_is_inert».obs ev with
    ⟨m2, cs12, ev14, _, rfl, -⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, he95, -⟩ |
    ⟨v1, m2, cs12, v52, x61, m63, cs72, v75, ev14, hne48, op89, ev74, op68, hne98, _, rfl, -⟩
  · obtain ⟨rfl, hres⟩ := role_index_of_full_spec hrc ha ev14
    rcases hres with ⟨_, hnone⟩ | ⟨ro, heq, _⟩
    · refine ⟨rfl, ?_⟩
      rintro ⟨ro, _, hof⟩
      exact hnone ro hof
    · exact absurd (Value.field.inj heq).symm (roleNum_add_one_ne_zero ro)
  · simp at he95
  · obtain ⟨rfl, hres⟩ := role_index_of_full_spec hrc ha ev14
    rcases hres with ⟨rfl, _⟩ | ⟨ro, rfl, hof⟩
    · exact absurd rfl hne48
    · simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op89
      subst op89
      refine ⟨role_spec_kind_heap_eq ev74, ?_⟩
      rintro ⟨ro', hinert', hof'⟩
      obtain ⟨_, _, _, hwf, _⟩ := hrc
      have hro_eq : ro' = ro :=
        Ix.Kernel.RoleTable.addressOf?_inj (RoleClosure.check_ok_of_wf hwf) hof' hof
      subst hro_eq
      obtain ⟨rfl, _⟩ := role_spec_kind_inert_eq hinert' ev74
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op68
      exact hne98 op68.symm

/-! ## `walk_covered`, `group_validation_limit`, `walk_ctx` -/

theorem walk_covered_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::walk_covered" [x_rc, x_a] h r h' calls) :
    r = .field 0 ∧ h' = h := by
  obtain ⟨_, tbl, hl_rc, _⟩ := hrc
  rcases Obs.«KernelRoles::walk_covered».obs ev with
    ⟨_, _, _, _, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, ld12, -⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, ld12, -⟩
  · exact ⟨rfl, rfl⟩
  · rw [hl_rc] at ld12; cases ld12
  · rw [hl_rc] at ld12; cases ld12

theorem group_validation_limit_spec {g : F} (hg : g.val < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::group_validation_limit" [.field g] h r h' calls) :
    h' = h ∧ ∃ lim' : Nat, lim' ≤ 46 ∧ r = .field (lim' : F) := by
  rcases Obs.«KernelRoles::group_validation_limit».obs ev with
    ⟨v1, m2, _, m16, _, ev14, ev29, rfl, rfl, -⟩ |
    ⟨v1, m2, _, _, m16, _, v58, m59, _, m73, _, ev14, ev29, _, ev71, ev86, rfl, rfl, -⟩ |
    ⟨v1, m2, _, _, m16, _, v58, m59, _, _, m73, _, ev14, ev29, _, ev71, ev86, _, rfl, rfl, -⟩
  · obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_well_founded_group».obs ev14
    obtain ⟨_, _, hlt_iff, _, rfl⟩ := Lib.less_than_fields_field ev29
    have hlt38 : g.val < 38 := by
      have h38 : (38 : F).val = 38 := ZMod.val_natCast_of_lt (by decide)
      simpa [h38] using hlt_iff.mp rfl
    exact ⟨rfl, g.val, by omega, by simp [ZMod.natCast_zmod_val]⟩
  · obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_well_founded_group».obs ev14
    obtain ⟨_, _, _, _, rfl⟩ := Lib.less_than_fields_field ev29
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_equation_group».obs ev71
    obtain ⟨_, _, _, _, rfl⟩ := Lib.less_than_fields_field ev86
    exact ⟨rfl, 38, by omega, rfl⟩
  · obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_well_founded_group».obs ev14
    obtain ⟨_, _, _, _, rfl⟩ := Lib.less_than_fields_field ev29
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_equation_group».obs ev71
    obtain ⟨_, _, _, _, rfl⟩ := Lib.less_than_fields_field ev86
    exact ⟨rfl, 46, by omega, rfl⟩

theorem walk_ctx_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::walk_ctx" [x_rc, x_a] h r h' calls) :
    Heap.Extends h h' ∧ ∃ lim' : Nat, RCFullRep t bAddr lim' h' r := by
  have ext := ev.heap_extends
  obtain ⟨hlim, tbl, hl_rc, htbl⟩ := hrc
  rcases Obs.«KernelRoles::walk_ctx».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, rfl, -⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, rfl, rfl, -⟩ |
    ⟨x_tbl, x_limit, w20, v36, m37, cs47, v51, m61, cs69, v108, m109, cs119, v122, v138,
      m139, x147, y148, m149, cs158, cs180, v183, v220, m230, cs238,
      ld12, _, _, _, _, _, ev160, _, _, _, _, rfl, rfl, ev240, -⟩ |
    ⟨_, _, ld12, -⟩
  · exact ⟨ext, lim, hlim, tbl, ext.loadValue_eq hl_rc, htbl.mono ext⟩
  · exact ⟨ext, lim, hlim, tbl, ext.loadValue_eq hl_rc, htbl.mono ext⟩
  · rw [hl_rc] at ld12
    injection ld12 with hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨rfl, _, _⟩ := hargs
    obtain ⟨g, _, rfl, _, hg_lt, _, _, _⟩ := Lib.less_than_fields_spec ev160
    obtain ⟨rfl, lim', hlim46, rfl⟩ := group_validation_limit_spec hg_lt ev240
    let rcNode := Value.construct rcEnum "Mk"
      [x_tbl, .field (lim' : F), .construct addrMapEnum "Nil" []]
    exact ⟨ext, lim', by omega, x_tbl, L1.loadValue_snoc m139 rcNode, htbl.mono ext⟩
  · rw [hl_rc] at ld12
    cases ld12

end IxVM.Refinement.Claim
