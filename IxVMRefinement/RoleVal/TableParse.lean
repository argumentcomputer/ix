import IxVMRefinement.Claim.RoleTable
import IxVMRefinement.Roles.Lookups

/-! # The role table as `KernelRoles::load_role_table` parses it

`Claim.load_role_table_spec` reads the load against a table given in advance. Here the table is
produced by the load itself: the readers `read_role_bindings`, `read_role_evidence` and
`read_evidence_entries` are read in the parse direction, from the bytes of the stream to the
pairs they hold, and the maps the load builds are described exactly (every parsed pair is an
entry and every entry is a parsed pair), not only soundly as `Core.TableRep` describes them.

* `RoleMapEntries en h es tree`: the in-order entries of a role-keyed map
  (`KernelRoles::RoleMap<V>`); with ascending keys a search finds every entry
  (`RoleMapEntries.search_of_mem`).
* `rbtreeEntries_det`: an address-keyed map's entries are determined by the tree.
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

/-! ## Role-keyed maps, exactly -/

/-- **The in-order entries of a role-keyed map** (`KernelRoles::RoleMap<V>`, held by value:
`Node(color, key, value, &left, &right)`), keys as natural numbers. -/
inductive RoleMapEntries (en : String) (h : Heap F) :
    List (Nat × SourceValue F) → SourceValue F → Prop where
  | nil : RoleMapEntries en h [] (.construct en "Nil" [])
  | node {c : F} {k : Nat} {v lp rp lv rv : SourceValue F}
      {ls rs : List (Nat × SourceValue F)}
      (hl : loadValue h lp = .ok lv) (hr : loadValue h rp = .ok rv)
      (rl : RoleMapEntries en h ls lv) (rr : RoleMapEntries en h rs rv) :
      RoleMapEntries en h (ls ++ [(k, v)] ++ rs)
        (.construct en "Node" [.field c, .field (k : F), v, lp, rp])

theorem RoleMapEntries.mono {en : String} {h₁ h₂ : Heap F}
    {es : List (Nat × SourceValue F)} {tree : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (he : RoleMapEntries en h₁ es tree) :
    RoleMapEntries en h₂ es tree := by
  induction he with
  | nil => exact .nil
  | node hl hr _ _ ihl ihr => exact .node (ext.loadValue_eq hl) (ext.loadValue_eq hr) ihl ihr

/-- Every entry of a map with these entries satisfies what each entry satisfies. -/
theorem RoleMapEntries.toAll {en : String} {h : Heap F} {es : List (Nat × SourceValue F)}
    {tree : SourceValue F} {P : Heap F → F → SourceValue F → Prop}
    (he : RoleMapEntries en h es tree) (hP : ∀ p ∈ es, P h (p.1 : F) p.2) :
    RoleMapAll en P h tree := by
  induction he with
  | nil => exact .nil
  | @node c k v lp rp lv rv ls rs hl hr _ _ ihl ihr =>
    exact .node (hP (k, v) (by simp)) hl hr
      (ihl (fun p hp => hP p (by simp [hp])))
      (ihr (fun p hp => hP p (by simp [hp])))

/-- **A search for a key of an ascending role map finds its entry.** -/
theorem RoleMapEntries.search_of_mem {en : String} {h : Heap F}
    {es : List (Nat × SourceValue F)} {tree : SourceValue F}
    (he : RoleMapEntries en h es tree) :
    es.Pairwise (fun p q => p.1 < q.1) → (∀ p ∈ es, p.1 < 4294967296) →
    ∀ {k : Nat} {v : SourceValue F} {res : Option (SourceValue F)},
      (k, v) ∈ es → Specs.Roles.RoleMapSearch en h (k : F) tree res → res = some v := by
  induction he with
  | nil => intro _ _ k v res hm; cases hm
  | @node c key v0 lp rp lv rv ls rs hl hr rl rr ihl ihr =>
    intro hasc hlt k v res hm hs
    have hk : k < 4294967296 := hlt (k, v) hm
    have hkey : key < 4294967296 := hlt (key, v0) (by simp)
    rw [List.pairwise_append, List.pairwise_append] at hasc
    obtain ⟨⟨hpl, -, hl_mid⟩, hpr, hlr⟩ := hasc
    have hls_lt : ∀ p ∈ ls, p.1 < key := fun p hp => hl_mid p hp (key, v0) (by simp)
    have hrs_gt : ∀ p ∈ rs, key < p.1 := fun p hp => hlr (key, v0) (by simp) p hp
    have hltL : ∀ p ∈ ls, p.1 < 4294967296 := fun p hp => hlt p (by simp [hp])
    have hltR : ∀ p ∈ rs, p.1 < 4294967296 := fun p hp => hlt p (by simp [hp])
    simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons,
      Prod.mk.injEq] at hm
    generalize hT : (Value.construct en "Node" [.field c, .field (key : F), v0, lp, rp] :
      SourceValue F) = T at hs
    cases hs with
    | nil =>
      injection hT with _ hc _
      exact absurd hc (by decide)
    | @here c' v' lp' rp' =>
      injection hT with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hkk, rfl, -, -⟩ := hargs
      have hke : key = k := Claim.natCast_inj_of_lt_u32 hkey hk (Value.field.inj hkk)
      subst hke
      rcases hm with hm | ⟨-, rfl⟩ | hm
      · exact absurd (hls_lt _ hm) (Nat.lt_irrefl _)
      · rfl
      · exact absurd (hrs_gt _ hm) (Nat.lt_irrefl _)
    | @left c' v' lp' rp' lv' key' res' hlt' hl' hs' =>
      injection hT with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hkk, -, rfl, -⟩ := hargs
      obtain rfl := Claim.loadValue_eq_inj hl hl'
      rw [← Value.field.inj hkk, Claim.val_of_lt_u32 hk, Claim.val_of_lt_u32 hkey] at hlt'
      rcases hm with hm | hm | hm
      · exact ihl hpl hltL hm hs'
      · exact absurd hm.1 (Nat.ne_of_lt hlt')
      · exact absurd (Nat.lt_trans hlt' (hrs_gt _ hm)) (Nat.lt_irrefl _)
    | @right c' v' lp' rp' rv' key' res' hgt' hr' hs' =>
      injection hT with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hkk, -, -, rfl⟩ := hargs
      obtain rfl := Claim.loadValue_eq_inj hr hr'
      rw [← Value.field.inj hkk, Claim.val_of_lt_u32 hk, Claim.val_of_lt_u32 hkey] at hgt'
      rcases hm with hm | hm | hm
      · exact absurd (Nat.lt_trans hgt' (hls_lt _ hm)) (Nat.lt_irrefl _)
      · exact absurd hm.1 (Nat.ne_of_gt hgt')
      · exact ihr hpr hltR hm hs'

/-! ## Address-keyed maps: entries determined by the tree -/

/-- **The entries of an address-keyed map are determined by the tree and the heap.** -/
theorem rbtreeEntries_det {t_V : Generic.Ty} {h : Heap F}
    {es : List (Bytes.Address × SourceValue F)} {tree : SourceValue F}
    (he : Claim.RBTreeEntries t_V h es tree) :
    ∀ {es' : List (Bytes.Address × SourceValue F)}, Claim.RBTreeEntries t_V h es' tree →
      es = es' := by
  induction he with
  | nil => intro es' h'; exact h'.nil_inv.symm
  | node hk hl hr rl rr ihl ihr =>
    intro es' h'
    obtain ⟨c', a', lv', rv', ls', rs', -, rfl, hk', hl', hr', rl', rr'⟩ := h'.node_inv
    obtain rfl := Claim.loadValue_eq_inj hl hl'
    obtain rfl := Claim.loadValue_eq_inj hr hr'
    obtain rfl := Bytes.repAddressRef_inj Aiur.Library.U32.Goldilocks.compatible hk hk'
    rw [ihl rl', ihr rr']

/-! ## Helpers for the readers -/

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons hr ht, h => .cons hr (forall₂_append ht h)

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ S l m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hr ht => .cons (H _ _ hr) (forall₂_imp H ht)

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ a ∈ l, ∃ b ∈ m, R a b
  | [], [], .nil, _, ha => by cases ha
  | _ :: _, _ :: _, .cons hr ht, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hab⟩ := forall₂_mem_left ht a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ b ∈ m, ∃ a ∈ l, R a b
  | [], [], .nil, _, hb => by cases hb
  | _ :: _, _ :: _, .cons hr ht, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_mem_right ht b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

private theorem twoF_ne_zero : (2 : F) ≠ 0 := by decide

/-- The count arithmetic of the balanced readers (as `Claim`'s, which is private). -/
theorem count_halves {count : Nat} (hpos : 0 < count) (hlt : count < 256)
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
  have hrep : RepU8 h b (.field (count : F)) := by
    show Value.field (count : F) = .field (b.toNat : F)
    rw [UInt8.toNat_ofNatLT]
  obtain ⟨htup, hm59⟩ := Lib.u8_raw_bit_decomposition_spec hrep ev71
  dsimp only [b] at htup
  rw [UInt8.toNat_ofNatLT] at htup
  simp only [Value.tuple.injEq, List.cons.injEq] at htup
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
  exact ⟨hm59, rfl, congrArg Value.field hrem⟩

theorem encAddr_ixAddr (b : Bytes.Address) :
    Ix.Kernel.RoleTable.encAddr (ixAddr b) = b.toList := rfl

theorem takeAddress_toList {bs : List UInt8} (hlen : 32 ≤ bs.length) :
    (Deserialize.takeAddress bs hlen).toList = bs.take 32 := by
  simp [Deserialize.takeAddress]

/-- Every index below 108 is a role's. -/
theorem exists_role_of_lt {k : Nat} (hk : k < 108) : ∃ ro : Ix.Kernel.Role, ro.idx = k := by
  have hc := Ix.Kernel.Role.ofIdx?_idx_below k hk
  cases hro : Ix.Kernel.Role.ofIdx? k with
  | none => simp [hro] at hc
  | some ro => exact ⟨ro, Ix.Kernel.Role.idx_ofIdx? hro⟩

/-- `UInt32::less_than_fields` on two small naturals. -/
theorem lt_fields_nat {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::less_than_fields" [.field (a : F), .field (b : F)] h r h' cs) :
    (r = .field 1 → a < b) ∧ (r = .field 0 → ¬ a < b) ∧ h' = h := by
  obtain ⟨-, -, hiff, h01, hh⟩ := Lib.less_than_fields_field ev
  rw [Claim.val_of_lt_u32 ha, Claim.val_of_lt_u32 hb] at hiff
  refine ⟨hiff.mp, fun h0 hlt => ?_, hh⟩
  have h1 := hiff.mpr hlt
  rw [h0] at h1
  exact zero_ne_one (Value.field.inj h1)

/-- An entry at another address survives an insertion (as `Claim`'s, which is private). -/
theorem mem_insSorted_of_ne {a b : Bytes.Address} {v w : SourceValue F}
    {es : List (Bytes.Address × SourceValue F)}
    (hbw : (b, w) ∈ es) (hne : b ≠ a) :
    (b, w) ∈ Claim.insSorted a v es := by
  induction es with
  | nil => cases hbw
  | cons kw rest ih =>
    rcases kw with ⟨k, w0⟩
    unfold Claim.insSorted
    by_cases hlt : Claim.addrRank a < Claim.addrRank k
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

/-! ## `read_role_bindings`, parsed -/

/-- **The address index after the bindings reader**: the entries it started from and, for each
pair read, the pair's address at the role's number plus one. -/
def IndexEntriesOf (es0 : List (Bytes.Address × SourceValue F))
    (lb : List (Ix.Kernel.Role × Bytes.Address))
    (es : List (Bytes.Address × SourceValue F)) : Prop :=
  ∀ b w, (b, w) ∈ es ↔ (b, w) ∈ es0 ∨ ∃ ro, (ro, b) ∈ lb ∧ w = .field (roleNum ro + 1)

/-- The role map's entries are the pairs read, in order, each at its address. -/
def BoundEntriesOf (h : Heap F) (lb : List (Ix.Kernel.Role × Bytes.Address))
    (ents : List (Nat × SourceValue F)) : Prop :=
  List.Forall₂ (fun p q => q.1 = p.1.idx ∧ Bytes.RepAddressRef addrTy h p.2 q.2) lb ents

theorem BoundEntriesOf.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {lb : List (Ix.Kernel.Role × Bytes.Address)} {ents : List (Nat × SourceValue F)}
    (hb : BoundEntriesOf h₁ lb ents) : BoundEntriesOf h₂ lb ents :=
  forall₂_imp (fun _ _ ⟨hk, ha⟩ => ⟨hk, Bytes.repAddressRef_heapMono₂ addrTy ext ha⟩) hb

/-- **`KernelRoles::read_role_bindings(s, n, next, by_addr)`, parsed**: the stream begins with
the encodings of `n` pairs of strictly ascending roles from `next` on, each with a 32-byte
address; the role map returned has exactly those pairs as entries, in order; the address index
returned is sorted and holds exactly the entries it was given and one per pair, at the pair's
address, the role's number plus one; the returned `next` bounds the roles read. -/
theorem read_role_bindings_parse :
    ∀ (n : Nat), n < 256 →
    ∀ (nxt : Nat) (es0 : List (Bytes.Address × SourceValue F)) {bs : List UInt8}
      {x_s x_by_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      nxt ≤ 108 →
      Claim.RBTreeBST .field h es0 x_by_addr →
      (∀ p ∈ es0, ∃ ro : Ix.Kernel.Role, p.2 = .field (roleNum ro + 1)) →
      L1.Stream h bs x_s →
      ObsFn W "KernelRoles::read_role_bindings"
        [x_s, .field (n : F), .field (nxt : F), x_by_addr] h r h' calls →
      Heap.Extends h h' ∧
      ∃ (lb : List (Ix.Kernel.Role × Bytes.Address)) (rest : List UInt8)
        (roleMap byAddr' restPtr : SourceValue F) (nxt' : Nat)
        (ents : List (Nat × SourceValue F)) (es' : List (Bytes.Address × SourceValue F)),
        r = .tuple [roleMap, byAddr', .field (nxt' : F), restPtr] ∧
        lb.length = n ∧
        bs = lb.flatMap (fun p => Ix.Kernel.RoleTable.encBound (p.1, ixAddr p.2)) ++ rest ∧
        L1.Stream h' rest restPtr ∧
        lb.Pairwise (fun p q => p.1.idx < q.1.idx) ∧
        nxt ≤ nxt' ∧ nxt' ≤ 108 ∧ (∀ p ∈ lb, nxt ≤ p.1.idx ∧ p.1.idx < nxt') ∧
        RoleMapEntries roleAddrMapEnum h' ents roleMap ∧ BoundEntriesOf h' lb ents ∧
        Claim.RBTreeBST .field h' es' byAddr' ∧ IndexEntriesOf es0 lb es' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn nxt es0 bs x_s x_by_addr r h h' calls hnxt hbst hvals hs ev
    cases n with
    | zero =>
      rcases Obs.«KernelRoles::read_role_bindings».obs ev with
        ⟨_, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, hne54, -⟩
      · refine ⟨Heap.Extends.refl _, [], bs, _, x_by_addr, x_s, nxt, [], es0, rfl, rfl,
          by simp, hs, List.Pairwise.nil, le_refl _, hnxt, by simp, .nil, List.Forall₂.nil,
          hbst, fun b w => by simp⟩
      · simp at hne54
    | succ n' =>
      rcases Obs.«KernelRoles::read_role_bindings».obs ev with
        ⟨hv14, -⟩ |
        ⟨m59, cs69, x_b0, w83, w84, w85, w86, w87, w88, w89, v130, x138, m157, cs167,
          x_left, x_by_addr_205, x_next_206, x_s_207, m229, cs239, x_rb, x_s_253,
          v264, m265, cs275, v297, m300, cs308, v312, m321, cs329, v350, m353, cs361,
          m388, cs398, x_a, x_s_412, v434, m437, cs445, v478, m479, cs489, v493,
          m525, cs535, v539, v540, y556, x_right, x_by_addr_598, x_next_599, x_s_600,
          m663, m674,
          _, ev71, op153, op145, ev169, ev241, ev277, ev331, ev310, heq338, ev363, heq386,
          ev400, ev447, heq477, op515, ev491, op571, op562, op586, ev537,
          rfl, rfl, rfl, rfl, -⟩
      · exfalso
        have h0 : ((n' + 1 : Nat) : F) = ((0 : Nat) : F) := by
          simpa using Value.field.inj hv14
        have := Claim.natCast_inj_of_lt_u32 (by omega) (by decide) h0
        omega
      · obtain ⟨rfl, rfl, rfl⟩ := count_halves (by omega) hn ev71 op153 op145 op571 op562
        -- the left subtree
        obtain ⟨extL, lbL, restL, roleL, byAddrL, sL, nxtL, entsL, esL, htupL, hlenL, hbsL, hsL,
          hascL, hnxtL1, hnxtL2, hrangeL, hentL, hbndL, hbstL, hidxL⟩ :=
          ih ((n' + 1) / 2) (by omega) (by omega) nxt es0 hnxt hbst hvals hs ev169
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupL
        obtain ⟨rfl, rfl, rfl, rfl⟩ := htupL
        -- the role byte
        obtain ⟨rfl, rb, bs1, sPtr1, rfl, hs1, htag⟩ := Deserialize.readByte_refines hsL ev241.erase
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htag
        obtain ⟨rfl, rfl⟩ := htag
        obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev277
        obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_count».obs ev331
        have hrb256 : rb.toNat < 256 := UInt8.toNat_lt rb
        obtain ⟨h108, -, rfl⟩ := lt_fields_nat (a := rb.toNat) (b := 108) (by omega) (by decide)
          (by rw [Nat.cast_ofNat]; exact ev310)
        have hrb108 : rb.toNat < 108 := h108 heq338
        obtain ⟨-, hgeN, rfl⟩ := lt_fields_nat (a := rb.toNat) (b := nxtL) (by omega) (by omega)
          ev363
        have hge : nxtL ≤ rb.toNat := Nat.le_of_not_lt (hgeN heq386)
        obtain ⟨ro, hro⟩ := exists_role_of_lt hrb108
        -- the address
        obtain ⟨ext_addr, hlen_a, addrPtr, sPtr2, haddr_tup, haddr_rep, hs2⟩ :=
          Deserialize.getAddress_refines hs1 ev400.erase
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
        obtain ⟨rfl, rfl⟩ := haddr_tup
        obtain ⟨a', ha'⟩ : ∃ a', Deserialize.takeAddress bs1 hlen_a = a' := ⟨_, rfl⟩
        rw [ha'] at haddr_rep
        -- no address twice
        rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev447
        obtain ⟨hlk_eq, rfl⟩ :=
          Claim.rbtree_map_lookup_or_default_spec haddr_rep (hbstL.mono ext_addr) ev447
        rw [heq477] at hlk_eq
        have hvalsL : ∀ p ∈ esL, ∃ ro' : Ix.Kernel.Role, p.2 = .field (roleNum ro' + 1) := by
          intro p hp
          rcases (hidxL p.1 p.2).mp hp with h0 | ⟨ro', -, hw⟩
          · exact hvals p h0
          · exact ⟨ro', hw⟩
        have hfresh : ∀ w, (a', w) ∉ esL := by
          intro w hw
          have hw' := Claim.lookupEntries_eq_of_mem (dflt := .field 0) hbstL.2 hw
          rw [← hlk_eq] at hw'
          obtain ⟨ro', hro'⟩ := hvalsL (a', w) hw
          rw [← hw'] at hro'
          exact RolesAux.roleNum_add_one_ne_zero ro' (Value.field.inj hro').symm
        -- the insertion
        obtain rfl := RolesAux.evalBinOp_add_field_inv op515
        obtain rfl := RolesAux.evalBinOp_add_field_inv op586
        rw [← Obs.Names.«RBTreeMap::rbtree_map_insert<Field>».symbol] at ev491
        obtain ⟨ext_ins, hbstM⟩ :=
          Claim.rbtree_map_insert_spec haddr_rep (hbstL.mono ext_addr) ev491
        have hv_eq : ((rb.toNat : F) + 1) = roleNum ro + 1 := by
          rw [← hro]
        rw [hv_eq] at hbstM
        have hidxM : IndexEntriesOf es0 (lbL ++ [(ro, a')])
            (Claim.insSorted a' (.field (roleNum ro + 1)) esL) := by
          intro b w
          constructor
          · intro hm
            rcases Claim.mem_insSorted hm with heq | hm
            · simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              exact .inr ⟨ro, by simp, rfl⟩
            · rcases (hidxL b w).mp hm with h0 | ⟨ro', hm', hw⟩
              · exact .inl h0
              · exact .inr ⟨ro', by simp [hm'], hw⟩
          · intro hm
            have hold : (b, w) ∈ esL →
                (b, w) ∈ Claim.insSorted a' (.field (roleNum ro + 1)) esL := by
              intro hbw
              have hne : b ≠ a' := by
                intro e
                subst e
                exact hfresh w hbw
              exact mem_insSorted_of_ne hbw hne
            rcases hm with h0 | ⟨ro', hm', hw⟩
            · exact hold ((hidxL b w).mpr (.inl h0))
            · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm'
              rcases hm' with hm' | ⟨rfl, rfl⟩
              · exact hold ((hidxL b w).mpr (.inr ⟨ro', hm', hw⟩))
              · subst hw
                exact Claim.mem_insSorted_self _ _ _
        have hvalsM : ∀ p ∈ Claim.insSorted a' (.field (roleNum ro + 1)) esL,
            ∃ ro' : Ix.Kernel.Role, p.2 = .field (roleNum ro' + 1) := by
          intro p hp
          rcases (hidxM p.1 p.2).mp hp with h0 | ⟨ro', -, hw⟩
          · exact hvals p h0
          · exact ⟨ro', hw⟩
        -- the right subtree
        have hnext_eq : ((rb.toNat : F) + 1) = ((ro.idx + 1 : Nat) : F) := by
          rw [← hro, Nat.cast_add, Nat.cast_one]
        rw [hnext_eq] at ev537
        obtain ⟨extR, lbR, restR, roleR, byAddrR, sR, nxtR, entsR, esR, htupR, hlenR, hbsR, hsR,
          hascR, hnxtR1, hnxtR2, hrangeR, hentR, hbndR, hbstR, hidxR⟩ :=
          ih ((n' + 1) - ((n' + 1) / 2 + 1)) (by omega) (by omega) (ro.idx + 1) _
            (by omega) hbstM hvalsM (L1.Stream.mono ext_ins hs2) ev537
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupR
        obtain ⟨rfl, rfl, rfl, rfl⟩ := htupR
        -- the node
        have extSnoc1 := Heap.Extends.snoc m525 x_left
        have extSnoc2 := Heap.Extends.snoc (m525 ++ [x_left]) x_right
        have extPost := extSnoc1.trans extSnoc2
        have extMid := ext_addr.trans (ext_ins.trans (extR.trans extPost))
        have ldL : loadValue ((m525 ++ [x_left]) ++ [x_right]) (.ptr x_left.type m525.length) =
            .ok x_left := extSnoc2.loadValue_eq (L1.loadValue_snoc m525 x_left)
        have ldR : loadValue ((m525 ++ [x_left]) ++ [x_right])
            (.ptr x_right.type (m525 ++ [x_left]).length) = .ok x_right :=
          L1.loadValue_snoc (m525 ++ [x_left]) x_right
        refine ⟨extL.trans extMid, lbL ++ [(ro, a')] ++ lbR, restR, _, _, _, nxtR,
          entsL ++ [(rb.toNat, x_a)] ++ entsR, esR, rfl, ?_, ?_, hsR.mono extPost, ?_,
          by omega, hnxtR2, ?_, ?_, ?_, hbstR.mono extPost, ?_⟩
        · simp only [List.length_append, List.length_singleton, hlenL, hlenR]
          omega
        · -- the bytes
          have hb1 : bs1 = a'.toList ++ bs1.drop 32 := by
            rw [← ha', takeAddress_toList hlen_a, List.take_append_drop]
          have hrb : ro.idx.toUInt8 = rb := by
            rw [hro, Ix.Kernel.RoleTable.toNat_toUInt8]
          rw [hbsL, hb1, hbsR]
          simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            Ix.Kernel.RoleTable.encBound, encAddr_ixAddr, hrb, List.append_assoc,
            List.cons_append, List.nil_append, List.append_nil]
        · -- ascending
          rw [List.pairwise_append, List.pairwise_append]
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
        · exact .node ldL ldR (hentL.mono extMid) (hentR.mono extPost)
        · refine forall₂_append (forall₂_append (hbndL.mono extMid) ?_) (hbndR.mono extPost)
          exact .cons ⟨hro.symm,
            Bytes.repAddressRef_heapMono₂ addrTy (ext_ins.trans (extR.trans extPost)) haddr_rep⟩
            .nil
        · intro b w
          rw [hidxR b w, hidxM b w]
          constructor
          · rintro ((h0 | ⟨ro', hm, hw⟩) | ⟨ro', hm, hw⟩)
            · exact .inl h0
            · exact .inr ⟨ro', List.mem_append_left _ hm, hw⟩
            · exact .inr ⟨ro', List.mem_append_right _ hm, hw⟩
          · rintro (h0 | ⟨ro', hm, hw⟩)
            · exact .inl (.inl h0)
            · rcases List.mem_append.mp hm with hm | hm
              · exact .inl (.inr ⟨ro', hm, hw⟩)
              · exact .inr ⟨ro', hm, hw⟩

end IxVM.Refinement.RoleVal
