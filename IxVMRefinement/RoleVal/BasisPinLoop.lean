import IxVMRefinement.RoleVal.TableParse
import IxVMRefinement.RoleVal.BasisPins
import IxVMRefinement.Lib.Bytes
import Ix.IxVM.Consistency.TableValid

/-! # The basis pin loop of `KernelRoles::load_role_table`

`assert_basis_pinned(tbl, r)` runs inside the load, on the heap right after the table node is
stored, and compares a pinned role's bound address with its pin only where `role_is_bound`
answers 1. On the table the load just built the role map is a search tree over exactly the
pairs read (`TableParse`), so `role_is_bound` answers 1 at every role read
(`role_is_bound_parsed`) and the loop pins every prelude role the table binds
(`assert_basis_pinned_loop`).

* `ParsedBindings h tbl lb`: the table node at `tbl`, its role map with exactly the entries `lb`
  (ascending), its address index with exactly one entry per pair.
* `load_role_table_bindings`: the load's observation gives `ParsedBindings` at the heap where the
  loop runs, and the loop's observation.
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

/-- **The bindings of a table node, exactly**: the node at `tbl`; its role map has exactly the
pairs `lb` as entries, roles ascending; its address index holds exactly one entry per pair, at
the pair's address, the role's number plus one. -/
def ParsedBindings (h : Heap F) (tbl : SourceValue F)
    (lb : List (Ix.Kernel.Role × Bytes.Address)) : Prop :=
  lb.Pairwise (fun p q => p.1.idx < q.1.idx) ∧
  ∃ (bp byRole byAddr ev : SourceValue F) (ents : List (Nat × SourceValue F))
    (es : List (Bytes.Address × SourceValue F)),
    loadValue h tbl = .ok (.construct rtEnum "Mk" [bp, byRole, byAddr, ev]) ∧
    RoleMapEntries roleAddrMapEnum h ents byRole ∧ BoundEntriesOf h lb ents ∧
    Claim.RBTreeBST .field h es byAddr ∧ IndexEntriesOf [] lb es

theorem ParsedBindings.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂) {tbl : SourceValue F}
    {lb : List (Ix.Kernel.Role × Bytes.Address)} (hp : ParsedBindings h₁ tbl lb) :
    ParsedBindings h₂ tbl lb := by
  obtain ⟨hasc, bp, byRole, byAddr, ev, ents, es, hl, hent, hbnd, hbst, hidx⟩ := hp
  exact ⟨hasc, bp, byRole, byAddr, ev, ents, es, ext.loadValue_eq hl, hent.mono ext,
    hbnd.mono ext, hbst.mono ext, hidx⟩

/-- The keys of entries paired with ascending roles are ascending and small. -/
theorem keys_of_forall₂ {R : (Ix.Kernel.Role × Bytes.Address) → (Nat × SourceValue F) → Prop}
    (hR : ∀ p q, R p q → q.1 = p.1.idx) :
    ∀ {lb : List (Ix.Kernel.Role × Bytes.Address)} {ents : List (Nat × SourceValue F)},
      List.Forall₂ R lb ents → lb.Pairwise (fun p q => p.1.idx < q.1.idx) →
      ents.Pairwise (fun p q => p.1 < q.1) ∧ ∀ p ∈ ents, p.1 < 4294967296
  | [], [], .nil, _ => ⟨.nil, by simp⟩
  | p :: lb', q :: ents', .cons hpq ht, hasc => by
    rw [List.pairwise_cons] at hasc
    obtain ⟨ih1, ih2⟩ := keys_of_forall₂ hR ht hasc.2
    refine ⟨List.pairwise_cons.mpr ⟨fun q' hq' => ?_, ih1⟩, fun q' hq' => ?_⟩
    · obtain ⟨p', hp', hrel⟩ := forall₂_mem_right ht q' hq'
      rw [hR _ _ hpq, hR _ _ hrel]
      exact hasc.1 p' hp'
    · rcases List.mem_cons.mp hq' with rfl | hq'
      · rw [hR _ _ hpq]
        have := p.1.idx_lt
        omega
      · exact ih2 q' hq'

/-! ## The role lookups on the parsed table -/

/-- **`role_bound_addr_or_zero` at a role read** returns the role's address. -/
theorem role_bound_addr_or_zero_parsed {h : Heap F} {tbl : SourceValue F}
    {lb : List (Ix.Kernel.Role × Bytes.Address)} (hp : ParsedBindings h tbl lb)
    {ro : Ix.Kernel.Role} {a : Bytes.Address} (hm : (ro, a) ∈ lb)
    {r : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::role_bound_addr_or_zero" [tbl, .field (roleNum ro)] h r h' cs) :
    Bytes.RepAddressRef addrTy h' a r := by
  obtain ⟨hasc, bp, byRole, byAddr, evm, ents, es, hl, hent, hbnd, -, -⟩ := hp
  let c₀ : Ctx := { E := default, env := default, t := default, lim := none }
  obtain ⟨res, hs, hres⟩ :=
    role_bound_addr_or_zero_step (ScopedCtx.unrestricted c₀) ev tbl (roleNum ro) rfl byRole
      ⟨bp, byAddr, evm, hl⟩
  obtain ⟨⟨k, v⟩, hq, hk, hrep⟩ := forall₂_mem_left hbnd (ro, a) hm
  simp only at hk
  subst hk
  obtain ⟨hpw, hlt⟩ := keys_of_forall₂ (fun _ _ h => h.1) hbnd hasc
  have hres' := hent.search_of_mem hpw hlt hq hs
  subst hres'
  rcases hres with hsome | ⟨hnone, _⟩
  · injection hsome with hr
    subst hr
    exact Bytes.repAddressRef_heapMono₂ addrTy ev.heap_extends hrep
  · cases hnone

/-- **`role_is_bound` answers 1 at a role read.** -/
theorem role_is_bound_parsed {h : Heap F} {tbl : SourceValue F}
    {lb : List (Ix.Kernel.Role × Bytes.Address)} (hp : ParsedBindings h tbl lb)
    {ro : Ix.Kernel.Role} {a : Bytes.Address} (hm : (ro, a) ∈ lb)
    {r : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::role_is_bound" [tbl, .field (roleNum ro)] h r h' cs) :
    r = .field 1 := by
  cases Obs.«KernelRoles::role_is_bound».obs ev with
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he103 _ _ => exact he103
  | other v1 m2 cs12 v31 x40 y41 m42 cs51 v55 m65 cs73 ev14 ev75 ev53 op97 op47 hne106 _ _ _ =>
    exfalso
    have hrep := role_bound_addr_or_zero_parsed hp hm ev14
    obtain ⟨-, bp, byRole, byAddr, evm, ents, es, hl, -, -, hbst, hidx⟩ :=
      hp.mono ev14.heap_extends
    obtain ⟨w20, w21, xba, w22, ld12, hr55, hm65, -⟩ := Obs.«KernelRoles::role_addr_index».obs ev75
    rw [hl] at ld12
    injection ld12 with hv
    injection hv with _ _ hxs
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨-, -, hba, -⟩ := hxs
    rw [hr55, ← hba] at ev53
    subst hm65
    rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev53
    obtain ⟨hx40, -⟩ := Claim.rbtree_map_lookup_or_default_spec hrep hbst ev53
    have hmem : (a, (.field (roleNum ro + 1) : SourceValue F)) ∈ es :=
      (hidx a _).mpr (.inr ⟨ro, hm, rfl⟩)
    rw [Claim.lookupEntries_eq_of_mem hbst.2 hmem] at hx40
    subst hx40
    obtain rfl := RolesAux.evalBinOp_add_field_inv op97
    simp only [evalBinOp, sub_self, Except.ok.injEq] at op47
    exact hne106 op47.symm

/-! ## The loop -/

set_option maxRecDepth 100000 in
/-- The prelude roles are the roles below 37 that `basis_pin` pins. -/
theorem prelude_idx_lt : ∀ ro ∈ IxVM.Consistency.preludeRoles, ro.idx < 37 := by
  intro ro hr
  cases ro <;> simp [IxVM.Consistency.preludeRoles, Ix.Kernel.preludeShape] at hr
  all_goals decide

private theorem seg1_extends {p w t x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (sg : Obs.«KernelRoles::assert_basis_pinned».Seg1 p w t x h r h' cs) : Heap.Extends h h' := by
  cases sg with
  | n1 m82 y91 cs102 v136 m139 cs147 v150 m153 cs161 ev104 op97 ev163 ev149 heq193 he196 he197
      hc198 =>
    subst he197
    exact ev104.heap_extends.trans (ev163.heap_extends.trans ev149.heap_extends)
  | other v81 m82 y91 cs102 ev104 op97 hne199 he205 he206 hc207 =>
    subst he206
    exact ev104.heap_extends

/-- **`KernelRoles::assert_basis_pinned(tbl, k)` on the parsed table**: every prelude role from
`k` on that the table binds is bound at the committed default table's address. -/
theorem assert_basis_pinned_loop {h₀ : Heap F} {tbl : SourceValue F}
    {lb : List (Ix.Kernel.Role × Bytes.Address)} (hp : ParsedBindings h₀ tbl lb) :
    ∀ (n k : Nat), k + n = 37 →
      ∀ {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}, Heap.Extends h₀ h →
        ObsFn W "KernelRoles::assert_basis_pinned" [tbl, .field (k : F)] h r h' calls →
        ∀ ro ∈ IxVM.Consistency.preludeRoles, k ≤ ro.idx → ∀ a, (ro, a) ∈ lb →
          committedDefaultRoleTable.addressOf? ro = some (ixAddr a) := by
  intro n
  induction n with
  | zero =>
    intro k hk r h h' calls ext ev ro hro hle a hm
    have := prelude_idx_lt ro hro
    omega
  | succ n ih =>
    intro k hk r h h' calls ext ev ro hro hle a hm
    cases Obs.«KernelRoles::assert_basis_pinned».obs ev with
    | n0 y11 x19 m21 cs30 ev32 op26 op17 _ _ _ =>
      exfalso
      obtain ⟨rfl, -, -⟩ := Obs.«KernelRoleSpec::role_quot_sound».obs ev32
      obtain rfl := RolesAux.evalBinOp_add_field_inv op26
      obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op17
      have e1 : ((k : Nat) : F) = 36 + 1 := (Value.field.inj hx1).trans (Value.field.inj hx2).symm
      have e : ((k : Nat) : F) = ((37 : Nat) : F) := by
        rw [e1]
        norm_num
      have := Claim.natCast_inj_of_lt_u32 (by omega) (by decide) e
      omega
    | other v1 y11 x19 m21 cs30 m47 cs57 x_pinned x_want v208 m209 cs211 cs220 v224
        ev32 op26 op17 hne42 ev59 sg216 op245 ev222 hc247 =>
      obtain ⟨rfl, hm21, -⟩ := Obs.«KernelRoleSpec::role_quot_sound».obs ev32
      subst hm21
      obtain rfl := RolesAux.evalBinOp_add_field_inv op245
      have ext47 : Heap.Extends h₀ m47 := ext.trans ev59.heap_extends
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · subst heq
        obtain ⟨rfl, a₀, ha₀, hwant⟩ := basis_pin_prelude hro ev59
        obtain ⟨b₀, hb₀, hix⟩ := hwant
        cases sg216 with
        | n1 m82 y91 cs102 v136 m139 cs147 v150 m153 cs161 ev104 op97 ev163 ev149 heq193 _ _ _ =>
          have hrep := role_bound_addr_or_zero_parsed
            (hp.mono (ext47.trans ev104.heap_extends)) hm ev163
          have hb₀' := Bytes.repAddressRef_heapMono₂ addrTy
            (ev104.heap_extends.trans ev163.heap_extends) hb₀
          obtain ⟨hv, -⟩ := Lib.address_eq_spec ev149 hrep hb₀'
          rw [heq193] at hv
          by_cases hab : a = b₀
          · rw [ha₀, ← hix, hab]
          · rw [if_neg hab] at hv
            exact absurd (Value.field.inj hv) one_ne_zero
        | other v81 m82 y91 cs102 ev104 op97 hne199 _ _ _ =>
          exfalso
          have h1 := role_is_bound_parsed (hp.mono ext47) hm ev104
          subst h1
          simp only [evalBinOp, mul_one, Except.ok.injEq] at op97
          exact hne199 op97.symm
      · exact ih (k + 1) (by omega) (ext47.trans (seg1_extends sg216))
          (by rw [Nat.cast_add, Nat.cast_one]; exact ev222) ro hro hlt a hm

/-! ## The load, up to the loop -/

/-- **The load builds the parsed bindings and runs the loop on them**: at the heap where
`assert_basis_pinned(tbl, 0)` starts, the node the load returned has the bindings it read
exactly (`ParsedBindings`). -/
theorem load_role_table_bindings {x_a x_tbl : SourceValue F} {h h₁ : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::load_role_table" [x_a] h x_tbl h₁ cs) :
    ∃ (hP : Heap F) (lb : List (Ix.Kernel.Role × Bytes.Address)) (v : SourceValue F)
      (cs' : List (Call F)),
      ParsedBindings hP x_tbl lb ∧
      ObsFn W "KernelRoles::assert_basis_pinned" [x_tbl, .field 0] hP v h₁ cs' := by
  obtain ⟨v1, m14, cs24, x_idx, x_len, v55, m56, cs66, v92, m93, cs103,
    m123, cs133, x_t0, x_s, v168, m171, cs179, m198, cs208, x_t1, x_s_222,
    v244, m247, cs255, m274, cs284, x_version, x_s_298, v320, v321, m323, cs331,
    m343, cs351, m356, cs366, x_n, x_s_380, m392, cs402, v406, m417, cs425,
    x_by_role, x_by_addr, x__next, x_s_454, m476, cs486, x_m, x_s_500,
    m512, cs522, v526, m536, cs544, x_evidence, x__next_564, x_s_565,
    v581, m582, cs592, m619, v665, m666, cs676,
    ld11, ev26, ev68, ev105, ev135, ev181, _, ev210, ev257, _,
    ev286, ev333, ev353, _, ev368, ev427, ev404, ev488, ev546, ev524,
    ev594, ld613, hm629, ev678, rfl, rfl, hc636⟩ := Obs.«KernelRoles::load_role_table».obs ev
  obtain ⟨bytes, _, ext1, ext2, hst, -, -⟩ := L1.checked_read ev26 ev68 ev105
  have hst0 : L1.Stream m93 bytes v55 := hst.mono ext2
  obtain ⟨rfl, b0, r0, p0, rfl, hs0, ht0⟩ := Deserialize.readByte_refines hst0 ev135.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht0
  obtain ⟨rfl, rfl⟩ := ht0
  obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev181
  obtain ⟨rfl, b1, r1, p1, rfl, hs1, ht1⟩ := Deserialize.readByte_refines hs0 ev210.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht1
  obtain ⟨rfl, rfl⟩ := ht1
  obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev257
  obtain ⟨rfl, b2, r2, p2, rfl, hs2, ht2⟩ := Deserialize.readByte_refines hs1 ev286.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht2
  obtain ⟨rfl, rfl⟩ := ht2
  obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev333
  obtain ⟨-, rfl, -⟩ := Obs.«KernelRoleSpec::spec_version».obs ev353
  obtain ⟨rfl, b3, r3, p3, rfl, hs3, ht3⟩ := Deserialize.readByte_refines hs2 ev368.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht3
  obtain ⟨rfl, rfl⟩ := ht3
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev427
  have hbst0 : Claim.RBTreeBST .field m356 []
      (.construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []) := by
    change Claim.RBTreeBST .field _ [] (.construct addrMapEnum "Nil" [])
    rw [← Claim.rbtreeEnum_field]
    exact Claim.RBTreeBST.nil .field _
  obtain ⟨extB, lb, rest, roleMap, byAddr', restPtr, nxt', ents, es', htup, -, -, -, hasc, -, -,
    -, hent, hbnd, hbst, hidx⟩ :=
    read_role_bindings_parse b3.toNat (UInt8.toNat_lt b3) 0 [] (by omega) hbst0 (by simp) hs3
      (by rw [Nat.cast_zero]; exact ev404)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  obtain ⟨rfl, rfl, -, -⟩ := htup
  subst hm629
  have ext : Heap.Extends m392 (m582 ++ [.construct rtEnum "Mk"
      [x_a, x_by_role, x_by_addr, x_evidence]]) :=
    ev488.heap_extends.trans (ev546.heap_extends.trans (ev524.heap_extends.trans
      (ev594.heap_extends.trans (Heap.Extends.snoc m582 _))))
  exact ⟨_, lb, v665, cs676,
    ⟨hasc, x_a, x_by_role, x_by_addr, x_evidence, ents, es',
      Claim.loadValue_snoc_construct m582 rtEnum "Mk" [x_a, x_by_role, x_by_addr, x_evidence],
      hent.mono ext, hbnd.mono ext, hbst.mono ext, hidx⟩, ev678⟩

end IxVM.Refinement.RoleVal
