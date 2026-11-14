import IxVMRefinement.Claim.Constant
import IxVMRefinement.Claim.Decode
import IxVMRefinement.Obs.Ingress0
import IxVMRefinement.Obs.IxVMCompat0

/-! # Claimable-seed refusals and closure walking for L6

Refines `KernelClaim` and `IxVMCompat` claim-walk functions:
* `const_idxs_expr`, `const_idxs_exprs`, `const_idxs_rules`, `const_idxs_ctors`,
  `const_idxs_muts`, `const_idxs_of`, and `g_list_has` against `S0.usedRefIdxs`;
* `Ingress::defn_is_unsafe_ci`, `ctors_unsafe`, `muts_unsafe`, `record_unsafe`, and
  `assert_claimable` against `IxVM.Consistency.InLogic` and `IxVM.Consistency.InertAt`;
* `run_check`, `run_check_transitive`, `walk_refs_transitive`, `IxVMCompat::check_owned`,
  `env_walk_all`, `env_walk_refs_all`, and `walk_leaves_owned` producing a closed list of
  walked and checked records (`WalkedRec`, `RecsClosed`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Monotonicity helpers and walked-record invariants -/

theorem checkedAt_mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hc : S0.CheckedAt cs₁ t a) :
    S0.CheckedAt cs₂ t a := by
  obtain ⟨cl, hmem, hname, rc, v, ap, lim, hargs, hrc, had⟩ := hc
  exact ⟨cl, hsub cl hmem, hname, rc, v, ap, lim, hargs, hrc, had⟩

/-- A record loaded, hashed, decoded, and checked (or observed as a mutual block) during the
claim walk. -/
structure WalkedRec (calls : List (Call F)) (t : Ix.Kernel.RoleTable) where
  addr : _root_.Address
  rawBytes : ByteArray
  c : Ixon.Constant
  hsz : rawBytes.size < 4294967296
  hhashed : Hashed calls rawBytes
  hblake : Address.blake3Pure rawBytes = addr
  hde : Ixon.deConstant rawBytes = .ok c
  hdeExact : Ixon.deConstantExact rawBytes = .ok c
  hchecked : (∃ ms, c.info = .muts ms) ∨ S0.CheckedAt calls t addr

/-- Lift a `WalkedRec` along call-list inclusion. -/
def WalkedRec.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (r : WalkedRec cs₁ t) : WalkedRec cs₂ t where
  addr := r.addr
  rawBytes := r.rawBytes
  c := r.c
  hsz := r.hsz
  hhashed := hashed_mono hsub r.hhashed
  hblake := r.hblake
  hde := r.hde
  hdeExact := r.hdeExact
  hchecked := r.hchecked.elim .inl (fun hc => .inr (checkedAt_mono hsub hc))

@[simp]
theorem map_addr_walkedRec_mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (recs : List (WalkedRec cs₁ t)) :
    (recs.map (WalkedRec.mono hsub)).map (·.addr) = recs.map (·.addr) := by
  induction recs with
  | nil => rfl
  | cons r rs ih => simp [WalkedRec.mono, ih]

/-- Edge-closure of a list of walked records under owner blocks and `S0.usedRefIdxs`. -/
def RecsClosed {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (recs : List (WalkedRec calls t)) : Prop :=
  ∀ r ∈ recs,
    (Ix.Cert.ownerOf r.addr r.c ≠ r.addr → Ix.Cert.ownerOf r.addr r.c ∈ recs.map (·.addr)) ∧
    (∀ i ∈ S0.usedRefIdxs r.c, ∀ b, r.c.refs[i]? = some b → b ∈ recs.map (·.addr))

theorem RecsClosed.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (WalkedRec cs₁ t)}
    (hcl : RecsClosed recs) :
    RecsClosed (recs.map (WalkedRec.mono hsub)) := by
  intro r' hr'
  rw [List.mem_map] at hr'
  obtain ⟨r, hr, rfl⟩ := hr'
  rw [map_addr_walkedRec_mono]
  exact hcl r hr

theorem RecsClosed.append {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {r₁ r₂ : List (WalkedRec calls t)} (h₁ : RecsClosed r₁) (h₂ : RecsClosed r₂) :
    RecsClosed (r₁ ++ r₂) := by
  intro r hr
  rw [List.map_append]
  rcases List.mem_append.mp hr with hr1 | hr2
  · obtain ⟨ho, hu⟩ := h₁ r hr1
    exact ⟨fun hne => List.mem_append_left _ (ho hne),
      fun i hi b hb => List.mem_append_left _ (hu i hi b hb)⟩
  · obtain ⟨ho, hu⟩ := h₂ r hr2
    exact ⟨fun hne => List.mem_append_right _ (ho hne),
      fun i hi b hb => List.mem_append_right _ (hu i hi b hb)⟩

theorem RecsClosed.cons {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {r₀ : WalkedRec calls t} {rest : List (WalkedRec calls t)}
    (hrest : RecsClosed rest)
    (hown : Ix.Cert.ownerOf r₀.addr r₀.c ≠ r₀.addr →
      Ix.Cert.ownerOf r₀.addr r₀.c ∈ (r₀ :: rest).map (·.addr))
    (hrefs : ∀ i ∈ S0.usedRefIdxs r₀.c, ∀ b, r₀.c.refs[i]? = some b →
      b ∈ (r₀ :: rest).map (·.addr)) :
    RecsClosed (r₀ :: rest) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hmem
  · exact ⟨hown, hrefs⟩
  · obtain ⟨ho, hu⟩ := hrest r hmem
    exact ⟨fun hne => List.mem_cons_of_mem _ (ho hne),
      fun i hi b hb => List.mem_cons_of_mem _ (hu i hi b hb)⟩

/-- Refusal postcondition established by `KernelClaim::assert_claimable` at seed `a`. -/
structure ClaimableSeed (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (a : _root_.Address) : Prop where
  notInert : ¬ IxVM.Consistency.InertAt t a
  selfSafe : ∃ raw₁ c₁,
    Hashed calls raw₁ ∧ Address.blake3Pure raw₁ = a ∧
    Ixon.deConstant raw₁ = .ok c₁ ∧ IxVM.Consistency.InLogic c₁
  ownerCase : ∃ raw₀ c₀,
    Hashed calls raw₀ ∧ Address.blake3Pure raw₀ = a ∧
    Ixon.deConstant raw₀ = .ok c₀ ∧
    (Ix.Cert.ownerOf a c₀ = a ∨
      ∃ rawB cb, Hashed calls rawB ∧
        Address.blake3Pure rawB = Ix.Cert.ownerOf a c₀ ∧
        Ixon.deConstant rawB = .ok cb ∧ IxVM.Consistency.InLogic cb)

theorem ClaimableSeed.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hs : ClaimableSeed cs₁ t a) :
    ClaimableSeed cs₂ t a := by
  obtain ⟨hn, ⟨raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩, ⟨raw₀, c₀, hh₀, hb₀, hd₀, hown⟩⟩ := hs
  refine ⟨hn, ⟨raw₁, c₁, hashed_mono hsub hh₁, hb₁, hd₁, hl₁⟩,
    ⟨raw₀, c₀, hashed_mono hsub hh₀, hb₀, hd₀, ?_⟩⟩
  rcases hown with heq | ⟨rawB, cb, hhB, hbB, hdB, hlB⟩
  · exact .inl heq
  · exact .inr ⟨rawB, cb, hashed_mono hsub hhB, hbB, hdB, hlB⟩

/-! ## `const_idxs_*` and `g_list_has` -/

/-- Element relation for `Lists::Node<Field>` holding reference-table indices `< 2^56`. -/
def RepBoundedIdx (_h : Heap F) (k : Nat) (v : SourceValue F) : Prop :=
  k < 72057594037927936 ∧ v = .field (k : F)

theorem repBoundedIdx_heapMono₂ : HeapMono₂ RepBoundedIdx :=
  fun _ _ _ _ _ h => h

private theorem natCast_inj_of_lt_u56 {a b : Nat}
    (ha : a < 72057594037927936) (hb : b < 72057594037927936)
    (heq : (a : F) = (b : F)) : a = b := by
  have hva : ZMod.val (a : F) = a :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hvb : ZMod.val (b : F) = b :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hv := congrArg ZMod.val heq
  omega

private theorem concat_boundedIdx_spec {xs ys : List Nat} {a b r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::concat<Field>» [a, b] h r h' cs)
    (ha : RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h xs a)
    (hb : RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h ys b) :
    Heap.Extends h h' ∧
    RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h' (xs ++ ys) r := by
  have ext := ev.heap_extends
  rw [← Obs.Names.«Lists::concat<Field>».symbol] at ev
  rw [← Obs.Names.«Lists::Node<Field>».symbol] at ha hb ⊢
  exact ⟨ext, Lib.Lists.concat_spec (t := .field) repBoundedIdx_heapMono₂ ev ha hb⟩

theorem const_idxs_expr_spec (e : Ixon.Expr) :
    ∀ {h h' : Heap F} {x_e r : SourceValue F} {calls : List (Call F)},
      Deserialize.RepExpr h e x_e →
      ObsFn Obs.W "KernelClaim::const_idxs_expr" [x_e] h r h' calls →
      Heap.Extends h h' ∧
      RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h' (S0.exprRefIdxs e) r := by
  induction e with
  | sort idx =>
    intro h h' x_e r calls rep ev
    cases rep with
    | sort cell =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, _, _, _, rfl, rfl, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
  | var idx =>
    intro h h' x_e r calls rep ev
    cases rep with
    | var cell =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, _, _, _, rfl, rfl, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
  | ref idx univs =>
    intro h h' x_e r calls rep ev
    cases rep with
    | ref cell _ =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨x_i, w20, v39, m42, cs50, m62, ld12, rfl, rfl, ev52, rfl, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, hne75, -⟩
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq] at hargs
        obtain ⟨hxi, -⟩ := hargs
        rw [← hxi] at ev52
        obtain ⟨hlt, hv39, hm42⟩ :=
          Lib.u64_to_field_spec (Deserialize.repU64_u64Value h idx) ev52
        rw [hv39, hm42]
        have ext1 := Heap.Extends.snoc h
          (.construct Obs.Names.«Lists::Node<Field>» "Nil" [])
        have ext2 := Heap.Extends.snoc
          (h ++ [.construct Obs.Names.«Lists::Node<Field>» "Nil" []])
          (.construct Obs.Names.«Lists::Node<Field>» "Cons"
            [.field (idx.toNat : F), .ptr (.enum Obs.Names.«Lists::Node<Field>») h.length])
        exact ⟨ext1.trans ext2,
          Lib.rep_store_cons repBoundedIdx_heapMono₂ ⟨hlt, rfl⟩ (Lib.rep_store_nil h)⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        exact absurd hv.symm (hne75 [_, _] rfl)
  | recur idx univs =>
    intro h h' x_e r calls rep ev
    cases rep with
    | recur cell _ =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, _, _, _, rfl, rfl, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
  | prj tIdx fIdx val ih =>
    intro h h' x_e r calls rep ev
    cases rep with
    | prj cell valRep =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨x_i, w82, x_inner, v106, v107, m109, cs117, m129, cs137,
          ld12, rfl, rfl, ev119, ev139, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, hne149, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨hxi, _, hxinner⟩ := hargs
        rw [← hxi] at ev119
        rw [← hxinner] at ev139
        obtain ⟨hlt, hv106, hm109⟩ :=
          Lib.u64_to_field_spec (Deserialize.repU64_u64Value h tIdx) ev119
        rw [hm109] at ev139
        rw [hv106]
        obtain ⟨ext_in, hrep_in⟩ := ih valRep ev139
        exact ⟨ext_in.trans (Heap.Extends.snoc m129 _),
          Lib.rep_store_cons repBoundedIdx_heapMono₂ ⟨hlt, rfl⟩ hrep_in⟩
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        exact absurd hv.symm (hne149 [_, _, _] rfl)
  | str idx =>
    intro h h' x_e r calls rep ev
    cases rep with
    | str cell =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, _, _, _, rfl, rfl, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
  | nat idx =>
    intro h h' x_e r calls rep ev
    cases rep with
    | nat cell =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, _, _, _, rfl, rfl, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
  | app fnE arg ih1 ih2 =>
    intro h h' x_e r calls rep ev
    cases rep with
    | app cell fnRep argRep =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨x_f, x_a, cs169, v172, v173, m175, cs183, m195, cs203,
          ld12, ev185, ev205, ev171, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, hne215, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl⟩ := hargs
        obtain ⟨ext1, h1⟩ := ih1 fnRep ev185
        obtain ⟨ext2, h2⟩ := ih2 (argRep.mono ext1) ev205
        obtain ⟨ext3, hcat⟩ :=
          concat_boundedIdx_spec ev171 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
        exact ⟨ext1.trans (ext2.trans ext3), hcat⟩
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        exact absurd hv.symm (hne215 [_, _] rfl)
  | lam ty body ih1 ih2 =>
    intro h h' x_e r calls rep ev
    cases rep with
    | lam cell tyRep bodyRep =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨x_t, x_b, cs235, v238, v239, m241, cs249, m261, cs269,
          ld12, ev251, ev271, ev237, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, hne281, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl⟩ := hargs
        obtain ⟨ext1, h1⟩ := ih1 tyRep ev251
        obtain ⟨ext2, h2⟩ := ih2 (bodyRep.mono ext1) ev271
        obtain ⟨ext3, hcat⟩ :=
          concat_boundedIdx_spec ev237 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
        exact ⟨ext1.trans (ext2.trans ext3), hcat⟩
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        exact absurd hv.symm (hne281 [_, _] rfl)
  | all ty body ih1 ih2 =>
    intro h h' x_e r calls rep ev
    cases rep with
    | all cell tyRep bodyRep =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨x_t, x_b, cs301, v304, v305, m307, cs315, m327, cs335,
          ld12, ev317, ev337, ev303, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, _, hne347, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl⟩ := hargs
        obtain ⟨ext1, h1⟩ := ih1 tyRep ev317
        obtain ⟨ext2, h2⟩ := ih2 (bodyRep.mono ext1) ev337
        obtain ⟨ext3, hcat⟩ :=
          concat_boundedIdx_spec ev303 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
        exact ⟨ext1.trans (ext2.trans ext3), hcat⟩
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        exact absurd hv.symm (hne347 [_, _] rfl)
  | letE nonDep mode ty val body ih1 ih2 ih3 =>
    intro h h' x_e r calls rep ev
    cases rep with
    | letE cell tyRep valRep bodyRep =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨w354, x_t, x_v, x_b, cs378, v381, v382, m384, cs392, m404, cs412,
          v415, v416, m418, cs426, m438, cs446,
          ld12, ev394, ev428, ev448, ev414, ev380, -⟩ |
        ⟨v1, ld12, _, _, _, _, _, hne458, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨_, rfl, rfl, rfl⟩ := hargs
        obtain ⟨ext1, h1⟩ := ih1 tyRep ev394
        obtain ⟨ext2, h2⟩ := ih2 (valRep.mono ext1) ev428
        obtain ⟨ext3, h3⟩ := ih3 (bodyRep.mono (ext1.trans ext2)) ev448
        obtain ⟨ext4, h23⟩ :=
          concat_boundedIdx_spec ev414 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext3 h2) h3
        obtain ⟨ext5, h123⟩ :=
          concat_boundedIdx_spec ev380
            (repList_heapMono₂ _ repBoundedIdx_heapMono₂ (ext2.trans (ext3.trans ext4)) h1) h23
        simp only [S0.exprRefIdxs, List.append_assoc]
        exact ⟨ext1.trans (ext2.trans (ext3.trans (ext4.trans ext5))), h123⟩
      · rw [Lib.load_enum_cell cell] at ld12
        injection ld12 with hv
        exact absurd hv.symm (hne458 [_, _, _, _] rfl)
  | share idx =>
    intro h h' x_e r calls rep ev
    cases rep with
    | share cell =>
      rcases Obs.«KernelClaim::const_idxs_expr».obs ev with
        ⟨_, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
        ⟨v1, ld12, _, _, _, _, _, _, rfl, rfl, -⟩
      all_goals try (rw [Lib.load_enum_cell cell] at ld12; simp at ld12; done)
      exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩

theorem const_idxs_exprs_spec (es : List Ixon.Expr) :
    ∀ {h h' : Heap F} {x_es r : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<&Ixon::Expr>» Deserialize.RepExpr h es x_es →
      ObsFn Obs.W "KernelClaim::const_idxs_exprs" [x_es] h r h' calls →
      Heap.Extends h h' ∧
      RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h' (es.flatMap S0.exprRefIdxs) r := by
  induction es with
  | nil =>
    intro h h' x_es r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_exprs».obs ev with
      ⟨ld12, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ld12, -⟩
    · exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons e rest ih =>
    intro h h' x_es r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_exprs».obs ev with
      ⟨ld12, -⟩ | ⟨x_e, x_rest, cs49, v52, v53, m55, cs63, m75, cs83, ld12, ev65, ev85, ev51, -⟩
    · cases Lib.rep_nil_of_load rep ld12
    · obtain ⟨e', rest', heq, he, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      obtain ⟨ext1, h1⟩ := const_idxs_expr_spec e he ev65
      obtain ⟨ext2, h2⟩ :=
        ih (repList_heapMono₂ _ Deserialize.repExpr_heapMono₂ ext1 hrest) ev85
      obtain ⟨ext3, hcat⟩ :=
        concat_boundedIdx_spec ev51 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
      simpa only [List.flatMap_cons] using ⟨ext1.trans (ext2.trans ext3), hcat⟩

theorem const_idxs_rules_spec (rs : List Ixon.RecursorRule) :
    ∀ {h h' : Heap F} {x_rs r : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Ixon::RecursorRule>» RepRecursorRule h rs x_rs →
      ObsFn Obs.W "KernelClaim::const_idxs_rules" [x_rs] h r h' calls →
      Heap.Extends h h' ∧
      RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h'
        (rs.flatMap fun rl => S0.exprRefIdxs rl.rhs) r := by
  induction rs with
  | nil =>
    intro h h' x_rs r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_rules».obs ev with
      ⟨ld12, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, ld12, -⟩
    · exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons rl rest ih =>
    intro h h' x_rs r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_rules».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_rest, w62, x_rhs, cs76, v79, v80, m82, cs90, m102, cs110, ld12, ev92, ev112, ev78, -⟩
    · cases Lib.rep_nil_of_load rep ld12
    · obtain ⟨rl', rest', heq, hrl, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      obtain ⟨rhsPtr, hv, hrhs⟩ := hrl
      injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      rw [← hargs.2] at hrhs
      obtain ⟨ext1, h1⟩ := const_idxs_expr_spec rl.rhs hrhs ev92
      obtain ⟨ext2, h2⟩ :=
        ih (repList_heapMono₂ _ repRecursorRule_heapMono₂ ext1 hrest) ev112
      obtain ⟨ext3, hcat⟩ :=
        concat_boundedIdx_spec ev78 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
      simpa only [List.flatMap_cons] using ⟨ext1.trans (ext2.trans ext3), hcat⟩

theorem const_idxs_ctors_spec (cs : List Ixon.Constructor) :
    ∀ {h h' : Heap F} {x_cs r : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Ixon::Constructor>» RepConstructor h cs x_cs →
      ObsFn Obs.W "KernelClaim::const_idxs_ctors" [x_cs] h r h' calls →
      Heap.Extends h h' ∧
      RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h'
        (cs.flatMap fun c => S0.exprRefIdxs c.typ) r := by
  induction cs with
  | nil =>
    intro h h' x_cs r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_ctors».obs ev with
      ⟨ld12, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩
    · exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons ctor rest ih =>
    intro h h' x_cs r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_ctors».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_rest, w62, w63, w64, w65, w66, w67, x_typ, cs106, v109, v110, m112, cs120, m132, cs140,
        ld12, ev122, ev142, ev108, -⟩
    · cases Lib.rep_nil_of_load rep ld12
    · obtain ⟨ctor', rest', heq, hctor, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      obtain ⟨uVal, modesPtr, tPtr, hv, _, _, htyp⟩ := hctor
      injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      rw [← hargs.2.2.2.2.2.2] at htyp
      obtain ⟨ext1, h1⟩ := const_idxs_expr_spec ctor.typ htyp ev122
      obtain ⟨ext2, h2⟩ :=
        ih (repList_heapMono₂ _ repConstructor_heapMono₂ ext1 hrest) ev142
      obtain ⟨ext3, hcat⟩ :=
        concat_boundedIdx_spec ev108 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
      simpa only [List.flatMap_cons] using ⟨ext1.trans (ext2.trans ext3), hcat⟩

theorem const_idxs_muts_spec (ms : List Ixon.MutConst) :
    ∀ {h h' : Heap F} {x_ms r : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Ixon::MutConst>» RepMutConst h ms x_ms →
      ObsFn Obs.W "KernelClaim::const_idxs_muts" [x_ms] h r h' calls →
      Heap.Extends h h' ∧
      RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h' (ms.flatMap S0.mutRefIdxs) r := by
  induction ms with
  | nil =>
    intro h h' x_ms r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_muts».obs ev with
      ⟨ld12, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩
    · exact ⟨Heap.Extends.snoc h _, Lib.rep_store_nil h⟩
    all_goals (obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12; cases hbad)
  | cons mc rest ih =>
    intro h h' x_ms r calls rep ev
    rcases Obs.«KernelClaim::const_idxs_muts».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_rest, w83, w84, w85, w86, x_typ, x_value, cs120, v123, v124, m126, cs134,
        v137, v138, m140, cs148, m160, cs168, m180, cs188,
        ld12, ev150, ev170, ev136, ev190, ev122, -⟩ |
      ⟨x_rest, w229, w230, w231, w232, x_typ, x_ctors, cs266, v269, v270, m272, cs280,
        v283, v284, m286, cs294, m306, cs314, m326, cs334,
        ld12, ev296, ev316, ev282, ev336, ev268, -⟩ |
      ⟨x_rest, w375, w376, w377, w378, w379, w380, w381, x_typ, x_rules, cs430, v433, v434,
        m436, cs444, v447, v448, m450, cs458, m470, cs478, m490, cs498,
        ld12, ev460, ev480, ev446, ev500, ev432, -⟩
    · cases Lib.rep_nil_of_load rep ld12
    · obtain ⟨mc', rest', heq, hmc, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      cases mc with
      | indc _ => obtain ⟨_, hv, _⟩ := hmc; simp at hv
      | recr _ => obtain ⟨_, hv, _⟩ := hmc; simp at hv
      | defn d =>
        obtain ⟨dv, hv, kVal, sVal, aVal, tPtr, vPtr, hdv, _, _, _, htyp, hval⟩ := hmc
        rw [hdv] at hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        injection hargs with _ _ hdargs
        simp only [List.cons.injEq, and_true] at hdargs
        rw [← hdargs.2.2.2.2.1] at htyp
        rw [← hdargs.2.2.2.2.2] at hval
        obtain ⟨ext1, h1⟩ := const_idxs_expr_spec d.typ htyp ev150
        obtain ⟨ext2, h2⟩ := const_idxs_expr_spec d.value (hval.mono ext1) ev170
        obtain ⟨ext3, h12⟩ :=
          concat_boundedIdx_spec ev136 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
        obtain ⟨ext4, hrest_out⟩ :=
          ih (repList_heapMono₂ _ repMutConst_heapMono₂ (ext1.trans (ext2.trans ext3)) hrest) ev190
        obtain ⟨ext5, hcat⟩ :=
          concat_boundedIdx_spec ev122
            (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext4 h12) hrest_out
        simpa only [List.flatMap_cons, S0.mutRefIdxs] using
          ⟨ext1.trans (ext2.trans (ext3.trans (ext4.trans ext5))), hcat⟩
    · obtain ⟨mc', rest', heq, hmc, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      cases mc with
      | defn _ => obtain ⟨_, hv, _⟩ := hmc; simp at hv
      | recr _ => obtain ⟨_, hv, _⟩ := hmc; simp at hv
      | indc ind =>
        obtain ⟨iv, hv, uVal, tPtr, ctorsPtr, hiv, _, htyp, hctors⟩ := hmc
        rw [hiv] at hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        injection hargs with _ _ hiargs
        simp only [List.cons.injEq, and_true] at hiargs
        rw [← hiargs.2.2.2.2.1] at htyp
        rw [← hiargs.2.2.2.2.2] at hctors
        obtain ⟨ext1, h1⟩ := const_idxs_expr_spec ind.typ htyp ev296
        obtain ⟨ext2, h2⟩ :=
          const_idxs_ctors_spec ind.ctors.toList
            (repList_heapMono₂ _ repConstructor_heapMono₂ ext1 hctors) ev316
        obtain ⟨ext3, h12⟩ :=
          concat_boundedIdx_spec ev282 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
        obtain ⟨ext4, hrest_out⟩ :=
          ih (repList_heapMono₂ _ repMutConst_heapMono₂ (ext1.trans (ext2.trans ext3)) hrest) ev336
        obtain ⟨ext5, hcat⟩ :=
          concat_boundedIdx_spec ev268
            (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext4 h12) hrest_out
        simpa only [List.flatMap_cons, S0.mutRefIdxs] using
          ⟨ext1.trans (ext2.trans (ext3.trans (ext4.trans ext5))), hcat⟩
    · obtain ⟨mc', rest', heq, hmc, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      cases mc with
      | defn _ => obtain ⟨_, hv, _⟩ := hmc; simp at hv
      | indc _ => obtain ⟨_, hv, _⟩ := hmc; simp at hv
      | recr rc =>
        obtain ⟨rv, hv, kVal, uVal, tPtr, rulesPtr, hrv, _, _, htyp, hrules⟩ := hmc
        rw [hrv] at hv
        injection hv with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        injection hargs with _ _ hrargs
        simp only [List.cons.injEq, and_true] at hrargs
        rw [← hrargs.2.2.2.2.2.2.2.1] at htyp
        rw [← hrargs.2.2.2.2.2.2.2.2] at hrules
        obtain ⟨ext1, h1⟩ := const_idxs_expr_spec rc.typ htyp ev460
        obtain ⟨ext2, h2⟩ :=
          const_idxs_rules_spec rc.rules.toList
            (repList_heapMono₂ _ repRecursorRule_heapMono₂ ext1 hrules) ev480
        obtain ⟨ext3, h12⟩ :=
          concat_boundedIdx_spec ev446 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
        obtain ⟨ext4, hrest_out⟩ :=
          ih (repList_heapMono₂ _ repMutConst_heapMono₂ (ext1.trans (ext2.trans ext3)) hrest) ev500
        obtain ⟨ext5, hcat⟩ :=
          concat_boundedIdx_spec ev432
            (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext4 h12) hrest_out
        simpa only [List.flatMap_cons, S0.mutRefIdxs] using
          ⟨ext1.trans (ext2.trans (ext3.trans (ext4.trans ext5))), hcat⟩

theorem const_idxs_of_spec {h h' : Heap F} {c : Ixon.Constant} {x_c r : SourceValue F}
    {calls : List (Call F)}
    (rep : RepConstant h c x_c)
    (ev : ObsFn Obs.W "KernelClaim::const_idxs_of" [x_c] h r h' calls) :
    Heap.Extends h h' ∧
    RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h' (S0.usedRefIdxs c) r := by
  obtain ⟨infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr, rfl, hinfo, hsh, _, _, _⟩ := rep
  have hsh' : RepList Obs.Names.«Lists::Node<&Ixon::Expr>» Deserialize.RepExpr h
      c.sharing.toList sharingPtr := by
    simpa only [Deserialize.RepShareVec, Obs.Names.n14714430324747779335] using hsh
  rcases Obs.«KernelClaim::const_idxs_of».obs ev with
    ⟨x_sharing, _, _, _, v45, m46, cs56, w104, w105, w106, w107, x_typ, x_value,
      cs141, v145, m154, cs162, v165, v166, m168, cs176, m188, cs196,
      hv15, ev58, ev178, ev198, ev164, ev143, -⟩ |
    ⟨x_sharing, _, _, _, v45, m46, cs56, w237, w238, w239, w240, w241, w242, w243,
      x_typ, x_rules, cs292, v296, m305, cs313, v316, v317, m319, cs327, m339, cs347,
      hv15, ev58, ev329, ev349, ev315, ev294, -⟩ |
    ⟨x_sharing, _, _, _, v45, m46, cs56, w388, w389, x_typ, cs408, v412, m421, cs429,
      hv15, ev58, ev431, ev410, -⟩ |
    ⟨x_sharing, _, _, _, v45, m46, cs56, w470, w471, x_typ, cs490, v494, m503, cs511,
      hv15, ev58, ev513, ev492, -⟩ |
    ⟨x_sharing, _, _, _, v45, m46, cs56, x_members, cs539, v543, m552, cs560,
      hv15, ev58, ev562, ev541, -⟩ |
    ⟨x_info, x_sharing, _, _, _, v45, m46, cs56,
      hv15, ev58, hne209, hne360, hne442, hne524, hne572, rfl, rfl, -⟩
  · injection hv15 with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hinfo_eq, rfl, -⟩ := hargs
    rw [hinfo_eq] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case defn d =>
      obtain ⟨dv, hdv_eq, kVal, sVal, aVal, tPtr, vPtr, hdv, _, _, _, htyp, hval⟩ := hinfo
      rw [hdv] at hdv_eq
      injection hdv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hdargs
      simp only [List.cons.injEq, and_true] at hdargs
      rw [← hdargs.2.2.2.2.1] at htyp
      rw [← hdargs.2.2.2.2.2] at hval
      obtain ⟨extS, hS⟩ := const_idxs_exprs_spec c.sharing.toList hsh' ev58
      obtain ⟨ext1, h1⟩ := const_idxs_expr_spec d.typ (htyp.mono extS) ev178
      obtain ⟨ext2, h2⟩ := const_idxs_expr_spec d.value (hval.mono (extS.trans ext1)) ev198
      obtain ⟨ext3, h12⟩ :=
        concat_boundedIdx_spec ev164 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
      obtain ⟨ext4, hcat⟩ :=
        concat_boundedIdx_spec ev143
          (repList_heapMono₂ _ repBoundedIdx_heapMono₂ (ext1.trans (ext2.trans ext3)) hS) h12
      simpa only [S0.usedRefIdxs, hc] using
        ⟨extS.trans (ext1.trans (ext2.trans (ext3.trans ext4))), hcat⟩
    all_goals (obtain ⟨_, hv, _⟩ := hinfo; simp at hv)
  · injection hv15 with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hinfo_eq, rfl, -⟩ := hargs
    rw [hinfo_eq] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case recr rc =>
      obtain ⟨rv, hrv_eq, kVal, uVal, tPtr, rulesPtr, hrv, _, _, htyp, hrules⟩ := hinfo
      rw [hrv] at hrv_eq
      injection hrv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hrargs
      simp only [List.cons.injEq, and_true] at hrargs
      rw [← hrargs.2.2.2.2.2.2.2.1] at htyp
      rw [← hrargs.2.2.2.2.2.2.2.2] at hrules
      obtain ⟨extS, hS⟩ := const_idxs_exprs_spec c.sharing.toList hsh' ev58
      obtain ⟨ext1, h1⟩ := const_idxs_expr_spec rc.typ (htyp.mono extS) ev329
      obtain ⟨ext2, h2⟩ :=
        const_idxs_rules_spec rc.rules.toList
          (repList_heapMono₂ _ repRecursorRule_heapMono₂ (extS.trans ext1) hrules) ev349
      obtain ⟨ext3, h12⟩ :=
        concat_boundedIdx_spec ev315 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext2 h1) h2
      obtain ⟨ext4, hcat⟩ :=
        concat_boundedIdx_spec ev294
          (repList_heapMono₂ _ repBoundedIdx_heapMono₂ (ext1.trans (ext2.trans ext3)) hS) h12
      simpa only [S0.usedRefIdxs, hc] using
        ⟨extS.trans (ext1.trans (ext2.trans (ext3.trans ext4))), hcat⟩
    all_goals (obtain ⟨_, hv, _⟩ := hinfo; simp at hv)
  · injection hv15 with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hinfo_eq, rfl, -⟩ := hargs
    rw [hinfo_eq] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case axio a =>
      obtain ⟨av, hav_eq, uVal, tPtr, hav, _, htyp⟩ := hinfo
      rw [hav] at hav_eq
      injection hav_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ haargs
      simp only [List.cons.injEq, and_true] at haargs
      rw [← haargs.2.2] at htyp
      obtain ⟨extS, hS⟩ := const_idxs_exprs_spec c.sharing.toList hsh' ev58
      obtain ⟨ext1, h1⟩ := const_idxs_expr_spec a.typ (htyp.mono extS) ev431
      obtain ⟨ext2, hcat⟩ :=
        concat_boundedIdx_spec ev410 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext1 hS) h1
      simpa only [S0.usedRefIdxs, hc] using ⟨extS.trans (ext1.trans ext2), hcat⟩
    all_goals (obtain ⟨_, hv, _⟩ := hinfo; simp at hv)
  · injection hv15 with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hinfo_eq, rfl, -⟩ := hargs
    rw [hinfo_eq] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case quot q =>
      obtain ⟨qv, hqv_eq, kVal, tPtr, hqv, _, htyp⟩ := hinfo
      rw [hqv] at hqv_eq
      injection hqv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hqargs
      simp only [List.cons.injEq, and_true] at hqargs
      rw [← hqargs.2.2] at htyp
      obtain ⟨extS, hS⟩ := const_idxs_exprs_spec c.sharing.toList hsh' ev58
      obtain ⟨ext1, h1⟩ := const_idxs_expr_spec q.typ (htyp.mono extS) ev513
      obtain ⟨ext2, hcat⟩ :=
        concat_boundedIdx_spec ev492 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext1 hS) h1
      simpa only [S0.usedRefIdxs, hc] using ⟨extS.trans (ext1.trans ext2), hcat⟩
    all_goals (obtain ⟨_, hv, _⟩ := hinfo; simp at hv)
  · injection hv15 with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hinfo_eq, rfl, -⟩ := hargs
    rw [hinfo_eq] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case muts ms =>
      obtain ⟨mv, hmv_eq, hms⟩ := hinfo
      injection hmv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      rw [← h1] at hms
      obtain ⟨extS, hS⟩ := const_idxs_exprs_spec c.sharing.toList hsh' ev58
      obtain ⟨ext1, h1⟩ :=
        const_idxs_muts_spec ms.toList (repList_heapMono₂ _ repMutConst_heapMono₂ extS hms) ev562
      obtain ⟨ext2, hcat⟩ :=
        concat_boundedIdx_spec ev541 (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext1 hS) h1
      simpa only [S0.usedRefIdxs, hc] using ⟨extS.trans (ext1.trans ext2), hcat⟩
    all_goals (obtain ⟨_, hv, _⟩ := hinfo; simp at hv)
  · injection hv15 with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨rfl, rfl, -⟩ := hargs
    obtain ⟨extS, hS⟩ := const_idxs_exprs_spec c.sharing.toList hsh' ev58
    cases hc : c.info <;> rw [hc] at hinfo
    case defn _ => obtain ⟨_, hv, _⟩ := hinfo; exact absurd hv (hne209 [_] rfl)
    case recr _ => obtain ⟨_, hv, _⟩ := hinfo; exact absurd hv (hne360 [_] rfl)
    case axio _ => obtain ⟨_, hv, _⟩ := hinfo; exact absurd hv (hne442 [_] rfl)
    case quot _ => obtain ⟨_, hv, _⟩ := hinfo; exact absurd hv (hne524 [_] rfl)
    case muts _ => obtain ⟨_, hv, _⟩ := hinfo; exact absurd hv (hne572 [_] rfl)
    all_goals simpa only [S0.usedRefIdxs, hc, List.append_nil] using ⟨extS, hS⟩

theorem g_list_has_spec (idxs : List Nat) {i : Nat} (hi : i < 72057594037927936) :
    ∀ {h h' : Heap F} {x_xs r : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h idxs x_xs →
      ObsFn Obs.W "KernelClaim::g_list_has" [x_xs, .field (i : F)] h r h' calls →
      h' = h ∧ (r = .field 1 ↔ i ∈ idxs) := by
  induction idxs with
  | nil =>
    intro h h' x_xs r calls rep ev
    rcases Obs.«KernelClaim::g_list_has».obs ev with
      ⟨ld12, rfl, rfl, -⟩ | ⟨_, _, ld12, -⟩ | ⟨_, _, _, _, ld12, -⟩
    · simp
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons k ks ih =>
    intro h h' x_xs r calls rep ev
    rcases Obs.«KernelClaim::g_list_has».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_y, x_rest, ld12, op56, rfl, rfl, -⟩ |
      ⟨x_y, x_rest, v40, cs73, ld12, op56, hne66, ev75, -⟩
    · cases Lib.rep_nil_of_load rep ld12
    · obtain ⟨k', ks', heq, ⟨hk_lt, rfl⟩, _⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq, sub_eq_zero] at op56
      have hki : k = i := natCast_inj_of_lt_u56 hk_lt hi op56
      subst hki
      simp
    · obtain ⟨k', ks', heq, ⟨hk_lt, rfl⟩, hks⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      simp only [evalBinOp, Except.ok.injEq] at op56
      subst op56
      have hne_ki : i ≠ k := by
        intro hik
        subst hik
        exact hne66 (by simp)
      obtain ⟨hh, hiff⟩ := ih hks ev75
      exact ⟨hh, by simp [hne_ki, hiff]⟩

/-! ## `defn_is_unsafe_ci`, `ctors_unsafe`, `muts_unsafe`, `record_unsafe`, `assert_claimable` -/

private theorem repBool_eq_false_of_field_zero {b : Bool} {uVal : SourceValue F}
    (hu : RepBool b uVal) (hu0 : uVal = .field 0) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd (hu.symm.trans hu0) (fun h => one_ne_zero (Value.field.inj h))

theorem defn_is_unsafe_ci_zero_spec {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
    {x_kind x_safety : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hk : RepDefKind kind x_kind)
    (hs : RepDefinitionSafety safety x_safety)
    (ev : ObsFn Obs.W "Ingress::defn_is_unsafe_ci" [x_kind, x_safety] h (.field 0) h' calls) :
    h' = h ∧ Ix.Kernel.Reader.safetyDeclineOf kind safety = none := by
  rcases Obs.«Ingress::defn_is_unsafe_ci».obs ev with
    ⟨hv15, _, rfl, -⟩ |
    ⟨_, _, _, he43, -⟩ |
    ⟨_, hv25, hne46, _, rfl, -⟩ |
    ⟨_, _, hv58, hv74, _, rfl, -⟩ |
    ⟨_, _, _, _, he83, -⟩
  · cases kind with
    | defn => rw [RepDefKind] at hk; rw [hk] at hv15; simp at hv15
    | opaq => rw [RepDefKind] at hk; rw [hk] at hv15; simp at hv15
    | thm => exact ⟨rfl, rfl⟩
  · simp at he43
  · cases kind <;> simp [RepDefKind] at hk
    · rw [hk] at hv25; simp at hv25
    · cases safety <;> simp [RepDefinitionSafety] at hs
      · exact absurd hs (hne46 [] rfl)
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · rw [hk] at hv25; simp at hv25
  · cases kind <;> simp [RepDefKind] at hk
    · cases safety <;> simp [RepDefinitionSafety] at hs
      · rw [hs] at hv74; simp at hv74
      · exact ⟨rfl, rfl⟩
      · rw [hs] at hv74; simp at hv74
    · rw [hk] at hv58; simp at hv58
    · rw [hk] at hv58; simp at hv58
  · simp at he83

theorem ctors_unsafe_zero_spec (cs : List Ixon.Constructor) :
    ∀ {h h' : Heap F} {x_cs : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Ixon::Constructor>» RepConstructor h cs x_cs →
      ObsFn Obs.W "KernelClaim::ctors_unsafe" [x_cs] h (.field 0) h' calls →
      h' = h ∧ ∀ ctor ∈ cs, ctor.isUnsafe = false := by
  induction cs with
  | nil =>
    intro h h' x_cs calls rep ev
    rcases Obs.«KernelClaim::ctors_unsafe».obs ev with
      ⟨ld12, _, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, ld12, -⟩ | ⟨_, _, _, _, _, _, _, _, ld12, -⟩
    · exact ⟨rfl, by simp⟩
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12; cases hbad
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12; cases hbad
  | cons ctor rest ih =>
    intro h h' x_cs calls rep ev
    rcases Obs.«KernelClaim::ctors_unsafe».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_rest, _, _, _, _, _, _, cs114, ld12, ev116, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, he130, -⟩
    · cases Lib.rep_nil_of_load rep ld12
    · obtain ⟨ctor', rest', heq, hctor, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      obtain ⟨uVal, _, _, hv, hu, _, _⟩ := hctor
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      have hu0 : uVal = .field 0 := hargs.1.symm
      have hfalse : ctor.isUnsafe = false := repBool_eq_false_of_field_zero hu hu0
      obtain ⟨hh, hrest_ok⟩ := ih hrest ev116
      refine ⟨hh, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact hfalse
      · exact hrest_ok c hmem
    · simp at he130

theorem muts_unsafe_zero_spec (ms : List Ixon.MutConst) :
    ∀ {h h' : Heap F} {x_ms : SourceValue F} {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Ixon::MutConst>» RepMutConst h ms x_ms →
      ObsFn Obs.W "KernelClaim::muts_unsafe" [x_ms] h (.field 0) h' calls →
      h' = h ∧ ∀ m ∈ ms, IxVM.Consistency.InLogicMut m := by
  induction ms with
  | nil =>
    intro h h' x_ms calls rep ev
    rcases Obs.«KernelClaim::muts_unsafe».obs ev with
      ⟨ld12, _, rfl, -⟩ | ⟨_, _, _, _, _, ld12, -⟩ | ⟨_, _, _, _, _, ld12, -⟩
    · exact ⟨rfl, by simp⟩
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12; cases hbad
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12; cases hbad
  | cons mc rest ih =>
    intro h h' x_ms calls rep ev
    rcases Obs.«KernelClaim::muts_unsafe».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_m, x_rest, m322, cs324, cs347, ld12, sg329, ev349, -⟩ |
      ⟨_, _, _, _, _, _, _, _, he363, -⟩
    · cases Lib.rep_nil_of_load rep ld12
    · obtain ⟨mc', rest', heq, hmc, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with he1 he2
      subst he1 he2
      have hseg : m322 = h ∧ IxVM.Consistency.InLogicMut mc := by
        rcases sg329 with
          ⟨x_kind, x_safety, _, _, _, _, cs114, hv54, ev116, -⟩ |
          ⟨_, _, _, _, x_ctors, cs214, _, hv140, ev216, -⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he230, -⟩ |
          ⟨_, x_is_unsafe, _, _, _, _, _, _, _, _, _, hv239, he316, rfl, -⟩
        · cases mc with
          | indc _ => obtain ⟨_, hv, _⟩ := hmc; rw [hv54] at hv; simp at hv
          | recr _ => obtain ⟨_, hv, _⟩ := hmc; rw [hv54] at hv; simp at hv
          | defn d =>
            obtain ⟨dv, hv, kVal, sVal, _, _, _, hdv, hk, hs, _, _, _⟩ := hmc
            rw [hdv, hv54] at hv
            injection hv with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hdargs
            simp only [List.cons.injEq] at hdargs
            rw [← hdargs.1] at hk
            rw [← hdargs.2.1] at hs
            obtain ⟨hh, hdecl⟩ := defn_is_unsafe_ci_zero_spec hk hs ev116
            exact ⟨hh, hdecl⟩
        · cases mc with
          | defn _ => obtain ⟨_, hv, _⟩ := hmc; rw [hv140] at hv; simp at hv
          | recr _ => obtain ⟨_, hv, _⟩ := hmc; rw [hv140] at hv; simp at hv
          | indc ind =>
            obtain ⟨iv, hv, uVal, _, ctorsPtr, hiv, hu, _, hctors⟩ := hmc
            rw [hiv, hv140] at hv
            injection hv with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hiargs
            simp only [List.cons.injEq, and_true] at hiargs
            have hu0 : uVal = .field 0 := hiargs.1.symm
            rw [← hiargs.2.2.2.2.2] at hctors
            have hfalse : ind.isUnsafe = false := repBool_eq_false_of_field_zero hu hu0
            obtain ⟨hh, hct_ok⟩ := ctors_unsafe_zero_spec ind.ctors.toList hctors ev216
            exact ⟨hh, hfalse, hct_ok⟩
        · simp at he230
        · cases mc with
          | defn _ => obtain ⟨_, hv, _⟩ := hmc; rw [hv239] at hv; simp at hv
          | indc _ => obtain ⟨_, hv, _⟩ := hmc; rw [hv239] at hv; simp at hv
          | recr rc =>
            obtain ⟨rv, hv, _, uVal, _, _, hrv, _, hu, _, _⟩ := hmc
            rw [hrv, hv239] at hv
            injection hv with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hrargs
            simp only [List.cons.injEq] at hrargs
            have hu0 : uVal = .field 0 := hrargs.2.1.symm.trans he316.symm
            have hfalse : rc.isUnsafe = false := repBool_eq_false_of_field_zero hu hu0
            exact ⟨rfl, hfalse⟩
      obtain ⟨rfl, hmc_ok⟩ := hseg
      obtain ⟨hh, hrest_ok⟩ := ih hrest ev349
      refine ⟨hh, fun m hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hmem
      · exact hmc_ok
      · exact hrest_ok m hmem
    · simp at he363

theorem record_unsafe_zero_spec {x_addr : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (ha : S0.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::record_unsafe" [x_addr] h (.field 0) h' calls) :
    Heap.Extends h h' ∧
    ∃ rawBytes c,
      Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = addr ∧
      Ixon.deConstant rawBytes = .ok c ∧
      IxVM.Consistency.InLogic c := by
  rcases Obs.«KernelClaim::record_unsafe».obs ev with
    ⟨m2, cs12, _, _, _, _, x_kind, x_safety, _, _, _, _, cs142, ev14, ev144, hc161⟩ |
    ⟨m2, cs12, _, _, _, _, _, x_is_unsafe, _, _, _, _, _, _, _, ev14, he245, rfl, hc247⟩ |
    ⟨m2, cs12, _, _, _, _, x_is_unsafe, _, _, ev14, he295, rfl, hc297⟩ |
    ⟨m2, cs12, _, _, _, _, x_members, cs314, ev14, ev316, hc325⟩ |
    ⟨m2, cs12, x_info, _, _, _, _, ev14, hne163, hne249, hne299, hne326, _, rfl, hc332⟩
  · obtain ⟨ext1, rawBytes, c, _, hh, hblk, hde, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case defn d =>
      obtain ⟨dv, hdv_eq, kVal, sVal, _, _, _, hdv, hk, hs, _, _, _⟩ := hinfo
      rw [hdv] at hdv_eq
      injection hdv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hdargs
      simp only [List.cons.injEq] at hdargs
      rw [← hdargs.1] at hk
      rw [← hdargs.2.1] at hs
      obtain ⟨rfl, hdecl⟩ := defn_is_unsafe_ci_zero_spec hk hs ev144
      refine ⟨ext1, rawBytes, c, hashed_mono (fun cl hcl => by rw [hc161]; simp [hcl]) hh,
        hblk, hde, ?_⟩
      simpa only [IxVM.Consistency.InLogic, Ix.Kernel.Reader.safetyDecline, hc] using hdecl
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, rawBytes, c, _, hh, hblk, hde, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case recr rc =>
      obtain ⟨rv, hrv_eq, _, uVal, _, _, hrv, _, hu, _, _⟩ := hinfo
      rw [hrv] at hrv_eq
      injection hrv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hrargs
      simp only [List.cons.injEq] at hrargs
      have hu0 : uVal = .field 0 := hrargs.2.1.symm.trans he245.symm
      have hfalse : rc.isUnsafe = false := repBool_eq_false_of_field_zero hu hu0
      refine ⟨ext1, rawBytes, c, hashed_mono (fun cl hcl => by rw [hc247]; simp [hcl]) hh,
        hblk, hde, ?_⟩
      simpa only [IxVM.Consistency.InLogic, hc] using hfalse
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, rawBytes, c, _, hh, hblk, hde, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case axio a =>
      obtain ⟨av, hav_eq, uVal, _, hav, hu, _⟩ := hinfo
      rw [hav] at hav_eq
      injection hav_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ haargs
      simp only [List.cons.injEq] at haargs
      have hu0 : uVal = .field 0 := haargs.1.symm.trans he295.symm
      have hfalse : a.isUnsafe = false := repBool_eq_false_of_field_zero hu hu0
      refine ⟨ext1, rawBytes, c, hashed_mono (fun cl hcl => by rw [hc297]; simp [hcl]) hh,
        hblk, hde, ?_⟩
      simpa only [IxVM.Consistency.InLogic, hc] using hfalse
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, rawBytes, c, _, hh, hblk, hde, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case muts ms =>
      obtain ⟨mv, hmv_eq, hms⟩ := hinfo
      injection hmv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      rw [← h1] at hms
      obtain ⟨rfl, hms_ok⟩ := muts_unsafe_zero_spec ms.toList hms ev316
      refine ⟨ext1, rawBytes, c, hashed_mono (fun cl hcl => by rw [hc325]; simp [hcl]) hh,
        hblk, hde, ?_⟩
      simpa only [IxVM.Consistency.InLogic, hc] using hms_ok
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, rawBytes, c, _, hh, hblk, hde, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc : c.info <;> rw [hc] at hinfo
    case defn _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne163 [_] rfl)
    case recr _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne249 [_] rfl)
    case axio _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne299 [_] rfl)
    case muts _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne326 [_] rfl)
    all_goals
      exact ⟨ext1, rawBytes, c, hashed_mono (fun cl hcl => by rw [hc332]; simp [hcl]) hh,
        hblk, hde, by simp [IxVM.Consistency.InLogic, hc]⟩

theorem assert_claimable_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ha : S0.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::assert_claimable" [x_rc, x_addr] h r h' calls) :
    Heap.Extends h h' ∧ ClaimableSeed calls t addr := by
  rcases Obs.«KernelClaim::assert_claimable».obs ev with
    ⟨m2, cs12, _, _, _, _, _, x_b, v136, m139, cs147, v176, m179, cs187, v216, m219, cs227,
      ev14, ev149, rfl, ev189, rfl, ev229, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, _, _, _, _, _, x_b, v310, m313, cs321, v350, m353, cs361, v390, m393, cs401,
      ev14, ev323, rfl, ev363, rfl, ev403, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, _, _, _, _, _, _, x_b, v490, m493, cs501, v530, m533, cs541, v570, m573, cs581,
      ev14, ev503, rfl, ev543, rfl, ev583, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, _, _, _, _, _, x_b, v664, m667, cs675, v704, m707, cs715, v744, m747, cs755,
      ev14, ev677, rfl, ev717, rfl, ev757, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, x_info, _, _, _, _, v803, m806, cs814, v843, m846, cs854, v883, m886, cs894,
      ev14, hne259, hne433, hne613, hne787, ev816, rfl, ev856, rfl, ev896, rfl, _, rfl, hc⟩
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case dPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev149
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev189
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev229
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case iPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev323
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev363
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev403
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case cPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev503
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev543
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev583
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case rPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev677
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev717
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev757
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    have hown_self : Ix.Cert.ownerOf addr c₀ = addr := by
      cases hc_info : c₀.info <;> rw [hc_info] at hinfo
      case dPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne259 [_] rfl)
      case iPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne433 [_] rfl)
      case cPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne613 [_] rfl)
      case rPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne787 [_] rfl)
      all_goals simp [Ix.Cert.ownerOf, hc_info]
    obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
      record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev816
    have ext3 := ev856.heap_extends
    obtain ⟨rfl, hn_inert⟩ :=
      role_is_inert_zero_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
        (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev896
    exact ⟨ext1.trans (ext2.trans ext3), hn_inert,
      ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
      ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀, .inl hown_self⟩⟩

/-! ## `run_check`, `run_check_transitive`, and `walk_refs_transitive` -/

theorem run_check_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ha : S0.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::run_check" [x_rc, x_addr] h r h' calls) :
    Heap.Extends h h' ∧ S0.CheckedAt calls t addr := by
  obtain ⟨v1, m2, p9, cs15, cs29, ev17, _, ev31, hc56⟩ := Obs.«KernelClaim::run_check».obs ev
  have ext1 := ev17.heap_extends
  have ext2 := ev31.heap_extends
  refine ⟨ext1.trans ext2, ⟨"KernelCheck::check_const", [x_rc, v1, x_addr], m2⟩,
    by rw [hc56]; simp, rfl, x_rc, v1, x_addr, some lim, rfl,
    (hrc.mono ext1).toRCRep, S0.addr_mono ext1 ha⟩

private theorem refs_size_lt_bound {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private theorem run_check_transitive_fuel_aux {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} :
    ∀ (fuel : Nat),
      (∀ {lim : Nat} {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         RCFullRep t bAddr lim h x_rc →
         S0.addr h x_addr addr →
         ObsFn Obs.W "KernelClaim::run_check_transitive" [x_rc, x_addr] h r h' calls →
         Heap.Extends h h' ∧
         ∃ recs : List (WalkedRec calls t),
           addr ∈ recs.map (·.addr) ∧ RecsClosed recs) ∧
      (∀ {lim i : Nat} {refs : List _root_.Address} {idxs : List Nat}
         {x_rc x_refs x_consts r : SourceValue F}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         i + refs.length < 8589934592 →
         RCFullRep t bAddr lim h x_rc →
         RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs x_refs →
         RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h idxs x_consts →
         ObsFn Obs.W "KernelClaim::walk_refs_transitive"
           [x_rc, x_refs, x_consts, .field (i : F)] h r h' calls →
         Heap.Extends h h' ∧
         ∃ recs : List (WalkedRec calls t),
           (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs → refs[j] ∈ recs.map (·.addr)) ∧
           RecsClosed recs) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    refine ⟨?_, ?_⟩
    · intro lim x_rc x_addr r addr h h' calls hfuel hrc ha ev
      obtain ⟨m2, cs12, x_info, w39, x_refs, w40, w41, v539, m540, cs542, cs551, v556, m573, cs581,
        ev14, sg547, ev583, ev553, hc598⟩ := Obs.«KernelClaim::run_check_transitive».obs ev
      obtain ⟨ext1, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        load_verified_constant_de ha ev14
      have hseg : Heap.Extends m2 m540 ∧
          ((∃ ms, c.info = .muts ms) ∨ S0.CheckedAt calls t addr) ∧
          ∃ recs_blk : List (WalkedRec calls t),
            RecsClosed recs_blk ∧
            (Ix.Cert.ownerOf addr c ≠ addr → Ix.Cert.ownerOf addr c ∈ recs_blk.map (·.addr)) := by
        obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.1] at hinfo
        rcases sg547 with
          ⟨x_members, cs91, hv81, ev93, hc133⟩ |
          ⟨_, x_block_addr, v173, m174, cs184, cs206, _, hv139, ev186, ev208, hc225⟩ |
          ⟨_, x_block_addr, v266, m267, cs277, cs299, _, _, hv232, ev279, ev301, hc318⟩ |
          ⟨_, _, x_block_addr, v365, m366, cs376, cs398, _, _, _, hv325, ev378, ev400, hc417⟩ |
          ⟨_, x_block_addr, v458, m459, cs469, cs491, _, _, _, _, hv424, ev471, ev493, hc510⟩ |
          ⟨cs519, hne134, hne227, hne320, hne419, hne512, ev521, hc538⟩
        · rw [hv81] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case muts ms =>
            exact ⟨ev93.heap_extends, .inl ⟨ms, rfl⟩, [], by simp [RecsClosed],
              fun hne => absurd (by simp [Ix.Cert.ownerOf, hc_i]) hne⟩
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv139] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case dPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev186
            have hlt_sub : cs206.length < fuel := by
              rw [hc598, hc225] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b⟩ :=
              (ih cs206.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev208
            have hsub_b : ∀ cl ∈ cs206, cl ∈ calls := fun cl hcl => by
              rw [hc598, hc225]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc598, hc225]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv232] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case iPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev279
            have hlt_sub : cs299.length < fuel := by
              rw [hc598, hc318] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b⟩ :=
              (ih cs299.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev301
            have hsub_b : ∀ cl ∈ cs299, cl ∈ calls := fun cl hcl => by
              rw [hc598, hc318]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc598, hc318]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv325] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case cPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev378
            have hlt_sub : cs398.length < fuel := by
              rw [hc598, hc417] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b⟩ :=
              (ih cs398.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev400
            have hsub_b : ∀ cl ∈ cs398, cl ∈ calls := fun cl hcl => by
              rw [hc598, hc417]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc598, hc417]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv424] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case rPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev471
            have hlt_sub : cs491.length < fuel := by
              rw [hc598, hc510] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b⟩ :=
              (ih cs491.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev493
            have hsub_b : ∀ cl ∈ cs491, cl ∈ calls := fun cl hcl => by
              rw [hc598, hc510]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc598, hc510]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev521
          have hown_self : Ix.Cert.ownerOf addr c = addr := by
            cases hc_i : c.info <;> rw [hc_i] at hinfo
            case muts _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne134 [_] rfl)
            case dPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne227 [_] rfl)
            case iPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne320 [_] rfl)
            case cPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne419 [_] rfl)
            case rPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne512 [_] rfl)
            all_goals simp [Ix.Cert.ownerOf, hc_i]
          exact ⟨ext_rc,
            .inr (checkedAt_mono (fun cl hcl => by rw [hc598, hc538]; simp [hcl]) hchk),
            [], by simp [RecsClosed], fun hne => absurd hown_self hne⟩
      obtain ⟨ext_seg, hchk_self, recs_blk, hcl_blk, hown_blk⟩ := hseg
      obtain ⟨ext_idx, hidxs⟩ := const_idxs_of_spec (hrep.mono ext_seg) ev583
      have hrefs_rep :
          RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem m573 c.refs.toList x_refs := by
        obtain ⟨_, _, refsPtr, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.2.2.1] at hr_list
        exact repList_heapMono₂ _ repAddrElem_heapMono₂ (ext_seg.trans ext_idx) hr_list
      have hlt_walk : cs551.length < fuel := by
        rw [hc598] at hfuel
        simp only [List.length_cons, List.length_append] at hfuel
        omega
      have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
        rw [Nat.zero_add, Array.length_toList]
        exact refs_size_lt_bound hsz hdeExact
      obtain ⟨ext_walk, recs_r, hmem_r, hcl_r⟩ :=
        (ih cs551.length hlt_walk).2 (i := 0) (Nat.le_refl _) hrefs_bound
          (hrc.mono (ext1.trans (ext_seg.trans ext_idx))) hrefs_rep hidxs ev553
      have hsub_r : ∀ cl ∈ cs551, cl ∈ calls := fun cl hcl => by
        rw [hc598]; simp [hcl]
      let r₀ : WalkedRec calls t := {
        addr := addr
        rawBytes := rawBytes
        c := c
        hsz := hsz
        hhashed := hashed_mono (fun cl hcl => by rw [hc598]; simp [hcl]) hh_load
        hblake := hblk
        hde := hde
        hdeExact := hdeExact
        hchecked := hchk_self
      }
      let recs_tail := recs_blk ++ recs_r.map (WalkedRec.mono hsub_r)
      refine ⟨ext1.trans (ext_seg.trans (ext_idx.trans ext_walk)),
        r₀ :: recs_tail, List.mem_cons_self,
        RecsClosed.cons (hcl_blk.append (hcl_r.mono hsub_r)) ?_ ?_⟩
      · intro hne
        exact List.mem_cons_of_mem _ (by
          rw [List.map_append]
          exact List.mem_append_left _ (hown_blk hne))
      · intro j hj b hb
        have hj_lt : j < c.refs.toList.length := by
          rw [Array.length_toList]
          exact (Array.getElem?_eq_some_iff.mp hb).1
        have hget : c.refs.toList[j] = b := by
          obtain ⟨_, heq_b⟩ := Array.getElem?_eq_some_iff.mp hb
          simpa using heq_b
        have hm := hmem_r j hj_lt (by simpa using hj)
        rw [hget] at hm
        exact List.mem_cons_of_mem _ (by
          rw [List.map_append, map_addr_walkedRec_mono]
          exact List.mem_append_right _ hm)
    · intro lim i refs idxs x_rc x_refs x_consts r h h' calls hfuel hbound hrc hrefs hidxs ev
      rcases Obs.«KernelClaim::walk_refs_transitive».obs ev with
        ⟨ld12, _, rfl, -⟩ |
        ⟨x_a, x_rest, v204, m205, cs207, cs216, v222, ld12, sg212, op257, ev218, hc259⟩
      · obtain rfl := Lib.rep_nil_of_load hrefs ld12
        exact ⟨Heap.Extends.refl _, [], fun _ hj => absurd hj (Nat.not_lt_zero _),
          by simp [RecsClosed]⟩
      · obtain ⟨a, rest, rfl, ha_head, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
        have hi_lt56 : i < 72057594037927936 := by simp at hbound; omega
        have hseg : Heap.Extends h m205 ∧
            ∃ recs₁ : List (WalkedRec calls t),
              (i ∈ idxs → a ∈ recs₁.map (·.addr)) ∧ RecsClosed recs₁ := by
          rcases sg212 with
            ⟨m43, cs54, v77, m78, cs88, m108, cs119, cs145, v148, m151, cs159,
              ev56, ev90, ev121, ev161, ev147, hc185⟩ |
            ⟨m43, cs54, v77, m78, cs88, v107, m108, cs119, ev56, ev90, ev121, hne186, -⟩ |
            ⟨v42, m43, cs54, ev56, hne195, _, rfl, -⟩
          · obtain ⟨rfl, _⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            have ext_ra := ev90.heap_extends
            obtain ⟨_, rfl⟩ := walk_covered_spec (hrc.mono ext_ra) ev121
            obtain ⟨ext_wc, lim', hrc'⟩ := walk_ctx_spec (hrc.mono ext_ra) ev161
            have hlt_sub : cs145.length < fuel := by
              rw [hc259, hc185] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            obtain ⟨ext_sub, recs_s, hmem_s, hcl_s⟩ :=
              (ih cs145.length hlt_sub).1 (Nat.le_refl _) hrc'
                (S0.addr_mono (ext_ra.trans ext_wc) ha_head) ev147
            have hsub_s : ∀ cl ∈ cs145, cl ∈ calls := fun cl hcl => by
              rw [hc259, hc185]; simp [hcl]
            refine ⟨ext_ra.trans (ext_wc.trans ext_sub),
              recs_s.map (WalkedRec.mono hsub_s), ?_, hcl_s.mono hsub_s⟩
            intro _
            rw [map_addr_walkedRec_mono]
            exact hmem_s
          · obtain ⟨rfl, _⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            have ext_ra := ev90.heap_extends
            obtain ⟨hv107, _⟩ := walk_covered_spec (hrc.mono ext_ra) ev121
            exact absurd hv107 hne186
          · obtain ⟨rfl, hiff⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            exact ⟨Heap.Extends.refl _, [], fun hi_in => absurd (hiff.mpr hi_in) hne195,
              by simp [RecsClosed]⟩
        obtain ⟨ext1, recs₁, hmem₁, hcl₁⟩ := hseg
        simp only [evalBinOp, Except.ok.injEq] at op257
        subst op257
        have hv_inc : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
        rw [hv_inc] at ev218
        have hlt_tail : cs216.length < fuel := by
          rw [hc259] at hfuel
          simp only [List.length_cons, List.length_append] at hfuel
          omega
        have hbound_tail : (i + 1) + rest.length < 8589934592 := by
          simp at hbound; omega
        obtain ⟨ext2, recs₂_raw, hmem₂, hcl₂⟩ :=
          (ih cs216.length hlt_tail).2 (i := i + 1) (Nat.le_refl _) hbound_tail
            (hrc.mono ext1)
            (repList_heapMono₂ _ repAddrElem_heapMono₂ ext1 hrest_rep)
            (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext1 hidxs)
            ev218
        have hsub₂ : ∀ cl ∈ cs216, cl ∈ calls := fun cl hcl => by
          rw [hc259]; simp [hcl]
        refine ⟨ext1.trans ext2, recs₁ ++ recs₂_raw.map (WalkedRec.mono hsub₂), ?_,
          hcl₁.append (hcl₂.mono hsub₂)⟩
        intro j hj hij
        rw [List.map_append, map_addr_walkedRec_mono]
        cases j with
        | zero =>
          simp only [Nat.add_zero] at hij
          exact List.mem_append_left _ (hmem₁ hij)
        | succ j' =>
          have hj' : j' < rest.length := by simp at hj; omega
          have hij' : (i + 1) + j' ∈ idxs := by
            have heq_idx : (i + 1) + j' = i + (j' + 1) := by omega
            rwa [heq_idx]
          exact List.mem_append_right _ (hmem₂ j' hj' hij')

theorem run_check_transitive_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (ha : S0.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::run_check_transitive" [x_rc, x_addr] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ recs : List (WalkedRec calls t),
      addr ∈ recs.map (·.addr) ∧ RecsClosed recs :=
  (run_check_transitive_fuel_aux calls.length).1 (Nat.le_refl _) hrc ha ev

/-! ## `check_owned`, `env_walk_all`, `env_walk_refs_all`, and `walk_leaves_owned` -/

private theorem addrVal_of_load {h : Heap F} {p v : SourceValue F} {a : _root_.Address}
    (ha : S0.addr h p a) (hl : loadValue h p = .ok v) :
    ∃ d : Bytes.Address, v = L1.digestV d ∧ ixAddr d = a := by
  obtain ⟨d, hd, hix⟩ := ha
  exact ⟨d, L1.load_repAddressRef hd hl, hix⟩

private theorem addr_of_snoc {h : Heap F} {d : Bytes.Address} {a : _root_.Address}
    (hix : ixAddr d = a) :
    S0.addr (h ++ [L1.digestV d]) (.ptr (L1.digestV d).type h.length) a :=
  ⟨d, repAddressRef_of_load_digestV (L1.loadValue_snoc h (L1.digestV d)), hix⟩

private theorem env_walk_fuel_aux {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) :
    ∀ (fuel : Nat),
      (∀ {d_b d_a : Bytes.Address} {addr : _root_.Address}
         {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         ixAddr d_b = b.address →
         ixAddr d_a = addr →
         ObsFn Obs.W "IxVMCompat::check_owned"
           [L1.digestV d_b, .field 3, L1.digestV d_a] h r h' calls →
         V.HashedCollision extra calls ∨
         (Heap.Extends h h' ∧
          ClaimableSeed calls t addr ∧
          ∃ recs : List (WalkedRec calls t),
            addr ∈ recs.map (·.addr) ∧ RecsClosed recs)) ∧
      (∀ {lim : Nat} {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         RCFullRep t b.address lim h x_rc →
         S0.addr h x_addr addr →
         ObsFn Obs.W "KernelClaim::env_walk_all" [x_rc, x_addr] h r h' calls →
         V.HashedCollision extra calls ∨
         (Heap.Extends h h' ∧
          ∃ recs : List (WalkedRec calls t),
            addr ∈ recs.map (·.addr) ∧ RecsClosed recs)) ∧
      (∀ {lim i : Nat} {refs : List _root_.Address} {idxs : List Nat}
         {x_rc x_refs x_consts r : SourceValue F}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         i + refs.length < 8589934592 →
         RCFullRep t b.address lim h x_rc →
         RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs x_refs →
         RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h idxs x_consts →
         ObsFn Obs.W "KernelClaim::env_walk_refs_all"
           [x_rc, x_refs, x_consts, .field (i : F)] h r h' calls →
         V.HashedCollision extra calls ∨
         (Heap.Extends h h' ∧
          ∃ recs : List (WalkedRec calls t),
            (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs → refs[j] ∈ recs.map (·.addr)) ∧
            RecsClosed recs)) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro d_b d_a addr r h h' calls hfuel hix_b hix_a ev
      obtain ⟨v1, m2, cs12, m18, v35, m36, cs46, m59, cs72, m85,
        rfl, ev14, rfl, ev48, rfl, ev74, hc95⟩ := Obs.«IxVMCompat::check_owned».obs ev
      have ext_s1 := Heap.Extends.snoc h (L1.digestV d_b)
      rcases role_ctx_for_validator_spec (V := V) hadm hb_extra (addr_of_snoc hix_b) ev14 with
        hcoll | ⟨ext_rc, hrc⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc95]; simp [hcl]) hcoll)
      have ext_s2 := Heap.Extends.snoc m2 (L1.digestV d_a)
      obtain ⟨ext_ac, hseed⟩ :=
        assert_claimable_spec (hrc.mono ext_s2) (addr_of_snoc hix_a) ev48
      have ext_s3 := Heap.Extends.snoc m36 (L1.digestV d_a)
      have hlt_ewa : cs72.length < fuel := by
        rw [hc95] at hfuel
        simp only [List.length_cons, List.length_append] at hfuel
        omega
      rcases (ih cs72.length hlt_ewa).2.1 (Nat.le_refl _)
          (hrc.mono (ext_s2.trans (ext_ac.trans ext_s3))) (addr_of_snoc hix_a) ev74 with
        hcoll | ⟨ext_ewa, recs, hmem, hcl⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc95]; simp [hcl]) hcoll)
      have hsub_ac : ∀ cl ∈ cs46, cl ∈ calls := fun cl hcl => by rw [hc95]; simp [hcl]
      have hsub_ewa : ∀ cl ∈ cs72, cl ∈ calls := fun cl hcl => by rw [hc95]; simp [hcl]
      refine .inr ⟨ext_s1.trans (ext_rc.trans (ext_s2.trans (ext_ac.trans (ext_s3.trans ext_ewa)))),
        hseed.mono hsub_ac, recs.map (WalkedRec.mono hsub_ewa), ?_, hcl.mono hsub_ewa⟩
      rw [map_addr_walkedRec_mono]
      exact hmem
    · intro lim x_rc x_addr r addr h h' calls hfuel hrc ha ev
      obtain ⟨m2, cs12, x_info, w39, x_refs, w40, w41, v699, m700, cs702, cs711, v716, m733, cs741,
        ev14, sg707, ev743, ev713, hc758⟩ := Obs.«KernelClaim::env_walk_all».obs ev
      obtain ⟨ext1, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        load_verified_constant_de ha ev14
      have hseg : V.HashedCollision extra calls ∨
          (Heap.Extends m2 m700 ∧
           ((∃ ms, c.info = .muts ms) ∨ S0.CheckedAt calls t addr) ∧
           ∃ recs_blk : List (WalkedRec calls t),
             RecsClosed recs_blk ∧
             (Ix.Cert.ownerOf addr c ≠ addr → Ix.Cert.ownerOf addr c ∈ recs_blk.map (·.addr))) := by
        obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.1] at hinfo
        rcases sg707 with
          ⟨x_members, cs91, hv81, ev93, hc133⟩ |
          ⟨_, x_block_addr, v173, m174, cs184, cs206, v209, v210, v211, m213, p218, cs224,
            m236, cs244, _, hv139, ev186, ev226, ld220, ev246, ld263, ev208, hc265⟩ |
          ⟨_, x_block_addr, v306, m307, cs317, cs339, v342, v343, v344, m346, p351, cs357,
            m369, cs377, _, _, hv272, ev319, ev359, ld353, ev379, ld396, ev341, hc398⟩ |
          ⟨_, _, x_block_addr, v445, m446, cs456, cs478, v481, v482, v483, m485, p490, cs496,
            m508, cs516, _, _, _, hv405, ev458, ev498, ld492, ev518, ld535, ev480, hc537⟩ |
          ⟨_, x_block_addr, v578, m579, cs589, cs611, v614, v615, v616, m618, p623, cs629,
            m641, cs649, _, _, _, _, hv544, ev591, ev631, ld625, ev651, ld668, ev613, hc670⟩ |
          ⟨cs679, hne134, hne267, hne400, hne539, hne672, ev681, hc698⟩
        · rw [hv81] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case muts ms =>
            exact .inr ⟨ev93.heap_extends, .inl ⟨ms, rfl⟩, [], by simp [RecsClosed],
              fun hne => absurd (by simp [Ix.Cert.ownerOf, hc_i]) hne⟩
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv139] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case dPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev186
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_spec (hrc.mono (ext1.trans ext_rc)) ev226
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load hp_b ld220
            obtain ⟨rfl, rfl⟩ := role_ctx_validator_spec (hrc.mono (ext1.trans ext_rc)) ev246
            obtain ⟨d_blk, rfl, hix_blk⟩ := addrVal_of_load (S0.addr_mono ext_rc hblk_addr) ld263
            have hlt_sub : cs206.length < fuel := by
              rw [hc758, hc265] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            rcases (ih cs206.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk ev208 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc758, hc265]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs206, cl ∈ calls := fun cl hcl => by
              rw [hc758, hc265]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc758, hc265]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv272] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case iPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev319
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_spec (hrc.mono (ext1.trans ext_rc)) ev359
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load hp_b ld353
            obtain ⟨rfl, rfl⟩ := role_ctx_validator_spec (hrc.mono (ext1.trans ext_rc)) ev379
            obtain ⟨d_blk, rfl, hix_blk⟩ := addrVal_of_load (S0.addr_mono ext_rc hblk_addr) ld396
            have hlt_sub : cs339.length < fuel := by
              rw [hc758, hc398] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            rcases (ih cs339.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk ev341 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc758, hc398]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs339, cl ∈ calls := fun cl hcl => by
              rw [hc758, hc398]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc758, hc398]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv405] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case cPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev458
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_spec (hrc.mono (ext1.trans ext_rc)) ev498
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load hp_b ld492
            obtain ⟨rfl, rfl⟩ := role_ctx_validator_spec (hrc.mono (ext1.trans ext_rc)) ev518
            obtain ⟨d_blk, rfl, hix_blk⟩ := addrVal_of_load (S0.addr_mono ext_rc hblk_addr) ld535
            have hlt_sub : cs478.length < fuel := by
              rw [hc758, hc537] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            rcases (ih cs478.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk ev480 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc758, hc537]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs478, cl ∈ calls := fun cl hcl => by
              rw [hc758, hc537]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc758, hc537]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv544] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case rPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev591
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_spec (hrc.mono (ext1.trans ext_rc)) ev631
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load hp_b ld625
            obtain ⟨rfl, rfl⟩ := role_ctx_validator_spec (hrc.mono (ext1.trans ext_rc)) ev651
            obtain ⟨d_blk, rfl, hix_blk⟩ := addrVal_of_load (S0.addr_mono ext_rc hblk_addr) ld668
            have hlt_sub : cs611.length < fuel := by
              rw [hc758, hc670] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            rcases (ih cs611.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk ev613 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc758, hc670]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs611, cl ∈ calls := fun cl hcl => by
              rw [hc758, hc670]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (checkedAt_mono (fun cl hcl => by rw [hc758, hc670]; simp [hcl]) hchk),
              recs_b.map (WalkedRec.mono hsub_b), hcl_b.mono hsub_b, ?_⟩
            intro _
            rw [map_addr_walkedRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · obtain ⟨ext_rc, hchk⟩ := run_check_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev681
          have hown_self : Ix.Cert.ownerOf addr c = addr := by
            cases hc_i : c.info <;> rw [hc_i] at hinfo
            case muts _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne134 [_] rfl)
            case dPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne267 [_] rfl)
            case iPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne400 [_] rfl)
            case cPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne539 [_] rfl)
            case rPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne672 [_] rfl)
            all_goals simp [Ix.Cert.ownerOf, hc_i]
          exact .inr ⟨ext_rc,
            .inr (checkedAt_mono (fun cl hcl => by rw [hc758, hc698]; simp [hcl]) hchk),
            [], by simp [RecsClosed], fun hne => absurd hown_self hne⟩
      rcases hseg with hcoll | ⟨ext_seg, hchk_self, recs_blk, hcl_blk, hown_blk⟩
      · exact .inl hcoll
      obtain ⟨ext_idx, hidxs⟩ := const_idxs_of_spec (hrep.mono ext_seg) ev743
      have hrefs_rep :
          RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem m733 c.refs.toList x_refs := by
        obtain ⟨_, _, refsPtr, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.2.2.1] at hr_list
        exact repList_heapMono₂ _ repAddrElem_heapMono₂ (ext_seg.trans ext_idx) hr_list
      have hlt_walk : cs711.length < fuel := by
        rw [hc758] at hfuel
        simp only [List.length_cons, List.length_append] at hfuel
        omega
      have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
        rw [Nat.zero_add, Array.length_toList]
        exact refs_size_lt_bound hsz hdeExact
      rcases (ih cs711.length hlt_walk).2.2 (i := 0) (Nat.le_refl _) hrefs_bound
          (hrc.mono (ext1.trans (ext_seg.trans ext_idx))) hrefs_rep hidxs ev713 with
        hcoll | ⟨ext_walk, recs_r, hmem_r, hcl_r⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc758]; simp [hcl]) hcoll)
      have hsub_r : ∀ cl ∈ cs711, cl ∈ calls := fun cl hcl => by
        rw [hc758]; simp [hcl]
      let r₀ : WalkedRec calls t := {
        addr := addr
        rawBytes := rawBytes
        c := c
        hsz := hsz
        hhashed := hashed_mono (fun cl hcl => by rw [hc758]; simp [hcl]) hh_load
        hblake := hblk
        hde := hde
        hdeExact := hdeExact
        hchecked := hchk_self
      }
      let recs_tail := recs_blk ++ recs_r.map (WalkedRec.mono hsub_r)
      refine .inr ⟨ext1.trans (ext_seg.trans (ext_idx.trans ext_walk)),
        r₀ :: recs_tail, List.mem_cons_self,
        RecsClosed.cons (hcl_blk.append (hcl_r.mono hsub_r)) ?_ ?_⟩
      · intro hne
        exact List.mem_cons_of_mem _ (by
          rw [List.map_append]
          exact List.mem_append_left _ (hown_blk hne))
      · intro j hj b_ref hb
        have hj_lt : j < c.refs.toList.length := by
          rw [Array.length_toList]
          exact (Array.getElem?_eq_some_iff.mp hb).1
        have hget : c.refs.toList[j] = b_ref := by
          obtain ⟨_, heq_b⟩ := Array.getElem?_eq_some_iff.mp hb
          simpa using heq_b
        have hm := hmem_r j hj_lt (by simpa using hj)
        rw [hget] at hm
        exact List.mem_cons_of_mem _ (by
          rw [List.map_append, map_addr_walkedRec_mono]
          exact List.mem_append_right _ hm)
    · intro lim i refs idxs x_rc x_refs x_consts r h h' calls hfuel hbound hrc hrefs hidxs ev
      rcases Obs.«KernelClaim::env_walk_refs_all».obs ev with
        ⟨ld12, _, rfl, -⟩ |
        ⟨x_a, x_rest, v329, m330, cs332, cs341, v347, ld12, sg337, op382, ev343, hc384⟩
      · obtain rfl := Lib.rep_nil_of_load hrefs ld12
        exact .inr ⟨Heap.Extends.refl _, [], fun _ hj => absurd hj (Nat.not_lt_zero _),
          by simp [RecsClosed]⟩
      · obtain ⟨a, rest, rfl, ha_head, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
        have hi_lt56 : i < 72057594037927936 := by simp at hbound; omega
        have hseg : V.HashedCollision extra calls ∨
            (Heap.Extends h m330 ∧
             ∃ recs₁ : List (WalkedRec calls t),
               (i ∈ idxs → a ∈ recs₁.map (·.addr)) ∧ RecsClosed recs₁) := by
          rcases sg337 with
            ⟨m43, cs54, v77, m78, cs88, m108, cs119, v142, m143, cs153, m173, x181, y182,
              m183, cs192, cs206, cs224, v227, v228, v229, m231, p236, cs242, m254, cs262,
              ev56, ev90, ev121, ev155, ev194, ev208, op188, ev244, ld238, ev264, ld281,
              ev226, hc283⟩ |
            ⟨m43, cs54, v77, m78, cs88, m108, cs119, v142, m143, cs153, v172, m173, x181, y182,
              m183, cs192, cs206, cs291,
              ev56, ev90, ev121, ev155, ev194, ev208, op188, hne284, ev293, hc310⟩ |
            ⟨m43, cs54, v77, m78, cs88, v107, m108, cs119, ev56, ev90, ev121, hne311, -⟩ |
            ⟨v42, m43, cs54, ev56, hne320, _, rfl, -⟩
          · obtain ⟨rfl, _⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            have ext_ra := ev90.heap_extends
            obtain ⟨_, rfl⟩ := walk_covered_spec (hrc.mono ext_ra) ev121
            obtain ⟨ext_wc, lim', hrc'⟩ := walk_ctx_spec (hrc.mono ext_ra) ev155
            obtain ⟨_, rfl⟩ := role_ctx_limit_spec hrc' ev194
            obtain ⟨_, rfl⟩ := role_ctx_limit_spec (hrc.mono (ext_ra.trans ext_wc)) ev208
            obtain ⟨rfl, hp_b⟩ :=
              role_ctx_binding_spec (hrc.mono (ext_ra.trans ext_wc)) ev244
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load hp_b ld238
            obtain ⟨rfl, rfl⟩ :=
              role_ctx_validator_spec (hrc.mono (ext_ra.trans ext_wc)) ev264
            obtain ⟨d_a, rfl, hix_a⟩ :=
              addrVal_of_load (S0.addr_mono (ext_ra.trans ext_wc) ha_head) ld281
            have hlt_sub : cs224.length < fuel := by
              rw [hc384, hc283] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            rcases (ih cs224.length hlt_sub).1 (Nat.le_refl _) hix_b hix_a ev226 with
              hcoll | ⟨ext_co, _, recs_s, hmem_s, hcl_s⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc384, hc283]; simp [hcl]) hcoll)
            have hsub_s : ∀ cl ∈ cs224, cl ∈ calls := fun cl hcl => by
              rw [hc384, hc283]; simp [hcl]
            refine .inr ⟨ext_ra.trans (ext_wc.trans ext_co),
              recs_s.map (WalkedRec.mono hsub_s), ?_, hcl_s.mono hsub_s⟩
            intro _
            rw [map_addr_walkedRec_mono]
            exact hmem_s
          · obtain ⟨rfl, _⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            have ext_ra := ev90.heap_extends
            obtain ⟨_, rfl⟩ := walk_covered_spec (hrc.mono ext_ra) ev121
            obtain ⟨ext_wc, lim', hrc'⟩ := walk_ctx_spec (hrc.mono ext_ra) ev155
            obtain ⟨_, rfl⟩ := role_ctx_limit_spec hrc' ev194
            obtain ⟨_, rfl⟩ := role_ctx_limit_spec (hrc.mono (ext_ra.trans ext_wc)) ev208
            obtain ⟨ext_sub, recs_s, hmem_s, hcl_s⟩ :=
              run_check_transitive_spec hrc' (S0.addr_mono (ext_ra.trans ext_wc) ha_head) ev293
            have hsub_s : ∀ cl ∈ cs291, cl ∈ calls := fun cl hcl => by
              rw [hc384, hc310]; simp [hcl]
            refine .inr ⟨ext_ra.trans (ext_wc.trans ext_sub),
              recs_s.map (WalkedRec.mono hsub_s), ?_, hcl_s.mono hsub_s⟩
            intro _
            rw [map_addr_walkedRec_mono]
            exact hmem_s
          · obtain ⟨rfl, _⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            have ext_ra := ev90.heap_extends
            obtain ⟨hv107, _⟩ := walk_covered_spec (hrc.mono ext_ra) ev121
            exact absurd hv107 hne311
          · obtain ⟨rfl, hiff⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            exact .inr ⟨Heap.Extends.refl _, [], fun hi_in => absurd (hiff.mpr hi_in) hne320,
              by simp [RecsClosed]⟩
        rcases hseg with hcoll | ⟨ext1, recs₁, hmem₁, hcl₁⟩
        · exact .inl hcoll
        simp only [evalBinOp, Except.ok.injEq] at op382
        subst op382
        have hv_inc : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
        rw [hv_inc] at ev343
        have hlt_tail : cs341.length < fuel := by
          rw [hc384] at hfuel
          simp only [List.length_cons, List.length_append] at hfuel
          omega
        have hbound_tail : (i + 1) + rest.length < 8589934592 := by
          simp at hbound; omega
        rcases (ih cs341.length hlt_tail).2.2 (i := i + 1) (Nat.le_refl _) hbound_tail
            (hrc.mono ext1)
            (repList_heapMono₂ _ repAddrElem_heapMono₂ ext1 hrest_rep)
            (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext1 hidxs)
            ev343 with
          hcoll | ⟨ext2, recs₂_raw, hmem₂, hcl₂⟩
        · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc384]; simp [hcl]) hcoll)
        have hsub₂ : ∀ cl ∈ cs341, cl ∈ calls := fun cl hcl => by
          rw [hc384]; simp [hcl]
        refine .inr ⟨ext1.trans ext2, recs₁ ++ recs₂_raw.map (WalkedRec.mono hsub₂), ?_,
          hcl₁.append (hcl₂.mono hsub₂)⟩
        intro j hj hij
        rw [List.map_append, map_addr_walkedRec_mono]
        cases j with
        | zero =>
          simp only [Nat.add_zero] at hij
          exact List.mem_append_left _ (hmem₁ hij)
        | succ j' =>
          have hj' : j' < rest.length := by simp at hj; omega
          have hij' : (i + 1) + j' ∈ idxs := by
            have heq_idx : (i + 1) + j' = i + (j' + 1) := by omega
            rwa [heq_idx]
          exact List.mem_append_right _ (hmem₂ j' hj' hij')

theorem check_owned_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra)
    {d_b d_a : Bytes.Address} {addr : _root_.Address}
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hix_b : ixAddr d_b = b.address)
    (hix_a : ixAddr d_a = addr)
    (ev : ObsFn Obs.W "IxVMCompat::check_owned"
      [L1.digestV d_b, .field 3, L1.digestV d_a] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧
     ClaimableSeed calls t addr ∧
     ∃ recs : List (WalkedRec calls t),
       addr ∈ recs.map (·.addr) ∧ RecsClosed recs) :=
  (env_walk_fuel_aux hadm hb_extra calls.length).1 (Nat.le_refl _) hix_b hix_a ev

theorem walk_leaves_owned_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra)
    (as : List Bytes.Address) :
    ∀ {lim : Nat} {x_rc x_leaves r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      RCFullRep t b.address lim h x_rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h as x_leaves →
      ObsFn Obs.W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] h r h' calls →
      V.HashedCollision extra calls ∨
      (Heap.Extends h h' ∧
       (∀ a ∈ as.map ixAddr, ClaimableSeed calls t a) ∧
       ∃ recs : List (WalkedRec calls t),
         (∀ a ∈ as.map ixAddr, a ∈ recs.map (·.addr)) ∧ RecsClosed recs) := by
  induction as with
  | nil =>
    intro lim x_rc x_leaves r h h' calls hrc hl ev
    rcases Obs.«KernelClaim::walk_leaves_owned».obs ev with
      ⟨ld12, _, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, -⟩
    · exact .inr ⟨Heap.Extends.refl _, by simp, [], by simp, by simp [RecsClosed]⟩
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hl ld12
      cases hbad
  | cons aB rest ih =>
    intro lim x_rc x_leaves r h h' calls hrc hl ev
    rcases Obs.«KernelClaim::walk_leaves_owned».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_a, x_rest, v42, m43, cs53, v56, v57, v58, m60, p65, cs71, m83, cs91, cs115,
        ld12, ev73, ld67, ev93, ld110, ev55, ev117, hc134⟩
    · cases Lib.rep_nil_of_load hl ld12
    · obtain ⟨aB', rest', heq, ha_ref, hrest⟩ := Lib.rep_cons_of_load hl ld12
      injection heq with he1 he2
      subst he1 he2
      obtain ⟨rfl, hp_b⟩ := role_ctx_binding_spec hrc ev73
      obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load hp_b ld67
      obtain ⟨rfl, rfl⟩ := role_ctx_validator_spec hrc ev93
      have hv58 : v58 = L1.digestV aB := L1.load_repAddressRef ha_ref ld110
      subst hv58
      rcases check_owned_spec (V := V) hadm hb_extra hix_b rfl ev55 with
        hcoll | ⟨ext1, hseed_hd, recs₁, hmem₁, hcl₁⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc134]; simp [hcl]) hcoll)
      rcases ih (hrc.mono ext1)
          (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hrest) ev117 with
        hcoll | ⟨ext2, hseed_tl, recs₂, hmem₂, hcl₂⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc134]; simp [hcl]) hcoll)
      have hsub₁ : ∀ cl ∈ cs53, cl ∈ calls := fun cl hcl => by rw [hc134]; simp [hcl]
      have hsub₂ : ∀ cl ∈ cs115, cl ∈ calls := fun cl hcl => by rw [hc134]; simp [hcl]
      refine .inr ⟨ext1.trans ext2, ?_,
        recs₁.map (WalkedRec.mono hsub₁) ++ recs₂.map (WalkedRec.mono hsub₂),
        ?_, (hcl₁.mono hsub₁).append (hcl₂.mono hsub₂)⟩
      · intro a ha_mem
        rcases List.mem_cons.mp ha_mem with rfl | htl
        · exact hseed_hd.mono hsub₁
        · exact (hseed_tl a htl).mono hsub₂
      · intro a ha_mem
        rw [List.map_append, map_addr_walkedRec_mono, map_addr_walkedRec_mono]
        rcases List.mem_cons.mp ha_mem with rfl | htl
        · exact List.mem_append_left _ hmem₁
        · exact List.mem_append_right _ (hmem₂ a htl)

end IxVM.Refinement.Claim
