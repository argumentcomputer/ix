import Ix.Cert.Aggr.EndToEnd
import IxVMRefinement.Endpoint.ComposedResidual
import IxVMRefinement.Claim.RefSafetyExcept
import IxCK.Kernel.Audit.Axioms

/-! # Conditional-Shard Partition Composition to a Set-Theoretic Model

Unconditionally proves `Ix.Cert.Aggr.CircuitShardedComposed` on the three standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`), generalizing `IxVM.Refinement.Endpoint.circuitComposed`
from a single monolithic `asm = none` typing run to an arbitrary finite topologically ordered DAG
(`Ix.Cert.Aggr.ClosedShardPartition`) of conditional `check` and `checkEnv` shard runs (each
carrying an optional assumption tree `asm : Option Address` discharged by earlier shards in the
partition, with no user axioms, no literal class, and uniform table-validation mode under a
verified `binding spec a` run).

## Proof Architecture

1. **ROM Disjoint-Union Merging (`bounded_of_roms_sum_le`):**
   Given `n` shard trace ROMs whose address counts sum to `≤ 2 ^ 39` (`< Goldilocks.modulus`),
   maps each shard `k`'s ROM addresses into disjoint intervals `[off_k, off_k + len_k)` inside
   `IxVM.F` via `Aiur.Value.mapAddress`, preserving `Aiur.ROM.Valid`, `Aiur.Value.type`, and
   `Aiur.Represents`, yielding a single valid combined ROM of at most `2 ^ 39` addresses carrying
   `shardCalls.flatten` (`IxVM.Consistency.Bounded shardCalls.flatten`).
2. **`FamCallsModeled` Closure (`famCallsModeled_flatten`):**
   Each shard's `IxVM::verify_claim` derivation satisfies `Typing.FamCallsModeled`; flattening
   preserves `Typing.FamCallsModeled` across `shardCalls.flatten`.
3. **Conditional Reference Safety & Walk Export (`RecordRefsUnderIn`, `CondTopRec`, `CondTopRecsClosed`):**
   Refines `KernelClaim::assert_safe_record_refs_under` (using `Claim.assert_safe_used_refs_set_spec`),
   `KernelClaim::assert_leaves_claimable`, `KernelClaim::env_walk`, `KernelClaim::env_walk_refs`,
   `KernelClaim::env_walk_leaves`, `KernelClaim::run_check_env` (`asm = Some r` and `asm = None`),
   and `KernelClaim::run_claim` under `Claim.RCLimRep` at either top-level limit (`some 77` for
   validator `3`, `none` for validator `4`).
4. **Closed-Partition Merge into `Claim.TopWalkCore` (`topWalkCore_of_closedPartition`):**
   Merges the closed conditional walk records across shards `0 .. n-1` into a single
   `Claim.TopWalkCore shardCalls.flatten a t allSeeds E_all lim Top_all rank_all` using
   lexicographic global rank `k * (allCalls.length + 1) + r.depth`. Any assumed dependency
   `x ∈ entries[k].asms` is discharged by an earlier shard `j < k` (`x ∈ entries[j].seeds`),
   yielding strictly smaller rank (`j * M + d_j < k * M + d_k`) for both `closed` and `owner`,
   `SourceSafe` via shard `j`'s `ClaimableSeed`, and non-block via `NoBlockAssumedRef`.
5. **Unconditional Set-Theoretic Model (`sourceShardedComposed`, `circuitShardedComposed`):**
   Restricts to seed-reachable records (`TopWalkCore.restrictReach`, `TopWalkCore.reach_graph`),
   instantiates `Binding.binding_skeleton_overW` and `Typing.familySteps_closedWF` at
   `FormerOpenTraceAt` (zero residual obligations), and applies `Typing.typing_skeleton_core_family_modeled`
   to conclude `ConsistentReadOver` (i.e., `Nonempty (Ix.Kernel.Model W (claimedEnv env))` for every
   `Ix.Kernel.SetTheory W`), `SeedsNotFalse`, `SeedsInhabited`, and
   `aggregated_root_sharded_checkEnv_model_unconditional`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

universe u

namespace IxVM.Refinement.Endpoint

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement
open IxVM.Refinement.Core
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding
open IxVM (F)
open Ix.Cert.Aggr

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## 1. ROM Disjoint-Union Merging (`bounded_of_roms_sum_le`) -/

private def addrPos : List F → F → Nat
  | [], _ => 0
  | x :: xs, a => if x = a then 0 else addrPos xs a + 1

private theorem addrPos_lt : ∀ {xs : List F} {a : F}, a ∈ xs → addrPos xs a < xs.length
  | [], _, h => by cases h
  | x :: xs, a, h => by
    unfold addrPos
    by_cases hxa : x = a
    · simp [hxa]
    · simp only [hxa, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp h with rfl | htl
      · exact absurd rfl hxa
      · exact Nat.succ_lt_succ (addrPos_lt htl)

private theorem addrPos_inj : ∀ {xs : List F} {a b : F},
    a ∈ xs → b ∈ xs → addrPos xs a = addrPos xs b → a = b
  | [], _, _, ha, _, _ => by cases ha
  | x :: xs, a, b, ha, hb, heq => by
    unfold addrPos at heq
    by_cases hxa : x = a <;> by_cases hxb : x = b
    · exact hxa.symm.trans hxb
    · rw [ite_eq_left hxa, ite_eq_right hxb] at heq; cases heq
    · rw [ite_eq_right hxa, ite_eq_left hxb] at heq; cases heq
    · simp only [hxa, hxb, ↓reduceIte, Nat.add_right_cancel_iff] at heq
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd rfl hxa
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hxb
        · exact addrPos_inj ha' hb' heq

private theorem nat_le_list_sum_of_mem : ∀ {xs : List Nat} {n : Nat}, n ∈ xs → n ≤ xs.sum
  | [], _, h => by cases h
  | x :: xs, n, h => by
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | htl
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (nat_le_list_sum_of_mem htl) (Nat.le_add_left _ _)

private theorem value_type_mapAddress {G A B : Type} (f : A → B) (v : Aiur.Value G A) :
    (v.mapAddress f).type = v.type := by
  cases v with
  | field _ | ptr _ _ | construct _ _ _ =>
    simp only [Aiur.Value.mapAddress, Aiur.Value.type]
  | tuple items =>
    simp only [Aiur.Value.mapAddress, Aiur.Value.type, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left fun x _ => value_type_mapAddress f x
termination_by sizeOf v

private theorem represents_remap {G : Type} (f : G → G) {rom rom' : Aiur.ROM G}
    {heap : Aiur.Heap G}
    (hsub : ∀ a enc, (a, enc) ∈ rom.entries → (f a, enc.mapAddress f) ∈ rom'.entries)
    {s : Aiur.SourceValue G} {v : Aiur.Value G}
    (hrep : Aiur.Represents rom heap s v) :
    Aiur.Represents rom' heap s (v.mapAddress f) := by
  induction hrep using Aiur.Represents.rec
    (motive_2 := fun xs ys _ =>
      List.Forall₂ (Aiur.Represents rom' heap) xs (ys.map (Aiur.Value.mapAddress f))) with
  | field =>
    simp only [Aiur.Value.mapAddress]
    exact .field
  | tuple _ ih =>
    simp only [Aiur.Value.mapAddress]
    exact .tuple ih
  | construct _ ih =>
    simp only [Aiur.Value.mapAddress]
    exact .construct ih
  | @ptr loc stored addr enc hsrc hcell _ ih =>
    simp only [Aiur.Value.mapAddress]
    rw [← value_type_mapAddress f enc]
    exact .ptr hsrc (hsub addr enc hcell) ih
  | nil => exact .nil
  | cons _ _ ihH ihT => exact .cons ihH ihT

private theorem represents_mono_entries {G : Type} {rom rom' : Aiur.ROM G} {heap : Aiur.Heap G}
    (hsub : ∀ e ∈ rom.entries, e ∈ rom'.entries)
    {s : Aiur.SourceValue G} {v : Aiur.Value G}
    (hrep : Aiur.Represents rom heap s v) :
    Aiur.Represents rom' heap s v := by
  induction hrep using Aiur.Represents.rec
    (motive_2 := fun xs ys _ => List.Forall₂ (Aiur.Represents rom' heap) xs ys) with
  | field => exact .field
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | ptr hsrc hcell _ ih => exact .ptr hsrc (hsub _ hcell) ih
  | nil => exact .nil
  | cons _ _ ihH ihT => exact .cons ihH ihT

private theorem natCast_inj_goldilocks {m n : Nat}
    (hm : m < Aiur.Library.U32.Goldilocks.modulus)
    (hn : n < Aiur.Library.U32.Goldilocks.modulus)
    (h : (m : F) = (n : F)) : m = n := by
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at hval

private theorem pow39_lt_goldilocks : 2 ^ 39 < Aiur.Library.U32.Goldilocks.modulus := by
  decide

private def remapEntries (off : Nat) (addrs : List F) (rom : Aiur.ROM F) :
    List (F × Aiur.Value F) :=
  let f : F → F := fun a => ((off + addrPos addrs a : Nat) : F)
  rom.entries.map fun e => (f e.1, e.2.mapAddress f)

private def mergeEntries :
    Nat → List (Aiur.ROM F × List F × List (Call F)) → List (F × Aiur.Value F)
  | _, [] => []
  | off, (rom, addrs, _) :: rest =>
    remapEntries off addrs rom ++ mergeEntries (off + addrs.length) rest

private def itemsTotalLen (items : List (Aiur.ROM F × List F × List (Call F))) : Nat :=
  (items.map fun x => x.2.1.length).sum

private theorem itemsTotalLen_cons (rom : Aiur.ROM F) (addrs : List F) (calls : List (Call F))
    (rest : List (Aiur.ROM F × List F × List (Call F))) :
    itemsTotalLen ((rom, addrs, calls) :: rest) = addrs.length + itemsTotalLen rest := rfl

private theorem mergeEntries_addr_range :
    ∀ (items : List (Aiur.ROM F × List F × List (Call F))) (off : Nat),
      (∀ it ∈ items, ∀ e ∈ it.1.entries, e.1 ∈ it.2.1) →
      ∀ e ∈ mergeEntries off items,
        ∃ m : Nat, off ≤ m ∧ m < off + itemsTotalLen items ∧ e.1 = (m : F) := by
  intro items
  induction items with
  | nil => intro off _ e he; cases he
  | cons it rest ih =>
    rcases it with ⟨rom, addrs, calls⟩
    intro off hcov e he
    simp only [mergeEntries, List.mem_append] at he
    rcases he with hhd | htl
    · unfold remapEntries at hhd
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hhd
      have hin : e₀.1 ∈ addrs := hcov (rom, addrs, calls) List.mem_cons_self e₀ he₀
      have hidx : addrPos addrs e₀.1 < addrs.length := addrPos_lt hin
      refine ⟨off + addrPos addrs e₀.1, Nat.le_add_right _ _, ?_, rfl⟩
      rw [itemsTotalLen_cons]
      omega
    · have hcov' : ∀ it ∈ rest, ∀ e ∈ it.1.entries, e.1 ∈ it.2.1 :=
        fun it hit => hcov it (List.mem_cons_of_mem _ hit)
      obtain ⟨m, hlo, hhi, hm⟩ := ih (off + addrs.length) hcov' e htl
      refine ⟨m, by omega, ?_, hm⟩
      rw [itemsTotalLen_cons]
      omega

private theorem mergeEntries_valid :
    ∀ (items : List (Aiur.ROM F × List F × List (Call F))) (off : Nat),
      (∀ it ∈ items, it.1.Valid ∧ ∀ e ∈ it.1.entries, e.1 ∈ it.2.1) →
      off + itemsTotalLen items ≤ 2 ^ 39 →
      (Aiur.ROM.mk (mergeEntries off items)).Valid := by
  intro items
  induction items with
  | nil => intro _ _ _ _ ha; cases ha
  | cons it rest ih =>
    rcases it with ⟨rom, addrs, calls⟩
    intro off hgood hle
    have ⟨hvalHd, hcovHd⟩ := hgood (rom, addrs, calls) List.mem_cons_self
    have hgoodTl : ∀ it ∈ rest, it.1.Valid ∧ ∀ e ∈ it.1.entries, e.1 ∈ it.2.1 :=
      fun it hit => hgood it (List.mem_cons_of_mem _ hit)
    have hleTl : (off + addrs.length) + itemsTotalLen rest ≤ 2 ^ 39 := by
      rw [itemsTotalLen_cons] at hle
      omega
    have hvalTl := ih (off + addrs.length) hgoodTl hleTl
    have hcovTl : ∀ it ∈ rest, ∀ e ∈ it.1.entries, e.1 ∈ it.2.1 :=
      fun it hit => (hgoodTl it hit).2
    have hmod : 2 ^ 39 < Aiur.Library.U32.Goldilocks.modulus := pow39_lt_goldilocks
    intro a ha b hb hab hty
    simp only [mergeEntries, List.mem_append] at ha hb
    rcases ha with ha1 | ha2 <;> rcases hb with hb1 | hb2
    · unfold remapEntries at ha1 hb1
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha1
      obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb1
      have haIn : a₀.1 ∈ addrs := hcovHd a₀ ha₀
      have hbIn : b₀.1 ∈ addrs := hcovHd b₀ hb₀
      have haIdx : addrPos addrs a₀.1 < addrs.length := addrPos_lt haIn
      have hbIdx : addrPos addrs b₀.1 < addrs.length := addrPos_lt hbIn
      have hNatEq : off + addrPos addrs a₀.1 = off + addrPos addrs b₀.1 := by
        apply natCast_inj_goldilocks
        · rw [itemsTotalLen_cons] at hle; omega
        · rw [itemsTotalLen_cons] at hle; omega
        · exact hab
      have hAddrEq : a₀.1 = b₀.1 := addrPos_inj haIn hbIn (by omega)
      have hTy0 : a₀.2.type = b₀.2.type := by
        simpa only [value_type_mapAddress] using hty
      have hValEq : a₀.2 = b₀.2 := hvalHd a₀ ha₀ b₀ hb₀ hAddrEq hTy0
      dsimp only
      rw [hValEq]
    · unfold remapEntries at ha1
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha1
      have haIdx : addrPos addrs a₀.1 < addrs.length := addrPos_lt (hcovHd a₀ ha₀)
      obtain ⟨mb, hloB, hhiB, hmb⟩ := mergeEntries_addr_range rest (off + addrs.length) hcovTl b hb2
      have hNatEq : off + addrPos addrs a₀.1 = mb := by
        apply natCast_inj_goldilocks
        · rw [itemsTotalLen_cons] at hle; omega
        · omega
        · exact hab.trans hmb
      omega
    · unfold remapEntries at hb1
      obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb1
      have hbIdx : addrPos addrs b₀.1 < addrs.length := addrPos_lt (hcovHd b₀ hb₀)
      obtain ⟨ma, hloA, hhiA, hma⟩ := mergeEntries_addr_range rest (off + addrs.length) hcovTl a ha2
      have hNatEq : ma = off + addrPos addrs b₀.1 := by
        apply natCast_inj_goldilocks
        · omega
        · rw [itemsTotalLen_cons] at hle; omega
        · exact hma.symm.trans hab
      omega
    · exact hvalTl a ha2 b hb2 hab hty

private theorem mergeEntries_callsInROM :
    ∀ (items : List (Aiur.ROM F × List F × List (Call F))) (off : Nat),
      (∀ it ∈ items, CallsInROM it.1 it.2.2) →
      CallsInROM (Aiur.ROM.mk (mergeEntries off items)) (items.map (·.2.2)).flatten := by
  intro items
  induction items with
  | nil => intro _ _ cl hcl; cases hcl
  | cons it rest ih =>
    rcases it with ⟨rom, addrs, calls⟩
    intro off hcalls cl hcl v hv
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at hcl
    rcases hcl with hhd | htl
    · obtain ⟨w, hw⟩ := hcalls (rom, addrs, calls) List.mem_cons_self cl hhd v hv
      let f : F → F := fun a => ((off + addrPos addrs a : Nat) : F)
      refine ⟨w.mapAddress f, represents_remap f ?_ hw⟩
      intro a enc hmem
      simp only [mergeEntries, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨(a, enc), hmem, rfl⟩)
    · have hcallsTl : ∀ it ∈ rest, CallsInROM it.1 it.2.2 :=
        fun it hit => hcalls it (List.mem_cons_of_mem _ hit)
      obtain ⟨w, hw⟩ := ih (off + addrs.length) hcallsTl cl htl v hv
      refine ⟨w, represents_mono_entries ?_ hw⟩
      intro e he
      simp only [mergeEntries, List.mem_append]
      exact Or.inr he

private theorem bounded_of_roms_sum_le
    (items : List (Aiur.ROM F × List F × List (Call F)))
    (hgood : ∀ it ∈ items, it.1.Valid ∧ (∀ e ∈ it.1.entries, e.1 ∈ it.2.1) ∧ CallsInROM it.1 it.2.2)
    (hle : itemsTotalLen items ≤ 2 ^ 39) :
    Bounded (items.map (·.2.2)).flatten := by
  refine ⟨⟨mergeEntries 0 items⟩,
    mergeEntries_valid items 0 (fun it hit => ⟨(hgood it hit).1, (hgood it hit).2.1⟩) (by simpa using hle),
    ?_,
    mergeEntries_callsInROM items 0 (fun it hit => (hgood it hit).2.2)⟩
  refine ⟨_root_.List.map (fun m : Nat => (m : F)) (_root_.List.range (itemsTotalLen items)), ?_, ?_⟩
  · rw [List.length_map, List.length_range]
    exact hle
  · intro e he
    obtain ⟨m, _, hlt, hm⟩ :=
      mergeEntries_addr_range items 0 (fun it hit => (hgood it hit).2.1) e he
    simp only [Nat.zero_add] at hlt
    exact List.mem_map.mpr ⟨m, List.mem_range.mpr hlt, hm.symm⟩

/-! ## 2. `FamCallsModeled` Closure Under Flattening -/

private theorem famCallsModeled_flatten {csList : List (List (Call F))}
    (h : ∀ cs ∈ csList, Typing.FamCallsModeled cs) :
    Typing.FamCallsModeled csList.flatten := by
  intro rc xb xrb h_cf b hmem hb
  obtain ⟨cs, hcs_in, hcl_in⟩ := List.mem_flatten.mp hmem
  obtain ⟨r_mod, m_mod, m_mod', cs_mod, ev, hne, hrep, hsub⟩ :=
    h cs hcs_in rc xb xrb h_cf b hcl_in hb
  exact ⟨r_mod, m_mod, m_mod', cs_mod, ev, hne, hrep,
    fun cl hcl => List.mem_flatten.mpr ⟨cs, hcs_in, hsub cl hcl⟩⟩

/-! ## 3. Conditional Reference Safety (`RecordRefsUnderIn`) & `CondTopRec` -/

private theorem rep_nil_of_load_any {α : Type} {en en' : String}
    {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {p : SourceValue F}
    (rep : RepList en R h xs p) (hl : loadValue h p = .ok (.construct en' "Nil" [])) :
    xs = [] := by
  cases rep with
  | nil _ => rfl
  | cons cell _ _ =>
    rw [Lib.load_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

private theorem rep_cons_of_load_any {α : Type} {en en' : String}
    {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {p x y : SourceValue F}
    (rep : RepList en R h xs p) (hl : loadValue h p = .ok (.construct en' "Cons" [x, y])) :
    ∃ z zs, xs = z :: zs ∧ R h z x ∧ RepList en R h zs y := by
  cases rep with
  | nil cell =>
    rw [Lib.load_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)
  | cons cell rh rt =>
    rw [Lib.load_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs
    injection hargs with hx hrest; injection hrest with hy _
    subst hx hy
    exact ⟨_, _, rfl, rh, rt⟩

private theorem repAddrSet_of_iff {h : Heap F} {S₁ S₂ : List _root_.Address} {tree : SourceValue F}
    (hiff : ∀ x, x ∈ S₁ ↔ x ∈ S₂) (hs : Claim.RepAddrSet h S₁ tree) :
    Claim.RepAddrSet h S₂ tree := by
  obtain ⟨es, hbst, hval, hmem⟩ := hs
  exact ⟨es, hbst, hval, fun b => (hmem b).trans (hiff (ixAddr b))⟩

private theorem addr_set_member_iff_spec {S : List _root_.Address} {b : Bytes.Address}
    {x_b tree r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h b x_b) (hs : Claim.RepAddrSet h S tree)
    (ev : ObsFn Obs.W "KernelClaim::addr_set_member" [x_b, tree] h r h' calls) :
    r = .field (if ixAddr b ∈ S then 1 else 0) ∧ h' = h := by
  obtain ⟨_, ev6, _⟩ := Obs.«KernelClaim::addr_set_member».obs ev
  rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev6
  exact Claim.rbtree_set_lookup_spec hb hs ev6

/-- The walk executed `assert_safe_record_refs_under(rc, addr, c, excluded)` where `excluded`
represents the address set `asms`. -/
private def RecordRefsUnderIn (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (bAddr : _root_.Address) (lim : Option Nat) (asms : List _root_.Address)
    (a : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∃ (h h' : Heap F) (rc ap cp ex r : SourceValue F) (cs : List (Call F)),
    Claim.RCLimRep t bAddr lim h rc ∧ BaseSeams.addr h ap a ∧ Claim.RepConstant h c cp ∧
    Claim.RepAddrSet h asms ex ∧
    ObsFn Obs.W "KernelClaim::assert_safe_record_refs_under" [rc, ap, cp, ex] h r h' cs ∧
    ∀ cl ∈ cs, cl ∈ calls

private theorem RecordRefsUnderIn.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr a : _root_.Address} {lim : Option Nat} {asms : List _root_.Address} {c : Ixon.Constant}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hg : RecordRefsUnderIn cs₁ t bAddr lim asms a c) :
    RecordRefsUnderIn cs₂ t bAddr lim asms a c := by
  obtain ⟨h, h', rc, ap, cp, ex, r, cs, hrc, ha, hc, hex, ev, hs⟩ := hg
  exact ⟨h, h', rc, ap, cp, ex, r, cs, hrc, ha, hc, hex, ev, fun cl hcl => hsub cl (hs cl hcl)⟩

private theorem RecordRefsUnderIn.of_recordRefsIn {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hg : Claim.RecordRefsIn calls t bAddr lim a c) :
    RecordRefsUnderIn calls t bAddr lim [] a c := by
  obtain ⟨h, h', rc, ap, cp, r, cs, hrc, ha, hc, ev, hs⟩ := hg
  obtain ⟨csUnder, evUnder, hcalls⟩ := Obs.«KernelClaim::assert_safe_record_refs».obs ev
  exact ⟨h, h', rc, ap, cp, .construct addrMapEnum "Nil" [], r, csUnder,
    hrc, ha, hc, Claim.RepAddrSet.nil h, evUnder,
    fun cl hcl => hs cl (by rw [hcalls]; simp [hcl])⟩

private theorem refs_small_of_decoded_cond {bytes : ByteArray} {c : Ixon.Constant}
    (hsz : bytes.size < 4294967296) (he : Ixon.deConstantExact bytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c he
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private theorem RecordRefsUnderIn.safe {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address} {lim : Option Nat}
    {asms : List _root_.Address} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hc : recordOf E₀ a = some c) (hsafe : Claim.SourceSafe E₀ a)
    (hg : RecordRefsUnderIn calls t bAddr lim asms a c) :
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      x ∉ asms → ¬ Claim.CoveredAt t lim x → Claim.SourceSafe E₀ x := by
  obtain ⟨h, h', rc, ap, cp, ex, r, cs, hrc, ha, hcp, hex, evUnder, hsubUnder⟩ := hg
  match Obs.«KernelClaim::assert_safe_record_refs_under».obs evUnder with
  | .other (cs13 := csSrc) (ev15 := ev15) (hne190 := hn) (hc198 := hcs) .. =>
    have hs : ∀ cl ∈ csSrc, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    exact (hn (Claim.record_unsafe_eq_zero_in_store hS hc (hsafe c hc).1 ha ev15 hs)).elim
  | .n0_other (cs40 := csOwner) (ev15 := ev15) (ev55 := ev55) (ev42 := ev42)
      (hne181 := hn) (hc189 := hcs) .. =>
    have ext := ev15.heap_extends
    obtain ⟨_, haOwner⟩ := Claim.record_owner_spec (BaseSeams.addr_mono ext ha) (hcp.mono ext) ev55
    obtain ⟨_, bytes, cb, hsz, hh, hb, hd, he, himp⟩ :=
      Claim.record_unsafe_safe_spec (BaseSeams.addr_mono ev55.heap_extends haOwner) ev42
    have hs : ∀ cl ∈ csOwner, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    have howner := Claim.recordOf_hashed hS hH (Core.hashed_mono hs hh) hsz hd he
    rw [hb] at howner
    exact (hn (himp ((hsafe c hc).2 cb howner))).elim
  | .n0_n0 (m147 := idxHeap) (cs13 := csSrc) (cs124 := csLoop) (x_refs := refsPtr) (ev15 := ev15)
      (ev55 := ev55) (ev42 := ev42) (hv90 := hv90) (ev157 := ev157) (ev126 := ev126)
      (hc179 := hcs) .. =>
    have hsSrc : ∀ cl ∈ csSrc, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    obtain ⟨_, bytes, c', hsz, hh, hb, _, he, _⟩ := Claim.record_unsafe_safe_spec ha ev15
    have hrecAt : Ix.Cert.recordAt E₀ a = some c := (hS.recordOf_eq_recordAt a).symm.trans hc
    have hcc : c' = c := hS.record_eq hrecAt (Core.hashed_mono hsSrc hh) hb he
    subst c'
    have hrefsSmall := refs_small_of_decoded_cond hsz he
    have extBefore := ev15.heap_extends.trans (ev55.heap_extends.trans ev42.heap_extends)
    obtain ⟨extIdx, hidx⟩ := Claim.const_idxs_of_spec (hcp.mono extBefore) ev157
    have hRefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem idxHeap
        c.refs.toList refsPtr := by
      obtain ⟨_, _, rp, _, _, heq, _, _, hrf, _, _⟩ := hcp
      have heq' := heq.symm.trans hv90
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at heq'
      rcases heq' with ⟨_, _, heqRefs, _, _⟩
      rw [heqRefs] at hrf
      exact repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ (extBefore.trans extIdx) hrf
    have hloopSub : ∀ cl ∈ csLoop, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    have hloop := Claim.assert_safe_used_refs_set_spec hS c.refs.toList 0
      (by simpa only [Nat.zero_add, Array.length_toList] using hrefsSmall)
      (hrc.mono (extBefore.trans extIdx)) hRefs hidx (hex.mono (extBefore.trans extIdx))
      ev126 hloopSub
    intro i hi x hx hnAsm hnCov
    obtain ⟨hiLt, hget⟩ := List.getElem?_eq_some_iff.mp hx
    have hi' : i ∈ BaseSeams.usedRefIdxs c := by
      rw [Assembly.usedRefIdxs_eq]
      exact hi
    have hs := hloop i hiLt (by simpa only [Nat.zero_add] using hi')
    rw [hget] at hs
    exact hs hnAsm hnCov

/-- A record checked and guarded by a conditional shard walk at limit `lim` under exclusion set
`asms`, tagged with its local call-tree depth. -/
private structure CondTopRec (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (lim : Option Nat) (asms : List _root_.Address) where
  addr : _root_.Address
  rawBytes : ByteArray
  c : Ixon.Constant
  depth : Nat
  hsz : rawBytes.size < 4294967296
  hhashed : Hashed calls rawBytes
  hblake : Address.blake3Pure rawBytes = addr
  hde : Ixon.deConstant rawBytes = .ok c
  hdeExact : Ixon.deConstantExact rawBytes = .ok c
  hchecked :
    (∃ ms, c.info = .muts ms ∧
      ∀ (k : Nat), k < ms.size → Claim.MemberCheckedLimAt calls bAddr t addr ms k lim) ∨
    Claim.CheckedLimAt calls bAddr t addr lim
  hguard : RecordRefsUnderIn calls t bAddr lim asms addr c
  hquot : Claim.QuotRecordRefsIn calls t bAddr lim addr c

private def CondTopRec.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (r : CondTopRec cs₁ bAddr t lim asms) :
    CondTopRec cs₂ bAddr t lim asms where
  addr := r.addr
  rawBytes := r.rawBytes
  c := r.c
  depth := r.depth
  hsz := r.hsz
  hhashed := Core.hashed_mono hsub r.hhashed
  hblake := r.hblake
  hde := r.hde
  hdeExact := r.hdeExact
  hchecked := r.hchecked.imp
    (fun ⟨ms, hms, hk⟩ => ⟨ms, hms, fun k hlt => (hk k hlt).mono hsub⟩)
    (fun hc => hc.mono hsub)
  hguard := r.hguard.mono hsub
  hquot := r.hquot.mono hsub

private theorem map_addr_condTopRec_mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (recs : List (CondTopRec cs₁ bAddr t lim asms)) :
    (recs.map (CondTopRec.mono hsub)).map (·.addr) = recs.map (·.addr) := by
  induction recs with
  | nil => rfl
  | cons r rs ih => simp [CondTopRec.mono, ih]

private def CondTopRec.ofTopRec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} (r : Claim.TopRec calls bAddr t lim) :
    CondTopRec calls bAddr t lim [] where
  addr := r.addr
  rawBytes := r.rawBytes
  c := r.c
  depth := r.depth
  hsz := r.hsz
  hhashed := r.hhashed
  hblake := r.hblake
  hde := r.hde
  hdeExact := r.hdeExact
  hchecked := r.hchecked
  hguard := RecordRefsUnderIn.of_recordRefsIn r.hguard
  hquot := r.hquot

private def CondTopRecsClosed {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address}
    (recs : List (CondTopRec calls bAddr t lim asms)) : Prop :=
  ∀ r ∈ recs,
    (Claim.IsProjRec r.c →
      (∃ r' ∈ recs, r'.addr = Ix.Cert.ownerOf r.addr r.c ∧ r'.depth < r.depth) ∨
        Ix.Cert.ownerOf r.addr r.c ∈ asms) ∧
    (∀ i ∈ BaseSeams.usedRefIdxs r.c, ∀ b, r.c.refs[i]? = some b →
      Claim.RefAllowedIn calls t bAddr lim b ∧
      ((Claim.NotBlockIn calls b ∧ ∃ r' ∈ recs, r'.addr = b ∧ r'.depth < r.depth) ∨
        Claim.CoveredAt t lim b ∨
        b ∈ asms))

private theorem CondTopRecsClosed.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (CondTopRec cs₁ bAddr t lim asms)}
    (hcl : CondTopRecsClosed recs) : CondTopRecsClosed (recs.map (CondTopRec.mono hsub)) := by
  intro rm hrm
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrm
  obtain ⟨ho, hu⟩ := hcl r hr
  refine ⟨fun hp => ?_, fun i hi b hb => ?_⟩
  · rcases ho hp with ⟨r', hr', ha', hlt'⟩ | hasm
    · exact .inl ⟨CondTopRec.mono hsub r', List.mem_map_of_mem hr', ha', hlt'⟩
    · exact .inr hasm
  · obtain ⟨hal, hrest⟩ := hu i hi b hb
    refine ⟨hal.mono hsub, ?_⟩
    rcases hrest with ⟨hnb, r', hr', ha', hlt'⟩ | hcov | hasm
    · exact .inl ⟨hnb.mono hsub, CondTopRec.mono hsub r', List.mem_map_of_mem hr', ha', hlt'⟩
    · exact .inr (.inl hcov)
    · exact .inr (.inr hasm)

private theorem CondTopRecsClosed.sub {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address}
    {xs ys : List (CondTopRec calls bAddr t lim asms)}
    (hsub : ∀ r ∈ xs, r ∈ ys) (hcl : CondTopRecsClosed xs) :
    ∀ r ∈ xs,
      (Claim.IsProjRec r.c →
        (∃ r' ∈ ys, r'.addr = Ix.Cert.ownerOf r.addr r.c ∧ r'.depth < r.depth) ∨
          Ix.Cert.ownerOf r.addr r.c ∈ asms) ∧
      (∀ i ∈ BaseSeams.usedRefIdxs r.c, ∀ b, r.c.refs[i]? = some b →
        Claim.RefAllowedIn calls t bAddr lim b ∧
        ((Claim.NotBlockIn calls b ∧ ∃ r' ∈ ys, r'.addr = b ∧ r'.depth < r.depth) ∨
          Claim.CoveredAt t lim b ∨
          b ∈ asms)) := by
  intro r hr
  obtain ⟨ho, hu⟩ := hcl r hr
  refine ⟨fun hp => ?_, fun i hi b hb => ?_⟩
  · rcases ho hp with ⟨r', hr', ha', hlt'⟩ | hasm
    · exact .inl ⟨r', hsub r' hr', ha', hlt'⟩
    · exact .inr hasm
  · obtain ⟨hal, hrest⟩ := hu i hi b hb
    refine ⟨hal, ?_⟩
    rcases hrest with ⟨hnb, r', hr', ha', hlt'⟩ | hcov | hasm
    · exact .inl ⟨hnb, r', hsub r' hr', ha', hlt'⟩
    · exact .inr (.inl hcov)
    · exact .inr (.inr hasm)

private theorem CondTopRecsClosed.append {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address}
    {r₁ r₂ : List (CondTopRec calls bAddr t lim asms)}
    (h₁ : CondTopRecsClosed r₁) (h₂ : CondTopRecsClosed r₂) :
    CondTopRecsClosed (r₁ ++ r₂) := by
  intro r hr
  rcases List.mem_append.mp hr with hr1 | hr2
  · exact h₁.sub (fun x hx => List.mem_append_left _ hx) r hr1
  · exact h₂.sub (fun x hx => List.mem_append_right _ hx) r hr2

private theorem condTopRecsClosed_cons {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address}
    {r₀ : CondTopRec calls bAddr t lim asms} {rest : List (CondTopRec calls bAddr t lim asms)}
    (hrest : CondTopRecsClosed rest)
    (hown : Claim.IsProjRec r₀.c →
      (∃ r' ∈ r₀ :: rest, r'.addr = Ix.Cert.ownerOf r₀.addr r₀.c ∧ r'.depth < r₀.depth) ∨
        Ix.Cert.ownerOf r₀.addr r₀.c ∈ asms)
    (hrefs : ∀ i ∈ BaseSeams.usedRefIdxs r₀.c, ∀ b, r₀.c.refs[i]? = some b →
      Claim.RefAllowedIn calls t bAddr lim b ∧
      ((Claim.NotBlockIn calls b ∧ ∃ r' ∈ r₀ :: rest, r'.addr = b ∧ r'.depth < r₀.depth) ∨
        Claim.CoveredAt t lim b ∨
        b ∈ asms)) :
    CondTopRecsClosed (r₀ :: rest) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hmem
  · exact ⟨hown, hrefs⟩
  · exact hrest.sub (fun x hx => List.mem_cons_of_mem _ hx) r hmem

private theorem condTopRecsClosed_of_topRecsClosed {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {recs : List (Claim.TopRec calls bAddr t lim)}
    (hcl : Claim.TopRecsClosed recs) :
    CondTopRecsClosed (recs.map CondTopRec.ofTopRec) := by
  intro rm hrm
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrm
  obtain ⟨ho, hu⟩ := hcl r hr
  refine ⟨fun hp => ?_, fun i hi b hb => ?_⟩
  · obtain ⟨r', hr', ha', hlt'⟩ := ho hp
    exact .inl ⟨CondTopRec.ofTopRec r', List.mem_map_of_mem hr', ha', hlt'⟩
  · obtain ⟨hal, hrest⟩ := hu i hi b hb
    refine ⟨hal, ?_⟩
    rcases hrest with ⟨hnb, r', hr', ha', hlt'⟩ | hcov
    · exact .inl ⟨hnb, CondTopRec.ofTopRec r', List.mem_map_of_mem hr', ha', hlt'⟩
    · exact .inr (.inl hcov)

private theorem condTopRec_mono_depth_lt {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address} {n : Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (CondTopRec cs₁ bAddr t lim asms)}
    (hdep : ∀ r ∈ recs, r.depth ≤ cs₁.length) (hlt : cs₁.length < n) :
    ∀ r ∈ recs.map (CondTopRec.mono hsub), r.depth < n := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  have hd := hdep r₀ hr₀
  simp only [CondTopRec.mono]
  omega

private theorem condTopRec_mono_depth_le {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {asms : List _root_.Address} {n : Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (CondTopRec cs₁ bAddr t lim asms)}
    (hdep : ∀ r ∈ recs, r.depth ≤ cs₁.length) (hle : cs₁.length ≤ n) :
    ∀ r ∈ recs.map (CondTopRec.mono hsub), r.depth ≤ n := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  have hd := hdep r₀ hr₀
  simp only [CondTopRec.mono]
  omega

/-- Output of decoding and walking one conditional shard under binding `bAddr`, role table `t`,
and uniform limit `lim`. -/
private def CondShardWalk (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (seeds asms : List _root_.Address) : Prop :=
  ∃ recs : List (CondTopRec calls bAddr t lim asms),
    (∀ a ∈ seeds, a ∈ recs.map (·.addr)) ∧
    (∀ a ∈ seeds, Claim.ClaimableSeed calls t a) ∧
    CondTopRecsClosed recs ∧
    (∀ r ∈ recs, r.depth ≤ calls.length)

/-! ## 4. Conditional Walk & Shard Claim Decoding Refinement -/

private theorem cond_mutShape_of_repMutConst {h : Heap F} {m : Ixon.MutConst}
    {v : SourceValue F} (hr : Claim.RepMutConst h m v) : Specs.Callees.MutShape h m v := by
  cases m with
  | defn d => obtain ⟨dv, hv, _⟩ := hr; exact ⟨dv, hv⟩
  | indc i => obtain ⟨iv, hv, _⟩ := hr; exact ⟨iv, hv⟩
  | recr r => obtain ⟨rv, hv, _⟩ := hr; exact ⟨rv, hv⟩

private theorem cond_membersRep_of_repMutConstList {h : Heap F}
    {xs : List Ixon.MutConst} {p : SourceValue F}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» Claim.RepMutConst h xs p) :
    Specs.Callees.MembersRep h xs p := by
  induction hrep with
  | nil cell => exact .nil cell
  | cons cell rh _ ih => exact .cons cell (cond_mutShape_of_repMutConst rh) ih

private theorem cond_blake3Pure_hash_size (b : ByteArray) :
    (Address.blake3Pure b).hash.size = 32 := by
  cases b with
  | mk arr =>
    have h := Ingress.blake3Pure_eq arr.toList
    simp only [Array.toArray_toList] at h
    rw [h]
    exact (Blake3.Pure.digest arr.toList).size_toArray

private theorem cond_getScope_ok_inv {variant : UInt64} {bs : List UInt8} {i : Nat}
    {fmt valByte : UInt8}
    (h1 : Ixon.getU8 { idx := i, bytes := ⟨bs.toArray⟩ } =
      .ok fmt { idx := i + 1, bytes := ⟨bs.toArray⟩ })
    (h2 : Ixon.getU8 { idx := i + 1, bytes := ⟨bs.toArray⟩ } =
      .ok valByte { idx := i + 2, bytes := ⟨bs.toArray⟩ })
    {w : UInt8} {st : Ixon.GetState}
    (hok : Ix.Claim.getScope variant { idx := i, bytes := ⟨bs.toArray⟩ } = .ok w st) :
    w = valByte ∧ st = { idx := i + 2, bytes := ⟨bs.toArray⟩ } ∧
      (valByte = Ix.Claim.validatorForVariant variant ∨
        valByte = Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∨
        valByte = Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS) := by
  unfold Ix.Claim.getScope at hok
  simp only [bind, EStateM.bind, pure, EStateM.pure, h1] at hok
  by_cases hfmt : (fmt == Ixon.Env.OBJECT_FORMAT) = true
  case neg =>
    simp [hfmt, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  simp only [hfmt, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure, h2] at hok
  by_cases hc1 : (valByte == Ix.Claim.validatorForVariant variant) = true
  · simp only [hc1, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst, .inl (beq_iff_eq.mp hc1)⟩
  simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc2 : (valByte == Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED &&
      Ix.Claim.variantMayAssume variant) = true
  · simp only [hc2, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst, .inr (.inl (beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hc2).1))⟩
  simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc3 : (valByte == Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS &&
      variant == Ix.Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · simp only [hc3, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst, .inr (.inr (beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hc3).1))⟩
  simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc4 : (Ix.Claim.validatorForVariant variant == Ix.Claim.VALIDATOR_ERASED_LEAN &&
      valByte == Ix.Claim.VALIDATOR_ERASED_LEAN_RETIRED) = true
  · simp [hc4, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  · simp [hc4, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

private theorem cond_getPayload_variant {variant : UInt64} {valByte : UInt8}
    {s : Ixon.GetState} {c : Ix.Claim} {st : Ixon.GetState} {assumed : Bool}
    (hok : Ix.Claim.getPayload variant valByte s = .ok c st)
    (hscope : InScopeConditionalTyping assumed c) :
    variant = 4 ∨ variant = 5 := by
  unfold Ix.Claim.getPayload at hok
  by_cases hv3 : (variant == Ix.Claim.VARIANT_EVAL_CLAIM) = true
  · simp only [hv3, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv4 : (variant == Ix.Claim.VARIANT_CHECK_CLAIM) = true
  · exact .inl (beq_iff_eq.mp hv4)
  simp only [hv4, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv5 : (variant == Ix.Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · exact .inr (beq_iff_eq.mp hv5)
  simp only [hv5, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv6 : (variant == Ix.Claim.VARIANT_REVEAL_CLAIM) = true
  · simp only [hv6, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv6, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv7 : (variant == Ix.Claim.VARIANT_CONTAINS_CLAIM) = true
  · simp only [hv7, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv7, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv8 : (variant == Ix.Claim.VARIANT_CATALOG_CLAIM) = true
  · simp only [hv8, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv8, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv10 : (variant == Ix.Claim.VARIANT_BINDING_CLAIM) = true
  · simp only [hv10, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp [hv10, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

private theorem rcLim_of_assumed {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {valByte : UInt8} {assumed : Bool} {r : SourceValue F} {h : Heap F}
    (hass : (valByte == Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED) = assumed)
    (hok : ((Value.field (valByte.toNat : F) : SourceValue F) = .field 3 ∧
        Claim.RCLimRep t bAddr (some 77) h r) ∨
      ((Value.field (valByte.toNat : F) : SourceValue F) = .field 4 ∧
        Claim.RCLimRep t bAddr none h r)) :
    Claim.RCLimRep t bAddr (if assumed then none else some 77) h r := by
  have hlt : valByte.toNat < 4294967296 := by have := valByte.toNat_lt; omega
  cases assumed with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hok with ⟨-, hrc⟩ | ⟨h4, -⟩
    · exact hrc
    · exfalso
      have hv : valByte.toNat = 4 :=
        Claim.natCast_inj_of_lt_u32 hlt (by decide) (Value.field.inj h4)
      have hvb : valByte = Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED := UInt8.ext hv
      rw [hvb] at hass
      cases hass
  | true =>
    simp only [↓reduceIte]
    rcases hok with ⟨h3, -⟩ | ⟨-, hrc⟩
    · exfalso
      have hv : valByte.toNat = 3 :=
        Claim.natCast_inj_of_lt_u32 hlt (by decide) (Value.field.inj h3)
      have hvb : valByte = 3 := UInt8.ext hv
      rw [hvb] at hass
      cases hass
    · exact hrc

private theorem cond_role_ctx_axioms_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (ev : ObsFn Obs.W "KernelRoles::role_ctx_axioms" [x_rc] h r h' calls) :
    r = .construct addrMapEnum "Nil" [] ∧ h' = h := by
  obtain ⟨tbl, htbl, ⟨n, -, -, hl⟩ | ⟨-, hl⟩⟩ := hrc.cases
  · rcases Obs.«KernelRoles::role_ctx_axioms».obs ev with
      ⟨_, _, x_axioms, ld12, rfl, rfl, -⟩ | ⟨_, _, ld12, -⟩ | ⟨_, _, _, _, ld12, -⟩ | ⟨_, _, _, ld12, -⟩
    · rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      exact ⟨hargs.2.2.symm, rfl⟩
    · rw [hl] at ld12; simp at ld12
    · rw [hl] at ld12; simp at ld12
    · rw [hl] at ld12; simp at ld12
  · rcases Obs.«KernelRoles::role_ctx_axioms».obs ev with
      ⟨_, _, _, ld12, -⟩ | ⟨_, x_axioms, ld12, rfl, rfl, -⟩ | ⟨_, _, _, _, ld12, -⟩ | ⟨_, _, _, ld12, -⟩
    · rw [hl] at ld12; simp at ld12
    · rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      exact ⟨hargs.2.symm, rfl⟩
    · rw [hl] at ld12; simp at ld12
    · rw [hl] at ld12; simp at ld12

/-! ### 4a. `assert_leaves_claimable` -/

private theorem assert_leaves_claimable_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} (as : List Bytes.Address) :
    ∀ {x_rc x_leaves r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.RCLimRep t bAddr lim h x_rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h as x_leaves →
      ObsFn Obs.W "KernelClaim::assert_leaves_claimable" [x_rc, x_leaves] h r h' calls →
      Heap.Extends h h' ∧ ∀ a ∈ as.map ixAddr, Claim.ClaimableSeed calls t a := by
  induction as with
  | nil =>
    intro x_rc x_leaves r h h' calls hrc hl ev
    have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.assert_leaves_claimable.lookup
      (by simp [IxVM.KernelClaim.assert_leaves_claimable, ControlLower.hasControl]) ev
    simp only [IxVM.KernelClaim.assert_leaves_claimable] at d0
    obtain ⟨v_sc, m_sc, bs_arm, body_arm, c_sc, c_arm, d_sc, sel, d_arm, rfl⟩ := d0.matchValue_inv
    obtain ⟨p_l, d_pl, hld⟩ := d_sc.load_inv
    obtain ⟨hlook, rfl, rfl⟩ := d_pl.var_inv; simp at hlook; subst hlook
    rcases selectArm_cons_inv sel with ⟨mt_nil, rfl⟩ | ⟨_, sel1⟩
    · obtain ⟨_, hv_nil, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
      obtain ⟨_, a_u, _⟩ := d_arm.tuple_inv
      obtain ⟨_, rfl, _⟩ := a_u.nil_inv
      exact ⟨Heap.Extends.refl _, by simp⟩
    · rcases selectArm_cons_inv sel1 with ⟨mt_cons, _⟩ | ⟨_, sel2⟩
      · obtain ⟨vs, hv_cons, hlen, _⟩ := matchPattern_construct_inv mt_cons
        rcases vs with _ | ⟨x_a, _ | ⟨x_rest, _ | _⟩⟩ <;> simp at hlen
        rw [hv_cons] at hld
        obtain ⟨_, _, hbad, -⟩ := rep_cons_of_load_any hl hld
        cases hbad
      · exact (selectArm_nil_inv sel2).elim
  | cons aB rest ih =>
    intro x_rc x_leaves r h h' calls hrc hl ev
    have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.assert_leaves_claimable.lookup
      (by simp [IxVM.KernelClaim.assert_leaves_claimable, ControlLower.hasControl]) ev
    simp only [IxVM.KernelClaim.assert_leaves_claimable] at d0
    obtain ⟨v_sc, m_sc, bs_arm, body_arm, c_sc, c_arm, d_sc, sel, d_arm, rfl⟩ := d0.matchValue_inv
    obtain ⟨p_l, d_pl, hld⟩ := d_sc.load_inv
    obtain ⟨hlook, rfl, rfl⟩ := d_pl.var_inv; simp at hlook; subst hlook
    rcases selectArm_cons_inv sel with ⟨mt_nil, _⟩ | ⟨_, sel1⟩
    · obtain ⟨_, hv_nil, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
      rw [hv_nil] at hld
      cases rep_nil_of_load_any hl hld
    · rcases selectArm_cons_inv sel1 with ⟨mt_cons, rfl⟩ | ⟨_, sel2⟩
      case inr => exact (selectArm_nil_inv sel2).elim
      obtain ⟨vs, hv_cons, -, ml_cons⟩ := matchPattern_construct_inv mt_cons
      obtain ⟨x_a, _, _, _, rfl, mt_a, ml_cons1, rfl⟩ := matchListWith_cons_inv ml_cons
      obtain rfl := matchPattern_bind_inv mt_a
      obtain ⟨x_rest, _, _, _, rfl, mt_rest, ml_cons2, rfl⟩ := matchListWith_cons_inv ml_cons1
      obtain rfl := matchPattern_bind_inv mt_rest
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_cons2
      rw [hv_cons] at hld
      obtain ⟨aB', rest', heq, ha_ref, hrest⟩ := rep_cons_of_load_any hl hld
      injection heq with he1 he2
      subst he1 he2
      obtain ⟨_, m1, _, cs_ac, cs_tl, d_ac, mt_w, d_tl, rfl⟩ := d_arm.letValue_inv
      obtain ⟨_, _, _, cs_ac', a_ac, ev_ac, rfl⟩ := d_ac.call_inv
      rw [instanceName_plain_some] at ev_ac
      obtain ⟨_, _, _, _, _, rfl, d_ac0, a_ac1, rfl⟩ := a_ac.cons_inv
      obtain ⟨l0, rfl, rfl⟩ := d_ac0.var_inv; simp at l0; subst l0
      obtain ⟨_, _, _, _, _, rfl, d_ac1, a_ac2, rfl⟩ := a_ac1.cons_inv
      obtain ⟨l1, rfl, rfl⟩ := d_ac1.var_inv; simp at l1; subst l1
      obtain ⟨rfl, rfl, rfl⟩ := a_ac2.nil_inv
      obtain rfl := matchPattern_wildcard_inv mt_w
      obtain ⟨_, _, _, cs_tl', a_tl, ev_tl, rfl⟩ := d_tl.call_inv
      rw [instanceName_plain_some] at ev_tl
      obtain ⟨_, _, _, _, _, rfl, d_tl0, a_tl1, rfl⟩ := a_tl.cons_inv
      obtain ⟨l2, rfl, rfl⟩ := d_tl0.var_inv; simp at l2; subst l2
      obtain ⟨_, _, _, _, _, rfl, d_tl1, a_tl2, rfl⟩ := a_tl1.cons_inv
      obtain ⟨l3, rfl, rfl⟩ := d_tl1.var_inv; simp at l3; subst l3
      obtain ⟨rfl, rfl, rfl⟩ := a_tl2.nil_inv
      obtain ⟨ext1, hseed_hd⟩ := Claim.assert_claimable_lim_spec hrc ⟨aB, ha_ref, rfl⟩ ev_ac
      obtain ⟨ext2, hseed_tl⟩ := ih (hrc.mono ext1)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hrest) ev_tl
      refine ⟨ext1.trans ext2, fun a ha_mem => ?_⟩
      simp only [List.map_cons, List.mem_cons] at ha_mem
      rcases ha_mem with rfl | htl
      · exact hseed_hd.mono fun cl hcl => by simp [hcl]
      · exact (hseed_tl a htl).mono fun cl hcl => by simp [hcl]

/-! ### 4b. `env_walk` & `env_walk_refs` at Limit `lim` Under Exclusion Set `asms` -/

private theorem env_walk_cond_lim_fuel_aux {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {asms : List _root_.Address} :
    ∀ (fuel : Nat),
      (∀ {x_rc x_addr x_owned x_asm x_strict r : SourceValue F} {addr : _root_.Address}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         Claim.RCLimRep t bAddr lim h x_rc →
         BaseSeams.addr h x_addr addr →
         Claim.RepAddrSet h asms x_asm →
         ObsFn Obs.W "KernelClaim::env_walk" [x_rc, x_addr, x_owned, x_asm, x_strict] h r h' calls →
         Heap.Extends h h' ∧
         ∃ recs : List (CondTopRec calls bAddr t lim asms),
           (addr ∈ recs.map (·.addr) ∨ (addr ∈ asms ∧ x_strict ≠ .field 2)) ∧
           CondTopRecsClosed recs ∧
           (∀ r ∈ recs, r.depth ≤ calls.length)) ∧
      (∀ {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
         {x_rc x_refs x_consts x_owned x_asm x_strict r : SourceValue F}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         i + refs.length < 8589934592 →
         Claim.RCLimRep t bAddr lim h x_rc →
         RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs x_refs →
         Claim.RepSortedIdxFrom h idxs i x_consts →
         Claim.RepAddrSet h asms x_asm →
         ObsFn Obs.W "KernelClaim::env_walk_refs"
           [x_rc, x_refs, x_consts, .field (i : F), x_owned, x_asm, x_strict] h r h' calls →
         Heap.Extends h h' ∧
         ∃ recs : List (CondTopRec calls bAddr t lim asms),
           (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
             Claim.RefAllowedIn calls t bAddr lim refs[j] ∧
             ((Claim.NotBlockIn calls refs[j] ∧ refs[j] ∈ recs.map (·.addr)) ∨
               Claim.CoveredAt t lim refs[j] ∨
               refs[j] ∈ asms)) ∧
           CondTopRecsClosed recs ∧
           (∀ r ∈ recs, r.depth ≤ calls.length)) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    refine ⟨?_, ?_⟩
    -- 1. `KernelClaim::env_walk`
    · intro x_rc x_addr x_owned x_asm x_strict r addr h h' calls hfuel hrc ha hasm ev
      have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.env_walk.lookup
        (by simp [IxVM.KernelClaim.env_walk, ControlLower.hasControl]) ev
      simp only [IxVM.KernelClaim.env_walk] at d0
      -- `match addr_set_member(addr, asm) { 1 => ..., _ => ... }`
      obtain ⟨v_mem, m_mem, bs_m, body_m, c_mem, c_arm, d_mem, sel_m, d_arm, hcalls⟩ :=
        d0.matchValue_inv
      obtain ⟨_, m_margs, _, cs_mem, a_mem, ev_mem, rfl⟩ := d_mem.call_inv
      rw [instanceName_plain_some] at ev_mem
      obtain ⟨_, _, m_m0, _, _, rfl, d_m0, a_m1, rfl⟩ := a_mem.cons_inv
      obtain ⟨lm0, hm_m0, rfl⟩ := d_m0.var_inv; simp at lm0; subst lm0; subst m_m0
      obtain ⟨_, _, m_m1, _, _, rfl, d_m1, a_m2, rfl⟩ := a_m1.cons_inv
      obtain ⟨lm1, hm_m1, rfl⟩ := d_m1.var_inv; simp at lm1; subst lm1; subst m_m1
      obtain ⟨rfl, hm_m2, rfl⟩ := a_m2.nil_inv; subst m_margs
      obtain ⟨aB, ha_ref, ha_ix⟩ := ha
      obtain ⟨hv_mem, hm_mem⟩ := addr_set_member_iff_spec ha_ref hasm ev_mem
      subst m_mem
      rcases selectArm_cons_inv sel_m with ⟨mt1, rfl⟩ | ⟨_, sel_m1⟩
      · -- Arm `1`: `addr` is in `asms`; `assert_eq!(Fields::is_zero(strict - 2), 0); ()`
        obtain ⟨hv1, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 1) mt1
        have haddr_in_asms : addr ∈ asms := by
          rw [← ha_ix]
          by_contra hnot
          rw [ite_eq_right hnot] at hv_mem
          exact zero_ne_one (Value.field.inj (hv_mem.symm.trans hv1))
        obtain ⟨_, m_eq, _, _, _, d_eq, mt_eq, d_u, rfl⟩ := d_arm.letValue_inv
        obtain ⟨_, a_eq, ap_eq⟩ := d_eq.builtin_inv
        obtain ⟨v_iz, _, m_iz, _, _, rfl, d_iz, a_eq1, rfl⟩ := a_eq.cons_inv
        obtain ⟨_, _, _, cs_iz, a_iz, ev_iz, rfl⟩ := d_iz.call_inv
        rw [instanceName_plain_some] at ev_iz
        obtain ⟨v_sub, _, m_sub, _, _, rfl, d_sub, a_iz1, rfl⟩ := a_iz.cons_inv
        obtain ⟨x_s, x_2, m_s, _, _, d_s, d_2, op_sub, rfl⟩ := d_sub.binary_inv
        obtain ⟨ls, rfl, rfl⟩ := d_s.var_inv; simp at ls; subst ls
        obtain ⟨rfl, rfl, rfl⟩ := d_2.literal_inv
        obtain ⟨rfl, rfl, rfl⟩ := a_iz1.nil_inv
        obtain ⟨_, _, _, _, _, rfl, d_0, a_eq2, rfl⟩ := a_eq1.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := d_0.literal_inv
        obtain ⟨rfl, rfl, rfl⟩ := a_eq2.nil_inv
        obtain ⟨heq_iz, rfl⟩ := Builtin.assertEq_inv ap_eq
        obtain ⟨hv_iz, rfl⟩ := Lib.is_zero_spec ev_iz
        obtain rfl := matchPattern_wildcard_inv mt_eq
        obtain ⟨_, a_u, _⟩ := d_u.tuple_inv
        obtain ⟨_, rfl, _⟩ := a_u.nil_inv
        have hstrict_ne2 : x_strict ≠ .field 2 := by
          intro h2
          subst h2
          simp only [evalBinOp, sub_self, Except.ok.injEq] at op_sub
          subst op_sub
          simp only [↓reduceIte] at hv_iz
          exact one_ne_zero (Value.field.inj (hv_iz.symm.trans heq_iz))
        exact ⟨Heap.Extends.refl _, [], .inr ⟨haddr_in_asms, hstrict_ne2⟩,
          by simp [CondTopRecsClosed], by simp⟩
      · -- Arm `_`: walk `addr`
        rcases selectArm_cons_inv sel_m1 with ⟨mt_w, rfl⟩ | ⟨_, sel_m2⟩
        case inr => exact (selectArm_nil_inv sel_m2).elim
        obtain rfl := matchPattern_wildcard_inv mt_w
        -- `let next_strict = match strict { ... };`
        obtain ⟨v_ns, m_ns, bs_ns, c_ns, c_after_ns, d_ns, mt_ns, d_after_ns, rfl⟩ :=
          d_arm.letValue_inv
        have ext_ns : Heap.Extends h m_ns := d_ns.heap_extends
        obtain rfl := matchPattern_bind_inv mt_ns
        -- `let c = Ingress::load_verified_constant(addr);`
        obtain ⟨x_c, m_load, bs_load, c_load, c_after_load, d_load, mt_load, d_after_load, rfl⟩ :=
          d_after_ns.letValue_inv
        obtain ⟨_, m_largs, _, cs_load, a_load, ev_load, rfl⟩ := d_load.call_inv
        rw [instanceName_plain_some] at ev_load
        obtain ⟨_, _, m_l0, _, _, rfl, d_l0, a_l1, rfl⟩ := a_load.cons_inv
        obtain ⟨ll0, hm_l0, rfl⟩ := d_l0.var_inv; simp at ll0; subst ll0; subst m_l0
        obtain ⟨rfl, hm_l1, rfl⟩ := a_l1.nil_inv; subst m_largs
        obtain rfl := matchPattern_bind_inv mt_load
        have ha_ns : BaseSeams.addr m_ns x_addr addr :=
          ⟨aB, Bytes.repAddressRef_heapMono₂ addrTy ext_ns ha_ref, ha_ix⟩
        obtain ⟨ext_load, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
          Claim.load_verified_constant_de ha_ns ev_load
        -- `match c { Ixon::Constant::Mk(info, _, refs, _, _) => ... }`
        obtain ⟨v_c, m_c, bs_c, body_c, c_c, c_body, d_c, sel_c, d_body, rfl⟩ :=
          d_after_load.matchValue_inv
        obtain ⟨lc, hm_c, rfl⟩ := d_c.var_inv; simp at lc; subst lc; subst m_c
        rcases selectArm_cons_inv sel_c with ⟨mt_mk, rfl⟩ | ⟨_, sel_c1⟩
        case inr => exact (selectArm_nil_inv sel_c1).elim
        obtain ⟨vs_mk, hv_mk, -, ml_mk⟩ := matchPattern_construct_inv mt_mk
        obtain ⟨x_info, _, _, _, rfl, mt_info, ml_mk1, rfl⟩ := matchListWith_cons_inv ml_mk
        obtain rfl := matchPattern_bind_inv mt_info
        obtain ⟨x_w1, _, _, _, rfl, mt_w1, ml_mk2, rfl⟩ := matchListWith_cons_inv ml_mk1
        obtain rfl := matchPattern_wildcard_inv mt_w1
        obtain ⟨x_refs, _, _, _, rfl, mt_refs, ml_mk3, rfl⟩ := matchListWith_cons_inv ml_mk2
        obtain rfl := matchPattern_bind_inv mt_refs
        obtain ⟨x_w2, _, _, _, rfl, mt_w2, ml_mk4, rfl⟩ := matchListWith_cons_inv ml_mk3
        obtain rfl := matchPattern_wildcard_inv mt_w2
        obtain ⟨x_w3, _, _, _, rfl, mt_w3, ml_mk5, rfl⟩ := matchListWith_cons_inv ml_mk4
        obtain rfl := matchPattern_wildcard_inv mt_w3
        obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_mk5
        -- Extract `info` and `refs` from `hrep : Claim.RepConstant m_load c x_c`
        have hinfo_refs : Claim.RepConstantInfo m_load c.info x_info ∧
            RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem m_load
              c.refs.toList x_refs := by
          obtain ⟨infoVal, _, refsPtr, _, _, hv_rep, hinfo, _, hr_list, _, _⟩ := hrep
          have heq := hv_rep.symm.trans hv_mk
          injection heq with _ _ hargs
          simp only [List.cons.injEq, and_true] at hargs
          rw [hargs.1] at hinfo
          rw [hargs.2.2.1] at hr_list
          exact ⟨hinfo, hr_list⟩
        obtain ⟨hinfo, hr_list⟩ := hinfo_refs
        -- Body statement 1: `match info { Muts => ..., DPrj => ..., IPrj => ..., CPrj => ..., RPrj => ..., _ => ... };`
        obtain ⟨_, m_seg, _, c_seg, c_after_seg, d_seg, mt_seg, d_after_seg, rfl⟩ :=
          d_body.letValue_inv
        obtain rfl := matchPattern_wildcard_inv mt_seg
        -- Body statement 2: `assert_safe_record_refs_under(rc, addr, c, asm);`
        obtain ⟨v_guard, m_guard, _, c_guard, c_after_guard, d_guard, mt_guard, d_after_guard, rfl⟩ :=
          d_after_seg.letValue_inv
        obtain ⟨_, m_gargs, _, cs_guard, a_guard, ev_guard, rfl⟩ := d_guard.call_inv
        rw [instanceName_plain_some] at ev_guard
        obtain ⟨_, _, m_g0, _, _, rfl, d_g0, a_g1, rfl⟩ := a_guard.cons_inv
        obtain ⟨lg0, hm_g0, rfl⟩ := d_g0.var_inv; simp at lg0; subst lg0; subst m_g0
        obtain ⟨_, _, m_g1, _, _, rfl, d_g1, a_g2, rfl⟩ := a_g1.cons_inv
        obtain ⟨lg1, hm_g1, rfl⟩ := d_g1.var_inv; simp at lg1; subst lg1; subst m_g1
        obtain ⟨_, _, m_g2, _, _, rfl, d_g2, a_g3, rfl⟩ := a_g2.cons_inv
        obtain ⟨lg2, hm_g2, rfl⟩ := d_g2.var_inv; simp at lg2; subst lg2; subst m_g2
        obtain ⟨_, _, m_g3, _, _, rfl, d_g3, a_g4, rfl⟩ := a_g3.cons_inv
        obtain ⟨lg3, hm_g3, rfl⟩ := d_g3.var_inv; simp at lg3; subst lg3; subst m_g3
        obtain ⟨rfl, hm_g4, rfl⟩ := a_g4.nil_inv; subst m_gargs
        obtain rfl := matchPattern_wildcard_inv mt_guard
        -- Body statement 3: `assert_quot_record_refs(rc, addr, c);`
        obtain ⟨v_quot, m_quot, _, c_quot, c_after_quot, d_quot, mt_quot, d_after_quot, rfl⟩ :=
          d_after_guard.letValue_inv
        obtain ⟨_, m_qargs, _, cs_quot, a_quot, ev_quot, rfl⟩ := d_quot.call_inv
        rw [instanceName_plain_some] at ev_quot
        obtain ⟨_, _, m_q0, _, _, rfl, d_q0, a_q1, rfl⟩ := a_quot.cons_inv
        obtain ⟨lq0, hm_q0, rfl⟩ := d_q0.var_inv; simp at lq0; subst lq0; subst m_q0
        obtain ⟨_, _, m_q1, _, _, rfl, d_q1, a_q2, rfl⟩ := a_q1.cons_inv
        obtain ⟨lq1, hm_q1, rfl⟩ := d_q1.var_inv; simp at lq1; subst lq1; subst m_q1
        obtain ⟨_, _, m_q2, _, _, rfl, d_q2, a_q3, rfl⟩ := a_q2.cons_inv
        obtain ⟨lq2, hm_q2, rfl⟩ := d_q2.var_inv; simp at lq2; subst lq2; subst m_q2
        obtain ⟨rfl, hm_q3, rfl⟩ := a_q3.nil_inv; subst m_qargs
        obtain rfl := matchPattern_wildcard_inv mt_quot
        -- Body statement 4: `env_walk_refs(rc, refs, const_idxs_of(c), 0, owned, asm, next_strict)`
        obtain ⟨_, m_eargs, _, cs_ewr, a_ewr, ev_ewr, rfl⟩ := d_after_quot.call_inv
        rw [instanceName_plain_some] at ev_ewr
        obtain ⟨_, _, m_e0, _, _, rfl, d_e0, a_e1, rfl⟩ := a_ewr.cons_inv
        obtain ⟨le0, hm_e0, rfl⟩ := d_e0.var_inv; simp at le0; subst le0; subst m_e0
        obtain ⟨_, _, m_e1, _, _, rfl, d_e1, a_e2, rfl⟩ := a_e1.cons_inv
        obtain ⟨le1, hm_e1, rfl⟩ := d_e1.var_inv; simp at le1; subst le1; subst m_e1
        obtain ⟨x_idxs, _, m_idx, _, _, rfl, d_e2, a_e3, rfl⟩ := a_e2.cons_inv
        obtain ⟨_, m_iargs, _, cs_idx, a_idx, ev_idx, rfl⟩ := d_e2.call_inv
        rw [instanceName_plain_some] at ev_idx
        obtain ⟨_, _, m_i0, _, _, rfl, d_i0, a_i1, rfl⟩ := a_idx.cons_inv
        obtain ⟨li0, hm_i0, rfl⟩ := d_i0.var_inv; simp at li0; subst li0; subst m_i0
        obtain ⟨rfl, hm_i1, rfl⟩ := a_i1.nil_inv; subst m_iargs
        obtain ⟨_, _, m_e3, _, _, rfl, d_e3, a_e4, rfl⟩ := a_e3.cons_inv
        obtain ⟨rfl, hm_e3, rfl⟩ := d_e3.literal_inv; subst m_e3
        obtain ⟨_, _, m_e4, _, _, rfl, d_e4, a_e5, rfl⟩ := a_e4.cons_inv
        obtain ⟨le4, hm_e4, rfl⟩ := d_e4.var_inv; simp at le4; subst le4; subst m_e4
        obtain ⟨_, _, m_e5, _, _, rfl, d_e5, a_e6, rfl⟩ := a_e5.cons_inv
        obtain ⟨le5, hm_e5, rfl⟩ := d_e5.var_inv; simp at le5; subst le5; subst m_e5
        obtain ⟨_, _, m_e6, _, _, rfl, d_e6, a_e7, rfl⟩ := a_e6.cons_inv
        obtain ⟨le6, hm_e6, rfl⟩ := d_e6.var_inv; simp at le6; subst le6; subst m_e6
        obtain ⟨rfl, hm_e7, rfl⟩ := a_e7.nil_inv; subst m_eargs
        -- Analyze `d_seg : match info { Muts | DPrj | IPrj | CPrj | RPrj | _ }`
        have hpre : Heap.Extends h m_load := ext_ns.trans ext_load
        have hrc_load : Claim.RCLimRep t bAddr lim m_load x_rc := hrc.mono hpre
        have ha_load : BaseSeams.addr m_load x_addr addr := BaseSeams.addr_mono ext_load ha_ns
        have hasm_load : Claim.RepAddrSet m_load asms x_asm := hasm.mono hpre
        have hseg : Heap.Extends m_load m_seg ∧
            ((∃ ms, c.info = .muts ms ∧
                ∀ (k : Nat), k < ms.size → Claim.MemberCheckedLimAt calls bAddr t addr ms k lim) ∨
              Claim.CheckedLimAt calls bAddr t addr lim) ∧
            ∃ recs_blk : List (CondTopRec calls bAddr t lim asms),
              CondTopRecsClosed recs_blk ∧
              (∀ r ∈ recs_blk, r.depth < calls.length) ∧
              (Claim.IsProjRec c →
                Ix.Cert.ownerOf addr c ∈ recs_blk.map (·.addr) ∨
                  Ix.Cert.ownerOf addr c ∈ asms) := by
          obtain ⟨v_i, m_i, bs_i, body_i, c_i, c_ibody, d_i, sel_i, d_ibody, hseg_cs⟩ :=
            d_seg.matchValue_inv
          obtain ⟨li, hm_i, rfl⟩ := d_i.var_inv; simp at li; subst li; subst m_i
          have hsub_ibody : ∀ cl ∈ c_ibody, cl ∈ calls := fun cl hcl => by
            rw [hcalls]; rw [hseg_cs]; simp [hcl]
          rcases selectArm_cons_inv sel_i with ⟨mt_muts, rfl⟩ | ⟨nm_muts, sel_i1⟩
          · -- Muts
            obtain ⟨vs_m, hv_m, -, ml_m⟩ := matchPattern_construct_inv mt_muts
            obtain ⟨x_members, _, _, _, rfl, mt_mem, ml_m1, rfl⟩ := matchListWith_cons_inv ml_m
            obtain rfl := matchPattern_bind_inv mt_mem
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_m1
            obtain ⟨_, _, _, cs_cm, a_cm, ev_cm, hcm_cs⟩ := d_ibody.call_inv
            rw [instanceName_plain_some] at ev_cm
            obtain ⟨_, _, _, _, _, rfl, d_cm0, a_cm1, rfl⟩ := a_cm.cons_inv
            obtain ⟨lcm0, rfl, rfl⟩ := d_cm0.var_inv; simp at lcm0; subst lcm0
            obtain ⟨_, _, _, _, _, rfl, d_cm1, a_cm2, rfl⟩ := a_cm1.cons_inv
            obtain ⟨lcm1, rfl, rfl⟩ := d_cm1.var_inv; simp at lcm1; subst lcm1
            obtain ⟨_, _, _, _, _, rfl, d_cm2, a_cm3, rfl⟩ := a_cm2.cons_inv
            obtain ⟨lcm2, rfl, rfl⟩ := d_cm2.var_inv; simp at lcm2; subst lcm2
            obtain ⟨_, _, _, _, _, rfl, d_cm3, a_cm4, rfl⟩ := a_cm3.cons_inv
            obtain ⟨lcm3, rfl, rfl⟩ := d_cm3.var_inv; simp at lcm3; subst lcm3
            obtain ⟨_, _, _, _, _, rfl, d_cm4, a_cm5, rfl⟩ := a_cm4.cons_inv
            obtain ⟨rfl, rfl, rfl⟩ := d_cm4.literal_inv
            obtain ⟨rfl, rfl, rfl⟩ := a_cm5.nil_inv
            rw [hv_m] at hinfo
            cases hc_i : c.info <;> rw [hc_i] at hinfo
            case muts ms =>
              obtain ⟨mv, hmv_eq, hms_rep⟩ := hinfo
              injection hmv_eq with _ _ hargs_m
              simp only [List.cons.injEq, and_true] at hargs_m
              rw [← hargs_m] at hms_rep
              obtain ⟨ext_muts, hchk_muts⟩ :=
                Claim.check_muts_all_lim_spec hrc_load ha_load
                  (cond_membersRep_of_repMutConstList hms_rep) ev_cm
              have hsub_cm : ∀ cl ∈ cs_cm, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hcm_cs]; simp [hcl])
              have hnp : ¬ Claim.IsProjRec c := by simp [Claim.IsProjRec, hc_i]
              exact ⟨ext_muts,
                .inl ⟨ms, rfl, fun k hk => (hchk_muts k hk).mono hsub_cm⟩,
                [], by simp [CondTopRecsClosed], by simp, fun hp => absurd hp hnp⟩
            all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
          rcases selectArm_cons_inv sel_i1 with ⟨mt_dprj, rfl⟩ | ⟨nm_dprj, sel_i2⟩
          · -- DPrj
            obtain ⟨vs_p, hv_p, -, ml_p⟩ := matchPattern_construct_inv mt_dprj
            obtain ⟨x_dprj, _, _, _, rfl, mt_p1, ml_p1, rfl⟩ := matchListWith_cons_inv ml_p
            obtain rfl := matchPattern_bind_inv mt_p1
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_p1
            obtain ⟨_, _, bs_dp, body_dp, _, c_dp, d_dp, sel_dp, d_dpb, hdp_cs⟩ :=
              d_ibody.matchValue_inv
            obtain ⟨ldp, rfl, rfl⟩ := d_dp.var_inv; simp at ldp; subst ldp
            rcases selectArm_cons_inv sel_dp with ⟨mt_dmk, rfl⟩ | ⟨_, sel_dp1⟩
            case inr => exact (selectArm_nil_inv sel_dp1).elim
            obtain ⟨vs_dmk, hv_dmk, -, ml_dmk⟩ := matchPattern_construct_inv mt_dmk
            obtain ⟨_, _, _, _, rfl, mt_dw, ml_dmk1, rfl⟩ := matchListWith_cons_inv ml_dmk
            obtain rfl := matchPattern_wildcard_inv mt_dw
            obtain ⟨x_blk, _, _, _, rfl, mt_dblk, ml_dmk2, rfl⟩ := matchListWith_cons_inv ml_dmk1
            obtain rfl := matchPattern_bind_inv mt_dblk
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_dmk2
            obtain ⟨_, m_rc, _, c_rc, c_ew, d_rc, mt_rc, d_ew, hseq_cs⟩ := d_dpb.letValue_inv
            obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, hrc_cs⟩ := d_rc.call_inv
            rw [instanceName_plain_some] at ev_rc
            obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
            obtain ⟨lrc0, rfl, rfl⟩ := d_rc0.var_inv; simp at lrc0; subst lrc0
            obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
            obtain ⟨lrc1, rfl, rfl⟩ := d_rc1.var_inv; simp at lrc1; subst lrc1
            obtain ⟨rfl, rfl, rfl⟩ := a_rc2.nil_inv
            obtain rfl := matchPattern_wildcard_inv mt_rc
            obtain ⟨_, _, _, cs_blk, a_blk, ev_blk, hblk_cs⟩ := d_ew.call_inv
            rw [instanceName_plain_some] at ev_blk
            obtain ⟨_, _, _, _, _, rfl, d_b0, a_b1, rfl⟩ := a_blk.cons_inv
            obtain ⟨lb0, rfl, rfl⟩ := d_b0.var_inv; simp at lb0; subst lb0
            obtain ⟨_, _, _, _, _, rfl, d_b1, a_b2, rfl⟩ := a_b1.cons_inv
            obtain ⟨lb1, rfl, rfl⟩ := d_b1.var_inv; simp at lb1; subst lb1
            obtain ⟨_, _, _, _, _, rfl, d_b2, a_b3, rfl⟩ := a_b2.cons_inv
            obtain ⟨lb2, rfl, rfl⟩ := d_b2.var_inv; simp at lb2; subst lb2
            obtain ⟨_, _, _, _, _, rfl, d_b3, a_b4, rfl⟩ := a_b3.cons_inv
            obtain ⟨lb3, rfl, rfl⟩ := d_b3.var_inv; simp at lb3; subst lb3
            obtain ⟨_, _, _, _, _, rfl, d_b4, a_b5, rfl⟩ := a_b4.cons_inv
            obtain ⟨lb4, rfl, rfl⟩ := d_b4.var_inv; simp at lb4; subst lb4
            obtain ⟨rfl, rfl, rfl⟩ := a_b5.nil_inv
            rw [hv_p] at hinfo
            cases hc_i : c.info <;> rw [hc_i] at hinfo
            case dPrj p =>
              obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
              injection hpv_eq with _ _ h1
              simp only [List.cons.injEq, and_true] at h1
              have heq_dp := hpv.symm.trans (h1.symm.trans hv_dmk)
              injection heq_dp with _ _ hpargs
              simp only [List.cons.injEq, and_true] at hpargs
              rw [hpargs.2] at hblk_addr
              obtain ⟨ext_rc, hchk⟩ := Claim.run_check_lim_spec hrc_load ha_load ev_rc
              have hlt_calls : cs_blk.length < calls.length := by
                rw [hcalls]
                rw [hseg_cs, hdp_cs, hseq_cs, hblk_cs]
                simp only [List.length_cons, List.length_append]
                omega
              have hlt_sub : cs_blk.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
              obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hdep_b⟩ :=
                (ih cs_blk.length hlt_sub).1 (Nat.le_refl _) (hrc_load.mono ext_rc)
                  (BaseSeams.addr_mono ext_rc hblk_addr) (hasm_load.mono ext_rc) ev_blk
              have hsub_rc : ∀ cl ∈ cs_rc, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hrc_cs]; simp [hcl])
              have hsub_b : ∀ cl ∈ cs_blk, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hblk_cs]; simp [hcl])
              refine ⟨ext_rc.trans ext_blk, .inr (hchk.mono hsub_rc),
                recs_b.map (CondTopRec.mono hsub_b), hcl_b.mono hsub_b,
                condTopRec_mono_depth_lt hsub_b hdep_b hlt_calls, fun _ => ?_⟩
              rw [map_addr_condTopRec_mono]
              simpa [Ix.Cert.ownerOf, hc_i] using hmem_b.imp id (·.1)
            all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
          rcases selectArm_cons_inv sel_i2 with ⟨mt_iprj, rfl⟩ | ⟨nm_iprj, sel_i3⟩
          · -- IPrj
            obtain ⟨vs_p, hv_p, -, ml_p⟩ := matchPattern_construct_inv mt_iprj
            obtain ⟨x_iprj, _, _, _, rfl, mt_p1, ml_p1, rfl⟩ := matchListWith_cons_inv ml_p
            obtain rfl := matchPattern_bind_inv mt_p1
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_p1
            obtain ⟨_, _, bs_dp, body_dp, _, c_dp, d_dp, sel_dp, d_dpb, hdp_cs⟩ :=
              d_ibody.matchValue_inv
            obtain ⟨ldp, rfl, rfl⟩ := d_dp.var_inv; simp at ldp; subst ldp
            rcases selectArm_cons_inv sel_dp with ⟨mt_dmk, rfl⟩ | ⟨_, sel_dp1⟩
            case inr => exact (selectArm_nil_inv sel_dp1).elim
            obtain ⟨vs_dmk, hv_dmk, -, ml_dmk⟩ := matchPattern_construct_inv mt_dmk
            obtain ⟨_, _, _, _, rfl, mt_dw, ml_dmk1, rfl⟩ := matchListWith_cons_inv ml_dmk
            obtain rfl := matchPattern_wildcard_inv mt_dw
            obtain ⟨x_blk, _, _, _, rfl, mt_dblk, ml_dmk2, rfl⟩ := matchListWith_cons_inv ml_dmk1
            obtain rfl := matchPattern_bind_inv mt_dblk
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_dmk2
            obtain ⟨_, m_rc, _, c_rc, c_ew, d_rc, mt_rc, d_ew, hseq_cs⟩ := d_dpb.letValue_inv
            obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, hrc_cs⟩ := d_rc.call_inv
            rw [instanceName_plain_some] at ev_rc
            obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
            obtain ⟨lrc0, rfl, rfl⟩ := d_rc0.var_inv; simp at lrc0; subst lrc0
            obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
            obtain ⟨lrc1, rfl, rfl⟩ := d_rc1.var_inv; simp at lrc1; subst lrc1
            obtain ⟨rfl, rfl, rfl⟩ := a_rc2.nil_inv
            obtain rfl := matchPattern_wildcard_inv mt_rc
            obtain ⟨_, _, _, cs_blk, a_blk, ev_blk, hblk_cs⟩ := d_ew.call_inv
            rw [instanceName_plain_some] at ev_blk
            obtain ⟨_, _, _, _, _, rfl, d_b0, a_b1, rfl⟩ := a_blk.cons_inv
            obtain ⟨lb0, rfl, rfl⟩ := d_b0.var_inv; simp at lb0; subst lb0
            obtain ⟨_, _, _, _, _, rfl, d_b1, a_b2, rfl⟩ := a_b1.cons_inv
            obtain ⟨lb1, rfl, rfl⟩ := d_b1.var_inv; simp at lb1; subst lb1
            obtain ⟨_, _, _, _, _, rfl, d_b2, a_b3, rfl⟩ := a_b2.cons_inv
            obtain ⟨lb2, rfl, rfl⟩ := d_b2.var_inv; simp at lb2; subst lb2
            obtain ⟨_, _, _, _, _, rfl, d_b3, a_b4, rfl⟩ := a_b3.cons_inv
            obtain ⟨lb3, rfl, rfl⟩ := d_b3.var_inv; simp at lb3; subst lb3
            obtain ⟨_, _, _, _, _, rfl, d_b4, a_b5, rfl⟩ := a_b4.cons_inv
            obtain ⟨lb4, rfl, rfl⟩ := d_b4.var_inv; simp at lb4; subst lb4
            obtain ⟨rfl, rfl, rfl⟩ := a_b5.nil_inv
            rw [hv_p] at hinfo
            cases hc_i : c.info <;> rw [hc_i] at hinfo
            case iPrj p =>
              obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
              injection hpv_eq with _ _ h1
              simp only [List.cons.injEq, and_true] at h1
              have heq_dp := hpv.symm.trans (h1.symm.trans hv_dmk)
              injection heq_dp with _ _ hpargs
              simp only [List.cons.injEq, and_true] at hpargs
              rw [hpargs.2] at hblk_addr
              obtain ⟨ext_rc, hchk⟩ := Claim.run_check_lim_spec hrc_load ha_load ev_rc
              have hlt_calls : cs_blk.length < calls.length := by
                rw [hcalls]
                rw [hseg_cs, hdp_cs, hseq_cs, hblk_cs]
                simp only [List.length_cons, List.length_append]
                omega
              have hlt_sub : cs_blk.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
              obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hdep_b⟩ :=
                (ih cs_blk.length hlt_sub).1 (Nat.le_refl _) (hrc_load.mono ext_rc)
                  (BaseSeams.addr_mono ext_rc hblk_addr) (hasm_load.mono ext_rc) ev_blk
              have hsub_rc : ∀ cl ∈ cs_rc, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hrc_cs]; simp [hcl])
              have hsub_b : ∀ cl ∈ cs_blk, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hblk_cs]; simp [hcl])
              refine ⟨ext_rc.trans ext_blk, .inr (hchk.mono hsub_rc),
                recs_b.map (CondTopRec.mono hsub_b), hcl_b.mono hsub_b,
                condTopRec_mono_depth_lt hsub_b hdep_b hlt_calls, fun _ => ?_⟩
              rw [map_addr_condTopRec_mono]
              simpa [Ix.Cert.ownerOf, hc_i] using hmem_b.imp id (·.1)
            all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
          rcases selectArm_cons_inv sel_i3 with ⟨mt_cprj, rfl⟩ | ⟨nm_cprj, sel_i4⟩
          · -- CPrj
            obtain ⟨vs_p, hv_p, -, ml_p⟩ := matchPattern_construct_inv mt_cprj
            obtain ⟨x_cprj, _, _, _, rfl, mt_p1, ml_p1, rfl⟩ := matchListWith_cons_inv ml_p
            obtain rfl := matchPattern_bind_inv mt_p1
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_p1
            obtain ⟨_, _, bs_dp, body_dp, _, c_dp, d_dp, sel_dp, d_dpb, hdp_cs⟩ :=
              d_ibody.matchValue_inv
            obtain ⟨ldp, rfl, rfl⟩ := d_dp.var_inv; simp at ldp; subst ldp
            rcases selectArm_cons_inv sel_dp with ⟨mt_dmk, rfl⟩ | ⟨_, sel_dp1⟩
            case inr => exact (selectArm_nil_inv sel_dp1).elim
            obtain ⟨vs_dmk, hv_dmk, -, ml_dmk⟩ := matchPattern_construct_inv mt_dmk
            obtain ⟨_, _, _, _, rfl, mt_dw1, ml_dmk1, rfl⟩ := matchListWith_cons_inv ml_dmk
            obtain rfl := matchPattern_wildcard_inv mt_dw1
            obtain ⟨_, _, _, _, rfl, mt_dw2, ml_dmk2, rfl⟩ := matchListWith_cons_inv ml_dmk1
            obtain rfl := matchPattern_wildcard_inv mt_dw2
            obtain ⟨x_blk, _, _, _, rfl, mt_dblk, ml_dmk3, rfl⟩ := matchListWith_cons_inv ml_dmk2
            obtain rfl := matchPattern_bind_inv mt_dblk
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_dmk3
            obtain ⟨_, m_rc, _, c_rc, c_ew, d_rc, mt_rc, d_ew, hseq_cs⟩ := d_dpb.letValue_inv
            obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, hrc_cs⟩ := d_rc.call_inv
            rw [instanceName_plain_some] at ev_rc
            obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
            obtain ⟨lrc0, rfl, rfl⟩ := d_rc0.var_inv; simp at lrc0; subst lrc0
            obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
            obtain ⟨lrc1, rfl, rfl⟩ := d_rc1.var_inv; simp at lrc1; subst lrc1
            obtain ⟨rfl, rfl, rfl⟩ := a_rc2.nil_inv
            obtain rfl := matchPattern_wildcard_inv mt_rc
            obtain ⟨_, _, _, cs_blk, a_blk, ev_blk, hblk_cs⟩ := d_ew.call_inv
            rw [instanceName_plain_some] at ev_blk
            obtain ⟨_, _, _, _, _, rfl, d_b0, a_b1, rfl⟩ := a_blk.cons_inv
            obtain ⟨lb0, rfl, rfl⟩ := d_b0.var_inv; simp at lb0; subst lb0
            obtain ⟨_, _, _, _, _, rfl, d_b1, a_b2, rfl⟩ := a_b1.cons_inv
            obtain ⟨lb1, rfl, rfl⟩ := d_b1.var_inv; simp at lb1; subst lb1
            obtain ⟨_, _, _, _, _, rfl, d_b2, a_b3, rfl⟩ := a_b2.cons_inv
            obtain ⟨lb2, rfl, rfl⟩ := d_b2.var_inv; simp at lb2; subst lb2
            obtain ⟨_, _, _, _, _, rfl, d_b3, a_b4, rfl⟩ := a_b3.cons_inv
            obtain ⟨lb3, rfl, rfl⟩ := d_b3.var_inv; simp at lb3; subst lb3
            obtain ⟨_, _, _, _, _, rfl, d_b4, a_b5, rfl⟩ := a_b4.cons_inv
            obtain ⟨lb4, rfl, rfl⟩ := d_b4.var_inv; simp at lb4; subst lb4
            obtain ⟨rfl, rfl, rfl⟩ := a_b5.nil_inv
            rw [hv_p] at hinfo
            cases hc_i : c.info <;> rw [hc_i] at hinfo
            case cPrj p =>
              obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
              injection hpv_eq with _ _ h1
              simp only [List.cons.injEq, and_true] at h1
              have heq_dp := hpv.symm.trans (h1.symm.trans hv_dmk)
              injection heq_dp with _ _ hpargs
              simp only [List.cons.injEq, and_true] at hpargs
              rw [hpargs.2.2] at hblk_addr
              obtain ⟨ext_rc, hchk⟩ := Claim.run_check_lim_spec hrc_load ha_load ev_rc
              have hlt_calls : cs_blk.length < calls.length := by
                rw [hcalls]
                rw [hseg_cs, hdp_cs, hseq_cs, hblk_cs]
                simp only [List.length_cons, List.length_append]
                omega
              have hlt_sub : cs_blk.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
              obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hdep_b⟩ :=
                (ih cs_blk.length hlt_sub).1 (Nat.le_refl _) (hrc_load.mono ext_rc)
                  (BaseSeams.addr_mono ext_rc hblk_addr) (hasm_load.mono ext_rc) ev_blk
              have hsub_rc : ∀ cl ∈ cs_rc, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hrc_cs]; simp [hcl])
              have hsub_b : ∀ cl ∈ cs_blk, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hblk_cs]; simp [hcl])
              refine ⟨ext_rc.trans ext_blk, .inr (hchk.mono hsub_rc),
                recs_b.map (CondTopRec.mono hsub_b), hcl_b.mono hsub_b,
                condTopRec_mono_depth_lt hsub_b hdep_b hlt_calls, fun _ => ?_⟩
              rw [map_addr_condTopRec_mono]
              simpa [Ix.Cert.ownerOf, hc_i] using hmem_b.imp id (·.1)
            all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
          rcases selectArm_cons_inv sel_i4 with ⟨mt_rprj, rfl⟩ | ⟨nm_rprj, sel_i5⟩
          · -- RPrj
            obtain ⟨vs_p, hv_p, -, ml_p⟩ := matchPattern_construct_inv mt_rprj
            obtain ⟨x_rprj, _, _, _, rfl, mt_p1, ml_p1, rfl⟩ := matchListWith_cons_inv ml_p
            obtain rfl := matchPattern_bind_inv mt_p1
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_p1
            obtain ⟨_, _, bs_dp, body_dp, _, c_dp, d_dp, sel_dp, d_dpb, hdp_cs⟩ :=
              d_ibody.matchValue_inv
            obtain ⟨ldp, rfl, rfl⟩ := d_dp.var_inv; simp at ldp; subst ldp
            rcases selectArm_cons_inv sel_dp with ⟨mt_dmk, rfl⟩ | ⟨_, sel_dp1⟩
            case inr => exact (selectArm_nil_inv sel_dp1).elim
            obtain ⟨vs_dmk, hv_dmk, -, ml_dmk⟩ := matchPattern_construct_inv mt_dmk
            obtain ⟨_, _, _, _, rfl, mt_dw, ml_dmk1, rfl⟩ := matchListWith_cons_inv ml_dmk
            obtain rfl := matchPattern_wildcard_inv mt_dw
            obtain ⟨x_blk, _, _, _, rfl, mt_dblk, ml_dmk2, rfl⟩ := matchListWith_cons_inv ml_dmk1
            obtain rfl := matchPattern_bind_inv mt_dblk
            obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_dmk2
            obtain ⟨_, m_rc, _, c_rc, c_ew, d_rc, mt_rc, d_ew, hseq_cs⟩ := d_dpb.letValue_inv
            obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, hrc_cs⟩ := d_rc.call_inv
            rw [instanceName_plain_some] at ev_rc
            obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
            obtain ⟨lrc0, rfl, rfl⟩ := d_rc0.var_inv; simp at lrc0; subst lrc0
            obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
            obtain ⟨lrc1, rfl, rfl⟩ := d_rc1.var_inv; simp at lrc1; subst lrc1
            obtain ⟨rfl, rfl, rfl⟩ := a_rc2.nil_inv
            obtain rfl := matchPattern_wildcard_inv mt_rc
            obtain ⟨_, _, _, cs_blk, a_blk, ev_blk, hblk_cs⟩ := d_ew.call_inv
            rw [instanceName_plain_some] at ev_blk
            obtain ⟨_, _, _, _, _, rfl, d_b0, a_b1, rfl⟩ := a_blk.cons_inv
            obtain ⟨lb0, rfl, rfl⟩ := d_b0.var_inv; simp at lb0; subst lb0
            obtain ⟨_, _, _, _, _, rfl, d_b1, a_b2, rfl⟩ := a_b1.cons_inv
            obtain ⟨lb1, rfl, rfl⟩ := d_b1.var_inv; simp at lb1; subst lb1
            obtain ⟨_, _, _, _, _, rfl, d_b2, a_b3, rfl⟩ := a_b2.cons_inv
            obtain ⟨lb2, rfl, rfl⟩ := d_b2.var_inv; simp at lb2; subst lb2
            obtain ⟨_, _, _, _, _, rfl, d_b3, a_b4, rfl⟩ := a_b3.cons_inv
            obtain ⟨lb3, rfl, rfl⟩ := d_b3.var_inv; simp at lb3; subst lb3
            obtain ⟨_, _, _, _, _, rfl, d_b4, a_b5, rfl⟩ := a_b4.cons_inv
            obtain ⟨lb4, rfl, rfl⟩ := d_b4.var_inv; simp at lb4; subst lb4
            obtain ⟨rfl, rfl, rfl⟩ := a_b5.nil_inv
            rw [hv_p] at hinfo
            cases hc_i : c.info <;> rw [hc_i] at hinfo
            case rPrj p =>
              obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
              injection hpv_eq with _ _ h1
              simp only [List.cons.injEq, and_true] at h1
              have heq_dp := hpv.symm.trans (h1.symm.trans hv_dmk)
              injection heq_dp with _ _ hpargs
              simp only [List.cons.injEq, and_true] at hpargs
              rw [hpargs.2] at hblk_addr
              obtain ⟨ext_rc, hchk⟩ := Claim.run_check_lim_spec hrc_load ha_load ev_rc
              have hlt_calls : cs_blk.length < calls.length := by
                rw [hcalls]
                rw [hseg_cs, hdp_cs, hseq_cs, hblk_cs]
                simp only [List.length_cons, List.length_append]
                omega
              have hlt_sub : cs_blk.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
              obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hdep_b⟩ :=
                (ih cs_blk.length hlt_sub).1 (Nat.le_refl _) (hrc_load.mono ext_rc)
                  (BaseSeams.addr_mono ext_rc hblk_addr) (hasm_load.mono ext_rc) ev_blk
              have hsub_rc : ∀ cl ∈ cs_rc, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hrc_cs]; simp [hcl])
              have hsub_b : ∀ cl ∈ cs_blk, cl ∈ calls := fun cl hcl =>
                hsub_ibody cl (by rw [hdp_cs, hseq_cs, hblk_cs]; simp [hcl])
              refine ⟨ext_rc.trans ext_blk, .inr (hchk.mono hsub_rc),
                recs_b.map (CondTopRec.mono hsub_b), hcl_b.mono hsub_b,
                condTopRec_mono_depth_lt hsub_b hdep_b hlt_calls, fun _ => ?_⟩
              rw [map_addr_condTopRec_mono]
              simpa [Ix.Cert.ownerOf, hc_i] using hmem_b.imp id (·.1)
            all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
          rcases selectArm_cons_inv sel_i5 with ⟨mt_iw, rfl⟩ | ⟨_, sel_i6⟩
          case inr => exact (selectArm_nil_inv sel_i6).elim
          · -- `_ => run_check(rc, addr)`
            obtain rfl := matchPattern_wildcard_inv mt_iw
            obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, hrc_cs⟩ := d_ibody.call_inv
            rw [instanceName_plain_some] at ev_rc
            obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
            obtain ⟨lrc0, rfl, rfl⟩ := d_rc0.var_inv; simp at lrc0; subst lrc0
            obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
            obtain ⟨lrc1, rfl, rfl⟩ := d_rc1.var_inv; simp at lrc1; subst lrc1
            obtain ⟨rfl, rfl, rfl⟩ := a_rc2.nil_inv
            obtain ⟨ext_rc, hchk⟩ := Claim.run_check_lim_spec hrc_load ha_load ev_rc
            have hnp : ¬ Claim.IsProjRec c := by
              intro hp
              have hneD := matchPattern_construct_none (by trivial) nm_dprj
              have hneI := matchPattern_construct_none (by trivial) nm_iprj
              have hneC := matchPattern_construct_none (by trivial) nm_cprj
              have hneR := matchPattern_construct_none (by trivial) nm_rprj
              rw [constructorName_named, instanceName_plain_some] at hneD hneI hneC hneR
              rcases hp with ⟨p, hc_i⟩ | ⟨p, hc_i⟩ | ⟨p, hc_i⟩ | ⟨p, hc_i⟩ <;>
                rw [hc_i] at hinfo
              · obtain ⟨pv, hv', _⟩ := hinfo; exact absurd hv' (hneD [pv] rfl)
              · obtain ⟨pv, hv', _⟩ := hinfo; exact absurd hv' (hneI [pv] rfl)
              · obtain ⟨pv, hv', _⟩ := hinfo; exact absurd hv' (hneC [pv] rfl)
              · obtain ⟨pv, hv', _⟩ := hinfo; exact absurd hv' (hneR [pv] rfl)
            have hsub_rc : ∀ cl ∈ cs_rc, cl ∈ calls := fun cl hcl =>
              hsub_ibody cl (by rw [hrc_cs]; simp [hcl])
            exact ⟨ext_rc, .inr (hchk.mono hsub_rc), [],
              by simp [CondTopRecsClosed], by simp, fun hp => absurd hp hnp⟩
        obtain ⟨ext_seg, hchk_self, recs_blk, hcl_blk, hdep_blk, hown_blk⟩ := hseg
        have ext_guard : Heap.Extends m_seg m_quot :=
          ev_guard.heap_extends.trans ev_quot.heap_extends
        obtain ⟨ext_idx, hidxs⟩ :=
          Claim.const_idxs_of_spec (hrep.mono (ext_seg.trans ext_guard)) ev_idx
        have ext_to_ewr : Heap.Extends m_load m_idx := ext_seg.trans (ext_guard.trans ext_idx)
        have hrefs_rep :
            RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem m_idx
              c.refs.toList x_refs :=
          repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext_to_ewr hr_list
        have hlt_r_calls : cs_ewr.length < calls.length := by
          rw [hcalls]
          simp only [List.length_cons, List.length_append]
          omega
        have hlt_walk : cs_ewr.length < fuel := Nat.lt_of_lt_of_le hlt_r_calls hfuel
        have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
          rw [Nat.zero_add, Array.length_toList]
          exact refs_small_of_decoded_cond hsz hdeExact
        obtain ⟨ext_walk, recs_r, hmem_r, hcl_r, hdep_r⟩ :=
          (ih cs_ewr.length hlt_walk).2 (i := 0) (Nat.le_refl _) hrefs_bound
            (hrc_load.mono ext_to_ewr) hrefs_rep hidxs (hasm_load.mono ext_to_ewr) ev_ewr
        have hsub_r : ∀ cl ∈ cs_ewr, cl ∈ calls := fun cl hcl => by
          rw [hcalls]; simp [hcl]
        have hdep_r_lt : ∀ r ∈ recs_r.map (CondTopRec.mono hsub_r), r.depth < calls.length :=
          condTopRec_mono_depth_lt hsub_r hdep_r hlt_r_calls
        let r₀ : CondTopRec calls bAddr t lim asms := {
          addr := addr
          rawBytes := rawBytes
          c := c
          depth := calls.length
          hsz := hsz
          hhashed := Core.hashed_mono (fun cl hcl => by rw [hcalls]; simp [hcl]) hh_load
          hblake := hblk
          hde := hde
          hdeExact := hdeExact
          hchecked := hchk_self
          hguard := ⟨m_seg, m_guard, x_rc, x_addr, x_c, x_asm, v_guard, cs_guard,
            hrc_load.mono ext_seg, BaseSeams.addr_mono ext_seg ha_load, hrep.mono ext_seg,
            hasm_load.mono ext_seg, ev_guard,
            fun cl hcl => by rw [hcalls]; simp [hcl]⟩
          hquot := ⟨m_guard, m_quot, x_rc, x_addr, x_c, v_quot, cs_quot,
            hrc_load.mono (ext_seg.trans ev_guard.heap_extends),
            BaseSeams.addr_mono (ext_seg.trans ev_guard.heap_extends) ha_load,
            hrep.mono (ext_seg.trans ev_guard.heap_extends), ev_quot,
            fun cl hcl => by rw [hcalls]; simp [hcl]⟩
        }
        let recs_tail := recs_blk ++ recs_r.map (CondTopRec.mono hsub_r)
        refine ⟨hpre.trans (ext_to_ewr.trans ext_walk),
          r₀ :: recs_tail, .inl List.mem_cons_self,
          condTopRecsClosed_cons (hcl_blk.append (hcl_r.mono hsub_r)) ?_ ?_, ?_⟩
        · intro hp
          rcases hown_blk hp with hm_b | hasm_b
          · obtain ⟨r', hr', ha'⟩ := List.mem_map.mp hm_b
            exact .inl ⟨r', List.mem_cons_of_mem _ (List.mem_append_left _ hr'),
              ha', hdep_blk r' hr'⟩
          · exact .inr hasm_b
        · intro j hj b hb
          have hj_lt : j < c.refs.toList.length := by
            rw [Array.length_toList]
            exact (Array.getElem?_eq_some_iff.mp hb).1
          have hget : c.refs.toList[j] = b := by
            obtain ⟨_, heq_b⟩ := Array.getElem?_eq_some_iff.mp hb
            simpa using heq_b
          obtain ⟨hal, hrest⟩ := hmem_r j hj_lt (by simpa using hj)
          rw [hget] at hal hrest
          refine ⟨hal.mono hsub_r, ?_⟩
          rcases hrest with ⟨hnb, hm⟩ | hcov | hasm_b
          · have hm' : b ∈ (recs_r.map (CondTopRec.mono hsub_r)).map (·.addr) := by
              rwa [map_addr_condTopRec_mono]
            obtain ⟨r', hr', ha'⟩ := List.mem_map.mp hm'
            exact .inl ⟨hnb.mono hsub_r, r',
              List.mem_cons_of_mem _ (List.mem_append_right _ hr'), ha', hdep_r_lt r' hr'⟩
          · exact .inr (.inl hcov)
          · exact .inr (.inr hasm_b)
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr_tl
          · exact Nat.le_refl _
          · rcases List.mem_append.mp hr_tl with hr_blk | hr_r
            · exact Nat.le_of_lt (hdep_blk r hr_blk)
            · exact Nat.le_of_lt (hdep_r_lt r hr_r)
    -- 2. `KernelClaim::env_walk_refs`
    · intro i refs idxs x_rc x_refs x_consts x_owned x_asm x_strict r h h' calls
        hfuel hbound hrc hrefs hidxs hasm ev
      have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.env_walk_refs.lookup
        (by simp [IxVM.KernelClaim.env_walk_refs, ControlLower.hasControl]) ev
      simp only [IxVM.KernelClaim.env_walk_refs] at d0
      obtain ⟨v_sc, m_sc, bs_arm, body_arm, c_sc, c_arm, d_sc, sel, d_arm, hcalls⟩ := d0.matchValue_inv
      obtain ⟨p_r, d_pr, hld⟩ := d_sc.load_inv
      obtain ⟨hlook, hm_sc, rfl⟩ := d_pr.var_inv; simp at hlook; subst hlook; subst m_sc
      rcases selectArm_cons_inv sel with ⟨mt_nil, rfl⟩ | ⟨_, sel1⟩
      · -- `Nil`
        obtain ⟨_, hv_nil, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
        obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
        rw [hv_nil] at hld
        obtain rfl := rep_nil_of_load_any hrefs hld
        obtain ⟨_, a_u, _⟩ := d_arm.tuple_inv
        obtain ⟨_, rfl, _⟩ := a_u.nil_inv
        exact ⟨Heap.Extends.refl _, [], fun _ hj => absurd hj (Nat.not_lt_zero _),
          by simp [CondTopRecsClosed], by simp⟩
      · -- `Cons(a, rest)`
        rcases selectArm_cons_inv sel1 with ⟨mt_cons, rfl⟩ | ⟨_, sel2⟩
        case inr => exact (selectArm_nil_inv sel2).elim
        obtain ⟨vs_c, hv_cons, -, ml_cons⟩ := matchPattern_construct_inv mt_cons
        obtain ⟨x_a, _, _, _, rfl, mt_a, ml_cons1, rfl⟩ := matchListWith_cons_inv ml_cons
        obtain rfl := matchPattern_bind_inv mt_a
        obtain ⟨x_rest, _, _, _, rfl, mt_rest, ml_cons2, rfl⟩ := matchListWith_cons_inv ml_cons1
        obtain rfl := matchPattern_bind_inv mt_rest
        obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_cons2
        rw [hv_cons] at hld
        obtain ⟨a, rest, rfl, ha_head, hrest_rep⟩ := rep_cons_of_load_any hrefs hld
        -- `let (hit, next_consts) = sorted_pop(consts, i);`
        obtain ⟨v_pop, m_pop, bs_pop, c_pop, c_after_pop, d_pop, mt_pop, d_after_pop, rfl⟩ :=
          d_arm.letValue_inv
        obtain ⟨_, m_pargs, _, cs_pop, a_pop, ev_pop, rfl⟩ := d_pop.call_inv
        rw [instanceName_plain_some] at ev_pop
        obtain ⟨_, _, m_p0, _, _, rfl, d_p0, a_p1, rfl⟩ := a_pop.cons_inv
        obtain ⟨lp0, hm_p0, rfl⟩ := d_p0.var_inv; simp at lp0; subst lp0; subst m_p0
        obtain ⟨_, _, m_p1, _, _, rfl, d_p1, a_p2, rfl⟩ := a_p1.cons_inv
        obtain ⟨lp1, hm_p1, rfl⟩ := d_p1.var_inv; simp at lp1; subst lp1; subst m_p1
        obtain ⟨rfl, hm_p2, rfl⟩ := a_p2.nil_inv; subst m_pargs
        obtain ⟨_, hv_pop, -, ml_pop⟩ := matchPattern_tuple_inv mt_pop
        subst hv_pop
        obtain ⟨x_hit, _, _, _, rfl, mt_hit, ml_pop1, rfl⟩ := matchListWith_cons_inv ml_pop
        obtain rfl := matchPattern_bind_inv mt_hit
        obtain ⟨x_nc, _, _, _, rfl, mt_nc, ml_pop2, rfl⟩ := matchListWith_cons_inv ml_pop1
        obtain rfl := matchPattern_bind_inv mt_nc
        obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_pop2
        have hi_lt56 : i < 72057594037927936 := by simp at hbound; omega
        obtain ⟨hm_pop, hiff_pop, hidxs_next⟩ := Claim.sorted_pop_spec idxs hi_lt56 hidxs ev_pop
        subst m_pop
        -- `match hit { 1 => ..., _ => () }; env_walk_refs(rc, rest, next_consts, i + 1, owned, asm, strict)`
        obtain ⟨_, m_seg, _, c_seg, c_tail, d_seg, mt_seg, d_tail, rfl⟩ := d_after_pop.letValue_inv
        obtain rfl := matchPattern_wildcard_inv mt_seg
        obtain ⟨_, m_targs, _, cs_tail, a_tail, ev_tail, rfl⟩ := d_tail.call_inv
        rw [instanceName_plain_some] at ev_tail
        obtain ⟨_, _, m_t0, _, _, rfl, d_t0, a_t1, rfl⟩ := a_tail.cons_inv
        obtain ⟨lt0, hm_t0, rfl⟩ := d_t0.var_inv; simp at lt0; subst lt0; subst m_t0
        obtain ⟨_, _, m_t1, _, _, rfl, d_t1, a_t2, rfl⟩ := a_t1.cons_inv
        obtain ⟨lt1, hm_t1, rfl⟩ := d_t1.var_inv; simp at lt1; subst lt1; subst m_t1
        obtain ⟨_, _, m_t2, _, _, rfl, d_t2, a_t3, rfl⟩ := a_t2.cons_inv
        obtain ⟨lt2, hm_t2, rfl⟩ := d_t2.var_inv; simp at lt2; subst lt2; subst m_t2
        obtain ⟨v_inc, _, m_inc, _, _, rfl, d_t3, a_t4, rfl⟩ := a_t3.cons_inv
        obtain ⟨_, _, m_ti, _, _, d_ti, d_t1l, op_inc, rfl⟩ := d_t3.binary_inv
        obtain ⟨lti, hm_ti, rfl⟩ := d_ti.var_inv; simp at lti; subst lti; subst m_ti
        obtain ⟨rfl, hm_t1l, rfl⟩ := d_t1l.literal_inv; subst m_inc
        obtain ⟨_, _, m_t4, _, _, rfl, d_t4, a_t5, rfl⟩ := a_t4.cons_inv
        obtain ⟨lt4, hm_t4, rfl⟩ := d_t4.var_inv; simp at lt4; subst lt4; subst m_t4
        obtain ⟨_, _, m_t5, _, _, rfl, d_t5, a_t6, rfl⟩ := a_t5.cons_inv
        obtain ⟨lt5, hm_t5, rfl⟩ := d_t5.var_inv; simp at lt5; subst lt5; subst m_t5
        obtain ⟨_, _, m_t6, _, _, rfl, d_t6, a_t7, rfl⟩ := a_t6.cons_inv
        obtain ⟨lt6, hm_t6, rfl⟩ := d_t6.var_inv; simp at lt6; subst lt6; subst m_t6
        obtain ⟨rfl, hm_t7, rfl⟩ := a_t7.nil_inv; subst m_targs
        simp only [evalBinOp, Except.ok.injEq] at op_inc
        subst op_inc
        have hv_inc : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
        rw [hv_inc] at ev_tail
        -- Analyze `d_seg : match hit { 1 => ..., _ => () }`
        have hseg : Heap.Extends h m_seg ∧
            ∃ recs₁ : List (CondTopRec calls bAddr t lim asms),
              (i ∈ idxs → Claim.RefAllowedIn calls t bAddr lim a ∧
                ((Claim.NotBlockIn calls a ∧ a ∈ recs₁.map (·.addr)) ∨
                  Claim.CoveredAt t lim a ∨
                  a ∈ asms)) ∧
              CondTopRecsClosed recs₁ ∧
              (∀ r ∈ recs₁, r.depth ≤ calls.length) := by
          obtain ⟨_, m_h, bs_h, body_h, _, c_h, d_h, sel_h, d_hb, hseg_cs⟩ := d_seg.matchValue_inv
          obtain ⟨lh, hm_h, rfl⟩ := d_h.var_inv; simp at lh; subst lh; subst m_h
          rcases selectArm_cons_inv sel_h with ⟨mt_h1, rfl⟩ | ⟨nm_h1, sel_h1⟩
          · -- `hit = 1`
            obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 1) mt_h1
            -- `KernelRoles::assert_ref_allowed(rc, a);`
            obtain ⟨v_ra, m_ra, _, c_ra, c_cov, d_ra, mt_ra, d_cov, h1_cs⟩ := d_hb.letValue_inv
            obtain ⟨_, m_raargs, _, cs_ra, a_ra, ev_ra, hra_cs⟩ := d_ra.call_inv
            rw [instanceName_plain_some] at ev_ra
            obtain ⟨_, _, m_ra0, _, _, rfl, d_ra0, a_ra1, rfl⟩ := a_ra.cons_inv
            obtain ⟨lra0, hm_ra0, rfl⟩ := d_ra0.var_inv; simp at lra0; subst lra0; subst m_ra0
            obtain ⟨_, _, m_ra1, _, _, rfl, d_ra1, a_ra2, rfl⟩ := a_ra1.cons_inv
            obtain ⟨lra1, hm_ra1, rfl⟩ := d_ra1.var_inv; simp at lra1; subst lra1; subst m_ra1
            obtain ⟨rfl, hm_ra2, rfl⟩ := a_ra2.nil_inv; subst m_raargs
            obtain rfl := matchPattern_wildcard_inv mt_ra
            have ext_ra := ev_ra.heap_extends
            have hsub_ra : ∀ cl ∈ cs_ra, cl ∈ calls := fun cl hcl => by
              rw [hcalls]; rw [hseg_cs, h1_cs, hra_cs]; simp [hcl]
            have hal : Claim.RefAllowedIn calls t bAddr lim a :=
              ⟨h, m_ra, x_rc, x_a, v_ra, cs_ra, hrc, ha_head, ev_ra, hsub_ra⟩
            -- `match KernelRoles::walk_covered(rc, a) { 0 => ..., _ => () }`
            obtain ⟨v_cov, m_cov, bs_cv, body_cv, c_cv, c_cvb, d_cv, sel_cv, d_cvb, hcov_cs⟩ :=
              d_cov.matchValue_inv
            obtain ⟨_, m_cvargs, _, cs_cv, a_cv, ev_cv, hcv_cs⟩ := d_cv.call_inv
            rw [instanceName_plain_some] at ev_cv
            obtain ⟨_, _, m_cv0, _, _, rfl, d_cv0, a_cv1, rfl⟩ := a_cv.cons_inv
            obtain ⟨lcv0, hm_cv0, rfl⟩ := d_cv0.var_inv; simp at lcv0; subst lcv0; subst m_cv0
            obtain ⟨_, _, m_cv1, _, _, rfl, d_cv1, a_cv2, rfl⟩ := a_cv1.cons_inv
            obtain ⟨lcv1, hm_cv1, rfl⟩ := d_cv1.var_inv; simp at lcv1; subst lcv1; subst m_cv1
            obtain ⟨rfl, hm_cv2, rfl⟩ := a_cv2.nil_inv; subst m_cvargs
            have ext_cov := ev_cv.heap_extends
            rcases selectArm_cons_inv sel_cv with ⟨mt_c0, rfl⟩ | ⟨nm_c0, sel_cv1⟩
            · -- `walk_covered = 0`
              obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) mt_c0
              -- `match addr_set_member(a, asm) { 1 => (), _ => assert_not_block_ref(a) };`
              obtain ⟨_, m_nb, _, c_nb, c_sub, d_nbm, mt_nb, d_sub, hnb_seq_cs⟩ :=
                d_cvb.letValue_inv
              obtain rfl := matchPattern_wildcard_inv mt_nb
              -- `env_walk(KernelRoles::walk_ctx(rc, a), a, owned, asm, strict)`
              obtain ⟨_, _, _, cs_sub, a_sub, ev_sub, hsub_cs⟩ := d_sub.call_inv
              rw [instanceName_plain_some] at ev_sub
              obtain ⟨v_wc, _, m_wc, _, _, rfl, d_s0, a_s1, rfl⟩ := a_sub.cons_inv
              obtain ⟨_, _, _, cs_wc, a_wc, ev_wc, hwc_cs⟩ := d_s0.call_inv
              rw [instanceName_plain_some] at ev_wc
              obtain ⟨_, _, _, _, _, rfl, d_w0, a_w1, rfl⟩ := a_wc.cons_inv
              obtain ⟨lw0, rfl, rfl⟩ := d_w0.var_inv; simp at lw0; subst lw0
              obtain ⟨_, _, _, _, _, rfl, d_w1, a_w2, rfl⟩ := a_w1.cons_inv
              obtain ⟨lw1, rfl, rfl⟩ := d_w1.var_inv; simp at lw1; subst lw1
              obtain ⟨rfl, rfl, rfl⟩ := a_w2.nil_inv
              obtain ⟨_, _, _, _, _, rfl, d_s1, a_s2, rfl⟩ := a_s1.cons_inv
              obtain ⟨ls1, rfl, rfl⟩ := d_s1.var_inv; simp at ls1; subst ls1
              obtain ⟨_, _, _, _, _, rfl, d_s2, a_s3, rfl⟩ := a_s2.cons_inv
              obtain ⟨ls2, rfl, rfl⟩ := d_s2.var_inv; simp at ls2; subst ls2
              obtain ⟨_, _, _, _, _, rfl, d_s3, a_s4, rfl⟩ := a_s3.cons_inv
              obtain ⟨ls3, rfl, rfl⟩ := d_s3.var_inv; simp at ls3; subst ls3
              obtain ⟨_, _, _, _, _, rfl, d_s4, a_s5, rfl⟩ := a_s4.cons_inv
              obtain ⟨ls4, rfl, rfl⟩ := d_s4.var_inv; simp at ls4; subst ls4
              obtain ⟨rfl, rfl, rfl⟩ := a_s5.nil_inv
              -- Invert `match addr_set_member(a, asm)`
              obtain ⟨v_am, m_am, bs_am, body_am, c_am, c_amb, d_am, sel_am, d_amb, ham_cs⟩ :=
                d_nbm.matchValue_inv
              obtain ⟨_, m_amargs, _, cs_am, a_am, ev_am, _⟩ := d_am.call_inv
              rw [instanceName_plain_some] at ev_am
              obtain ⟨_, _, m_am0, _, _, rfl, d_am0, a_am1, rfl⟩ := a_am.cons_inv
              obtain ⟨lam0, hm_am0, rfl⟩ := d_am0.var_inv; simp at lam0; subst lam0; subst m_am0
              obtain ⟨_, _, m_am1, _, _, rfl, d_am1, a_am2, rfl⟩ := a_am1.cons_inv
              obtain ⟨lam1, hm_am1, rfl⟩ := d_am1.var_inv; simp at lam1; subst lam1; subst m_am1
              obtain ⟨rfl, hm_am2, rfl⟩ := a_am2.nil_inv; subst m_amargs
              obtain ⟨aB, ha_ref, ha_ix⟩ := ha_head
              have ext_rcov := ext_ra.trans ext_cov
              obtain ⟨hv_am, hm_am⟩ := addr_set_member_iff_spec
                (Bytes.repAddressRef_heapMono₂ addrTy ext_rcov ha_ref)
                (hasm.mono ext_rcov) ev_am
              subst m_am
              rcases selectArm_cons_inv sel_am with ⟨mt_am1, rfl⟩ | ⟨_, sel_am1⟩
              · -- `a ∈ asms`: skip `assert_not_block_ref`, return `a ∈ asms` directly!
                obtain ⟨hv1, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 1) mt_am1
                have ha_in_asms : a ∈ asms := by
                  rw [← ha_ix]
                  by_contra hnot
                  rw [ite_eq_right hnot] at hv_am
                  exact zero_ne_one (Value.field.inj (hv_am.symm.trans hv1))
                obtain ⟨_, a_u, _⟩ := d_amb.tuple_inv
                obtain ⟨_, rfl, _⟩ := a_u.nil_inv
                exact ⟨ext_rcov.trans (ev_wc.heap_extends.trans ev_sub.heap_extends), [],
                  fun _ => ⟨hal, .inr (.inr ha_in_asms)⟩,
                  by simp [CondTopRecsClosed], by simp⟩
              · -- `a ∉ asms`: `assert_not_block_ref(a)` then `env_walk(walk_ctx(rc, a), a, ...)`
                rcases selectArm_cons_inv sel_am1 with ⟨mt_amw, rfl⟩ | ⟨_, sel_am2⟩
                case inr => exact (selectArm_nil_inv sel_am2).elim
                obtain rfl := matchPattern_wildcard_inv mt_amw
                obtain ⟨_, m_nbargs, _, cs_nb, a_nb, ev_nb, hnb_cs⟩ := d_amb.call_inv
                rw [instanceName_plain_some] at ev_nb
                obtain ⟨_, _, m_nb0, _, _, rfl, d_nb0, a_nb1, rfl⟩ := a_nb.cons_inv
                obtain ⟨lnb0, hm_nb0, rfl⟩ := d_nb0.var_inv; simp at lnb0; subst lnb0; subst m_nb0
                obtain ⟨rfl, hm_nb1, rfl⟩ := a_nb1.nil_inv; subst m_nbargs
                have ha_rcov : BaseSeams.addr m_cov x_a a :=
                  ⟨aB, Bytes.repAddressRef_heapMono₂ addrTy ext_rcov ha_ref, ha_ix⟩
                obtain ⟨ext_nb, hnb⟩ := Claim.assert_not_block_ref_notBlock ha_rcov ev_nb
                have ext_pre := ext_rcov.trans ext_nb
                obtain ⟨ext_wc, hwc⟩ :=
                  Claim.walk_ctx_lim_spec (hrc.mono ext_pre) (BaseSeams.addr_mono ext_nb ha_rcov) ev_wc
                have hsub_nb : ∀ cl ∈ cs_nb, cl ∈ calls := fun cl hcl => by
                  rw [hcalls]
                  rw [hseg_cs, h1_cs, hcov_cs, hnb_seq_cs, ham_cs, hnb_cs]; simp [hcl]
                rcases hwc with rfl | ⟨hcov, -⟩
                · have hlt_calls : cs_sub.length < calls.length := by
                    rw [hcalls]
                    rw [hseg_cs, h1_cs, hcov_cs, hnb_seq_cs, hsub_cs]
                    simp only [List.length_cons, List.length_append]
                    omega
                  have hlt_sub : cs_sub.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
                  have ext_pre' := ext_pre.trans ext_wc
                  obtain ⟨ext_sub, recs_s, hmem_s, hcl_s, hdep_s⟩ :=
                    (ih cs_sub.length hlt_sub).1 (Nat.le_refl _) (hrc.mono ext_pre')
                      (BaseSeams.addr_mono (ext_nb.trans ext_wc) ha_rcov) (hasm.mono ext_pre') ev_sub
                  have hsub_s : ∀ cl ∈ cs_sub, cl ∈ calls := fun cl hcl => by
                    rw [hcalls]
                    rw [hseg_cs, h1_cs, hcov_cs, hnb_seq_cs, hsub_cs]; simp [hcl]
                  refine ⟨ext_pre'.trans ext_sub, recs_s.map (CondTopRec.mono hsub_s), ?_,
                    hcl_s.mono hsub_s,
                    condTopRec_mono_depth_le hsub_s hdep_s (Nat.le_of_lt hlt_calls)⟩
                  intro _
                  refine ⟨hal, ?_⟩
                  rcases hmem_s with hm | ⟨hasm_a, _⟩
                  · refine .inl ⟨hnb.mono hsub_nb, ?_⟩
                    rw [map_addr_condTopRec_mono]
                    exact hm
                  · exact .inr (.inr hasm_a)
                · exact ⟨ext_pre.trans (ext_wc.trans ev_sub.heap_extends), [],
                    fun _ => ⟨hal, .inr (.inl hcov)⟩,
                    by simp [CondTopRecsClosed], by simp⟩
            · -- `walk_covered ≠ 0`
              rcases selectArm_cons_inv sel_cv1 with ⟨mt_cw, rfl⟩ | ⟨_, sel_cv2⟩
              case inr => exact (selectArm_nil_inv sel_cv2).elim
              obtain rfl := matchPattern_wildcard_inv mt_cw
              obtain ⟨_, a_u, _⟩ := d_cvb.tuple_inv
              obtain ⟨_, rfl, _⟩ := a_u.nil_inv
              obtain ⟨-, hv⟩ :=
                Claim.walk_covered_lim_spec (hrc.mono ext_ra) (BaseSeams.addr_mono ext_ra ha_head) ev_cv
              rcases hv with hv0 | hcov
              · exact absurd hv0 (MatchesConst.none_inv (MatchesConst.literal 0) nm_c0)
              · exact ⟨ext_ra.trans ext_cov, [], fun _ => ⟨hal, .inr (.inl hcov)⟩,
                  by simp [CondTopRecsClosed], by simp⟩
          · -- `hit ≠ 1`
            rcases selectArm_cons_inv sel_h1 with ⟨mt_hw, rfl⟩ | ⟨_, sel_h2⟩
            case inr => exact (selectArm_nil_inv sel_h2).elim
            obtain rfl := matchPattern_wildcard_inv mt_hw
            obtain ⟨_, a_u, _⟩ := d_hb.tuple_inv
            obtain ⟨_, rfl, _⟩ := a_u.nil_inv
            exact ⟨Heap.Extends.refl _, [],
              fun hi_in =>
                absurd (hiff_pop.mpr hi_in) (MatchesConst.none_inv (MatchesConst.literal 1) nm_h1),
              by simp [CondTopRecsClosed], by simp⟩
        obtain ⟨ext1, recs₁, hmem₁, hcl₁, hdep₁⟩ := hseg
        have hlt_tail_calls : cs_tail.length < calls.length := by
          rw [hcalls]
          simp only [List.length_cons, List.length_append]
          omega
        have hlt_tail : cs_tail.length < fuel := Nat.lt_of_lt_of_le hlt_tail_calls hfuel
        have hbound_tail : (i + 1) + rest.length < 8589934592 := by
          simp at hbound; omega
        obtain ⟨ext2, recs₂_raw, hmem₂, hcl₂, hdep₂⟩ :=
          (ih cs_tail.length hlt_tail).2 (i := i + 1) (Nat.le_refl _) hbound_tail
            (hrc.mono ext1)
            (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext1 hrest_rep)
            (hidxs_next.mono ext1) (hasm.mono ext1) ev_tail
        have hsub₂ : ∀ cl ∈ cs_tail, cl ∈ calls := fun cl hcl => by
          rw [hcalls]; simp [hcl]
        refine ⟨ext1.trans ext2, recs₁ ++ recs₂_raw.map (CondTopRec.mono hsub₂), ?_,
          hcl₁.append (hcl₂.mono hsub₂), ?_⟩
        · intro j hj hij
          cases j with
          | zero =>
            simp only [Nat.add_zero] at hij
            obtain ⟨hal, hrest⟩ := hmem₁ hij
            refine ⟨hal, ?_⟩
            rcases hrest with ⟨hnb, hm⟩ | hcov | hasm_a
            · refine .inl ⟨hnb, ?_⟩
              rw [List.map_append]
              exact List.mem_append_left _ hm
            · exact .inr (.inl hcov)
            · exact .inr (.inr hasm_a)
          | succ j' =>
            have hj' : j' < rest.length := by simp at hj; omega
            have hij' : (i + 1) + j' ∈ idxs := by
              have heq_idx : (i + 1) + j' = i + (j' + 1) := by omega
              rwa [heq_idx]
            obtain ⟨hal, hrest⟩ := hmem₂ j' hj' hij'
            refine ⟨hal.mono hsub₂, ?_⟩
            rcases hrest with ⟨hnb, hm⟩ | hcov | hasm_b
            · refine .inl ⟨hnb.mono hsub₂, ?_⟩
              rw [List.map_append, map_addr_condTopRec_mono]
              exact List.mem_append_right _ hm
            · exact .inr (.inl hcov)
            · exact .inr (.inr hasm_b)
        · intro r hr
          rcases List.mem_append.mp hr with hr1 | hr2
          · exact hdep₁ r hr1
          · exact condTopRec_mono_depth_le hsub₂ hdep₂ (Nat.le_of_lt hlt_tail_calls) r hr2

private theorem env_walk_cond_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {asms : List _root_.Address}
    {x_rc x_addr x_owned x_asm x_strict r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (ha : BaseSeams.addr h x_addr addr)
    (hasm : Claim.RepAddrSet h asms x_asm)
    (ev : ObsFn Obs.W "KernelClaim::env_walk" [x_rc, x_addr, x_owned, x_asm, x_strict] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ recs : List (CondTopRec calls bAddr t lim asms),
      (addr ∈ recs.map (·.addr) ∨ (addr ∈ asms ∧ x_strict ≠ .field 2)) ∧
      CondTopRecsClosed recs ∧
      (∀ r ∈ recs, r.depth ≤ calls.length) :=
  (env_walk_cond_lim_fuel_aux calls.length).1 (Nat.le_refl _) hrc ha hasm ev

/-! ### 4c. `env_walk_leaves` & `run_check_env` (Both `asm = none` and `asm = some r`) -/

private theorem env_walk_leaves_cond_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {asms : List _root_.Address} (as : List Bytes.Address) :
    ∀ {x_rc x_leaves x_owned x_asm r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.RCLimRep t bAddr lim h x_rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h as x_leaves →
      Claim.RepAddrSet h asms x_asm →
      ObsFn Obs.W "KernelClaim::env_walk_leaves" [x_rc, x_leaves, x_owned, x_asm] h r h' calls →
      Heap.Extends h h' ∧
      ∃ recs : List (CondTopRec calls bAddr t lim asms),
        (∀ a ∈ as.map ixAddr, a ∈ recs.map (·.addr)) ∧
        CondTopRecsClosed recs ∧
        (∀ r ∈ recs, r.depth ≤ calls.length) := by
  induction as with
  | nil =>
    intro x_rc x_leaves x_owned x_asm r h h' calls hrc hl hasm ev
    have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.env_walk_leaves.lookup
      (by simp [IxVM.KernelClaim.env_walk_leaves, ControlLower.hasControl]) ev
    simp only [IxVM.KernelClaim.env_walk_leaves] at d0
    obtain ⟨v_sc, m_sc, bs_arm, body_arm, c_sc, c_arm, d_sc, sel, d_arm, rfl⟩ := d0.matchValue_inv
    obtain ⟨p_l, d_pl, hld⟩ := d_sc.load_inv
    obtain ⟨hlook, rfl, rfl⟩ := d_pl.var_inv; simp at hlook; subst hlook
    rcases selectArm_cons_inv sel with ⟨mt_nil, rfl⟩ | ⟨_, sel1⟩
    · obtain ⟨_, hv_nil, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
      obtain ⟨_, a_u, _⟩ := d_arm.tuple_inv
      obtain ⟨_, rfl, _⟩ := a_u.nil_inv
      exact ⟨Heap.Extends.refl _, [], by simp, by simp [CondTopRecsClosed], by simp⟩
    · rcases selectArm_cons_inv sel1 with ⟨mt_cons, _⟩ | ⟨_, sel2⟩
      · obtain ⟨vs, hv_cons, hlen, _⟩ := matchPattern_construct_inv mt_cons
        rcases vs with _ | ⟨x_a, _ | ⟨x_rest, _ | _⟩⟩ <;> simp at hlen
        rw [hv_cons] at hld
        obtain ⟨_, _, hbad, -⟩ := rep_cons_of_load_any hl hld
        cases hbad
      · exact (selectArm_nil_inv sel2).elim
  | cons aB rest ih =>
    intro x_rc x_leaves x_owned x_asm r h h' calls hrc hl hasm ev
    have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.env_walk_leaves.lookup
      (by simp [IxVM.KernelClaim.env_walk_leaves, ControlLower.hasControl]) ev
    simp only [IxVM.KernelClaim.env_walk_leaves] at d0
    obtain ⟨v_sc, m_sc, bs_arm, body_arm, c_sc, c_arm, d_sc, sel, d_arm, hcalls⟩ := d0.matchValue_inv
    obtain ⟨p_l, d_pl, hld⟩ := d_sc.load_inv
    obtain ⟨hlook, rfl, rfl⟩ := d_pl.var_inv; simp at hlook; subst hlook
    rcases selectArm_cons_inv sel with ⟨mt_nil, _⟩ | ⟨_, sel1⟩
    · obtain ⟨_, hv_nil, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
      rw [hv_nil] at hld
      cases rep_nil_of_load_any hl hld
    · rcases selectArm_cons_inv sel1 with ⟨mt_cons, rfl⟩ | ⟨_, sel2⟩
      case inr => exact (selectArm_nil_inv sel2).elim
      obtain ⟨vs, hv_cons, -, ml_cons⟩ := matchPattern_construct_inv mt_cons
      obtain ⟨x_a, _, _, _, rfl, mt_a, ml_cons1, rfl⟩ := matchListWith_cons_inv ml_cons
      obtain rfl := matchPattern_bind_inv mt_a
      obtain ⟨x_rest, _, _, _, rfl, mt_rest, ml_cons2, rfl⟩ := matchListWith_cons_inv ml_cons1
      obtain rfl := matchPattern_bind_inv mt_rest
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_cons2
      rw [hv_cons] at hld
      obtain ⟨aB', rest', heq, ha_ref, hrest⟩ := rep_cons_of_load_any hl hld
      injection heq with he1 he2
      subst he1 he2
      -- `assert_eq!(addr_set_member(a, asm), 0, ...);`
      obtain ⟨_, m_eq, _, c_eq, c_after_eq, d_eq, mt_eq, d_after_eq, rfl⟩ := d_arm.letValue_inv
      obtain ⟨_, a_eq, ap_eq⟩ := d_eq.builtin_inv
      obtain ⟨v_am, _, m_am, _, _, rfl, d_am, a_eq1, rfl⟩ := a_eq.cons_inv
      obtain ⟨_, _, _, cs_am, a_am, ev_am, rfl⟩ := d_am.call_inv
      rw [instanceName_plain_some] at ev_am
      obtain ⟨_, _, _, _, _, rfl, d_am0, a_am1, rfl⟩ := a_am.cons_inv
      obtain ⟨lam0, rfl, rfl⟩ := d_am0.var_inv; simp at lam0; subst lam0
      obtain ⟨_, _, _, _, _, rfl, d_am1, a_am2, rfl⟩ := a_am1.cons_inv
      obtain ⟨lam1, rfl, rfl⟩ := d_am1.var_inv; simp at lam1; subst lam1
      obtain ⟨rfl, rfl, rfl⟩ := a_am2.nil_inv
      obtain ⟨_, _, _, _, _, rfl, d_0, a_eq2, rfl⟩ := a_eq1.cons_inv
      obtain ⟨rfl, rfl, rfl⟩ := d_0.literal_inv
      obtain ⟨rfl, rfl, rfl⟩ := a_eq2.nil_inv
      obtain ⟨heq_am, rfl⟩ := Builtin.assertEq_inv ap_eq
      obtain ⟨hv_am, hm_am⟩ := addr_set_member_iff_spec ha_ref hasm ev_am
      subst hm_am
      have ha_notin : ixAddr aB ∉ asms := by
        intro hin
        rw [ite_eq_left hin] at hv_am
        exact one_ne_zero (Value.field.inj (hv_am.symm.trans heq_am))
      obtain rfl := matchPattern_wildcard_inv mt_eq
      -- `env_walk(rc, a, owned, asm, 1);`
      obtain ⟨_, m1, _, c_ew, c_tl, d_ew, mt_ew, d_tl, rfl⟩ := d_after_eq.letValue_inv
      obtain ⟨_, _, _, cs_ew, a_ew, ev_ew, rfl⟩ := d_ew.call_inv
      rw [instanceName_plain_some] at ev_ew
      obtain ⟨_, _, _, _, _, rfl, d_w0, a_w1, rfl⟩ := a_ew.cons_inv
      obtain ⟨lw0, rfl, rfl⟩ := d_w0.var_inv; simp at lw0; subst lw0
      obtain ⟨_, _, _, _, _, rfl, d_w1, a_w2, rfl⟩ := a_w1.cons_inv
      obtain ⟨lw1, rfl, rfl⟩ := d_w1.var_inv; simp at lw1; subst lw1
      obtain ⟨_, _, _, _, _, rfl, d_w2, a_w3, rfl⟩ := a_w2.cons_inv
      obtain ⟨lw2, rfl, rfl⟩ := d_w2.var_inv; simp at lw2; subst lw2
      obtain ⟨_, _, _, _, _, rfl, d_w3, a_w4, rfl⟩ := a_w3.cons_inv
      obtain ⟨lw3, rfl, rfl⟩ := d_w3.var_inv; simp at lw3; subst lw3
      obtain ⟨_, _, _, _, _, rfl, d_w4, a_w5, rfl⟩ := a_w4.cons_inv
      obtain ⟨rfl, rfl, rfl⟩ := d_w4.literal_inv
      obtain ⟨rfl, rfl, rfl⟩ := a_w5.nil_inv
      obtain rfl := matchPattern_wildcard_inv mt_ew
      -- `env_walk_leaves(rc, rest, owned, asm)`
      obtain ⟨_, _, _, cs_tl, a_tl, ev_tl, rfl⟩ := d_tl.call_inv
      rw [instanceName_plain_some] at ev_tl
      obtain ⟨_, _, _, _, _, rfl, d_t0, a_t1, rfl⟩ := a_tl.cons_inv
      obtain ⟨lt0, rfl, rfl⟩ := d_t0.var_inv; simp at lt0; subst lt0
      obtain ⟨_, _, _, _, _, rfl, d_t1, a_t2, rfl⟩ := a_t1.cons_inv
      obtain ⟨lt1, rfl, rfl⟩ := d_t1.var_inv; simp at lt1; subst lt1
      obtain ⟨_, _, _, _, _, rfl, d_t2, a_t3, rfl⟩ := a_t2.cons_inv
      obtain ⟨lt2, rfl, rfl⟩ := d_t2.var_inv; simp at lt2; subst lt2
      obtain ⟨_, _, _, _, _, rfl, d_t3, a_t4, rfl⟩ := a_t3.cons_inv
      obtain ⟨lt3, rfl, rfl⟩ := d_t3.var_inv; simp at lt3; subst lt3
      obtain ⟨rfl, rfl, rfl⟩ := a_t4.nil_inv
      obtain ⟨ext1, recs₁, hmem₁_or, hcl₁, hdep₁⟩ :=
        env_walk_cond_lim_spec hrc ⟨aB, ha_ref, rfl⟩ hasm ev_ew
      have hmem₁ : ixAddr aB ∈ recs₁.map (·.addr) := by
        rcases hmem₁_or with hm | ⟨hin, _⟩
        · exact hm
        · exact absurd hin ha_notin
      obtain ⟨ext2, recs₂, hmem₂, hcl₂, hdep₂⟩ := ih (hrc.mono ext1)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hrest)
        (hasm.mono ext1) ev_tl
      have hsub₁ : ∀ cl ∈ cs_ew, cl ∈ calls := fun cl hcl => by rw [hcalls]; simp [hcl]
      have hsub₂ : ∀ cl ∈ cs_tl, cl ∈ calls := fun cl hcl => by rw [hcalls]; simp [hcl]
      have hle₁ : cs_ew.length ≤ calls.length := by
        rw [hcalls]; simp only [List.length_cons, List.length_append, List.length_nil]; omega
      have hle₂ : cs_tl.length ≤ calls.length := by
        rw [hcalls]; simp only [List.length_cons, List.length_append, List.length_nil]; omega
      refine ⟨ext1.trans ext2,
        recs₁.map (CondTopRec.mono hsub₁) ++ recs₂.map (CondTopRec.mono hsub₂), ?_,
        (hcl₁.mono hsub₁).append (hcl₂.mono hsub₂), ?_⟩
      · intro a ha_mem
        rw [List.map_append, map_addr_condTopRec_mono, map_addr_condTopRec_mono]
        simp only [List.map_cons, List.mem_cons] at ha_mem
        rcases ha_mem with rfl | htl
        · exact List.mem_append_left _ hmem₁
        · exact List.mem_append_right _ (hmem₂ a htl)
      · intro r hr
        rcases List.mem_append.mp hr with hr1 | hr2
        · exact condTopRec_mono_depth_le hsub₁ hdep₁ hle₁ r hr1
        · exact condTopRec_mono_depth_le hsub₂ hdep₂ hle₂ r hr2

private theorem run_check_env_none_cond_lim_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none)
    {tOwned : Ix.AssumptionTree} (htOwned : tOwned ∈ V.trees)
    {x_rc x_env_root r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCLimRep t b.address lim h x_rc)
    (hroot : BaseSeams.addr h x_env_root (treeRoot tOwned))
    (ev : ObsFn Obs.W "KernelClaim::run_check_env"
      [x_rc, x_env_root, .construct Obs.Names.«Options::Option<&[Field; 32]>» "None" []]
      h r h' calls) :
    V.HashedCollision extra calls ∨
    CondShardWalk calls b.address t lim (treeLeaves tOwned) [] := by
  rcases Obs.«KernelClaim::run_check_env».obs ev with
    ⟨v1, m2, cs12, v98, m99, cs101, m124, cs135, cs155,
      ev14, sg106, _, ev137, ev157, hc174⟩ |
    ⟨v1, m2, cs12, v98, m99, cs101, m124, cs135, _, _, _, _, _, _, _, _, _,
      ev14, sg106, _, ev137, _, _, hc264⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hne266, _⟩
  · rcases Claim.load_assumption_tree_spec (V := V) (extra := extra) htOwned hroot ev14 with
      hcoll | ⟨ext1, as, hmap, hlLeaves⟩
    · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
        (fun cl hcl => by rw [hc174]; simp [hcl]) hcoll)
    · rcases sg106 with ⟨_, heq67, _, _, _⟩ | ⟨_, _, _, _, hm99, hc101⟩
      · simp at heq67
      · subst m99 cs101
        have hrc2 := hrc.mono ext1
        obtain ⟨_, hm124⟩ := cond_role_ctx_axioms_lim_spec hrc2 ev137
        subst m124
        rcases Claim.walk_leaves_owned_lim_spec (V := V) (extra := extra) hadm hb_extra hlim as
            hrc2 hlLeaves ev157 with
          hcoll | ⟨-, hseeds_cl, recs, hmem, hcl, hdep⟩
        · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
            (fun cl hcl => by rw [hc174]; simp [hcl]) hcoll)
        · have hsub : ∀ cl ∈ cs155, cl ∈ calls := fun cl hcl => by rw [hc174]; simp [hcl]
          have hle : cs155.length ≤ calls.length := by
            rw [hc174]; simp only [List.length_cons, List.length_append]; omega
          refine .inr ⟨(recs.map CondTopRec.ofTopRec).map (CondTopRec.mono hsub), ?_, ?_,
            (condTopRecsClosed_of_topRecsClosed hcl).mono hsub, ?_⟩
          · intro a ha
            rw [← hmap] at ha
            rw [map_addr_condTopRec_mono]
            have hm := hmem a ha
            obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hm
            exact List.mem_map.mpr ⟨CondTopRec.ofTopRec r₀, List.mem_map_of_mem hr₀, rfl⟩
          · intro a ha
            rw [← hmap] at ha
            exact (hseeds_cl a ha).mono hsub
          · intro r hr
            obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hr
            obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr1
            have hd := hdep r0 hr0
            simp only [CondTopRec.mono, CondTopRec.ofTopRec]
            omega
  · rcases Claim.load_assumption_tree_spec (V := V) (extra := extra) htOwned hroot ev14 with
      hcoll | ⟨ext1, _, _, _⟩
    · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
        (fun cl hcl => by rw [hc264]; simp [hcl]) hcoll)
    · have hm99 : m99 = m2 := by
        rcases sg106 with ⟨_, _, _, hm, _⟩ | ⟨_, _, _, _, hm, _⟩ <;> exact hm
      subst hm99
      obtain ⟨hax, _⟩ := cond_role_ctx_axioms_lim_spec (hrc.mono ext1) ev137
      simp at hax
  · exact absurd rfl (hne266 [] rfl)

private theorem run_check_env_some_cond_lim_spec {V : View} {extra : List ByteArray}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {tOwned tAsm : Ix.AssumptionTree} (htOwned : tOwned ∈ V.trees) (htAsm : tAsm ∈ V.trees)
    {x_rc x_env_root x_asm_root r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (hroot : BaseSeams.addr h x_env_root (treeRoot tOwned))
    (hasmRoot : BaseSeams.addr h x_asm_root (treeRoot tAsm))
    (ev : ObsFn Obs.W "KernelClaim::run_check_env"
      [x_rc, x_env_root, .construct Obs.Names.«Options::Option<&[Field; 32]>» "Some" [x_asm_root]]
      h r h' calls) :
    V.HashedCollision extra calls ∨
    CondShardWalk calls bAddr t lim (treeLeaves tOwned) (treeLeaves tAsm) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.run_check_env.lookup
    (by simp [IxVM.KernelClaim.run_check_env, ControlLower.hasControl]) ev
  simp only [IxVM.KernelClaim.run_check_env] at d0
  -- `let owned = load_assumption_tree(env_root);`
  obtain ⟨x_owned, m_own, _, c_own, c1, d_own, mt_own, d1, hcalls⟩ := d0.letValue_inv
  obtain ⟨_, _, _, cs_own, a_own, ev_own, rfl⟩ := d_own.call_inv
  rw [instanceName_plain_some] at ev_own
  obtain ⟨_, _, _, _, _, rfl, d_o0, a_o1, rfl⟩ := a_own.cons_inv
  obtain ⟨lo0, rfl, rfl⟩ := d_o0.var_inv; simp at lo0; subst lo0
  obtain ⟨rfl, rfl, rfl⟩ := a_o1.nil_inv
  obtain rfl := matchPattern_bind_inv mt_own
  -- `match (*(owned)) { Nil => assert_eq!(0, 1); (), Cons(_, _) => () };`
  obtain ⟨_, m_ne, _, c_ne, c2, d_ne, mt_ne, d2, rfl⟩ := d1.letValue_inv
  have ext_ne := d_ne.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_ne
  -- `match asm { None => ..., Some(r) => ... }`
  obtain ⟨v_asm, m_asm, bs_a, body_a, c_asm, c_arm, d_asm, sel_a, d_arm, rfl⟩ := d2.matchValue_inv
  obtain ⟨la, rfl, rfl⟩ := d_asm.var_inv; simp at la; subst la
  rcases selectArm_cons_inv sel_a with ⟨mt_none, _⟩ | ⟨_, sel_a1⟩
  · obtain ⟨_, hv_none, _, _⟩ := matchPattern_construct_inv mt_none
    injection hv_none with _ hctor _
    exact absurd hctor (by decide)
  rcases selectArm_cons_inv sel_a1 with ⟨mt_some, rfl⟩ | ⟨_, sel_a2⟩
  case inr => exact (selectArm_nil_inv sel_a2).elim
  obtain ⟨vs_s, hv_some, -, ml_some⟩ := matchPattern_construct_inv mt_some
  obtain ⟨x_r, _, _, _, rfl, mt_r, ml_some1, rfl⟩ := matchListWith_cons_inv ml_some
  obtain rfl := matchPattern_bind_inv mt_r
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_some1
  injection hv_some with _ _ hargs_some
  injection hargs_some with hxr_eq _
  subst hxr_eq
  -- `assert_leaves_claimable(rc, owned);`
  obtain ⟨_, m_alc, _, c_alc, c3, d_alc, mt_alc, d3, rfl⟩ := d_arm.letValue_inv
  obtain ⟨_, _, _, cs_alc, a_alc, ev_alc, rfl⟩ := d_alc.call_inv
  rw [instanceName_plain_some] at ev_alc
  obtain ⟨_, _, _, _, _, rfl, d_a0, a_a1, rfl⟩ := a_alc.cons_inv
  obtain ⟨la0, rfl, rfl⟩ := d_a0.var_inv; simp at la0; subst la0
  obtain ⟨_, _, _, _, _, rfl, d_a1, a_a2, rfl⟩ := a_a1.cons_inv
  obtain ⟨la1, rfl, rfl⟩ := d_a1.var_inv; simp at la1; subst la1
  obtain ⟨rfl, rfl, rfl⟩ := a_a2.nil_inv
  obtain rfl := matchPattern_wildcard_inv mt_alc
  -- `let owned_set = addr_set_build(owned, RBTreeMap::RBTreeMap::Nil);`
  obtain ⟨x_os, m_os, _, c_os, c4, d_os, mt_os, d4, rfl⟩ := d3.letValue_inv
  have ext_os := d_os.heap_extends
  obtain rfl := matchPattern_bind_inv mt_os
  -- `let asm_set = addr_set_build(load_assumption_tree(r), RBTreeMap::RBTreeMap::Nil);`
  obtain ⟨x_as, m_as, _, c_as, c5, d_as, mt_as, d5, rfl⟩ := d4.letValue_inv
  obtain ⟨_, m_asargs, _, cs_as, a_as, ev_as, rfl⟩ := d_as.call_inv
  rw [instanceName_plain_some] at ev_as
  obtain ⟨x_al, _, m_al, _, _, rfl, d_la, a_as1, rfl⟩ := a_as.cons_inv
  obtain ⟨_, m_laargs, _, cs_la, a_la, ev_la, rfl⟩ := d_la.call_inv
  rw [instanceName_plain_some] at ev_la
  obtain ⟨_, _, m_la0, _, _, rfl, d_la0, a_la1, rfl⟩ := a_la.cons_inv
  obtain ⟨lla0, hm_la0, rfl⟩ := d_la0.var_inv; simp at lla0; subst lla0; subst m_la0
  obtain ⟨rfl, hm_la1, rfl⟩ := a_la1.nil_inv; subst m_laargs
  obtain ⟨x_nil, _, m_nil, _, _, rfl, d_nil, a_as2, rfl⟩ := a_as1.cons_inv
  obtain ⟨vs_nil, a_nil, hnil_eq⟩ := d_nil.construct_inv
  obtain ⟨rfl, hm_nil, rfl⟩ := a_nil.nil_inv; subst m_nil
  obtain ⟨rfl, hm_as2, rfl⟩ := a_as2.nil_inv; subst m_asargs
  obtain rfl := matchPattern_bind_inv mt_as
  -- `env_walk_leaves(rc, owned, owned_set, asm_set)`
  obtain ⟨_, m_ewlargs, _, cs_ewl, a_ewl, ev_ewl, rfl⟩ := d5.call_inv
  rw [instanceName_plain_some] at ev_ewl
  obtain ⟨_, _, m_e0, _, _, rfl, d_e0, a_e1, rfl⟩ := a_ewl.cons_inv
  obtain ⟨le0, hm_e0, rfl⟩ := d_e0.var_inv; simp at le0; subst le0; subst m_e0
  obtain ⟨_, _, m_e1, _, _, rfl, d_e1, a_e2, rfl⟩ := a_e1.cons_inv
  obtain ⟨le1, hm_e1, rfl⟩ := d_e1.var_inv; simp at le1; subst le1; subst m_e1
  obtain ⟨_, _, m_e2, _, _, rfl, d_e2, a_e3, rfl⟩ := a_e2.cons_inv
  obtain ⟨le2, hm_e2, rfl⟩ := d_e2.var_inv; simp at le2; subst le2; subst m_e2
  obtain ⟨_, _, m_e3, _, _, rfl, d_e3, a_e4, rfl⟩ := a_e3.cons_inv
  obtain ⟨le3, hm_e3, rfl⟩ := d_e3.var_inv; simp at le3; subst le3; subst m_e3
  obtain ⟨rfl, hm_e4, rfl⟩ := a_e4.nil_inv; subst m_ewlargs
  -- Discharge `load_assumption_tree(env_root)`
  rcases Claim.load_assumption_tree_spec (V := V) (extra := extra) htOwned hroot ev_own with
    hcoll | ⟨ext_own, asOwned, hmapOwned, hlOwned⟩
  · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
      (fun cl hcl => by rw [hcalls]; simp [hcl]) hcoll)
  have ext_to_alc := ext_own.trans ext_ne
  obtain ⟨ext_alc, hclaimable⟩ := assert_leaves_claimable_lim_spec asOwned
    (hrc.mono ext_to_alc)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_ne hlOwned) ev_alc
  have ext_to_la := ext_to_alc.trans (ext_alc.trans ext_os)
  -- Discharge `load_assumption_tree(r)`
  rcases Claim.load_assumption_tree_spec (V := V) (extra := extra) htAsm
      (BaseSeams.addr_mono ext_to_la hasmRoot) ev_la with
    hcoll | ⟨ext_la, asAsm, hmapAsm, hlAsm⟩
  · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
      (fun cl hcl => by rw [hcalls]; simp [hcl]) hcoll)
  have hnil_rep : Claim.RepAddrSet m_al [] x_nil := by
    rw [hnil_eq]
    have hsym : instanceName [] "RBTreeMap::RBTreeMap" (some [.field]) = addrMapEnum := by
      simpa [instanceName, Ty.subst, Ty.toCore] using Obs.Names.«RBTreeMap::RBTreeMap<Field>».symbol
    simpa only [hsym] using Claim.RepAddrSet.nil m_al
  obtain ⟨ext_as, hset_rev⟩ := Claim.addr_set_build_spec hlAsm hnil_rep ev_as
  have hset : Claim.RepAddrSet m_as (treeLeaves tAsm) x_as :=
    repAddrSet_of_iff (fun x => by
      rw [List.append_nil, ← hmapAsm, List.mem_map, List.mem_map]
      simp [List.mem_reverse]) hset_rev
  have ext_to_ewl := ext_to_la.trans (ext_la.trans ext_as)
  have ext_own_to_ewl := ext_ne.trans (ext_alc.trans (ext_os.trans (ext_la.trans ext_as)))
  obtain ⟨_, recs, hmem, hcl, hdep⟩ := env_walk_leaves_cond_lim_spec asOwned
    (hrc.mono ext_to_ewl)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_own_to_ewl hlOwned)
    hset ev_ewl
  have hsub_alc : ∀ cl ∈ cs_alc, cl ∈ calls := fun cl hcl => by rw [hcalls]; simp [hcl]
  have hsub_ewl : ∀ cl ∈ cs_ewl, cl ∈ calls := fun cl hcl => by rw [hcalls]; simp [hcl]
  have hle_ewl : cs_ewl.length ≤ calls.length := by
    rw [hcalls]; simp only [List.length_cons, List.length_append, List.length_nil]; omega
  refine .inr ⟨recs.map (CondTopRec.mono hsub_ewl), ?_, ?_, hcl.mono hsub_ewl,
    condTopRec_mono_depth_le hsub_ewl hdep hle_ewl⟩
  · intro a ha
    rw [← hmapOwned] at ha
    rw [map_addr_condTopRec_mono]
    exact hmem a ha
  · intro a ha
    rw [← hmapOwned] at ha
    exact (hclaimable a ha).mono hsub_alc

/-! ### 4d. `verify_claim_conditional_walk_spec` (`IxVM::verify_claim` on Conditional Shards) -/

private theorem verify_claim_conditional_walk_spec
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W verifyClaim [digestValue d] [] value heap calls)
    {bytes : ByteArray} {c : Ix.Claim} (hde : Ix.Claim.de bytes = .ok c)
    (hpack : packDigest (Address.blake3Pure bytes) = d)
    {assumed : Bool} (hscope : InScopeConditionalTyping assumed c)
    {V : View} {seeds asms : List _root_.Address}
    (hseeds : ShardClaimSeeds c V seeds)
    (hasms : ShardClaimAssumptions c V asms)
    {ctx : Ix.ClaimContext} (hctx : c.context? = some ctx) {tb : ByteArray}
    {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ = .ok t) :
    V.HashedCollision (bytes :: tb :: committedFootprint) calls ∨
    CondShardWalk calls ctx.binding t (if assumed then none else some 77) seeds asms := by
  obtain ⟨cs_run, ev_run, hc_top⟩ := Obs.«IxVM::verify_claim».obs ev
  have hsub_run : ∀ cl ∈ cs_run, cl ∈ calls := fun cl hcl => by rw [hc_top]; simp [hcl]
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.run_claim.lookup
    (by simp [IxVM.KernelClaim.run_claim, ControlLower.hasControl]) ev_run
  simp only [IxVM.KernelClaim.run_claim] at d0
  -- 1. `let (idx, len) = hint::<(Field, Field)>("ixvm.io.claim", digest);`
  obtain ⟨v_hint, m_hint, bs_hint, c_hint, c1, d_hint, mt_hint, d1, rfl⟩ := d0.letValue_inv
  obtain ⟨_, _, d_harg, _, rfl⟩ := d_hint.hint_inv
  obtain ⟨_, rfl, rfl⟩ := d_harg.var_inv
  obtain ⟨_, -, -, ml_hint⟩ := matchPattern_tuple_inv mt_hint
  obtain ⟨x_idx, _, _, _, rfl, mt_idx, ml_hint1, rfl⟩ := matchListWith_cons_inv ml_hint
  obtain rfl := matchPattern_bind_inv mt_idx
  obtain ⟨x_len, _, _, _, rfl, mt_len, ml_hint2, rfl⟩ := matchListWith_cons_inv ml_hint1
  obtain rfl := matchPattern_bind_inv mt_len
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_hint2
  -- 2. `let bytes = IxByteStream::read_finite_byte_stream(0, idx, len);`
  obtain ⟨x_bytes, m_read, bs_read, c_read, c2, d_read, mt_read, d2, rfl⟩ := d1.letValue_inv
  obtain ⟨_, _, _, cs_read, a_read, ev_read, rfl⟩ := d_read.call_inv
  rw [instanceName_plain_some] at ev_read
  obtain ⟨_, _, _, _, _, rfl, d_r0, a_read1, rfl⟩ := a_read.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := d_r0.literal_inv
  obtain ⟨_, _, _, _, _, rfl, d_r1, a_read2, rfl⟩ := a_read1.cons_inv
  obtain ⟨l_r1, rfl, rfl⟩ := d_r1.var_inv; simp at l_r1; subst l_r1
  obtain ⟨_, _, _, _, _, rfl, d_r2, a_read3, rfl⟩ := a_read2.cons_inv
  obtain ⟨l_r2, rfl, rfl⟩ := d_r2.var_inv; simp at l_r2; subst l_r2
  obtain ⟨rfl, rfl, rfl⟩ := a_read3.nil_inv
  obtain rfl := matchPattern_bind_inv mt_read
  obtain ⟨_, rawBytes, hraw_lt, -, hst_raw⟩ := Ingress.read_finite_byte_stream_spec ev_read
  -- 3. `let h = Blake3::hash(bytes);`
  obtain ⟨x_h, m_hash, bs_hash, c_hash, c3, d_hash, mt_hash, d3, rfl⟩ := d2.letValue_inv
  obtain ⟨_, _, _, cs_hash, a_hash, ev_hash, rfl⟩ := d_hash.call_inv
  rw [instanceName_plain_some] at ev_hash
  obtain ⟨_, _, _, _, _, rfl, d_h0, a_hash1, rfl⟩ := a_hash.cons_inv
  obtain ⟨l_h0, rfl, rfl⟩ := d_h0.var_inv; simp at l_h0; subst l_h0
  obtain ⟨rfl, rfl, rfl⟩ := a_hash1.nil_inv
  obtain rfl := matchPattern_bind_inv mt_hash
  obtain ⟨ext_hash, rfl, hcv_raw⟩ :=
    Ingress.hash_digest_spec hst_raw (Ingress.native_of_lt hraw_lt) ev_hash
  have hhashed_raw : Hashed calls ⟨rawBytes.toArray⟩ :=
    Ingress.hashed_of_call (hsub_run _ (by simp [instanceName_plain_some])) hst_raw
  -- 4. `assert_eq!(Blake3::pack_digest(h), digest, ...);`
  obtain ⟨_, m_eq1, bs_eq1, c_eq1, c4, d_eq1, mt_eq1, d4, rfl⟩ := d3.letValue_inv
  obtain ⟨_, a_eq1, ap_eq1⟩ := d_eq1.builtin_inv
  obtain ⟨v_pd, _, m_pd, _, _, rfl, d_pd, a_eq1', rfl⟩ := a_eq1.cons_inv
  obtain ⟨_, _, _, cs_pd, a_pd, ev_pd, rfl⟩ := d_pd.call_inv
  rw [instanceName_plain_some] at ev_pd
  obtain ⟨_, _, _, _, _, rfl, d_pd0, a_pd1, rfl⟩ := a_pd.cons_inv
  obtain ⟨l_pd0, rfl, rfl⟩ := d_pd0.var_inv; simp at l_pd0; subst l_pd0
  obtain ⟨rfl, rfl, rfl⟩ := a_pd1.nil_inv
  obtain ⟨_, _, _, _, _, rfl, d_dig, a_eq1'', rfl⟩ := a_eq1'.cons_inv
  obtain ⟨l_dig, rfl, rfl⟩ := d_dig.var_inv; simp at l_dig; subst l_dig
  obtain ⟨rfl, rfl, rfl⟩ := a_eq1''.nil_inv
  obtain ⟨heq_pd, rfl⟩ := Builtin.assertEq_inv ap_eq1
  obtain rfl := matchPattern_wildcard_inv mt_eq1
  obtain ⟨hv_pd, rfl⟩ := Claim.pack_digest_spec ev_pd
  rw [hv_pd, hcv_raw] at heq_pd
  have hblk_eq : Address.blake3Pure ⟨rawBytes.toArray⟩ = Address.blake3Pure bytes := by
    apply Claim.packDigest_inj (cond_blake3Pure_hash_size _) (cond_blake3Pure_hash_size _)
    have hp := Claim.digestValue_inj heq_pd
    rw [← hpack] at hp
    rw [Ingress.blake3Pure_eq]
    exact hp
  by_cases heq_bytes : (⟨rawBytes.toArray⟩ : ByteArray) = bytes
  case neg =>
    exact .inl (.inl ⟨Address.blake3Pure bytes, bytes, ⟨rawBytes.toArray⟩,
      .inr (.inl ⟨by simp, rfl⟩), hhashed_raw, heq_bytes, hblk_eq⟩)
  rw [← heq_bytes] at hde
  have hget_top : ∃ st_end, Ix.Claim.get { idx := 0, bytes := ⟨rawBytes.toArray⟩ } = .ok c st_end := by
    unfold Ix.Claim.de Ixon.runGetExact EStateM.run at hde
    cases hres : Ix.Claim.get { idx := 0, bytes := ⟨rawBytes.toArray⟩ } with
    | error e s => simp [hres] at hde
    | ok c' s =>
      simp only [hres] at hde
      by_cases hidx : s.idx = (ByteArray.mk rawBytes.toArray).size
      · simp [hidx] at hde; subst hde; exact ⟨s, rfl⟩
      · simp [hidx] at hde
  obtain ⟨st_end, hget_claim⟩ := hget_top
  -- 5. `let (tag, s) = IxonDeserialize::get_tagn4(bytes);`
  obtain ⟨v_tagn, m_tagn, bs_tagn, c_tagn, c5, d_tagn, mt_tagn, d5, rfl⟩ := d4.letValue_inv
  obtain ⟨_, _, _, cs_tagn, a_tagn, ev_tagn, rfl⟩ := d_tagn.call_inv
  rw [instanceName_plain_some] at ev_tagn
  obtain ⟨_, _, _, _, _, rfl, d_tn0, a_tn1, rfl⟩ := a_tagn.cons_inv
  obtain ⟨l_tn0, rfl, rfl⟩ := d_tn0.var_inv; simp at l_tn0; subst l_tn0
  obtain ⟨rfl, rfl, rfl⟩ := a_tn1.nil_inv
  obtain ⟨_, hv_tagn, -, ml_tagn⟩ := matchPattern_tuple_inv mt_tagn
  subst hv_tagn
  obtain ⟨x_tag0, _, _, _, rfl, mt_tag0, ml_tagn1, rfl⟩ := matchListWith_cons_inv ml_tagn
  obtain rfl := matchPattern_bind_inv mt_tag0
  obtain ⟨x_s0, _, _, _, rfl, mt_s0, ml_tagn2, rfl⟩ := matchListWith_cons_inv ml_tagn1
  obtain rfl := matchPattern_bind_inv mt_s0
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_tagn2
  obtain ⟨rfl, tag, n1, restPtr1, hok_tag, hs_n1, htagn_tup⟩ :=
    TagN.getTagN4_refines_at (i := 0) (by simpa using Ingress.Stream.mono ext_hash hst_raw) ev_tagn.erase
  simp only [Nat.zero_add] at hok_tag hs_n1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htagn_tup
  obtain ⟨rfl, rfl⟩ := htagn_tup
  -- 6. `let (flag, size) = tag;`
  obtain ⟨v_ft, m_ft, bs_ft, c_ft, c6, d_ft, mt_ft, d6, rfl⟩ := d5.letValue_inv
  obtain ⟨l_ft, rfl, rfl⟩ := d_ft.var_inv; simp at l_ft
  obtain ⟨_, hv_ft, -, ml_ft⟩ := matchPattern_tuple_inv mt_ft
  rw [← l_ft] at hv_ft
  simp only [Value.tuple.injEq] at hv_ft
  subst hv_ft
  obtain ⟨x_flag, _, _, _, hxf, mt_flag, ml_ft1, rfl⟩ := matchListWith_cons_inv ml_ft
  obtain rfl := matchPattern_bind_inv mt_flag
  obtain ⟨x_size, _, _, _, hxs, mt_size, ml_ft2, rfl⟩ := matchListWith_cons_inv ml_ft1
  obtain rfl := matchPattern_bind_inv mt_size
  obtain ⟨_, rfl⟩ := matchListWith_nil_inv ml_ft2
  simp only [List.cons.injEq] at hxf
  obtain ⟨rfl, hxf'⟩ := hxf
  rw [← hxf'] at hxs
  simp only [List.cons.injEq] at hxs
  obtain ⟨rfl, _⟩ := hxs
  -- 7. `assert_eq!(flag, 14, ...);`
  obtain ⟨_, m_eq2, bs_eq2, c_eq2, c7, d_eq2, mt_eq2, d7, rfl⟩ := d6.letValue_inv
  have ext_eq2 := d_eq2.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq2
  -- 8. `let [_, sz1, sz2, sz3, sz4, sz5, sz6, sz7] = size;`
  obtain ⟨_, m_sz, bs_sz, c_sz, c8, d_sz, mt_sz, d8, rfl⟩ := d7.letValue_inv
  obtain ⟨l_sz0, rfl, rfl⟩ := d_sz.var_inv; simp at l_sz0
  obtain ⟨_, hv_sz, -, ml_sz0⟩ := matchPattern_array_inv mt_sz
  rw [← l_sz0, TagN.u64Value] at hv_sz
  simp only [Value.tuple.injEq] at hv_sz
  subst hv_sz
  obtain ⟨_, _, _, _, hsz0, mt_w0, ml_sz1, rfl⟩ := matchListWith_cons_inv ml_sz0
  obtain rfl := matchPattern_wildcard_inv mt_w0
  obtain ⟨sz1, _, _, _, hsz1, mt_w1, ml_sz2, rfl⟩ := matchListWith_cons_inv ml_sz1
  obtain rfl := matchPattern_bind_inv mt_w1
  obtain ⟨sz2, _, _, _, hsz2, mt_w2, ml_sz3, rfl⟩ := matchListWith_cons_inv ml_sz2
  obtain rfl := matchPattern_bind_inv mt_w2
  obtain ⟨sz3, _, _, _, hsz3, mt_w3, ml_sz4, rfl⟩ := matchListWith_cons_inv ml_sz3
  obtain rfl := matchPattern_bind_inv mt_w3
  obtain ⟨sz4, _, _, _, hsz4, mt_w4, ml_sz5, rfl⟩ := matchListWith_cons_inv ml_sz4
  obtain rfl := matchPattern_bind_inv mt_w4
  obtain ⟨sz5, _, _, _, hsz5, mt_w5, ml_sz6, rfl⟩ := matchListWith_cons_inv ml_sz5
  obtain rfl := matchPattern_bind_inv mt_w5
  obtain ⟨sz6, _, _, _, hsz6, mt_w6, ml_sz7, rfl⟩ := matchListWith_cons_inv ml_sz6
  obtain rfl := matchPattern_bind_inv mt_w6
  obtain ⟨sz7, _, _, _, hsz7, mt_w7, ml_sz8, rfl⟩ := matchListWith_cons_inv ml_sz7
  obtain rfl := matchPattern_bind_inv mt_w7
  obtain ⟨_, rfl⟩ := matchListWith_nil_inv ml_sz8
  -- 9. `assert_eq!(sz1 + ... + sz7, 0, ...);`
  obtain ⟨_, m_eq3, bs_eq3, c_eq3, c9, d_eq3, mt_eq3, d9, rfl⟩ := d8.letValue_inv
  have ext_eq3 := d_eq3.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq3
  -- 10. `let variant = size[0];`
  obtain ⟨x_variant, m_var, bs_var, c_var, c10, d_var, mt_var, d10, rfl⟩ := d9.letValue_inv
  obtain ⟨p_sz, d_szv, pr_sz0⟩ := d_var.index_inv
  obtain ⟨l_szv, rfl, rfl⟩ := d_szv.var_inv; simp at l_szv; subst l_szv
  obtain rfl := matchPattern_bind_inv mt_var
  -- 11. `let (format, s) = IxonDeserialize::read_byte(s);`
  obtain ⟨v_fmt, m_fmt, bs_fmt, c_fmt, c11, d_fmt, mt_fmt, d11, rfl⟩ := d10.letValue_inv
  obtain ⟨_, _, _, cs_fmt, a_fmt, ev_fmt, rfl⟩ := d_fmt.call_inv
  rw [instanceName_plain_some] at ev_fmt
  obtain ⟨_, _, _, _, _, rfl, d_f0, a_f1, rfl⟩ := a_fmt.cons_inv
  obtain ⟨l_f0, rfl, rfl⟩ := d_f0.var_inv; simp at l_f0; subst l_f0
  obtain ⟨rfl, rfl, rfl⟩ := a_f1.nil_inv
  obtain ⟨_, hv_fmt, -, ml_fmt⟩ := matchPattern_tuple_inv mt_fmt
  subst hv_fmt
  obtain ⟨x_fmt, _, _, _, rfl, mt_xfmt, ml_fmt1, rfl⟩ := matchListWith_cons_inv ml_fmt
  obtain rfl := matchPattern_bind_inv mt_xfmt
  obtain ⟨x_s1, _, _, _, rfl, mt_xs1, ml_fmt2, rfl⟩ := matchListWith_cons_inv ml_fmt1
  obtain rfl := matchPattern_bind_inv mt_xs1
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_fmt2
  obtain ⟨rfl, fmtByte, restFmt, _, hcons_fmt, hs_fmt, htup_fmt⟩ :=
    Deserialize.readByte_refines (Ingress.Stream.mono (ext_eq2.trans ext_eq3) hs_n1) ev_fmt.erase
  injection htup_fmt with htup_fmt'; simp only [List.cons.injEq, and_true] at htup_fmt'
  obtain ⟨rfl, rfl⟩ := htup_fmt'
  obtain ⟨hu8_fmt, hdrop_fmt, -⟩ := Deserialize.getU8_of_drop_cons hcons_fmt
  rw [← hdrop_fmt] at hs_fmt
  -- 12. `assert_eq!(UInt8::to_field(format), 4, ...);`
  obtain ⟨_, m_eq4, bs_eq4, c_eq4, c12, d_eq4, mt_eq4, d12, rfl⟩ := d11.letValue_inv
  have ext_eq4 := d_eq4.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq4
  -- 13. `let (validator, s) = IxonDeserialize::read_byte(s);`
  obtain ⟨v_val, m_val, bs_val, c_val, c13, d_val, mt_val, d13, rfl⟩ := d12.letValue_inv
  obtain ⟨_, _, _, cs_val, a_val, ev_val, rfl⟩ := d_val.call_inv
  rw [instanceName_plain_some] at ev_val
  obtain ⟨_, _, _, _, _, rfl, d_v0, a_v1, rfl⟩ := a_val.cons_inv
  obtain ⟨l_v0, rfl, rfl⟩ := d_v0.var_inv; simp at l_v0; subst l_v0
  obtain ⟨rfl, rfl, rfl⟩ := a_v1.nil_inv
  obtain ⟨_, hv_val, -, ml_val⟩ := matchPattern_tuple_inv mt_val
  subst hv_val
  obtain ⟨x_val, _, _, _, rfl, mt_xval, ml_val1, rfl⟩ := matchListWith_cons_inv ml_val
  obtain rfl := matchPattern_bind_inv mt_xval
  obtain ⟨x_s2, _, _, _, rfl, mt_xs2, ml_val2, rfl⟩ := matchListWith_cons_inv ml_val1
  obtain rfl := matchPattern_bind_inv mt_xs2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_val2
  obtain ⟨rfl, valByte, restVal, _, hcons_val, hs_val, htup_val⟩ :=
    Deserialize.readByte_refines (Ingress.Stream.mono ext_eq4 hs_fmt) ev_val.erase
  injection htup_val with htup_val'; simp only [List.cons.injEq, and_true] at htup_val'
  obtain ⟨rfl, rfl⟩ := htup_val'
  obtain ⟨hu8_val, hdrop_val, -⟩ := Deserialize.getU8_of_drop_cons hcons_val
  rw [← hdrop_val] at hs_val
  rw [Nat.add_assoc] at hu8_val hs_val
  -- Align `Ix.Claim.get` through `getTagN 4` and `getScope`
  unfold Ix.Claim.get at hget_claim
  simp only [bind, EStateM.bind, pure, EStateM.pure, hok_tag] at hget_claim
  by_cases hflag_ne : (tag.flag != Ix.Claim.FLAG_CLAIM) = true
  · simp [hflag_ne, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hget_claim
  simp only [hflag_ne, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hget_claim
  by_cases hret9 : (tag.value == Ix.Claim.VARIANT_RESOURCE_CLAIM_RETIRED) = true
  · simp [hret9, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hget_claim
  simp only [hret9, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hget_claim
  obtain ⟨w_val, st_scope, hok_scope, hok_payload⟩ := Ixon.Verify.TagN.bind_ok_inv hget_claim
  obtain ⟨hw_val, rfl, hval_ok⟩ := cond_getScope_ok_inv hu8_fmt hu8_val hok_scope
  subst w_val
  have hvar_45 := cond_getPayload_variant hok_payload hscope
  -- 14. `match UInt8::to_field(variant) { ... }`
  obtain ⟨v_scrut, m_scrut, bs_arm, body_arm, c_scrut, c_arm, d_scrut, sel_arm, d_arm, rfl⟩ :=
    d13.matchValue_inv
  obtain ⟨_, _, _, cs_scrut, a_scrut, ev_scrut, rfl⟩ := d_scrut.call_inv
  rw [instanceName_plain_some] at ev_scrut
  obtain ⟨_, _, _, _, _, rfl, d_sc0, a_sc1, rfl⟩ := a_scrut.cons_inv
  obtain ⟨l_sc0, rfl, rfl⟩ := d_sc0.var_inv; simp at l_sc0; subst l_sc0
  obtain ⟨rfl, rfl, rfl⟩ := a_sc1.nil_inv
  obtain ⟨hv_scrut, hm_scrut⟩ := Ingress.u8_toField ev_scrut
  subst v_scrut m_scrut
  have hsub_arm : ∀ cl ∈ c_arm, cl ∈ calls := fun cl hcl =>
    hsub_run cl (by simp [hcl])
  have hlen_arm : c_arm.length ≤ calls.length := by
    rw [hc_top]
    simp only [List.length_cons, List.length_append]
    omega
  rcases hvar_45 with htv4 | htv5
  · -- Variant 4 (`Ix.Claim.check`)
    rw [htv4] at pr_sz0 hok_payload hval_ok
    change projectValue (TagN.u64Value 4) 0 = .ok x_variant at pr_sz0
    simp only [TagN.u64Value, projectValue, List.getElem?_cons_zero, pure, Except.pure,
      Except.ok.injEq] at pr_sz0
    subst x_variant
    rcases selectArm_cons_inv sel_arm with ⟨mt3, _⟩ | ⟨_, sel_arm1⟩
    · obtain ⟨heq34, _⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt3
      simp at heq34
      exact absurd heq34 (by decide)
    rcases selectArm_cons_inv sel_arm1 with ⟨mt4, rfl⟩ | ⟨nm4, _⟩
    case inr =>
      exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal 4) nm4)
    obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 4) mt4
    -- `match UInt8::to_field(validator) { 10 => ..., 11 => ..., _ => ... }`
    obtain ⟨v_vsc, m_vsc, bs_varm, body_varm, c_vsc, c_varm, d_vsc, sel_varm, d_arm, rfl⟩ :=
      d_arm.matchValue_inv
    obtain ⟨_, _, _, cs_vsc, a_vsc, ev_vsc, rfl⟩ := d_vsc.call_inv
    rw [instanceName_plain_some] at ev_vsc
    obtain ⟨_, _, _, _, _, rfl, d_vsc0, a_vsc1, rfl⟩ := a_vsc.cons_inv
    obtain ⟨l_vsc0, rfl, rfl⟩ := d_vsc0.var_inv; simp at l_vsc0; subst l_vsc0
    obtain ⟨rfl, rfl, rfl⟩ := a_vsc1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_vsc
    have hsub_varm : ∀ cl ∈ c_varm, cl ∈ calls := fun cl hcl =>
      hsub_arm cl (by simp [hcl])
    have hlen_varm : c_varm.length ≤ calls.length := by
      simp only [List.length_cons, List.length_append, List.length_nil] at hlen_arm
      omega
    rcases selectArm_cons_inv sel_varm with ⟨mt10, _⟩ | ⟨_, sel_varm1⟩
    · obtain ⟨heq10, _⟩ := MatchesConst.some_inv (MatchesConst.literal 10) mt10
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq10) (by decide)
    rcases selectArm_cons_inv sel_varm1 with ⟨mt11, _⟩ | ⟨_, sel_varm2⟩
    · obtain ⟨heq11, _⟩ := MatchesConst.some_inv (MatchesConst.literal 11) mt11
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq11) (by decide)
    rcases selectArm_cons_inv sel_varm2 with ⟨mt_w, rfl⟩ | ⟨nm_w, _⟩
    case inr => exact (matchPattern_wildcard_none nm_w).elim
    obtain rfl := matchPattern_wildcard_inv mt_w
    -- Arm 4 body:
    obtain ⟨_, m_ctx, bs_ctx, c_ctx, ca1, d_ctx, mt_ctx, da1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs_ctx, a_ctx, ev_ctx, rfl⟩ := d_ctx.call_inv
    rw [instanceName_plain_some] at ev_ctx
    obtain ⟨_, _, _, _, _, rfl, d_cx0, a_cx1, rfl⟩ := a_ctx.cons_inv
    obtain ⟨l_cx0, rfl, rfl⟩ := d_cx0.var_inv; simp at l_cx0; subst l_cx0
    obtain ⟨rfl, rfl, rfl⟩ := a_cx1.nil_inv
    obtain ⟨_, hv_ctx, -, ml_ctx⟩ := matchPattern_tuple_inv mt_ctx
    subst hv_ctx
    obtain ⟨x_binding, _, _, _, rfl, mt_xb, ml_ctx1, rfl⟩ := matchListWith_cons_inv ml_ctx
    obtain rfl := matchPattern_bind_inv mt_xb
    obtain ⟨x_axioms, _, _, _, rfl, mt_xax, ml_ctx2, rfl⟩ := matchListWith_cons_inv ml_ctx1
    obtain rfl := matchPattern_bind_inv mt_xax
    obtain ⟨x_s3, _, _, _, rfl, mt_xs3, ml_ctx3, rfl⟩ := matchListWith_cons_inv ml_ctx2
    obtain rfl := matchPattern_bind_inv mt_xs3
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_ctx3
    obtain ⟨ext_ctx, ctx₀, kCtx, _, _, _, hget_ctx, htup_ctx, haddr_bind, hax_none, hs_ctx⟩ :=
      Claim.get_claim_context_spec hs_val ev_ctx
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ctx
    obtain ⟨rfl, rfl, rfl⟩ := htup_ctx
    obtain ⟨x_rc, m_rc, bs_rc, c_rc, ca2, d_rc, mt_rc, da2, rfl⟩ := da1.letValue_inv
    obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, rfl⟩ := d_rc.call_inv
    rw [instanceName_plain_some] at ev_rc
    obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
    obtain ⟨l_rc0, rfl, rfl⟩ := d_rc0.var_inv; simp at l_rc0; subst l_rc0
    obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
    obtain ⟨_, _, _, cs_rc_v, a_rc_v, ev_rc_v, rfl⟩ := d_rc1.call_inv
    rw [instanceName_plain_some] at ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rcv0, a_rcv1, rfl⟩ := a_rc_v.cons_inv
    obtain ⟨l_rcv0, rfl, rfl⟩ := d_rcv0.var_inv; simp at l_rcv0; subst l_rcv0
    obtain ⟨rfl, rfl, rfl⟩ := a_rcv1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rc2, a_rc3, rfl⟩ := a_rc2.cons_inv
    obtain ⟨l_rc2, rfl, rfl⟩ := d_rc2.var_inv; simp at l_rc2; subst l_rc2
    obtain ⟨rfl, rfl, rfl⟩ := a_rc3.nil_inv
    obtain rfl := matchPattern_bind_inv mt_rc
    obtain ⟨_, m_tgt, bs_tgt, c_tgt, ca3, d_tgt, mt_tgt, da3, rfl⟩ := da2.letValue_inv
    obtain ⟨_, _, _, cs_tgt, a_tgt, ev_tgt, rfl⟩ := d_tgt.call_inv
    rw [instanceName_plain_some] at ev_tgt
    obtain ⟨_, _, _, _, _, rfl, d_tg0, a_tg1, rfl⟩ := a_tgt.cons_inv
    obtain ⟨l_tg0, rfl, rfl⟩ := d_tg0.var_inv; simp at l_tg0; subst l_tg0
    obtain ⟨rfl, rfl, rfl⟩ := a_tg1.nil_inv
    obtain ⟨_, hv_tgt, -, ml_tgt⟩ := matchPattern_tuple_inv mt_tgt
    subst hv_tgt
    obtain ⟨x_target, _, _, _, rfl, mt_xt, ml_tgt1, rfl⟩ := matchListWith_cons_inv ml_tgt
    obtain rfl := matchPattern_bind_inv mt_xt
    obtain ⟨x_s4, _, _, _, rfl, mt_xs4, ml_tgt2, rfl⟩ := matchListWith_cons_inv ml_tgt1
    obtain rfl := matchPattern_bind_inv mt_xs4
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_tgt2
    obtain ⟨_, m_asm, bs_asm, c_asm, ca4, d_asm, mt_asm, da4, rfl⟩ := da3.letValue_inv
    obtain ⟨_, _, _, cs_asm, a_asm, ev_asm, rfl⟩ := d_asm.call_inv
    rw [instanceName_plain_some] at ev_asm
    obtain ⟨_, _, _, _, _, rfl, d_as0, a_as1, rfl⟩ := a_asm.cons_inv
    obtain ⟨l_as0, rfl, rfl⟩ := d_as0.var_inv; simp at l_as0; subst l_as0
    obtain ⟨rfl, rfl, rfl⟩ := a_as1.nil_inv
    obtain ⟨_, hv_asm, -, ml_asm⟩ := matchPattern_tuple_inv mt_asm
    subst hv_asm
    obtain ⟨x_asm, _, _, _, rfl, mt_xasm, ml_asm1, rfl⟩ := matchListWith_cons_inv ml_asm
    obtain rfl := matchPattern_bind_inv mt_xasm
    obtain ⟨x_rest, _, _, _, rfl, mt_xrest, ml_asm2, rfl⟩ := matchListWith_cons_inv ml_asm1
    obtain rfl := matchPattern_bind_inv mt_xrest
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_asm2
    obtain ⟨_, m_nil, bs_nil, c_nil, ca5, d_nil, mt_nil, da5, rfl⟩ := da4.letValue_inv
    obtain ⟨_, d_nil_v, _⟩ := d_nil.load_inv
    obtain ⟨_, hm_nil, rfl⟩ := d_nil_v.var_inv; subst m_nil
    obtain ⟨_, _, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
    obtain ⟨v_ac, m_ac, bs_ac, c_ac, ca6, d_ac, mt_ac, da6, rfl⟩ := da5.letValue_inv
    obtain ⟨_, m_acargs, _, cs_ac, a_ac, ev_ac, rfl⟩ := d_ac.call_inv
    rw [instanceName_plain_some] at ev_ac
    obtain ⟨_, _, m_ac0, _, _, rfl, d_ac0, a_ac1, rfl⟩ := a_ac.cons_inv
    obtain ⟨l_ac0, hm_ac0, rfl⟩ := d_ac0.var_inv; simp at l_ac0; subst l_ac0; subst m_ac0
    obtain ⟨_, _, m_ac1, _, _, rfl, d_ac1, a_ac2, rfl⟩ := a_ac1.cons_inv
    obtain ⟨l_ac1, hm_ac1, rfl⟩ := d_ac1.var_inv; simp at l_ac1; subst l_ac1; subst m_ac1
    obtain ⟨rfl, hm_ac2, rfl⟩ := a_ac2.nil_inv; subst m_acargs
    obtain rfl := matchPattern_wildcard_inv mt_ac
    obtain ⟨v_mw, m_mw, bs_mw, c_mw, ca7, d_mw, mt_mw, _, rfl⟩ := da6.letValue_inv
    obtain rfl := matchPattern_wildcard_inv mt_mw
    obtain ⟨_, m_asm_sc, bs_asm_m, body_asm_m, _, c_asm_body, d_asm_sc, sel_asm, d_asm_body, rfl⟩ :=
      d_mw.matchValue_inv
    obtain ⟨l_asm_sc, hm_asm_sc, rfl⟩ := d_asm_sc.var_inv; simp at l_asm_sc; subst l_asm_sc; subst m_asm_sc
    -- Align `getPayload 4 valByte`
    have ext_rc0 := ev_rc.heap_extends
    obtain ⟨ext_tgt, hlen_tgt, _, _, htup_tgt, haddr_tgt, hs_tgt⟩ :=
      Deserialize.getAddress_refines (Ingress.Stream.mono ext_rc0 hs_ctx) ev_tgt.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_tgt
    obtain ⟨rfl, rfl⟩ := htup_tgt
    rw [List.drop_drop] at hs_tgt
    have hget_tgt := Claim.getAddress_of_drop hlen_tgt
    obtain ⟨ext_asm, optAsm, kAsm, _, _, hget_asm, htup_asm, hopt_asm, _⟩ :=
      Claim.get_opt_addr_spec hs_tgt ev_asm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_asm
    obtain ⟨rfl, rfl⟩ := htup_asm
    unfold Ix.Claim.getPayload at hok_payload
    have hv3_f : (4 == Ix.Claim.VARIANT_EVAL_CLAIM) = false := rfl
    have hv4_t : (4 == Ix.Claim.VARIANT_CHECK_CLAIM) = true := rfl
    simp only [hv3_f, hv4_t, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure,
      EStateM.pure, hget_ctx, hget_tgt, hget_asm] at hok_payload
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok_payload
    obtain ⟨hctx_ax, -, hctx_ass⟩ := hscope
    dsimp only at hctx_ax hctx_ass
    have hx_ax := hax_none hctx_ax
    rw [hx_ax] at ev_rc
    simp only [Ix.Claim.context?, Option.some.injEq] at hctx
    have hb_eq : ctx.binding = ctx₀.binding := by rw [← hctx]
    rw [← hb_eq] at haddr_bind
    rcases Claim.load_role_ctx_lim_spec (V := V)
        (extra := bytes :: tb :: committedFootprint)
        hadm (by simp) haddr_bind ev_rc with hcoll | ⟨_, hok_rc⟩
    · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
        (fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    have hrc_rep := rcLim_of_assumed hctx_ass hok_rc
    have ha_tgt_asm : BaseSeams.addr m_asm x_target (ixAddr (Deserialize.takeAddress _ hlen_tgt)) :=
      ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext_asm haddr_tgt, rfl⟩
    obtain ⟨ext_ac, hseed_tgt⟩ :=
      Claim.assert_claimable_lim_spec (hrc_rep.mono (ext_tgt.trans ext_asm)) ha_tgt_asm ev_ac
    have hseeds_eq : seeds = [ixAddr (Deserialize.takeAddress _ hlen_tgt)] := hseeds
    cases optAsm with
    | none =>
      dsimp only at hopt_asm hasms
      subst hopt_asm
      have hasms_eq : asms = [] := hasms
      subst hasms_eq
      rcases selectArm_cons_inv sel_asm with ⟨mt_none, rfl⟩ | ⟨_, sel_asm1⟩
      · obtain ⟨_, _, -, ml_none⟩ := matchPattern_construct_inv mt_none
        obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_none
        obtain ⟨_, _, _, cs_tr, a_tr, ev_tr, rfl⟩ := d_asm_body.call_inv
        rw [instanceName_plain_some] at ev_tr
        obtain ⟨_, _, _, _, _, rfl, d_tr0, a_tr1, rfl⟩ := a_tr.cons_inv
        obtain ⟨l_tr0, rfl, rfl⟩ := d_tr0.var_inv; simp at l_tr0; subst l_tr0
        obtain ⟨_, _, _, _, _, rfl, d_tr1, a_tr2, rfl⟩ := a_tr1.cons_inv
        obtain ⟨l_tr1, rfl, rfl⟩ := d_tr1.var_inv; simp at l_tr1; subst l_tr1
        obtain ⟨rfl, rfl, rfl⟩ := a_tr2.nil_inv
        obtain ⟨-, recs, hmem, hcl, hdep⟩ := Claim.run_check_transitive_lim_spec
          (hrc_rep.mono (ext_tgt.trans (ext_asm.trans ext_ac)))
          (BaseSeams.addr_mono ext_ac ha_tgt_asm) ev_tr
        have hsub_ac : ∀ cl ∈ cs_ac, cl ∈ calls :=
          fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])
        have hsub_tr : ∀ cl ∈ cs_tr, cl ∈ calls :=
          fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])
        have hle_tr : cs_tr.length ≤ calls.length := by
          simp only [List.length_cons, List.length_append, List.length_nil] at hlen_varm
          omega
        refine .inr ⟨(recs.map CondTopRec.ofTopRec).map (CondTopRec.mono hsub_tr), ?_, ?_,
          (condTopRecsClosed_of_topRecsClosed hcl).mono hsub_tr, ?_⟩
        · intro x hx
          rw [hseeds_eq] at hx
          rcases List.mem_singleton.mp hx with rfl
          rw [map_addr_condTopRec_mono]
          obtain ⟨r0, hr0, hr0a⟩ := List.mem_map.mp hmem
          exact List.mem_map.mpr ⟨CondTopRec.ofTopRec r0, List.mem_map_of_mem hr0, hr0a⟩
        · intro x hx
          rw [hseeds_eq] at hx
          rcases List.mem_singleton.mp hx with rfl
          exact hseed_tgt.mono hsub_ac
        · intro r hr
          obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hr
          obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr1
          have hd := hdep r0 hr0
          simp only [CondTopRec.mono, CondTopRec.ofTopRec]
          omega
      · rcases selectArm_cons_inv sel_asm1 with ⟨mt_some, _⟩ | ⟨_, sel_asm2⟩
        · obtain ⟨_, hv_bad, _, _⟩ := matchPattern_construct_inv mt_some
          injection hv_bad with _ hctor _
          exact absurd hctor (by decide)
        · exact (selectArm_nil_inv sel_asm2).elim
    | some asmRoot =>
      dsimp only at hopt_asm hasms
      obtain ⟨addrPtr, hopt_eq, haddr_asm⟩ := hopt_asm
      subst hopt_eq
      obtain ⟨tAsm, htAsm, hrootAsm, hasms_eq⟩ := hasms
      rcases selectArm_cons_inv sel_asm with ⟨mt_none, _⟩ | ⟨_, sel_asm1⟩
      · obtain ⟨_, hv_bad, _, _⟩ := matchPattern_construct_inv mt_none
        injection hv_bad with _ hctor _
        exact absurd hctor (by decide)
      rcases selectArm_cons_inv sel_asm1 with ⟨mt_some, rfl⟩ | ⟨_, sel_asm2⟩
      case inr => exact (selectArm_nil_inv sel_asm2).elim
      obtain ⟨vs_s, hv_some, -, ml_some⟩ := matchPattern_construct_inv mt_some
      obtain ⟨x_r, _, _, _, rfl, mt_r, ml_some1, rfl⟩ := matchListWith_cons_inv ml_some
      obtain rfl := matchPattern_bind_inv mt_r
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_some1
      injection hv_some with _ _ hargs_some
      injection hargs_some with hxr_eq _
      subst hxr_eq
      -- `let asm_leaves = load_assumption_tree(r);`
      obtain ⟨x_al, m_al, _, c_al, ca_s1, d_al, mt_al, da_s1, rfl⟩ := d_asm_body.letValue_inv
      obtain ⟨_, m_alargs, _, cs_al, a_al, ev_al, rfl⟩ := d_al.call_inv
      rw [instanceName_plain_some] at ev_al
      obtain ⟨_, _, m_al0, _, _, rfl, d_al0, a_al1, rfl⟩ := a_al.cons_inv
      obtain ⟨lal0, hm_al0, rfl⟩ := d_al0.var_inv; simp at lal0; subst lal0; subst m_al0
      obtain ⟨rfl, hm_al1, rfl⟩ := a_al1.nil_inv; subst m_alargs
      obtain rfl := matchPattern_bind_inv mt_al
      -- `let asm_set = addr_set_build(asm_leaves, RBTreeMap::RBTreeMap::Nil);`
      obtain ⟨x_as, m_as, _, c_as, ca_s2, d_as, mt_as, da_s2, rfl⟩ := da_s1.letValue_inv
      obtain ⟨_, m_asargs, _, cs_as, a_as, ev_as, rfl⟩ := d_as.call_inv
      rw [instanceName_plain_some] at ev_as
      obtain ⟨_, _, m_as0, _, _, rfl, d_as0, a_as1, rfl⟩ := a_as.cons_inv
      obtain ⟨las0, hm_as0, rfl⟩ := d_as0.var_inv; simp at las0; subst las0; subst m_as0
      obtain ⟨x_nil, _, m_nil, _, _, rfl, d_nil, a_as2, rfl⟩ := a_as1.cons_inv
      obtain ⟨vs_nil, a_nil, hnil_eq⟩ := d_nil.construct_inv
      obtain ⟨rfl, hm_nil, rfl⟩ := a_nil.nil_inv; subst m_nil
      obtain ⟨rfl, hm_as2, rfl⟩ := a_as2.nil_inv; subst m_asargs
      obtain rfl := matchPattern_bind_inv mt_as
      -- `env_walk(rc, target, RBTreeMap::RBTreeMap::Nil, asm_set, 2)`
      obtain ⟨_, m_ewargs, _, cs_ew, a_ew, ev_ew, rfl⟩ := da_s2.call_inv
      rw [instanceName_plain_some] at ev_ew
      obtain ⟨_, _, m_e0, _, _, rfl, d_e0, a_e1, rfl⟩ := a_ew.cons_inv
      obtain ⟨le0, hm_e0, rfl⟩ := d_e0.var_inv; simp at le0; subst le0; subst m_e0
      obtain ⟨_, _, m_e1, _, _, rfl, d_e1, a_e2, rfl⟩ := a_e1.cons_inv
      obtain ⟨le1, hm_e1, rfl⟩ := d_e1.var_inv; simp at le1; subst le1; subst m_e1
      obtain ⟨x_onil, _, m_onil, _, _, rfl, d_e2, a_e3, rfl⟩ := a_e2.cons_inv
      obtain ⟨_, a_onil, _⟩ := d_e2.construct_inv
      obtain ⟨rfl, hm_onil, rfl⟩ := a_onil.nil_inv; subst m_onil
      obtain ⟨_, _, m_e3, _, _, rfl, d_e3, a_e4, rfl⟩ := a_e3.cons_inv
      obtain ⟨le3, hm_e3, rfl⟩ := d_e3.var_inv; simp at le3; subst le3; subst m_e3
      obtain ⟨_, _, m_e4, _, _, rfl, d_e4, a_e5, rfl⟩ := a_e4.cons_inv
      obtain ⟨rfl, hm_e4, rfl⟩ := d_e4.literal_inv; subst m_e4
      obtain ⟨rfl, hm_e5, rfl⟩ := a_e5.nil_inv; subst m_ewargs
      -- Discharge `load_assumption_tree(r)`
      have hroot_asm : BaseSeams.addr m_ac addrPtr (treeRoot tAsm) := by
        rw [hrootAsm]
        exact BaseSeams.addr_mono ext_ac haddr_asm
      rcases Claim.load_assumption_tree_spec (V := V)
          (extra := bytes :: tb :: committedFootprint) htAsm hroot_asm ev_al with
        hcoll | ⟨ext_al, asAsm, hmapAsm, hlAsm⟩
      · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
          (fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])) hcoll)
      have hnil_rep : Claim.RepAddrSet m_al [] x_nil := by
        rw [hnil_eq]
        have hsym : instanceName [] "RBTreeMap::RBTreeMap" (some [.field]) = addrMapEnum := by
          simpa [instanceName, Ty.subst, Ty.toCore] using Obs.Names.«RBTreeMap::RBTreeMap<Field>».symbol
        simpa only [hsym] using Claim.RepAddrSet.nil m_al
      obtain ⟨ext_as, hset_rev⟩ := Claim.addr_set_build_spec hlAsm hnil_rep ev_as
      have hset : Claim.RepAddrSet m_as asms x_as :=
        repAddrSet_of_iff (fun x => by
          rw [hasms_eq, List.append_nil, ← hmapAsm, List.mem_map, List.mem_map]
          simp [List.mem_reverse]) hset_rev
      have ext_to_ew := ext_ac.trans (ext_al.trans ext_as)
      obtain ⟨-, recs, hmem_or, hcl, hdep⟩ := env_walk_cond_lim_spec
        (hrc_rep.mono (ext_tgt.trans (ext_asm.trans ext_to_ew)))
        (BaseSeams.addr_mono ext_to_ew ha_tgt_asm) hset ev_ew
      have hmem : ixAddr (Deserialize.takeAddress _ hlen_tgt) ∈ recs.map (·.addr) := by
        rcases hmem_or with hm | ⟨-, hne2⟩
        · exact hm
        · exact absurd rfl hne2
      have hsub_ac : ∀ cl ∈ cs_ac, cl ∈ calls :=
        fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])
      have hsub_ew : ∀ cl ∈ cs_ew, cl ∈ calls :=
        fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])
      have hle_ew : cs_ew.length ≤ calls.length := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hlen_varm
        omega
      refine .inr ⟨recs.map (CondTopRec.mono hsub_ew), ?_, ?_, hcl.mono hsub_ew,
        condTopRec_mono_depth_le hsub_ew hdep hle_ew⟩
      · intro x hx
        rw [hseeds_eq] at hx
        rcases List.mem_singleton.mp hx with rfl
        rwa [map_addr_condTopRec_mono]
      · intro x hx
        rw [hseeds_eq] at hx
        rcases List.mem_singleton.mp hx with rfl
        exact hseed_tgt.mono hsub_ac
  · -- Variant 5 (`Ix.Claim.checkEnv`)
    rw [htv5] at pr_sz0 hok_payload hval_ok
    change projectValue (TagN.u64Value 5) 0 = .ok x_variant at pr_sz0
    simp only [TagN.u64Value, projectValue, List.getElem?_cons_zero, pure, Except.pure,
      Except.ok.injEq] at pr_sz0
    subst x_variant
    rcases selectArm_cons_inv sel_arm with ⟨mt3, _⟩ | ⟨_, sel_arm1⟩
    · obtain ⟨heq35, _⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt3
      simp at heq35
      exact absurd heq35 (by decide)
    rcases selectArm_cons_inv sel_arm1 with ⟨mt4, _⟩ | ⟨_, sel_arm2⟩
    · obtain ⟨heq45, _⟩ := MatchesConst.some_inv (MatchesConst.literal 4) mt4
      simp at heq45
      exact absurd heq45 (by decide)
    rcases selectArm_cons_inv sel_arm2 with ⟨mt5, rfl⟩ | ⟨nm5, _⟩
    case inr =>
      exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal 5) nm5)
    obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 5) mt5
    -- `match UInt8::to_field(validator) { 10 => ..., 11 => ..., _ => ... }`
    obtain ⟨v_vsc, m_vsc, bs_varm, body_varm, c_vsc, c_varm, d_vsc, sel_varm, d_arm, rfl⟩ :=
      d_arm.matchValue_inv
    obtain ⟨_, _, _, cs_vsc, a_vsc, ev_vsc, rfl⟩ := d_vsc.call_inv
    rw [instanceName_plain_some] at ev_vsc
    obtain ⟨_, _, _, _, _, rfl, d_vsc0, a_vsc1, rfl⟩ := a_vsc.cons_inv
    obtain ⟨l_vsc0, rfl, rfl⟩ := d_vsc0.var_inv; simp at l_vsc0; subst l_vsc0
    obtain ⟨rfl, rfl, rfl⟩ := a_vsc1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_vsc
    have hsub_varm : ∀ cl ∈ c_varm, cl ∈ calls := fun cl hcl =>
      hsub_arm cl (by simp [hcl])
    have hlen_varm : c_varm.length ≤ calls.length := by
      simp only [List.length_cons, List.length_append, List.length_nil] at hlen_arm
      omega
    rcases selectArm_cons_inv sel_varm with ⟨mt10, _⟩ | ⟨_, sel_varm1⟩
    · obtain ⟨heq10, _⟩ := MatchesConst.some_inv (MatchesConst.literal 10) mt10
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq10) (by decide)
    rcases selectArm_cons_inv sel_varm1 with ⟨mt11, _⟩ | ⟨_, sel_varm2⟩
    · obtain ⟨heq11, _⟩ := MatchesConst.some_inv (MatchesConst.literal 11) mt11
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq11) (by decide)
    rcases selectArm_cons_inv sel_varm2 with ⟨mt_w, rfl⟩ | ⟨nm_w, _⟩
    case inr => exact (matchPattern_wildcard_none nm_w).elim
    obtain rfl := matchPattern_wildcard_inv mt_w
    -- Arm 5 body:
    obtain ⟨_, m_ctx, bs_ctx, c_ctx, ca1, d_ctx, mt_ctx, da1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs_ctx, a_ctx, ev_ctx, rfl⟩ := d_ctx.call_inv
    rw [instanceName_plain_some] at ev_ctx
    obtain ⟨_, _, _, _, _, rfl, d_cx0, a_cx1, rfl⟩ := a_ctx.cons_inv
    obtain ⟨l_cx0, rfl, rfl⟩ := d_cx0.var_inv; simp at l_cx0; subst l_cx0
    obtain ⟨rfl, rfl, rfl⟩ := a_cx1.nil_inv
    obtain ⟨_, hv_ctx, -, ml_ctx⟩ := matchPattern_tuple_inv mt_ctx
    subst hv_ctx
    obtain ⟨x_binding, _, _, _, rfl, mt_xb, ml_ctx1, rfl⟩ := matchListWith_cons_inv ml_ctx
    obtain rfl := matchPattern_bind_inv mt_xb
    obtain ⟨x_axioms, _, _, _, rfl, mt_xax, ml_ctx2, rfl⟩ := matchListWith_cons_inv ml_ctx1
    obtain rfl := matchPattern_bind_inv mt_xax
    obtain ⟨x_s3, _, _, _, rfl, mt_xs3, ml_ctx3, rfl⟩ := matchListWith_cons_inv ml_ctx2
    obtain rfl := matchPattern_bind_inv mt_xs3
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_ctx3
    obtain ⟨ext_ctx, ctx₀, kCtx, _, _, _, hget_ctx, htup_ctx, haddr_bind, hax_none, hs_ctx⟩ :=
      Claim.get_claim_context_spec hs_val ev_ctx
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ctx
    obtain ⟨rfl, rfl, rfl⟩ := htup_ctx
    obtain ⟨x_rc, m_rc, bs_rc, c_rc, ca2, d_rc, mt_rc, da2, rfl⟩ := da1.letValue_inv
    obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, rfl⟩ := d_rc.call_inv
    rw [instanceName_plain_some] at ev_rc
    obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
    obtain ⟨l_rc0, rfl, rfl⟩ := d_rc0.var_inv; simp at l_rc0; subst l_rc0
    obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
    obtain ⟨_, _, _, cs_rc_v, a_rc_v, ev_rc_v, rfl⟩ := d_rc1.call_inv
    rw [instanceName_plain_some] at ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rcv0, a_rcv1, rfl⟩ := a_rc_v.cons_inv
    obtain ⟨l_rcv0, rfl, rfl⟩ := d_rcv0.var_inv; simp at l_rcv0; subst l_rcv0
    obtain ⟨rfl, rfl, rfl⟩ := a_rcv1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rc2, a_rc3, rfl⟩ := a_rc2.cons_inv
    obtain ⟨l_rc2, rfl, rfl⟩ := d_rc2.var_inv; simp at l_rc2; subst l_rc2
    obtain ⟨rfl, rfl, rfl⟩ := a_rc3.nil_inv
    obtain rfl := matchPattern_bind_inv mt_rc
    obtain ⟨_, m_rt, bs_rt, c_rt, ca3, d_rt, mt_rt, da3, rfl⟩ := da2.letValue_inv
    obtain ⟨_, _, _, cs_rt, a_rt, ev_rt, rfl⟩ := d_rt.call_inv
    rw [instanceName_plain_some] at ev_rt
    obtain ⟨_, _, _, _, _, rfl, d_rt0, a_rt1, rfl⟩ := a_rt.cons_inv
    obtain ⟨l_rt0, rfl, rfl⟩ := d_rt0.var_inv; simp at l_rt0; subst l_rt0
    obtain ⟨rfl, rfl, rfl⟩ := a_rt1.nil_inv
    obtain ⟨_, hv_rt, -, ml_rt⟩ := matchPattern_tuple_inv mt_rt
    subst hv_rt
    obtain ⟨x_root, _, _, _, rfl, mt_xrt, ml_rt1, rfl⟩ := matchListWith_cons_inv ml_rt
    obtain rfl := matchPattern_bind_inv mt_xrt
    obtain ⟨x_s4, _, _, _, rfl, mt_xs4, ml_rt2, rfl⟩ := matchListWith_cons_inv ml_rt1
    obtain rfl := matchPattern_bind_inv mt_xs4
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_rt2
    obtain ⟨_, m_asm, bs_asm, c_asm, ca4, d_asm, mt_asm, da4, rfl⟩ := da3.letValue_inv
    obtain ⟨_, _, _, cs_asm, a_asm, ev_asm, rfl⟩ := d_asm.call_inv
    rw [instanceName_plain_some] at ev_asm
    obtain ⟨_, _, _, _, _, rfl, d_as0, a_as1, rfl⟩ := a_asm.cons_inv
    obtain ⟨l_as0, rfl, rfl⟩ := d_as0.var_inv; simp at l_as0; subst l_as0
    obtain ⟨rfl, rfl, rfl⟩ := a_as1.nil_inv
    obtain ⟨_, hv_asm, -, ml_asm⟩ := matchPattern_tuple_inv mt_asm
    subst hv_asm
    obtain ⟨x_asm, _, _, _, rfl, mt_xasm, ml_asm1, rfl⟩ := matchListWith_cons_inv ml_asm
    obtain rfl := matchPattern_bind_inv mt_xasm
    obtain ⟨x_rest, _, _, _, rfl, mt_xrest, ml_asm2, rfl⟩ := matchListWith_cons_inv ml_asm1
    obtain rfl := matchPattern_bind_inv mt_xrest
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_asm2
    obtain ⟨_, m_nil, bs_nil, c_nil, ca5, d_nil, mt_nil, da5, rfl⟩ := da4.letValue_inv
    obtain ⟨_, d_nil_v, _⟩ := d_nil.load_inv
    obtain ⟨_, hm_nil, rfl⟩ := d_nil_v.var_inv; subst m_nil
    obtain ⟨_, _, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
    obtain ⟨v_rce, m_rce, bs_rce, c_rce, ca6, d_rce, mt_rce, _, rfl⟩ := da5.letValue_inv
    obtain ⟨_, m_ceargs, _, cs_rce, a_rce, ev_rce, rfl⟩ := d_rce.call_inv
    rw [instanceName_plain_some] at ev_rce
    obtain ⟨_, _, m_ce0, _, _, rfl, d_ce0, a_ce1, rfl⟩ := a_rce.cons_inv
    obtain ⟨l_ce0, hm_ce0, rfl⟩ := d_ce0.var_inv; simp at l_ce0; subst l_ce0; subst m_ce0
    obtain ⟨_, _, m_ce1, _, _, rfl, d_ce1, a_ce2, rfl⟩ := a_ce1.cons_inv
    obtain ⟨l_ce1, hm_ce1, rfl⟩ := d_ce1.var_inv; simp at l_ce1; subst l_ce1; subst m_ce1
    obtain ⟨_, _, m_ce2, _, _, rfl, d_ce2, a_ce3, rfl⟩ := a_ce2.cons_inv
    obtain ⟨l_ce2, hm_ce2, rfl⟩ := d_ce2.var_inv; simp at l_ce2; subst l_ce2; subst m_ce2
    obtain ⟨rfl, hm_ce3, rfl⟩ := a_ce3.nil_inv; subst m_ceargs
    obtain rfl := matchPattern_wildcard_inv mt_rce
    -- Align `getPayload 5 valByte`
    have ext_rc0 := ev_rc.heap_extends
    obtain ⟨ext_rt, hlen_rt, _, _, htup_rt, haddr_rt, hs_rt⟩ :=
      Deserialize.getAddress_refines (Ingress.Stream.mono ext_rc0 hs_ctx) ev_rt.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_rt
    obtain ⟨rfl, rfl⟩ := htup_rt
    rw [List.drop_drop] at hs_rt
    have hget_rt := Claim.getAddress_of_drop hlen_rt
    obtain ⟨ext_asm, optAsm, kAsm, _, _, hget_asm, htup_asm, hopt_asm, _⟩ :=
      Claim.get_opt_addr_spec hs_rt ev_asm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_asm
    obtain ⟨rfl, rfl⟩ := htup_asm
    unfold Ix.Claim.getPayload at hok_payload
    have hv3_f : (5 == Ix.Claim.VARIANT_EVAL_CLAIM) = false := rfl
    have hv4_f : (5 == Ix.Claim.VARIANT_CHECK_CLAIM) = false := rfl
    have hv5_t : (5 == Ix.Claim.VARIANT_CHECK_ENV_CLAIM) = true := rfl
    simp only [hv3_f, hv4_f, hv5_t, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure,
      EStateM.pure, hget_ctx, hget_rt, hget_asm] at hok_payload
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok_payload
    obtain ⟨hctx_ax, -, hctx_ass⟩ := hscope
    dsimp only at hctx_ax hctx_ass
    have hx_ax := hax_none hctx_ax
    rw [hx_ax] at ev_rc
    simp only [Ix.Claim.context?, Option.some.injEq] at hctx
    have hb_eq : ctx.binding = ctx₀.binding := by rw [← hctx]
    rw [← hb_eq] at haddr_bind
    rcases Claim.load_role_ctx_lim_spec (V := V)
        (extra := bytes :: tb :: committedFootprint)
        hadm (by simp) haddr_bind ev_rc with hcoll | ⟨_, hok_rc⟩
    · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx)
        (fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    have hrc_rep := rcLim_of_assumed hctx_ass hok_rc
    obtain ⟨tOwned, htOwned, hrootOwned, hseeds_eq⟩ := hseeds
    have hroot_addr : BaseSeams.addr m_asm x_root (treeRoot tOwned) :=
      ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext_asm haddr_rt, hrootOwned.symm⟩
    have hsub_rce : ∀ cl ∈ cs_rce, cl ∈ calls :=
      fun cl hcl => hsub_varm cl (by simp [instanceName_plain_some, hcl])
    have hle_rce : cs_rce.length ≤ calls.length := by
      simp only [List.length_cons, List.length_append, List.length_nil] at hlen_varm
      omega
    cases optAsm with
    | none =>
      dsimp only at hopt_asm hasms
      subst hopt_asm
      have hasms_eq : asms = [] := hasms
      subst hasms_eq
      subst hseeds_eq
      have hlim_or : (if assumed then none else some 77) = some 77 ∨
          (if assumed then none else some 77) = none := by
        cases assumed <;> simp
      rcases run_check_env_none_cond_lim_spec (V := V)
          (extra := bytes :: tb :: committedFootprint)
          (b := ⟨ctx.binding, tb⟩) hadm (by simp) hlim_or htOwned
          (hrc_rep.mono (ext_rt.trans ext_asm)) hroot_addr ev_rce with
        hcoll | ⟨recs, hmem, hcl_s, hcl, hdep⟩
      · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx) hsub_rce hcoll)
      · refine .inr ⟨recs.map (CondTopRec.mono hsub_rce), ?_, ?_, hcl.mono hsub_rce,
          condTopRec_mono_depth_le hsub_rce hdep hle_rce⟩
        · intro a ha; rw [map_addr_condTopRec_mono]; exact hmem a ha
        · intro a ha; exact (hcl_s a ha).mono hsub_rce
    | some asmRoot =>
      dsimp only at hopt_asm hasms
      obtain ⟨addrPtr, hopt_eq, haddr_asm⟩ := hopt_asm
      subst hopt_eq
      obtain ⟨tAsm, htAsm, hrootAsm, hasms_eq⟩ := hasms
      subst hseeds_eq
      subst hasms_eq
      have hroot_asm : BaseSeams.addr m_asm addrPtr (treeRoot tAsm) := by
        rw [hrootAsm]; exact haddr_asm
      rcases run_check_env_some_cond_lim_spec (V := V)
          (extra := bytes :: tb :: committedFootprint)
          htOwned htAsm (hrc_rep.mono (ext_rt.trans ext_asm)) hroot_addr hroot_asm ev_rce with
        hcoll | ⟨recs, hmem, hcl_s, hcl, hdep⟩
      · exact .inl (IxVM.Consistency.hashedCollision_mono (fun _ hx => Or.inl hx) hsub_rce hcoll)
      · refine .inr ⟨recs.map (CondTopRec.mono hsub_rce), ?_, ?_, hcl.mono hsub_rce,
          condTopRec_mono_depth_le hsub_rce hdep hle_rce⟩
        · intro a ha; rw [map_addr_condTopRec_mono]; exact hmem a ha
        · intro a ha; exact (hcl_s a ha).mono hsub_rce

/-! ## 5. Merging a Closed Shard Partition into One `Claim.TopWalkCore` -/

private structure MergedRec (allCalls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (lim : Option Nat) (entries : List ShardClaimEntry) where
  shardIdx : Fin entries.length
  topRec : CondTopRec allCalls bAddr t lim (entries[shardIdx.val]).asms

private def globalDepth {allCalls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {entries : List ShardClaimEntry}
    (M : Nat) (m : MergedRec allCalls bAddr t lim entries) : Nat :=
  m.shardIdx.val * M + m.topRec.depth

private noncomputable def mergedRank {allCalls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {entries : List ShardClaimEntry}
    (M : Nat) (merged : List (MergedRec allCalls bAddr t lim entries))
    (a : _root_.Address) : Nat :=
  sInf {d | ∃ m ∈ merged, m.topRec.addr = a ∧ globalDepth M m = d}

private theorem mergedRank_le {allCalls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {entries : List ShardClaimEntry}
    {M : Nat} {merged : List (MergedRec allCalls bAddr t lim entries)}
    {m : MergedRec allCalls bAddr t lim entries} (hm : m ∈ merged) :
    mergedRank M merged m.topRec.addr ≤ globalDepth M m :=
  Nat.sInf_le ⟨m, hm, rfl, rfl⟩

private theorem exists_min_mergedRec {allCalls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {entries : List ShardClaimEntry}
    {M : Nat} {merged : List (MergedRec allCalls bAddr t lim entries)} {a : _root_.Address}
    (ha : ∃ m ∈ merged, m.topRec.addr = a) :
    ∃ m ∈ merged, m.topRec.addr = a ∧ globalDepth M m = mergedRank M merged a := by
  obtain ⟨m, hm, hma⟩ := ha
  exact Nat.sInf_mem
    (s := {d | ∃ m ∈ merged, m.topRec.addr = a ∧ globalDepth M m = d})
    ⟨globalDepth M m, m, hm, hma, rfl⟩

private theorem shardCalls_sub_flatten {shardCalls : List (List (Call F))}
    {k : Nat} (hk : k < shardCalls.length) :
    ∀ cl ∈ shardCalls[k], cl ∈ shardCalls.flatten :=
  fun cl hcl => List.mem_flatten.mpr ⟨shardCalls[k], List.getElem_mem hk, hcl⟩

private theorem shardCalls_length_le_flatten {shardCalls : List (List (Call F))}
    {k : Nat} (hk : k < shardCalls.length) :
    shardCalls[k].length ≤ shardCalls.flatten.length := by
  rw [List.length_flatten]
  exact nat_le_list_sum_of_mem (List.mem_map.mpr ⟨shardCalls[k], List.getElem_mem hk, rfl⟩)

private theorem topWalkCore_of_closedPartition
    {shardCalls : List (List (Call F))}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none)
    {entries : List ShardClaimEntry} (hLen : entries.length = shardCalls.length)
    (hDag : ∀ (k : Nat) (hk : k < entries.length),
      ∀ x ∈ entries[k].asms, ∃ (j : Nat) (hj : j < k),
        x ∈ (entries[j]'(Nat.lt_trans hj hk)).seeds)
    (hWalks : ∀ (k : Nat) (hk : k < entries.length),
      CondShardWalk (shardCalls[k]'(hLen ▸ hk)) b.address t lim entries[k].seeds entries[k].asms)
    (hnoColl : ∀ b₁ b₂ : ByteArray,
      Hashed shardCalls.flatten b₁ → Hashed shardCalls.flatten b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂)
    (hNoBlk : NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries)) :
    ∃ (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
      Claim.TopWalkCore shardCalls.flatten b.address t (ShardClaimEntry.allSeeds entries)
        (Claim.runEnv b (t := t) shardCalls.flatten) lim Top rank := by
  classical
  let allCalls := shardCalls.flatten
  let E₀ := Claim.runEnv b (t := t) allCalls
  let M := allCalls.length + 1
  let recsOf (k : Fin entries.length) :
      List (CondTopRec (shardCalls[k.val]'(hLen ▸ k.isLt)) b.address t lim (entries[k.val]).asms) :=
    Classical.choose (hWalks k.val k.isLt)
  have hRecsSpec (k : Fin entries.length) :
      (∀ a ∈ (entries[k.val]).seeds, a ∈ (recsOf k).map (·.addr)) ∧
      (∀ a ∈ (entries[k.val]).seeds, Claim.ClaimableSeed (shardCalls[k.val]'(hLen ▸ k.isLt)) t a) ∧
      CondTopRecsClosed (recsOf k) ∧
      (∀ r ∈ recsOf k, r.depth ≤ (shardCalls[k.val]'(hLen ▸ k.isLt)).length) :=
    Classical.choose_spec (hWalks k.val k.isLt)
  let hsub (k : Fin entries.length) :
      ∀ cl ∈ shardCalls[k.val]'(hLen ▸ k.isLt), cl ∈ allCalls :=
    shardCalls_sub_flatten (hLen ▸ k.isLt)
  let merged : List (MergedRec allCalls b.address t lim entries) :=
    (List.finRange entries.length).flatMap fun k =>
      (recsOf k).map fun r => ⟨k, r.mono (hsub k)⟩
  have hmem_merged : ∀ (k : Fin entries.length) (r : _), r ∈ recsOf k →
      (⟨k, r.mono (hsub k)⟩ : MergedRec allCalls b.address t lim entries) ∈ merged := by
    intro k r hr
    exact List.mem_flatMap.mpr ⟨k, List.mem_finRange k, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hmerged_inv : ∀ m ∈ merged,
      ∃ r ∈ recsOf m.shardIdx, m.topRec = r.mono (hsub m.shardIdx) := by
    intro m hm
    obtain ⟨k, _, hkm⟩ := List.mem_flatMap.mp hm
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hkm
    cases heq
    exact ⟨r, hr, rfl⟩
  have hdepth_lt_M : ∀ (k : Fin entries.length) (r : _), r ∈ recsOf k → r.depth < M := by
    intro k r hr
    have h1 := (hRecsSpec k).2.2.2 r hr
    have h2 := shardCalls_length_le_flatten (Nat.lt_of_lt_of_eq k.isLt hLen)
    dsimp only [M, allCalls]
    omega
  have hw0 : Claim.WalkedClaim allCalls t E₀ [] :=
    Claim.walkedClaim_envOfRecs (seeds := []) hnoColl [] hadm (by simp) (by intro r hr; cases hr)
  have hload : LoadedBy allCalls E₀ := Claim.envOfRecs_loadedBy b allCalls []
  have hS : LoadedReads.RunStore allCalls E₀ := LoadedReads.RunStore.of_walkedClaim hload hw0
  have hH : LoadedReads.HashedRecordsStored allCalls E₀ :=
    LoadedReads.hashedRecordsStored_of_walkedClaim hw0
  have hrec : ∀ m ∈ merged, recordOf E₀ m.topRec.addr = some m.topRec.c := by
    intro m _
    obtain ⟨lc, hget, hraw, -⟩ :=
      hH m.topRec.rawBytes m.topRec.c m.topRec.hhashed m.topRec.hsz m.topRec.hde m.topRec.hdeExact
    rw [m.topRec.hblake] at hget
    unfold recordOf
    rw [hget]
    simp [hraw, m.topRec.hdeExact, Except.toOption]
  have huniq : ∀ m ∈ merged, ∀ c, recordOf E₀ m.topRec.addr = some c → c = m.topRec.c := by
    intro m hm c hc
    rw [hrec m hm] at hc
    exact (Option.some.inj hc).symm
  have hat : ∀ {a : _root_.Address} {c : Ixon.Constant},
      recordOf E₀ a = some c → Ix.Cert.recordAt E₀ a = some c :=
    fun h => (hS.recordOf_eq_recordAt _).symm.trans h
  have hmin : ∀ a c, (∃ m ∈ merged, m.topRec.addr = a) → recordOf E₀ a = some c →
      ∃ m ∈ merged, m.topRec.addr = a ∧ globalDepth M m = mergedRank M merged a ∧ m.topRec.c = c := by
    intro a c hTa hc
    obtain ⟨m, hm, hma, hmd⟩ := exists_min_mergedRec hTa
    refine ⟨m, hm, hma, hmd, ?_⟩
    subst hma
    exact (huniq m hm c hc).symm
  have huse : ∀ (c : Ixon.Constant) (i : Nat) (x : _root_.Address), i ∈ usedRefIdxs c →
      c.refs[i]? = some x → i ∈ BaseSeams.usedRefIdxs c := by
    intro c i x hi _
    rw [Assembly.usedRefIdxs_eq]
    exact hi
  have hSeedIdx : ∀ a ∈ ShardClaimEntry.allSeeds entries,
      ∃ k : Fin entries.length, a ∈ (entries[k.val]).seeds := by
    intro a ha
    obtain ⟨e, he_mem, ha_e⟩ := List.mem_flatMap.mp ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he_mem
    exact ⟨⟨k, hk⟩, ha_e⟩
  have hClaimableOfSeed : ∀ (k : Fin entries.length) {a : _root_.Address},
      a ∈ (entries[k.val]).seeds → Claim.ClaimableSeed allCalls t a := by
    intro k a ha
    exact ((hRecsSpec k).2.1 a ha).mono (hsub k)
  have hSourceSafeOfClaimable : ∀ {a : _root_.Address},
      Claim.ClaimableSeed allCalls t a → Claim.SourceSafe E₀ a := by
    intro a hcl c hc
    have hout := Claim.claimableSeed_not_outsideLogicAt (b := b) hnoColl
      ([] : List (Claim.WalkedRec allCalls b.address t)) hcl
    refine ⟨?_, fun cb hcb => ?_⟩
    · by_contra hn
      exact hout ⟨c, hat hc, Or.inl hn⟩
    · by_contra hn
      exact hout ⟨c, hat hc, Or.inr ⟨cb, hat hcb, hn⟩⟩
  refine ⟨fun a => ∃ m ∈ merged, m.topRec.addr = a, mergedRank M merged, ?_⟩
  refine
    { topLim := hlim
      table := ⟨b.bytes, by cases b; exact hadm⟩
      runStore := hS
      hashedStored := hH
      seedsTop := ?_
      record := ?_
      closed := ?_
      owner := ?_
      seedLogic := ?_
      seedNotInert := ?_
      checked := ?_
      refsNotInert := ?_
      refsNotBlock := ?_
      safeRefs := ?_
      quotBound := ?_ }
  -- 1. seedsTop
  · intro a ha
    obtain ⟨k, ha_k⟩ := hSeedIdx a ha
    obtain ⟨r, hr, hra⟩ := List.mem_map.mp ((hRecsSpec k).1 a ha_k)
    exact ⟨⟨k, r.mono (hsub k)⟩, hmem_merged k r hr, hra⟩
  -- 2. record
  · rintro a ⟨m, hm, rfl⟩
    exact ⟨m.topRec.c, hrec m hm⟩
  -- 3. closed
  · rintro a x hTa ⟨c, i, hc, hi, hx⟩
    obtain ⟨m, hm, rfl, hmd, rfl⟩ := hmin a c hTa hc
    obtain ⟨r, hr, hm_eq⟩ := hmerged_inv m hm
    have hi' : i ∈ BaseSeams.usedRefIdxs r.c := by
      have : r.c = m.topRec.c := by rw [hm_eq]; rfl
      rw [this]; exact huse _ i x hi hx
    have hx' : r.c.refs[i]? = some x := by
      have : r.c = m.topRec.c := by rw [hm_eq]; rfl
      rwa [this]
    obtain ⟨-, hrest⟩ := ((hRecsSpec m.shardIdx).2.2.1 r hr).2 i hi' x hx'
    rcases hrest with ⟨-, r', hr', rfl, hlt⟩ | hcov | hasm
    · let m' : MergedRec allCalls b.address t lim entries :=
        ⟨m.shardIdx, r'.mono (hsub m.shardIdx)⟩
      have hm' : m' ∈ merged := hmem_merged m.shardIdx r' hr'
      have hdep_m : m.topRec.depth = r.depth := by rw [hm_eq]; rfl
      have hlt_g : globalDepth M m' < globalDepth M m := by
        dsimp only [globalDepth, m', CondTopRec.mono]
        omega
      refine .inl ⟨⟨m', hm', rfl⟩, ?_⟩
      have hle' : mergedRank M merged r'.addr ≤ globalDepth M m' := mergedRank_le hm'
      omega
    · exact .inr (Claim.covered_of_coveredAt hcov)
    · obtain ⟨j, hjk, hj_seed⟩ := hDag m.shardIdx.val m.shardIdx.isLt x hasm
      let jf : Fin entries.length := ⟨j, Nat.lt_trans hjk m.shardIdx.isLt⟩
      obtain ⟨r', hr', hra'⟩ := List.mem_map.mp ((hRecsSpec jf).1 x hj_seed)
      let m' : MergedRec allCalls b.address t lim entries := ⟨jf, r'.mono (hsub jf)⟩
      have hm' : m' ∈ merged := hmem_merged jf r' hr'
      have hdep_lt : r'.depth < M := hdepth_lt_M jf r' hr'
      have hlt_g : globalDepth M m' < globalDepth M m := by
        dsimp only [globalDepth, m', jf, CondTopRec.mono]
        have hstep : (j + 1) * M ≤ m.shardIdx.val * M :=
          Nat.mul_le_mul_right M hjk
        have h1 : j * M + r'.depth < j * M + M := Nat.add_lt_add_left hdep_lt _
        have h2 : j * M + M = (j + 1) * M := by rw [Nat.add_mul, Nat.one_mul]
        omega
      refine .inl ⟨⟨m', hm', hra'⟩, ?_⟩
      have hle' : mergedRank M merged x ≤ globalDepth M m' := by
        simpa [m', CondTopRec.mono, hra'] using mergedRank_le hm'
      omega
  -- 4. owner
  · intro a c hTa hc hp
    obtain ⟨m, hm, rfl, hmd, rfl⟩ := hmin a c hTa hc
    obtain ⟨r, hr, hm_eq⟩ := hmerged_inv m hm
    have hp' : Claim.IsProjRec r.c := by
      have : r.c = m.topRec.c := by rw [hm_eq]; rfl
      rwa [this]
    have hown_eq : Ix.Cert.ownerOf r.addr r.c = Ix.Cert.ownerOf m.topRec.addr m.topRec.c := by
      rw [hm_eq]; rfl
    rcases ((hRecsSpec m.shardIdx).2.2.1 r hr).1 hp' with ⟨r', hr', ha', hlt⟩ | hasm
    · let m' : MergedRec allCalls b.address t lim entries :=
        ⟨m.shardIdx, r'.mono (hsub m.shardIdx)⟩
      have hm' : m' ∈ merged := hmem_merged m.shardIdx r' hr'
      have hdep_m : m.topRec.depth = r.depth := by rw [hm_eq]; rfl
      have hlt_g : globalDepth M m' < globalDepth M m := by
        dsimp only [globalDepth, m', CondTopRec.mono]; omega
      rw [← hown_eq, ← ha']
      refine ⟨⟨m', hm', rfl⟩, ?_⟩
      have hle' : mergedRank M merged r'.addr ≤ globalDepth M m' := mergedRank_le hm'
      omega
    · rw [hown_eq] at hasm
      obtain ⟨j, hjk, hj_seed⟩ :=
        hDag m.shardIdx.val m.shardIdx.isLt (Ix.Cert.ownerOf m.topRec.addr m.topRec.c) hasm
      let jf : Fin entries.length := ⟨j, Nat.lt_trans hjk m.shardIdx.isLt⟩
      obtain ⟨r', hr', hra'⟩ := List.mem_map.mp ((hRecsSpec jf).1 _ hj_seed)
      let m' : MergedRec allCalls b.address t lim entries := ⟨jf, r'.mono (hsub jf)⟩
      have hm' : m' ∈ merged := hmem_merged jf r' hr'
      have hdep_lt : r'.depth < M := hdepth_lt_M jf r' hr'
      have hlt_g : globalDepth M m' < globalDepth M m := by
        dsimp only [globalDepth, m', jf, CondTopRec.mono]
        have hstep : (j + 1) * M ≤ m.shardIdx.val * M := Nat.mul_le_mul_right M hjk
        have h1 : j * M + r'.depth < j * M + M := Nat.add_lt_add_left hdep_lt _
        have h2 : j * M + M = (j + 1) * M := by rw [Nat.add_mul, Nat.one_mul]
        omega
      refine ⟨⟨m', hm', hra'⟩, ?_⟩
      have hle' : mergedRank M merged (Ix.Cert.ownerOf m.topRec.addr m.topRec.c) ≤ globalDepth M m' := by
        simpa [m', CondTopRec.mono, hra'] using mergedRank_le hm'
      omega
  -- 5. seedLogic
  · intro a ha c hc
    obtain ⟨k, ha_k⟩ := hSeedIdx a ha
    exact hSourceSafeOfClaimable (hClaimableOfSeed k ha_k) c hc
  -- 6. seedNotInert
  · intro a ha
    obtain ⟨k, ha_k⟩ := hSeedIdx a ha
    exact (hClaimableOfSeed k ha_k).notInert
  -- 7. checked
  · rintro a ⟨m, hm, rfl⟩
    exact ⟨m.topRec.c, hrec m hm, m.topRec.hchecked⟩
  -- 8. refsNotInert
  · rintro a x hTa ⟨c, i, hc, hi, hx⟩
    obtain ⟨m, hm, rfl, -, rfl⟩ := hmin a c hTa hc
    obtain ⟨r, hr, hm_eq⟩ := hmerged_inv m hm
    have hi' : i ∈ BaseSeams.usedRefIdxs r.c := by
      have : r.c = m.topRec.c := by rw [hm_eq]; rfl
      rw [this]; exact huse _ i x hi hx
    have hx' : r.c.refs[i]? = some x := by
      have : r.c = m.topRec.c := by rw [hm_eq]; rfl
      rwa [this]
    obtain ⟨hal, -⟩ := ((hRecsSpec m.shardIdx).2.2.1 r hr).2 i hi' x hx'
    exact Claim.refAllowed_not_inert_top (hal.mono (hsub m.shardIdx)) hlim
  -- 9. refsNotBlock
  · rintro a x hTa ⟨c, i, hc, hi, hx⟩ hncov cx hcx ⟨ms, hms⟩
    obtain ⟨m, hm, rfl, -, rfl⟩ := hmin a c hTa hc
    obtain ⟨r, hr, hm_eq⟩ := hmerged_inv m hm
    have hi' : i ∈ BaseSeams.usedRefIdxs r.c := by
      have : r.c = m.topRec.c := by rw [hm_eq]; rfl
      rw [this]; exact huse _ i x hi hx
    have hx' : r.c.refs[i]? = some x := by
      have : r.c = m.topRec.c := by rw [hm_eq]; rfl
      rwa [this]
    obtain ⟨-, hrest⟩ := ((hRecsSpec m.shardIdx).2.2.1 r hr).2 i hi' x hx'
    rcases hrest with ⟨⟨raw, c', hh, hb, hd, hn⟩, r', hr', rfl, -⟩ | hcov | hasm
    · have hhAll : Hashed allCalls raw := Core.hashed_mono (hsub m.shardIdx) hh
      have hr'All : Hashed allCalls r'.rawBytes := Core.hashed_mono (hsub m.shardIdx) r'.hhashed
      have hraw : raw = r'.rawBytes := hnoColl raw r'.rawBytes hhAll hr'All (hb.trans r'.hblake.symm)
      rw [hraw, r'.hde] at hd
      have hc' : r'.c = c' := Except.ok.inj hd
      let m' : MergedRec allCalls b.address t lim entries :=
        ⟨m.shardIdx, r'.mono (hsub m.shardIdx)⟩
      have hcx' : cx = r'.c := huniq m' (hmem_merged m.shardIdx r' hr') cx hcx
      exact hn ms (hc' ▸ hcx' ▸ hms)
    · exact hncov (Claim.covered_of_coveredAt hcov)
    · have hxAll : x ∈ ShardClaimEntry.allAsms entries :=
        List.mem_flatMap.mpr ⟨entries[m.shardIdx.val], List.getElem_mem m.shardIdx.isLt, hasm⟩
      unfold recordOf at hcx
      cases hgetx : E₀.consts.get? x with
      | none => rw [hgetx] at hcx; cases hcx
      | some lcx =>
        rw [hgetx] at hcx
        simp only [Option.bind_some] at hcx
        cases hdex : Ixon.deConstantExact lcx.rawBytes with
        | error e => rw [hdex] at hcx; cases hcx
        | ok cx' =>
          rw [hdex] at hcx
          simp only [Except.toOption, Option.some.injEq] at hcx
          subst cx'
          obtain ⟨hhx, hblx⟩ := hload.1 x lcx hgetx
          exact hNoBlk m.topRec.rawBytes m.topRec.c m.topRec.hhashed m.topRec.hdeExact i hi x hx hxAll
            lcx.rawBytes cx hhx hblx hdex ms hms
  -- 10. safeRefs
  · rintro a x hTa hsafe ⟨c, i, hc, hi, hx⟩ hncov
    obtain ⟨m, hm, rfl, -, rfl⟩ := hmin a c hTa hc
    by_cases hxAsm : x ∈ (entries[m.shardIdx.val]).asms
    · obtain ⟨j, hjk, hj_seed⟩ := hDag m.shardIdx.val m.shardIdx.isLt x hxAsm
      let jf : Fin entries.length := ⟨j, Nat.lt_trans hjk m.shardIdx.isLt⟩
      exact hSourceSafeOfClaimable (hClaimableOfSeed jf hj_seed)
    · exact m.topRec.hguard.safe hS hH (hrec m hm) hsafe i hi x (by simpa using hx) hxAsm
        (fun hcov => hncov (Claim.covered_of_coveredAt hcov))
  -- 11. quotBound
  · intro x ro c hTx hqr hof hc
    obtain ⟨m, hm, rfl, -, rfl⟩ := hmin x c hTx hc
    have hrefs := refs_small_of_decoded_cond m.topRec.hsz m.topRec.hdeExact
    obtain ⟨hstand, hrefsOk⟩ := m.topRec.hquot.spec hrefs hqr hof
    refine ⟨hstand, fun y ⟨c', i, hc', hi, hy⟩ => ?_⟩
    have hc_eq : c' = m.topRec.c := huniq m hm c' hc'
    subst hc_eq
    exact hrefsOk i hi y hy

/-! ## 6. Unconditional Binding Half & Family Steps -/

private theorem bindingSpecOn_unconditional
    {dB : Digest} {valueB : SourceValue F} {heapB : Heap F} {callsB : List (Call F)}
    (evB : ObsFn Obs.W verifyClaim [digestValue dB] [] valueB heapB callsB)
    (hbB : Bounded callsB) :
    BindingSpecOn.{u} (OverWFam.{u} FormerOpenTraceAt) callsB dB :=
  binding_skeleton_overW (Run := BindingRun callsB) (Fam := ClosureFam callsB)
    (bindingClaimExport_of_table_and_stores Binding.loadedTableAdmits
      Binding.loadedTablePinsPrelude FamilyRecon.groupStoresOfRun_closed
      dB valueB heapB callsB evB hbB)
    (basisOverW_bindingRun FormerOpenTraceAt callsB)
    (admitsChain_bindingRun callsB)
    (admitsReadsChain_bindingRun callsB)
    (fun _ _ _ h => h.families)
    (groupClosureFamily_of_steps Binding.closureUnitSteps_bindingRun
      (FamilyAlias.closureFamilySteps_of_checkRow FamilyAlias.closureFamilyCheck_of_run)
      TwinFamily.closureTwinSteps_closed callsB)
    (Binding.groupWithoutRoleUnit_bindingRun.{u} callsB)
    (Binding.operationRoleUnitW_of_projFree.{u} Binding.certProjFree_bindingRun callsB)
    (Binding.standardAxiomRoleUnitW_closed callsB)

private theorem familySteps_unconditional
    (allCalls : List (Call F)) (hfamMod : Typing.FamCallsModeled allCalls) :
    Typing.FamilyStepsFamFull.{u} FormerOpenTraceAt allCalls (Claim.TopWalk allCalls) :=
  Typing.familySteps_closedWF
    storedFormAt_recon
    (innerStepsChecked_of_kinds
      (nativeBlockTelescope_checked linkLaws_formerOpenTrace Core.projGuardRunReading))
    (FamilyAlias.familyBlockRow_of_check linkLaws_formerOpenTrace
      FamilyAlias.familyBlockCheckRow_of_run)
    TwinFamily.familyTwinWF_closed
    (standaloneDefinition_foldExtra linkLaws_formerOpenTrace)
    (standaloneTheoremOrOpaque_foldExtra linkLaws_formerOpenTrace)
    (standaloneRecursor_of_freshNotBasis freshRecursorMajorNotBasis_walked)
    (definitionBlock_of_nonempty (definitionBlock_foldExtra linkLaws_formerOpenTrace))
    (nativeBlockTelescope_walked linkLaws_formerOpenTrace Core.projGuardRunReading)
    nativeBlockAlias_walked
    nativeBlockOtherTelescope_step
    allCalls hfamMod

/-! ## 7. Source-Level & Circuit-Level Sharded Composition + Corollaries -/

private theorem collisionWith_to_combined_hashedCollision
    {V : View} {shardBytes : List ByteArray} {bytesB tb : ByteArray}
    {R : Ixon.Env} {allCalls callsB : List (Call F)}
    (htb : Hashed callsB tb) (hloadB : LoadedBy callsB R)
    (hcol : CollisionWith V (shardBytes ++ tb :: committedFootprint) R allCalls) :
    V.HashedCollision (shardBytes ++ bytesB :: committedFootprint) (allCalls ++ callsB) := by
  have hcA : ∀ cl ∈ allCalls, cl ∈ allCalls ++ callsB :=
    fun cl h => List.mem_append.mpr (Or.inl h)
  have hcB : ∀ cl ∈ callsB, cl ∈ allCalls ++ callsB :=
    fun cl h => List.mem_append.mpr (Or.inr h)
  have heA : ∀ x ∈ shardBytes ++ tb :: committedFootprint,
      x ∈ shardBytes ++ bytesB :: committedFootprint ∨ Hashed (allCalls ++ callsB) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact Or.inl (List.mem_append_left _ hx1)
    · rcases List.mem_cons.mp hx2 with rfl | hx3
      · exact Or.inr (IxVM.Consistency.hashed_mono hcB htb)
      · exact Or.inl (List.mem_append_right _ (List.mem_cons_of_mem _ hx3))
  have hR : ∀ {x : _root_.Address} {held : ByteArray},
      ((∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨ R.blobs.get? x = some held) →
      Hashed callsB held ∧ Address.blake3Pure held = x := by
    intro x held hheld
    obtain ⟨hrec, hblob⟩ := hloadB
    rcases hheld with ⟨lc, hl, hlc⟩ | hbl
    · rw [← hlc]; exact hrec x lc hl
    · exact hblob x held hbl
  rcases hcol with hcol | ⟨x, held, bytes, hheld, hh, hne, hx⟩ |
    ⟨x, held, image, hheld, ⟨blk, cb, ms, hblk, hdec, hms, himg⟩, hne, hx⟩
  · exact IxVM.Consistency.hashedCollision_mono heA hcA hcol
  · have hR' := hR hheld
    exact Or.inl ⟨x, held, bytes,
      Or.inr (Or.inr ⟨IxVM.Consistency.hashed_mono hcB hR'.1, hR'.2⟩),
      IxVM.Consistency.hashed_mono hcA hh, hne, hx⟩
  · have hR' := hR hheld
    exact Or.inr (Or.inl ⟨x, held, image, blk, cb, ms,
      Or.inr (Or.inr ⟨IxVM.Consistency.hashed_mono hcB hR'.1, hR'.2⟩),
      IxVM.Consistency.hashed_mono hcA hblk, hdec, hms, himg, hne, hx⟩)

/-- **Source-level conditional-shard partition composition (`sourceShardedComposed`):**
Given a bounded observed `IxVM::verify_claim` binding derivation `(callsB, dB)` and a finite list
of observed `IxVM::verify_claim` shard derivations `(shardCalls, ds)` whose flattened calls are
bounded (`Bounded shardCalls.flatten`), `ShardedComposedSpec` holds unconditionally. -/
theorem sourceShardedComposed
    {dB : Digest} {valueB : SourceValue F} {heapB : Heap F} {callsB : List (Call F)}
    (evB : ObsFn Obs.W verifyClaim [digestValue dB] [] valueB heapB callsB)
    (hbB : Bounded callsB)
    {ds : List Digest} {shardCalls : List (List (Call F))}
    (hShardObs : List.Forall₂
      (fun d calls => ∃ value heap, ObsFn Obs.W verifyClaim [digestValue d] [] value heap calls)
      ds shardCalls)
    (hbAll : Bounded shardCalls.flatten) :
    ShardedComposedSpec.{u} shardCalls callsB ds dB := by
  intro bytesB spec a hdeB hdB assumed V entries hPart hNoBlk
  let allCalls := shardCalls.flatten
  have hcB : ∀ cl ∈ callsB, cl ∈ allCalls ++ callsB :=
    fun cl h => List.mem_append.mpr (Or.inr h)
  -- 1. Discharge the binding claim run into a full 77-group TableWitness (OverWFam FormerOpenTraceAt)
  rcases bindingSpecOn_unconditional.{u} evB hbB bytesB spec a hdeB hdB V with
    hcolB | ⟨tb, t, R, envT, htb, ht, hall, hloadB, hW⟩
  · refine Or.inl (IxVM.Consistency.hashedCollision_mono (fun x hx => ?_) hcB hcolB)
    exact Or.inl (List.mem_append_right _ hx)
  -- 2. Case split on any collision of allCalls against V / shardBytes / tb / committedFootprint / R
  let extraAll : List ByteArray := ShardClaimEntry.allBytes entries ++ tb :: committedFootprint
  by_cases hnc : CollisionWith V extraAll R allCalls
  · exact Or.inl (collisionWith_to_combined_hashedCollision htb hloadB hnc)
  · refine Or.inr ⟨tb, t, R, envT, htb, ht, hall, hloadB, hW.shape, ?_⟩
    have hnoVCol : ¬ V.HashedCollision extraAll allCalls := fun hc => hnc (Or.inl hc)
    have hnoColl : ∀ b₁ b₂ : ByteArray, Hashed allCalls b₁ → Hashed allCalls b₂ →
        Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂ := by
      rcases Claim.noColl_or_hashedCollision V extraAll allCalls with hc | hok
      · exact (hnoVCol hc).elim
      · exact hok
    have hObsLen : ds.length = shardCalls.length := (List.forall₂_iff_get.mp hShardObs).1
    have hLen : entries.length = shardCalls.length :=
      hPart.length_eq.trans hObsLen
    let lim : Option Nat := if assumed then none else some 77
    have hlim : lim = some 77 ∨ lim = none := by
      cases assumed <;> simp [lim]
    -- 3. Extract CondShardWalk for every shard k < entries.length
    have hWalks : ∀ (k : Nat) (hk : k < entries.length),
        CondShardWalk (shardCalls[k]'(hLen ▸ hk)) a t lim entries[k].seeds entries[k].asms := by
      intro k hk
      have hkd : k < ds.length := hPart.length_eq ▸ hk
      have hks : k < shardCalls.length := hLen ▸ hk
      have hobs_k := (List.forall₂_iff_get.mp hShardObs).2 k hkd hks
      obtain ⟨vk, hk_heap, ev_k⟩ := hobs_k
      have hval_k := hPart.valid k hk
      obtain ⟨hde_k, hd_k, hscope_k, hctx_k, hba_k, hseeds_k, hasms_k⟩ := hval_k
      have ht_k : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨entries[k].ctx.binding, tb⟩ = .ok t := by
        rw [hba_k]; exact ht
      rcases verify_claim_conditional_walk_spec ev_k hde_k hd_k hscope_k hseeds_k hasms_k hctx_k ht_k with
        hcol_k | hwalk_k
      · exfalso
        apply hnoVCol
        refine IxVM.Consistency.hashedCollision_mono (fun x hx => ?_)
          (shardCalls_sub_flatten hks) hcol_k
        rcases List.mem_cons.mp hx with rfl | hx1
        · exact Or.inl (List.mem_append_left _
            (List.mem_map.mpr ⟨entries[k], List.getElem_mem hk, rfl⟩))
        · exact Or.inl (List.mem_append_right _ hx1)
      · rw [hba_k] at hwalk_k
        exact hwalk_k
    -- 4. Merge closed shard partition into one TopWalkCore over allCalls
    obtain ⟨Top, rank, hCore⟩ :=
      topWalkCore_of_closedPartition (b := ⟨a, tb⟩) ht hlim hLen hPart.dagClosed hWalks hnoColl hNoBlk
    let E₀ := Claim.runEnv (⟨a, tb⟩ : Ix.Kernel.Admission.Binding) (t := t) allCalls
    let allSeeds := ShardClaimEntry.allSeeds entries
    have hWalk : Claim.TopWalk allCalls t allSeeds E₀ lim (Claim.TopReach t E₀ allSeeds) rank :=
      ⟨a, hCore.restrictReach, hCore.reach_graph hCore.safeRefs⟩
    -- 5. FamCallsModeled holds on allCalls via flattening
    have hfamMod : Typing.FamCallsModeled allCalls := by
      refine famCallsModeled_flatten fun cs hcs => ?_
      obtain ⟨k, hks, rfl⟩ := List.getElem_of_mem hcs
      have hkd : k < ds.length := hObsLen ▸ hks
      obtain ⟨vk, hk_heap, ev_k⟩ := (List.forall₂_iff_get.mp hShardObs).2 k hkd hks
      exact Typing.FamCallsModeled.of_verifyClaim ev_k
    -- 6. Apply the zero-residual family typing skeleton to reach ConsistentReadOver
    have ht_ok : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp ht).wellFormed
    have hextra : ∀ x ∈ committedFootprint, x ∈ extraAll :=
      fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx)
    have hF : BoundaryFacts t (fun _ => True) R envT := hW.facts.1.1
    obtain ⟨Reg, hR⟩ := hW.facts.1.2
    obtain ⟨famOf, hSF⟩ := hW.facts.2
    have hc : Carried lim := carried_of_typingLim hlim
    obtain ⟨E_m, hM⟩ := merged_exists E₀ R
    have hctx_m : StepCtx.{u} allCalls t R envT E₀ E_m :=
      ⟨hW.shape,
        hM.recordsFor hCore.runStore.loaded hCore.runStore.decoded hW.shape.committed hextra hnc,
        fun x c h => hM.run_record hCore.runStore.loaded hCore.runStore.decoded hextra hnc h,
        fun x bl h => hM.run_blob hCore.runStore.loaded hnc h,
        fun env lim' => hM.good hCore.runStore.loaded hW.shape.zeroFree hextra hnc hbAll env t lim'⟩
    have hEnvWF : Ix.Kernel.EnvWF envT :=
      (hR E_m hctx_m.recordsFor lim hc (limWithin_all t lim)).prefixInv.store.store.wf
    have hsteps := familySteps_unconditional.{u} allCalls hfamMod
    obtain ⟨rank', fam, twin, adv, Inner, hWalk', hFG, hTop, hInner, hFam, hTwin, hTwinStored⟩ :=
      hsteps t allSeeds E₀ lim (Claim.TopReach t E₀ allSeeds) rank hWalk R envT hW.shape famOf hSF
        (records_agree hCore.runStore.loaded hnc) ⟨E_m, hctx_m⟩ hEnvWF hF.whole
    exact typing_skeleton_core_family_modeled (X := fun E => FoldExtra.{u} FormerOpenTraceAt t E)
      hW.shape
      (fun E hE => (hR E hE lim hc (limWithin_all t lim)).prefixInv) hF.whole
      (fun E hE => (hR E hE lim hc (limWithin_all t lim)).extra)
      ht_ok hbAll hextra hnc hCore.runStore (Claim.TopWalk.graph hWalk')
      hFG hTop hInner hFam hTwin hTwinStored

/-- Extract observed source derivation and ROM address cover for one `AcceptedCircuitRun`. -/
private theorem acceptedCircuitRun_to_source {d : Digest} (run : AcceptedCircuitRun d) :
    ∃ (value : SourceValue F) (heap : Heap F) (calls : List (Call F)) (addrs : List F),
      ObsFn IxVM.source.world verifyClaim [digestValue d] [] value heap calls ∧
      (run.compiled.traceROM run.rom).Valid ∧
      addrs.length ≤ run.rom.entries.length ∧
      (∀ e ∈ (run.compiled.traceROM run.rom).entries, e.1 ∈ addrs) ∧
      CallsInROM (run.compiled.traceROM run.rom) calls := by
  obtain ⟨value, heap, calls, observed, -, carried, -⟩ :=
    circuitToSource run.compiled run.physical run.certified run.bits run.plan run.activated
      (List.mem_singleton.mpr rfl) run.valid run.small run.signed run.rooted run.outside
      run.bound run.checked run.arguments run.decoded
  obtain ⟨addrs, hfew, hcover⟩ := run.compiled.traceROM_addresses run.rom
  exact ⟨value, heap, calls, addrs, observed,
    Aiur.WireROM.decode_valid (Aiur.WidthROM.toWireROM_valid run.valid _ _),
    hfew, hcover, carried⟩

private theorem extract_shardRuns (shardRuns : List (Sigma AcceptedCircuitRun)) :
    ∃ (items : List (Aiur.ROM F × List F × List (Call F))),
      itemsTotalLen items ≤ (shardRuns.map fun r => r.2.rom.entries.length).sum ∧
      (∀ it ∈ items, it.1.Valid ∧ (∀ e ∈ it.1.entries, e.1 ∈ it.2.1) ∧ CallsInROM it.1 it.2.2) ∧
      List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) (it : Aiur.ROM F × List F × List (Call F)) =>
        ∃ (value : SourceValue F) (heap : Heap F),
          ObsFn IxVM.source.world verifyClaim [digestValue run.1] [] value heap it.2.2 ∧
          CallsInROM (run.2.compiled.traceROM run.2.rom) it.2.2)
        shardRuns items := by
  induction shardRuns with
  | nil =>
    exact ⟨[], by simp [itemsTotalLen], by simp, .nil⟩
  | cons r rest ih =>
    obtain ⟨val, hp, calls, addrs, hobs, hval, hlen, hcov, hcar⟩ := acceptedCircuitRun_to_source r.2
    obtain ⟨items, hsum, hgood, hfor⟩ := ih
    refine ⟨(r.2.compiled.traceROM r.2.rom, addrs, calls) :: items, ?_, ?_,
      .cons ⟨val, hp, hobs, hcar⟩ hfor⟩
    · simp only [itemsTotalLen, List.map_cons, List.sum_cons] at hsum ⊢
      omega
    · intro it hit
      rcases List.mem_cons.mp hit with rfl | htl
      · exact ⟨hval, hcov, hcar⟩
      · exact hgood it htl

private theorem forall₂_shardRuns_obs
    {shardRuns : List (Sigma AcceptedCircuitRun)}
    {items : List (Aiur.ROM F × List F × List (Call F))}
    (h : List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) it =>
      ∃ (value : SourceValue F) (heap : Heap F),
        ObsFn IxVM.source.world verifyClaim [digestValue run.1] [] value heap it.2.2 ∧
        CallsInROM (run.2.compiled.traceROM run.2.rom) it.2.2) shardRuns items) :
    List.Forall₂
      (fun d calls => ∃ value heap, ObsFn Obs.W verifyClaim [digestValue d] [] value heap calls)
      (shardRuns.map (·.1)) (items.map (·.2.2)) := by
  induction h with
  | nil => exact .nil
  | cons hhd _ ih =>
    obtain ⟨v, h, ho, _⟩ := hhd
    exact .cons ⟨v, h, ho⟩ ih

private theorem forall₂_shardRuns_car
    {shardRuns : List (Sigma AcceptedCircuitRun)}
    {items : List (Aiur.ROM F × List F × List (Call F))}
    (h : List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) it =>
      ∃ (value : SourceValue F) (heap : Heap F),
        ObsFn IxVM.source.world verifyClaim [digestValue run.1] [] value heap it.2.2 ∧
        CallsInROM (run.2.compiled.traceROM run.2.rom) it.2.2) shardRuns items) :
    List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) calls =>
      ∃ (value : SourceValue F) (heap : Heap F),
        ObsFn IxVM.source.world verifyClaim [digestValue run.1] [] value heap calls ∧
        CallsInROM (run.2.compiled.traceROM run.2.rom) calls)
      shardRuns (items.map (·.2.2)) := by
  induction h with
  | nil => exact .nil
  | cons hhd _ ih => exact .cons hhd ih

/-- **Certified Conditional-Shard Partition Composition (`circuitShardedComposed`):**
Unconditional zero-argument theorem on `[propext, Classical.choice, Quot.sound]` proving
`Ix.Cert.Aggr.CircuitShardedComposed`: any accepted `IxVM::verify_claim` binding proof paired with
any finite list of accepted conditional shard proofs (with combined width-ROM entries `≤ 2 ^ 39`)
satisfies `ShardedComposedSpec`, so any closed DAG partition of conditional shards under the
binding table `a` either exhibits a BLAKE3 collision or yields `ConsistentReadOver` — a
set-theoretic `Ix.Kernel.Model W` in every `SetTheory W` covering the union of all shards' claimed
environments. -/
theorem circuitShardedComposed : Ix.Cert.Aggr.CircuitShardedComposed.{u} := by
  unfold Ix.Cert.Aggr.CircuitShardedComposed
  refine circuitSound_of_bounded circuitToSource ?_
  intro dB valueB heapB callsB evB hbB shardRuns hSumRom
  obtain ⟨items, hItemsLen, hItemsGood, hItemsFor⟩ := extract_shardRuns shardRuns
  have hbAll : Bounded (items.map (·.2.2)).flatten :=
    bounded_of_roms_sum_le items hItemsGood (hItemsLen.trans hSumRom)
  have hObs := forall₂_shardRuns_obs hItemsFor
  have hCar := forall₂_shardRuns_car hItemsFor
  exact ⟨items.map (·.2.2), hCar, sourceShardedComposed.{u} evB hbB hObs hbAll⟩

/-- **Circuit-level `no-False` corollary for closed conditional-shard partitions**, parametric in
any `Ix.Kernel.SetTheory W` over a `SelfHashed` view. -/
theorem circuitShardedComposed_no_False (W : Type u) [Ix.Kernel.SetTheory W] :
    CircuitSound fun callsB dB =>
      ∀ (shardRuns : List (Sigma AcceptedCircuitRun)),
        (shardRuns.map fun r => r.2.rom.entries.length).sum ≤ 2 ^ 39 →
        ∃ shardCalls : List (List (Call F)),
          List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) calls =>
            ∃ (value : SourceValue F) (heap : Heap F),
              ObsFn IxVM.source.world verifyClaim [digestValue run.1] [] value heap calls ∧
              CallsInROM (run.2.compiled.traceROM run.2.rom) calls)
            shardRuns shardCalls ∧
          ∀ (bytesB : ByteArray) (spec a : _root_.Address),
            Ix.Claim.de bytesB = .ok (.binding spec a) →
            packDigest (Address.blake3Pure bytesB) = dB →
            ∀ (assumed : Bool) (V : View) (entries : List ShardClaimEntry),
              ClosedShardPartition (shardRuns.map (·.1)) a assumed V entries →
              NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries) →
              SelfHashed V →
              GenuineCollision V (ShardClaimEntry.allBytes entries ++ bytesB :: committedFootprint)
                  (shardCalls.flatten ++ callsB) ∨
                ComposedWith.{u}
                  (fun t R _ => SeedsNotFalse shardCalls.flatten t R (ShardClaimEntry.allSeeds entries))
                  callsB a := by
  refine circuitSound_mono (fun callsB dB hShards => ?_) circuitShardedComposed.{u}
  intro shardRuns hSumRom
  obtain ⟨shardCalls, hCar, hSpec⟩ := hShards shardRuns hSumRom
  refine ⟨shardCalls, hCar, fun bytesB spec a hdeB hdB assumed V entries hPart hNoBlk hV => ?_⟩
  rcases shardedModelConclusion_selfHashed hV (hSpec bytesB spec a hdeB hdB assumed V entries hPart hNoBlk) with
    hCol | hOk
  · exact Or.inl hCol
  · exact Or.inr (ComposedWith.imp (fun _ _ _ hr => ConsistentReadOver.seeds_not_false W hr) hOk)

/-- **Circuit-level `SeedsInhabited` corollary for closed conditional-shard partitions** over a
`SelfHashed` view. -/
theorem circuitShardedComposed_seeds_inhabited :
    CircuitSound fun callsB dB =>
      ∀ (shardRuns : List (Sigma AcceptedCircuitRun)),
        (shardRuns.map fun r => r.2.rom.entries.length).sum ≤ 2 ^ 39 →
        ∃ shardCalls : List (List (Call F)),
          List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) calls =>
            ∃ (value : SourceValue F) (heap : Heap F),
              ObsFn IxVM.source.world verifyClaim [digestValue run.1] [] value heap calls ∧
              CallsInROM (run.2.compiled.traceROM run.2.rom) calls)
            shardRuns shardCalls ∧
          ∀ (bytesB : ByteArray) (spec a : _root_.Address),
            Ix.Claim.de bytesB = .ok (.binding spec a) →
            packDigest (Address.blake3Pure bytesB) = dB →
            ∀ (assumed : Bool) (V : View) (entries : List ShardClaimEntry),
              ClosedShardPartition (shardRuns.map (·.1)) a assumed V entries →
              NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries) →
              SelfHashed V →
              GenuineCollision V (ShardClaimEntry.allBytes entries ++ bytesB :: committedFootprint)
                  (shardCalls.flatten ++ callsB) ∨
                ComposedWith.{u}
                  (fun t R _ => SeedsInhabited.{u} shardCalls.flatten t R (ShardClaimEntry.allSeeds entries))
                  callsB a := by
  refine circuitSound_mono (fun callsB dB hShards => ?_) circuitShardedComposed.{u}
  intro shardRuns hSumRom
  obtain ⟨shardCalls, hCar, hSpec⟩ := hShards shardRuns hSumRom
  refine ⟨shardCalls, hCar, fun bytesB spec a hdeB hdB assumed V entries hPart hNoBlk hV => ?_⟩
  rcases shardedModelConclusion_selfHashed hV (hSpec bytesB spec a hdeB hdB assumed V entries hPart hNoBlk) with
    hCol | hOk
  · exact Or.inl hCol
  · exact Or.inr (ComposedWith.imp (fun _ _ _ hr => ConsistentReadOver.seeds_inhabited hr) hOk)

/-- **Unconditional Aggregated Sharded-Root Model Theorem
(`aggregated_root_sharded_checkEnv_model_unconditional`):**
Discharges `ShardedComposedSpec` directly via `circuitShardedComposed` for an accepted 19-shape
aggregation tree `t` rooted at `.checkEnv (.validated b) S ∅ ∅ ∅ ∅` paired with an accepted
`binding spec b` circuit run and a finite list of accepted conditional-shard circuit runs forming
a `ClosedShardPartition` whose union of seeds is `S`. -/
theorem aggregated_root_sharded_checkEnv_model_unconditional (W : Type u) [Ix.Kernel.SetTheory W]
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {b : _root_.Address} {S : _root_.Address → Prop}
    {dB : Digest} (runB : AcceptedCircuitRun dB)
    {bytesB : ByteArray} {spec : _root_.Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec b))
    (hdB : packDigest (Address.blake3Pure bytesB) = dB)
    (shardRuns : List (Sigma AcceptedCircuitRun))
    (hSumRom : (shardRuns.map fun r => r.2.rom.entries.length).sum ≤ 2 ^ 39)
    {assumed : Bool} {V : View} {entries : List ShardClaimEntry}
    (hPart : ClosedShardPartition (shardRuns.map (·.1)) b assumed V entries)
    (hS : ∀ x, S x ↔ x ∈ ShardClaimEntry.allSeeds entries)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv (.validated b) S (fun _ => False) (fun _ => False) (fun _ => False) (fun _ => False))) :
    ∃ (callsB : List (Call F)) (shardCalls : List (List (Call F))),
      (∃ vB hB, ObsFn IxVM.source.world verifyClaim [digestValue dB] [] vB hB callsB ∧
        CallsInROM (runB.compiled.traceROM runB.rom) callsB) ∧
      List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) calls =>
        ∃ v h, ObsFn IxVM.source.world verifyClaim [digestValue run.1] [] v h calls ∧
          CallsInROM (run.2.compiled.traceROM run.2.rom) calls)
        shardRuns shardCalls ∧
      (NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries) →
        (∀ x, S x → sem.Checked b (fun _ => False) (fun _ => False) (fun _ => False) x) ∧
        (∀ x y, S x → sem.Dep x y → S y) ∧
        (∀ x, S x ↔ x ∈ ShardClaimEntry.allSeeds entries) ∧
        t.dynamicLinkDischarges = 0 ∧
        (t.HasTreeCollision ∨
          ∀ vp ∈ t.childProofs, ∃ proofBytes,
            Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) ∧
        (V.HashedCollision (ShardClaimEntry.allBytes entries ++ bytesB :: committedFootprint)
            (shardCalls.flatten ++ callsB) ∨
          ComposedWith.{u}
            (fun tRole R envT =>
              ConsistentReadOver.{u} shardCalls.flatten tRole R envT
                (ShardClaimEntry.allSeeds entries) ∧
              SeedsNotFalse shardCalls.flatten tRole R (ShardClaimEntry.allSeeds entries))
            callsB b)) := by
  obtain ⟨vB, hB, callsB, hObsB, hCarB, hShards⟩ :=
    circuitShardedComposed.{u} runB.compiled runB.physical runB.certified runB.bits runB.plan
      runB.activated runB.valid runB.small dB runB.signed runB.rooted runB.outside runB.bound
      runB.checked runB.arguments runB.decoded
  obtain ⟨shardCalls, hCarShards, hSpec⟩ := hShards shardRuns hSumRom
  exact ⟨callsB, shardCalls, ⟨vB, hB, hObsB, hCarB⟩, hCarShards, fun hNoBlk =>
    aggregated_root_sharded_checkEnv_no_axioms_model W hSpec hdeB hdB hPart hNoBlk hS t⟩

end IxVM.Refinement.Endpoint

#guard_kernel_axioms IxVM.Refinement.Endpoint.sourceShardedComposed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitShardedComposed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitShardedComposed_no_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitShardedComposed_seeds_inhabited [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.aggregated_root_sharded_checkEnv_model_unconditional [propext, Classical.choice, Quot.sound]
