import IxVMRefinement.Assembly.L7
import Ix.Cert.FallbackStore

/-! # Sub-store construction, `RolePreludeInputs`, multi-walk union, and `coreEnv`

Provides the Phase-2 store infrastructure backing `WalkedBareBridge`:

* `RolePreludeInputs`: parametric role-table / committed-fallback interface matching `W4-Roles`'s
  proven exports (`fallbackHashed`, `preludeFor_of_readerTable`,
  `literalSupportBound_of_readerTable`, `fallback_record_agree`, `fallback_blob_agree`), with
  derived committed-image membership, non-padding addresses, and `recordAt` agreement;
* `ClosedSubwalk`, `WkAll`, and `rankAll`: combines `WalkedL6`'s seed closure with any number of
  `Claim.RecsClosed` sub-walks from `KernelClaim::run_check_transitive` (invoked by
  `role_used_implicitly`, `group_admit`, and `check_witness` kind 0) into a single `WalkEdge`-closed
  rank-decreasing safe set via `Nat.find`;
* `subEnv_withProj_usedClosureOrderAt` and `walkedBareWitness_of_subEnv_withProj`: generalizes
  `subEnv_twoTier_usedClosureOrderAt` so `Keep` may also retain canonical projection records of kept
  blocks (`c.sharing = #[] ∧ c.refs = #[]`) without affecting `Draws`, owner-closure, or
  `UsedRecordRef` ordering;
* `preludeRecSupp` and `coreEnv`: supplements kept prelude blocks with their committed standalone
  `.recr` records (kernel-verified self-contained in `RoleData.prelude`) and constructs `coreEnv`
  extending `subEnv E₀ Keep supp` with `pre.records ++ pre.evidence`, discharging `Core.Good` and
  `L1.EnvDecoded` unconditionally. -/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-! ## Parametric role-prelude interface (`RolePreludeInputs`) -/

/-- Role-validation and committed-fallback facts consumed by `Assembly/Bridge.lean`, matching the
proven exports of `RoleVal/{CommittedData,ReaderTable}.lean` with zero cross-lane imports. -/
structure RolePreludeInputs : Prop where
  fallbackHashed : Ix.Cert.RoleClosure.FallbackHashed
  preludeFor_of_readerTable :
    ∀ {clm : Ix.Claim} {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
      {t : Ix.Kernel.RoleTable},
      IxVM.Consistency.ReaderTable clm V b →
      Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t →
      ∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) t = .ok pre
  literalSupportBound_of_readerTable :
    ∀ {clm : Ix.Claim} {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
      {t : Ix.Kernel.RoleTable},
      IxVM.Consistency.ReaderTable clm V b →
      Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t →
      IxVM.Refinement.LiteralSupportBound t
  fallback_record_agree :
    ∀ {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env},
      (∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra) →
      IxVM.Consistency.LoadedBy calls E₀ →
      ∀ {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon},
        Ix.Kernel.Reader.preludeFor t = .ok pre →
        ∀ {a : _root_.Address} {c : Ixon.Constant}, (a, c) ∈ pre.records ++ pre.evidence →
        ∀ {lc : Ixon.LazyConstant}, E₀.consts.get? a = some lc →
        V.HashedCollision extra calls ∨ (lc.rawBytes = Ixon.serConstant c ∧ c.wireWF)
  fallback_blob_agree :
    ∀ {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env},
      (∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra) →
      IxVM.Consistency.LoadedBy calls E₀ →
      ∀ {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon},
        Ix.Kernel.Reader.preludeFor t = .ok pre →
        ∀ {a : _root_.Address} {blob raw : ByteArray}, (a, blob) ∈ pre.blobs →
        E₀.blobs.get? a = some raw →
        V.HashedCollision extra calls ∨ raw = blob

private def fallbackRowsNotPaddingBool : Bool :=
  (Ix.Kernel.Reader.RoleData.prelude ++ Ix.Kernel.Reader.RoleData.evidence).all fun row =>
    Ix.Kernel.Reader.addressOfHex row.1 != some Ix.HostAdmission.Merkle.padding

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
private theorem fallbackRowsNotPadding_ok : fallbackRowsNotPaddingBool = true := by
  decide +kernel

/-- Every record `(a, c)` in `pre.records ++ pre.evidence` has `Ixon.serConstant c` in
`committedImages`, pure BLAKE3 digest `a`, wire well-formedness `c.wireWF`, and non-padding address
`a ≠ Ix.HostAdmission.Merkle.padding`. -/
theorem RolePreludeInputs.serConstant_mem_committedImages (hRP : RolePreludeInputs)
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence) :
    Ixon.serConstant c ∈ IxVM.Consistency.committedImages ∧
      _root_.Address.blake3Pure (Ixon.serConstant c) = a ∧
      c.wireWF ∧
      a ≠ Ix.HostAdmission.Merkle.padding := by
  obtain ⟨hauth, hwf⟩ := Ix.Cert.FallbackStore.fallback_authentic hRP.fallbackHashed hpre hmem
  rw [_root_.Address.admissionHash_eq] at hauth
  obtain ⟨hr, he⟩ := Ix.Cert.ReaderFallback.preludeFor_records hpre
  have hrow : ∃ row ∈ (Ix.Kernel.Reader.RoleData.prelude ++
      Ix.Kernel.Reader.RoleData.evidence).toList,
      Ix.Kernel.Reader.addressOfHex row.1 = some a ∧
      ∃ raw, bytesOfHex row.2 = some raw ∧
        Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
          Ix.Kernel.Reader.preludeMaxUnivNodes raw = .ok c := by
    rcases Array.mem_append.mp hmem with h1 | h2
    · obtain ⟨row, hrow, hrest⟩ := Ix.Cert.FallbackStore.decoded_rows "prelude"
        Ix.Kernel.Reader.RoleData.prelude hr (a, c) (Array.mem_toList_iff.mpr h1)
      exact ⟨row, by simp [Array.toList_append, hrow], hrest⟩
    · obtain ⟨row, hrow, hrest⟩ := Ix.Cert.FallbackStore.decoded_rows "evidence"
        Ix.Kernel.Reader.RoleData.evidence he (a, c) (Array.mem_toList_iff.mpr h2)
      exact ⟨row, by simp [Array.toList_append, hrow], hrest⟩
  obtain ⟨row, hrow_mem, ha_hex, raw, hraw_hex, hde_can⟩ := hrow
  obtain ⟨-, -, hser⟩ := Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hde_can
  have himg : Ixon.serConstant c ∈ IxVM.Consistency.committedImages := by
    rw [hser]
    unfold IxVM.Consistency.committedImages
    rw [List.mem_filterMap]
    refine ⟨row.2, ?_, hraw_hex⟩
    rw [List.mem_map]
    refine ⟨row, ?_, rfl⟩
    rw [Array.toList_append]
    exact List.mem_append_left _ hrow_mem
  have hnotPad : a ≠ Ix.HostAdmission.Merkle.padding := by
    have hall := Array.all_eq_true_iff_forall_mem.mp fallbackRowsNotPadding_ok row
      (Array.mem_toList_iff.mp hrow_mem)
    intro heq
    rw [heq, ha_hex] at hall
    simp at hall
  exact ⟨himg, hauth.symm, hwf, hnotPad⟩

/-- Under `¬ V.HashedCollision extra calls` and exact decoding on `E₀`, any record present in `E₀`
at an address of `pre.records ++ pre.evidence` decodes to the committed fallback constant `c`. -/
theorem RolePreludeInputs.fallback_recordAt_agree (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env}
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hnoCol : ¬ V.HashedCollision extra calls)
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence)
    {lc : Ixon.LazyConstant} (hget : E₀.consts.get? a = some lc) :
    lc.rawBytes = Ixon.serConstant c ∧ c.wireWF ∧ Ix.Cert.recordAt E₀ a = some c := by
  rcases hRP.fallback_record_agree hcomm_extra hload hpre hmem hget with hcol | ⟨hraw, hwf⟩
  · exact absurd hcol hnoCol
  · obtain ⟨c', hlc_c', hex⟩ := hexact₀ a lc hget
    rw [hraw, Ixon.Verify.deConstantExact_serConstant c hwf] at hex
    injection hex with hce
    subst hce
    refine ⟨hraw, hwf, ?_⟩
    unfold Ix.Cert.recordAt
    rw [hget]
    exact hlc_c'

/-! ## `ClosedSubwalk` union (`WkAll`, `rankAll`) across `WalkedL6` and `RecsClosed` sub-walks -/

/-- A `WalkEdge`-closed, rank-decreasing, safe, checked subset of `E₀`. -/
structure ClosedSubwalk (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (W : _root_.Address → Prop) (rk : _root_.Address → Nat) : Prop where
  step : ∀ x y, W x → Core.S0.WalkEdge E₀ x y → W y ∧ rk y < rk x
  safe : ∀ x, W x → ¬ IxVM.Consistency.OutsideLogicAt E₀ x
  checked : ∀ x, W x → ∃ c, Ix.Cert.recordAt E₀ x = some c ∧
    ((∃ ms, c.info = .muts ms ∧
      ∀ (k : Nat), k < ms.size → Claim.MutsMemberCheckedAtFull calls bAddr t x ms k) ∨
     Claim.CheckedAtFull calls bAddr t x)

/-- Union of all `ClosedSubwalk`s for `(calls, bAddr, t, E₀)`. -/
def WkAll (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (x : _root_.Address) : Prop :=
  ∃ W rk, ClosedSubwalk calls bAddr t E₀ W rk ∧ W x

private theorem wkAll_exists_nat {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {x : _root_.Address}
    (h : WkAll calls bAddr t E₀ x) :
    ∃ n : Nat, ∃ W rk, ClosedSubwalk calls bAddr t E₀ W rk ∧ W x ∧ rk x = n := by
  obtain ⟨W, rk, hcs, hwx⟩ := h
  exact ⟨rk x, W, rk, hcs, hwx, rfl⟩

/-- Minimum rank across all `ClosedSubwalk`s containing `x` (`0` outside `WkAll`). -/
noncomputable def rankAll (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (x : _root_.Address) : Nat :=
  letI := Classical.propDecidable
  if h : ∃ n : Nat, ∃ W rk, ClosedSubwalk calls bAddr t E₀ W rk ∧ W x ∧ rk x = n then
    Nat.find h
  else 0

theorem wkAll_of_closedSubwalk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {W : _root_.Address → Prop}
    {rk : _root_.Address → Nat}
    (hcs : ClosedSubwalk calls bAddr t E₀ W rk) {x : _root_.Address} (hx : W x) :
    WkAll calls bAddr t E₀ x :=
  ⟨W, rk, hcs, hx⟩

theorem rankAll_le_of_closedSubwalk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {W : _root_.Address → Prop}
    {rk : _root_.Address → Nat}
    (hcs : ClosedSubwalk calls bAddr t E₀ W rk) {x : _root_.Address} (hx : W x) :
    rankAll calls bAddr t E₀ x ≤ rk x := by
  classical
  have hex : ∃ n : Nat, ∃ W' rk', ClosedSubwalk calls bAddr t E₀ W' rk' ∧ W' x ∧ rk' x = n :=
    ⟨rk x, W, rk, hcs, hx, rfl⟩
  simp only [rankAll, hex, ↓reduceDIte]
  exact Nat.find_min' hex ⟨W, rk, hcs, hx, rfl⟩

/-- `(WkAll, rankAll)` is itself a `ClosedSubwalk` (closed under `WalkEdge` with strict `rankAll`
decrease, safe, and checked). -/
theorem wkAll_closedSubwalk (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) :
    ClosedSubwalk calls bAddr t E₀
      (WkAll calls bAddr t E₀) (rankAll calls bAddr t E₀) where
  step x y hx hedge := by
    classical
    have hex := wkAll_exists_nat hx
    have hfind := Nat.find_spec hex
    obtain ⟨W, rk, hcs, hwx, hrk_eq⟩ := hfind
    have hrk_all : rankAll calls bAddr t E₀ x = Nat.find hex := by
      simp only [rankAll, hex, ↓reduceDIte]
    obtain ⟨hwy, hlt⟩ := hcs.step x y hwx hedge
    have hle := rankAll_le_of_closedSubwalk hcs hwy
    exact ⟨⟨W, rk, hcs, hwy⟩, by omega⟩
  safe x hx := by
    obtain ⟨W, rk, hcs, hwx⟩ := hx
    exact hcs.safe x hwx
  checked x hx := by
    obtain ⟨W, rk, hcs, hwx⟩ := hx
    exact hcs.checked x hwx

/-- Reflexive-transitive closure of `Core.S0.WalkEdge E₀` starting from `seeds`. -/
def SeedReach (E₀ : Ixon.Env) (seeds : List _root_.Address) (x : _root_.Address) : Prop :=
  ∃ s ∈ seeds, Relation.ReflTransGen (Core.S0.WalkEdge E₀) s x

theorem seedReach_of_mem {E₀ : Ixon.Env} {seeds : List _root_.Address} {a : _root_.Address}
    (ha : a ∈ seeds) : SeedReach E₀ seeds a :=
  ⟨a, ha, .refl⟩

theorem seedReach_step {E₀ : Ixon.Env} {seeds : List _root_.Address} {x y : _root_.Address}
    (hx : SeedReach E₀ seeds x) (hedge : Core.S0.WalkEdge E₀ x y) :
    SeedReach E₀ seeds y := by
  obtain ⟨s, hs, hrt⟩ := hx
  exact ⟨s, hs, .tail hrt hedge⟩

/-- Restricting `(Wk, rank)` from `WalkedL6` to `SeedReach E₀ seeds` forms a `ClosedSubwalk` once
safety (`¬ OutsideLogicAt E₀`) is propagated along `SeedReach`. -/
theorem closedSubwalk_of_seedReach {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hseeds_wk : ∀ a ∈ seeds, Wk a)
    (hwk_step : ∀ a b, Wk a → Core.S0.WalkEdge E₀ a b → Wk b ∧ rank b < rank a)
    (hwk_chk : ∀ a, Wk a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧
      ((∃ ms, c.info = .muts ms ∧
        ∀ (k : Nat), k < ms.size → Claim.MutsMemberCheckedAtFull calls bAddr t a ms k) ∨
       Claim.CheckedAtFull calls bAddr t a))
    (hsafe : ∀ x, SeedReach E₀ seeds x → ¬ IxVM.Consistency.OutsideLogicAt E₀ x) :
    ClosedSubwalk calls bAddr t E₀ (SeedReach E₀ seeds) rank := by
  have hsub_wk : ∀ x, SeedReach E₀ seeds x → Wk x := by
    intro x ⟨s, hs, hrt⟩
    induction hrt with
    | refl => exact hseeds_wk s hs
    | tail _ hedge ih => exact (hwk_step _ _ ih hedge).1
  exact {
    step := fun x y hx hedge =>
      ⟨seedReach_step hx hedge, (hwk_step x y (hsub_wk x hx) hedge).2⟩
    safe := hsafe
    checked := fun x hx => hwk_chk x (hsub_wk x hx)
  }

private def minNatList : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: rest =>
    let m := minNatList (y :: rest)
    if x ≤ m then x else m

private theorem minNatList_le_of_mem : ∀ {xs : List Nat} {a : Nat}, a ∈ xs → minNatList xs ≤ a
  | [], _, h => nomatch h
  | [x], a, h => by
    rcases List.mem_singleton.mp h with rfl
    exact Nat.le_refl _
  | x :: y :: rest, a, h => by
    simp only [minNatList]
    rcases List.mem_cons.mp h with rfl | htl
    · split_ifs <;> omega
    · have ih := minNatList_le_of_mem htl
      split_ifs <;> omega

private theorem minNatList_mem_of_ne_nil : ∀ {xs : List Nat}, xs ≠ [] → minNatList xs ∈ xs
  | [], h => absurd rfl h
  | [x], _ => List.mem_cons_self
  | x :: y :: rest, _ => by
    simp only [minNatList]
    have hrec : minNatList (y :: rest) ∈ y :: rest := minNatList_mem_of_ne_nil (by simp)
    split_ifs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hrec

/-- Rank of `a` inside a `WalkedRec` list `recs` (`min` of `r.depth` at `r.addr = a`). -/
def recsRank {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    (recs : List (Claim.WalkedRec calls bAddr t)) (a : _root_.Address) : Nat :=
  minNatList ((recs.filter (fun r => r.addr == a)).map (·.depth))

/-- Any `Claim.RecsClosed` list `recs` from a `run_check_transitive` call in `calls` forms a
`ClosedSubwalk` on `E₀` once `E₀.consts` completeness from `WalkedL6` and safety on `recs` are
given. -/
theorem closedSubwalk_of_recsClosed {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (hconsts_complete : ∀ bytes c, IxVM.Refinement.Hashed calls bytes →
      bytes.size < 4294967296 → Ixon.deConstant bytes = .ok c →
      Ixon.deConstantExact bytes = .ok c →
      ∃ lc, E₀.consts.get? (_root_.Address.blake3Pure bytes) = some lc ∧
        lc.rawBytes = bytes ∧ lc.get? = some c)
    (recs : List (Claim.WalkedRec calls bAddr t))
    (hcl : Claim.RecsClosed recs)
    (hsafe : ∀ a ∈ recs.map (·.addr), ¬ IxVM.Consistency.OutsideLogicAt E₀ a) :
    ClosedSubwalk calls bAddr t E₀ (fun a => a ∈ recs.map (·.addr)) (recsRank recs) := by
  have hrecAt : ∀ r ∈ recs, Ix.Cert.recordAt E₀ r.addr = some r.c := by
    intro r hr
    obtain ⟨lc, hget, _, hlc_c⟩ :=
      hconsts_complete r.rawBytes r.c r.hhashed r.hsz r.hde r.hdeExact
    rw [r.hblake] at hget
    unfold Ix.Cert.recordAt
    rw [hget]
    exact hlc_c
  refine {
    step := fun a b ha ⟨c, hrec_a, hstep⟩ => ?_
    safe := hsafe
    checked := fun a ha => ?_
  }
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp ha
    have hne : ((recs.filter (fun r => r.addr == r₀.addr)).map (·.depth)) ≠ [] := by
      intro hemp
      have hm : r₀.depth ∈ (recs.filter (fun r => r.addr == r₀.addr)).map (·.depth) :=
        List.mem_map.mpr ⟨r₀, List.mem_filter.mpr ⟨hr₀, beq_self_eq_true _⟩, rfl⟩
      rw [hemp] at hm
      cases hm
    obtain ⟨r_min, hr_filt, hdep⟩ := List.mem_map.mp (minNatList_mem_of_ne_nil hne)
    obtain ⟨hr_mem, hr_beq⟩ := List.mem_filter.mp hr_filt
    have hr_addr : r_min.addr = r₀.addr := beq_iff_eq.mp hr_beq
    have hrec_min := hrecAt r_min hr_mem
    rw [hr_addr, hrec_a] at hrec_min
    injection hrec_min with hc_eq
    obtain ⟨hown, hrefs⟩ := hcl r_min hr_mem
    rw [hr_addr, ← hc_eq] at hown
    rw [← hc_eq] at hrefs
    rcases hstep with ⟨rfl, hne_own⟩ | ⟨i, hi, hb⟩
    · obtain ⟨r', hr', ha', hlt'⟩ := hown hne_own
      have hle' : recsRank recs r'.addr ≤ r'.depth :=
        minNatList_le_of_mem
          (List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', beq_self_eq_true _⟩, rfl⟩)
      rw [ha'] at hle'
      exact ⟨List.mem_map.mpr ⟨r', hr', ha'⟩, by unfold recsRank at hle' ⊢; omega⟩
    · obtain ⟨r', hr', ha', hlt'⟩ := hrefs i hi b hb
      have hle' : recsRank recs r'.addr ≤ r'.depth :=
        minNatList_le_of_mem
          (List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', beq_self_eq_true _⟩, rfl⟩)
      rw [ha'] at hle'
      exact ⟨List.mem_map.mpr ⟨r', hr', ha'⟩, by unfold recsRank at hle' ⊢; omega⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact ⟨r.c, hrecAt r hr, r.hchecked⟩

/-! ## `UsedClosureOrderAt` on `subEnv` with extra recursors and canonical projections -/

/-- Owner-closure and `UsedClosureOrderAt` for `subEnv E₀ Keep supp` when every non-`Wk` record in
`subEnv` is either a recursor record (`IsRecursorRecord`) or a canonical projection record
(`c.sharing = #[] ∧ c.refs = #[]`) whose owner is a kept `Wk` or `IsRecursorRecord` block. -/
theorem subEnv_withProj_usedClosureOrderAt (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (Keep : _root_.Address → Prop) (supp : List SuppEntry) (S : _root_.Address → Prop)
    {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (iblock : _root_.Address → _root_.Address)
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_step : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    (hextra_kind : ∀ x c, ¬ Wk x → Ix.Cert.recordAt (subEnv E₀ Keep supp) x = some c →
      IxVM.Refinement.IsRecursorRecord c ∨
        (c.sharing = #[] ∧ c.refs = #[] ∧ Ix.Cert.ownerOf x c ≠ x ∧
          (Wk (Ix.Cert.ownerOf x c) ∨
            ∃ co, Ix.Cert.recordAt (subEnv E₀ Keep supp) (Ix.Cert.ownerOf x c) = some co ∧
              IxVM.Refinement.IsRecursorRecord co)))
    (hextra_refs : ∀ a c, ¬ Wk a → Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c →
      IxVM.Refinement.IsRecursorRecord c →
      ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ r cr,
        c.refs[i]? = some r →
        Ix.Cert.recordAt (subEnv E₀ Keep supp) r = some cr →
        Ix.Cert.ownerOf r cr ≠ a →
        (Wk (Ix.Cert.ownerOf r cr) ∧ rank (Ix.Cert.ownerOf r cr) ≤ rank (iblock a)) ∨
          (¬ Wk (Ix.Cert.ownerOf r cr) ∧ rank (iblock (Ix.Cert.ownerOf r cr)) < rank (iblock a))) :
    IxVM.Consistency.UsedClosureOrderAt t (subEnv E₀ Keep supp) S
      (closureOrderByRank t (subEnv E₀ Keep supp) S (twoTierRank Wk rank iblock)) := by
  let E := subEnv E₀ Keep supp
  have hown : ∀ a c, Ix.Cert.recordAt E a = some c →
      E.consts.contains (Ix.Cert.ownerOf a c) = true := by
    intro a c hrec
    by_cases hwa : Wk a
    · obtain ⟨c₀, hrec₀⟩ := hwk_rec a hwa
      have hrec' := recordAt_subEnv_of_keep E₀ Keep supp (hwk_keep a hwa) hrec₀
      rw [hrec] at hrec'
      injection hrec' with hceq
      subst hceq
      by_cases hown_eq : Ix.Cert.ownerOf a c = a
      · rw [hown_eq]
        exact contains_of_recordAt hrec
      · obtain ⟨hwb, _⟩ := hwk_step a (Ix.Cert.ownerOf a c) hwa ⟨c, hrec₀, Or.inl ⟨rfl, hown_eq⟩⟩
        obtain ⟨cb, hrec_b⟩ := hwk_rec _ hwb
        exact contains_of_recordAt (recordAt_subEnv_of_keep E₀ Keep supp (hwk_keep _ hwb) hrec_b)
    · rcases hextra_kind a c hwa hrec with hrec_k | ⟨_, _, _, hown_wk⟩
      · rw [isRecursorRecord_ownerOf_eq a hrec_k]
        exact contains_of_recordAt hrec
      · rcases hown_wk with hwb | ⟨co, hrec_o, _⟩
        · obtain ⟨cb, hrec_b⟩ := hwk_rec _ hwb
          exact contains_of_recordAt (recordAt_subEnv_of_keep E₀ Keep supp (hwk_keep _ hwb) hrec_b)
        · exact contains_of_recordAt hrec_o
  refine usedClosureOrderAt_closureOrderByRank hown fun a b _ _ href => ?_
  by_cases hwa : Wk a
  · obtain ⟨hwb, hlt⟩ := usedRecordRef_of_wk hwk_keep hwk_step hwk_rec hwa href
    simp only [twoTierRank, hwa, hwb, ↓reduceIte]
    omega
  · obtain ⟨c, hrec_a, i, hi, r, hr, cr, hrec_r, hown_r, hne⟩ := href
    rcases hextra_kind a c hwa hrec_a with hrec_k | ⟨_, hrefs_emp, _, _⟩
    · have hex := hextra_refs a c hwa hrec_a hrec_k i hi r cr hr hrec_r (by rw [hown_r]; exact hne)
      rw [hown_r] at hex
      rcases hex with ⟨hwb, hle⟩ | ⟨hnwb, hlt⟩
      · simp only [twoTierRank, hwa, hwb, ↓reduceIte]
        omega
      · simp only [twoTierRank, hwa, hnwb, ↓reduceIte]
        omega
    · rw [hrefs_emp] at hr
      simp at hr

/-- Witness packager upgrading `walkedBareWitness_of_subEnv` with `subEnv_withProj_usedClosureOrderAt`. -/
theorem walkedBareWitness_of_subEnv_withProj
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (Keep : _root_.Address → Prop) (supp : List SuppEntry)
    {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (iblock : _root_.Address → _root_.Address)
    (hsupp_rec : ∀ entry ∈ supp, IxVM.Refinement.IsRecursorRecord entry.2.2)
    (hsupp_auth : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧ Ixon.deConstantExact raw = .ok c)
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_step : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    (hextra_kind : ∀ x c, ¬ Wk x → Ix.Cert.recordAt (subEnv E₀ Keep supp) x = some c →
      IxVM.Refinement.IsRecursorRecord c ∨
        (c.sharing = #[] ∧ c.refs = #[] ∧ Ix.Cert.ownerOf x c ≠ x ∧
          (Wk (Ix.Cert.ownerOf x c) ∨
            ∃ co, Ix.Cert.recordAt (subEnv E₀ Keep supp) (Ix.Cert.ownerOf x c) = some co ∧
              IxVM.Refinement.IsRecursorRecord co)))
    (hextra_refs : ∀ a c, ¬ Wk a → Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c →
      IxVM.Refinement.IsRecursorRecord c →
      ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ r cr,
        c.refs[i]? = some r →
        Ix.Cert.recordAt (subEnv E₀ Keep supp) r = some cr →
        Ix.Cert.ownerOf r cr ≠ a →
        (Wk (Ix.Cert.ownerOf r cr) ∧ rank (Ix.Cert.ownerOf r cr) ≤ rank (iblock a)) ∨
          (¬ Wk (Ix.Cert.ownerOf r cr) ∧ rank (iblock (Ix.Cert.ownerOf r cr)) < rank (iblock a)))
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {st' : Ix.Kernel.Reader.State .anon} {decls : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hreads :
      let E := subEnv E₀ Keep supp
      let S := fun a => a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList
      let order := closureOrderByRank t E S (twoTierRank Wk rank iblock)
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls)
    (hkeeps : Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true)
    (hchk : ∀ ds_pre d ds_suf env_pre,
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf →
      IxVM.Consistency.Installs ds_pre env_pre →
      Checked calls env_pre d)
    (hseeds : ∀ a ∈ seeds,
      IxVM.Consistency.IsBlockAt E₀ a ∨
      ∃ (k : Ix.Kernel.Key .anon) (d : Ix.Kernel.Declaration .anon)
        (ci₀ : Ix.Kernel.ConstantInfo .anon),
        IxVM.Refinement.AddressKey b a k ∧ ci₀.name = k ∧
        d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList ∧
        ci₀ ∈ IxVM.Consistency.installs d) :
    ∃ (E : Ixon.Env) (order : List _root_.Address) (pre : Ix.Kernel.Reader.Prelude .anon)
      (st' : Ix.Kernel.Reader.State .anon) (decls : Array (Ix.Kernel.Reader.CDecl .anon)),
      IxVM.Refinement.Draws E E₀ ∧
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun a => a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList)
        order ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      (∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a) ∧
      (∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a) ∧
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) ∧
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true ∧
      (∀ ds_pre d ds_suf env_pre,
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf →
        IxVM.Consistency.Installs ds_pre env_pre →
        Checked calls env_pre d) ∧
      (∀ a ∈ seeds,
        IxVM.Consistency.IsBlockAt E₀ a ∨
        ∃ (k : Ix.Kernel.Key .anon) (d : Ix.Kernel.Declaration .anon)
          (ci₀ : Ix.Kernel.ConstantInfo .anon),
          IxVM.Refinement.AddressKey b a k ∧ ci₀.name = k ∧
          d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList ∧
          ci₀ ∈ IxVM.Consistency.installs d) := by
  let E := subEnv E₀ Keep supp
  let S := fun a => a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList
  let order := closureOrderByRank t E S (twoTierRank Wk rank iblock)
  refine ⟨E, order, pre, st', decls,
    subEnv_draws E₀ Keep supp hsupp_rec,
    subEnv_withProj_usedClosureOrderAt t E₀ Keep supp S iblock
      hwk_keep hwk_step hwk_rec hextra_kind hextra_refs,
    hpre,
    fun a lc hget => (subEnv_consts_authentic_exact hload hexact₀ hsupp_auth hget).1,
    fun a bytes hget => (hload.2 a bytes hget).2,
    fun a _ lc hget => (subEnv_consts_authentic_exact hload hexact₀ hsupp_auth hget).2,
    hreads, hkeeps, hchk, hseeds⟩

/-! ## Prelude standalone recursor supplements (`preludeRecSupp`) -/

private theorem mem_of_lookup_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {ls : List (α × β)} {k : α} {v : β}, ls.lookup k = some v → (k, v) ∈ ls
  | [], _, _, h => nomatch h
  | (a, b) :: tl, k, v, h => by
    simp only [List.lookup] at h
    cases hbeq : (k == a) with
    | true =>
      rw [hbeq] at h
      injection h with hbv
      subst hbv
      rw [beq_iff_eq.mp hbeq]
      exact List.mem_cons_self
    | false =>
      rw [hbeq] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_some h)

/-- For a `.recr` constant `c` in `records`, extract the inductive block owning `c.refs[0]?`. -/
def preludeRecOwner? (records : List (_root_.Address × Ixon.Constant))
    (c : Ixon.Constant) : Option _root_.Address :=
  match c.info with
  | .recr _ =>
    match c.refs[0]? with
    | some r => (records.lookup r).map (Ix.Cert.ownerOf r)
    | none => none
  | _ => none

private def decodeRawPreludeRow (row : String × String) :
    Option (_root_.Address × Ixon.Constant) := do
  let a ← Ix.Kernel.Reader.addressOfHex row.1
  let b ← bytesOfHex row.2
  match Ixon.deConstantExact b with
  | .ok c => some (a, c)
  | .error _ => none

private def decodeRawPrelude : Option (List (_root_.Address × Ixon.Constant)) :=
  Ix.Kernel.Reader.RoleData.prelude.toList.mapM decodeRawPreludeRow

private theorem decodeRawPrelude_of_forall₂ :
    ∀ {rows : List (String × String)} {out : List (_root_.Address × Ixon.Constant)},
      List.Forall₂ (fun row (p : _root_.Address × Ixon.Constant) =>
        (do
          let some a := Ix.Kernel.Reader.addressOfHex row.1
            | throw s!"prelude: bad address {row.1}"
          let some b := bytesOfHex row.2
            | throw s!"prelude: bad bytes at {row.1}"
          let c ← (Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
            Ix.Kernel.Reader.preludeMaxUnivNodes b).mapError
            (s!"prelude: record {row.1}: " ++ ·)
          pure (a, c) : Except String (_root_.Address × Ixon.Constant)) = .ok p) rows out →
      rows.mapM decodeRawPreludeRow = some out
  | [], [], .nil => rfl
  | row :: rrest, p :: prest, .cons hhd htl => by
    have ih := decodeRawPrelude_of_forall₂ htl
    have hrow : decodeRawPreludeRow row = some p := by
      unfold decodeRawPreludeRow
      cases ha : Ix.Kernel.Reader.addressOfHex row.1 with
      | none => simp [ha] at hhd
      | some a =>
        cases hb : bytesOfHex row.2 with
        | none => simp [ha, hb] at hhd
        | some b =>
          simp only [ha, hb] at hhd
          obtain ⟨c, hdc, hpure⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hhd
          cases hpure
          cases hcan : Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
              Ix.Kernel.Reader.preludeMaxUnivNodes b with
          | error e => simp [hcan, Except.mapError] at hdc
          | ok c' =>
            simp only [hcan, Except.mapError, Except.ok.injEq] at hdc
            subst hdc
            have hbd := (Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hcan).1
            have hex := (Ixon.Verify.BoundedConstant.deConstant_spec _ _ _ _ hbd).2.2
            simp [bind, Option.bind, hex]
    simp [List.mapM_cons, hrow, ih, bind, Option.bind, pure]

private theorem decodeRawPrelude_eq_of_preludeFor {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre) :
    decodeRawPrelude = some pre.records.toList := by
  obtain ⟨hpr, _⟩ := Ix.Cert.ReaderFallback.preludeFor_records hpre
  unfold Ix.Kernel.Reader.preludeRecords Ix.Kernel.Reader.decodeCommitted at hpr
  rw [Array.mapM_eq_mapM_toList] at hpr
  simp only [Functor.map, Except.map] at hpr
  split at hpr
  · cases hpr
  · rename_i ys hr
    cases hpr
    simpa [decodeRawPrelude] using
      decodeRawPrelude_of_forall₂ (Ix.CompileCert.Loop.mapM_forall₂ _ hr)

private def preludeRecsSelfContainedBool : Bool :=
  match decodeRawPrelude with
  | none => false
  | some ls =>
    ls.all fun (a, c) =>
      match c.info with
      | .recr _ =>
        match preludeRecOwner? ls c with
        | some b =>
          (b != a) &&
          (ls.lookup b).isSome &&
          c.refs.toList.all fun r =>
            match ls.lookup r with
            | some cr => Ix.Cert.ownerOf r cr == b
            | none => false
        | none => false
      | _ => true

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
private theorem preludeRecsSelfContained_ok : preludeRecsSelfContainedBool = true := by
  decide +kernel

/-- Every `.recr` record `(a, c)` in `pre.records` has a unique owner block `b ≠ a` in
`pre.records` (`preludeRecOwner? pre.records.toList c = some b`), and every reference `r` in
`c.refs` resolves in `pre.records` to a projection record with `Ix.Cert.ownerOf r cr = b`. -/
theorem preludeRecOwner_spec {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant} {recVal : Ixon.Recursor}
    (hmem : (a, c) ∈ pre.records.toList) (hinfo : c.info = .recr recVal) :
    ∃ b cb, preludeRecOwner? pre.records.toList c = some b ∧
      b ≠ a ∧
      (b, cb) ∈ pre.records.toList ∧
      ∀ r ∈ c.refs.toList, ∃ cr, (r, cr) ∈ pre.records.toList ∧ Ix.Cert.ownerOf r cr = b := by
  have hdec := decodeRawPrelude_eq_of_preludeFor hpre
  have hchk := preludeRecsSelfContained_ok
  unfold preludeRecsSelfContainedBool at hchk
  rw [hdec] at hchk
  have hrow := List.all_eq_true.mp hchk (a, c) hmem
  simp only [hinfo] at hrow
  cases hown : preludeRecOwner? pre.records.toList c with
  | none => rw [hown] at hrow; cases hrow
  | some b =>
    rw [hown, Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne] at hrow
    obtain ⟨⟨hne, hisSome⟩, hall_refs⟩ := hrow
    obtain ⟨cb, hlookup_b⟩ := Option.isSome_iff_exists.mp hisSome
    refine ⟨b, cb, rfl, hne, mem_of_lookup_some hlookup_b, fun r hr => ?_⟩
    have hr_ok := List.all_eq_true.mp hall_refs r hr
    cases hlr : pre.records.toList.lookup r with
    | none => rw [hlr] at hr_ok; cases hr_ok
    | some cr =>
      rw [hlr, beq_iff_eq] at hr_ok
      exact ⟨cr, mem_of_lookup_some hlr, hr_ok⟩

/-- Supplement list supplying committed prelude `.recr` records `(a, serConstant c, c)` whose
prelude inductive block satisfies `KeepBlock`. -/
noncomputable def preludeRecSupp (pre : Ix.Kernel.Reader.Prelude .anon)
    (KeepBlock : _root_.Address → Prop) : List SuppEntry :=
  letI := Classical.propDecidable
  pre.records.toList.filterMap fun (a, c) =>
    match preludeRecOwner? pre.records.toList c with
    | some b => if KeepBlock b then some (a, Ixon.serConstant c, c) else none
    | none => none

theorem mem_preludeRecSupp_iff {pre : Ix.Kernel.Reader.Prelude .anon}
    {KeepBlock : _root_.Address → Prop} {a : _root_.Address} {raw : ByteArray}
    {c : Ixon.Constant} :
    (a, raw, c) ∈ preludeRecSupp pre KeepBlock ↔
      ∃ b, (a, c) ∈ pre.records.toList ∧
        preludeRecOwner? pre.records.toList c = some b ∧
        KeepBlock b ∧ raw = Ixon.serConstant c := by
  classical
  simp only [preludeRecSupp, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨a', c', hm, hfn⟩
    cases hown : preludeRecOwner? pre.records.toList c' with
    | none => simp [hown] at hfn
    | some b =>
      simp only [hown] at hfn
      split_ifs at hfn with hkb
      · injection hfn with htuple
        injection htuple with ha hrest
        injection hrest with hraw hc
        subst ha; subst hraw; subst hc
        exact ⟨b, hm, hown, hkb, rfl⟩
  · rintro ⟨b, hm, hown, hkb, rfl⟩
    refine ⟨a, c, hm, ?_⟩
    simp [hown, hkb]

theorem preludeRecSupp_isRecursorRecord {pre : Ix.Kernel.Reader.Prelude .anon}
    {KeepBlock : _root_.Address → Prop} {entry : SuppEntry}
    (hm : entry ∈ preludeRecSupp pre KeepBlock) :
    IxVM.Refinement.IsRecursorRecord entry.2.2 := by
  rcases entry with ⟨a, raw, c⟩
  obtain ⟨b, _, hown, _, _⟩ := mem_preludeRecSupp_iff.mp hm
  unfold preludeRecOwner? at hown
  cases hinfo : c.info <;> simp [hinfo, IxVM.Refinement.IsRecursorRecord] at hown ⊢

theorem preludeRecSupp_nodup {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (KeepBlock : _root_.Address → Prop) :
    ((preludeRecSupp pre KeepBlock).map (·.1)).Nodup := by
  classical
  have hkeys := Ix.Cert.ReaderFallback.preludeFor_keys hpre
  rw [Array.toList_append, List.map_append, List.nodup_append] at hkeys
  have hpre_nd : (pre.records.toList.map Prod.fst).Nodup := hkeys.1
  unfold preludeRecSupp
  have hsub : ∀ ls : List (_root_.Address × Ixon.Constant),
      (ls.map Prod.fst).Nodup →
      ((ls.filterMap fun (a, c) =>
        match preludeRecOwner? pre.records.toList c with
        | some b => if KeepBlock b then some (a, Ixon.serConstant c, c) else none
        | none => none).map (·.1)).Nodup := by
    intro ls hnd
    induction ls with
    | nil => exact List.nodup_nil
    | cons hd tl ih =>
      rcases hd with ⟨a, c⟩
      rw [List.map_cons, List.nodup_cons] at hnd
      cases hown : preludeRecOwner? pre.records.toList c with
      | none =>
        simp only [List.filterMap_cons, hown]
        exact ih hnd.2
      | some b =>
        simp only [List.filterMap_cons, hown]
        split_ifs
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih hnd.2⟩
          intro hmem
          obtain ⟨⟨a', _, c'⟩, hm_fm, rfl⟩ := List.mem_map.mp hmem
          obtain ⟨⟨a'', c''⟩, hm_tl, hfn⟩ := List.mem_filterMap.mp hm_fm
          dsimp only at hfn
          cases hown' : preludeRecOwner? pre.records.toList c'' with
          | none => simp [hown'] at hfn
          | some b' =>
            simp only [hown'] at hfn
            split_ifs at hfn
            injection hfn with ht
            injection ht with ha_eq _
            subst ha_eq
            exact hnd.1 (List.mem_map.mpr ⟨(a'', c''), hm_tl, rfl⟩)
        · exact ih hnd.2
  exact hsub pre.records.toList hpre_nd

/-! ## Core-backing environment (`coreEnv`) extending `subEnv` with committed fallback records -/

/-- All committed fallback records (`pre.records ++ pre.evidence`) packaged as `SuppEntry` items. -/
def fallbackSupp (pre : Ix.Kernel.Reader.Prelude .anon) : List SuppEntry :=
  (pre.records ++ pre.evidence).toList.map fun (a, c) => (a, Ixon.serConstant c, c)

/-- Core-backing `Ixon.Env` extending `subEnv E₀ Keep supp` with every record in
`pre.records ++ pre.evidence`, so `Core.LoadFacts`, `Core.Good`, and `L1.EnvDecoded` hold
simultaneously across stream and prelude/evidence constants. -/
noncomputable def coreEnv (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) (pre : Ix.Kernel.Reader.Prelude .anon) : Ixon.Env :=
  subEnv E₀
    (fun x => Keep x ∨ ∃ c, (x, c) ∈ pre.records ++ pre.evidence)
    (supp ++ fallbackSupp pre)

theorem fallbackSupp_nodup {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre) :
    ((fallbackSupp pre).map (·.1)).Nodup := by
  have hkeys := Ix.Cert.ReaderFallback.preludeFor_keys hpre
  unfold fallbackSupp
  rwa [List.map_map, show ((fun x : SuppEntry => x.1) ∘
    fun (p : _root_.Address × Ixon.Constant) => (p.1, Ixon.serConstant p.2, p.2)) = Prod.fst from rfl]

/-- **`Core.Good` on `coreEnv E₀ Keep supp pre`** from `RolePreludeInputs` and
`¬ V.HashedCollision extra calls`. -/
theorem coreEnv_good (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env}
    {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (env : Ix.Kernel.Env .anon) (lim : Option Nat)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧
      (V.Preimage a raw ∨ IxVM.Refinement.Hashed calls raw ∨
        (raw ∈ extra ∧ a ≠ Ix.HostAdmission.Merkle.padding)))
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hbound : IxVM.Consistency.Bounded calls) :
    Core.Good ⟨coreEnv E₀ Keep supp pre, env, t, lim⟩ calls := by
  apply good_subEnv_of_noCollision env t lim hload _ hnoCol hbound
  intro a raw c hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact hsupp a raw c h1
  · unfold fallbackSupp at h2
    obtain ⟨⟨a', c'⟩, hmem, heq⟩ := List.mem_map.mp h2
    injection heq with ha hrest
    injection hrest with hraw hc
    subst ha; subst hraw; subst hc
    obtain ⟨himg, hblk, _, hnotPad⟩ :=
      hRP.serConstant_mem_committedImages hpre (Array.mem_toList_iff.mp hmem)
    exact ⟨hblk, Or.inr (Or.inr ⟨hcomm_extra _ himg, hnotPad⟩)⟩

/-- **`L1.EnvDecoded` on `coreEnv E₀ Keep supp pre`** from `Claim.WalkedL6` and exact-decoded
supplements. -/
theorem coreEnv_envDecoded (hRP : RolePreludeInputs)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {seeds : List _root_.Address} {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    (hwalk : Claim.WalkedL6 calls t E₀ seeds)
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp → Ixon.deConstantExact raw = .ok c) :
    L1.EnvDecoded (coreEnv E₀ Keep supp pre) := by
  apply subEnv_envDecoded_of_walkedL6 _ hwalk
  intro a raw c hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact hsupp a raw c h1
  · unfold fallbackSupp at h2
    obtain ⟨⟨a', c'⟩, hmem, heq⟩ := List.mem_map.mp h2
    injection heq with ha hrest
    injection hrest with hraw hc
    subst ha; subst hraw; subst hc
    obtain ⟨_, _, hwf, _⟩ :=
      hRP.serConstant_mem_committedImages hpre (Array.mem_toList_iff.mp hmem)
    exact Ixon.Verify.deConstantExact_serConstant c' hwf

private theorem addSupplements_append_left
    (m₀ base : Std.HashMap _root_.Address Ixon.LazyConstant) :
    ∀ {supp₁ : List SuppEntry} (supp₂ : List SuppEntry)
      {x : _root_.Address} {raw : ByteArray} {c : Ixon.Constant},
      (supp₁.map (·.1)).Nodup → (x, raw, c) ∈ supp₁ → m₀.contains x = false →
      (addSupplements m₀ base (supp₁ ++ supp₂)).get? x = some (Claim.mkLazy raw c)
  | [], _, _, _, _, _, hm, _ => nomatch hm
  | (a, raw₀, c₀) :: rest, supp₂, x, raw, c, hnd, hm, hnc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq
      simp only [List.cons_append, addSupplements, hnc, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true]
    · have hax : a ≠ x := by
        intro heq
        subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(a, raw, c), htl, rfl⟩)
      have ih := addSupplements_append_left m₀ base supp₂ hnd.2 htl hnc
      simp only [List.cons_append, addSupplements]
      split
      · exact ih
      · have hbe : (a == x) = false := beq_eq_false_iff_ne.mpr hax
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
          ← Std.HashMap.get?_eq_getElem?]
        exact ih

/-- Every record in `subEnv E₀ Keep supp` (when `(supp.map (·.1)).Nodup`) is also stored identically
in `coreEnv E₀ Keep supp pre`. -/
theorem recordAt_coreEnv_of_subEnv {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hnd : (supp.map (·.1)).Nodup)
    {a : _root_.Address} {c : Ixon.Constant}
    (hrec : Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c) :
    Ix.Cert.recordAt (coreEnv E₀ Keep supp pre) a = some c := by
  rcases recordAt_subEnv_some_inv E₀ Keep supp hrec with ⟨hk, hrec₀⟩ | ⟨hnc, raw, hm⟩
  · exact recordAt_subEnv_of_keep E₀ _ _ (Or.inl hk) hrec₀
  · unfold coreEnv subEnv Ix.Cert.recordAt
    dsimp only
    rw [addSupplements_append_left E₀.consts _ (fallbackSupp pre) hnd hm hnc]
    rfl

/-- Every committed fallback record `(a, c) ∈ pre.records ++ pre.evidence` is stored at `a` in
`coreEnv E₀ Keep supp pre` whenever `supp` agrees with `pre.records ++ pre.evidence` on shared
addresses. -/
theorem recordAt_coreEnv_of_fallback (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env}
    {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hsupp_compat : ∀ a raw c' c, (a, raw, c') ∈ supp →
      (a, c) ∈ pre.records ++ pre.evidence → c' = c)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence) :
    Ix.Cert.recordAt (coreEnv E₀ Keep supp pre) a = some c := by
  cases hget₀ : E₀.consts.get? a with
  | some lc =>
    obtain ⟨_, _, hrec₀⟩ :=
      hRP.fallback_recordAt_agree hcomm_extra hload hexact₀ hnoCol hpre hmem hget₀
    exact recordAt_subEnv_of_keep E₀ _ _ (Or.inr ⟨c, hmem⟩) hrec₀
  | none =>
    have hnc : E₀.consts.contains a = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hget₀]
      rfl
    have hfb_nd := fallbackSupp_nodup hpre
    have hfb_mem : (a, Ixon.serConstant c, c) ∈ fallbackSupp pre :=
      List.mem_map.mpr ⟨(a, c), Array.mem_toList_iff.mpr hmem, rfl⟩
    unfold coreEnv subEnv Ix.Cert.recordAt
    dsimp only
    have hstep : ∀ (s₁ : List SuppEntry),
        (∀ raw c', (a, raw, c') ∈ s₁ → c' = c) →
        ∃ raw', (addSupplements E₀.consts
          (restrictConsts E₀.consts (fun x => Keep x ∨ ∃ c, (x, c) ∈ pre.records ++ pre.evidence))
          (s₁ ++ fallbackSupp pre)).get? a = some (Claim.mkLazy raw' c) := by
      intro s₁ hcompat₁
      induction s₁ with
      | nil =>
        exact ⟨Ixon.serConstant c,
          addSupplements_get?_of_mem_nodup E₀.consts _ hfb_nd hfb_mem hnc⟩
      | cons hd tl ih =>
        rcases hd with ⟨a₁, raw₁, c₁⟩
        simp only [List.cons_append, addSupplements]
        by_cases ha_eq : a₁ = a
        · subst ha_eq
          have hc_eq := hcompat₁ raw₁ c₁ List.mem_cons_self
          subst hc_eq
          simp only [hnc, Bool.false_eq_true, ↓reduceIte,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true]
          exact ⟨raw₁, rfl⟩
        · obtain ⟨raw', ih'⟩ := ih (fun r' c' hm => hcompat₁ r' c' (List.mem_cons_of_mem _ hm))
          split
          · exact ⟨raw', ih'⟩
          · have hbe : (a₁ == a) = false := beq_eq_false_iff_ne.mpr ha_eq
            rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
              ← Std.HashMap.get?_eq_getElem?]
            exact ⟨raw', ih'⟩
    obtain ⟨raw', hget'⟩ := hstep supp (fun raw c' hm => hsupp_compat a raw c' c hm hmem)
    rw [hget']
    rfl

end IxVM.Refinement.Assembly
