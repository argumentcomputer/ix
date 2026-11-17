import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Assembly.TypingRecParentArm
import IxVMRefinement.Callees.Modeled
import IxVMRefinement.L1.Decode

/-! # A top-walked recursor record: the arm its check took and its family block

The recursor step of the typing fold reads two things off the walk at a top-walked standalone
recursor record `A` (`c.info = .recr rc`):

* `TopWalkCore.recArm`, `TopWalkCore.nativeRecArm`: the walk loaded the record and ran
  `check_const` on the loaded `Rec` value (`Typing.NativeRecArm` at a validating run, its form
  at any limit `RecArmLimAt`). `Ingress::get_ci` of a recursor record returns the
  `Convert::convert_recursor` value (`get_ci_recr_value`); the run store fixes the record the
  load decoded.
* `TopWalkCore.recFamilyNative`: the family block. The `Rec` arm of `check_const` computes the
  block of the recursor's family (`KernelModeled::rec_family_block`: the block of the inductive
  heading the carrier of the first motive) and asserts that `KernelModeled::block_is_modeled`
  answers `0` on it (a recursor of a mutual or nested family is refused). The walk gives that
  observation (`RecFamilyNativeObs`, one instance of what `Typing.NativeRouteAt` quantifies
  over, and `Typing.NativeAt` at a step's context through `NativeObsAt.nativeAt`), the block in
  the run store, the inductive projection record that names it, and that the block has exactly
  one inductive member (`block_is_modeled_zero_count`: the dispatch loads the bytes the run
  hashed at the block's address, which the run store makes unique, and answers `1` at two or
  more inductives and `0` at none).

Nothing here reads the role context: both statements hold at every limit. What the run does not
give without more is `Typing.NativeRouteAt` itself: at a block of one inductive the dispatch's
answer is the circuit's scan of the constructors for a nested occurrence
(`KernelModeled::ctors_nested`), and that every observation of the scan on the same block
answers alike needs a specification of the scan as a function of the stored constructors. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Loads -/

/-- `Ingress::load_verified_constant` on a represented address returning a constant whose info
has the constructor `tag`: the run hashed the bytes at the address, which decode exactly to a
record, and a record whose info is a recursor has the tag `Recr`. -/
private theorem lvc_tag {a : Bytes.Address} {x_addr : SourceValue F} {tag : String}
    {args : List (SourceValue F)} {x_sh x_rf x_un x_bd : SourceValue F} {h m : Heap F}
    {cs calls : List (Call F)} (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn Obs.W "Ingress::load_verified_constant" [x_addr] h
      (.construct "Ixon::Constant" "Mk"
        [.construct "Ixon::ConstantInfo" tag args, x_sh, x_rf, x_un, x_bd]) m cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant), Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = Core.ixAddr a ∧ Ixon.deConstantExact rawBytes = .ok c ∧
      ∀ rc : Ixon.Recursor, c.info = .recr rc → tag = "Recr" := by
  obtain ⟨-, bytes, c, -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
    L1.load_verified_constant_decode_bounded ha ev
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
  subst infoVal
  refine ⟨⟨bytes.toArray⟩, c, Core.hashed_mono hsub hh, haddr, hexact, fun rc hrc => ?_⟩
  rw [hrc] at hinfo
  obtain ⟨rv, hv, -⟩ := hinfo
  injection hv with _ htag _

/-- `Ingress::load_verified_constant` on any argument: the run hashed fewer than `2^32` bytes
that decode exactly to a record the returned value represents. -/
private theorem lvc_decode_any {a r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Ingress::load_verified_constant" [a] h r h' cs) :
    ∃ (raw : ByteArray) (c : Ixon.Constant), raw.size < 4294967296 ∧ Hashed cs raw ∧
      Ixon.deConstantExact raw = .ok c ∧ L1.RepConstant h' c r := by
  obtain ⟨v1, m14, cs24, x_idx, x_len, v55, m56, cs66, v92, m93, cs103, m123, cs133, x_constant,
    x_rest, ld11, -⟩ := Obs.«Ingress::load_verified_constant».obs ev
  obtain ⟨bytes, inp, rest, m, cs', length, -, hst, hashed, -, hget, hrest, -⟩ :=
    L1.load_verified_constant_spec ld11 ev
  have hst0 : L1.Stream m (bytes.drop 0) inp := by
    rw [List.drop_zero]
    exact hst
  obtain ⟨-, c, n, cVal, restPtr, hok, heq, -, -, -, -, -, cRep, hdropRep⟩ :=
    L1.get_constant_spec hst0 hget
  simp only [Nat.zero_add] at hok hdropRep
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
  obtain ⟨_, _⟩ := heq
  subst cVal restPtr
  have hdrop_nil : bytes.drop n = [] := L1.repList_nil_of_load hdropRep hrest
  have hlen_le : bytes.length ≤ n := List.drop_eq_nil_iff.mp hdrop_nil
  have hspan := Ixon.Verify.ConstantBounds.getConstant_bound
    { idx := 0, bytes := ⟨bytes.toArray⟩ } { idx := n, bytes := ⟨bytes.toArray⟩ } c
    (Nat.zero_le _) hok
  have hn_le : n ≤ bytes.length := by simpa [ByteArray.size] using hspan.within
  have hn_eq : n = (⟨bytes.toArray⟩ : ByteArray).size := by
    simp only [ByteArray.size, List.size_toArray]
    omega
  have hexact : Ixon.deConstantExact ⟨bytes.toArray⟩ = .ok c := by
    unfold Ixon.deConstantExact Ixon.runGetExact EStateM.run
    rw [hok]
    simp [hn_eq]
  exact ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using length,
    hashed, hexact, cRep⟩

/-! ## What `Ingress::get_ci` returns -/

/-- **`Ingress::get_ci` at a recursor record returns a `Rec` value**: the run hashed the bytes
at the address, which decode exactly to a record, and when the record is a recursor the
returned pointer holds the `Rec` value `Convert::convert_recursor` built. -/
theorem get_ci_recr_value {a : Bytes.Address} {x_addr r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_addr] h r h' calls) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant), Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = Core.ixAddr a ∧ Ixon.deConstantExact rawBytes = .ok c ∧
      ∀ rc : Ixon.Recursor, c.info = .recr rc →
        ∃ (levels type parameters indices motives minors rules k unsafeFlag block position :
          SourceValue F),
          loadValue h' r = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
            [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
              position]) := by
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (ev14 := ev14) (hc302 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .Defn_other (ev14 := ev14) (hc423 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .Axio (ev14 := ev14) (hc515 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .Quot (ev14 := ev14) (hc606 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .DPrj (ev14 := ev14) (hc675 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .IPrj (ev14 := ev14) (hc750 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .CPrj (ev14 := ev14) (hc851 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .RPrj (ev14 := ev14) (hc926 := hc) .. =>
    obtain ⟨raw, c, hh, hba, hx, htag⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    exact ⟨raw, c, hh, hba, hx, fun rc hrc => absurd (htag rc hrc) (by decide)⟩
  | .Recr (m978 := m978) (v977 := v977) (ev14 := ev14) (he981 := hr) (hm980 := hh)
      (ev987 := conv) (hc1071 := hc) .. =>
    obtain ⟨raw, c, hhash, hba, hx, -⟩ := lvc_tag (calls := calls) ha ev14 (by rw [hc]; intro x hx; simp [hx])
    refine ⟨raw, c, hhash, hba, hx, fun rc hrc => ?_⟩
    match Obs.«Convert::convert_recursor».obs conv with
    | .run (he237 := hv) .. =>
      rw [hr, hh, hv]
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, loadValue_snoc_self m978 _⟩

/-! ### The conversions return no `Induct` value -/

private theorem convert_definition_ne_induct {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_definition" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_definition».obs ev with
  | .Definition (he242 := he) .. | .Opaque (he329 := he) .. | .Theorem (he373 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_axiom_ne_induct {a₁ a₂ a₃ a₄ a₅ a₆ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_axiom" [a₁, a₂, a₃, a₄, a₅, a₆] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_axiom».obs ev with
  | .run (he107 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_quotient_ne_induct {a₁ a₂ a₃ a₄ a₅ a₆ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_quotient" [a₁, a₂, a₃, a₄, a₅, a₆] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_quotient».obs ev with
  | .run (he107 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_constructor_ne_induct {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_constructor" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] h r h'
      cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_constructor».obs ev with
  | .run (he134 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_recursor_ne_induct {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_recursor" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] h r h'
      cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_recursor».obs ev with
  | .run (he237 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

/-- **`Ingress::get_ci` returning an inductive, on any argument**: the loaded record is an
inductive projection record (the run hashed its bytes, which decode exactly to it) naming a
block the run loaded, with an inductive member at the projection's index; the block field of
the returned value represents that block's address. -/
theorem get_ci_induct_head {x_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_addr] h r h' calls)
    {nl ty np ni nc u x_blk idx : SourceValue F}
    (hld : loadValue h' r = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [nl, ty, np, ni, nc, u, x_blk, idx])) :
    ∃ (b : Bytes.Address) (raw : ByteArray) (c : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Bytes.RepAddressRef Core.addrTy h' b x_blk ∧
      raw.size < 4294967296 ∧ Hashed calls raw ∧ Ixon.deConstantExact raw = .ok c ∧
      c.info = .iPrj ip ∧ ip.block = Core.ixAddr b ∧
      BlockLoad calls (Core.ixAddr b) cb ms ∧ ms.toList[ip.idx.toNat]? = some (.indc ind) := by
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (he219 := hr) (hm218 := hh) (ev225 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_definition_ne_induct conv _)
  | .Defn_other (he340 := hr) (hm339 := hh) (ev346 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_definition_ne_induct conv _)
  | .Axio (he441 := hr) (hm440 := hh) (ev447 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_axiom_ne_induct conv _)
  | .Quot (he532 := hr) (hm531 := hh) (ev538 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_quotient_ne_induct conv _)
  | .Recr (he981 := hr) (hm980 := hh) (ev987 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_recursor_ne_induct conv _)
  | .DPrj (ev650 := ev650) .. =>
    match Obs.«Ingress::get_ci_dprj».obs ev650 with
    | .run (he230 := hr) (hm229 := hh) (ev236 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self] at hld
      exact absurd (Except.ok.inj hld) (convert_definition_ne_induct conv _)
  | .CPrj (ev800 := ev800) .. =>
    match Obs.«Ingress::get_ci_cprj».obs ev800 with
    | .run (he251 := hr) (hm250 := hh) (ev257 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self] at hld
      exact absurd (Except.ok.inj hld) (convert_constructor_ne_induct conv _)
  | .RPrj (ev896 := ev896) .. =>
    match Obs.«Ingress::get_ci_rprj».obs ev896 with
    | .run (he170 := hr) (hm169 := hh) (ev176 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self] at hld
      exact absurd (Except.ok.inj hld) (convert_recursor_ne_induct conv _)
  | .IPrj (m2 := m2) (x_idx := x_idx) (x_block_addr := x_blk') (cs718 := csi) (v722 := v722)
      (m731 := m731) (cs12 := cs12) (ev14 := ev14) (ev741 := ev741) (ev720 := ev720)
      (hc750 := hc) .. =>
    obtain ⟨raw, c₀, hsz, hh, hx, cRep⟩ := lvc_decode_any ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨⟨idx', blk⟩, hci, hx_idx, hblk_ix⟩ := L1.repConstantInfo_iPrj_inv hinfo
    have hx_idx' : x_idx = TagN.u64Value idx'.toNat := hx_idx
    subst hx_idx'
    obtain ⟨hidx56, hv722, hm731⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 idx') ev741
    subst v722 m731
    obtain ⟨b, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    have hb_eq' : Core.ixAddr b = blk := hb_eq
    obtain ⟨cb, ms, ind, hbl, hmem, nl', ty', np', ni', u', hld'⟩ := get_ci_iprj_head hb_rep ev720
    rw [L1.val_cast_u56_ing hidx56] at hmem
    have hv := Except.ok.inj (hld.symm.trans hld')
    injection hv with _ _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hxb _
    subst hxb
    have hsubi : ∀ x ∈ csi, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    have hsub12 : ∀ x ∈ cs12, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    exact ⟨b, raw, c₀, ⟨idx', blk⟩, cb, ms, ind,
      Bytes.repAddressRef_heapMono₂ Core.addrTy ev720.heap_extends hb_rep, hsz,
      Core.hashed_mono hsub12 hh, hx, hci, hb_eq'.symm, hbl.mono hsubi, hmem⟩

/-! ## The dispatch on a block of one inductive -/

private theorem mutShape_of_repMutConst_rec {h : Heap F} {m : Ixon.MutConst}
    {v : SourceValue F} (hr : L1.RepMutConst h m v) : Specs.Callees.MutShape h m v := by
  cases m with
  | defn d => obtain ⟨dv, hv, _⟩ := hr; exact ⟨dv, hv⟩
  | indc i => obtain ⟨iv, hv, _⟩ := hr; exact ⟨iv, hv⟩
  | recr r => obtain ⟨rv, hv, _⟩ := hr; exact ⟨rv, hv⟩

private theorem membersRep_of_repMutConstList_rec {h : Heap F}
    {xs : List Ixon.MutConst} {p : SourceValue F}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» L1.RepMutConst h xs p) :
    Specs.Callees.MembersRep h xs p := by
  induction hrep with
  | nil cell => exact .nil cell
  | cons cell rh _ ih => exact .cons cell (mutShape_of_repMutConst_rec rh) ih

/-- **A dispatch answering `0` at a loaded block with an inductive member: the block has exactly
one inductive member.** `KernelModeled::block_is_modeled` loads the bytes the run hashed at the
block's address (the run store makes them unique), answers `1` at two or more inductive members
and `0` at none; the count is read below `2^39` (a loaded record has fewer than `2^32`
bytes). -/
theorem block_is_modeled_zero_count {fb : SourceValue F} {h h' : Heap F}
    {cs calls : List (Call F)} {E₀ : Ixon.Env} {b : Bytes.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive}
    (hS : LoadedReads.RunStore calls E₀) (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hb : Bytes.RepAddressRef Core.addrTy h b fb)
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [fb] h (.field 0) h' cs)
    (hbl : BlockLoad calls (Core.ixAddr b) cb ms) (hi : ms.toList[i]? = some (.indc ind)) :
    (ms.toList.filter Specs.Callees.isIndc).length = 1 := by
  obtain ⟨bytes₀, hsz₀, hh₀, hb₀, hx₀, hinfo₀⟩ := hbl
  -- the dispatch's load of the block is the run's record at the address
  have hload : ∀ {x_info w39 w40 w41 w42 : SourceValue F} {m2 : Heap F} {cs12 : List (Call F)},
      ObsFn Obs.W "Ingress::load_verified_constant" [fb] h
        (.construct "Ixon::Constant" "Mk" [x_info, w39, w40, w41, w42]) m2 cs12 →
      (∀ cl ∈ cs12, cl ∈ calls) → L1.RepConstantInfo m2 cb.info x_info := by
    intro x_info w39 w40 w41 w42 m2 cs12 ev14 hs12
    obtain ⟨-, bytes, c, -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hb ev14
    have hraw : (⟨bytes.toArray⟩ : ByteArray) = bytes₀ :=
      hS.hashed_inj (Core.hashed_mono hs12 hh) hh₀ (haddr.trans hb₀.symm)
    rw [hraw, hx₀] at hexact
    have hcc : cb = c := Except.ok.inj hexact
    subst hcc
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    exact hinfo
  have hmembers : ∀ {x_members : SourceValue F} {m2 : Heap F},
      L1.RepConstantInfo m2 cb.info (.construct "Ixon::ConstantInfo" "Muts" [x_members]) →
      Specs.Callees.MembersRep m2 ms.toList x_members := by
    intro x_members m2 hrep
    rw [hinfo₀] at hrep
    obtain ⟨msPtr, hmk, hms⟩ := hrep
    injection hmk with _ _ hl
    injection hl with hl1 _
    subst hl1
    exact membersRep_of_repMutConstList_rec hms
  -- the count is small and positive
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes₀ cb hx₀
  have hsize := muts_size_le hinfo₀
  have hfle := List.length_filter_le Specs.Callees.isIndc ms.toList
  have hlen : ms.toList.length = ms.size := Array.length_toList
  have h39 : (549755813888 : Nat) ≤ 2 ^ 39 := by norm_num
  have hflen : (ms.toList.filter Specs.Callees.isIndc).length < 2 ^ 39 := by omega
  have hmemf : Ixon.MutConst.indc ind ∈ ms.toList.filter Specs.Callees.isIndc :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? hi, rfl⟩
  have hpos : 0 < (ms.toList.filter Specs.Callees.isIndc).length := by
    cases hf : ms.toList.filter Specs.Callees.isIndc with
    | nil =>
      rw [hf] at hmemf
      cases hmemf
    | cons _ _ => simp
  match Obs.«KernelModeled::block_is_modeled».obs ev with
  | .Muts_n0 (ev14 := ev14) (ev103 := ev103) (hc118 := hc) .. =>
    have hrep := hload ev14 (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec (hmembers hrep) ev103
    have hk0 : (ms.toList.filter Specs.Callees.isIndc).length = 0 :=
      (ModeledAux.natCast_inj_lt (by decide) hflen (Value.field.inj hcnt)).symm
    omega
  | .Muts_n1 (ev14 := ev14) (ev103 := ev103) (hc241 := hc) .. =>
    have hrep := hload ev14 (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec (hmembers hrep) ev103
    exact (ModeledAux.natCast_inj_lt (a := 1) (by decide) hflen
      (by simpa using Value.field.inj hcnt)).symm
  | .Muts_other (he246 := hr) .. =>
    exact absurd (Value.field.inj hr) (by decide)
  | .other (ev14 := ev14) (hne249 := hne) (hc255 := hc) .. =>
    have hrep := hload ev14 (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    rw [hinfo₀] at hrep
    obtain ⟨msPtr, hmk, -⟩ := hrep
    exact absurd hmk (hne [msPtr] rfl)

/-! ## The observations -/

/-- **One observation of the dispatch on `B` answered native**: one instance of what
`Typing.NativeRouteAt calls B` quantifies over. -/
def NativeObsAt (calls : List (Call F)) (B : _root_.Address) : Prop :=
  ∃ (bp : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
    ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' cs ∧
    (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧ Core.ixAddr b = B

/-- At a step's context (the run good for it), the observation is the tree's `NativeAt`. -/
theorem NativeObsAt.nativeAt {calls : List (Call F)} {B : _root_.Address} {c : Core.Ctx}
    (hobs : NativeObsAt calls B) (hg : Core.Good c calls) : Typing.NativeAt c.E B := by
  obtain ⟨bp, h, h', cs, b, ev, hsub, hb, rfl⟩ := hobs
  exact Typing.nativeAt_of_route ev hsub hg hb

/-- **The family block of the record at `A`, as the check computed it, answered native**:
`KernelModeled::rec_family_block` on a pointer to `A` returned a pointer to `B`, and
`KernelModeled::block_is_modeled` on that pointer answered `0`, each within the run. -/
def RecFamilyNativeObs (calls : List (Call F)) (A B : _root_.Address) : Prop :=
  ∃ (h₁ h₂ : Heap F) (ap fb : SourceValue F) (cs₁ : List (Call F)) (b : Bytes.Address),
    S0.addr h₁ ap A ∧
    ObsFn Obs.W "KernelModeled::rec_family_block" [ap] h₁ fb h₂ cs₁ ∧
    (∀ cl ∈ cs₁, cl ∈ calls) ∧
    Bytes.RepAddressRef Core.addrTy h₂ b fb ∧ Core.ixAddr b = B ∧
    ∃ (h₃ : Heap F) (cs₂ : List (Call F)),
      ObsFn Obs.W "KernelModeled::block_is_modeled" [fb] h₂ (.field 0) h₃ cs₂ ∧
      (∀ cl ∈ cs₂, cl ∈ calls)

theorem RecFamilyNativeObs.nativeObs {calls : List (Call F)} {A B : _root_.Address}
    (h : RecFamilyNativeObs calls A B) : NativeObsAt calls B := by
  obtain ⟨h₁, h₂, ap, fb, cs₁, b, -, -, -, hb, hB, h₃, cs₂, ev, hsub⟩ := h
  exact ⟨fb, h₂, h₃, cs₂, b, ev, hsub, hb, hB⟩

/-! ## The recursor arm at the walk -/

/-- **The walk's check of the record at `A` took the recursor arm, at the limit `lim`**: the
walk loaded the record and ran `check_const` on the loaded `Rec` value (`Typing.NativeRecArm`
over `RCLimRep`). -/
def RecArmLimAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (A : _root_.Address) (lim : Option Nat) : Prop :=
  ∃ (h_pre m_chk h'_chk : Heap F) (rc ap ptr r_chk : SourceValue F)
    (levels type parameters indices motives minors rules k unsafeFlag block position :
      SourceValue F)
    (cs_load cs_chk : List (Call F)),
    RCLimRep t bAddr lim h_pre rc ∧ RCLimRep t bAddr lim m_chk rc ∧
    S0.addr h_pre ap A ∧ S0.addr m_chk ap A ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
      [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position]) ∧
    ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position],
        ap] m_chk r_chk h'_chk cs_chk ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

section Walk

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {seeds : List _root_.Address} {E₀ : Ixon.Env} {Top : _root_.Address → Prop}
  {rank : _root_.Address → Nat}

/-- **A top-walked recursor record's check took the recursor arm**, at every limit. -/
theorem TopWalkCore.recArm {lim : Option Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) :
    RecArmLimAt calls bAddr t A lim := by
  obtain ⟨c', hc', hchk⟩ := hW.checked A hT
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  rcases hchk with ⟨ms, hms, -⟩ | hdirect
  · rw [hinfo] at hms
    cases hms
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hdirect
  obtain ⟨ab, hab, hA⟩ := ha_pre
  obtain ⟨raw, c', hh, hba, hx, hrec⟩ := get_ci_recr_value hab ev_ld
  have hrec₀ : Ix.Cert.recordAt E₀ (Core.ixAddr ab) = some c := by
    rw [hA]
    exact (hW.runStore.recordOf_eq_recordAt A).symm.trans hc
  have hcc : c' = c := hW.runStore.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hx
  subst c'
  obtain ⟨levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
    position, hv⟩ := hrec rc hinfo
  have hvv := Except.ok.inj (hld.symm.trans hv)
  subst hvv
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, k, unsafeFlag, block, position, cs_load, cs_chk, hrc_pre, hrc_m,
    ⟨ab, hab, hA⟩, ha_m, ev_ld, hsub_ld, hv, ev_chk, hsub_chk⟩

/-- **`NativeRecArm` from the walk** at a validating run: the recursor step's evidence at the
record (`CheckedLimAt … (some n)` is `CheckedAtFullAt … n`). -/
theorem TopWalkCore.nativeRecArm {n : Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ (some n) Top rank) {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) :
    Typing.NativeRecArm calls bAddr t A n := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, k, unsafeFlag, block, position, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre, ha_m,
    ev_ld, hsub_ld, hld, ev_chk, hsub_chk⟩ := hW.recArm hT hc hinfo
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, k, unsafeFlag, block, position, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre, ha_m,
    ev_ld, hsub_ld, hld, ev_chk, hsub_chk⟩

/-- **A8: the family block of a top-walked recursor record is a block of one inductive that the
check found native**, at every limit. The `Rec` arm of `check_const` computed the family block
`B` (`rec_family_block`: the block of the inductive heading the carrier of the first motive)
and its dispatch on `B` answered `0` (`RecFamilyNativeObs`); `B` is the run store's block
record, with exactly one inductive member; an inductive projection record of the store names
`B` at an inductive member (the record `rec_family_block` loaded at the carrier's head). -/
theorem TopWalkCore.recFamilyNative {lim : Option Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) :
    ∃ (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      RecFamilyNativeObs calls A B ∧ recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧
      (ms.toList.filter Specs.Callees.isIndc).length = 1 ∧
      ∃ (P₀ : _root_.Address) (c₀ : Ixon.Constant) (ip : Ixon.InductiveProj),
        recordOf E₀ P₀ = some c₀ ∧ c₀.info = .iPrj ip ∧ ip.block = B ∧
        ∃ ind, ms.toList[ip.idx.toNat]? = some (.indc ind) := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, k, unsafeFlag, block, position, cs_load, cs_chk, -, -, -, ha_m,
    -, -, -, ev_chk, hsub_chk⟩ := hW.recArm hT hc hinfo
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := shape) ..
  | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) ..
  | .Quot (hv1076 := shape) ..
  | .Induct_n0 (hv1240 := shape) ..
  | .Induct_other_n0 (hv1240 := shape) ..
  | .Induct_other_other (hv1240 := shape) ..
  | .Ctor_n0_n0 (hv1941 := shape) ..
  | .Ctor_n0_other (hv1941 := shape) ..
  | .Ctor_other_n0 (hv1941 := shape) ..
  | .Ctor_other_other (hv1941 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Rec_other (heq2925 := native) (hne2998 := modeled) .. =>
    exact absurd native modeled
  | .Rec_n0 (m2 := scopeBefore) (m2693 := scopeAfter) (m2761 := sortBefore)
      (m2730 := sortAfter) (m2774 := safeAfter) (m2804 := rulesAfter) (m2834 := kindsAfter)
      (v2855 := fb) (cs2866 := famCalls) (cs2888 := modCalls)
      (ev14 := unsafeRun) (ev2705 := scopeRun) (hm2769 := nilSort)
      (ev2742 := sortRun) (ev2786 := safeRun) (ev2816 := rulesRun) (ev2846 := kindsRun)
      (ev2868 := familyRun) (ev2890 := modeledRun) (hc2997 := allCalls) .. =>
    have e1 : Heap.Extends scopeAfter sortBefore := by
      rw [nilSort]
      exact Heap.Extends.snoc _ _
    have hext : Heap.Extends m_chk kindsAfter :=
      unsafeRun.heap_extends.trans (scopeRun.heap_extends.trans (e1.trans
        (sortRun.heap_extends.trans (safeRun.heap_extends.trans (rulesRun.heap_extends.trans
          kindsRun.heap_extends)))))
    have hsubF : ∀ cl ∈ famCalls, cl ∈ calls :=
      fun cl hcl => hsub_chk cl (by rw [allCalls]; simp [hcl])
    have hsubM : ∀ cl ∈ modCalls, cl ∈ calls :=
      fun cl hcl => hsub_chk cl (by rw [allCalls]; simp [hcl])
    match Obs.«KernelModeled::rec_family_block».obs familyRun with
    | .run (cs266 := headCalls) (ev268 := headLoad) (ld262 := headInfo) (he331 := hfb)
        (he332 := hheap) (hc333 := famEq) .. =>
      subst hfb hheap
      have hsubH : ∀ cl ∈ headCalls, cl ∈ calls :=
        fun cl hcl => hsubF cl (by rw [famEq]; simp [hcl])
      obtain ⟨b, raw, c₀, ip, cb, ms, ind, hbrep, hsz, hh, hx, hci, hblk, hbl, hmem⟩ :=
        get_ci_induct_head headLoad headInfo
      have hbl' := hbl.mono hsubH
      obtain ⟨hrecB, hcbi⟩ := hbl'.stored hW.hashedStored
      have hcount := block_is_modeled_zero_count hW.runStore hsubM hbrep modeledRun hbl' hmem
      exact ⟨Core.ixAddr b, cb, ms,
        ⟨_, _, ap, _, famCalls, b, S0.addr_mono hext ha_m, familyRun, hsubF, hbrep, rfl,
          _, modCalls, modeledRun, hsubM⟩,
        hrecB, hcbi, hcount, Address.blake3Pure raw, c₀, ip,
        recordOf_of_hashed hW.hashedStored (Core.hashed_mono hsubH hh) hsz hx, hci, hblk,
        ind, hmem⟩

end Walk

end IxVM.Refinement.Claim
