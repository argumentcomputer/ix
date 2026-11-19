import IxVMRefinement.Claim.TopWalkCheck

/-! # The claim walk at a limit, with the operation order of every reference it walks

A validation below the well-founded block walks a used reference `b` under `walk_ctx(rc, b)`,
which asserts `KernelRoles::assert_op_reached_in_order`: an operation bound at `b` is of a group
below the limit, when the limit is below the well-founded block (33). The walk's specification
`run_check_transitive_lim_spec` does not keep that assertion. This module repeats its induction
(`Claim/TopWalkCheck.lean`) with it:

* `OpOrderedAt t lim b`: an operation bound at `b` is of a group below `n`, at `lim = some n`
  with `n < 33`.
* `assert_op_reached_in_order_spec`, `walk_ctx_ordered`: the assertion, and `walk_ctx` at a
  limit gives `OpOrderedAt`.
* `TopRecsOrdered recs`: every used reference of a record of the walk is `OpOrderedAt` or covered
  at the limit.
* `run_check_transitive_lim_ordered`, `walk_refs_transitive_lim_ordered`: the walk's closed list,
  as in `run_check_transitive_lim_spec`, with `TopRecsOrdered`, and each walked reference ordered
  or covered. -/

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

/-! ## The order assertion -/

/-- **An operation bound at `b` is in force at `lim`**, when `lim` is below the well-founded
block: what `walk_ctx`'s `assert_op_reached_in_order` asserts. -/
def OpOrderedAt (t : Ix.Kernel.RoleTable) (lim : Option Nat) (b : _root_.Address) : Prop :=
  ∀ ro : Ix.Kernel.Role, t.addressOf? ro = some b → RoleVal.roleSpecKindNat ro = 2 →
    ∀ n, lim = some n → n < 33 → Ix.SpecDigest.groupOf ro < n

/-- **`KernelRoles::assert_op_reached_in_order(r, g, limit)`** at a role, its group and a limit
below the well-founded block: an operation's group is below the limit. -/
theorem assert_op_reached_in_order_spec {ro : Ix.Kernel.Role} {n : Nat} (hn : n < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::assert_op_reached_in_order"
      [.field (roleNum ro), .field (Ix.SpecDigest.groupOf ro : F), .field (n : F)] h r h' calls) :
    RoleVal.roleSpecKindNat ro = 2 → n < 33 → Ix.SpecDigest.groupOf ro < n := by
  intro h2 h33
  have hnv : ZMod.val (n : F) = n := RolesAux.val_natCast (Nat.lt_trans hn (by decide))
  have h33v : ZMod.val (33 : F) = 33 := RolesAux.val_natCast (by decide)
  match Obs.«KernelRoles::assert_op_reached_in_order».obs ev with
  | .n2_n1 (ev63 := ev63) (ev92 := ev92) (heq115 := heq) .. =>
    obtain ⟨hlt, -, hiff, -, -⟩ := Lib.less_than_fields_field ev92
    have h1 := hiff.mp heq
    rwa [RolesAux.val_groupOf, hnv] at h1
  | .n2_other (ev63 := ev63) (ev42 := ev42) (hne121 := hne) .. =>
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_well_founded_group».obs ev63
    obtain ⟨-, -, hiff, -, -⟩ := Lib.less_than_fields_field ev42
    exact absurd (hiff.mpr (by rw [hnv, h33v]; exact h33)) hne
  | .other (ev15 := ev15) (hne130 := hne) .. =>
    obtain ⟨hk, -⟩ := RoleVal.role_spec_kind_spec ev15
    exact absurd (by rw [hk, h2]; simp) hne

private theorem sub_one_roleNum_ord {ro : Ix.Kernel.Role} {v : SourceValue F}
    (op : evalBinOp .sub (.field (roleNum ro + 1)) (.field 1) = .ok v) :
    v = .field (roleNum ro) := by
  simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op
  exact op.symm

/-- **`KernelRoles::walk_ctx` at a limit orders the reference**: an operation bound at it is in
force, when the limit is below the well-founded block. -/
theorem walk_ctx_ordered {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc) (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::walk_ctx" [x_rc, x_a] h r h' calls) : OpOrderedAt t lim a := by
  intro ro hro h2 n hn h33
  obtain ⟨tbl, htbl, ⟨n', rfl, hn', hl⟩ | ⟨rfl, hl⟩⟩ := hrc.cases
  · have e : n' = n := Option.some.inj hn
    subst e
    have hwf : t.wf = true := htbl.1
    have hinj : ∀ ro', t.addressOf? ro' = some a → ro' = ro := by
      intro ro' h'
      have hk := (keyOf_of_addressOf hwf h').symm.trans (keyOf_of_addressOf hwf hro)
      injection hk
    match Obs.«KernelRoles::walk_ctx».obs ev with
    | .Mk_n0 (ld12 := ld12) (ev71 := ev71) (ev49 := ev49) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨-, -, hlk⟩ := addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨-, hnone⟩ | ⟨ro', hv', -⟩
      · exact absurd hro (hnone ro)
      · exact absurd (Value.field.inj hv') (fun e => RolesAux.roleNum_add_one_ne_zero ro' e.symm)
    | .Mk_other_n0 (ld12 := ld12) (ev71 := ev71) (ev49 := ev49) (hne104 := hne)
        (op136 := op136) (ev121 := ev121) (op168 := op168) (ev151 := ev151) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, hlk⟩ := addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨rfl, -⟩ | ⟨ro', rfl, hof⟩
      · exact absurd rfl hne
      · obtain rfl := hinj ro' hof
        rw [sub_one_roleNum_ord op136] at ev121
        rw [sub_one_roleNum_ord op168] at ev151
        obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev121
        exact assert_op_reached_in_order_spec hn' ev151 h2 h33
    | .Mk_other_other (ld12 := ld12) (ev71 := ev71) (ev49 := ev49) (hne104 := hne)
        (op136 := op136) (ev121 := ev121) (op168 := op168) (ev151 := ev151) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, hlk⟩ := addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨rfl, -⟩ | ⟨ro', rfl, hof⟩
      · exact absurd rfl hne
      · obtain rfl := hinj ro' hof
        rw [sub_one_roleNum_ord op136] at ev121
        rw [sub_one_roleNum_ord op168] at ev151
        obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev121
        exact assert_op_reached_in_order_spec hn' ev151 h2 h33
    | .Assumed (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
  · cases hn

/-! ## The walk's records, ordered -/

/-- **Every used reference of a record of the walk is ordered or covered** at the limit. -/
def TopRecsOrdered {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} (recs : List (TopRec calls bAddr t lim)) : Prop :=
  ∀ r ∈ recs, ∀ i ∈ S0.usedRefIdxs r.c, ∀ b, r.c.refs[i]? = some b →
    OpOrderedAt t lim b ∨ CoveredAt t lim b

theorem TopRecsOrdered.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (TopRec cs₁ bAddr t lim)}
    (h : TopRecsOrdered recs) : TopRecsOrdered (recs.map (TopRec.mono hsub)) := by
  intro r hr i hi b hb
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  exact h r₀ hr₀ i hi b hb

theorem TopRecsOrdered.append {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {r₁ r₂ : List (TopRec calls bAddr t lim)}
    (h₁ : TopRecsOrdered r₁) (h₂ : TopRecsOrdered r₂) : TopRecsOrdered (r₁ ++ r₂) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact h₁ r h
  · exact h₂ r h

theorem topRecsOrdered_nil {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} :
    TopRecsOrdered ([] : List (TopRec calls bAddr t lim)) :=
  fun _ h => (nomatch h)

/-! ## Helpers (copies of the private helpers of `Claim/TopWalkCheck.lean`) -/

private theorem mutShape_of_repMutConst_ord {h : Heap F} {m : Ixon.MutConst}
    {v : SourceValue F} (hr : RepMutConst h m v) : Specs.Callees.MutShape h m v := by
  cases m with
  | defn d => obtain ⟨dv, hv, _⟩ := hr; exact ⟨dv, hv⟩
  | indc i => obtain ⟨iv, hv, _⟩ := hr; exact ⟨iv, hv⟩
  | recr r => obtain ⟨rv, hv, _⟩ := hr; exact ⟨rv, hv⟩

private theorem membersRep_of_repMutConstList_ord {h : Heap F}
    {xs : List Ixon.MutConst} {p : SourceValue F}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» RepMutConst h xs p) :
    Specs.Callees.MembersRep h xs p := by
  induction hrep with
  | nil cell => exact .nil cell
  | cons cell rh _ ih => exact .cons cell (mutShape_of_repMutConst_ord rh) ih

private theorem refs_size_lt_bound_ord {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private theorem topRec_mono_depth_lt_ord {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {n : Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (TopRec cs₁ bAddr t lim)}
    (hdep : ∀ r ∈ recs, r.depth ≤ cs₁.length) (hlt : cs₁.length < n) :
    ∀ r ∈ recs.map (TopRec.mono hsub), r.depth < n := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  have hd := hdep r₀ hr₀
  simp only [TopRec.mono]
  omega

private theorem topRec_mono_depth_le_ord {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {n : Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (TopRec cs₁ bAddr t lim)}
    (hdep : ∀ r ∈ recs, r.depth ≤ cs₁.length) (hle : cs₁.length ≤ n) :
    ∀ r ∈ recs.map (TopRec.mono hsub), r.depth ≤ n := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  have hd := hdep r₀ hr₀
  simp only [TopRec.mono]
  omega

/-- Close a list of records with a new head record. -/
private theorem topRecsClosed_cons_ord {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {r₀ : TopRec calls bAddr t lim} {rest : List (TopRec calls bAddr t lim)}
    (hrest : TopRecsClosed rest)
    (hown : IsProjRec r₀.c →
      ∃ r' ∈ r₀ :: rest, r'.addr = Ix.Cert.ownerOf r₀.addr r₀.c ∧ r'.depth < r₀.depth)
    (hrefs : ∀ i ∈ S0.usedRefIdxs r₀.c, ∀ b, r₀.c.refs[i]? = some b →
      RefAllowedIn calls t bAddr lim b ∧
      ((NotBlockIn calls b ∧ ∃ r' ∈ r₀ :: rest, r'.addr = b ∧ r'.depth < r₀.depth) ∨
        CoveredAt t lim b)) :
    TopRecsClosed (r₀ :: rest) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hmem
  · exact ⟨hown, hrefs⟩
  · exact TopRecsClosed.sub (ys := r₀ :: rest) (fun x hx => List.mem_cons_of_mem _ hx) hrest r hmem

/-! ## `run_check_transitive` and `walk_refs_transitive` at a limit, ordered -/

private theorem run_check_transitive_lim_ordered_aux {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {lim : Option Nat} :
    ∀ (fuel : Nat),
      (∀ {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         RCLimRep t bAddr lim h x_rc →
         S0.addr h x_addr addr →
         ObsFn Obs.W "KernelClaim::run_check_transitive" [x_rc, x_addr] h r h' calls →
         Heap.Extends h h' ∧
         ∃ recs : List (TopRec calls bAddr t lim),
           addr ∈ recs.map (·.addr) ∧
           TopRecsClosed recs ∧
           TopRecsOrdered recs ∧
           (∀ r ∈ recs, r.depth ≤ calls.length)) ∧
      (∀ {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
         {x_rc x_refs x_consts r : SourceValue F}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         i + refs.length < 8589934592 →
         RCLimRep t bAddr lim h x_rc →
         RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs x_refs →
         RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h idxs x_consts →
         ObsFn Obs.W "KernelClaim::walk_refs_transitive"
           [x_rc, x_refs, x_consts, .field (i : F)] h r h' calls →
         Heap.Extends h h' ∧
         ∃ recs : List (TopRec calls bAddr t lim),
           (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
             RefAllowedIn calls t bAddr lim refs[j] ∧
             ((NotBlockIn calls refs[j] ∧ refs[j] ∈ recs.map (·.addr)) ∨
               CoveredAt t lim refs[j])) ∧
           (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
             OpOrderedAt t lim refs[j] ∨ CoveredAt t lim refs[j]) ∧
           TopRecsClosed recs ∧
           TopRecsOrdered recs ∧
           (∀ r ∈ recs, r.depth ≤ calls.length)) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    refine ⟨?_, ?_⟩
    · intro x_rc x_addr r addr h h' calls hfuel hrc ha ev
      obtain ⟨m2, cs12, x_info, w39, x_refs, w40, w41, v539, m540, cs542, v548, m549, cs559, v_quot,
        m_quot, cs_quot, cs589, v594, m611, cs619, ev14, sg547, ev561, ev_quot, ev621, ev591, hc636⟩ :=
        Obs.«KernelClaim::run_check_transitive».obs ev
      obtain ⟨ext1, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        load_verified_constant_de ha ev14
      have hseg : Heap.Extends m2 m540 ∧
          ((∃ ms, c.info = .muts ms ∧
              ∀ (k : Nat), k < ms.size → MemberCheckedLimAt calls bAddr t addr ms k lim) ∨
            CheckedLimAt calls bAddr t addr lim) ∧
          ∃ recs_blk : List (TopRec calls bAddr t lim),
            TopRecsClosed recs_blk ∧
            TopRecsOrdered recs_blk ∧
            (∀ r ∈ recs_blk, r.depth < calls.length) ∧
            (IsProjRec c → Ix.Cert.ownerOf addr c ∈ recs_blk.map (·.addr)) := by
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
            obtain ⟨mv, hmv_eq, hms_rep⟩ := hinfo
            injection hmv_eq with _ _ hargs_m
            simp only [List.cons.injEq, and_true] at hargs_m
            rw [← hargs_m] at hms_rep
            obtain ⟨ext_muts, hchk_muts⟩ :=
              check_muts_all_lim_spec (hrc.mono ext1) (S0.addr_mono ext1 ha)
                (membersRep_of_repMutConstList_ord hms_rep) ev93
            have hsub_m : ∀ cl ∈ cs91, cl ∈ calls := fun cl hcl => by
              rw [hc636, hc133]; simp [hcl]
            have hnp : ¬ IsProjRec c := by simp [IsProjRec, hc_i]
            exact ⟨ext_muts,
              .inl ⟨ms, rfl, fun k hk => (hchk_muts k hk).mono hsub_m⟩,
              [], by simp [TopRecsClosed], topRecsOrdered_nil, by simp, fun hp => absurd hp hnp⟩
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
            obtain ⟨ext_rc, hchk⟩ :=
              run_check_lim_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev186
            have hlt_calls : cs206.length < calls.length := by
              rw [hc636, hc225]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs206.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hord_b, hdep_b⟩ :=
              (ih cs206.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev208
            have hsub_b : ∀ cl ∈ cs206, cl ∈ calls := fun cl hcl => by
              rw [hc636, hc225]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (hchk.mono (fun cl hcl => by rw [hc636, hc225]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b, hord_b.mono hsub_b,
              topRec_mono_depth_lt_ord hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
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
            obtain ⟨ext_rc, hchk⟩ :=
              run_check_lim_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev279
            have hlt_calls : cs299.length < calls.length := by
              rw [hc636, hc318]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs299.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hord_b, hdep_b⟩ :=
              (ih cs299.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev301
            have hsub_b : ∀ cl ∈ cs299, cl ∈ calls := fun cl hcl => by
              rw [hc636, hc318]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (hchk.mono (fun cl hcl => by rw [hc636, hc318]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b, hord_b.mono hsub_b,
              topRec_mono_depth_lt_ord hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
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
            obtain ⟨ext_rc, hchk⟩ :=
              run_check_lim_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev378
            have hlt_calls : cs398.length < calls.length := by
              rw [hc636, hc417]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs398.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hord_b, hdep_b⟩ :=
              (ih cs398.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev400
            have hsub_b : ∀ cl ∈ cs398, cl ∈ calls := fun cl hcl => by
              rw [hc636, hc417]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (hchk.mono (fun cl hcl => by rw [hc636, hc417]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b, hord_b.mono hsub_b,
              topRec_mono_depth_lt_ord hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
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
            obtain ⟨ext_rc, hchk⟩ :=
              run_check_lim_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev471
            have hlt_calls : cs491.length < calls.length := by
              rw [hc636, hc510]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs491.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            obtain ⟨ext_blk, recs_b, hmem_b, hcl_b, hord_b, hdep_b⟩ :=
              (ih cs491.length hlt_sub).1 (Nat.le_refl _)
                (hrc.mono (ext1.trans ext_rc)) (S0.addr_mono ext_rc hblk_addr) ev493
            have hsub_b : ∀ cl ∈ cs491, cl ∈ calls := fun cl hcl => by
              rw [hc636, hc510]; simp [hcl]
            refine ⟨ext_rc.trans ext_blk,
              .inr (hchk.mono (fun cl hcl => by rw [hc636, hc510]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b, hord_b.mono hsub_b,
              topRec_mono_depth_lt_ord hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · obtain ⟨ext_rc, hchk⟩ :=
            run_check_lim_spec (hrc.mono ext1) (S0.addr_mono ext1 ha) ev521
          have hnp : ¬ IsProjRec c := by
            intro hp
            rcases hp with ⟨p, hc_i⟩ | ⟨p, hc_i⟩ | ⟨p, hc_i⟩ | ⟨p, hc_i⟩ <;>
              rw [hc_i] at hinfo
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne227 [_] rfl)
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne320 [_] rfl)
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne419 [_] rfl)
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne512 [_] rfl)
          exact ⟨ext_rc,
            .inr (hchk.mono (fun cl hcl => by rw [hc636, hc538]; simp [hcl])),
            [], by simp [TopRecsClosed], topRecsOrdered_nil, by simp, fun hp => absurd hp hnp⟩
      obtain ⟨ext_seg, hchk_self, recs_blk, hcl_blk, hord_blk, hdep_blk, hown_blk⟩ := hseg
      have ext_guard : Heap.Extends m540 m_quot := ev561.heap_extends.trans ev_quot.heap_extends
      obtain ⟨ext_idx, hidxs⟩ := const_idxs_of_spec (hrep.mono (ext_seg.trans ext_guard)) ev621
      have hrefs_rep :
          RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem m611 c.refs.toList x_refs := by
        obtain ⟨_, _, refsPtr, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.2.2.1] at hr_list
        exact repList_heapMono₂ _ repAddrElem_heapMono₂ (ext_seg.trans (ext_guard.trans ext_idx)) hr_list
      have hlt_r_calls : cs589.length < calls.length := by
        rw [hc636]
        simp only [List.length_cons, List.length_append]
        omega
      have hlt_walk : cs589.length < fuel := Nat.lt_of_lt_of_le hlt_r_calls hfuel
      have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
        rw [Nat.zero_add, Array.length_toList]
        exact refs_size_lt_bound_ord hsz hdeExact
      obtain ⟨ext_walk, recs_r, hmem_r, hordj_r, hcl_r, hord_r, hdep_r⟩ :=
        (ih cs589.length hlt_walk).2 (i := 0) (Nat.le_refl _) hrefs_bound
          (hrc.mono (ext1.trans (ext_seg.trans (ext_guard.trans ext_idx)))) hrefs_rep hidxs ev591
      have hsub_r : ∀ cl ∈ cs589, cl ∈ calls := fun cl hcl => by
        rw [hc636]; simp [hcl]
      have hdep_r_lt : ∀ r ∈ recs_r.map (TopRec.mono hsub_r), r.depth < calls.length :=
        topRec_mono_depth_lt_ord hsub_r hdep_r hlt_r_calls
      let r₀ : TopRec calls bAddr t lim := {
        addr := addr
        rawBytes := rawBytes
        c := c
        depth := calls.length
        hsz := hsz
        hhashed := hashed_mono (fun cl hcl => by rw [hc636]; simp [hcl]) hh_load
        hblake := hblk
        hde := hde
        hdeExact := hdeExact
        hchecked := hchk_self
        hguard := ⟨m540, m549, x_rc, x_addr,
          .construct "Ixon::Constant" "Mk" [x_info, w39, x_refs, w40, w41], v548, cs559,
          hrc.mono (ext1.trans ext_seg), S0.addr_mono (ext1.trans ext_seg) ha,
          hrep.mono ext_seg, ev561, fun cl hcl => by rw [hc636]; simp [hcl]⟩
        hquot := ⟨m549, m_quot, x_rc, x_addr,
          .construct "Ixon::Constant" "Mk" [x_info, w39, x_refs, w40, w41], v_quot, cs_quot,
          hrc.mono (ext1.trans (ext_seg.trans ev561.heap_extends)),
          S0.addr_mono (ext1.trans (ext_seg.trans ev561.heap_extends)) ha,
          hrep.mono (ext_seg.trans ev561.heap_extends), ev_quot,
          fun cl hcl => by rw [hc636]; simp [hcl]⟩
      }
      let recs_tail := recs_blk ++ recs_r.map (TopRec.mono hsub_r)
      refine ⟨ext1.trans (ext_seg.trans (ext_guard.trans (ext_idx.trans ext_walk))),
        r₀ :: recs_tail, List.mem_cons_self,
        topRecsClosed_cons_ord (hcl_blk.append (hcl_r.mono hsub_r)) ?_ ?_, ?_, ?_⟩
      · intro hp
        obtain ⟨r', hr', ha'⟩ := List.mem_map.mp (hown_blk hp)
        exact ⟨r', List.mem_cons_of_mem _ (List.mem_append_left _ hr'), ha', hdep_blk r' hr'⟩
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
        rcases hrest with ⟨hnb, hm⟩ | hcov
        · have hm' : b ∈ (recs_r.map (TopRec.mono hsub_r)).map (·.addr) := by
            rwa [map_addr_topRec_mono]
          obtain ⟨r', hr', ha'⟩ := List.mem_map.mp hm'
          exact .inl ⟨hnb.mono hsub_r, r',
            List.mem_cons_of_mem _ (List.mem_append_right _ hr'), ha', hdep_r_lt r' hr'⟩
        · exact .inr hcov
      · intro r hr i hi b hb
        rcases List.mem_cons.mp hr with rfl | hr_tl
        · have hj_lt : i < c.refs.toList.length := by
            rw [Array.length_toList]
            exact (Array.getElem?_eq_some_iff.mp hb).1
          have hget : c.refs.toList[i] = b := by
            obtain ⟨_, heq_b⟩ := Array.getElem?_eq_some_iff.mp hb
            simpa using heq_b
          have ho := hordj_r i hj_lt (by simpa using hi)
          rw [hget] at ho
          exact ho
        · exact (hord_blk.append (hord_r.mono hsub_r)) r hr_tl i hi b hb
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr_tl
        · exact Nat.le_refl _
        · rcases List.mem_append.mp hr_tl with hr_blk | hr_r
          · exact Nat.le_of_lt (hdep_blk r hr_blk)
          · exact Nat.le_of_lt (hdep_r_lt r hr_r)
    · intro i refs idxs x_rc x_refs x_consts r h h' calls hfuel hbound hrc hrefs hidxs ev
      match Obs.«KernelClaim::walk_refs_transitive».obs ev with
      | .Nil (ld12 := ld12) (he23 := he23) .. =>
        obtain rfl := Lib.rep_nil_of_load hrefs ld12
        subst he23
        exact ⟨Heap.Extends.refl _, [], fun _ hj => absurd hj (Nat.not_lt_zero _),
          fun _ hj => absurd hj (Nat.not_lt_zero _), by simp [TopRecsClosed], topRecsOrdered_nil,
          by simp⟩
      | .Cons (x_a := x_a) (x_rest := x_rest) (m227 := m227) (cs229 := cs229) (cs238 := cs238)
          (ld12 := ld12) (sg234 := sg234) (op279 := op279) (ev240 := ev240) (hc281 := hc281) .. =>
        obtain ⟨a, rest, rfl, ha_head, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
        have hi_lt56 : i < 72057594037927936 := by simp at hbound; omega
        have hseg : Heap.Extends h m227 ∧
            ∃ recs₁ : List (TopRec calls bAddr t lim),
              (i ∈ idxs → RefAllowedIn calls t bAddr lim a ∧
                ((NotBlockIn calls a ∧ a ∈ recs₁.map (·.addr)) ∨ CoveredAt t lim a)) ∧
              (i ∈ idxs → OpOrderedAt t lim a ∨ CoveredAt t lim a) ∧
              TopRecsClosed recs₁ ∧
              TopRecsOrdered recs₁ ∧
              (∀ r ∈ recs₁, r.depth ≤ calls.length) := by
          match sg234 with
          | .n1_n0 (cs88 := cs88) (cs153 := cs153) (cs167 := cs167) (v170 := v170)
              (ev56 := ev56) (ev90 := ev90) (ev121 := ev121) (ev155 := ev155) (ev183 := ev183)
              (ev169 := ev169) (hc207 := hc207) .. =>
            obtain ⟨rfl, -⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            have ext_ra := ev90.heap_extends
            have ext_cov := ev121.heap_extends
            obtain ⟨ext_nb, hnb⟩ :=
              assert_not_block_ref_notBlock (S0.addr_mono (ext_ra.trans ext_cov) ha_head) ev155
            have ext_pre := ext_ra.trans (ext_cov.trans ext_nb)
            obtain ⟨ext_wc, hwc⟩ :=
              walk_ctx_lim_spec (hrc.mono ext_pre) (S0.addr_mono ext_pre ha_head) ev183
            have hordA := walk_ctx_ordered (hrc.mono ext_pre) (S0.addr_mono ext_pre ha_head) ev183
            have hsub_ra : ∀ cl ∈ cs88, cl ∈ calls := fun cl hcl => by
              rw [hc281, hc207]; simp [hcl]
            have hsub_nb : ∀ cl ∈ cs153, cl ∈ calls := fun cl hcl => by
              rw [hc281, hc207]; simp [hcl]
            have hal : RefAllowedIn calls t bAddr lim a :=
              ⟨_, _, _, _, _, _, hrc, ha_head, ev90, hsub_ra⟩
            rcases hwc with rfl | ⟨hcov, -⟩
            · have hlt_calls : cs167.length < calls.length := by
                rw [hc281, hc207]
                simp only [List.length_cons, List.length_append]
                omega
              have hlt_sub : cs167.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
              have ext_pre' := ext_pre.trans ext_wc
              obtain ⟨ext_sub, recs_s, hmem_s, hcl_s, hord_s, hdep_s⟩ :=
                (ih cs167.length hlt_sub).1 (Nat.le_refl _) (hrc.mono ext_pre')
                  (S0.addr_mono ext_pre' ha_head) ev169
              have hsub_s : ∀ cl ∈ cs167, cl ∈ calls := fun cl hcl => by
                rw [hc281, hc207]; simp [hcl]
              refine ⟨ext_pre'.trans ext_sub, recs_s.map (TopRec.mono hsub_s), ?_,
                fun _ => .inl hordA, hcl_s.mono hsub_s, hord_s.mono hsub_s,
                topRec_mono_depth_le_ord hsub_s hdep_s (Nat.le_of_lt hlt_calls)⟩
              intro _
              refine ⟨hal, .inl ⟨hnb.mono hsub_nb, ?_⟩⟩
              rw [map_addr_topRec_mono]
              exact hmem_s
            · exact ⟨ext_pre.trans (ext_wc.trans ev169.heap_extends), [],
                fun _ => ⟨hal, .inr hcov⟩, fun _ => .inr hcov, by simp [TopRecsClosed],
                topRecsOrdered_nil, by simp⟩
          | .n1_other (cs88 := cs88) (ev56 := ev56) (ev90 := ev90) (ev121 := ev121)
              (hne208 := hne208) (he215 := he215) (hc216 := hc216) .. =>
            obtain ⟨rfl, -⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            have ext_ra := ev90.heap_extends
            have ext_cov := ev121.heap_extends
            obtain ⟨-, hv⟩ :=
              walk_covered_lim_spec (hrc.mono ext_ra) (S0.addr_mono ext_ra ha_head) ev121
            rcases hv with hv0 | hcov
            · exact absurd hv0 hne208
            · have hsub_ra : ∀ cl ∈ cs88, cl ∈ calls := fun cl hcl => by
                rw [hc281, hc216]; simp [hcl]
              have hal : RefAllowedIn calls t bAddr lim a :=
                ⟨_, _, _, _, _, _, hrc, ha_head, ev90, hsub_ra⟩
              refine ⟨by rw [he215]; exact ext_ra.trans ext_cov, [], fun _ => ⟨hal, .inr hcov⟩,
                fun _ => .inr hcov, by simp [TopRecsClosed], topRecsOrdered_nil, by simp⟩
          | .other (ev56 := ev56) (hne217 := hne217) (he224 := he224) .. =>
            obtain ⟨rfl, hiff⟩ := g_list_has_spec idxs hi_lt56 hidxs ev56
            refine ⟨by subst he224; exact Heap.Extends.refl _, [],
              fun hi_in => absurd (hiff.mpr hi_in) hne217,
              fun hi_in => absurd (hiff.mpr hi_in) hne217, by simp [TopRecsClosed], topRecsOrdered_nil,
              by simp⟩
        obtain ⟨ext1, recs₁, hmem₁, hordj₁, hcl₁, hord₁, hdep₁⟩ := hseg
        simp only [evalBinOp, Except.ok.injEq] at op279
        subst op279
        have hv_inc : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
        rw [hv_inc] at ev240
        have hlt_tail_calls : cs238.length < calls.length := by
          rw [hc281]
          simp only [List.length_cons, List.length_append]
          omega
        have hlt_tail : cs238.length < fuel := Nat.lt_of_lt_of_le hlt_tail_calls hfuel
        have hbound_tail : (i + 1) + rest.length < 8589934592 := by
          simp at hbound; omega
        obtain ⟨ext2, recs₂_raw, hmem₂, hordj₂, hcl₂, hord₂, hdep₂⟩ :=
          (ih cs238.length hlt_tail).2 (i := i + 1) (Nat.le_refl _) hbound_tail
            (hrc.mono ext1)
            (repList_heapMono₂ _ repAddrElem_heapMono₂ ext1 hrest_rep)
            (repList_heapMono₂ _ repBoundedIdx_heapMono₂ ext1 hidxs)
            ev240
        have hsub₂ : ∀ cl ∈ cs238, cl ∈ calls := fun cl hcl => by
          rw [hc281]; simp [hcl]
        refine ⟨ext1.trans ext2, recs₁ ++ recs₂_raw.map (TopRec.mono hsub₂), ?_,
          ?_, hcl₁.append (hcl₂.mono hsub₂), hord₁.append (hord₂.mono hsub₂), ?_⟩
        · intro j hj hij
          cases j with
          | zero =>
            simp only [Nat.add_zero] at hij
            obtain ⟨hal, hrest⟩ := hmem₁ hij
            refine ⟨hal, ?_⟩
            rcases hrest with ⟨hnb, hm⟩ | hcov
            · refine .inl ⟨hnb, ?_⟩
              rw [List.map_append]
              exact List.mem_append_left _ hm
            · exact .inr hcov
          | succ j' =>
            have hj' : j' < rest.length := by simp at hj; omega
            have hij' : (i + 1) + j' ∈ idxs := by
              have heq_idx : (i + 1) + j' = i + (j' + 1) := by omega
              rwa [heq_idx]
            obtain ⟨hal, hrest⟩ := hmem₂ j' hj' hij'
            refine ⟨hal.mono hsub₂, ?_⟩
            rcases hrest with ⟨hnb, hm⟩ | hcov
            · refine .inl ⟨hnb.mono hsub₂, ?_⟩
              rw [List.map_append, map_addr_topRec_mono]
              exact List.mem_append_right _ hm
            · exact .inr hcov
        · intro j hj hij
          cases j with
          | zero =>
            simp only [Nat.add_zero] at hij
            exact hordj₁ hij
          | succ j' =>
            have hj' : j' < rest.length := by simp at hj; omega
            have hij' : (i + 1) + j' ∈ idxs := by
              have heq_idx : (i + 1) + j' = i + (j' + 1) := by omega
              rwa [heq_idx]
            exact hordj₂ j' hj' hij'
        · intro r hr
          rcases List.mem_append.mp hr with hr1 | hr2
          · exact hdep₁ r hr1
          · exact topRec_mono_depth_le_ord hsub₂ hdep₂ (Nat.le_of_lt hlt_tail_calls) r hr2

/-- **`KernelClaim::run_check_transitive(rc, a)` under a context at the limit `lim`, ordered**:
`run_check_transitive_lim_spec` with every used reference of a walked record ordered or covered
(`TopRecsOrdered`). -/
theorem run_check_transitive_lim_ordered {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ha : S0.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::run_check_transitive" [x_rc, x_addr] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ recs : List (TopRec calls bAddr t lim),
      addr ∈ recs.map (·.addr) ∧ TopRecsClosed recs ∧ TopRecsOrdered recs ∧
        (∀ r ∈ recs, r.depth ≤ calls.length) :=
  (run_check_transitive_lim_ordered_aux calls.length).1 (Nat.le_refl _) hrc ha ev

/-- **`KernelClaim::walk_refs_transitive(rc, refs, consts, i)` under a context at the limit
`lim`, ordered**: `walk_refs_transitive_lim_spec` with each reference at a position in `consts`
ordered or covered, and the walked records ordered. -/
theorem walk_refs_transitive_lim_ordered {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
    {x_rc x_refs x_consts r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbound : i + refs.length < 8589934592)
    (hrc : RCLimRep t bAddr lim h x_rc)
    (hrefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs x_refs)
    (hidxs : RepList Obs.Names.«Lists::Node<Field>» RepBoundedIdx h idxs x_consts)
    (ev : ObsFn Obs.W "KernelClaim::walk_refs_transitive"
      [x_rc, x_refs, x_consts, .field (i : F)] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ recs : List (TopRec calls bAddr t lim),
      (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
        RefAllowedIn calls t bAddr lim refs[j] ∧
        ((NotBlockIn calls refs[j] ∧ refs[j] ∈ recs.map (·.addr)) ∨
          CoveredAt t lim refs[j])) ∧
      (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
        OpOrderedAt t lim refs[j] ∨ CoveredAt t lim refs[j]) ∧
      TopRecsClosed recs ∧ TopRecsOrdered recs ∧
      (∀ r ∈ recs, r.depth ≤ calls.length) :=
  (run_check_transitive_lim_ordered_aux calls.length).2 (Nat.le_refl _) hbound hrc hrefs hidxs ev

end IxVM.Refinement.Claim
