import IxVMRefinement.Claim.TopSeed

/-! # The claim walk at a role-context limit: `walk_leaves_owned`

A `checkEnv` typing claim walks its owned leaves with `KernelClaim::walk_leaves_owned(rc,
leaves)`: for each leaf it calls `IxVMCompat::check_owned(binding, validator, a)` with the
context's binding and validator, which reloads the context (`role_ctx_for_validator`), refuses a
leaf that is not claimable (`assert_claimable`) and walks the leaf with `env_walk_all`.
`env_walk_all` checks the record at the address (every member of a block record), walks a
projection's block by `check_owned`, and walks the record's used references
(`env_walk_refs_all`). For a used reference `x` that walk asks `assert_ref_allowed(rc, x)`, skips
`x` when `walk_covered(rc, x)` is nonzero, and otherwise refuses a block record at `x`
(`assert_not_block_ref`) and walks `x` by `check_owned` when `walk_ctx(rc, x)` has the context's
limit, by `run_check_transitive` under a validation context of its own otherwise.

At a top-level limit (`some 77`, validator `3`; `none`, validator `4`) the reloaded context is at
the walk's own limit. For a run at an admitted binding this module proves, unless the run hashed
a collision with `extra`:

* `check_owned_lim_spec`: the leaf is claimable (`ClaimableSeed`) and is a record of a closed
  list of records walked at the limit (`TopRec`, `TopRecsClosed`);
* `env_walk_all_lim_spec`, `env_walk_refs_all_lim_spec`: each used reference was asked about
  (`RefAllowedIn`) and is a walked record that is no block record (`NotBlockIn`), or is covered
  at the limit (`CoveredAt`);
* `walk_leaves_owned_lim_spec`: every leaf is claimable and walked. -/

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

/-! ## Helpers -/

private theorem addrVal_of_load_env {h : Heap F} {p v : SourceValue F} {a : _root_.Address}
    (ha : BaseSeams.addr h p a) (hl : loadValue h p = .ok v) :
    ∃ d : Bytes.Address, v = Ingress.digestV d ∧ ixAddr d = a := by
  obtain ⟨d, hd, hix⟩ := ha
  exact ⟨d, Ingress.load_repAddressRef hd hl, hix⟩

private theorem addr_of_snoc_env {h : Heap F} {d : Bytes.Address} {a : _root_.Address}
    (hix : ixAddr d = a) :
    BaseSeams.addr (h ++ [Ingress.digestV d]) (.ptr (Ingress.digestV d).type h.length) a :=
  ⟨d, repAddressRef_of_load_digestV (Ingress.loadValue_snoc h (Ingress.digestV d)), hix⟩

private theorem mutShape_of_repMutConst_env {h : Heap F} {m : Ixon.MutConst}
    {v : SourceValue F} (hr : RepMutConst h m v) : Specs.Callees.MutShape h m v := by
  cases m with
  | defn d => obtain ⟨dv, hv, _⟩ := hr; exact ⟨dv, hv⟩
  | indc i => obtain ⟨iv, hv, _⟩ := hr; exact ⟨iv, hv⟩
  | recr r => obtain ⟨rv, hv, _⟩ := hr; exact ⟨rv, hv⟩

private theorem membersRep_of_repMutConstList_env {h : Heap F}
    {xs : List Ixon.MutConst} {p : SourceValue F}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» RepMutConst h xs p) :
    Specs.Callees.MembersRep h xs p := by
  induction hrep with
  | nil cell => exact .nil cell
  | cons cell rh _ ih => exact .cons cell (mutShape_of_repMutConst_env rh) ih

private theorem refs_size_lt_bound_env {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private theorem topRec_mono_depth_lt_env {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {n : Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (TopRec cs₁ bAddr t lim)}
    (hdep : ∀ r ∈ recs, r.depth ≤ cs₁.length) (hlt : cs₁.length < n) :
    ∀ r ∈ recs.map (TopRec.mono hsub), r.depth < n := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  have hd := hdep r₀ hr₀
  simp only [TopRec.mono]
  omega

private theorem topRec_mono_depth_le_env {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
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
private theorem topRecsClosed_cons_env {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {r₀ : TopRec calls bAddr t lim} {rest : List (TopRec calls bAddr t lim)}
    (hrest : TopRecsClosed rest)
    (hown : IsProjRec r₀.c →
      ∃ r' ∈ r₀ :: rest, r'.addr = Ix.Cert.ownerOf r₀.addr r₀.c ∧ r'.depth < r₀.depth)
    (hrefs : ∀ i ∈ BaseSeams.usedRefIdxs r₀.c, ∀ x, r₀.c.refs[i]? = some x →
      RefAllowedIn calls t bAddr lim x ∧
      ((NotBlockIn calls x ∧ ∃ r' ∈ r₀ :: rest, r'.addr = x ∧ r'.depth < r₀.depth) ∨
        CoveredAt t lim x)) :
    TopRecsClosed (r₀ :: rest) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hmem
  · exact ⟨hown, hrefs⟩
  · exact TopRecsClosed.sub (ys := r₀ :: rest) (fun y hy => List.mem_cons_of_mem _ hy) hrest r hmem

/-- **`KernelClaim::assert_not_block_ref(a)`**: the record at `a` is loaded and is no block
record. -/
private theorem assert_not_block_ref_env {a : _root_.Address} {x_a r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ha : BaseSeams.addr h x_a a)
    (ev : ObsFn Obs.W "KernelClaim::assert_not_block_ref" [x_a] h r h' calls) :
    Heap.Extends h h' ∧ NotBlockIn calls a := by
  have ext := ev.heap_extends
  match Obs.«KernelClaim::assert_not_block_ref».obs ev with
  | .Muts (heq115 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
  | .other (ev14 := ev14) (hne121 := hne) (hc129 := hc) .. =>
    obtain ⟨-, rawBytes, c, -, hh, hb, hde, -, hrep, -⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, -⟩ := hrep
    injection hv_c with _ _ hargs_c
    simp only [List.cons.injEq] at hargs_c
    rw [← hargs_c.1] at hinfo
    refine ⟨ext, rawBytes, c, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh, hb, hde,
      fun ms hms => ?_⟩
    rw [hms] at hinfo
    obtain ⟨_, hv', _⟩ := hinfo
    exact absurd hv' (hne [_] rfl)

/-- **The context `check_owned` reloads is at the walk's limit**: the validator of a context at a
top-level limit (`role_ctx_validator_lim_spec`) selects that limit again
(`role_ctx_for_validator_lim_spec`). -/
private theorem rcLim_of_validator {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none) {x_v rc : SourceValue F} {h : Heap F}
    (hv : ((∃ n, lim = some n) ∧ x_v = .field 3) ∨ (lim = none ∧ x_v = .field 4))
    (hrc : (x_v = .field 3 ∧ RCLimRep t bAddr (some 77) h rc) ∨
      (x_v = .field 4 ∧ RCLimRep t bAddr none h rc)) :
    RCLimRep t bAddr lim h rc := by
  rcases hv with ⟨⟨n, rfl⟩, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hlim with hl | hl
    · cases hl
      rcases hrc with ⟨-, hr⟩ | ⟨h34, -⟩
      · exact hr
      · exact absurd (Value.field.inj h34) (by decide)
    · cases hl
  · rcases hrc with ⟨h43, -⟩ | ⟨-, hr⟩
    · exact absurd (Value.field.inj h43) (by decide)
    · exact hr

/-! ## `check_owned`, `env_walk_all` and `env_walk_refs_all` at a top-level limit -/

private theorem env_walk_lim_fuel_aux {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none) :
    ∀ (fuel : Nat),
      (∀ {d_b d_a : Bytes.Address} {x_v r : SourceValue F} {addr : _root_.Address}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         ixAddr d_b = b.address →
         ixAddr d_a = addr →
         (((∃ n, lim = some n) ∧ x_v = .field 3) ∨ (lim = none ∧ x_v = .field 4)) →
         ObsFn Obs.W "IxVMCompat::check_owned"
           [Ingress.digestV d_b, x_v, Ingress.digestV d_a] h r h' calls →
         V.HashedCollision extra calls ∨
         (Heap.Extends h h' ∧
          ClaimableSeed calls t addr ∧
          ∃ recs : List (TopRec calls b.address t lim),
            addr ∈ recs.map (·.addr) ∧
            TopRecsClosed recs ∧
            (∀ r ∈ recs, r.depth ≤ calls.length))) ∧
      (∀ {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         RCLimRep t b.address lim h x_rc →
         BaseSeams.addr h x_addr addr →
         ObsFn Obs.W "KernelClaim::env_walk_all" [x_rc, x_addr] h r h' calls →
         V.HashedCollision extra calls ∨
         (Heap.Extends h h' ∧
          ∃ recs : List (TopRec calls b.address t lim),
            addr ∈ recs.map (·.addr) ∧
            TopRecsClosed recs ∧
            (∀ r ∈ recs, r.depth ≤ calls.length))) ∧
      (∀ {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
         {x_rc x_refs x_consts r : SourceValue F}
         {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel →
         i + refs.length < 8589934592 →
         RCLimRep t b.address lim h x_rc →
         RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs x_refs →
         RepSortedIdxFrom h idxs i x_consts →
         ObsFn Obs.W "KernelClaim::env_walk_refs_all"
           [x_rc, x_refs, x_consts, .field (i : F)] h r h' calls →
         V.HashedCollision extra calls ∨
         (Heap.Extends h h' ∧
          ∃ recs : List (TopRec calls b.address t lim),
            (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
              RefAllowedIn calls t b.address lim refs[j] ∧
              ((NotBlockIn calls refs[j] ∧ refs[j] ∈ recs.map (·.addr)) ∨
                CoveredAt t lim refs[j])) ∧
            TopRecsClosed recs ∧
            (∀ r ∈ recs, r.depth ≤ calls.length))) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    -- `check_owned`
    · intro d_b d_a x_v r addr h h' calls hfuel hix_b hix_a hv ev
      obtain ⟨v1, m2, cs12, m18, v35, m36, cs46, m59, cs72, m85,
        rfl, ev14, rfl, ev48, rfl, ev74, hc95⟩ := Obs.«IxVMCompat::check_owned».obs ev
      have ext_s1 := Heap.Extends.snoc h (Ingress.digestV d_b)
      rcases role_ctx_for_validator_lim_spec (V := V) hadm hb_extra (addr_of_snoc_env hix_b)
          ev14 with
        hcoll | ⟨ext_rc, hrc_v⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc95]; simp [hcl]) hcoll)
      have hrc := rcLim_of_validator hlim hv hrc_v
      have ext_s2 := Heap.Extends.snoc m2 (Ingress.digestV d_a)
      obtain ⟨ext_ac, hseed⟩ :=
        assert_claimable_lim_spec (hrc.mono ext_s2) (addr_of_snoc_env hix_a) ev48
      have ext_s3 := Heap.Extends.snoc m36 (Ingress.digestV d_a)
      have hlt_ewa_calls : cs72.length < calls.length := by
        rw [hc95]
        simp only [List.length_cons, List.length_append]
        omega
      have hlt_ewa : cs72.length < fuel := Nat.lt_of_lt_of_le hlt_ewa_calls hfuel
      rcases (ih cs72.length hlt_ewa).2.1 (Nat.le_refl _)
          (hrc.mono (ext_s2.trans (ext_ac.trans ext_s3))) (addr_of_snoc_env hix_a) ev74 with
        hcoll | ⟨ext_ewa, recs, hmem, hcl, hdep⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc95]; simp [hcl]) hcoll)
      have hsub_ac : ∀ cl ∈ cs46, cl ∈ calls := fun cl hcl => by rw [hc95]; simp [hcl]
      have hsub_ewa : ∀ cl ∈ cs72, cl ∈ calls := fun cl hcl => by rw [hc95]; simp [hcl]
      refine .inr ⟨ext_s1.trans (ext_rc.trans (ext_s2.trans (ext_ac.trans
          (ext_s3.trans ext_ewa)))),
        hseed.mono hsub_ac, recs.map (TopRec.mono hsub_ewa), ?_, hcl.mono hsub_ewa,
        topRec_mono_depth_le_env hsub_ewa hdep (Nat.le_of_lt hlt_ewa_calls)⟩
      rw [map_addr_topRec_mono]
      exact hmem
    -- `env_walk_all`
    · intro x_rc x_addr r addr h h' calls hfuel hrc ha ev
      obtain ⟨m2, cs12, x_info, w39, x_refs, w40, w41, v699, m700, cs702, v708, m709, cs719, v_quot,
        m_quot, cs_quot, cs749, v754, m771, cs779, ev14, sg707, ev721, ev_quot, ev781, ev751, hc796⟩ :=
        Obs.«KernelClaim::env_walk_all».obs ev
      obtain ⟨ext1, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        load_verified_constant_de ha ev14
      have hseg : V.HashedCollision extra calls ∨
          (Heap.Extends m2 m700 ∧
           ((∃ ms, c.info = .muts ms ∧
               ∀ (k : Nat), k < ms.size → MemberCheckedLimAt calls b.address t addr ms k lim) ∨
             CheckedLimAt calls b.address t addr lim) ∧
           ∃ recs_blk : List (TopRec calls b.address t lim),
             TopRecsClosed recs_blk ∧
             (∀ r ∈ recs_blk, r.depth < calls.length) ∧
             (IsProjRec c → Ix.Cert.ownerOf addr c ∈ recs_blk.map (·.addr))) := by
        obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.1] at hinfo
        match sg707 with
        | .Muts (cs91 := cs91) (hv81 := hv81) (ev93 := ev93) (hc133 := hc133) .. =>
          rw [hv81] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case muts ms =>
            obtain ⟨mv, hmv_eq, hms_rep⟩ := hinfo
            injection hmv_eq with _ _ hargs_m
            simp only [List.cons.injEq, and_true] at hargs_m
            rw [← hargs_m] at hms_rep
            obtain ⟨ext_muts, hchk_muts⟩ :=
              check_muts_all_lim_spec (hrc.mono ext1) (BaseSeams.addr_mono ext1 ha)
                (membersRep_of_repMutConstList_env hms_rep) ev93
            have hsub_m : ∀ cl ∈ cs91, cl ∈ calls := fun cl hcl => by
              rw [hc796, hc133]; simp [hcl]
            have hnp : ¬ IsProjRec c := by simp [IsProjRec, hc_i]
            exact .inr ⟨ext_muts,
              .inl ⟨ms, rfl, fun k hk => (hchk_muts k hk).mono hsub_m⟩,
              [], by simp [TopRecsClosed], by simp, fun hp => absurd hp hnp⟩
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        | .DPrj (x_block_addr := x_block_addr) (cs206 := cs206) (hv139 := hv139)
            (ev186 := ev186) (ev226 := ev226) (ld220 := ld220) (ev246 := ev246)
            (ld263 := ld263) (ev208 := ev208) (hc265 := hc265) .. =>
          rw [hv139] at hinfo
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
              run_check_lim_spec (hrc.mono ext1) (BaseSeams.addr_mono ext1 ha) ev186
            have hrc' := hrc.mono (ext1.trans ext_rc)
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_lim_spec hrc' ev226
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load_env hp_b ld220
            obtain ⟨rfl, hv⟩ := role_ctx_validator_lim_spec hrc' ev246
            obtain ⟨d_blk, rfl, hix_blk⟩ :=
              addrVal_of_load_env (BaseSeams.addr_mono ext_rc hblk_addr) ld263
            have hlt_calls : cs206.length < calls.length := by
              rw [hc796, hc265]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs206.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            rcases (ih cs206.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk hv ev208 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b, hdep_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc796, hc265]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs206, cl ∈ calls := fun cl hcl => by
              rw [hc796, hc265]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (hchk.mono (fun cl hcl => by rw [hc796, hc265]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b,
              topRec_mono_depth_lt_env hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        | .IPrj (x_block_addr := x_block_addr) (cs339 := cs339) (hv272 := hv272)
            (ev319 := ev319) (ev359 := ev359) (ld353 := ld353) (ev379 := ev379)
            (ld396 := ld396) (ev341 := ev341) (hc398 := hc398) .. =>
          rw [hv272] at hinfo
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
              run_check_lim_spec (hrc.mono ext1) (BaseSeams.addr_mono ext1 ha) ev319
            have hrc' := hrc.mono (ext1.trans ext_rc)
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_lim_spec hrc' ev359
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load_env hp_b ld353
            obtain ⟨rfl, hv⟩ := role_ctx_validator_lim_spec hrc' ev379
            obtain ⟨d_blk, rfl, hix_blk⟩ :=
              addrVal_of_load_env (BaseSeams.addr_mono ext_rc hblk_addr) ld396
            have hlt_calls : cs339.length < calls.length := by
              rw [hc796, hc398]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs339.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            rcases (ih cs339.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk hv ev341 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b, hdep_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc796, hc398]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs339, cl ∈ calls := fun cl hcl => by
              rw [hc796, hc398]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (hchk.mono (fun cl hcl => by rw [hc796, hc398]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b,
              topRec_mono_depth_lt_env hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        | .CPrj (x_block_addr := x_block_addr) (cs478 := cs478) (hv405 := hv405)
            (ev458 := ev458) (ev498 := ev498) (ld492 := ld492) (ev518 := ev518)
            (ld535 := ld535) (ev480 := ev480) (hc537 := hc537) .. =>
          rw [hv405] at hinfo
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
              run_check_lim_spec (hrc.mono ext1) (BaseSeams.addr_mono ext1 ha) ev458
            have hrc' := hrc.mono (ext1.trans ext_rc)
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_lim_spec hrc' ev498
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load_env hp_b ld492
            obtain ⟨rfl, hv⟩ := role_ctx_validator_lim_spec hrc' ev518
            obtain ⟨d_blk, rfl, hix_blk⟩ :=
              addrVal_of_load_env (BaseSeams.addr_mono ext_rc hblk_addr) ld535
            have hlt_calls : cs478.length < calls.length := by
              rw [hc796, hc537]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs478.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            rcases (ih cs478.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk hv ev480 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b, hdep_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc796, hc537]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs478, cl ∈ calls := fun cl hcl => by
              rw [hc796, hc537]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (hchk.mono (fun cl hcl => by rw [hc796, hc537]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b,
              topRec_mono_depth_lt_env hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        | .RPrj (x_block_addr := x_block_addr) (cs611 := cs611) (hv544 := hv544)
            (ev591 := ev591) (ev631 := ev631) (ld625 := ld625) (ev651 := ev651)
            (ld668 := ld668) (ev613 := ev613) (hc670 := hc670) .. =>
          rw [hv544] at hinfo
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
              run_check_lim_spec (hrc.mono ext1) (BaseSeams.addr_mono ext1 ha) ev591
            have hrc' := hrc.mono (ext1.trans ext_rc)
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_lim_spec hrc' ev631
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load_env hp_b ld625
            obtain ⟨rfl, hv⟩ := role_ctx_validator_lim_spec hrc' ev651
            obtain ⟨d_blk, rfl, hix_blk⟩ :=
              addrVal_of_load_env (BaseSeams.addr_mono ext_rc hblk_addr) ld668
            have hlt_calls : cs611.length < calls.length := by
              rw [hc796, hc670]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs611.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            rcases (ih cs611.length hlt_sub).1 (Nat.le_refl _) hix_b hix_blk hv ev613 with
              hcoll | ⟨ext_co, _, recs_b, hmem_b, hcl_b, hdep_b⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc796, hc670]; simp [hcl]) hcoll)
            have hsub_b : ∀ cl ∈ cs611, cl ∈ calls := fun cl hcl => by
              rw [hc796, hc670]; simp [hcl]
            refine .inr ⟨ext_rc.trans ext_co,
              .inr (hchk.mono (fun cl hcl => by rw [hc796, hc670]; simp [hcl])),
              recs_b.map (TopRec.mono hsub_b), hcl_b.mono hsub_b,
              topRec_mono_depth_lt_env hsub_b hdep_b hlt_calls, ?_⟩
            intro _
            rw [map_addr_topRec_mono]
            simpa [Ix.Cert.ownerOf, hc_i] using hmem_b
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        | .other (hne134 := hne134) (hne267 := hne267) (hne400 := hne400)
            (hne539 := hne539) (hne672 := hne672) (ev681 := ev681) (hc698 := hc698) .. =>
          obtain ⟨ext_rc, hchk⟩ :=
            run_check_lim_spec (hrc.mono ext1) (BaseSeams.addr_mono ext1 ha) ev681
          have hnp : ¬ IsProjRec c := by
            intro hp
            rcases hp with ⟨p, hc_i⟩ | ⟨p, hc_i⟩ | ⟨p, hc_i⟩ | ⟨p, hc_i⟩ <;>
              rw [hc_i] at hinfo
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne267 [_] rfl)
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne400 [_] rfl)
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne539 [_] rfl)
            · obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne672 [_] rfl)
          exact .inr ⟨ext_rc,
            .inr (hchk.mono (fun cl hcl => by rw [hc796, hc698]; simp [hcl])),
            [], by simp [TopRecsClosed], by simp, fun hp => absurd hp hnp⟩
      rcases hseg with hcoll | ⟨ext_seg, hchk_self, recs_blk, hcl_blk, hdep_blk, hown_blk⟩
      · exact .inl hcoll
      have ext_guard : Heap.Extends m700 m_quot := ev721.heap_extends.trans ev_quot.heap_extends
      obtain ⟨ext_idx, hidxs⟩ := const_idxs_of_spec (hrep.mono (ext_seg.trans ext_guard)) ev781
      have hrefs_rep :
          RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem m771 c.refs.toList x_refs := by
        obtain ⟨_, _, refsPtr, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.2.2.1] at hr_list
        exact repList_heapMono₂ _ repAddrElem_heapMono₂ (ext_seg.trans (ext_guard.trans ext_idx)) hr_list
      have hlt_r_calls : cs749.length < calls.length := by
        rw [hc796]
        simp only [List.length_cons, List.length_append]
        omega
      have hlt_walk : cs749.length < fuel := Nat.lt_of_lt_of_le hlt_r_calls hfuel
      have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
        rw [Nat.zero_add, Array.length_toList]
        exact refs_size_lt_bound_env hsz hdeExact
      rcases (ih cs749.length hlt_walk).2.2 (i := 0) (Nat.le_refl _) hrefs_bound
          (hrc.mono (ext1.trans (ext_seg.trans (ext_guard.trans ext_idx)))) hrefs_rep hidxs ev751 with
        hcoll | ⟨ext_walk, recs_r, hmem_r, hcl_r, hdep_r⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc796]; simp [hcl]) hcoll)
      have hsub_r : ∀ cl ∈ cs749, cl ∈ calls := fun cl hcl => by
        rw [hc796]; simp [hcl]
      have hdep_r_lt : ∀ r ∈ recs_r.map (TopRec.mono hsub_r), r.depth < calls.length :=
        topRec_mono_depth_lt_env hsub_r hdep_r hlt_r_calls
      let r₀ : TopRec calls b.address t lim := {
        addr := addr
        rawBytes := rawBytes
        c := c
        depth := calls.length
        hsz := hsz
        hhashed := hashed_mono (fun cl hcl => by rw [hc796]; simp [hcl]) hh_load
        hblake := hblk
        hde := hde
        hdeExact := hdeExact
        hchecked := hchk_self
        hguard := ⟨m700, m709, x_rc, x_addr,
          .construct "Ixon::Constant" "Mk" [x_info, w39, x_refs, w40, w41], v708, cs719,
          hrc.mono (ext1.trans ext_seg), BaseSeams.addr_mono (ext1.trans ext_seg) ha,
          hrep.mono ext_seg, ev721, fun cl hcl => by rw [hc796]; simp [hcl]⟩
        hquot := ⟨m709, m_quot, x_rc, x_addr,
          .construct "Ixon::Constant" "Mk" [x_info, w39, x_refs, w40, w41], v_quot, cs_quot,
          hrc.mono (ext1.trans (ext_seg.trans ev721.heap_extends)),
          BaseSeams.addr_mono (ext1.trans (ext_seg.trans ev721.heap_extends)) ha,
          hrep.mono (ext_seg.trans ev721.heap_extends), ev_quot,
          fun cl hcl => by rw [hc796]; simp [hcl]⟩
      }
      let recs_tail := recs_blk ++ recs_r.map (TopRec.mono hsub_r)
      refine .inr ⟨ext1.trans (ext_seg.trans (ext_guard.trans (ext_idx.trans ext_walk))),
        r₀ :: recs_tail, List.mem_cons_self,
        topRecsClosed_cons_env (hcl_blk.append (hcl_r.mono hsub_r)) ?_ ?_, ?_⟩
      · intro hp
        obtain ⟨r', hr', ha'⟩ := List.mem_map.mp (hown_blk hp)
        exact ⟨r', List.mem_cons_of_mem _ (List.mem_append_left _ hr'), ha', hdep_blk r' hr'⟩
      · intro j hj x hx
        have hj_lt : j < c.refs.toList.length := by
          rw [Array.length_toList]
          exact (Array.getElem?_eq_some_iff.mp hx).1
        have hget : c.refs.toList[j] = x := by
          obtain ⟨_, heq_x⟩ := Array.getElem?_eq_some_iff.mp hx
          simpa using heq_x
        obtain ⟨hal, hrest⟩ := hmem_r j hj_lt (by simpa using hj)
        rw [hget] at hal hrest
        refine ⟨hal.mono hsub_r, ?_⟩
        rcases hrest with ⟨hnb, hm⟩ | hcov
        · have hm' : x ∈ (recs_r.map (TopRec.mono hsub_r)).map (·.addr) := by
            rwa [map_addr_topRec_mono]
          obtain ⟨r', hr', ha'⟩ := List.mem_map.mp hm'
          exact .inl ⟨hnb.mono hsub_r, r',
            List.mem_cons_of_mem _ (List.mem_append_right _ hr'), ha', hdep_r_lt r' hr'⟩
        · exact .inr hcov
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr_tl
        · exact Nat.le_refl _
        · rcases List.mem_append.mp hr_tl with hr_blk | hr_r
          · exact Nat.le_of_lt (hdep_blk r hr_blk)
          · exact Nat.le_of_lt (hdep_r_lt r hr_r)
    -- `env_walk_refs_all`
    · intro i refs idxs x_rc x_refs x_consts r h h' calls hfuel hbound hrc hrefs hidxs ev
      match Obs.«KernelClaim::env_walk_refs_all».obs ev with
      | .Nil (ld12 := ld12) (he23 := he23) .. =>
        obtain rfl := Lib.rep_nil_of_load hrefs ld12
        subst he23
        exact .inr ⟨Heap.Extends.refl _, [], fun _ hj => absurd hj (Nat.not_lt_zero _),
          by simp [TopRecsClosed], by simp⟩
      | .Cons (x_a := x_a) (x_rest := x_rest) (m_sszfdvej := m352) (cs_bixmeype := cs354)
          (cs363 := cs363) (ld12 := ld12) (ev_fibarwuo := evPop) (sg_opqpxwys := sg359)
          (op404 := op404) (ev365 := ev365) (hc406 := hc406) .. =>
        obtain ⟨a, rest, rfl, ha_head, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
        have hi_lt56 : i < 72057594037927936 := by simp at hbound; omega
        obtain ⟨rfl, hiff_pop, hidxs_next⟩ := sorted_pop_spec idxs hi_lt56 hidxs evPop
        have hseg : V.HashedCollision extra calls ∨
            (Heap.Extends h m352 ∧
             ∃ recs₁ : List (TopRec calls b.address t lim),
               (i ∈ idxs → RefAllowedIn calls t b.address lim a ∧
                 ((NotBlockIn calls a ∧ a ∈ recs₁.map (·.addr)) ∨ CoveredAt t lim a)) ∧
               TopRecsClosed recs₁ ∧
               (∀ r ∈ recs₁, r.depth ≤ calls.length)) := by
          match sg359 with
          | .n1_n0_n0 (cs_qutgqozh := cs88) (cs_jhnvxttf := cs153) (cs_ziuzjvtk := cs246)
              (ev_icqlvczq := ev90) (ev_qjsortre := ev121) (ev_uzqslaue := ev155)
              (ev_ycpkbnlw := ev177) (ev_qnhmodbg := ev216) (ev_avalyevs := ev230)
              (ev_ondlztqg := ev266) (ld_kxhlyuje := ld260) (ev_syoaqeyu := ev286)
              (ld_dpfinybr := ld303) (ev_iecuttfo := ev248) (hc_deognqoh := hc305) .. =>
            -- `walk_ctx` kept the context's limit: the reference is walked by `check_owned`
            have ext_ra := ev90.heap_extends
            have ext_cov := ev121.heap_extends
            obtain ⟨ext_nb, hnb⟩ :=
              assert_not_block_ref_env (BaseSeams.addr_mono (ext_ra.trans ext_cov) ha_head) ev155
            have ext_pre := ext_ra.trans (ext_cov.trans (ext_nb.trans
              (ev177.heap_extends.trans (ev216.heap_extends.trans ev230.heap_extends))))
            have hrc' := hrc.mono ext_pre
            obtain ⟨rfl, hp_b⟩ := role_ctx_binding_lim_spec hrc' ev266
            obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load_env hp_b ld260
            obtain ⟨rfl, hv⟩ := role_ctx_validator_lim_spec hrc' ev286
            obtain ⟨d_a, rfl, hix_a⟩ := addrVal_of_load_env (BaseSeams.addr_mono ext_pre ha_head) ld303
            have hlt_calls : cs246.length < calls.length := by
              rw [hc406, hc305]
              simp only [List.length_cons, List.length_append]
              omega
            have hlt_sub : cs246.length < fuel := Nat.lt_of_lt_of_le hlt_calls hfuel
            rcases (ih cs246.length hlt_sub).1 (Nat.le_refl _) hix_b hix_a hv ev248 with
              hcoll | ⟨ext_co, _, recs_s, hmem_s, hcl_s, hdep_s⟩
            · exact .inl (hashedCollision_mono
                (fun cl hcl => by rw [hc406, hc305]; simp [hcl]) hcoll)
            have hsub_s : ∀ cl ∈ cs246, cl ∈ calls := fun cl hcl => by
              rw [hc406, hc305]; simp [hcl]
            have hsub_ra : ∀ cl ∈ cs88, cl ∈ calls := fun cl hcl => by
              rw [hc406, hc305]; simp [hcl]
            have hsub_nb : ∀ cl ∈ cs153, cl ∈ calls := fun cl hcl => by
              rw [hc406, hc305]; simp [hcl]
            have hal : RefAllowedIn calls t b.address lim a :=
              ⟨_, _, _, _, _, _, hrc, ha_head, ev90, hsub_ra⟩
            refine .inr ⟨ext_pre.trans ext_co, recs_s.map (TopRec.mono hsub_s), ?_,
              hcl_s.mono hsub_s, topRec_mono_depth_le_env hsub_s hdep_s (Nat.le_of_lt hlt_calls)⟩
            intro _
            refine ⟨hal, .inl ⟨hnb.mono hsub_nb, ?_⟩⟩
            rw [map_addr_topRec_mono]
            exact hmem_s
          | .n1_n0_other (cs_qutgqozh := cs88) (ev_icqlvczq := ev90) (ev_qjsortre := ev121)
              (ev_uzqslaue := ev155) (ev_ycpkbnlw := ev177) (ev_qnhmodbg := ev216)
              (ev_avalyevs := ev230) (op_susgienm := op210) (hne_jolytbqc := hne306)
              (ev_lrepvcdw := ev315) (hc_fxpxruvy := hc332) .. =>
            -- `walk_ctx` changed the limit: the reference is covered at the limit
            have ext_ra := ev90.heap_extends
            have ext_cov := ev121.heap_extends
            have ext_nb := ev155.heap_extends
            have ext_pre := ext_ra.trans (ext_cov.trans ext_nb)
            obtain ⟨ext_wc, hwc⟩ :=
              walk_ctx_lim_spec (hrc.mono ext_pre) (BaseSeams.addr_mono ext_pre ha_head) ev177
            have ext_l1 := ev216.heap_extends
            have ext_l2 := ev230.heap_extends
            rcases hwc with rfl | ⟨hcov, -⟩
            · obtain ⟨-, hx⟩ := role_ctx_limit_lim_spec (hrc.mono (ext_pre.trans ext_wc)) ev216
              obtain ⟨-, hy⟩ :=
                role_ctx_limit_lim_spec (hrc.mono (ext_pre.trans (ext_wc.trans ext_l1))) ev230
              rw [hx, hy] at op210
              simp only [evalBinOp, sub_self, Except.ok.injEq] at op210
              exact absurd op210.symm hne306
            · have hsub_ra : ∀ cl ∈ cs88, cl ∈ calls := fun cl hcl => by
                rw [hc406, hc332]; simp [hcl]
              have hal : RefAllowedIn calls t b.address lim a :=
                ⟨_, _, _, _, _, _, hrc, ha_head, ev90, hsub_ra⟩
              exact .inr ⟨ext_pre.trans (ext_wc.trans (ext_l1.trans (ext_l2.trans
                  ev315.heap_extends))), [],
                fun _ => ⟨hal, .inr hcov⟩, by simp [TopRecsClosed], by simp⟩
          | .n1_other (cs_qutgqozh := cs88) (ev_icqlvczq := ev90) (ev_qjsortre := ev121)
              (hne_kcxluxmw := hne333) (he_vvdjdbjt := he340) (hc_rftbjjug := hc341) .. =>
            -- `walk_covered` skipped the reference: it is covered at the limit
            have ext_ra := ev90.heap_extends
            have ext_cov := ev121.heap_extends
            obtain ⟨-, hv⟩ :=
              walk_covered_lim_spec (hrc.mono ext_ra) (BaseSeams.addr_mono ext_ra ha_head) ev121
            rcases hv with hv0 | hcov
            · exact absurd hv0 hne333
            · have hsub_ra : ∀ cl ∈ cs88, cl ∈ calls := fun cl hcl => by
                rw [hc406, hc341]; simp [hcl]
              have hal : RefAllowedIn calls t b.address lim a :=
                ⟨_, _, _, _, _, _, hrc, ha_head, ev90, hsub_ra⟩
              exact .inr ⟨by rw [he340]; exact ext_ra.trans ext_cov, [],
                fun _ => ⟨hal, .inr hcov⟩, by simp [TopRecsClosed], by simp⟩
          | .other (hne_yeueqpng := hne342) (he_eemargwo := he349) .. =>
            -- the reference is not used
            exact .inr ⟨by subst he349; exact Heap.Extends.refl _, [],
              fun hi_in => absurd (hiff_pop.mpr hi_in) hne342, by simp [TopRecsClosed], by simp⟩
        rcases hseg with hcoll | ⟨ext1, recs₁, hmem₁, hcl₁, hdep₁⟩
        · exact .inl hcoll
        simp only [evalBinOp, Except.ok.injEq] at op404
        subst op404
        have hv_inc : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
        rw [hv_inc] at ev365
        have hlt_tail_calls : cs363.length < calls.length := by
          rw [hc406]
          simp only [List.length_cons, List.length_append]
          omega
        have hlt_tail : cs363.length < fuel := Nat.lt_of_lt_of_le hlt_tail_calls hfuel
        have hbound_tail : (i + 1) + rest.length < 8589934592 := by
          simp at hbound; omega
        rcases (ih cs363.length hlt_tail).2.2 (i := i + 1) (Nat.le_refl _) hbound_tail
            (hrc.mono ext1)
            (repList_heapMono₂ _ repAddrElem_heapMono₂ ext1 hrest_rep)
            (hidxs_next.mono ext1)
            ev365 with
          hcoll | ⟨ext2, recs₂_raw, hmem₂, hcl₂, hdep₂⟩
        · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc406]; simp [hcl]) hcoll)
        have hsub₂ : ∀ cl ∈ cs363, cl ∈ calls := fun cl hcl => by
          rw [hc406]; simp [hcl]
        refine .inr ⟨ext1.trans ext2, recs₁ ++ recs₂_raw.map (TopRec.mono hsub₂), ?_,
          hcl₁.append (hcl₂.mono hsub₂), ?_⟩
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
        · intro r hr
          rcases List.mem_append.mp hr with hr1 | hr2
          · exact hdep₁ r hr1
          · exact topRec_mono_depth_le_env hsub₂ hdep₂ (Nat.le_of_lt hlt_tail_calls) r hr2

/-- **`IxVMCompat::check_owned(binding, validator, a)` at a top-level limit**: unless the run
hashed a collision with `extra`, `a` is claimable and is a record of a closed list of records
walked at the limit. The validator is the one `role_ctx_validator` gives a context at `lim`. -/
theorem check_owned_lim_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none)
    {d_b d_a : Bytes.Address} {x_v r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hix_b : ixAddr d_b = b.address) (hix_a : ixAddr d_a = addr)
    (hv : ((∃ n, lim = some n) ∧ x_v = .field 3) ∨ (lim = none ∧ x_v = .field 4))
    (ev : ObsFn W "IxVMCompat::check_owned" [Ingress.digestV d_b, x_v, Ingress.digestV d_a] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧ ClaimableSeed calls t addr ∧
      ∃ recs : List (TopRec calls b.address t lim),
        addr ∈ recs.map (·.addr) ∧ TopRecsClosed recs ∧
        (∀ r ∈ recs, r.depth ≤ calls.length)) :=
  (env_walk_lim_fuel_aux hadm hb_extra hlim calls.length).1 (Nat.le_refl _) hix_b hix_a hv ev

/-- **`KernelClaim::env_walk_all(rc, a)` at a top-level limit**: unless the run hashed a
collision with `extra`, `a` is a record of a closed list of records walked at the limit. -/
theorem env_walk_all_lim_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none)
    {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t b.address lim h x_rc) (ha : BaseSeams.addr h x_addr addr)
    (ev : ObsFn W "KernelClaim::env_walk_all" [x_rc, x_addr] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧
      ∃ recs : List (TopRec calls b.address t lim),
        addr ∈ recs.map (·.addr) ∧ TopRecsClosed recs ∧
        (∀ r ∈ recs, r.depth ≤ calls.length)) :=
  (env_walk_lim_fuel_aux hadm hb_extra hlim calls.length).2.1 (Nat.le_refl _) hrc ha ev

/-- **`KernelClaim::env_walk_refs_all(rc, refs, consts, i)` at a top-level limit**: unless the
run hashed a collision with `extra`, each reference at a position in `consts` was asked about,
and is a walked record that is no block record or is covered at the limit; the walked records
are closed. -/
theorem env_walk_refs_all_lim_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none)
    {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
    {x_rc x_refs x_consts r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbound : i + refs.length < 8589934592)
    (hrc : RCLimRep t b.address lim h x_rc)
    (hrefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs x_refs)
    (hidxs : RepSortedIdxFrom h idxs i x_consts)
    (ev : ObsFn W "KernelClaim::env_walk_refs_all"
      [x_rc, x_refs, x_consts, .field (i : F)] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧
      ∃ recs : List (TopRec calls b.address t lim),
        (∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
          RefAllowedIn calls t b.address lim refs[j] ∧
          ((NotBlockIn calls refs[j] ∧ refs[j] ∈ recs.map (·.addr)) ∨
            CoveredAt t lim refs[j])) ∧
        TopRecsClosed recs ∧
        (∀ r ∈ recs, r.depth ≤ calls.length)) :=
  (env_walk_lim_fuel_aux hadm hb_extra hlim calls.length).2.2 (Nat.le_refl _) hbound hrc hrefs
    hidxs ev

/-! ## `walk_leaves_owned` at a top-level limit -/

private theorem walk_leaves_owned_lim_aux {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none)
    (as : List Bytes.Address) :
    ∀ {x_rc x_leaves r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RCLimRep t b.address lim h x_rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h as x_leaves →
      ObsFn W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] h r h' calls →
      V.HashedCollision extra calls ∨
      (Heap.Extends h h' ∧ (∀ a ∈ as.map ixAddr, ClaimableSeed calls t a) ∧
        ∃ recs : List (TopRec calls b.address t lim),
          (∀ a ∈ as.map ixAddr, a ∈ recs.map (·.addr)) ∧ TopRecsClosed recs ∧
          (∀ r ∈ recs, r.depth ≤ calls.length)) := by
  induction as with
  | nil =>
    intro x_rc x_leaves r h h' calls hrc hl ev
    match Obs.«KernelClaim::walk_leaves_owned».obs ev with
    | .Nil (he23 := he23) .. =>
      subst he23
      exact .inr ⟨Heap.Extends.refl _, by simp, [], by simp, by simp [TopRecsClosed], by simp⟩
    | .Cons (ld12 := ld12) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hl ld12
      cases hbad
  | cons aB rest ih =>
    intro x_rc x_leaves r h h' calls hrc hl ev
    match Obs.«KernelClaim::walk_leaves_owned».obs ev with
    | .Nil (ld12 := ld12) .. => cases Lib.rep_nil_of_load hl ld12
    | .Cons (cs53 := cs53) (cs115 := cs115) (ld12 := ld12) (ev73 := ev73) (ld67 := ld67)
        (ev93 := ev93) (ld110 := ld110) (ev55 := ev55) (ev117 := ev117) (hc134 := hc134) .. =>
      obtain ⟨aB', rest', heq, ha_ref, hrest⟩ := Lib.rep_cons_of_load hl ld12
      injection heq with he1 he2
      subst he1 he2
      obtain ⟨rfl, hp_b⟩ := role_ctx_binding_lim_spec hrc ev73
      obtain ⟨d_b, rfl, hix_b⟩ := addrVal_of_load_env hp_b ld67
      obtain ⟨rfl, hv⟩ := role_ctx_validator_lim_spec hrc ev93
      have hv58 := Ingress.load_repAddressRef ha_ref ld110
      subst hv58
      rcases check_owned_lim_spec (V := V) hadm hb_extra hlim hix_b rfl hv ev55 with
        hcoll | ⟨ext1, hseed_hd, recs₁, hmem₁, hcl₁, hdep₁⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc134]; simp [hcl]) hcoll)
      rcases ih (hrc.mono ext1)
          (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hrest) ev117 with
        hcoll | ⟨ext2, hseed_tl, recs₂, hmem₂, hcl₂, hdep₂⟩
      · exact .inl (hashedCollision_mono (fun cl hcl => by rw [hc134]; simp [hcl]) hcoll)
      have hsub₁ : ∀ cl ∈ cs53, cl ∈ calls := fun cl hcl => by rw [hc134]; simp [hcl]
      have hsub₂ : ∀ cl ∈ cs115, cl ∈ calls := fun cl hcl => by rw [hc134]; simp [hcl]
      have hle₁ : cs53.length ≤ calls.length := by
        rw [hc134]; simp only [List.length_cons, List.length_append]; omega
      have hle₂ : cs115.length ≤ calls.length := by
        rw [hc134]; simp only [List.length_cons, List.length_append]; omega
      refine .inr ⟨ext1.trans ext2, ?_,
        recs₁.map (TopRec.mono hsub₁) ++ recs₂.map (TopRec.mono hsub₂),
        ?_, (hcl₁.mono hsub₁).append (hcl₂.mono hsub₂), ?_⟩
      · intro a ha_mem
        rcases List.mem_cons.mp ha_mem with rfl | htl
        · exact hseed_hd.mono hsub₁
        · exact (hseed_tl a htl).mono hsub₂
      · intro a ha_mem
        rw [List.map_append, map_addr_topRec_mono, map_addr_topRec_mono]
        rcases List.mem_cons.mp ha_mem with rfl | htl
        · exact List.mem_append_left _ hmem₁
        · exact List.mem_append_right _ (hmem₂ a htl)
      · intro r hr
        rcases List.mem_append.mp hr with hr1 | hr2
        · exact topRec_mono_depth_le_env hsub₁ hdep₁ hle₁ r hr1
        · exact topRec_mono_depth_le_env hsub₂ hdep₂ hle₂ r hr2

/-- **`KernelClaim::walk_leaves_owned(rc, leaves)` at a top-level limit** (a `checkEnv` claim's
walk): unless the run hashed a collision with `extra`, every leaf is claimable and is a record
of a closed list of records walked at the limit. -/
theorem walk_leaves_owned_lim_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra) {lim : Option Nat} (hlim : lim = some 77 ∨ lim = none)
    (as : List Bytes.Address) {x_rc x_leaves r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (hrc : RCLimRep t b.address lim h x_rc)
    (hl : RepList addrListEnum (Bytes.RepAddressRef addrTy) h as x_leaves)
    (ev : ObsFn W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧ (∀ a ∈ as.map ixAddr, ClaimableSeed calls t a) ∧
      ∃ recs : List (TopRec calls b.address t lim),
        (∀ a ∈ as.map ixAddr, a ∈ recs.map (·.addr)) ∧ TopRecsClosed recs ∧
        (∀ r ∈ recs, r.depth ≤ calls.length)) :=
  walk_leaves_owned_lim_aux hadm hb_extra hlim as hrc hl ev

end IxVM.Refinement.Claim
