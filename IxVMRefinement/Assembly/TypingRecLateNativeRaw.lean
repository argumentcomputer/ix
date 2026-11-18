import IxVMRefinement.Assembly.TypingRecLateNativeFront2
import IxVMRefinement.Assembly.TypingRecLateNativeElim
import IxVMRefinement.Assembly.TypingRecLateNativeRead

/-! # The scoping of a late recursor's rules, from the member check

A late recursor record `c` at `A` (`c.info = .recr rc`) is checked by `check_const`'s `Rec` arm,
whose member check `check_recursor_member` runs `check_rec_rules_wellscoped` on the record's
converted rule list: the scope check `validate_expr_well_scoped(rhs, 0, nlvls)` on every rule's
right-hand side, `nlvls` the record's level count. That check reads the right-hand side's heap
cells syntactically: every `BVar` below the binders it passes, every level parameter of a `Srt`
or `Const` cell below `nlvls` (`Assembly.validate_expr_well_scoped_spec`). So:

* `rec_member_rules_scope_run`: the member check runs the rules' scope check on the record's rule
  list and level count, at a heap after its own, within its calls;
* `rules_wellscoped_reads`: by induction on a converted rule list, every rule's right-hand side
  read under the positions is closed and its level parameters are positions below `nlvls`;
* `rec_rules_reads_scoped`: at the record's load (`RecArmRun`), every rule of the record read
  under the positions is scoped by the record's level count;
* `rec_lvls_or_of_arm`: at the tied parent, the record's level count is the member's, or one
  more (the canonical comparison's level link, `nat_rec_check_levels`);
* `rec_rules_scoped_of_arm`: every rule read under the record's level parameters
  `ps := recLps large (range k)` is closed and its level parameters are among `ps`, the reading
  under `ps` being the reading under the positions renamed by `posOf ps`
  (`read_recParam_scoped`).
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency

/-! ## The rules' scope check inside the member check -/

/-- **The member check runs the rules' scope check**: `check_recursor_member` runs
`check_rec_rules_wellscoped` on the record's rule list with the record's level count, at a heap
after its own, its calls among the member check's. -/
theorem rec_member_rules_scope_run
    {rc address levels type parameters indices motives minors rules k unsafeFlag block position
      result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_member"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address]
      heap result final calls) :
    ∃ (depth r : SourceValue F) (scopeHeap scopeAfter : Heap F) (scopeCalls : List (Call F)),
      Heap.Extends heap scopeHeap ∧
      ObsFn Obs.W "KernelCheck::check_rec_rules_wellscoped" [rules, depth, levels]
        scopeHeap r scopeAfter scopeCalls ∧
      (∀ cl ∈ scopeCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::check_recursor_member».obs observed with
  | .run (hv15 := input) (ev85 := e1) (ev142 := e2) (ev233 := e3) (ev278 := e4) (ev292 := e5)
      (ev314 := e6) (ev382 := e7) (ev412 := e8) (ev477 := scopeRun) (hc898 := children) .. =>
    injection input with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    refine ⟨_, _, _, _, _,
      e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
        (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
          (e7.heap_extends.trans e8.heap_extends)))))), scopeRun, ?_⟩
    intro call member
    rw [children]
    simp [member]

/-- **The rules' scope check, rule by rule**: on a converted rule list at a heap before the
check's, every rule's right-hand side read under the positions is closed and its level
parameters are positions below the level count the check is given. -/
theorem rules_wellscoped_reads {calls : List (Call F)} (hbound : Bounded calls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {h₀ : Heap F} {nlvls : Nat} (hn : nlvls < 4294967296) :
    ∀ (rus : List Ixon.RecursorRule) {j : Nat} {root : F} {p depth r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      L1.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
        tree h₀ j root rus p →
      Heap.Extends h₀ h →
      ObsFn Obs.W "KernelCheck::check_rec_rules_wellscoped" [p, depth, .field (nlvls : F)]
        h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ ru ∈ rus, ∀ E_rd : Ix.Kernel.Expr .anon,
        (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ru.rhs = .ok E_rd →
        E_rd.looseBVarsBounded 0 = true ∧
          E_rd.allLevelParamsDefined (List.range nlvls) = true := by
  intro rus
  induction rus with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ ru hru
    cases hru
  | cons ru₀ rus ih =>
    intro j root p depth r h h' cs htr hext ev hsub ru hru E_rd hread
    cases htr with
    | cons cell hf raw planned levels rs =>
      match Obs.«KernelCheck::check_rec_rules_wellscoped».obs ev with
      | .Nil (ld12 := ld) .. =>
        have ld' : loadValue h _ = .ok (.construct Core.krrListEnum "Nil" []) := ld
        exact (Core.load_cell_ne (hext.getElem?_eq cell) ld' (by decide)).elim
      | .Cons (x_rest := xrest) (w58 := w0) (x_nf := xnf) (x_rhs := xr) (ld12 := ld)
          (ev87 := evV) (ev116 := evR) (hc141 := hcalls) .. =>
        have ld' : loadValue h _ = .ok (.construct Core.krrListEnum "Cons"
            [.construct Core.krrEnum "Mk" [w0, xnf, xr], xrest]) := ld
        obtain ⟨-, hxs⟩ := Core.load_cell (hext.getElem?_eq cell) ld'
        simp only [List.cons.injEq, and_true] at hxs
        obtain ⟨hmk, hrest⟩ := hxs
        injection hmk with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨-, -, hrhs⟩ := hargs
        subst hrhs hrest
        rcases List.mem_cons.mp hru with rfl | hmem
        · exact (Assembly.validate_expr_well_scoped_spec hbound hn raw hext hread evV
            (hsub _ (by rw [hcalls]; simp))).2
        · exact ih rs (hext.trans evV.heap_extends) evR
            (fun cl hcl => hsub cl (by rw [hcalls]; simp [hcl])) ru hmem E_rd hread

/-! ## At the record's load -/

/-- **Every rule of the record, read under the positions, is scoped by the record's level
count**: at the record's load (`RecArmRun`), the member check's scope check runs on the
converted rule list. -/
theorem rec_rules_reads_scoped {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) :
    ∀ ru ∈ rc.rules.toList, ∀ E_rd : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t A)).read ru.rhs = .ok E_rd →
      E_rd.looseBVarsBounded 0 = true ∧
        E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true := by
  have hgood := hst.good default none
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := hnat
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    L1.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold L1.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, -, -, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, bR, planT, -, -, hv, -, -, -,
    hrulesTr⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfields
  obtain ⟨-, sB, sA, sortAfter, mH, sR, sortR, sCs, sortCs, mCs, hextS, evS, -, evSort,
    -, -, hextSM, evM, hsubM⟩ := check_const_rec_arm ev_chk
  have hextM : Heap.Extends m_chk mH :=
    hextS.trans (evS.heap_extends.trans ((Heap.Extends.snoc _ _).trans
      (evSort.heap_extends.trans hextSM)))
  obtain ⟨depth, rR, scopeHeap, scopeAfter, scopeCalls, eSc, evSc, hsSc⟩ :=
    rec_member_rules_scope_run evM
  intro ru hru E_rd hread
  exact rules_wellscoped_reads hgood.2 (cx := readCtx t (fun x => E₀.blobs.get? x)) (src := c)
    (self := soloSelf t (Core.ixAddr a')) hlvls rc.rules.toList hrulesTr (hextM.trans eSc) evSc
    (fun cl hcl => hsub_chk cl (hsubM cl (hsSc cl hcl))) ru hru E_rd hread

/-! ## The level count at the tied parent -/

/-- **The record's level count is the member's, or one more**: the canonical comparison at the
tied parent runs `nat_rec_check` with the large-eliminator bit as universe offset, and
`nat_rec_check` asserts the record's level count is the parent's plus the offset. -/
theorem rec_lvls_or_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    rc.lvls.toNat = ind.lvls.toNat ∨ rc.lvls.toNat = ind.lvls.toNat + 1 := by
  obtain ⟨rcv, apv, parentV, tyPtr, rulesPtr, blkPtr, tyPtrP, unsP, blkPtrP, pointer, result,
    scopeResult, sortResult, bA, bR, bT, bP, blobs, tree, planT, ldHeap, scopeBefore, scopeAfter,
    sortAfter, memberHeap, scanHeap, loadedHeap, canonHeap, final, ldCalls, scopeCalls,
    sortCalls, scanCalls, loadCalls, canonCalls, hrc, hbA, hbA', hbR, hbR', hhp, hsLd, hblob,
    built, rty, hpT, hlT, hrulesTr, hrules_lt, hidx56, hlvR, hpR, hiR, hmR, hmiR, hlvP, hpP, hiP,
    hcP, eLS, evS, hmemS, evSort, hsSort, eSM, evScan, hsScan, hbT, hbT', hbP, hbP', eSL, evLoad,
    hsLoad, hldP, eC, evCanon, hsCanon⟩ :=
    rec_front_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  obtain ⟨large', natHeap, natCalls, eN, evNat, hsNat⟩ := canonical_full_nat_rec_bool evCanon
  have hsum := Decl.evalBinOp_add_nat _ _ (nat_rec_check_levels evNat)
  have hb1 : (if large' then 1 else 0 : Nat) ≤ 1 := by cases large' <;> decide
  have hlvEq : rc.lvls.toNat = ind.lvls.toNat + (if large' then 1 else 0) :=
    field_nat_inj (by omega) (by omega) hsum
  cases large' with
  | false => exact Or.inl (by simpa using hlvEq)
  | true => exact Or.inr (by simpa using hlvEq)

/-! ## The rules' scoping at the arm -/

/-- A pair of a positionwise relation has its right-hand entry's partner on the left. -/
theorem forall₂_exists_left_of_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ →
      ∃ a, a ∈ l₁ ∧ R a b
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons hr hs, _, hb => by
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), hr⟩
    · obtain ⟨a, ha, hra⟩ := forall₂_exists_left_of_mem_right hs hb'
      exact ⟨a, List.mem_cons.mpr (Or.inr ha), hra⟩

/-- **The scoping of the record's rules as the reader reads them, at the arm**: every rule read
under the record's level parameters `ps := recLps large (range k)` is closed and its level
parameters are among `ps`. The member check's scope check bounds the rules read under the
positions by the record's level count, which is `ps.length` (`rec_lvls_or_of_arm`); the reading
under `ps` is that reading renamed by `posOf ps`. -/
theorem rec_rules_scoped_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim)
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    ∀ rules : List (Ix.Kernel.RecRule .anon),
      List.Forall₂ (fun ru rl₀ => (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules →
      ∀ rl₀ ∈ rules, rl₀.rhs.looseBVarsBounded 0 = true ∧
        rl₀.rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true := by
  intro rules hrd rl₀ hrl
  have hlvOr := rec_lvls_or_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi
    htie hcb hms hind
  have hpsLen : (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat)).length = rc.lvls.toNat := LoadedReads.recPs_length hlvOr
  have hpsPerm : (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat)).Perm (List.range (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)).length) :=
    LoadedReads.recPs_perm hlvOr
  obtain ⟨ru, hru, hR⟩ := forall₂_exists_left_of_mem_right hrd hrl
  have hid := read_recParam_posOf hpsPerm hR
  obtain ⟨hlbb₀, hdef₀⟩ := rec_rules_reads_scoped hS hst hc hinfo hnat ru hru _ hid
  exact read_recParam_scoped hpsPerm hR hid hlbb₀ (by rw [hpsLen]; exact hdef₀)

end IxVM.Refinement.Typing
