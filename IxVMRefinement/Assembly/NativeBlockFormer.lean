import IxVMRefinement.Assembly.NativeBlockStage
import IxVMRefinement.Assembly.TypingDefnCheck
import IxVMRefinement.Decl.NativePrelude

/-! # The former of a native block, typed at the prefix

The former's type is checked against the prefix (`k_ensure_sort` in the `Induct` arm), so its
heap term must be represented under the prefix's keying, which does not resolve the former's own
address. The circuit's scan `expr_mentions_block(ty, [B]) = 0` (run on the heap term, through the
type, value and body of every `let`) excludes a `Const` cell at a member of the block, so every
cell of the term is a reference the block uses, which the prefix stores.

* `TmExact.rekey`, `TmCExact.rekey`: exact representations under another keying that agrees on
  the term's cells;
* `LoadedReads.annotation_canon_exact`: `annotation_canon_range` keeping the exact representation;
* `peer_zero_not_former`, `mentions_block_cells`: a cell of a scanned term is no member of the
  block, or heads a projection;
* `formerChecked_of_member`: from the walked check of the block's member, the canonical former is
  checked at the prefix (`ConstantValCheckJ`) and its type is typed there as a sort.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency

/-! ## Exact representations under another keying -/

theorem TmExact.rekey {κ₁ κ₂ : _root_.Address → Core.KKey} {d : Nat} {Γ : Nat → Core.KExpr}
    {h : Heap F} {k : Nat} {E : Core.KExpr} {p : SourceValue F}
    (rep : Decl.TmExact κ₁ d Γ h k E p) :
    (∀ a, Core.AddrIn h p a → κ₂ (Core.ixAddr a) = κ₁ (Core.ixAddr a)) →
    (∀ a, Core.ProjIn h p a → Core.ProjPermitted κ₁ (Core.ixAddr a) →
      Core.ProjPermitted κ₂ (Core.ixAddr a)) →
      Decl.TmExact κ₂ d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact fun _ _ => .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact fun _ _ => .bvarFree cell hs hk hd
  | sort cell rl => exact fun _ _ => .sort cell rl
  | @const k addr ap lsp a ls res cell ra rls =>
    intro agree _
    have e := agree a (.const cell ra)
    have : Core.Resolved (κ₂ (Core.ixAddr a)) := ⟨by rw [e]; exact res.ne⟩
    rw [← e]
    exact .const cell ra rls
  | app cell _ _ ihf iha =>
    exact fun agree perm => .app cell
      (ihf (fun a m => agree a (.appFn cell m)) (fun a m => perm a (.appFn cell m)))
      (iha (fun a m => agree a (.appArg cell m)) (fun a m => perm a (.appArg cell m)))
  | lam cell _ _ rl iht ihb =>
    exact fun agree perm => .lam cell
      (iht (fun a m => agree a (.lamTy cell m)) (fun a m => perm a (.lamTy cell m)))
      (ihb (fun a m => agree a (.lamBody cell m)) (fun a m => perm a (.lamBody cell m))) rl
  | forallE cell _ _ rl iht ihb =>
    exact fun agree perm => .forallE cell
      (iht (fun a m => agree a (.forallTy cell m)) (fun a m => perm a (.forallTy cell m)))
      (ihb (fun a m => agree a (.forallBody cell m)) (fun a m => perm a (.forallBody cell m))) rl
  | letE cell _ _ _ iht ihv ihb =>
    exact fun agree perm => .letE cell
      (iht (fun a m => agree a (.letTy cell m)) (fun a m => perm a (.letTy cell m)))
      (ihv (fun a m => agree a (.letVal cell m)) (fun a m => perm a (.letVal cell m)))
      (ihb (fun a m => agree a (.letBody cell m)) (fun a m => perm a (.letBody cell m)))
  | litNat cell rl hc => exact fun _ _ => .litNat cell rl hc
  | litStr cell rb hs => exact fun _ _ => .litStr cell rb hs
  | @proj k addr ap ep a i E res pm cell ra _ ih =>
    intro agree perm
    have e := agree a (.projHead cell ra)
    have : Core.Resolved (κ₂ (Core.ixAddr a)) := ⟨by rw [e]; exact res.ne⟩
    have : Core.ProjPermitted κ₂ (Core.ixAddr a) := perm a (.head cell ra) pm
    rw [← e]
    exact .proj cell ra
      (ih (fun a m => agree a (.projArg cell m)) (fun a m => perm a (.projArg cell m)))

theorem TmCExact.rekey {κ₁ κ₂ : _root_.Address → Core.KKey} {h : Heap F} {E : Core.KExpr}
    {p : SourceValue F} (rep : Decl.TmCExact κ₁ h E p)
    (agree : ∀ a, Core.AddrIn h p a → κ₂ (Core.ixAddr a) = κ₁ (Core.ixAddr a))
    (perm : ∀ a, Core.ProjIn h p a → Core.ProjPermitted κ₁ (Core.ixAddr a) →
      Core.ProjPermitted κ₂ (Core.ixAddr a)) :
    Decl.TmCExact κ₂ h E p :=
  fun d Γ => TmExact.rekey (rep d Γ) agree perm

end IxVM.Refinement.Typing

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-- **`annotation_canon_range`, keeping the exact representation** under the table's keying. -/
theorem annotation_canon_exact {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {n : Nat}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {E_rd : Ix.Kernel.Expr .anon} {root : F} {tree : L1.BinderTreeData}
    {plan : List Core.KLevel}
    (hn : n < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hread : (exprReader t blob src id self).read e = .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined (List.range n) = true) :
    ∃ E' : Ix.Kernel.Expr .anon,
      canonAnn src (List.range n) root e E_rd = some E' ∧ Annotates E' E_rd ∧
      Decl.TmCExact (Core.keyOf t) h (Core.posOf (List.range n) E') kp := by
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range n)) self).read e = .ok E_rd := by
    have h1 : (exprReader t blob src (Ix.Kernel.Reader.recParam (List.range n)) self).read e =
        .ok E_rd := by
      rw [Assembly.recParam_range]
      exact hread
    exact h1
  obtain ⟨E', hann, htm, htrace⟩ :=
    raw.toTmCExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := List.range n) (by simp)
      (by simpa using hn) (readCtx_keyAt_inv ht blob) hselfk hagree hread' hlbb hdef
  have hap := htrace plan levels []
  rw [List.append_nil] at hap
  refine ⟨E', ?_, hann, htm⟩
  unfold canonAnn
  rw [canonTree_eq built, planned]
  show (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel (List.range n) level))
    E_rd plan).map Prod.fst = some E'
  rw [hap]
  rfl

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency

/-! ## The scan excludes the block's own member -/

section Scan

variable {c : Core.Ctx} {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}

/-- **A constant the peer test answers `0` for is not the block's member**, where the store holds
the block and its member's projection record. -/
theorem peer_zero_not_former (hdec : L1.EnvDecoded c.E)
    (hblock : recordOf c.E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf c.E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    {b₀ : Bytes.Address} (hb₀ : Core.ixAddr b₀ = B)
    {a : Bytes.Address} {ca bas : SourceValue F} {m m' : Heap F} {cs : List (Call F)}
    (ha : Bytes.RepAddressRef Core.addrTy m a ca)
    (hbas : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m [b₀] bas)
    (ev : ObsFn Core.W "KernelCheck::caddr_is_peer" [ca, bas] m (.field 0) m' cs)
    (hg : Core.Good c cs) : Core.ixAddr a ≠ Core.iprjAddr B 0 := by
  intro hx
  have hrecA : Ix.Cert.recordAt c.E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hx]
    exact recordAt_of_recordOf hdec hproj
  have hdecA : ∀ lc, c.E.consts.get? (Core.ixAddr a) = some lc →
      Ixon.deConstantExact lc.rawBytes = .ok (memberProjection B 0 (.indc ind)) := by
    rw [hx]
    exact decoded_at_of_recordOf hproj
  have h0 : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  have hmem0 : (#[.indc ind] : Array Ixon.MutConst)[
      (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat]? = some (.indc ind) := by
    rw [h0]
    rfl
  match Obs.«KernelCheck::caddr_is_peer».obs ev with
  | .Induct (m2 := m2) (p9 := p9) (cs15 := cs15) (ev17 := ev_ci) (ld11 := ld) (ev94 := ev_in)
      (hc111 := hc) .. =>
    subst hc
    have hg1 : Core.Good c cs15 := hg.sub (fun x hx => by simp [hx])
    obtain ⟨nl', ty', u', blk', b', hld', hb', hbB', -, -⟩ :=
      L1.indRecord_of_deConstantExact (c := c) (p := ⟨(0 : Nat).toUInt64, B⟩) hdecA
        (decoded_at_of_recordOf hblock) ev_ci hg1 ha hrecA rfl
        (recordAt_of_recordOf hdec hblock) hmuts hmem0
    rw [hld'] at ld
    have same := Except.ok.inj ld
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at same
    obtain ⟨-, -, -, -, -, -, hblkEq, -⟩ := same
    rw [← hblkEq] at ev_in
    have hbas' := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
      ev_ci.heap_extends hbas
    obtain ⟨-, hres⟩ := Decl.addr_list_contains_singleton_spec hbas' hb' ev_in
    rcases hres with ⟨hr1, -⟩ | ⟨-, hne⟩
    · exact nomatch hr1
    · exact hne (hbB'.trans hb₀.symm)
  | .other (m2 := m2) (p9 := p9) (cs15 := cs15) (ev17 := ev_ci) (ld11 := ld)
      (hne112 := hne_ind) (hc118 := hc) .. =>
    subst hc
    have hg1 : Core.Good c cs15 := hg.sub (fun x hx => by simp [hx])
    obtain ⟨nl', ty', u', blk', b', hld', -, -, -, -⟩ :=
      L1.indRecord_of_deConstantExact (c := c) (p := ⟨(0 : Nat).toUInt64, B⟩) hdecA
        (decoded_at_of_recordOf hblock) ev_ci hg1 ha hrecA rfl
        (recordAt_of_recordOf hdec hblock) hmuts hmem0
    rw [ld] at hld'
    injection hld' with hv1
    exact hne_ind [_, _, _, _, _, _, _, _] rfl hv1

/-- **A cell of a term the scan answers `0` for is no member of the block, or heads a
projection.** The scan runs on the heap term (every `let`'s type, value and body). -/
theorem mentions_block_cells (hdec : L1.EnvDecoded c.E)
    (hblock : recordOf c.E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf c.E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    {b₀ : Bytes.Address} (hb₀ : Core.ixAddr b₀ = B) {h : Heap F} :
    ∀ {pe : SourceValue F} {a : Bytes.Address}, Core.AddrIn h pe a →
    ∀ {m m' : Heap F} {bas : SourceValue F} {cs : List (Call F)},
      Heap.Extends h m → RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m [b₀] bas →
      ObsFn Core.W "KernelCheck::expr_mentions_block" [pe, bas] m (.field 0) m' cs →
      Core.Good c cs → Core.ProjIn h pe a ∨ Core.ixAddr a ≠ Core.iprjAddr B 0 := by
  intro pe a hin
  induction hin with
  | const cell ra =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Const (cs66 := cs66) (ld12 := ld) (ev68 := ev_peer) (hc85 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      injection hargs with hap _
      subst hap
      exact Or.inr (peer_zero_not_former hdec hblock hmuts hproj hb₀
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext ra) hbas ev_peer
        (hg.sub (fun x hx => by simp [hc, hx])))
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) .. | .Let_other_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | projHead cell ra =>
    intro _ _ _ _ _ _ _ _
    exact Or.inl (.head cell ra)
  | projArg cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Proj (cs516 := cs1) (ld12 := ld) (ev518 := ev1) (hc535 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, -, rfl⟩ := hargs
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.projArg cell hp)
      · exact Or.inr hne
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) .. | .Let_other_other (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | appFn cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .App_other (cs115 := cs1) (ld12 := ld) (ev117 := ev1) (hne141 := hne1) (hc167 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.appFn cell hp)
      · exact Or.inr hne
    | .App_n1 (he138 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .Lam_n1 (ld12 := ld) .. | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | appArg cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .App_other (cs148 := cs2) (ld12 := ld) (ev117 := ev1) (ev150 := ev2) (hc167 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl⟩ := hargs
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.appArg cell hp)
      · exact Or.inr hne
    | .App_n1 (he138 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .Lam_n1 (ld12 := ld) .. | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | lamTy cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Lam_other (cs203 := cs1) (ld12 := ld) (ev205 := ev1) (hne229 := hne1) (hc255 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.lamTy cell hp)
      · exact Or.inr hne
    | .Lam_n1 (he226 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | lamBody cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Lam_other (cs236 := cs2) (ld12 := ld) (ev205 := ev1) (ev238 := ev2) (hc255 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.lamBody cell hp)
      · exact Or.inr hne
    | .Lam_n1 (he226 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | forallTy cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Forall_other (cs291 := cs1) (ld12 := ld) (ev293 := ev1) (hne317 := hne1)
        (hc343 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.forallTy cell hp)
      · exact Or.inr hne
    | .Forall_n1 (he314 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | forallBody cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Forall_other (cs324 := cs2) (ld12 := ld) (ev293 := ev1) (ev326 := ev2)
        (hc343 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.forallBody cell hp)
      · exact Or.inr hne
    | .Forall_n1 (he314 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | letTy cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Let_other_other (cs378 := cs1) (ld12 := ld) (ev380 := ev1) (hne404 := hne1)
        (hc472 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.letTy cell hp)
      · exact Or.inr hne
    | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | letVal cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Let_other_other (cs420 := cs2) (ld12 := ld) (ev380 := ev1) (ev422 := ev2)
        (hne446 := hne2) (hc472 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev2).resolve_right hne2] at ev2
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.letVal cell hp)
      · exact Or.inr hne
    | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | letBody cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Let_other_other (cs453 := cs3) (ld12 := ld) (ev380 := ev1) (ev422 := ev2)
        (ev455 := ev3) (hc472 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, -, rfl⟩ := hargs
      have ext12 := ev1.heap_extends.trans ev2.heap_extends
      have hbas3 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext12 hbas
      rcases ih (ext.trans ext12) hbas3 ev3 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.letBody cell hp)
      · exact Or.inr hne
    | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim

end Scan

/-! ## The former checked at the prefix -/

/-- **The former of a native block, checked at the prefix.** From the walked check of member `0`
of the block at `B` under the walk's role context at the limit `n`: the canonical annotation `ty'`
of the reading `ty₀` of the former's type is checked against the prefix environment
(`ConstantValCheckJ`, at the prefix's keying, where the former's own address does not resolve), and
it is typed there as a sort. The inputs about the prefix are the invariant, the references the
block uses stored, the former's key fresh and free. -/
theorem formerChecked_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {n : Nat} {env : Ix.Kernel.Env .anon}
    (hst : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hfv : ty₀.hasFvar = false)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0))) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ =
        some ty' ∧ Annotates ty' ty₀ ∧
      Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ ∧
      ∃ sty u, Ix.Kernel.Rules.Infer env .full 0 ty' sty ∧
        Ix.Kernel.Rules.Red env 0 sty (.sort u) := by
  have hbound : Bounded calls := (hst.good env none).2
  have hchkA := mutsMemberAt_checkedAt hbound hchk
    (rfl : (#[.indc ind] : Array Ixon.MutConst)[0]? = some (.indc ind))
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre,
    ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchkA
  obtain ⟨a, ha, hax⟩ := ha_pre
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hg_ld : Core.Good ⟨E, env, t, some n⟩ cs_load := hgood.sub hsub_ld
  have hg_chk : Core.Good ⟨E, env, t, some n⟩ cs_chk := hgood.sub hsub_chk
  have h0' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  -- the load of the member's projection record, traced
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrec : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hproj
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B 0 (.indc ind) := by
    rw [hb, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts))
  subst hmsEq
  rw [h0'] at hms planned hraw
  have hiEq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst typePtr
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hg_ld.1 hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon_exact ht hlvls (LoadedReads.blockSelf_key t B #[.indc ind])
      hagree rty built planned trace hty hty_lbb hty_def
  -- the prelude of the check
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  -- the references the block uses are stored in the prefix
  have used : ∀ x, L1.RefUsed cb.refs.toList cb.sharing.toList ind.typ x →
      ∃ ci, env.find? (Core.keyOf t x) = some ci := by
    have hmem' : Ixon.MutConst.indc ind ∈ (#[.indc ind] : Array Ixon.MutConst).toList :=
      List.mem_singleton.mpr rfl
    intro x hu
    obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      rw [hmuts]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.indc ind, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
  let κP := (Core.Ctx.stored ⟨E, env, t, some n⟩).κ
  have hextM : Heap.Extends m_chk prelude.mentionsBefore :=
    prelude.initialExtended.trans prelude.scope_to_mentions
  have hagreeP : ∀ a', Core.AddrIn m_chk tyPtr a' →
      κP (Core.ixAddr a') = Core.keyOf t (Core.ixAddr a') := by
    intro a' hin
    rcases rty.addrIn_used a' hin with hu | hr
    · obtain ⟨ci, hci⟩ := used _ hu
      exact Core.Ctx.stored_key_of_find (c := ⟨E, env, t, some n⟩) hci
    · exfalso
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨m, hm, hxm⟩ := LoadedReads.blockRecurAddrs_get hk
      have hk0 : k = 0 := by
        have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
        omega
      subst hk0
      have hmm : m = .indc ind := by simpa using hm.symm
      subst hmm
      rw [LoadedReads.memberAddr_indc] at hxm
      have hxm' : Core.ixAddr a' = Core.iprjAddr B 0 := hxm
      have hscan := mentions_block_cells (c := ⟨E, env, t, some n⟩) hst.decoded hblock hmuts hproj
        hb_eq hin hextM (prelude.blocksRep hb_rep) prelude.mentionsRun
        (hg_chk.sub prelude.mentionsSubset)
      rcases hscan with hp | hne
      · obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
        rw [hxm', hfresh] at hci
        cases hci
      · exact hne hxm'
  have hpermP : ∀ a', Core.ProjIn m_chk tyPtr a' →
      Core.ProjPermitted (Core.keyOf t) (Core.ixAddr a') → Core.ProjPermitted κP (Core.ixAddr a') := by
    intro a' hp _
    obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
    exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, some n⟩) hci
  have htmP : Decl.TmCExact κP m_chk (Core.posOf (List.range ind.lvls.toNat) ty') tyPtr :=
    htmT.rekey hagreeP hpermP
  have hvP : Decl.ValRepExact κP m_chk (.field (ind.lvls.toNat : F)) tyPtr
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ :=
    ⟨by simp, by simpa using hlvls, by simp, htmP⟩
  have hgS : Core.CoreGood (Core.Ctx.stored ⟨E, env, t, some n⟩) prelude.sortCalls :=
    Core.CoreGood.ofRaw (hg_chk.sub prelude.sortSubset) (fun _ _ => trivial)
  obtain ⟨checked, sty, u, ℓ, inferred, reduced, -, -⟩ :=
    Decl.constantValCheckJ_of_scoped (c := Core.Ctx.stored ⟨E, env, t, some n⟩)
      (cv := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩)
      ⟨rfl, rfl, hannT⟩ (hvP.mono prelude.initialExtended) hty_lbb hfv hfresh hfree.1
      (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) hinv.store.store
      (Decl.PosSortLift.of_range rfl) prelude.scopeRun prelude.scope_to_sort
      (hrc_m.toRCRep.mono (prelude.initialExtended.trans prelude.scope_to_sort))
      (prelude.typesRep κP (fun _ => default)) hinv.scopedCoreFacts.1 hinv.loads hgS
      prelude.sortRun
  rw [Decl.posOf_range] at inferred
  exact ⟨ty', hcT, hannT, checked, sty, u, inferred, reduced⟩

end IxVM.Refinement.Typing
