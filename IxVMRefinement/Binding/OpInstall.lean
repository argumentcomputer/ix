import IxVMRefinement.Binding.Raise
import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.Assembly.TypingModel
import IxVMRefinement.Assembly.ValueUnitStep
import IxVMRefinement.StatementRel.ReadsMono
import IxVMRefinement.StatementRel.Inhabit

/-! # An operation's group in the binding fold: the install of the operation

After the closure of an operation's group `g` (its records other than the operation's own are
installed), the operation is installed at its role key with `RoleOps.op_step`, and the invariant
over the fold's clause moves from the groups below `g` to the state before the raise past `g`
(`BeforeRaise`): the public shape and the facts beside the clause on the groups up to `g`, the
clause at the limits within the groups below `g`, and what the raise past `g` needs.

`roleOp_step` is that step. Its inputs:

* the invariant below `g` at the store `R₁` and the environment `env₁` its closure left, and the
  admission of `g` (for the store clauses of `R'`, which is `R₁` and the operation's record,
  `AddsAt`);
* the operation's check at `env₁` (`RoleOps.OpChecked`), the stored terms annotating the record's
  reading (`Annotates`), and the reading itself;
* the record is a standalone definition (`hsolo`) at an address of 32 bytes, and the stored
  constant is the one every load of the record represents (`hreload`, `Decl.ReloadsAs`): a load
  of an address represents the canonical annotation of its record
  (`LoadedReads.get_ci_defn_canon`), and the load contract of the prefix invariant
  (`ScopedLoadFacts.getCI`) reads the constant stored at the address's key, so an arbitrary
  annotation (`Annotates` admits any binder data) would not do.

The clause is kept by the operation's own declaration step: an operation is a value constant at
the key of a 32-byte address, and its install record is the kernel's (`opChecked_run`), so
`FoldClauseWith.consValue` applies at every record store and every limit within the groups below
`g`, with the registry unchanged. The raise past the group is not taken here: the step hands the
fold what the raise needs (`RaiseAt`): the operation's companion below the well-founded block,
and at the block's last group every well-founded operation stored as pinned.

Also here: `recordsFor_exists` (a record store for every store that agrees with the committed
prelude rows: the merged store over no run) and the store transfers between `R₁` and `R'`
(`keptIn_up`, `reads_down`).
-/

universe u

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Binding.OpInstall

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## A record store exists -/

/-- **A record store for every store that agrees with the committed prelude rows**: the merged
store over the empty run (`Typing.merged_exists`), which hashes nothing and so hashes no
collision. -/
theorem recordsFor_exists {R : Ixon.Env} (hcomm : AgreesCommitted R) : ∃ E, RecordsFor R E := by
  obtain ⟨E, hM⟩ := merged_exists ({} : Ixon.Env) R
  have hnh : ∀ b, ¬ Hashed ([] : List (Call F)) b := by
    rintro b ⟨c, hc, -⟩
    cases hc
  have hnp : ∀ x b, ¬ IxVM.Refinement.View.Preimage ⟨{}, []⟩ x b := by
    rintro x b (⟨lc, hlc, -⟩ | hb | ⟨rb, hrb, -⟩ | ⟨tr, htr, -⟩)
    · have h' : ({} : Ixon.Env).consts.get? x = some lc := hlc
      rw [TableInhabit.emptyStore_consts] at h'
      cases h'
    · have h' : ({} : Ixon.Env).blobs.get? x = some b := hb
      rw [TableInhabit.emptyStore_blobs] at h'
      cases h'
    · have h' : ({} : Ixon.Env).roleBinding = some rb := hrb
      cases h'
    · cases htr
  refine ⟨E, hM.recordsFor (calls := []) (V := ⟨{}, []⟩) (extra := committedFootprint)
    ⟨fun a lc h => ?_, fun a b h => ?_⟩ (fun x lc h => ?_) hcomm (fun _ hx => hx) ?_⟩
  · rw [TableInhabit.emptyStore_consts] at h
    cases h
  · rw [TableInhabit.emptyStore_blobs] at h
    cases h
  · rw [TableInhabit.emptyStore_consts] at h
    cases h
  · rintro ((⟨x, held, bytes, -, hh, -⟩ | ⟨x, held, image, blk, cb, ms, -, hh, -⟩ |
        ⟨bytes, hpre | hh, -⟩) | ⟨x, held, bytes, -, hh, -⟩ |
        ⟨x, held, image, -, ⟨blk, cb, ms, hh, -⟩, -⟩)
    · exact hnh _ hh
    · exact hnh _ hh
    · exact hnp _ _ hpre
    · exact hnh _ hh
    · exact hnh _ hh
    · exact hnh _ hh

/-! ## The keying of a prefix context -/

/-- The keying of a prefix context does not read the limit. -/
theorem stored_κ_lim (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable)
    (lim lim' : Option Nat) :
    (Core.Ctx.stored ⟨E, env, t, lim⟩).κ = (Core.Ctx.stored ⟨E, env, t, lim'⟩).κ := rfl

/-! ## The environment after the operation -/

section Installed

variable {env : Ix.Kernel.Env .anon} {c : Core.KKey} {ty val : Core.KExpr}
  {hint : Ix.Kernel.ReducibilityHint}

theorem installed_find_ne {k : Core.KKey} (h : c ≠ k) :
    (RoleOps.installed env c ty val hint).find? k = env.find? k := by
  show (⟨(Ix.Kernel.ConstantInfo.defnInfo ⟨c, [], ty⟩ val hint) :: env.consts⟩ :
    Ix.Kernel.Env .anon).find? k = env.find? k
  rw [Ix.Kernel.Env.find?_cons]
  exact ite_eq_right h

theorem not_mem_names_of_find_none {k : Core.KKey} (h : env.find? k = none) :
    k ∉ env.consts.map (·.name) := by
  unfold Ix.Kernel.Env.find? at h
  intro hm
  obtain ⟨ci, hci, he⟩ := List.mem_map.mp hm
  have h' := List.find?_eq_none.mp h ci hci
  simp [he] at h'

end Installed

/-- **The kernel's install record of an operation**, from its check and its prefix, either
family. -/
theorem opChecked_run {env : Ix.Kernel.Env .anon} {c : Core.KKey} {ty₀ val₀ ty val : Core.KExpr}
    (hint : Ix.Kernel.ReducibilityHint) (hS : Ix.Kernel.Open.StoreInv env)
    (h : RoleOps.OpChecked env c ty₀ val₀ ty val) :
    Ix.Kernel.Semantics.DeclDefnRunJ Ix.Kernel.Model.rulesJ env ⟨c, [], ty₀⟩ val₀ hint
      (RoleOps.installed env c ty val hint) := by
  cases h with
  | struct hc hp hk => exact RoleOps.structOp_run hint hS hc hp hk
  | wf hc hp hk => exact RoleOps.wfOp_run hint hS hc hp hk

/-- **The prefix invariant after the operation**, at a limit where it held before: the
operation's install record keeps the declaration layer's invariant and its store part, and the
record reloads as the constant stored. -/
theorem prefixInv_installed {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role} {a : _root_.Address}
    {ty₀ val₀ ty val tyD valD : Core.KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (h : Decl.PrefixInv.{u} E t lim env) (ha : t.addressOf? r = some a)
    (hchk : RoleOps.OpChecked env (.role r) ty₀ val₀ ty val)
    (hty : Annotates ty tyD) (hval : Annotates val valD)
    (hreload : Decl.ReloadsAs E t (RoleOps.installed env (.role r) ty val hint)
      (.defnInfo ⟨.role r, [], ty⟩ val hint)) :
    Decl.PrefixInv.{u} E t lim (RoleOps.installed env (.role r) ty val hint) := by
  have hbase := RoleOps.isBaseKey_of_mem_opNames hchk.mem
  have hrun := opChecked_run hint h.store.store hchk
  exact h.cons_value (cn := .defnInfo ⟨.role r, [], ty⟩ val hint) (a₀ := a)
    (Core.keyOf_of_addressOf h.tableWf ha).symm hchk.opPrefix.fresh
    (fun _ => Decl.ne_projTableName_of_isBaseKey hbase) (fun _ _ e => nomatch e)
    (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e) (fun _ e => nomatch e)
    (RoleOps.op_step hint hchk hty hval).2.2.1
    (Decl.foldStoreInv_step_declRunJ (d := .defnDecl ⟨.role r, [], ty₀⟩ val₀ hint) h.store
      (fun _ _ heq => nomatch heq) hrun)
    hreload

/-! ## The store, one record later -/

section Store

variable {R₁ R' : Ixon.Env} {a : _root_.Address}

theorem recordOf_up (hs : AddsAt R₁ R' a) {x : _root_.Address} {c : Ixon.Constant}
    (h : recordOf R₁ x = some c) : recordOf R' x = some c := by
  unfold recordOf at h ⊢
  cases h₁ : R₁.consts.get? x with
  | none => rw [h₁] at h; cases h
  | some lc =>
    rw [h₁] at h
    rw [hs.1 x lc h₁]
    exact h

theorem consts_ne (hs : AddsAt R₁ R' a) {x : _root_.Address} (hne : x ≠ a) :
    R'.consts.get? x = R₁.consts.get? x := by
  cases h' : R'.consts.get? x with
  | none =>
    cases h₁ : R₁.consts.get? x with
    | none => rfl
    | some lc =>
      rw [hs.1 x lc h₁] at h'
      cases h'
  | some lc =>
    rcases hs.2.1 x lc h' with h₁ | rfl
    · rw [h₁]
    · exact absurd rfl hne

theorem recordOf_ne (hs : AddsAt R₁ R' a) {x : _root_.Address} (hne : x ≠ a) :
    recordOf R' x = recordOf R₁ x := by
  unfold recordOf
  rw [consts_ne hs hne]

theorem blobs_eq (hs : AddsAt R₁ R' a) :
    (fun x => R'.blobs.get? x) = (fun x => R₁.blobs.get? x) := by
  funext x
  cases h' : R'.blobs.get? x with
  | none =>
    cases h₁ : R₁.blobs.get? x with
    | none => rfl
    | some b =>
      have := (hs.2.2 x b).mpr h₁
      rw [h'] at this
      cases this
  | some b => exact ((hs.2.2 x b).mp h').symm

theorem recordsFor_down (hs : AddsAt R₁ R' a) {E : Ixon.Env} (h : RecordsFor R' E) :
    RecordsFor R₁ E :=
  ⟨h.1, fun x c hc => h.2.1 x c (recordOf_up hs hc),
    fun x b hb => h.2.2.1 x b ((hs.2.2 x b).mpr hb), h.2.2.2⟩

/-- **What a constant keeps of a record of `R₁` it keeps of the same record in `R'`.** -/
theorem keptIn_up (hs : AddsAt R₁ R' a) {t : Ix.Kernel.RoleTable} {x : _root_.Address}
    {ci : Ix.Kernel.ConstantInfo .anon}
    (h : KeptIn t (recordOf R₁) (fun y => R₁.blobs.get? y) x ci) :
    KeptIn t (recordOf R') (fun y => R'.blobs.get? y) x ci := by
  obtain ⟨hax, ci₀, hr, hst⟩ := h
  refine ⟨fun c ax hc hinfo => ?_, ci₀,
    ReadsIn.mono (fun y c hc => recordOf_up hs hc)
      (fun y b hb => (hs.2.2 y b).mpr hb) hr, hst⟩
  obtain ⟨c₀, hc₀, -⟩ := hr
  rw [recordOf_up hs hc₀] at hc
  have hcc : c₀ = c := Option.some.inj hc
  rw [← hcc] at hinfo
  exact hax c₀ ax hc₀ hinfo

end Store

/-! ## A reading that does not consult one address -/

section Back

open Ix.Kernel.Reader

variable {t : Ix.Kernel.RoleTable} {S S' : Store} {a : _root_.Address}

/-- `S'` is `S` but at `a`, where it holds no block and no inductive projection. -/
def AgreeBut (S S' : Store) (a : _root_.Address) : Prop :=
  (∀ y, y ≠ a → S' y = S y) ∧
    ∀ c, S' a = some c → (∀ ms, c.info ≠ .muts ms) ∧ ∀ p, c.info ≠ .iPrj p

theorem memberAt_back (hS : AgreeBut S S' a) {x : _root_.Address} {c : Ixon.Constant}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    {m : Ixon.MutConst} (h : MemberAt S' x c B cb ms i m) : MemberAt S x c B cb ms i m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hB : B ≠ a := by
    rintro rfl
    exact (hS.2 cb h1).1 ms h2
  unfold MemberAt
  exact ⟨by rw [← hS.1 B hB]; exact h1, h2, h3, h4, h5, h6⟩

theorem indKeyAt_back (hS : AgreeBut S S' a) {k : Ix.Kernel.Key .anon} {B : _root_.Address}
    {i : Nat} {ind : Ixon.Inductive} (h : IndKeyAt t S' k B i ind) : IndKeyAt t S k B i ind := by
  obtain ⟨x, c, p, cb, ms, h1, h2, h3, h4, h5, h6⟩ := h
  have hx : x ≠ a := by
    rintro rfl
    exact (hS.2 c h2).2 p h3
  unfold IndKeyAt
  exact ⟨x, c, p, cb, ms, h1, by rw [← hS.1 x hx]; exact h2, h3, h4, h5, memberAt_back hS h6⟩

theorem recReads_back (hS : AgreeBut S S' a) {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {name : Ix.Kernel.Key .anon} {rc : Ixon.Recursor} {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (h : RecReads t S' blob src self name rc ci₀) : RecReads t S blob src self name rc ci₀ := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10⟩ := h
  unfold RecReads
  exact ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, h1, h2, indKeyAt_back hS h3, h4,
    indKeyAt_back hS h5, h6, h7, h8, h9, h10⟩

/-- **A reading at another address than `a` does not read `a`'s record**, where that record is
no block and no inductive projection. -/
theorem readsIn_back (hS : AgreeBut S S' a) {blob : _root_.Address → Option ByteArray}
    {x : _root_.Address} (hx : x ≠ a) {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (h : ReadsIn t S' blob x ci₀) : ReadsIn t S blob x ci₀ := by
  obtain ⟨c, hc, h⟩ := h
  refine Exists.intro c (And.intro (by rw [← hS.1 x hx]; exact hc) ?_)
  generalize c.info = info at h ⊢
  cases info with
  | defn d => exact h
  | axio ax => exact h
  | quot q => exact h
  | recr rc =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (recReads_back hS h2)
  | dPrj p =>
    obtain ⟨cb, ms, d, hm, hr⟩ := h
    exact ⟨cb, ms, d, memberAt_back hS hm, hr⟩
  | iPrj p =>
    obtain ⟨cb, ms, ind, hm, hr⟩ := h
    exact ⟨cb, ms, ind, memberAt_back hS hm, hr⟩
  | cPrj p =>
    obtain ⟨cb, ms, ind, ct, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    have hB : p.block ≠ a := by
      rintro hB
      rw [hB] at h1
      exact (hS.2 cb h1).1 ms h2
    exact ⟨cb, ms, ind, ct, by rw [← hS.1 _ hB]; exact h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | rPrj p =>
    obtain ⟨cb, ms, rc, hm, hr⟩ := h
    exact ⟨cb, ms, rc, memberAt_back hS hm, recReads_back hS hr⟩
  | muts ms => exact h

end Back

/-- **A reading of `R'` at another address than the new record's is a reading of `R₁`**, the
new record being a standalone definition. -/
theorem reads_down {t : Ix.Kernel.RoleTable} {R₁ R' : Ixon.Env} {a : _root_.Address}
    (hs : AddsAt R₁ R' a) (hsolo : ∃ c d, recordOf R' a = some c ∧ c.info = .defn d)
    {x : _root_.Address} (hx : x ≠ a) {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (h : Reads t R' x ci₀) : Reads t R₁ x ci₀ := by
  obtain ⟨c₀, d₀, hc₀, hd₀⟩ := hsolo
  have hS : AgreeBut (recordOf R₁) (recordOf R') a := by
    refine ⟨fun y hy => recordOf_ne hs hy, fun c hc => ?_⟩
    rw [hc₀] at hc
    have hcc : c₀ = c := Option.some.inj hc
    rw [← hcc, hd₀]
    exact ⟨(fun ms e => nomatch e), (fun p e => nomatch e)⟩
  have h' := readsIn_back (blob := fun y => R'.blobs.get? y) hS hx h
  have hbl := blobs_eq hs
  unfold Reads
  rw [← hbl]
  exact h'

/-! ## Decided facts about the operation roles -/

set_option maxRecDepth 100000 in
private theorem roleGroup_groupOf_all :
    (List.range 77).all (fun g => (roleGroup g).all fun r => Ix.SpecDigest.groupOf r == g) =
      true := by
  decide +kernel

/-- **A role of group `g` is of group `g`.** -/
theorem groupOf_of_mem_roleGroup {g : Nat} {r : Ix.Kernel.Role} (h : r ∈ roleGroup g) :
    Ix.SpecDigest.groupOf r = g := by
  rcases Nat.lt_or_ge g Ix.SpecDigest.groups.length with hl | hge
  · have h1 := List.all_eq_true.mp roleGroup_groupOf_all g (List.mem_range.mpr hl)
    exact beq_iff_eq.mp (List.all_eq_true.mp h1 r h)
  · rw [roleGroup_eq_nil hge] at h
    cases h

set_option maxRecDepth 100000 in
private theorem op_groups_all : RoleOps.opRoles.all (fun r =>
    decide ((7 ≤ Ix.SpecDigest.groupOf r ∧ Ix.SpecDigest.groupOf r < 33) ∨
      (33 ≤ Ix.SpecDigest.groupOf r ∧ Ix.SpecDigest.groupOf r ≤ 40))) = true := by
  decide +kernel

/-- An operation's group is one of the structural groups (below the well-founded block) or of
the well-founded block. -/
theorem op_group {r : Ix.Kernel.Role} (h : r ∈ RoleOps.opRoles) :
    (7 ≤ Ix.SpecDigest.groupOf r ∧ Ix.SpecDigest.groupOf r < 33) ∨
      (33 ≤ Ix.SpecDigest.groupOf r ∧ Ix.SpecDigest.groupOf r ≤ 40) :=
  of_decide_eq_true (List.all_eq_true.mp op_groups_all r h)

set_option maxRecDepth 100000 in
private theorem op_walked_all : RoleOps.opRoles.all (fun r => walkedRole r) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem op_not_prelude : ∀ r ∈ RoleOps.opRoles, r ∉ preludeRoles := by
  decide +kernel

/-- An operation's constant is kept (its record is walked) and it is no prelude role. -/
theorem op_kept {r : Ix.Kernel.Role} (h : r ∈ RoleOps.opRoles) :
    keptRole r ∧ r ∉ preludeRoles :=
  ⟨Or.inl (Or.inl (List.all_eq_true.mp op_walked_all r h)), op_not_prelude r h⟩

set_option maxRecDepth 100000 in
/-- The well-founded operations are operations of the groups 33 to 40. -/
theorem wf_group : ∀ r ∈ wfOpRoles,
    (33 ≤ Ix.SpecDigest.groupOf r ∧ Ix.SpecDigest.groupOf r ≤ 40) ∧ r ∈ RoleOps.opRoles := by
  decide +kernel

/-- A role that is no operation is not the operation `r`. -/
theorem ne_of_not_op {r X : Ix.Kernel.Role} (hr : r ∈ RoleOps.opRoles)
    (hX : X ∉ RoleOps.opRoles) : (Ix.Kernel.Key.role r : Core.KKey) ≠ Ix.Kernel.Key.role X := by
  intro h
  have h' : r = X := Ix.Kernel.Key.role.inj h
  rw [h'] at hr
  exact hX hr

/-! ## The shapes, after the operation -/

/-- `stdAxiomOk` reads the environment at keys of roles that are no operation only. -/
theorem stdAxiomOk_congr {env env' : Ix.Kernel.Env .anon}
    (h : ∀ X : Ix.Kernel.Role, X ∉ RoleOps.opRoles →
      env'.find? (Ix.Kernel.Key.role X) = env.find? (Ix.Kernel.Key.role X))
    (cvA : Ix.Kernel.ConstantVal .anon) :
    Ix.Kernel.stdAxiomOk env' cvA = Ix.Kernel.stdAxiomOk env cvA := by
  have h1 : env'.find? Ix.Kernel.eqName = env.find? Ix.Kernel.eqName := h .eq (by decide)
  have h2 : env'.find? Ix.Kernel.iffName = env.find? Ix.Kernel.iffName := h .iff (by decide)
  have h3 : env'.find? Ix.Kernel.iffIntroName = env.find? Ix.Kernel.iffIntroName :=
    h .iffIntro (by decide)
  have h4 : env'.find? Ix.Kernel.iffRecName = env.find? Ix.Kernel.iffRecName :=
    h .iffRec (by decide)
  have h5 : env'.find? Ix.Kernel.nonemptyName = env.find? Ix.Kernel.nonemptyName :=
    h .nonempty (by decide)
  have h6 : env'.find? Ix.Kernel.nonemptyIntroName = env.find? Ix.Kernel.nonemptyIntroName :=
    h .nonemptyIntro (by decide)
  have h7 : env'.find? Ix.Kernel.nonemptyRecName = env.find? Ix.Kernel.nonemptyRecName :=
    h .nonemptyRec (by decide)
  unfold Ix.Kernel.stdAxiomOk
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- **The shapes on the groups below `g` are kept by the operation of group `g`, and extend to
`g`**, whose only role is the operation. -/
theorem shapes_installed {g : Nat} {r : Ix.Kernel.Role} {env : Ix.Kernel.Env .anon}
    {ty val : Core.KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (hgrp : roleGroup g = [r]) (hop : r ∈ RoleOps.opRoles)
    (hfresh : env.find? (Ix.Kernel.Key.role r) = none) (hs : Shapes (· < g) env) :
    Shapes (· < g + 1) (RoleOps.installed env (.role r) ty val hint) := by
  have hext := RoleOps.installed_ext hfresh (RoleOps.isBaseKey_of_mem_opNames
    (by rw [RoleOps.opNames_eq_map]; exact List.mem_map.mpr ⟨r, hop, rfl⟩)) ty val hint
  have hfr : ∀ X : Ix.Kernel.Role, X ∉ RoleOps.opRoles →
      (RoleOps.installed env (.role r) ty val hint).find? (Ix.Kernel.Key.role X) =
        env.find? (Ix.Kernel.Key.role X) :=
    fun X hX => installed_find_ne (ne_of_not_op hop hX)
  -- a shape role of group `g` would be the operation
  have hnot : ∀ X : Ix.Kernel.Role, X ∉ RoleOps.opRoles → Ix.SpecDigest.groupOf X ≠ g := by
    intro X hX hg
    have hm : X ∈ roleGroup g := hg ▸ role_mem_roleGroup X
    rw [hgrp, List.mem_singleton] at hm
    rw [hm] at hX
    exact hX hop
  have below : ∀ X : Ix.Kernel.Role, X ∉ RoleOps.opRoles →
      Ix.SpecDigest.groupOf X < g + 1 → Ix.SpecDigest.groupOf X < g := by
    intro X hX hor
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hor) with h | h
    · exact h
    · exact absurd h (hnot X hX)
  exact {
    bool := fun h => by
      obtain ⟨h1, h2, h3⟩ := hs.bool (below .bool (by decide) h)
      exact ⟨h1.mono hext, h2.mono hext, h3.mono hext⟩
    char := fun h => by
      have e : (RoleOps.installed env (.role r) ty val hint).find? Ix.Kernel.charName =
          env.find? Ix.Kernel.charName := hfr .char (by decide)
      rw [e]
      exact hs.char (below .char (by decide) h)
    string := fun h => by
      have e : (RoleOps.installed env (.role r) ty val hint).find? Ix.Kernel.stringName =
          env.find? Ix.Kernel.stringName := hfr .string (by decide)
      rw [e]
      exact hs.string (below .string (by decide) h)
    list := fun h => by
      have e1 : (RoleOps.installed env (.role r) ty val hint).find? Ix.Kernel.listName =
          env.find? Ix.Kernel.listName := hfr .list (by decide)
      have e2 : (RoleOps.installed env (.role r) ty val hint).find? Ix.Kernel.listNilName =
          env.find? Ix.Kernel.listNilName := hfr .listNil (by decide)
      have e3 : (RoleOps.installed env (.role r) ty val hint).find? Ix.Kernel.listConsName =
          env.find? Ix.Kernel.listConsName := hfr .listCons (by decide)
      rw [e1, e2, e3]
      exact hs.list (below .list (by decide) h)
    charOfNat := fun h => by
      have e : (RoleOps.installed env (.role r) ty val hint).find? Ix.Kernel.charOfNatName =
          env.find? Ix.Kernel.charOfNatName := hfr .charOfNat (by decide)
      rw [e]
      exact hs.charOfNat (below .charOfNat (by decide) h)
    stringOfList := fun h => by
      have e : (RoleOps.installed env (.role r) ty val hint).find? Ix.Kernel.stringOfListName =
          env.find? Ix.Kernel.stringOfListName := hfr .stringOfList (by decide)
      rw [e]
      exact hs.stringOfList (below .stringOfList (by decide) h)
    iff := fun h cvA hn hm => by
      rw [stdAxiomOk_congr hfr cvA]
      exact hs.iff (below .iff (by decide) h) cvA hn hm
    nonempty := fun h cvA hn hm => by
      rw [stdAxiomOk_congr hfr cvA]
      exact hs.nonempty (below .nonempty (by decide) h) cvA hn hm }

/-! ## The step -/

set_option maxHeartbeats 1600000 in
/-- **The operation's group, after its closure and before the raise past it**: from the
invariant below `g` at the closure's store and environment, the operation's check there, the
reading of its record and the reload of the stored constant, the invariant before the raise
past `g` at the store with the operation's record and the environment with the operation
installed. The clause is kept at the limits within the groups below `g` by the operation's own
declaration step (`FoldClauseWith.consValue`: a value constant at the key of a 32-byte
address). -/
theorem roleOp_step {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L)
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} {R R₁ R' : Ixon.Env}
    {env₁ : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role} {a : _root_.Address}
    {ty₀ val₀ ty val tyD valD : Core.KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (hall : AllBound t) (hgrp : roleGroup g = [r]) (hop : r ∈ RoleOps.opRoles)
    (ha : t.addressOf? r = some a) (hadm : Admits ρ t g R R')
    (hb : BndOver.{u} L t (· < g) R₁ env₁) (hadds : AddsAt R₁ R' a)
    (hchk : RoleOps.OpChecked env₁ (.role r) ty₀ val₀ ty val)
    (hty : Annotates ty tyD) (hval : Annotates val valD)
    (hreads : Reads t R' a (.defnInfo ⟨.role r, [], tyD⟩ valD hint))
    (hsolo : ∃ c d, recordOf R' a = some c ∧ c.info = .defn d)
    (hsize : a.hash.size = 32)
    (hreload : ∀ E, RecordsFor R' E →
      Decl.ReloadsAs E t (RoleOps.installed env₁ (.role r) ty val hint)
        (.defnInfo ⟨.role r, [], ty⟩ val hint)) :
    BeforeRaise.{u} L t g R' (RoleOps.installed env₁ (.role r) ty val hint) := by
  -- the group, the operation's key, the new constant
  have hrg : r ∈ roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := groupOf_of_mem_roleGroup hrg
  have hglt : g ≤ 40 := by
    rcases op_group hop with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hopN : (Ix.Kernel.Key.role r : Core.KKey) ∈ RoleOps.opNames := by
    rw [RoleOps.opNames_eq_map]
    exact List.mem_map.mpr ⟨r, hop, rfl⟩
  have hbase := RoleOps.isBaseKey_of_mem_opNames hopN
  have hfresh : env₁.find? (Ix.Kernel.Key.role r) = none := hchk.opPrefix.fresh
  have hext := RoleOps.installed_ext hfresh hbase ty val hint
  have hself := RoleOps.installed_find_self env₁ (.role r) ty val hint
  have hfind_ne : ∀ r' : Ix.Kernel.Role, r' ≠ r →
      (RoleOps.installed env₁ (.role r) ty val hint).find? (Ix.Kernel.Key.role r') =
        env₁.find? (Ix.Kernel.Key.role r') := by
    intro r' hne
    exact installed_find_ne (fun h => hne (Ix.Kernel.Key.role.inj h).symm)
  have hstep := RoleOps.op_step.{u} hint hchk hty hval
  have hpinI : RoleOps.OpsPinned (RoleOps.installed env₁ (.role r) ty val hint) :=
    hstep.2.2.2.1 hb.facts.opsPinned
  have htwf : t.wf = true := by
    obtain ⟨E, hE⟩ := recordsFor_exists hb.shape.committed
    exact (hb.inv hE (carried_valLimit g) (limWithin_below t g)).tableWf
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
  have hkey_role : ∀ x, keyOf t x = Ix.Kernel.Key.role r → x = a := by
    intro x hx
    have h1 := Core.addressOf_of_keyOf htwf hx
    rw [ha] at h1
    exact (Option.some.inj h1).symm
  -- the new record
  obtain ⟨cA, dA, hcA, hdA⟩ := hsolo
  have hkeptNew : KeptIn t (recordOf R') (fun x => R'.blobs.get? x) a
      (.defnInfo ⟨.role r, [], ty⟩ val hint) := by
    refine ⟨fun c ax hc hinfo => ?_, _, hreads, ⟨⟨rfl, rfl, hty⟩, hval, rfl⟩⟩
    rw [hcA] at hc
    have hcc : cA = c := Option.some.inj hc
    rw [← hcc, hdA] at hinfo
    cases hinfo
  -- the prefix invariant at the limits within the groups below `g`
  have hinvA : ∀ E, RecordsFor R' E → ∀ lim, Carried lim → LimWithin (· < g) t lim →
      Decl.PrefixInv.{u} E t lim (RoleOps.installed env₁ (.role r) ty val hint) :=
    fun E hE lim hc hw => prefixInv_installed
      (hb.inv (recordsFor_down hadds hE) hc hw) ha hchk hty hval (hreload E hE)
  -- the clause at those limits, by the operation's own declaration step
  have hclause : FoldClauseOver.{u} L t (· < g) R'
      (RoleOps.installed env₁ (.role r) ty val hint) := by
    obtain ⟨Reg, hR⟩ := hb.clause
    refine ⟨Reg, fun E hE lim hc hw => ?_⟩
    have h0 := hR E (recordsFor_down hadds hE) lim hc hw
    exact FoldClauseWith.consValue hL h0 (cn := .defnInfo ⟨.role r, [], ty⟩ val hint)
      (d₀ := .defnDecl ⟨.role r, [], ty₀⟩ val₀ hint) hfresh (Or.inl ⟨_, _, _, rfl⟩)
      (fun _ => Decl.ne_projTableName_of_isBaseKey hbase)
      (opChecked_run hint h0.store hchk) ⟨a, hkeya.symm, hsize⟩ (hinvA E hE lim hc hw)
  -- the reading of `R'`
  have hnodup : ((RoleOps.installed env₁ (.role r) ty val hint).consts.map (·.name)).Nodup :=
    List.nodup_cons.mpr ⟨not_mem_names_of_find_none hfresh, hb.shape.reading.nodup⟩
  have hprov : ∀ ci ∈ (claimedEnv (RoleOps.installed env₁ (.role r) ty val hint)).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ x, KeptIn t (recordOf R') (fun y => R'.blobs.get? y) x ci := by
    intro ci hci
    unfold claimedEnv at hci
    obtain ⟨hmem, hp⟩ := List.mem_filter.mp hci
    rcases List.mem_cons.mp hmem with rfl | hold
    · exact Or.inr (Or.inr ⟨a, hkeptNew⟩)
    · rcases hb.shape.reading.provenance ci (List.mem_filter.mpr ⟨hold, hp⟩) with
        h | h | ⟨x, hx⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨x, keptIn_up hadds hx⟩)
  have hreading : ReadingOf t R' (RoleOps.installed env₁ (.role r) ty val hint) := by
    refine ⟨hnodup, hprov, fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [hkeya]
      exact ⟨_, hself, Or.inr ⟨_, hreads, ⟨⟨rfl, rfl, hty⟩, hval, rfl⟩⟩⟩
    · obtain ⟨ci₀, hr₀⟩ := hx
      obtain ⟨ci, hci, hpin⟩ := hb.shape.reading.stored x ⟨ci₀, reads_down hadds
        ⟨cA, dA, hcA, hdA⟩ hxa hr₀⟩
      refine ⟨ci, hext.find hci, ?_⟩
      rcases hpin with hp | ⟨ci₁, hr₁, hst⟩
      · exact Or.inl hp
      · exact Or.inr ⟨ci₁, ReadsIn.mono (fun y c hc => recordOf_up hadds hc)
          (fun y b hb' => (hadds.2.2 y b).mpr hb') hr₁, hst⟩
  -- a kept role of a group below `g` is no operation of `g`'s
  have hkeep_old : ∀ (r' : Ix.Kernel.Role) (ci : Ix.Kernel.ConstantInfo .anon),
      env₁.find? (Ix.Kernel.Key.role r') = some ci →
        (RoleOps.installed env₁ (.role r) ty val hint).find? (Ix.Kernel.Key.role r') =
          some ci := fun r' ci hci => hext.find hci
  have hshape : TableShape.{u} t (· < g + 1) R'
      (RoleOps.installed env₁ (.role r) ty val hint) := {
    needsClosed := fun k hk r' hr' => by
      have h1 := groupNeeded_lt hr'
      have hk' : k < g + 1 := hk
      show Ix.SpecDigest.groupOf r' < g + 1
      omega
    bound := fun k _ r' _ => hall r'
    prelude := hb.shape.prelude
    literals := hb.shape.literals
    hashed := hadm.hashed
    usedClosed := hadm.usedClosed
    committed := hadm.committed
    zeroFree := hadm.zeroFree
    kept := fun k r' a' hk hr' hkr ha' => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · obtain ⟨ci, hci, hpin⟩ := hb.shape.kept k r' a' hk hr' hkr ha'
        refine ⟨ci, hkeep_old r' ci hci, ?_⟩
        rcases hpin with hp | hp
        · exact Or.inl hp
        · exact Or.inr (keptIn_up hadds hp)
      · rw [hgrp, List.mem_singleton] at hr'
        subst hr'
        rw [ha] at ha'
        obtain rfl := Option.some.inj ha'
        exact ⟨_, hself, Or.inr hkeptNew⟩
    reading := hreading
    pins := fun kind ci hci => List.mem_cons_of_mem _ (hb.shape.pins kind ci hci)
    preludeKept := fun k r' a' hk hr' hpr ha' => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · obtain ⟨ci, hci, hpin⟩ := hb.shape.preludeKept k r' a' hk hr' hpr ha'
        refine ⟨ci, hkeep_old r' ci hci, ?_⟩
        rcases hpin with hp | hp
        · exact Or.inl hp
        · exact Or.inr (keptIn_up hadds hp)
      · rw [hgrp, List.mem_singleton] at hr'
        subst hr'
        exact absurd hpr (op_kept hop).2
    model := by
      obtain ⟨E, hE⟩ := recordsFor_exists hadm.committed
      exact claimedEnv_models_of_prefixInv
        (hinvA E hE (some (valLimit g)) (carried_valLimit g) (limWithin_below t g)) hnodup
        hprov }
  have hfacts : BoundaryFacts t (· < g + 1) R'
      (RoleOps.installed env₁ (.role r) ty val hint) := {
    whole := fun E hE x B c cb ms hfx hrec hown hne hrecB hmuts => by
      by_cases hk : keyOf t x = Ix.Kernel.Key.role r
      · have hx := hkey_role x hk
        subst hx
        have hrA : Ix.Cert.recordAt E x = some cA := hE.2.1 x cA hcA
        rw [hrA] at hrec
        have hcc : cA = c := Option.some.inj hrec
        subst hcc
        have hown' : Ix.Cert.ownerOf x cA = x := by
          unfold Ix.Cert.ownerOf
          rw [hdA]
        exact absurd (hown.symm.trans hown') hne
      · have e : (RoleOps.installed env₁ (.role r) ty val hint).find? (keyOf t x) =
            env₁.find? (keyOf t x) := installed_find_ne (fun h => hk h.symm)
        have hfx' : (env₁.find? (keyOf t x)).isSome = true := by
          rw [← e]
          exact hfx
        have hbs := hb.facts.whole E (recordsFor_down hadds hE) x B c cb ms hfx' hrec hown hne
          hrecB hmuts
        intro i m hm
        obtain ⟨h1, h2⟩ := hbs i m hm
        refine ⟨?_, fun ind j hind hj => ?_⟩
        · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h1
          rw [hext.find hci]
          rfl
        · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (h2 ind j hind hj)
          rw [hext.find hci]
          rfl
    opsPinned := hpinI
    opsAdmitted := fun r'' hr'' hs => by
      show Ix.SpecDigest.groupOf r'' < g + 1
      by_cases hrr : r'' = r
      · rw [hrr, hgr]
        exact Nat.lt_succ_self g
      · rw [hfind_ne r'' hrr] at hs
        have h1 : Ix.SpecDigest.groupOf r'' < g := hb.facts.opsAdmitted r'' hr'' hs
        exact Nat.lt_succ_of_lt h1
    shapes := shapes_installed hgrp hop hfresh hb.facts.shapes }
  -- what the raise past `g` needs: the operation's companion below the well-founded block, the
  -- well-founded operations stored as pinned at the block's last group
  have hraise : RaiseAt t (RoleOps.installed env₁ (.role r) ty val hint) g := {
    succ := fun _ r'' hr'' _ => by
      rw [hgrp, List.mem_singleton] at hr''
      subst hr''
      refine ⟨Or.inl (RoleOps.op_companion hint hchk), fun _ a' ha' => ?_⟩
      rw [ha] at ha'
      obtain rfl := Option.some.inj ha'
      rw [Core.keyOf_of_addressOf htwf ha]
      exact ⟨_, hself⟩
    wf := fun hg40 r'' hr'' hbd => by
      subst hg40
      obtain ⟨⟨hg1, hg2⟩, hop''⟩ := wf_group r'' hr''
      have hopN'' : (Ix.Kernel.Key.role r'' : Core.KKey) ∈ RoleOps.opNames := by
        rw [RoleOps.opNames_eq_map]
        exact List.mem_map.mpr ⟨r'', hop'', rfl⟩
      refine hpinI _ hopN'' ?_
      by_cases hrr : r'' = r
      · subst hrr
        rw [hself]
        rfl
      · have hlt'' : Ix.SpecDigest.groupOf r'' < 40 := by
          rcases Nat.lt_or_ge (Ix.SpecDigest.groupOf r'') 40 with h | h
          · exact h
          · have he : Ix.SpecDigest.groupOf r'' = 40 := by omega
            have hm : r'' ∈ roleGroup 40 := he ▸ role_mem_roleGroup r''
            rw [hgrp, List.mem_singleton] at hm
            exact absurd hm hrr
        obtain ⟨a'', ha''⟩ := Option.isSome_iff_exists.mp hbd
        obtain ⟨ci, hci, -⟩ := hb.shape.kept _ r'' a'' hlt'' (role_mem_roleGroup r'')
          (op_kept hop'').1 ha''
        rw [hfind_ne r'' hrr, hci]
        rfl
    literal := fun h45 => absurd h45 (by omega) }
  exact ⟨hshape, hclause, hfacts, hraise⟩

end IxVM.Refinement.Binding.OpInstall
