import IxVMRefinement.Decl.Common
import IxVMRefinement.Core.Roles
import IxVMRefinement.Obs.KernelCheck
import IxVMRefinement.Obs.KernelRoles
import IxVMRefinement.Obs.KernelRoleSpec

/-! # Value, Axiom, Opaque, Theorem, Quotient, and Basis Declarations

Refinement of `KernelCheck::check_const` and its role/standing helpers for standalone value,
axiom, theorem, opaque, quotient, and pinned-basis declarations against `DeclRunJ rulesJ`,
`InstallStep`, `ThmVal`, and `DeclInv`.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (ConstantInfo ConstantVal Declaration RecRule BasisKind LevelParam Level Expr)
open Ix.Kernel.Rules (Annot Infer DefEq Red)
open Ix.Kernel.Semantics (ConstantValRunJ ValueFrontRunJ DeclDefnRunJ DeclThmRunJ
  DeclOpaqueRunJ DeclAxiomRunJ DeclBasisRun DeclRunJ IndRoutesJ)
open Ix.Kernel.Model (rulesJ EnvModelT EnvModelOk)

universe u

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## `ThmVal` extraction from `DeclInv` -/

/-- Every `DeclInv V env` witnesses an `EnvModel V env` satisfying `IxVM.Consistency.ThmVal`:
stored theorem values are annotated, so `ThmValOk` reads each stored theorem's value directly to
its leaf in `mp.base2.acval`, which is `WellDenoted` and `AnnotValid` (`WellDenotedV`). -/
theorem DeclInv.exists_envModel_thmVal {V : Type u} [Ix.Kernel.SetTheory V]
    {env : Ix.Kernel.Env .anon} (hinv : DeclInv V env) :
    ∃ m : Ix.Kernel.Model.EnvModel V env, IxVM.Consistency.ThmVal m := by
  obtain ⟨⟨mp, hthm⟩, -⟩ := hinv.model
  refine ⟨mp.base2, fun ψ cv value hmem => ?_⟩
  refine ⟨mp.base2.acval cv.name ψ, hthm.reads ψ cv value hmem, ?_, fun _ => rfl⟩
  intro ρ
  exact ⟨mp.base2.acval_wellDenoted cv.name ψ ρ, mp.acval_validV cv.name ψ ρ⟩

/-! ## Context, key, and `LevelParam.nodup` helpers -/

/-- Changing only the group limit `lim` of a `Ctx` preserves `LoadFacts`, since no field of
`LoadFacts` reads `c.lim`. -/
theorem LoadFacts.withLim {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {t : Ix.Kernel.RoleTable} {lim₁ lim₂ : Option Nat}
    (h : LoadFacts ⟨E, env, t, lim₁⟩) : LoadFacts ⟨E, env, t, lim₂⟩ where
  getCI := h.getCI
  getCprj := h.getCprj
  getIprj := h.getIprj
  indRecord := h.indRecord
  inductRecord := h.inductRecord
  projTables := h.projTables
  projTablesAt := h.projTablesAt
  unitLike := h.unitLike
  eta := h.eta
  etaIota := h.etaIota
  canonical := h.canonical

/-- Keys assigned by `keyOf` are `.role` or `.id`, never projection-function/table `.aux` keys. -/
theorem keyOf_isProjFnShape_false (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    (keyOf t a).isProjFnShape = false := by
  unfold keyOf
  split <;> rfl

/-- Keys assigned by `keyOf` are never `.aux`. -/
theorem keyOf_ne_aux (t : Ix.Kernel.RoleTable) (a : _root_.Address) (k : KKey)
    (d : Ix.Kernel.Derived) : keyOf t a ≠ .aux k d := by
  unfold keyOf
  split <;> intro h <;> cases h

/-- `List.Nodup` implies `Ix.Kernel.LevelParam.nodup = true`. -/
theorem levelParam_nodup_of_nodup :
    ∀ {ps : List LevelParam}, ps.Nodup → Ix.Kernel.LevelParam.nodup ps = true
  | [], _ => rfl
  | p :: ps, h => by
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp h
    simp only [Ix.Kernel.LevelParam.nodup, Bool.and_eq_true]
    refine ⟨?_, levelParam_nodup_of_nodup hnd⟩
    cases hc : ps.contains p with
    | false => rfl
    | true => exact absurd (List.mem_of_elem_eq_true hc) hnot

/-- `cv.levelParams.Perm (List.range n)` implies `LevelParam.nodup cv.levelParams = true`. -/
theorem levelParam_nodup_of_perm_range {ps : List LevelParam} {n : Nat}
    (hperm : ps.Perm (List.range n)) : Ix.Kernel.LevelParam.nodup ps = true :=
  levelParam_nodup_of_nodup (hperm.nodup_iff.mpr List.nodup_range)

/-! ## Safety tag and `KernelCheck::is_unsafe_ci` -/

/-- The loaded `KConstantInfo` value carries the safe tag/flag (`Ixon::DefinitionSafety::Safe`
on `Defn`, `.field 0` on `Axiom`/`Opaque`/`Induct`/`Ctor`/`Rec`), as holds of every constant in
Lean's logic (`IxVM.Consistency.InLogic`). -/
def CISafe : SourceValue F → Prop
  | .construct en "Axiom" [_, _, u] => en = kciEnum → u = .field 0
  | .construct en "Defn" [_, _, _, s, _] =>
    en = kciEnum → s = .construct "Ixon::DefinitionSafety" "Safe" []
  | .construct en "Opaque" [_, _, _, u] => en = kciEnum → u = .field 0
  | .construct en "Induct" [_, _, _, _, _, u, _, _] => en = kciEnum → u = .field 0
  | .construct en "Ctor" [_, _, _, _, _, _, _, u] => en = kciEnum → u = .field 0
  | .construct en "Rec" [_, _, _, _, _, _, _, _, u, _, _] => en = kciEnum → u = .field 0
  | _ => True

/-- `KernelCheck::is_unsafe_ci` answers `.field 0` on any safe `KConstantInfo` value without
modifying the heap or making calls. -/
theorem is_unsafe_ci_zero {v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::is_unsafe_ci" [v] h r h' cs) (hsafe : CISafe v) :
    r = .field 0 ∧ h' = h ∧ cs = [] := by
  cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
  | Axiom _ _ _ hv hr hh hc =>
    subst hv; exact ⟨hr.trans (hsafe rfl), hh, hc⟩
  | Defn_Safe _ _ _ _ _ _ hr hh hc =>
    exact ⟨hr, hh, hc⟩
  | Defn_other _ _ _ x_s _ _ hv hne _ _ _ =>
    subst hv; exact absurd (hsafe rfl) (hne [] rfl)
  | Thm _ _ _ _ _ _ hr hh hc =>
    exact ⟨hr, hh, hc⟩
  | Opaque _ _ _ _ _ _ _ hv hr hh hc =>
    subst hv; exact ⟨hr.trans (hsafe rfl), hh, hc⟩
  | Quot _ _ _ _ _ _ _ _ hr hh hc =>
    exact ⟨hr, hh, hc⟩
  | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv hr hh hc =>
    subst hv; exact ⟨hr.trans (hsafe rfl), hh, hc⟩
  | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv hr hh hc =>
    subst hv; exact ⟨hr.trans (hsafe rfl), hh, hc⟩
  | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv hr hh hc =>
    subst hv; exact ⟨hr.trans (hsafe rfl), hh, hc⟩

/-! ## Role-context, standing, and quotient specs -/

/-- The role-lookup family specifications (`Core.Specs.Roles.Fn.spec`). -/
def RolesSpec : Prop :=
  ∀ (c : Ctx) (f : Specs.Roles.Fn) (args : List (SourceValue F)) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) (calls : List (Call F)),
    ObsFn W f.name args h r h' calls → f.spec c args h r h' calls

/-- A role context whose user-axiom tree is empty (`Nil`), as built by `verify_claim` when the
claim allows no uncertified user axioms. -/
def RCAxiomsNil (h : Heap F) (rc : SourceValue F) : Prop :=
  ∃ node, loadValue h rc = .ok node ∧
    ((∃ tbl lim, node = .construct rcEnum "Mk" [tbl, lim, .construct addrMapEnum "Nil" []]) ∨
      ∃ tbl, node = .construct rcEnum "Assumed" [tbl, .construct addrMapEnum "Nil" []])

theorem RCAxiomsNil.mono {h₁ h₂ : Heap F} {rc : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (hrc : RCAxiomsNil h₁ rc) : RCAxiomsNil h₂ rc := by
  obtain ⟨node, hl, hshape⟩ := hrc
  exact ⟨node, ext.loadValue_eq hl, hshape⟩

/-- Direct proof of `KernelRoles::role_ctx_table` from its observed paths. -/
theorem role_ctx_table_spec {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {rc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : RCRep t lim h rc)
    (ev : ObsFn W "KernelRoles::role_ctx_table" [rc] h r h' cs) :
    h' = h ∧ TableRep t h r ∧ cs = [] := by
  obtain ⟨tbl, ax, node, hl, hn, htbl⟩ := hrc
  cases Obs.«KernelRoles::role_ctx_table».obs ev with
  | Mk x_t w20 w21 ld hr hh hc =>
    rw [hl] at ld
    rcases hn with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
    · injection ld with hnode
      injection hnode with _ _ hargs
      injection hargs with htbl_eq _
      exact ⟨hh, hr ▸ htbl_eq ▸ htbl, hc⟩
    · injection ld with hnode
      injection hnode with _ htag _
      exact absurd htag (by decide)
  | Assumed x_t w48 ld hr hh hc =>
    rw [hl] at ld
    rcases hn with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
    · injection ld with hnode
      injection hnode with _ htag _
      exact absurd htag (by decide)
    · injection ld with hnode
      injection hnode with _ _ hargs
      injection hargs with htbl_eq _
      exact ⟨hh, hr ▸ htbl_eq ▸ htbl, hc⟩

/-- Direct proof of `KernelRoles::role_addr_index` from its observed path. -/
theorem role_addr_index_spec {t : Ix.Kernel.RoleTable} {tbl r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h tbl)
    (ev : ObsFn W "KernelRoles::role_addr_index" [tbl] h r h' cs) :
    h' = h ∧ AddrMapAll addrMapEnum (IndexEntry t) h r ∧ cs = [] := by
  obtain ⟨bp, byRole, byAddr, evm, hl, -, hidx, -⟩ := htbl
  cases Obs.«KernelRoles::role_addr_index».obs ev with
  | run w20 w21 x_by_addr w22 ld hr hh hc =>
    rw [hl] at ld
    injection ld with hmk
    injection hmk with _ _ hargs
    injection hargs with _ h1
    injection h1 with _ h2
    injection h2 with hba _
    exact ⟨hh, hr ▸ hba ▸ hidx, hc⟩

/-- Direct proof of `KernelRoles::role_ctx_axioms` on a role context with empty user-axiom map. -/
theorem role_ctx_axioms_nil {rc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnil : RCAxiomsNil h rc)
    (ev : ObsFn W "KernelRoles::role_ctx_axioms" [rc] h r h' cs) :
    r = .construct addrMapEnum "Nil" [] ∧ h' = h ∧ cs = [] := by
  obtain ⟨node, hl, hshape⟩ := hnil
  cases Obs.«KernelRoles::role_ctx_axioms».obs ev with
  | Mk w20 w21 x_ax ld hr hh hc =>
    rw [hl] at ld
    rcases hshape with ⟨tbl, lim, rfl⟩ | ⟨tbl, rfl⟩
    · injection ld with hnode
      injection hnode with _ _ hargs
      injection hargs with _ h1
      injection h1 with _ h2
      injection h2 with hax _
      exact ⟨hr.trans hax.symm, hh, hc⟩
    · injection ld with hnode
      injection hnode with _ htag _
      exact absurd htag (by decide)
  | Assumed w48 x_ax ld hr hh hc =>
    rw [hl] at ld
    rcases hshape with ⟨tbl, lim, rfl⟩ | ⟨tbl, rfl⟩
    · injection ld with hnode
      injection hnode with _ htag _
      exact absurd htag (by decide)
    · injection ld with hnode
      injection hnode with _ _ hargs
      injection hargs with _ h1
      injection h1 with hax _
      exact ⟨hr.trans hax.symm, hh, hc⟩

private theorem role_idx_of_roleNum_eq {ro : Ix.Kernel.Role} {k : Nat} (hk : k < 200)
    (h : roleNum ro = (k : F)) : ro.idx = k := by
  have hro : ro.idx < 200 := by cases ro <;> decide
  have hv := congrArg ZMod.val h
  have h1 : ((ro.idx : F)).val = ro.idx :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hro (by decide))
  have h2 : ((k : F)).val = k :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hk (by decide))
  change ((ro.idx : F)).val = ((k : F)).val at hv
  rwa [h1, h2] at hv

private theorem evalBinOp_sub_field (a b : F) {v : SourceValue F}
    (hop : evalBinOp .sub (.field a) (.field b) = .ok v) : v = .field (a - b) := by
  simp only [evalBinOp, Except.ok.injEq] at hop
  exact hop.symm

private theorem evalBinOp_sub_eq_zero_inv {x : SourceValue F} {b : F}
    (hop : evalBinOp .sub x (.field b) = .ok (.field 0)) : x = .field b := by
  cases x with
  | field a =>
    simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at hop
    exact congrArg Value.field (sub_eq_zero.mp hop)
  | _ =>
    simp [evalBinOp] at hop

/-- `KernelRoleSpec::role_spec_kind` answers `.field 4` only on inert roles (`sorryAx`,
`trustCompiler`, `ofReduceBool`, `ofReduceNat`). -/
theorem role_spec_kind_four_inert {ro : Ix.Kernel.Role} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::role_spec_kind" [.field (roleNum ro)] h (.field 4) h' cs) :
    ro.inert = true := by
  have p := Obs.«KernelRoleSpec::role_spec_kind».obs ev
  cases p with
  | n58 hv _ _ _ =>
    injection hv with hf
    have hi : ro.idx = 58 := role_idx_of_roleNum_eq (by decide) hf
    cases ro <;> first | exact absurd hi (by decide) | rfl
  | n103 hv _ _ _ =>
    injection hv with hf
    have hi : ro.idx = 103 := role_idx_of_roleNum_eq (by decide) hf
    cases ro <;> first | exact absurd hi (by decide) | rfl
  | n106 hv _ _ _ =>
    injection hv with hf
    have hi : ro.idx = 106 := role_idx_of_roleNum_eq (by decide) hf
    cases ro <;> first | exact absurd hi (by decide) | rfl
  | n107 hv _ _ _ =>
    injection hv with hf
    have hi : ro.idx = 107 := role_idx_of_roleNum_eq (by decide) hf
    cases ro <;> first | exact absurd hi (by decide) | rfl
  | _ =>
    exfalso
    rename_i he _ _
    injection he with hf
    have hv := congrArg ZMod.val hf
    change 4 = ZMod.val _ at hv
    first
    | (change 4 = ZMod.val ((0 : Nat) : F) at hv; rw [ZMod.val_natCast_of_lt (by decide)] at hv; omega)
    | (change 4 = ZMod.val ((1 : Nat) : F) at hv; rw [ZMod.val_natCast_of_lt (by decide)] at hv; omega)
    | (change 4 = ZMod.val ((2 : Nat) : F) at hv; rw [ZMod.val_natCast_of_lt (by decide)] at hv; omega)
    | (change 4 = ZMod.val ((3 : Nat) : F) at hv; rw [ZMod.val_natCast_of_lt (by decide)] at hv; omega)
    | (change 4 = ZMod.val ((5 : Nat) : F) at hv; rw [ZMod.val_natCast_of_lt (by decide)] at hv; omega)

/-- `KernelRoles::axiom_role_standing` answers nonzero at `roleNum ro + 1` only when `ro` is
`propext`, `choice`, `quotSound`, or an inert axiom role. -/
theorem axiom_role_standing_spec {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::axiom_role_standing" [.field (roleNum ro + 1)] h r h' cs)
    (hne : r ≠ .field 0) :
    ro = .propext ∨ ro = .choice ∨ ro = .quotSound ∨ ro.inert = true := by
  cases Obs.«KernelRoles::axiom_role_standing».obs ev with
  | n0 _ hr _ _ => exact absurd hr hne
  | other_n0 v22 m40 y49 cs60 _ op37 ev62 op55 _ _ _ =>
    have hv22 : v22 = .field (roleNum ro) := by
      rw [evalBinOp_sub_field _ _ op37, add_sub_cancel_right]
    obtain ⟨hy, _, _⟩ := Obs.«KernelRoleSpec::role_propext».obs ev62
    rw [hv22, hy] at op55
    have heq := evalBinOp_sub_eq_zero_inv op55
    injection heq with hf
    have hi : ro.idx = 56 := role_idx_of_roleNum_eq (by decide) hf
    left
    cases ro <;> first | exact absurd hi (by decide) | rfl
  | other_other_n0 v22 v39 m40 y49 cs60 m75 y84 cs95 _ op37 _ _ _ ev97 op90 _ _ _ =>
    have hv22 : v22 = .field (roleNum ro) := by
      rw [evalBinOp_sub_field _ _ op37, add_sub_cancel_right]
    obtain ⟨hy, _, _⟩ := Obs.«KernelRoleSpec::role_choice».obs ev97
    rw [hv22, hy] at op90
    have heq := evalBinOp_sub_eq_zero_inv op90
    injection heq with hf
    have hi : ro.idx = 57 := role_idx_of_roleNum_eq (by decide) hf
    right; left
    cases ro <;> first | exact absurd hi (by decide) | rfl
  | other_other_other_n0 v22 v39 m40 y49 cs60 v74 m75 y84 cs95 m110 y119 cs130
      _ op37 _ _ _ _ _ _ ev132 op125 _ _ _ =>
    have hv22 : v22 = .field (roleNum ro) := by
      rw [evalBinOp_sub_field _ _ op37, add_sub_cancel_right]
    obtain ⟨hy, _, _⟩ := Obs.«KernelRoleSpec::role_quot_sound».obs ev132
    rw [hv22, hy] at op125
    have heq := evalBinOp_sub_eq_zero_inv op125
    injection heq with hf
    have hi : ro.idx = 36 := role_idx_of_roleNum_eq (by decide) hf
    right; right; left
    cases ro <;> first | exact absurd hi (by decide) | rfl
  | other_other_other_other_n0 v22 v39 m40 y49 cs60 v74 m75 y84 cs95 v109 m110 y119 cs130
      x153 m155 cs164 _ op37 _ _ _ _ _ _ _ _ _ ev166 op160 _ _ _ =>
    have hv22 : v22 = .field (roleNum ro) := by
      rw [evalBinOp_sub_field _ _ op37, add_sub_cancel_right]
    have hx153 : x153 = .field 4 := evalBinOp_sub_eq_zero_inv op160
    rw [hv22, hx153] at ev166
    exact Or.inr (Or.inr (Or.inr (role_spec_kind_four_inert ev166)))
  | other_other_other_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hr _ _ =>
    exact absurd hr hne

/-- `KernelRoles::axiom_standing` answers nonzero under a context with no user axioms only when
the address is bound to an in-force role among `propext`, `choice`, `quotSound`, or an inert
role. -/
theorem axiom_standing_spec {c : Ctx} {rc ap r : SourceValue F} {a : Bytes.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hroles : RolesSpec) (hgood : Good c calls) (hwf : c.t.wf = true)
    (hrc : RCRep c.t c.lim h rc) (hnil : RCAxiomsNil h rc)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn W "KernelRoles::axiom_standing" [rc, ap] h r h' calls)
    (hne : r ≠ .field 0) :
    ∃ ro : Ix.Kernel.Role,
      c.t.addressOf? ro = some (ixAddr a) ∧ c.inForce ro ∧
      (ro = .propext ∨ ro = .choice ∨ ro = .quotSound ∨ ro.inert = true) := by
  cases Obs.«KernelRoles::axiom_standing».obs ev with
  | n0 v1 m2 cs12 m24 cs34 v38 m48 cs56 cs90 v94 m104 cs112 ev14 ev58 ev36 ev114 ev92 _ =>
    obtain ⟨hm2, htbl, _⟩ := role_ctx_table_spec hrc ev14
    rw [hm2] at ev58
    obtain ⟨hm48, _, _⟩ := role_addr_index_spec htbl ev58
    rw [hm48] at ev36
    have e36 := ObsFn.heap_extends ev36
    obtain ⟨hv94, hm104, _⟩ := role_ctx_axioms_nil (hnil.mono e36) ev114
    rw [hv94, hm104] at ev92
    have hlkp : Specs.Roles.rbtree_map_lookup_or_default_field c
        [ap, .construct addrMapEnum "Nil" [], .field 0] m24 r h' cs90 :=
      hroles c .rbtree_map_lookup_or_default_field _ _ _ _ _ ev92
    rcases hlkp ap _ (.field 0) rfl a (Bytes.repAddressRef_heapMono₂ addrTy e36 ha)
        (fun _ _ _ => False) .nil with hr | hfalse
    · exact absurd hr hne
    · exact hfalse.elim
  | other_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
    exact absurd hr hne
  | other_other_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
    exact absurd hr hne
  | other_other_other v1 m2 cs12 v23 m24 cs34 v38 m48 cs56 v134 m135 cs145 v177 m178 cs189
      ev14 ev58 ev36 hne130 ev147 hne173 ev191 hne215 _ _ hc222 =>
    subst hc222
    obtain ⟨hm2, htbl, _⟩ := role_ctx_table_spec hrc ev14
    rw [hm2] at ev58
    obtain ⟨hm48, hidx, _⟩ := role_addr_index_spec htbl ev58
    rw [hm48] at ev36
    have hlkp_fn : Specs.Roles.rbtree_map_lookup_or_default_field c
        [ap, v38, .field 0] h v23 m24 cs34 :=
      hroles c .rbtree_map_lookup_or_default_field _ _ _ _ _ ev36
    rcases hlkp_fn ap v38 (.field 0) rfl a ha (IndexEntry c.t) hidx with hv23 | ⟨ro, hv23, hro_addr⟩
    · exact absurd hv23 hne130
    · rw [hv23] at ev147
      have hstand := axiom_role_standing_spec ev147 hne173
      have e_pre := (ObsFn.heap_extends ev36).trans (ObsFn.heap_extends ev147)
      have hof_fn : Specs.Roles.role_of c [rc, ap] m135 v177 m178 cs189 :=
        hroles c .role_of _ _ _ _ _ ev191
      rcases hof_fn rc ap a rfl (hgood.sub fun x hx => by simp [hx]) (hrc.mono e_pre)
          (Bytes.repAddressRef_heapMono₂ addrTy e_pre ha) with hv177 | ⟨ro', _, hro'_addr, hin⟩
      · exact absurd hv177 hne215
      · have hk1 : keyOf c.t (ixAddr a) = .role ro := keyOf_of_addressOf hwf hro_addr
        have hk2 : keyOf c.t (ixAddr a) = .role ro' := keyOf_of_addressOf hwf hro'_addr
        have hro_eq : ro = ro' := by
          have := hk1.symm.trans hk2
          injection this
        subst hro_eq
        exact ⟨ro, hro_addr, hin, hstand⟩

/-- `KernelCheck::check_quot` on `QuotKind::Typ` certifies that `self_addr` is bound to `.quot`
with both `.quot` and its dependency `.eq` in force. -/
theorem check_quot_typ_spec {c : Ctx} {rc ap r : SourceValue F} {a : Bytes.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hroles : RolesSpec) (hgood : Good c calls) (hwf : c.t.wf = true)
    (hrc : RCRep c.t c.lim h rc) (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn W "KernelCheck::check_quot"
      [rc, ap, .construct "Ixon::QuotKind" "Typ" []] h r h' calls) :
    c.t.addressOf? .quot = some (ixAddr a) ∧ c.inForce .quot ∧ c.inForce .eq := by
  obtain ⟨v67, m68, cs70, v87, m90, cs98, sg75, ev100, heq131, _, _, hc136⟩ :=
    Obs.«KernelCheck::check_quot».obs ev
  subst hc136 heq131
  rcases sg75 with
    ⟨cs20, _, ev22, _⟩ |
    ⟨_, hne24, _, _, _⟩ |
    ⟨_, hne24, _, _, _, _⟩ |
    ⟨_, hne24, _, _, _, _, _⟩
  · obtain ⟨hv67, hm68, _⟩ := Obs.«KernelRoleSpec::role_quot».obs ev22
    rw [hv67, hm68] at ev100
    have hnum : (32 : F) = roleNum .quot := rfl
    rw [hnum] at ev100
    have his_fn : Specs.Roles.role_is c [rc, ap, .field (roleNum .quot)] h (.field 1) m90 cs98 :=
      hroles c .role_is _ _ _ _ _ ev100
    have his := his_fn rc ap a .quot rfl (hgood.sub fun x hx => by simp [hx]) hrc ha (by
      intro h0; injection h0 with hf; exact one_ne_zero hf)
    exact ⟨his.1, his.2,
      Ctx.inForce_of_block_or_dep hwf his.2 (.inr (by decide : .eq ∈ Ix.Kernel.Role.deps .quot))⟩
  · exact absurd rfl (hne24 [] rfl)
  · exact absurd rfl (hne24 [] rfl)
  · exact absurd rfl (hne24 [] rfl)

/-! ## Path-extraction lemmas for `KernelCheck::check_const` -/

/-- Inversion of `KernelCheck::check_const` on a safe `"Axiom"` constant. -/
theorem check_const_axiom_inv {rc nl ty ap r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Axiom" [nl, ty, .field 0], ap] h r h' calls) :
    ∃ (v55 v92 v136 v189 : SourceValue F) (m56 m93 m124 m137 m190 : Heap F)
      (cs66 cs103 cs147 cs201 : List (Call F)),
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v55 m56 cs66 ∧
      m124 = m56 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_ensure_sort"
        [rc, ty, .ptr (.enum kexprListEnum) m56.length] m124 v92 m93 cs103 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, ty] m93 v136 m137 cs147 ∧
      ObsFn W "KernelRoles::axiom_standing" [rc, ap] m137 v189 m190 cs201 ∧
      v189 ≠ .field 0 ∧
      (∀ x ∈ cs66, x ∈ calls) ∧ (∀ x ∈ cs103, x ∈ calls) ∧
      (∀ x ∈ cs147, x ∈ calls) ∧ (∀ x ∈ cs201, x ∈ calls) := by
  have p := Obs.«KernelCheck::check_const».obs ev
  cases p with
  | Axiom_n1 m2 cs12 _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ _ =>
    obtain ⟨h0, _, _⟩ := is_unsafe_ci_zero ev14 (fun _ => rfl)
    injection h0 with hf
    exact absurd hf one_ne_zero
  | Axiom_other_n0 v1 m2 cs12 x_nlvls x_ty w39 v55 m56 cs66 v92 m93 cs103 m124 v136 m137 cs147
      m190 cs201 ev14 _ _ _ _ _ _ _ heq249 _ _ _ =>
    injection heq249 with hf
    exact absurd hf zero_ne_one
  | Axiom_other_other v1 m2 cs12 x_nlvls x_ty w39 v55 m56 cs66 v92 m93 cs103 m124 v136 m137 cs147
      v189 m190 cs201 ev14 hv37 ev68 hm132 ev105 ev149 _ ev203 hne255 _ _ hc263 =>
    obtain ⟨hv1, hm2, _⟩ := is_unsafe_ci_zero ev14 (fun _ => rfl)
    rw [hm2] at ev68
    rw [hv1] at ev149
    injection hv37 with _ _ hargs
    injection hargs with hnl h1
    injection h1 with hty _
    subst hnl hty hc263
    exact ⟨v55, v92, v136, v189, m56, m93, m124, m137, m190, cs66, cs103, cs147, cs201,
      ev68, hm132, ev105, ev149, ev203, hne255,
      fun x hx => by simp [hx], fun x hx => by simp [hx],
      fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  | _ =>
    have hv : Value.construct kciEnum "Axiom" [nl, ty, .field 0] =
        Value.construct "KernelTypes::KConstantInfo" _ _ := by assumption
    injection hv with _ htag _
    exact absurd htag (by decide)

/-- Inversion of `KernelCheck::check_const` on a safe `"Defn"` constant. -/
theorem check_const_defn_inv {rc nl ty val hint ap r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Defn"
        [nl, ty, val, .construct "Ixon::DefinitionSafety" "Safe" [], hint], ap] h r h' calls) :
    ∃ (v298 v335 v372 v416 v446 : SourceValue F)
      (m299 m336 m373 m404 m417 m447 m508 : Heap F)
      (cs309 cs346 cs383 cs427 cs457 cs479 : List (Call F)),
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v298 m299 cs309 ∧
      ObsFn W "KernelCheck::validate_expr_well_scoped" [val, .field 0, nl] m299 v335 m336 cs346 ∧
      m404 = m336 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_ensure_sort"
        [rc, ty, .ptr (.enum kexprListEnum) m336.length] m404 v372 m373 cs383 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, ty] m373 v416 m417 cs427 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, val] m417 v446 m447 cs457 ∧
      m508 = m447 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_check"
        [rc, val, ty, .ptr (.enum kexprListEnum) m447.length] m508 r h' cs479 ∧
      (∀ x ∈ cs309, x ∈ calls) ∧ (∀ x ∈ cs346, x ∈ calls) ∧
      (∀ x ∈ cs383, x ∈ calls) ∧ (∀ x ∈ cs479, x ∈ calls) := by
  have p := Obs.«KernelCheck::check_const».obs ev
  cases p with
  | Defn v1 m2 cs12 x_nlvls x_ty x_val w271 w272 v298 m299 cs309 v335 m336 cs346 v372 m373 cs383
      m404 v416 m417 cs427 v446 m447 cs457 cs479 m508
      ev14 _ hv269 ev311 ev348 hm404 ev385 ev429 ev459 hm508 ev481 hc520 =>
    obtain ⟨hv1, hm2, _⟩ := is_unsafe_ci_zero ev14 (fun _ => rfl)
    rw [hm2] at ev311
    rw [hv1] at ev429 ev459
    injection hv269 with _ _ hargs
    injection hargs with hnl h1
    injection h1 with hty h2
    injection h2 with hval _
    subst hnl hty hval hc520
    exact ⟨v298, v335, v372, v416, v446, m299, m336, m373, m404, m417, m447, m508,
      cs309, cs346, cs383, cs427, cs457, cs479,
      ev311, ev348, hm404, ev385, ev429, ev459, hm508, ev481,
      fun x hx => by simp [hx], fun x hx => by simp [hx],
      fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  | _ =>
    have hv : Value.construct kciEnum "Defn"
        [nl, ty, val, .construct "Ixon::DefinitionSafety" "Safe" [], hint] =
        Value.construct "KernelTypes::KConstantInfo" _ _ := by assumption
    injection hv with _ htag _
    exact absurd htag (by decide)

/-- Inversion of `KernelCheck::check_const` on a `"Thm"` constant. -/
theorem check_const_thm_inv {rc nl ty val ap r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Thm" [nl, ty, val], ap] h r h' calls) :
    ∃ (v543 v580 v617 v715 v745 : SourceValue F)
      (m544 m581 m618 m649 m675 m696 m716 m746 m807 : Heap F)
      (cs554 cs591 cs628 cs683 cs726 cs756 cs778 : List (Call F)),
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v543 m544 cs554 ∧
      ObsFn W "KernelCheck::validate_expr_well_scoped" [val, .field 0, nl] m544 v580 m581 cs591 ∧
      m649 = m581 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_ensure_sort"
        [rc, ty, .ptr (.enum kexprListEnum) m581.length] m649 v617 m618 cs628 ∧
      m696 = m618 ++ [.construct "KernelTypes::KLevelNode" "Zero" []] ∧
      ObsFn W "KernelLevels::level_equal"
        [v617, .ptr (.enum "KernelTypes::KLevelNode") m618.length] m696 (.field 1) m675 cs683 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, ty] m675 v715 m716 cs726 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, val] m716 v745 m746 cs756 ∧
      m807 = m746 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_check"
        [rc, val, ty, .ptr (.enum kexprListEnum) m746.length] m807 r h' cs778 ∧
      (∀ x ∈ cs554, x ∈ calls) ∧ (∀ x ∈ cs591, x ∈ calls) ∧
      (∀ x ∈ cs628, x ∈ calls) ∧ (∀ x ∈ cs683, x ∈ calls) ∧ (∀ x ∈ cs778, x ∈ calls) := by
  have p := Obs.«KernelCheck::check_const».obs ev
  cases p with
  | Thm v1 m2 cs12 x_nlvls x_ty x_val v543 m544 cs554 v580 m581 cs591 v617 m618 cs628 m649
      v672 m675 cs683 m696 v715 m716 cs726 v745 m746 cs756 cs778 m807
      ev14 _ _ hv526 ev556 ev593 hm657 ev630 hm704 ev685 heq714 ev728 ev758 hm815 ev780 hc819 =>
    obtain ⟨hv1, hm2, _⟩ := is_unsafe_ci_zero ev14 trivial
    rw [hm2] at ev556
    rw [hv1] at ev728 ev758
    rw [heq714] at ev685
    injection hv526 with _ _ hargs
    injection hargs with hnl h1
    injection h1 with hty h2
    injection h2 with hval _
    subst hnl hty hval hc819
    exact ⟨v543, v580, v617, v715, v745, m544, m581, m618, m649, m675, m696, m716, m746, m807,
      cs554, cs591, cs628, cs683, cs726, cs756, cs778,
      ev556, ev593, hm657, ev630, hm704, ev685, ev728, ev758, hm815, ev780,
      fun x hx => by simp [hx], fun x hx => by simp [hx],
      fun x hx => by simp [hx], fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  | _ =>
    have hv : Value.construct kciEnum "Thm" [nl, ty, val] =
        Value.construct "KernelTypes::KConstantInfo" _ _ := by assumption
    injection hv with _ htag _
    exact absurd htag (by decide)

/-- Inversion of `KernelCheck::check_const` on a safe `"Opaque"` constant. -/
theorem check_const_opaque_inv {rc nl ty val ap r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Opaque" [nl, ty, val, .field 0], ap] h r h' calls) :
    ∃ (v848 v885 v922 v966 v996 : SourceValue F)
      (m849 m886 m923 m954 m967 m997 m1058 : Heap F)
      (cs859 cs896 cs933 cs977 cs1007 cs1029 : List (Call F)),
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v848 m849 cs859 ∧
      ObsFn W "KernelCheck::validate_expr_well_scoped" [val, .field 0, nl] m849 v885 m886 cs896 ∧
      m954 = m886 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_ensure_sort"
        [rc, ty, .ptr (.enum kexprListEnum) m886.length] m954 v922 m923 cs933 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, ty] m923 v966 m967 cs977 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, val] m967 v996 m997 cs1007 ∧
      m1058 = m997 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_check"
        [rc, val, ty, .ptr (.enum kexprListEnum) m997.length] m1058 r h' cs1029 ∧
      (∀ x ∈ cs859, x ∈ calls) ∧ (∀ x ∈ cs896, x ∈ calls) ∧
      (∀ x ∈ cs933, x ∈ calls) ∧ (∀ x ∈ cs1029, x ∈ calls) := by
  have p := Obs.«KernelCheck::check_const».obs ev
  cases p with
  | Opaque v1 m2 cs12 x_nlvls x_ty x_val w827 v848 m849 cs859 v885 m886 cs896 v922 m923 cs933
      m954 v966 m967 cs977 v996 m997 cs1007 cs1029 m1058
      ev14 _ _ _ hv825 ev861 ev898 hm962 ev935 ev979 ev1009 hm1066 ev1031 hc1070 =>
    obtain ⟨hv1, hm2, _⟩ := is_unsafe_ci_zero ev14 (fun _ => rfl)
    rw [hm2] at ev861
    rw [hv1] at ev979 ev1009
    injection hv825 with _ _ hargs
    injection hargs with hnl h1
    injection h1 with hty h2
    injection h2 with hval _
    subst hnl hty hval hc1070
    exact ⟨v848, v885, v922, v966, v996, m849, m886, m923, m954, m967, m997, m1058,
      cs859, cs896, cs933, cs977, cs1007, cs1029,
      ev861, ev898, hm962, ev935, ev979, ev1009, hm1066, ev1031,
      fun x hx => by simp [hx], fun x hx => by simp [hx],
      fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  | _ =>
    have hv : Value.construct kciEnum "Opaque" [nl, ty, val, .field 0] =
        Value.construct "KernelTypes::KConstantInfo" _ _ := by assumption
    injection hv with _ htag _
    exact absurd htag (by decide)

/-- Inversion of `KernelCheck::check_const` on a `"Quot"` constant. -/
theorem check_const_quot_inv {rc nl ty kind ap r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Quot" [nl, ty, kind], ap] h r h' calls) :
    ∃ (v1093 v1130 v1174 : SourceValue F)
      (m1094 m1131 m1162 m1175 : Heap F)
      (cs1104 cs1141 cs1185 cs1207 : List (Call F)),
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v1093 m1094 cs1104 ∧
      m1162 = m1094 ++ [.construct kexprListEnum "Nil" []] ∧
      ObsFn W "KernelInfer::k_ensure_sort"
        [rc, ty, .ptr (.enum kexprListEnum) m1094.length] m1162 v1130 m1131 cs1141 ∧
      ObsFn W "KernelCheck::assert_safety" [.field 0, ty] m1131 v1174 m1175 cs1185 ∧
      ObsFn W "KernelCheck::check_quot" [rc, ap, kind] m1175 r h' cs1207 ∧
      (∀ x ∈ cs1104, x ∈ calls) ∧ (∀ x ∈ cs1141, x ∈ calls) ∧
      (∀ x ∈ cs1185, x ∈ calls) ∧ (∀ x ∈ cs1207, x ∈ calls) := by
  have p := Obs.«KernelCheck::check_const».obs ev
  cases p with
  | Quot v1 m2 cs12 x_nlvls x_ty x_kind v1093 m1094 cs1104 v1130 m1131 cs1141 m1162 v1174 m1175
      cs1185 cs1207 ev14 _ _ _ _ hv1076 ev1106 hm1170 ev1143 ev1187 ev1209 hc1234 =>
    obtain ⟨hv1, hm2, _⟩ := is_unsafe_ci_zero ev14 trivial
    rw [hm2] at ev1106
    rw [hv1] at ev1187
    injection hv1076 with _ _ hargs
    injection hargs with hnl h1
    injection h1 with hty h2
    injection h2 with hkind _
    subst hnl hty hkind hc1234
    exact ⟨v1093, v1130, v1174, m1094, m1131, m1162, m1175, cs1104, cs1141, cs1185, cs1207,
      ev1106, hm1170, ev1143, ev1187, ev1209,
      fun x hx => by simp [hx], fun x hx => by simp [hx],
      fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  | _ =>
    have hv : Value.construct kciEnum "Quot" [nl, ty, kind] =
        Value.construct "KernelTypes::KConstantInfo" _ _ := by assumption
    injection hv with _ htag _
    exact absurd htag (by decide)

/-! ## Shared front-end assembly (`ConstantValRunJ`, `ValueFrontRunJ`, `rulesJ.isZero`) -/

private def zeroGhost : Nat → KExpr := fun _ => .sort .zero

/-- Assemble `ConstantValRunJ rulesJ` from `validate_expr_well_scoped` + `k_ensure_sort` on an
exact closed type representation with positional level parameters `List.range n`. -/
theorem constantValRunJ_of_front (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {type' : KExpr}
    {rc nl ty v55 v92 : SourceValue F} {h m56 m93 m124 : Heap F}
    {cs66 cs103 : List (Call F)}
    (hfresh : env.find? cv.name = none)
    (hres : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (hnoprj : cv.name.isProjFnShape = false)
    (hrange : cv.levelParams = List.range cv.levelParams.length)
    (hcenv : c.env = env)
    (hval : ValRepExact c.κ h nl ty ⟨cv.name, cv.levelParams, type'⟩)
    (hann : IxVM.Consistency.Annotates type' cv.type)
    (hrc : RCRep c.t c.lim h rc) (hef : EnvFacts c) (hlf : LoadFacts c)
    (hg66 : Good c cs66) (hg103 : Good c cs103)
    (ev_sc : ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v55 m56 cs66)
    (hm124 : m124 = m56 ++ [.construct kexprListEnum "Nil" []])
    (ev_sort : ObsFn W "KernelInfer::k_ensure_sort"
      [rc, ty, .ptr (.enum kexprListEnum) m56.length] m124 v92 m93 cs103) :
    ConstantValRunJ rulesJ env cv type' ∧
      ∃ stype u ℓ,
        Infer env .full 0 type' stype ∧ Red env 0 stype (.sort u) ∧
        RepKLevel m93 ℓ v92 ∧ LvEq u ℓ := by
  obtain ⟨rfl, hnl, hperm, hty_rep⟩ := hval
  have hty_pos : posOf cv.levelParams type' = type' := by
    conv => lhs; rw [hrange]
    exact posOf_range cv.levelParams.length type'
  rw [hty_pos] at hty_rep
  have hlvl_def0 : type'.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
    validate_expr_well_scoped_spec hnl (hty_rep 0 zeroGhost) ev_sc
  have hlvl_def : type'.allLevelParamsDefined cv.levelParams = true := by
    rw [← hrange] at hlvl_def0; exact hlvl_def0
  have e_sc := ObsFn.heap_extends ev_sc
  have e_nil : Heap.Extends h m124 :=
    hm124 ▸ e_sc.trans (heap_extends_append m56 _)
  have htypes : TypesRep c.κ zeroGhost m124 0 (.ptr (.enum kexprListEnum) m56.length) :=
    hm124 ▸ typesRep_alloc_nil c.κ zeroGhost m56
  obtain ⟨stype, u, ℓ, hinf0, hred0, hℓ, hu⟩ :=
    core_ensure_sort hCore (hrc.mono e_nil) htypes (ghostScoped_zero zeroGhost) hef hlf hg103
      ev_sort ((hty_rep 0 zeroGhost).toTm.mono e_nil)
  have hinf : Infer env .full 0 type' stype := hcenv ▸ hinf0
  have hred : Red env 0 stype (.sort u) := hcenv ▸ hred0
  have hty'_nfv : type'.hasFvar = false :=
    Tm.hasFvar_false (hty_rep 0 zeroGhost).toTm
  have hcv_nfv : cv.type.hasFvar = false := annotates_hasFvar_false hann hty'_nfv
  have hty'_bvs : type'.looseBVarsBounded 0 = true :=
    (hty_rep 0 zeroGhost).toTm.looseBVarsBounded
  have hcv_bvs : cv.type.looseBVarsBounded 0 = true :=
    annotates_looseBVarsBounded hann hty'_bvs
  have hcr : type'.constsResolve env = true := infer_constsResolve hinf hty'_nfv
  refine ⟨⟨?_, hres, hnoprj, levelParam_nodup_of_perm_range hperm, hcv_bvs, hcv_nfv,
    annot_of_annotates hann, hlvl_def, hcr, stype, u, hinf, hred⟩,
    stype, u, ℓ, hinf, hred, hℓ, hu⟩
  rw [hfresh]; rfl

/-- Assemble `ValueFrontRunJ rulesJ` from `validate_expr_well_scoped` + `k_check` on exact closed
type and value representations with positional level parameters `List.range n`. -/
theorem valueFrontRunJ_of_front (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {value type' value' : KExpr}
    {rc ty val v_sc r_chk : SourceValue F} {h₀ h_sc h_pre h_chk h_chk' h' : Heap F}
    {cs_sc cs_chk : List (Call F)}
    (hrange : cv.levelParams = List.range cv.levelParams.length)
    (hcenv : c.env = env)
    (hnl : cv.levelParams.length < 4294967296)
    (hty_rep : TmCExact c.κ h₀ type' ty)
    (hval_rep : TmCExact c.κ h₀ value' val)
    (hann : IxVM.Consistency.Annotates value' value)
    (ext_sc : Heap.Extends h₀ h_sc)
    (ext_pre : Heap.Extends h₀ h_pre)
    (hrc : RCRep c.t c.lim h₀ rc) (hef : EnvFacts c) (hlf : LoadFacts c)
    (hg_sc : Good c cs_sc) (hg_chk : Good c cs_chk)
    (ev_sc : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [val, .field 0, .field (cv.levelParams.length : F)] h_sc v_sc h_chk cs_sc)
    (hm_chk : h_chk' = h_pre ++ [.construct kexprListEnum "Nil" []])
    (ev_chk : ObsFn W "KernelInfer::k_check"
      [rc, val, ty, .ptr (.enum kexprListEnum) h_pre.length] h_chk' r_chk h' cs_chk) :
    ValueFrontRunJ rulesJ env cv value type' value' := by
  have hlvl_def0 : value'.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
    validate_expr_well_scoped_spec hnl ((hval_rep 0 zeroGhost).mono ext_sc) ev_sc
  have hlvl_def : value'.allLevelParamsDefined cv.levelParams = true := by
    rw [← hrange] at hlvl_def0; exact hlvl_def0
  have e_chk : Heap.Extends h₀ h_chk' :=
    hm_chk ▸ ext_pre.trans (heap_extends_append h_pre _)
  have htypes : TypesRep c.κ zeroGhost h_chk' 0 (.ptr (.enum kexprListEnum) h_pre.length) :=
    hm_chk ▸ typesRep_alloc_nil c.κ zeroGhost h_pre
  obtain ⟨vtype, hinf0, hde0⟩ :=
    core_check hCore (hrc.mono e_chk) htypes (ghostScoped_zero zeroGhost) hef hlf hg_chk ev_chk
      ((hval_rep 0 zeroGhost).toTm.mono e_chk) ((hty_rep 0 zeroGhost).toTm.mono e_chk)
  have hinf : Infer env .full 0 value' vtype := hcenv ▸ hinf0
  have hde : DefEq env 0 vtype type' := hcenv ▸ hde0
  have hval'_nfv : value'.hasFvar = false := Tm.hasFvar_false (hval_rep 0 zeroGhost).toTm
  have hval_nfv : value.hasFvar = false := annotates_hasFvar_false hann hval'_nfv
  have hval'_bvs : value'.looseBVarsBounded 0 = true :=
    (hval_rep 0 zeroGhost).toTm.looseBVarsBounded
  have hval_bvs : value.looseBVarsBounded 0 = true :=
    annotates_looseBVarsBounded hann hval'_bvs
  have hcr : value'.constsResolve env = true := infer_constsResolve hinf hval'_nfv
  exact ⟨hval_bvs, hval_nfv, annot_of_annotates hann, hlvl_def, hcr, vtype, hinf, hde⟩

/-- Derive `rulesJ.isZero u` from `k_ensure_sort`'s output level `ℓ` (`LvEq u ℓ`) and
`KernelLevels::level_equal` comparing `v617` against a freshly allocated `Zero` node. -/
theorem thm_isZero_of_level_equal (hLevels : IxVM.Consistency.Levels)
    {u ℓ : KLevel} {v617 : SourceValue F} {m618 m696 m675 : Heap F} {cs683 : List (Call F)}
    (hbnd : IxVM.Consistency.Bounded cs683)
    (hℓ : RepKLevel m618 ℓ v617) (hu : LvEq u ℓ)
    (hm696 : m696 = m618 ++ [.construct "KernelTypes::KLevelNode" "Zero" []])
    (ev685 : ObsFn W "KernelLevels::level_equal"
      [v617, .ptr (.enum "KernelTypes::KLevelNode") m618.length] m696 (.field 1) m675 cs683) :
    (rulesJ (md := .anon)).isZero u := by
  have ext : Heap.Extends m618 m696 := hm696 ▸ heap_extends_append m618 _
  have hzero : RepKLevel m696 .zero (.ptr (.enum "KernelTypes::KLevelNode") m618.length) :=
    RepKLevel.zero (by simp [hm696])
  have heq := levels_equal_one hLevels ev685 hbnd (hℓ.mono ext) hzero
  intro φ
  exact (hu φ).trans (heq φ)

/-! ## Assembly, loader, and role-validation companions (`DeclValueExtraFacts`) -/

/-- Companions owed by the record loader (L1), role/standing validation (L6), and declaration-order
assembly (L7) for standalone value, axiom, theorem, opaque, quotient, and pinned-basis steps. -/
structure DeclValueExtraFacts (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (d : Declaration .anon) : Prop where
  /-- L6 role-lookup family specifications (`Core.Specs.Roles.Fn.spec`). -/
  rolesSpec : RolesSpec
  /-- Distinct names in `installs d` (reader block/basis invariant). -/
  installsNodup : ((IxVM.Consistency.installs d).map (·.name)).Nodup
  /-- Freshness of `installs d` in the prefix `env` (L7 assembly topological order). -/
  installsFresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none
  /-- For `.quotDecl .type`, `.basisDecl .quotK`, or pinned `.quotK` block, `Eq` is already stored
  as `eqA` (validated in an earlier role group before `.quot`). -/
  quotEqStored :
    ((∃ cv, d = .quotDecl .type cv) ∨ d = .basisDecl .quotK ∨
      ∃ block nP, d = .indDecl block nP ∧ Ix.Kernel.basisPinHit block = some .quotK) →
      env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA
  /-- Observed sub-derivation, exact loader witness, safety tag, empty user-axiom map, and
  role-context companions for a `check_const` call in `S0.Checked` on standalone value/axiom
  declarations. -/
  checkedValue :
    ∀ (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (cl : Call F)
      (rc v ap : SourceValue F) (lim : Option Nat) (a : _root_.Address)
      (ci ci₀ : ConstantInfo .anon),
      t.wf = true →
      Good ⟨E, env, t, none⟩ calls →
      cl ∈ calls → cl.name = "KernelCheck::check_const" → cl.args = [rc, v, ap] →
      RCRep t lim cl.heap rc → S0.addr cl.heap ap a → keyOf t a = ci₀.name →
      CIRep (keyOf t) cl.heap v ci → IxVM.Consistency.StoredAs ci ci₀ →
      ci₀ ∈ IxVM.Consistency.installs d →
      (DeclStoreInv env → CtxRoleFacts ⟨E, env, t, lim⟩) ∧
      CISafe v ∧ RCAxiomsNil cl.heap rc ∧
      Ix.Kernel.reservedBasisNames.contains ci₀.name = false ∧
      ci₀.toConstantVal.levelParams = List.range ci₀.toConstantVal.levelParams.length ∧
      (∃ (r_cl : SourceValue F) (h'_cl : Heap F) (subcalls : List (Call F)),
        ObsFn W "KernelCheck::check_const" [rc, v, ap] cl.heap r_cl h'_cl subcalls ∧
        (∀ x ∈ subcalls, x ∈ calls)) ∧
      (∀ cv, d = .axiomDecl cv → ∃ nl ty u,
        v = .construct kciEnum "Axiom" [nl, ty, u] ∧
        ValRepExact (keyOf t) cl.heap nl ty ci.toConstantVal) ∧
      (∀ cv value hint, d = .defnDecl cv value hint → CIRepExact (keyOf t) cl.heap v ci) ∧
      (∀ cv value, d = .thmDecl cv value → CIRepExact (keyOf t) cl.heap v ci) ∧
      (∀ cv value, d = .opaqueDecl cv value → ∃ nl ty val u value',
        v = .construct kciEnum "Opaque" [nl, ty, val, u] ∧
        ValRepExact (keyOf t) cl.heap nl ty ci.toConstantVal ∧
        TmCExact (keyOf t) cl.heap (posOf ci.toConstantVal.levelParams value') val ∧
        IxVM.Consistency.Annotates value' value)
  /-- L6 role-group validation (`validate_typed` / `validate_group`) pins `propext` and `choice`
  against their standard signatures once their role is in force. -/
  stdAxiomPinned :
    ∀ (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
      (ro : Ix.Kernel.Role) (cvA : ConstantVal .anon),
      DeclStoreInv env → t.wf = true →
      Ctx.inForce ⟨E, env, t, lim⟩ ro →
      (ro = .propext ∨ ro = .choice) → cvA.name = .role ro →
      Ix.Kernel.stdAxiomOk env cvA = true
  /-- L6 operation validation (`KernelRoles::validate_op`) supplies the structural `Nat`
  recurrence equations and `div`/`mod` certificate derivations when `cv.name` is a certified
  `Nat` operation. -/
  defnOpCertified :
    ∀ (cv : ConstantVal .anon) (value : KExpr) (hint : Ix.Kernel.ReducibilityHint)
      (type' value' : KExpr),
      d = .defnDecl cv value hint → DeclStoreInv env →
      ConstantValRunJ rulesJ env cv type' →
      ValueFrontRunJ rulesJ env cv value type' value' →
      let env₂ : Ix.Kernel.Env .anon :=
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint :: env.consts⟩
      (Ix.Kernel.natOpNames.contains cv.name = true →
        Ix.Kernel.natOpGuard env₂ cv.name = true ∧
        (Ix.Kernel.natOpDeps cv.name).all (Ix.Kernel.natOpStoredOk env₂) = true ∧
        Ix.Kernel.Semantics.NatEqsRunJ rulesJ env
          ((Ix.Kernel.natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))) ∧
      (Ix.Kernel.natDivModNames.contains cv.name = true →
        Ix.Kernel.Semantics.DivModCertRunJ rulesJ env env₂ cv.name value')

/-! ## Per-kind step preservation theorems -/

/-- Step preservation for `.axiomDecl cv` (both empty installs at `quotSoundName` / `inertKey` and
certified standard axioms `propext` / `choice`). -/
theorem axiomDecl_step (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon}
    (hchk : S0.Checked calls env (.axiomDecl cv))
    (hx : DeclValueExtraFacts calls env (.axiomDecl cv)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.axiomDecl cv) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  by_cases hskip : cv.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv.name = true
  · have hempty : IxVM.Consistency.installs (.axiomDecl cv) = [] := by
      simp only [IxVM.Consistency.installs]
      exact ite_eq_left hskip
    exact ⟨env, installStep_empty hempty, fun _ _ h => h⟩
  · have hinst_eq : IxVM.Consistency.installs (.axiomDecl cv) = [.axiomInfo cv] := by
      simp only [IxVM.Consistency.installs]
      exact ite_eq_right hskip
    refine decls_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
    obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
    have hmem : ConstantInfo.axiomInfo cv ∈ IxVM.Consistency.installs (.axiomDecl cv) := by
      rw [hinst_eq]; exact List.mem_singleton.mpr rfl
    obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
      hall (.axiomInfo cv) hmem
    obtain ⟨hR_fn, hsafe, hnil, hres, hrange, ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩,
      hax_shape, -, -, -⟩ :=
      hx.checkedValue E t cl rc v ap lim a ci (.axiomInfo cv) htwf hgood hcl hname hargs
        hrc hadr hkey hci hstored hmem
    obtain ⟨nl, ty, u, rfl, hval⟩ := hax_shape cv rfl
    have hu0 : u = .field 0 := hsafe rfl
    subst hu0
    cases ci with
    | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
    | projInfo _ => cases hstored.2
    | axiomInfo cvA =>
      obtain ⟨⟨hcv_name, hcv_lps, hann_ty⟩, -⟩ := hstored
      dsimp only [ConstantInfo.toConstantVal] at hval
      let c : Ctx := ⟨E, env, t, lim⟩
      have hgood_c : Good c calls := hgood
      have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
      have hlf : LoadFacts c := hloads.withLim
      have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.axiomInfo cv) hmem
      have hnoprj : cv.name.isProjFnShape = false := by
        have hk := keyOf_isProjFnShape_false t a
        rw [hkey] at hk; exact hk
      have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ := by
        have : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
          cases cvA; dsimp only at hcv_name hcv_lps; subst hcv_name hcv_lps; rfl
        exact this ▸ hval
      obtain ⟨v55, v92, v136, v189, m56, m93, m124, m137, m190, cs66, cs103, cs147, cs201,
        ev68, hm132, ev105, ev149, ev203, hne255, hcs66, hcs103, _, hcs201⟩ :=
        check_const_axiom_inv ev_chk
      obtain ⟨hcv_run, -⟩ := constantValRunJ_of_front hCore hfresh_cv hres hnoprj hrange rfl
        hval_cv hann_ty hrc hef hlf
        (hgood_c.sub fun x hx => hsub x (hcs66 x hx))
        (hgood_c.sub fun x hx => hsub x (hcs103 x hx))
        ev68 hm132 ev105
      obtain ⟨a', ha', heq_a⟩ := hadr
      have e_to_m137 : Heap.Extends cl.heap m137 :=
        (ObsFn.heap_extends ev68).trans
          ((hm132 ▸ heap_extends_append m56 _).trans
            ((ObsFn.heap_extends ev105).trans (ObsFn.heap_extends ev149)))
      obtain ⟨ro, hro_addr, hin, hro_cases⟩ :=
        axiom_standing_spec hx.rolesSpec (hgood_c.sub fun x hx => hsub x (hcs201 x hx))
          htwf (hrc.mono e_to_m137) (hnil.mono e_to_m137)
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_m137 ha') ev203 hne255
      have hkey_ro : cv.name = .role ro := by
        have hk := keyOf_of_addressOf htwf hro_addr
        rw [heq_a, hkey] at hk
        exact hk.symm
      have hro_std : ro = .propext ∨ ro = .choice := by
        rcases hro_cases with rfl | rfl | rfl | hinert
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd (Or.inl hkey_ro) hskip
        · have : IxVM.Consistency.inertKey cv.name = true := by
            rw [hkey_ro]; exact hinert
          exact absurd (Or.inr this) hskip
      have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
        cases cvA; dsimp only at hcv_name hcv_lps; subst hcv_name hcv_lps; rfl
      have hstd : Ix.Kernel.stdAxiomOk env ⟨cv.name, cv.levelParams, cvA.type⟩ = true :=
        hx.stdAxiomPinned E t lim ro _ hS htwf hin hro_std hkey_ro
      have hfresh_ci : env.find? (ConstantInfo.axiomInfo cvA).name = none := by
        show env.find? cvA.name = none
        rw [hcv_name]; exact hfresh_cv
      refine ⟨⟨.axiomInfo cvA :: env.consts⟩,
        installStep_single hinst_eq hstored hfresh_ci, ?_⟩
      show DeclAxiomRunJ rulesJ env cv ⟨.axiomInfo cvA :: env.consts⟩
      refine Or.inr ⟨cvA.type, hcv_run, Or.inl ⟨hstd, ?_⟩⟩
      rw [← hcvA_eq]

/-- Step preservation for `.defnDecl cv value hint`. -/
theorem defnDecl_step (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (hchk : S0.Checked calls env (.defnDecl cv value hint))
    (hx : DeclValueExtraFacts calls env (.defnDecl cv value hint)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.defnDecl cv value hint) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.defnDecl cv value hint) =
      [.defnInfo cv value hint] := rfl
  refine decls_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
  obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
  have hmem : ConstantInfo.defnInfo cv value hint ∈
      IxVM.Consistency.installs (.defnDecl cv value hint) := List.mem_singleton.mpr rfl
  obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
    hall (.defnInfo cv value hint) hmem
  obtain ⟨hR_fn, hsafe, -, hres, hrange, ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩,
    -, hdefn_exact, -, -⟩ :=
    hx.checkedValue E t cl rc v ap lim a ci (.defnInfo cv value hint) htwf hgood hcl hname hargs
      hrc hadr hkey hci hstored hmem
  have hexact := hdefn_exact cv value hint rfl
  cases ci with
  | axiomInfo _ | thmInfo _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
  | projInfo _ => cases hstored.2
  | defnInfo cvA value' hint' =>
    obtain ⟨⟨hcv_name, hcv_lps, hann_ty⟩, hann_val, rfl⟩ := hstored
    cases hexact with
    | quot _ hk =>
      rcases hk with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;>
        cases h
    | defn hval hV =>
      rename_i nl ty val sf hn_v
      have hsf0 : sf = .construct "Ixon::DefinitionSafety" "Safe" [] := hsafe rfl
      subst hsf0
      let c : Ctx := ⟨E, env, t, lim⟩
      have hgood_c : Good c calls := hgood
      have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
      have hlf : LoadFacts c := hloads.withLim
      have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.defnInfo cv value hint) hmem
      have hnoprj : cv.name.isProjFnShape = false := by
        have hk := keyOf_isProjFnShape_false t a
        rw [hkey] at hk; exact hk
      have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
        cases cvA; dsimp only at hcv_name hcv_lps; subst hcv_name hcv_lps; rfl
      have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ :=
        hcvA_eq ▸ hval
      obtain ⟨v298, v335, v372, v416, v446, m299, m336, m373, m404, m417, m447, m508,
        cs309, cs346, cs383, cs427, cs457, cs479,
        ev311, ev348, hm404, ev385, ev429, ev459, hm508, ev481,
        hcs309, hcs346, hcs383, hcs479⟩ :=
        check_const_defn_inv ev_chk
      have e_sc1 := ObsFn.heap_extends ev311
      have e_sc2 := ObsFn.heap_extends ev348
      have hm404' : m404 = m336 ++ [.construct kexprListEnum "Nil" []] := hm404
      obtain ⟨rfl, hnl, hperm, hty_rep0⟩ := hval_cv
      have hty_pos : posOf cv.levelParams cvA.type = cvA.type := by
        conv => lhs; rw [hrange]
        exact posOf_range cv.levelParams.length cvA.type
      have hval_pos : posOf cvA.levelParams value' = value' := by
        rw [hcv_lps]; conv => lhs; rw [hrange]
        exact posOf_range cv.levelParams.length value'
      rw [hty_pos] at hty_rep0
      rw [hval_pos] at hV
      -- Assemble `ConstantValRunJ` (noting `k_ensure_sort` runs at `m404` after `ev348`).
      have hlvl_ty0 : cvA.type.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
        validate_expr_well_scoped_spec hnl (hty_rep0 0 zeroGhost) ev311
      have hlvl_ty : cvA.type.allLevelParamsDefined cv.levelParams = true := by
        rw [← hrange] at hlvl_ty0; exact hlvl_ty0
      have e_m404 : Heap.Extends cl.heap m404 :=
        hm404' ▸ (e_sc1.trans e_sc2).trans (heap_extends_append m336 _)
      have htypes404 : TypesRep c.κ zeroGhost m404 0 (.ptr (.enum kexprListEnum) m336.length) :=
        hm404' ▸ typesRep_alloc_nil c.κ zeroGhost m336
      obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
        core_ensure_sort hCore (hrc.mono e_m404) htypes404 (ghostScoped_zero zeroGhost) hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs383 x hx)) ev385
          ((hty_rep0 0 zeroGhost).toTm.mono e_m404)
      have hty'_nfv : cvA.type.hasFvar = false := Tm.hasFvar_false (hty_rep0 0 zeroGhost).toTm
      have hty'_bvs : cvA.type.looseBVarsBounded 0 = true :=
        (hty_rep0 0 zeroGhost).toTm.looseBVarsBounded
      have hcv_run : ConstantValRunJ rulesJ env cv cvA.type :=
        ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_perm_range hperm,
          annotates_looseBVarsBounded hann_ty hty'_bvs,
          annotates_hasFvar_false hann_ty hty'_nfv,
          annot_of_annotates hann_ty, hlvl_ty,
          infer_constsResolve hinf_ty hty'_nfv, stype, u, hinf_ty, hred_ty⟩
      have e_pre_chk : Heap.Extends cl.heap m447 :=
        e_m404.trans ((ObsFn.heap_extends ev385).trans
          ((ObsFn.heap_extends ev429).trans (ObsFn.heap_extends ev459)))
      have hv_run : ValueFrontRunJ rulesJ env cv value cvA.type value' :=
        valueFrontRunJ_of_front hCore hrange rfl hnl hty_rep0 hV hann_val e_sc1 e_pre_chk
          hrc hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs346 x hx))
          (hgood_c.sub fun x hx => hsub x (hcs479 x hx))
          ev348 hm508 ev481
      obtain ⟨hop, hdm⟩ := hx.defnOpCertified cv value hint cvA.type value' rfl hS hcv_run hv_run
      have hfresh_ci : env.find? (ConstantInfo.defnInfo cvA value' hint).name = none := by
        show env.find? cvA.name = none
        rw [hcv_name]; exact hfresh_cv
      refine ⟨⟨.defnInfo cvA value' hint :: env.consts⟩,
        installStep_single hinst_eq hstored hfresh_ci, ?_⟩
      show DeclDefnRunJ rulesJ env cv value hint ⟨.defnInfo cvA value' hint :: env.consts⟩
      refine ⟨cvA.type, value', hcv_run, hv_run, ?_, hop, hdm⟩
      rw [← hcvA_eq]

/-- Step preservation for `.thmDecl cv value`, storing the annotated theorem value `value'` so
`ThmValOk` and `IxVM.Consistency.ThmVal` hold. -/
theorem thmDecl_step (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hchk : S0.Checked calls env (.thmDecl cv value))
    (hx : DeclValueExtraFacts calls env (.thmDecl cv value)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.thmDecl cv value) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.thmDecl cv value) = [.thmInfo cv value] := rfl
  refine decls_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
  obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
  have hmem : ConstantInfo.thmInfo cv value ∈ IxVM.Consistency.installs (.thmDecl cv value) :=
    List.mem_singleton.mpr rfl
  obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
    hall (.thmInfo cv value) hmem
  obtain ⟨hR_fn, -, -, hres, hrange, ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩,
    -, -, hthm_exact, -⟩ :=
    hx.checkedValue E t cl rc v ap lim a ci (.thmInfo cv value) htwf hgood hcl hname hargs
      hrc hadr hkey hci hstored hmem
  have hexact := hthm_exact cv value rfl
  cases ci with
  | axiomInfo _ | defnInfo _ _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
  | projInfo _ => cases hstored.2
  | thmInfo cvA value' =>
    obtain ⟨⟨hcv_name, hcv_lps, hann_ty⟩, hann_val⟩ := hstored
    cases hexact with
    | quot _ hk =>
      rcases hk with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;>
        cases h
    | thm hval hV =>
      rename_i nl ty val
      let c : Ctx := ⟨E, env, t, lim⟩
      have hgood_c : Good c calls := hgood
      have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
      have hlf : LoadFacts c := hloads.withLim
      have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.thmInfo cv value) hmem
      have hnoprj : cv.name.isProjFnShape = false := by
        have hk := keyOf_isProjFnShape_false t a
        rw [hkey] at hk; exact hk
      have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
        cases cvA; dsimp only at hcv_name hcv_lps; subst hcv_name hcv_lps; rfl
      have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ :=
        hcvA_eq ▸ hval
      obtain ⟨v543, v580, v617, v724, v754, m544, m581, m618, m649, m675, m696, m725, m755, m807,
        cs554, cs591, cs628, cs683, cs735, cs765, cs778,
        ev556, ev593, hm649, ev630, hm696, ev685, ev737, ev767, hm807, ev780,
        _, hcs591, hcs628, hcs683, hcs778⟩ :=
        check_const_thm_inv ev_chk
      have e_sc1 := ObsFn.heap_extends ev556
      have e_sc2 := ObsFn.heap_extends ev593
      obtain ⟨rfl, hnl, hperm, hty_rep0⟩ := hval_cv
      have hty_pos : posOf cv.levelParams cvA.type = cvA.type := by
        conv => lhs; rw [hrange]
        exact posOf_range cv.levelParams.length cvA.type
      have hval_pos : posOf cvA.levelParams value' = value' := by
        rw [hcv_lps]; conv => lhs; rw [hrange]
        exact posOf_range cv.levelParams.length value'
      rw [hty_pos] at hty_rep0
      rw [hval_pos] at hV
      have hlvl_ty0 : cvA.type.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
        validate_expr_well_scoped_spec hnl (hty_rep0 0 zeroGhost) ev556
      have hlvl_ty : cvA.type.allLevelParamsDefined cv.levelParams = true := by
        rw [← hrange] at hlvl_ty0; exact hlvl_ty0
      have e_m649 : Heap.Extends cl.heap m649 :=
        hm649 ▸ (e_sc1.trans e_sc2).trans (heap_extends_append m581 _)
      have htypes649 : TypesRep c.κ zeroGhost m649 0 (.ptr (.enum kexprListEnum) m581.length) :=
        hm649 ▸ typesRep_alloc_nil c.κ zeroGhost m581
      obtain ⟨stype, u, ℓ, hinf_ty, hred_ty, hℓ, hu⟩ :=
        core_ensure_sort hCore (hrc.mono e_m649) htypes649 (ghostScoped_zero zeroGhost) hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs628 x hx)) ev630
          ((hty_rep0 0 zeroGhost).toTm.mono e_m649)
      have hisZero : (rulesJ (md := .anon)).isZero u :=
        thm_isZero_of_level_equal hLevels
          (bounded_sub (fun x hx => hsub x (hcs683 x hx)) hgood.2)
          hℓ hu hm696 ev685
      have hty'_nfv : cvA.type.hasFvar = false := Tm.hasFvar_false (hty_rep0 0 zeroGhost).toTm
      have hty'_bvs : cvA.type.looseBVarsBounded 0 = true :=
        (hty_rep0 0 zeroGhost).toTm.looseBVarsBounded
      have hcv_run : ConstantValRunJ rulesJ env cv cvA.type :=
        ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_perm_range hperm,
          annotates_looseBVarsBounded hann_ty hty'_bvs,
          annotates_hasFvar_false hann_ty hty'_nfv,
          annot_of_annotates hann_ty, hlvl_ty,
          infer_constsResolve hinf_ty hty'_nfv, stype, u, hinf_ty, hred_ty⟩
      have e_m696 : Heap.Extends m618 m696 := hm696 ▸ heap_extends_append m618 _
      have e_pre_chk : Heap.Extends cl.heap m755 :=
        e_m649.trans ((ObsFn.heap_extends ev630).trans
          (e_m696.trans ((ObsFn.heap_extends ev685).trans
            ((ObsFn.heap_extends ev737).trans (ObsFn.heap_extends ev767)))))
      have hv_run : ValueFrontRunJ rulesJ env cv value cvA.type value' :=
        valueFrontRunJ_of_front hCore hrange rfl hnl hty_rep0 hV hann_val e_sc1 e_pre_chk
          hrc hef hlf
          (hgood_c.sub fun x hx => hsub x (hcs591 x hx))
          (hgood_c.sub fun x hx => hsub x (hcs778 x hx))
          ev593 hm807 ev780
      have hfresh_ci : env.find? (ConstantInfo.thmInfo cvA value').name = none := by
        show env.find? cvA.name = none
        rw [hcv_name]; exact hfresh_cv
      refine ⟨⟨.thmInfo cvA value' :: env.consts⟩,
        installStep_single hinst_eq hstored hfresh_ci, ?_⟩
      show DeclThmRunJ rulesJ env cv value ⟨.thmInfo cvA value' :: env.consts⟩
      refine ⟨cvA.type, value', hcv_run, ⟨stype, u, hinf_ty, hred_ty, hisZero⟩, hv_run, ?_⟩
      rw [← hcvA_eq]; rfl

/-- Step preservation for `.opaqueDecl cv value` (installed as `.axiomInfo cvA`). -/
theorem opaqueDecl_step (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr}
    (hchk : S0.Checked calls env (.opaqueDecl cv value))
    (hx : DeclValueExtraFacts calls env (.opaqueDecl cv value)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.opaqueDecl cv value) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.opaqueDecl cv value) = [.axiomInfo cv] := rfl
  refine decls_step_of_store hchk hx.installsNodup hx.installsFresh fun hS => ?_
  obtain ⟨E, t, htwf, hloads, hgood, hall⟩ := hchk
  have hmem : ConstantInfo.axiomInfo cv ∈ IxVM.Consistency.installs (.opaqueDecl cv value) :=
    List.mem_singleton.mpr rfl
  obtain ⟨cl, hcl, hname, rc, v, ap, lim, a, ci, hargs, hrc, hadr, hkey, hci, hstored⟩ :=
    hall (.axiomInfo cv) hmem
  obtain ⟨hR_fn, hsafe, -, hres, hrange, ⟨r_cl, h'_cl, subcalls, ev_chk, hsub⟩,
    -, -, -, hopaq_shape⟩ :=
    hx.checkedValue E t cl rc v ap lim a ci (.axiomInfo cv) htwf hgood hcl hname hargs
      hrc hadr hkey hci hstored hmem
  obtain ⟨nl, ty, val, u, value', rfl, hval, hV, hann_val⟩ := hopaq_shape cv value rfl
  have hu0 : u = .field 0 := hsafe rfl
  subst hu0
  cases ci with
  | defnInfo _ _ _ | thmInfo _ _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _
  | projInfo _ => cases hstored.2
  | axiomInfo cvA =>
    obtain ⟨⟨hcv_name, hcv_lps, hann_ty⟩, -⟩ := hstored
    dsimp only [ConstantInfo.toConstantVal] at hval hV
    let c : Ctx := ⟨E, env, t, lim⟩
    have hgood_c : Good c calls := hgood
    have hef : EnvFacts c := hS.toEnvFacts htwf (hR_fn hS)
    have hlf : LoadFacts c := hloads.withLim
    have hfresh_cv : env.find? cv.name = none := hx.installsFresh (.axiomInfo cv) hmem
    have hnoprj : cv.name.isProjFnShape = false := by
      have hk := keyOf_isProjFnShape_false t a
      rw [hkey] at hk; exact hk
    have hcvA_eq : cvA = ⟨cv.name, cv.levelParams, cvA.type⟩ := by
      cases cvA; dsimp only at hcv_name hcv_lps; subst hcv_name hcv_lps; rfl
    have hval_cv : ValRepExact c.κ cl.heap nl ty ⟨cv.name, cv.levelParams, cvA.type⟩ :=
      hcvA_eq ▸ hval
    obtain ⟨v848, v885, v922, v966, v996, m849, m886, m923, m954, m967, m997, m1058,
      cs859, cs896, cs933, cs977, cs1007, cs1029,
      ev861, ev898, hm954, ev935, ev979, ev1009, hm1058, ev1031,
      _, hcs896, hcs933, hcs1029⟩ :=
      check_const_opaque_inv ev_chk
    have e_sc1 := ObsFn.heap_extends ev861
    have e_sc2 := ObsFn.heap_extends ev898
    obtain ⟨rfl, hnl, hperm, hty_rep0⟩ := hval_cv
    have hty_pos : posOf cv.levelParams cvA.type = cvA.type := by
      conv => lhs; rw [hrange]
      exact posOf_range cv.levelParams.length cvA.type
    have hval_pos : posOf cvA.levelParams value' = value' := by
      rw [hcv_lps]; conv => lhs; rw [hrange]
      exact posOf_range cv.levelParams.length value'
    rw [hty_pos] at hty_rep0
    rw [hval_pos] at hV
    have hlvl_ty0 : cvA.type.allLevelParamsDefined (List.range cv.levelParams.length) = true :=
      validate_expr_well_scoped_spec hnl (hty_rep0 0 zeroGhost) ev861
    have hlvl_ty : cvA.type.allLevelParamsDefined cv.levelParams = true := by
      rw [← hrange] at hlvl_ty0; exact hlvl_ty0
    have e_m954 : Heap.Extends cl.heap m954 :=
      hm954 ▸ (e_sc1.trans e_sc2).trans (heap_extends_append m886 _)
    have htypes954 : TypesRep c.κ zeroGhost m954 0 (.ptr (.enum kexprListEnum) m886.length) :=
      hm954 ▸ typesRep_alloc_nil c.κ zeroGhost m886
    obtain ⟨stype, u, _, hinf_ty, hred_ty, _, _⟩ :=
      core_ensure_sort hCore (hrc.mono e_m954) htypes954 (ghostScoped_zero zeroGhost) hef hlf
        (hgood_c.sub fun x hx => hsub x (hcs933 x hx)) ev935
        ((hty_rep0 0 zeroGhost).toTm.mono e_m954)
    have hty'_nfv : cvA.type.hasFvar = false := Tm.hasFvar_false (hty_rep0 0 zeroGhost).toTm
    have hty'_bvs : cvA.type.looseBVarsBounded 0 = true :=
      (hty_rep0 0 zeroGhost).toTm.looseBVarsBounded
    have hcv_run : ConstantValRunJ rulesJ env cv cvA.type :=
      ⟨by rw [hfresh_cv]; rfl, hres, hnoprj, levelParam_nodup_of_perm_range hperm,
        annotates_looseBVarsBounded hann_ty hty'_bvs,
        annotates_hasFvar_false hann_ty hty'_nfv,
        annot_of_annotates hann_ty, hlvl_ty,
        infer_constsResolve hinf_ty hty'_nfv, stype, u, hinf_ty, hred_ty⟩
    have e_pre_chk : Heap.Extends cl.heap m997 :=
      e_m954.trans ((ObsFn.heap_extends ev935).trans
        ((ObsFn.heap_extends ev979).trans (ObsFn.heap_extends ev1009)))
    have hv_run : ValueFrontRunJ rulesJ env cv value cvA.type value' :=
      valueFrontRunJ_of_front hCore hrange rfl hnl hty_rep0 hV hann_val e_sc1 e_pre_chk
        hrc hef hlf
        (hgood_c.sub fun x hx => hsub x (hcs896 x hx))
        (hgood_c.sub fun x hx => hsub x (hcs1029 x hx))
        ev898 hm1058 ev1031
    have hfresh_ci : env.find? (ConstantInfo.axiomInfo cvA).name = none := by
      show env.find? cvA.name = none
      rw [hcv_name]; exact hfresh_cv
    refine ⟨⟨.axiomInfo cvA :: env.consts⟩,
      installStep_single hinst_eq hstored hfresh_ci, ?_⟩
    show DeclOpaqueRunJ rulesJ env cv value ⟨.axiomInfo cvA :: env.consts⟩
    refine ⟨cvA.type, value', hcv_run, hv_run, ?_⟩
    rw [← hcvA_eq]

/-- Step preservation for `.quotDecl k cv` (`.type` installs the pinned quotient block; `.ctor`,
`.lift`, `.ind` install nothing). -/
theorem quotDecl_step {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {k : Ix.Kernel.QuotKind} {cv : ConstantVal .anon}
    (hx : DeclValueExtraFacts calls env (.quotDecl k cv)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.quotDecl k cv) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  cases k with
  | type =>
    obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .quotDecl .type cv) .quotK rfl
      (fun _ => hx.quotEqStored (Or.inl ⟨cv, rfl⟩)) hx.installsFresh
    exact ⟨⟨BasisKind.quotK.declsA.reverse ++ env.consts⟩, hinst,
      fun _ _ hInv => hInv.step_declRunJ hrun⟩
  | ctor => exact ⟨env, installStep_empty rfl, fun _ _ h => h⟩
  | lift => exact ⟨env, installStep_empty rfl, fun _ _ h => h⟩
  | ind => exact ⟨env, installStep_empty rfl, fun _ _ h => h⟩

/-- Step preservation for `.basisDecl kind`. -/
theorem basisDecl_step {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {kind : BasisKind}
    (hx : DeclValueExtraFacts calls env (.basisDecl kind)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.basisDecl kind) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .basisDecl kind) kind rfl
    (fun hk => hx.quotEqStored (Or.inr (Or.inl (hk ▸ rfl)))) hx.installsFresh
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩, hinst,
    fun _ _ hInv => hInv.step_declRunJ hrun⟩

/-- Step preservation for pinned `.indDecl block nP` (`basisPinHit block = some kind`). -/
theorem pinnedIndDecl_step {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {kind : BasisKind}
    (hpin : Ix.Kernel.basisPinHit block = some kind)
    (hx : DeclValueExtraFacts calls env (.indDecl block nP)) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  have hinst_eq : IxVM.Consistency.installs (.indDecl block nP) = kind.declsA := by
    simp [IxVM.Consistency.installs, hpin]
  obtain ⟨hrun, hinst⟩ := basis_step_of_fresh (d := .indDecl block nP) kind hinst_eq
    (fun hk => hx.quotEqStored (Or.inr (Or.inr ⟨block, nP, rfl, hk ▸ hpin⟩)))
    (hinst_eq ▸ hx.installsFresh)
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP)
      ⟨kind.declsA.reverse ++ env.consts⟩ := by
    simp only [DeclRunJ, hpin]
    exact hrun
  exact ⟨⟨kind.declsA.reverse ++ env.consts⟩, hinst,
    fun _ _ hInv => hInv.step_declRunJ hdecl⟩

/-- Unified step preservation across all non-inductive declarations and pinned inductive blocks,
leaving only unpinned `.indDecl` (`basisPinHit block = none`) for the modeled and native inductive
routes. -/
theorem valueOrPinnedDecl_step (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hchk : S0.Checked calls env d)
    (hx : DeclValueExtraFacts calls env d)
    (hind : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∃ env₂, IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
        ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂) :
    ∃ env₂, IxVM.Consistency.InstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  cases d with
  | axiomDecl cv => exact axiomDecl_step hCore hchk hx
  | defnDecl cv value hint => exact defnDecl_step hCore hchk hx
  | thmDecl cv value => exact thmDecl_step hLevels hCore hchk hx
  | opaqueDecl cv value => exact opaqueDecl_step hCore hchk hx
  | quotDecl k cv => exact quotDecl_step hx
  | basisDecl kind => exact basisDecl_step hx
  | indDecl block nP =>
    cases hpin : Ix.Kernel.basisPinHit block with
    | some kind => exact pinnedIndDecl_step hpin hx
    | none => exact hind block nP rfl hpin

end IxVM.Refinement.Decl
