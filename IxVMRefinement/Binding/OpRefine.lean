import IxVMRefinement.Binding.OpInstall
import IxVMRefinement.Decl.DeclWalkedConst
import IxVMRefinement.RoleOps.Producers

/-! # An operation's check facts from the circuit's validation (`KernelRoles::validate_op`)

The operations lane's interface (`RoleOps.OpChecked`) has a prefix half and a check half. This
file produces both at the environment `env` the closure of the operation's group leaves, the
boundary invariant below the group holding there.

* `opPrefix_of_bnd`, `wfPrefix_of_bnd`: **the prefix half from the boundary invariant alone**:
  the operation is not stored yet (`BoundaryFacts.opsAdmitted`), `Nat` literals are supported (the
  companions at the group's limit), the operations it depends on are stored as pinned (their
  groups are earlier: `TableShape.kept` and `BoundaryFacts.opsPinned`), `Bool` has its shapes (group 6,
  `Shapes.bool`), and `Eq` is the pinned basis constant (`TableShape.pins`).
* `opFront_of_checked`: **the definition's check from the walked check of the operation's
  record** (`KernelClaim::run_check_transitive(rc, a)` in `validate_op`): the evidence of
  `check_const`'s definition arm (`Decl.CheckedConstOriginAt.defnDecl`, at any list of role
  addresses, so at the operation's own) gives `OpFront` at `env` through
  `scoped_core_ensure_sort` and `scoped_core_check`.
* `eqs_of_obs`: **one recurrence from its comparison** (`k_is_def_eq(rc, L, R, types) = 1` in
  `validate_op_equations`' definitional arm), the two sides represented at depth 2 as the
  recurrence's sides with the operation replaced by its value (`EqObs`), through
  `scoped_core_defeq`.
* `certFacts_of_obs`: **one certificate from its check** (`k_check(rc, P x y h…, E, types)` in
  the proof arm), the applied proof and the opened equation represented at depth `2 + n`
  (`CertObs`), through `scoped_core_check` and `RoleOps.CertFacts.of_frame`.
* `opChecked_struct`, `opChecked_wf`: the two families assembled.

What the observations (`EqObs`, `CertObs`) and the pinned shape (`OpTyShape`) still take from
the circuit is the representation of the rendered specification terms (`role_type`,
`op_equation_lhs`/`op_equation_rhs` and `op_certificate` of `KernelRoleSpec`, which
`Binding/RenderedArms.lean` reads off their syntax trees) opened (`open_two_lams`,
`open_foralls`) and substituted (`subst_const`), and the applied proof (`apply_spine`,
`bvars_desc`).
-/

universe u

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Binding.OpRefine

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding
open IxVM.Refinement.Binding.OpInstall
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Ix.Kernel (natOpNames natDivModNames natOpEquations divModCertStmts divModCertApplied)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

/-! ## A stored constant is found under its name -/

theorem find?_of_mem_nodup :
    ∀ (cs : List (Ix.Kernel.ConstantInfo .anon)) (ci : Ix.Kernel.ConstantInfo .anon),
      ci ∈ cs → (cs.map (·.name)).Nodup → (⟨cs⟩ : Ix.Kernel.Env .anon).find? ci.name = some ci
  | [], ci, hm, _ => by cases hm
  | c :: cs, ci, hm, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [Ix.Kernel.Env.find?_cons (env := ⟨cs⟩)]
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact ite_eq_left rfl
    · have hne : c.name ≠ ci.name := fun he => hnd.1 (he ▸ List.mem_map.mpr ⟨ci, hm', rfl⟩)
      rw [ite_eq_right hne]
      exact find?_of_mem_nodup cs ci hm' hnd.2

/-! ## The prefix half, from the boundary invariant -/

set_option maxRecDepth 100000 in
private theorem basic_groups :
    Ix.SpecDigest.groupOf .nat < 7 ∧ Ix.SpecDigest.groupOf .natZero < 7 ∧
      Ix.SpecDigest.groupOf .natSucc < 7 ∧ Ix.SpecDigest.groupOf .bool < 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The operations an operation's recurrences involve are of earlier groups** (decided over
the fifteen). -/
theorem deps_earlier : ∀ r ∈ RoleOps.opRoles, ∀ r' ∈ RoleOps.opRoles,
    (Ix.Kernel.Key.role r' : Core.KKey) ∈ Ix.Kernel.natOpDeps (Ix.Kernel.Key.role r : Core.KKey) →
      r' ≠ r → Ix.SpecDigest.groupOf r' < Ix.SpecDigest.groupOf r := by
  decide +kernel

/-- An operation's group is past the basis and `Bool`'s groups, and its limit is at least 7. -/
theorem op_valLimit {r : Ix.Kernel.Role} (hop : r ∈ RoleOps.opRoles) :
    7 ≤ valLimit (Ix.SpecDigest.groupOf r) := by
  show 7 ≤ RoleVal.groupValLimit (Ix.SpecDigest.groupOf r)
  unfold RoleVal.groupValLimit
  rcases op_group hop with ⟨h7, h33⟩ | ⟨h33, h40⟩ <;> split_ifs <;> omega

/-- **The prefix half of an operation's check, from the boundary invariant below its group.** -/
theorem opPrefix_of_bnd
    {L : Ix.Kernel.Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {r : Ix.Kernel.Role} (hall : AllBound t) (hgrp : roleGroup g = [r])
    (hop : r ∈ RoleOps.opRoles) (hb : BndOver.{u} L t (· < g) R env) :
    RoleOps.OpPrefix env (.role r) := by
  have hrg : r ∈ roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := groupOf_of_mem_roleGroup hrg
  have hopN : (Ix.Kernel.Key.role r : Core.KKey) ∈ RoleOps.opNames := by
    rw [RoleOps.opNames_eq_map]
    exact List.mem_map.mpr ⟨r, hop, rfl⟩
  obtain ⟨hN, hZ, hS, hB⟩ := basic_groups
  have h7 := op_valLimit hop
  rw [hgr] at h7
  have hg7 : 7 ≤ g := Nat.le_trans h7 (valLimit_le g)
  -- fresh: an operation is stored only once its group is admitted
  have hfresh : env.find? (Ix.Kernel.Key.role r) = none := by
    cases hf : env.find? (Ix.Kernel.Key.role r) with
    | none => rfl
    | some ci =>
      have hlt := hb.facts.opsAdmitted r hop (by rw [hf]; rfl)
      exact absurd (hgr ▸ hlt) (Nat.lt_irrefl g)
  -- `Nat` literals: the companions at the group's limit
  obtain ⟨E, hE⟩ := recordsFor_exists hb.shape.committed
  have hinv := hb.inv hE (carried_valLimit g) (limWithin_below t g)
  have hforce : ∀ X : Ix.Kernel.Role, Ix.SpecDigest.groupOf X < 7 →
      Core.Ctx.inForce ⟨E, env, t, some (valLimit g)⟩ X := fun X hX =>
    ⟨hall X, fun n hn => by
      obtain rfl := Option.some.inj hn
      omega⟩
  have hnat : Ix.Kernel.natLitSupported env = true :=
    hinv.companions.natLit (hforce _ hN) (hforce _ hZ) (hforce _ hS)
  -- `Bool`'s shapes: group 6
  obtain ⟨hbp, hbc, hbt⟩ := hb.facts.shapes.bool (by omega)
  refine RoleOps.OpPrefix.of_pinned hb.facts.opsPinned hopN hfresh hnat (fun n hn hne => ?_)
    (fun _ => hbc) (fun _ => hbp)
  have hnN := RoleOps.natOpDeps_sub_opNames hopN hn
  rw [RoleOps.opNames_eq_map] at hnN
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hnN
  have hne' : r' ≠ r := fun e => hne (by rw [e])
  have hlt : Ix.SpecDigest.groupOf r' < g := hgr ▸ deps_earlier r hop r' hr' hn hne'
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall r')
  obtain ⟨ci, hci, -⟩ := hb.shape.kept _ r' a' hlt (role_mem_roleGroup r') (op_kept hr').1 ha'
  show (env.find? (Ix.Kernel.Key.role r')).isSome = true
  rw [hci]
  rfl

/-- **The prefix half of a well-founded operation's check, from the boundary invariant.** -/
theorem wfPrefix_of_bnd
    {L : Ix.Kernel.Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {r : Ix.Kernel.Role} (hall : AllBound t) (hgrp : roleGroup g = [r])
    (hop : r ∈ RoleOps.opRoles) (hb : BndOver.{u} L t (· < g) R env) :
    RoleOps.WfPrefix env (.role r) := by
  have hrg : r ∈ roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := groupOf_of_mem_roleGroup hrg
  obtain ⟨-, -, -, hB⟩ := basic_groups
  have h7 := op_valLimit hop
  rw [hgr] at h7
  have hg7 : 7 ≤ g := Nat.le_trans h7 (valLimit_le g)
  obtain ⟨-, -, hbt⟩ := hb.facts.shapes.bool (by omega)
  have hmem : (Ix.Kernel.eqA : Ix.Kernel.ConstantInfo .anon) ∈ env.consts :=
    hb.shape.pins .eqK _ (List.Mem.head _)
  have heq := find?_of_mem_nodup env.consts _ hmem hb.shape.reading.nodup
  exact ⟨opPrefix_of_bnd hall hgrp hop hb, heq, hbt⟩

/-! ## The definition's check, from the walked check of the record -/

section Front

private theorem tm_noLetExpr {κ : _root_.Address → Core.KKey} {d : Nat} {Γ : Nat → Core.KExpr}
    {h : Aiur.Heap F} {k : Nat} {E : Core.KExpr} {p : SourceValue F}
    (hΓ : ∀ j, j < d → Decl.noLetExpr (Γ j) = true)
    (rep : Core.Tm κ d Γ h k E p) :
    Decl.noLetExpr E = true := by
  induction rep with
  | bvarLocal => rfl
  | @bvarFree k₀ _ i _ _ hk hd =>
    exact hΓ (Core.fvIdx d k₀ (ZMod.val i)) (by unfold Core.fvIdx; omega)
  | sort | const | litNat | litStr => rfl
  | app _ _ _ ihf iha => simp only [Decl.noLetExpr, ihf, iha]; rfl
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp only [Decl.noLetExpr, iht, ihb]; rfl
  | letE _ _ _ _ _ ihv ihb => exact Decl.noLetExpr_instShift ihv 0 ihb
  | proj _ _ _ ihe => exact ihe

/-- A closed represented term has no `let`, no opened variable, is closed and is its own
annotation. -/
theorem tmC_props {κ : _root_.Address → Core.KKey} {h : Aiur.Heap F}
    {e : Core.KExpr} {p : SourceValue F} (rep : Core.TmC κ h e p) :
    Decl.noLetExpr e = true ∧ e.hasFvar = false ∧ e.looseBVarsBounded 0 = true ∧
      Annot 0 e e := by
  have h0 : Core.Tm κ 0 (fun _ => .sort .zero) h 0 e p := rep 0 (fun _ => .sort .zero)
  have hnl : Decl.noLetExpr e = true :=
    tm_noLetExpr (fun _ hlt => absurd hlt (Nat.not_lt_zero _)) h0
  have hfv : e.hasFvar = false := Decl.Tm.hasFvar_false h0
  have hbvs : e.looseBVarsBounded 0 = true := Core.Tm.looseBVarsBounded h0
  exact ⟨hnl, hfv, hbvs, Decl.annot_refl_of_noLetExpr hnl hfv hbvs 0⟩

private theorem typesRep_nil (κ : _root_.Address → Core.KKey) (Γ : Nat → Core.KExpr)
    {m m_pre : Aiur.Heap F}
    (hm : m = m_pre ++
      [.construct IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) :
    Core.TypesRep κ Γ m 0
      (.ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre.length) := by
  rw [hm]
  exact Decl.typesRep_alloc_nil κ Γ m_pre

/-- **The definition's check of an operation's record, from the walked check of the record**:
the evidence of `check_const`'s definition arm at the prefix's keying (any list of role
addresses), with no level parameter, gives `OpFront` at the prefix, the stored terms being their
own annotations, and the stored terms annotate the declared ones. -/
theorem opFront_of_checked {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {E : Ixon.Env} {order_role : List _root_.Address} {lim : Nat}
    {env : Ix.Kernel.Env .anon} {d d' : Ix.Kernel.Declaration .anon} {k : Core.KKey}
    {ty₀ val₀ ty val : Core.KExpr} {hn : Ix.Kernel.ReducibilityHint}
    (hinv : Decl.PrefixInv.{u} E t (some lim) env)
    (hchk : Decl.CheckedConstOriginAt (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ lim calls t
      bAddr E order_role d d')
    (hgood : Core.Good ⟨E, env, t, none⟩ calls)
    (hd : d = .defnDecl ⟨k, [], ty₀⟩ val₀ hn) (hd' : d' = .defnDecl ⟨k, [], ty⟩ val hn) :
    RoleOps.OpFront env ty val ty val ∧ Annotates ty ty₀ ∧ Annotates val val₀ := by
  cases hchk with
  | axiomDecl => cases hd'
  | thmDecl => cases hd'
  | opaqueDecl => cases hd'
  | @defnDecl a nlvls ty₀' val₀' ty' val' hn' m_pre1 m_es m_es' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann hty'_def hval'_def
      hm_es hty_tmc_es hrc_es ev_es _ hsub_es
      _ hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc _ hsub_kc =>
    simp only [Ix.Kernel.Declaration.defnDecl.injEq, Ix.Kernel.ConstantVal.mk.injEq] at hd hd'
    obtain ⟨⟨-, -, e1⟩, e2, -⟩ := hd
    obtain ⟨⟨-, hl, e3⟩, e4, -⟩ := hd'
    subst e1
    subst e2
    subst e3
    subst e4
    have hn0 : nlvls = 0 := by
      cases nlvls with
      | zero => rfl
      | succ n => exact absurd hl (by simp [List.range_succ])
    subst hn0
    let c : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some lim⟩
    have hgood_c : Core.Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
    have hty_tmc_es' : Core.TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [Decl.posOf_range 0 ty'] at h
    have hty_tmc_kc' : Core.TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [Decl.posOf_range 0 ty'] at h
    have hval_tmc_kc' : Core.TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [Decl.posOf_range 0 val'] at h
    obtain ⟨-, hty_nfv, hty_bvs, hty_an⟩ := tmC_props hty_tmc_es'
    obtain ⟨-, hval_nfv, hval_bvs, hval_an⟩ := tmC_props hval_tmc_kc'
    obtain ⟨stype, u', _, hinf_ty, hred_ty, _, _⟩ :=
      Decl.scoped_core_ensure_sort (c := c) hrc_es.toRCRep (typesRep_nil c.κ _ hm_es)
        (Decl.ghostScoped_zero _) hef hlf
        (Core.CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 (fun _ => .sort .zero))
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      Decl.scoped_core_check (c := c) hrc_kc.toRCRep (typesRep_nil c.κ _ hm_kc)
        (Decl.ghostScoped_zero _) hef hlf
        (Core.CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 (fun _ => .sort .zero)) (hty_tmc_kc' 0 (fun _ => .sort .zero))
    exact ⟨⟨hty_bvs, hty_nfv, hty_an, hty'_def, ⟨stype, u', hinf_ty, hred_ty⟩,
      hval_bvs, hval_nfv, hval_an, hval'_def, ⟨vtype, hinf_val, hde_val⟩⟩, hty_ann, hval_ann⟩

end Front

/-! ## The recurrences and the certificates, from their comparisons -/

/-- **A comparison of one recurrence, as `validate_op_equations` makes it**: a successful
`k_is_def_eq` under the group's role context, at depth 2 under a scoped ghost context the
context list represents, of two terms that represent the recurrence's sides with the
operation replaced by `val`, in a run good for the store. -/
def EqObs (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Nat) (env : Ix.Kernel.Env .anon)
    (c : Core.KKey) (val : Core.KExpr) (eq : Core.KExpr × Core.KExpr) : Prop :=
  ∃ (Γ : Nat → Core.KExpr) (rc types lp rp : SourceValue F) (h h' : Aiur.Heap F)
    (cs : List (Call F)),
    Core.RCRep t (some lim) h rc ∧
    Core.TypesRep (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ Γ h 2 types ∧
    Core.GhostScoped Γ 2 ∧
    ObsFn Core.W "KernelDefEq::k_is_def_eq" [rc, lp, rp, types] h (.field 1) h' cs ∧
    Core.Good ⟨E, env, t, none⟩ cs ∧
    Core.Tm (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ 2 Γ h 0
      (Ix.Kernel.Expr.substConst0 c val eq.1) lp ∧
    Core.Tm (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ 2 Γ h 0
      (Ix.Kernel.Expr.substConst0 c val eq.2) rp

/-- **A recurrence, from its comparison.** -/
theorem eqs_of_obs {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Nat}
    {env : Ix.Kernel.Env .anon} {c : Core.KKey} {val : Core.KExpr}
    {eq : Core.KExpr × Core.KExpr} (hinv : Decl.PrefixInv.{u} E t (some lim) env)
    (h : EqObs E t lim env c val eq) :
    DefEq env 2 (Ix.Kernel.Expr.substConst0 c val eq.1) (Ix.Kernel.Expr.substConst0 c val eq.2) := by
  obtain ⟨Γ, rc, types, lp, rp, h₁, h₂, cs, hrc, hty, hsc, ev, hgood, hl, hr⟩ := h
  obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
  have hgood_c : Core.Good (Core.Ctx.stored ⟨E, env, t, some lim⟩).toCtx cs := hgood
  exact Decl.scoped_core_defeq (c := Core.Ctx.stored ⟨E, env, t, some lim⟩) hrc hty hsc hef hlf
    (Core.CoreGood.ofRaw hgood_c (fun _ _ => trivial)) ev hl hr

/-- **A check of one certificate, as `validate_op_equations` makes it**: a successful `k_check`
under the group's role context, at depth `2 + n` (`n` hypotheses) under a scoped ghost context the
context list represents, of a term that represents the proof applied to the statement's variables
against one that represents the statement's equation, the operation replaced by `val`. -/
def CertObs (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Nat) (env : Ix.Kernel.Env .anon)
    (c : Core.KKey) (val : Core.KExpr) (st : List Core.KExpr × Core.KExpr) (P : Core.KExpr) :
    Prop :=
  ∃ (Γ : Nat → Core.KExpr) (rc types ap ep r : SourceValue F) (h h' : Aiur.Heap F)
    (cs : List (Call F)),
    Core.RCRep t (some lim) h rc ∧
    Core.TypesRep (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ Γ h (2 + st.1.length) types ∧
    Core.GhostScoped Γ (2 + st.1.length) ∧
    ObsFn Core.W "KernelInfer::k_check" [rc, ap, ep, types] h r h' cs ∧
    Core.Good ⟨E, env, t, none⟩ cs ∧
    Core.Tm (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ (2 + st.1.length) Γ h 0
      (divModCertApplied P (st.1.map (Ix.Kernel.Expr.substConst0 c val))) ap ∧
    Core.Tm (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ (2 + st.1.length) Γ h 0
      (Ix.Kernel.Expr.substConst0 c val st.2) ep

/-- **One certificate, from its check**: the substituted proof closed, with no `let` and no level
parameter (`validate_expr_well_scoped(p, 0, 0)` on the result of `subst_const`), and the check
of the applied proof. -/
theorem certFacts_of_obs {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Nat}
    {env : Ix.Kernel.Env .anon} {c : Core.KKey} {val : Core.KExpr}
    {st : List Core.KExpr × Core.KExpr} {P : Core.KExpr}
    (hinv : Decl.PrefixInv.{u} E t (some lim) env) (hc : c ∈ natDivModNames)
    (hst : st ∈ divModCertStmts c) (hvf : val.hasFvar = false)
    (hcl : P.looseBVarsBounded 0 = true) (hnf : P.hasFvar = false)
    (hnl : Decl.noLetExpr P = true) (hlv : P.allLevelParamsDefined [] = true)
    (h : CertObs E t lim env c val st P) : RoleOps.CertFacts env c val st P := by
  obtain ⟨Γ, rc, types, ap, ep, r, h₁, h₂, cs, hrc, hty, hsc, ev, hgood, happ, heq⟩ := h
  obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
  have hgood_c : Core.Good (Core.Ctx.stored ⟨E, env, t, some lim⟩).toCtx cs := hgood
  have htyped := Decl.scoped_core_check (c := Core.Ctx.stored ⟨E, env, t, some lim⟩) hrc hty hsc
    hef hlf (Core.CoreGood.ofRaw hgood_c (fun _ _ => trivial)) ev happ heq
  exact RoleOps.CertFacts.of_frame hinv.store.store hc hst hvf hcl hnf hnl hlv htyped

/-! ## The two families -/

/-- **A structural operation's check facts at the closure's environment**: the prefix half from
the boundary invariant below its group, the definition's check from the walked check of the
record, the pinned shape, and one comparison per recurrence. -/
theorem opChecked_struct
    {L : Ix.Kernel.Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {r : Ix.Kernel.Role} {E : Ixon.Env} {lim : Nat} {ty val : Core.KExpr}
    (hall : AllBound t) (hgrp : roleGroup g = [r]) (hop : r ∈ RoleOps.opRoles)
    (hc : (Ix.Kernel.Key.role r : Core.KKey) ∈ natOpNames)
    (hb : BndOver.{u} L t (· < g) R env) (hinv : Decl.PrefixInv.{u} E t (some lim) env)
    (hfront : RoleOps.OpFront env ty val ty val) (hsh : RoleOps.OpTyShape (.role r) ty)
    (heqs : ∀ eq ∈ natOpEquations 0 (Ix.Kernel.Key.role r : Core.KKey),
      EqObs E t lim env (.role r) val eq) :
    RoleOps.OpChecked env (.role r) ty val ty val :=
  .struct hc (opPrefix_of_bnd hall hgrp hop hb)
    ⟨hfront, hsh, fun eq heq => eqs_of_obs hinv (heqs eq heq)⟩

/-- `Forall₂` with a membership hypothesis on the left. -/
theorem forall₂_of_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a ∈ l₁, ∀ b, R a b → S a b) →
      List.Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h rest, H =>
    .cons (H _ (List.Mem.head _) _ h)
      (forall₂_of_mem rest fun a ha b hr => H a (List.Mem.tail _ ha) b hr)

/-- **A well-founded operation's check facts at the closure's environment**: the prefix half
from the boundary invariant below its group, the definition's check, the pinned shape, and per
certificate statement a proof term, closed, with no `let` and no level parameter, with its
check. -/
theorem opChecked_wf
    {L : Ix.Kernel.Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {r : Ix.Kernel.Role} {E : Ixon.Env} {lim : Nat} {ty val : Core.KExpr}
    (hall : AllBound t) (hgrp : roleGroup g = [r]) (hop : r ∈ RoleOps.opRoles)
    (hc : (Ix.Kernel.Key.role r : Core.KKey) ∈ natDivModNames)
    (hb : BndOver.{u} L t (· < g) R env) (hinv : Decl.PrefixInv.{u} E t (some lim) env)
    (hfront : RoleOps.OpFront env ty val ty val) (hsh : RoleOps.OpTyShape (.role r) ty)
    (hcerts : ∃ proofs : List Core.KExpr, List.Forall₂ (fun st P =>
      P.looseBVarsBounded 0 = true ∧ P.hasFvar = false ∧ Decl.noLetExpr P = true ∧
        P.allLevelParamsDefined [] = true ∧ CertObs E t lim env (.role r) val st P)
      (divModCertStmts (Ix.Kernel.Key.role r : Core.KKey)) proofs) :
    RoleOps.OpChecked env (.role r) ty val ty val := by
  obtain ⟨proofs, hp⟩ := hcerts
  refine .wf hc (wfPrefix_of_bnd hall hgrp hop hb) ⟨hfront, hsh, proofs, ?_⟩
  exact forall₂_of_mem hp fun st hst P ⟨hcl, hnf, hnl, hlv, hobs⟩ =>
    certFacts_of_obs hinv hc hst hfront.valNoFvar hcl hnf hnl hlv hobs

end IxVM.Refinement.Binding.OpRefine
