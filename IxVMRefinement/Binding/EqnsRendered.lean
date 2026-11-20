import IxVMRefinement.Binding.RenderedArms
import IxVMRefinement.Binding.EqnsKit

/-! # Rendered equation and anchor specifications (`KernelRoleSpec::role_type`, `eqns_*`)

Proves that the rendered specification functions for equation-specified roles and their
associated anchors return exact kernel terms (including exact `BinderMeta`) matching
`Ix.Kernel.Role.spec`. -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)

/-! ## Exact reading (preserving `BinderMeta`) -/

/-- Exact version of `armReadsAs`: checks `T == T₀` (including `BinderMeta`), not just `erasePw`. -/
def armReadsExact (arms : List (Generic.Pattern F × Generic.Expr F)) (key : Nat)
    (T₀ : KExpr) : Bool :=
  match litArmBody key arms with
  | none => false
  | some e =>
    match readExpr readDepth [("tbl", .table)] e with
    | some (.tm T _) => closedBelow 0 T && (T == T₀)
    | _ => false

theorem rendersExact_of_armReadsExact {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {arms : List (Generic.Pattern F × Generic.Expr F)} {key : F} {T₀ : KExpr}
    (hread : armReadsExact arms (ZMod.val key) T₀ = true)
    {x_tbl : SourceValue F} {locals : Environment F Nat}
    (hloc : List.find? (fun p => p.1 == "tbl") locals = some ("tbl", x_tbl))
    {h : Heap F} {res : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    {bs : Environment F Nat} {body : Generic.Expr F}
    (htbl : TableRep t h x_tbl)
    (sel : selectArm W [] h (.field key) arms = Except.ok (some (bs, body)))
    (dArm : ObsExpr W [] (bs ++ locals) body h res h' cs) :
    Heap.Extends h h' ∧ Decl.TmCExact (keyOf t) h' T₀ res ∧
      (∀ x, AddrIn h' res x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
        ∀ P, T₀.constsResolveBy P = true → P (Ix.Kernel.Key.role s) = true) := by
  unfold armReadsExact at hread
  cases hb : litArmBody (ZMod.val key) arms with
  | none => simp [hb] at hread
  | some e =>
    cases hre : readExpr readDepth [("tbl", .table)] e with
    | none => simp [hb, hre] at hread
    | some s =>
      cases s with
      | tm T _ =>
        simp only [hb, hre, Bool.and_eq_true, beq_iff_eq] at hread
        obtain ⟨hcl, rfl⟩ := hread
        obtain ⟨hbs, hbody⟩ := selectArm_litArmBody hb sel
        subst hbs
        rw [hbody] at dArm
        have henv : EnvReads t h [("tbl", .table)] locals := by
          intro x r hx
          have hx' : (if "tbl" = x then some Rendered.table else none) = some r := hx
          by_cases hxt : "tbl" = x
          · rw [ite_eq_left hxt] at hx'
            cases hx'
            subst hxt
            exact ⟨x_tbl, hloc, .table htbl⟩
          · rw [ite_eq_right hxt] at hx'
            cases hx'
        obtain ⟨x1, rd⟩ := readExpr_sound htwf readDepth hre henv dArm
        cases rd with
        | tm rep _ cells _ =>
          exact ⟨x1, fun d Γ => rep d Γ 0 hcl, cells h' (Heap.Extends.refl _)⟩
      | _ => simp [hb, hre] at hread

theorem keyed_rendersExact {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {arms : List (Generic.Pattern F × Generic.Expr F)} {r : Role} {k : Nat} (hk : k < 64)
    {T₀ : KExpr} (hread : armReadsExact arms (64 * r.idx + k) T₀ = true)
    {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (d0 : ObsExpr W []
      (["tbl", "r", "k"].zip [x_tbl, .field (roleNum r), .field ((k : Nat) : F)])
      (.matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k")) arms)
      h res h' cs) :
    Heap.Extends h h' ∧ Decl.TmCExact (keyOf t) h' T₀ res ∧
      (∀ x, AddrIn h' res x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
        ∀ P, T₀.constsResolveBy P = true → P (Ix.Kernel.Key.role s) = true) := by
  obtain ⟨bs, body, cs', sel, dArm⟩ :=
    keyed_match_inv (a := roleNum r) (b := ((k : Nat) : F)) (by simp) (by simp) d0
  have hread' : armReadsExact arms (ZMod.val (64 * roleNum r + ((k : Nat) : F))) T₀ = true := by
    rw [val_key r hk]
    exact hread
  exact rendersExact_of_armReadsExact htwf hread' (by simp) htbl sel dArm

/-! ## Exact specified types for equation roles and their anchors -/

def roleTypeExactArmsRead : Bool :=
  Role.all.all fun r =>
    if isEqnsOrAnchorRole r then
      match roleTypeExact r with
      | none => false
      | some T₀ => armReadsExact (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body) r.idx T₀
    else true

set_option maxRecDepth 1000000 in
theorem roleTypeExactArmsRead_true : roleTypeExactArmsRead = true := by decide +kernel

/-- **`KernelRoleSpec::role_type(tbl, r)` builds the exact annotated type `T₀`** for every
role in `59..102`. -/
theorem roleTypeExactRenders {t : Ix.Kernel.RoleTable} {r : Role} {T₀ : KExpr}
    (hr : isEqnsOrAnchorRole r = true) (hspec : roleTypeExact r = some T₀) (htwf : t.wf = true)
    {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)} (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::role_type" [x_tbl, .field (roleNum r)] h res h' cs) :
    Heap.Extends h h' ∧ Decl.TmCExact (keyOf t) h' T₀ res ∧
      (∀ x, AddrIn h' res x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
        ∀ P, T₀.constsResolveBy P = true → P (Ix.Kernel.Key.role s) = true) := by
  have hall := List.all_eq_true.mp roleTypeExactArmsRead_true r (Role.mem_all r)
  simp only [hr, ↓reduceIte, hspec] at hall
  have hread : armReadsExact (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body)
      (ZMod.val (roleNum r)) T₀ = true := by
    rw [RolesAux.val_roleNum]; exact hall
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_type.lookup
    role_type_noControl ev
  have hp : (IxVM.KernelRoleSpec.role_type.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_type.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨vr, m0, bs, body, _, _, dScrut, sel, dArm, -⟩ := d0.matchValue_inv
  obtain ⟨lr, hm0, -⟩ := dScrut.var_inv
  simp at lr
  subst vr; subst m0
  exact rendersExact_of_armReadsExact htwf hread (by simp) htbl sel dArm

/-! ## `eqns_lhs` and `eqns_rhs` -/

def eqnsSideArmsRead (arms : List (Generic.Pattern F × Generic.Expr F))
    (side : Ix.Kernel.Equation .anon → KExpr) : Bool :=
  Role.all.all fun r =>
    allIdx (fun k e =>
      if e.hyps.isEmpty then
        decide (k < 64) && armReadsExact arms (64 * r.idx + k) (eqnsSideExact e (side e))
      else true) 0 (eqnsOfRole r)

theorem eqnsSide_read {arms : List (Generic.Pattern F × Generic.Expr F)}
    {side : Ix.Kernel.Equation .anon → KExpr} (hall : eqnsSideArmsRead arms side = true)
    {r : Role} {k : Nat} {e : Ix.Kernel.Equation .anon}
    (hget : (eqnsOfRole r)[k]? = some e) (huncond : e.hyps.isEmpty = true) :
    k < 64 ∧ armReadsExact arms (64 * r.idx + k) (eqnsSideExact e (side e)) = true := by
  have hr := List.all_eq_true.mp hall r (Role.mem_all r)
  have hk := allIdx_get hr hget
  simp only [Nat.zero_add, huncond, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hk
  exact hk

set_option maxRecDepth 100000 in
theorem eqns_lhs_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.eqns_lhs.body = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem eqns_rhs_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.eqns_rhs.body = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem eqnsLhsArmsRead_true :
    eqnsSideArmsRead (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_lhs.body)
      (fun e => e.lhs) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem eqnsRhsArmsRead_true :
    eqnsSideArmsRead (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_rhs.body)
      (fun e => e.rhs) = true := by decide +kernel

/-- **`KernelRoleSpec::eqns_lhs(tbl, r, k)` builds the exact closed left side** of an
unconditional equation. -/
theorem eqnsLhsExactRenders {t : Ix.Kernel.RoleTable} {r : Role} {k : Nat}
    {e : Ix.Kernel.Equation .anon} (hget : (eqnsOfRole r)[k]? = some e)
    (huncond : e.hyps.isEmpty = true) (htwf : t.wf = true)
    {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)} (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::eqns_lhs" [x_tbl, .field (roleNum r), .field ((k : Nat) : F)]
      h res h' cs) :
    Heap.Extends h h' ∧ Decl.TmCExact (keyOf t) h' (eqnsSideExact e e.lhs) res ∧
      (∀ x, AddrIn h' res x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
        ∀ P, (eqnsSideExact e e.lhs).constsResolveBy P = true → P (Ix.Kernel.Key.role s) = true) := by
  obtain ⟨hk, hread⟩ := eqnsSide_read eqnsLhsArmsRead_true hget huncond
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.eqns_lhs.lookup
    eqns_lhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.eqns_lhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.eqns_lhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_lhs.body) := rfl
  rw [hp, hb] at d0
  exact keyed_rendersExact htwf hk hread htbl d0

/-- **`KernelRoleSpec::eqns_rhs(tbl, r, k)` builds the exact closed right side** of an
unconditional equation. -/
theorem eqnsRhsExactRenders {t : Ix.Kernel.RoleTable} {r : Role} {k : Nat}
    {e : Ix.Kernel.Equation .anon} (hget : (eqnsOfRole r)[k]? = some e)
    (huncond : e.hyps.isEmpty = true) (htwf : t.wf = true)
    {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)} (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::eqns_rhs" [x_tbl, .field (roleNum r), .field ((k : Nat) : F)]
      h res h' cs) :
    Heap.Extends h h' ∧ Decl.TmCExact (keyOf t) h' (eqnsSideExact e e.rhs) res ∧
      (∀ x, AddrIn h' res x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
        ∀ P, (eqnsSideExact e e.rhs).constsResolveBy P = true → P (Ix.Kernel.Key.role s) = true) := by
  obtain ⟨hk, hread⟩ := eqnsSide_read eqnsRhsArmsRead_true hget huncond
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.eqns_rhs.lookup
    eqns_rhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.eqns_rhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.eqns_rhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_rhs.body) := rfl
  rw [hp, hb] at d0
  exact keyed_rendersExact htwf hk hread htbl d0

/-! ## `eqns_statement` -/

def eqnsStmtArmsRead : Bool :=
  Role.all.all fun r =>
    allIdx (fun k e => decide (k < 64) &&
      armReadsExact (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_statement.body)
        (64 * r.idx + k) (eqnsStmtExact e)) 0 (eqnsOfRole r)

set_option maxRecDepth 100000 in
theorem eqns_statement_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.eqns_statement.body = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem eqnsStmtArmsRead_true : eqnsStmtArmsRead = true := by decide +kernel

/-- **`KernelRoleSpec::eqns_statement(tbl, r, k)` builds the exact closed equation statement.** -/
theorem eqnsStatementExactRenders {t : Ix.Kernel.RoleTable} {r : Role} {k : Nat}
    {e : Ix.Kernel.Equation .anon} (hget : (eqnsOfRole r)[k]? = some e) (htwf : t.wf = true)
    {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)} (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::eqns_statement"
      [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h res h' cs) :
    Heap.Extends h h' ∧ Decl.TmCExact (keyOf t) h' (eqnsStmtExact e) res ∧
      (∀ x, AddrIn h' res x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
        ∀ P, (eqnsStmtExact e).constsResolveBy P = true → P (Ix.Kernel.Key.role s) = true) := by
  have hr := List.all_eq_true.mp eqnsStmtArmsRead_true r (Role.mem_all r)
  have hk := allIdx_get hr hget
  simp only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq] at hk
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.eqns_statement.lookup
    eqns_statement_noControl ev
  have hp : (IxVM.KernelRoleSpec.eqns_statement.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.eqns_statement.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_statement.body) := rfl
  rw [hp, hb] at d0
  exact keyed_rendersExact htwf hk.1 hk.2 htbl d0

/-! ## `eqns_conditional` and `eqns_equation_count` -/

def eqnsCondTableOk : Bool :=
  Role.all.all fun r =>
    allIdx (fun k e => decide (k < 64) &&
      (RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_conditional.body)
        ((64 * r.idx + k : Nat) : F) == some (if e.hyps.isEmpty then 0 else 1))) 0 (eqnsOfRole r)

set_option maxRecDepth 100000 in
theorem eqns_conditional_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.eqns_conditional.body = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem eqnsCondTableOk_true : eqnsCondTableOk = true := by decide +kernel

/-- **`KernelRoleSpec::eqns_conditional(r, k)`** returns `0` for an unconditional equation and
`1` for a conditional one. -/
theorem eqns_conditional_spec {r : Role} {k : Nat} {e : Ix.Kernel.Equation .anon}
    (hget : (eqnsOfRole r)[k]? = some e) {h h' : Heap F} {res : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::eqns_conditional" [.field (roleNum r), .field ((k : Nat) : F)]
      h res h' cs) :
    res = .field (if e.hyps.isEmpty then 0 else 1) ∧ h' = h := by
  have hr := List.all_eq_true.mp eqnsCondTableOk_true r (Role.mem_all r)
  have hk := allIdx_get hr hget
  simp only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.eqns_conditional.lookup
    eqns_conditional_noControl ev
  have hp : (IxVM.KernelRoleSpec.eqns_conditional.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.eqns_conditional.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_conditional.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨bs, body, cs', sel, dArm⟩ :=
    keyed_match_inv (a := roleNum r) (b := ((k : Nat) : F)) (by simp) (by simp) d0
  have heqKey : (64 * roleNum r + ((k : Nat) : F) : F) = ((64 * r.idx + k : Nat) : F) := by
    unfold roleNum
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [heqKey] at sel
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable hk.2 sel
  obtain ⟨rfl, rfl, -⟩ := dArm.literal_inv
  exact ⟨rfl, rfl⟩

/-- Every role's `eqns_equation_count` matches `(eqnsOfRole r).length`. -/
def eqnsCountTableOk : Bool :=
  Role.all.all fun r =>
    RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body)
      (roleNum r) == some ((eqnsOfRole r).length : F)

set_option maxRecDepth 100000 in
theorem eqns_equation_count_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.eqns_equation_count.body = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem eqnsCountTableOk_true : eqnsCountTableOk = true := by decide +kernel

/-- **`KernelRoleSpec::eqns_equation_count(r)`** returns `(eqnsOfRole r).length`. -/
theorem eqns_equation_count_exact (r : Role) {h h' : Heap F} {res : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::eqns_equation_count" [.field (roleNum r)] h res h' cs) :
    res = .field ((eqnsOfRole r).length : F) ∧ h' = h := by
  have hr := beq_iff_eq.mp (List.all_eq_true.mp eqnsCountTableOk_true r (Role.mem_all r))
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.eqns_equation_count.lookup
    eqns_equation_count_noControl ev
  have hp : (IxVM.KernelRoleSpec.eqns_equation_count.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.eqns_equation_count.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨v1, m2, bs, body, _, _, d7, sel, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable hr sel
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

end IxVM.Refinement.Binding
