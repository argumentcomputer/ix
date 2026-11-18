import IxVMRefinement.Binding.RenderedRead

/-! # The rendered role specifications return the specified terms

`KernelRoleSpec::role_type`, `op_equation_lhs`, `op_equation_rhs` and `op_certificate` each
return, at every role (and every recurrence or certificate index), the term the kernel's
specification set declares, up to the binders' data: the four statements of
`Binding/RenderedSpecs.lean`, proved.

Each proof is the same two steps. The kernel evaluates the reader of `Binding/RenderedRead.lean`
over every arm of the function's `match` and compares what the arm reads as with the specified
term (`roleTypeArmsRead_true`, `opEquationLhsArmsRead_true`, `opEquationRhsArmsRead_true`,
`certArmsRead_true`); the reader's soundness turns that evaluation into the statement about the
observed call (`roleTypeRenders`, `opEquationLhsRenders`, `opEquationRhsRenders`,
`opCertificateRenders`). No generated evaluation path of the four functions is read.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)

/-! ## Lists read with positions -/

/-- A test of every element of a list with its position, counted from `i`. -/
def allIdx {α : Type} (p : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x :: xs => p i x && allIdx p (i + 1) xs

theorem allIdx_get {α : Type} {p : Nat → α → Bool} :
    ∀ {l : List α} {i k : Nat} {x : α},
      allIdx p i l = true → l[k]? = some x → p (i + k) x = true := by
  intro l
  induction l with
  | nil =>
    intro i k x _ hk
    simp at hk
  | cons y ys ih =>
    intro i k x ha hk
    simp only [allIdx, Bool.and_eq_true] at ha
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ha.1
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hk
      have h2 := ih ha.2 hk
      have e : i + (k' + 1) = i + 1 + k' := by omega
      rw [e]
      exact h2

/-! ## `role_type` -/

set_option maxRecDepth 100000 in
/-- The body of `role_type` raises no control. -/
theorem role_type_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.role_type.body = false := by decide +kernel

/-- Every role's arm of `role_type` reads as the role's specified type. -/
def roleTypeArmsRead : Bool :=
  Role.all.all fun r =>
    match specTypeRaw r with
    | none => true
    | some T₀ => armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body) r.idx T₀ 0

set_option maxRecDepth 1000000 in
theorem roleTypeArmsRead_true : roleTypeArmsRead = true := by decide +kernel

/-- **`KernelRoleSpec::role_type(tbl, r)` builds the role's specified type**, at every role. -/
theorem roleTypeRenders : RoleTypeRenders := by
  intro t r T₀ hspec htwf x_tbl res h h' cs htbl ev
  have hread : armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body)
      (ZMod.val (roleNum r)) T₀ 0 = true := by
    rw [RolesAux.val_roleNum]
    have hall : (match specTypeRaw r with
        | none => true
        | some T₀ => armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body)
            r.idx T₀ 0) = true :=
      List.all_eq_true.mp roleTypeArmsRead_true r (Role.mem_all r)
    rw [hspec] at hall
    exact hall
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_type.lookup
    role_type_noControl ev
  have hp : (IxVM.KernelRoleSpec.role_type.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_type.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨vr, m0, bs, body, c1, c2, dScrut, sel, dArm, -⟩ := d0.matchValue_inv
  obtain ⟨lr, hm0, -⟩ := dScrut.var_inv
  simp at lr
  subst vr
  subst m0
  obtain ⟨x1, hren, -⟩ := renders_of_armReadsAs htwf hread (by simp) htbl sel dArm
  exact ⟨x1, hren⟩

/-- **The cells of `role_type(tbl, r)` are the addresses of the roles its specified type
names**: every cell of the returned term is the address the table binds a role to whose key
the specified type names. -/
theorem roleType_cells {t : Ix.Kernel.RoleTable} {r : Role} {T₀ : KExpr}
    (hspec : specTypeRaw r = some T₀) (htwf : t.wf = true) {x_tbl res : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::role_type" [x_tbl, .field (roleNum r)] h res h' cs) :
    ∀ x, AddrIn h' res x → ∃ r', t.addressOf? r' = some (ixAddr x) ∧
      ∀ P, T₀.constsResolveBy P = true → P (Ix.Kernel.Key.role r') = true := by
  have hread : armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body)
      (ZMod.val (roleNum r)) T₀ 0 = true := by
    rw [RolesAux.val_roleNum]
    have hall : (match specTypeRaw r with
        | none => true
        | some T₀ => armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body)
            r.idx T₀ 0) = true :=
      List.all_eq_true.mp roleTypeArmsRead_true r (Role.mem_all r)
    rw [hspec] at hall
    exact hall
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_type.lookup
    role_type_noControl ev
  have hp : (IxVM.KernelRoleSpec.role_type.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_type.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_type.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨vr, m0, bs, body, c1, c2, dScrut, sel, dArm, -⟩ := d0.matchValue_inv
  obtain ⟨lr, hm0, -⟩ := dScrut.var_inv
  simp at lr
  subst vr
  subst m0
  exact cells_of_armReadsAs htwf hread (by simp) htbl sel dArm

/-! ## The functions keyed by a role and an index -/

/-- The key an arm of a rendered `match 64 * r + k` is selected at. -/
private theorem key_value {a b : F} {x v : SourceValue F}
    (o1 : evalBinOp .mul (.field 64 : SourceValue F) (.field a) = .ok x)
    (o2 : evalBinOp .add x (.field b) = .ok v) : v = .field (64 * a + b) := by
  simp only [evalBinOp, Except.ok.injEq] at o1
  subst o1
  simp only [evalBinOp, Except.ok.injEq] at o2
  exact o2.symm

/-- The key of a role and an index below `64`, as a number. -/
theorem val_key (r : Role) {k : Nat} (hk : k < 64) :
    ZMod.val (64 * roleNum r + ((k : Nat) : F)) = 64 * r.idx + k := by
  have e : (64 * roleNum r + ((k : Nat) : F) : F) = ((64 * r.idx + k : Nat) : F) := by
    unfold roleNum
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [e]
  exact RolesAux.val_natCast (by have := r.idx_lt; omega)

/-- A `match 64 * r + k` selects its arm at the key and evaluates it. -/
theorem keyed_match_inv {arms : List (Generic.Pattern F × Generic.Expr F)}
    {locals : Environment F Nat} {a b : F}
    (hr : List.find? (fun p => p.1 == "r") locals = some ("r", .field a))
    (hk : List.find? (fun p => p.1 == "k") locals = some ("k", .field b))
    {h : Heap F} {res : SourceValue F} {h' : Heap F} {cs : List (Call F)}
    (d0 : ObsExpr W [] locals
      (.matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k")) arms)
      h res h' cs) :
    ∃ bs body cs', selectArm W [] h (.field (64 * a + b)) arms = Except.ok (some (bs, body)) ∧
      ObsExpr W [] (bs ++ locals) body h res h' cs' := by
  obtain ⟨v1, m2, bs, body, c5, c6, d7, sel, d9, -⟩ := d0.matchValue_inv
  obtain ⟨x10, y11, m12, c13, c14, d15, d16, op17, -⟩ := d7.binary_inv
  obtain ⟨x18, y19, m20, c21, c22, d23, d24, op25, -⟩ := d15.binary_inv
  obtain ⟨hx18, hm20, -⟩ := d23.literal_inv
  obtain ⟨l26, hm12, -⟩ := d24.var_inv
  obtain ⟨l27, hm2, -⟩ := d16.var_inv
  rw [hr] at l26
  rw [hk] at l27
  cases l26
  cases l27
  subst hx18
  subst hm20
  subst hm12
  subst hm2
  have hv := key_value op25 op17
  subst hv
  exact ⟨bs, body, c6, sel, d9⟩

/-- **A function keyed by a role and an index returns the specified term**, when the arm at the
key reads as it. -/
theorem keyed_renders {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {arms : List (Generic.Pattern F × Generic.Expr F)} {r : Role} {k : Nat} (hk : k < 64)
    {T₀ : KExpr} {sp : Nat} (hread : armReadsAs arms (64 * r.idx + k) T₀ sp = true)
    {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (d0 : ObsExpr W []
      (["tbl", "r", "k"].zip [x_tbl, .field (roleNum r), .field ((k : Nat) : F)])
      (.matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k")) arms)
      h res h' cs) :
    Heap.Extends h h' ∧ RendersUpToBinderData t h' T₀ res ∧ OpOpen.ForallSpine h' sp res := by
  obtain ⟨bs, body, cs', sel, dArm⟩ :=
    keyed_match_inv (a := roleNum r) (b := ((k : Nat) : F)) (by simp) (by simp) d0
  have hread' : armReadsAs arms (ZMod.val (64 * roleNum r + ((k : Nat) : F))) T₀ sp = true := by
    rw [val_key r hk]
    exact hread
  exact renders_of_armReadsAs htwf hread' (by simp) htbl sel dArm

/-! ## The recurrences' sides -/

/-- Every arm of a recurrence-side function reads as the closed side of the recurrence it is
keyed by. -/
def opSideArmsRead (arms : List (Generic.Pattern F × Generic.Expr F))
    (side : KExpr × KExpr → KExpr) : Bool :=
  Role.all.all fun r =>
    if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames then
      allIdx (fun k eq => decide (k < 64) &&
          armReadsAs arms (64 * r.idx + k) (opSideRaw (side eq)) 0) 0
        (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))
    else true

theorem opSide_read {arms : List (Generic.Pattern F × Generic.Expr F)}
    {side : KExpr × KExpr → KExpr} (hall : opSideArmsRead arms side = true) {r : Role} {k : Nat}
    {eq : KExpr × KExpr} (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    (hget : (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k]? = some eq) :
    k < 64 ∧ armReadsAs arms (64 * r.idx + k) (opSideRaw (side eq)) 0 = true := by
  unfold opSideArmsRead at hall
  have hr : (if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames then
      allIdx (fun k eq => decide (k < 64) &&
          armReadsAs arms (64 * r.idx + k) (opSideRaw (side eq)) 0) 0
        (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))
      else true) = true := List.all_eq_true.mp hall r (Role.mem_all r)
  rw [ite_eq_left hmem] at hr
  have hk := allIdx_get hr hget
  simp only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq] at hk
  exact hk

set_option maxRecDepth 100000 in
theorem op_equation_lhs_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.op_equation_lhs.body = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem op_equation_rhs_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.op_equation_rhs.body = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opEquationLhsArmsRead_true :
    opSideArmsRead (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_lhs.body) Prod.fst =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opEquationRhsArmsRead_true :
    opSideArmsRead (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_rhs.body) Prod.snd =
      true := by decide +kernel

/-- **`KernelRoleSpec::op_equation_lhs(tbl, r, k)` builds the left side of the `k`-th
recurrence**, at every structural operation and every recurrence. -/
theorem opEquationLhsRenders : OpEquationLhsRenders := by
  intro t r k eq hmem hget htwf x_tbl res h h' cs htbl ev
  obtain ⟨hk, hread⟩ := opSide_read opEquationLhsArmsRead_true hmem hget
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_lhs.lookup
    op_equation_lhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.op_equation_lhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_lhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_lhs.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨x1, hren, -⟩ := keyed_renders htwf hk hread htbl d0
  exact ⟨x1, hren⟩

/-- **`KernelRoleSpec::op_equation_rhs(tbl, r, k)` builds the right side of the `k`-th
recurrence**, at every structural operation and every recurrence. -/
theorem opEquationRhsRenders : OpEquationRhsRenders := by
  intro t r k eq hmem hget htwf x_tbl res h h' cs htbl ev
  obtain ⟨hk, hread⟩ := opSide_read opEquationRhsArmsRead_true hmem hget
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_rhs.lookup
    op_equation_rhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.op_equation_rhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_rhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_rhs.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨x1, hren, -⟩ := keyed_renders htwf hk hread htbl d0
  exact ⟨x1, hren⟩

/-! ## The certificates -/

/-- Every arm of `op_certificate` reads as the closed certificate statement it is keyed by,
along as many `Forall` cells as the statement has variables and hypotheses. -/
def certArmsRead : Bool :=
  Role.all.all fun r =>
    if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames then
      allIdx (fun k st => decide (k < 64) &&
          armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.op_certificate.body)
            (64 * r.idx + k) (certRaw st) (2 + st.1.length)) 0
        (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey))
    else true

set_option maxRecDepth 100000 in
theorem op_certificate_noControl :
    ControlLower.hasControl IxVM.KernelRoleSpec.op_certificate.body = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem certArmsRead_true : certArmsRead = true := by decide +kernel

/-- **`KernelRoleSpec::op_certificate(tbl, r, k)` builds the `k`-th certificate statement of a
well-founded operation**, along a spine of `Forall` cells. -/
theorem opCertificateRenders : OpCertificateRenders := by
  intro t r k st hmem hget htwf x_tbl res h h' cs htbl ev
  have hr : (if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames then
      allIdx (fun k st => decide (k < 64) &&
          armReadsAs (RolesAux.matchArms IxVM.KernelRoleSpec.op_certificate.body)
            (64 * r.idx + k) (certRaw st) (2 + st.1.length)) 0
        (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey))
      else true) = true := List.all_eq_true.mp certArmsRead_true r (Role.mem_all r)
  rw [ite_eq_left hmem] at hr
  have hk := allIdx_get hr hget
  simp only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq] at hk
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_certificate.lookup
    op_certificate_noControl ev
  have hp : (IxVM.KernelRoleSpec.op_certificate.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.op_certificate.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_certificate.body) := rfl
  rw [hp, hb] at d0
  exact keyed_renders htwf hk.1 hk.2 htbl d0

end IxVM.Refinement.Binding
