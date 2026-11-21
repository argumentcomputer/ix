import IxVMRefinement.RoleOps.Interface

/-! # From a check of a `Nat` operation to the kernel's install record

`structOp_run` and `wfOp_run`: the facts of an operation's check (`StructOpCheck`, `WfOpCheck`)
and the facts of the prefix (`OpPrefix`, `WfPrefix`) give the kernel's judgement-level record of
the definition at the operation's key, over derivations, in the environment before the operation
is stored: `DeclDefnRunJ rulesJ env ⟨c, [], ty₀⟩ val₀ hint (installed env c ty val hint)`.

`structOp_step` and `wfOp_step`: hence the install of the declared definition
(`IxVM.Consistency.InstallStep`) and the step of the fold invariant, in every set theory.

What the next declarations read of the operation:

* `OpsPinned.install_op` (`Guards.lean`): the operation is stored as pinned, which a later
  operation's `OpPrefix` reads;
* `opCompanion_installed`, `coreCompanions_withOps` (`Companions.lean`): the stored shapes the
  checker's native arithmetic reads (`natOpStored`, and `natAddTyOk` for `Nat.add`), as the role
  fields of `CoreCompanions` at a group limit that puts the operation in force.
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KExpr KKey Ctx)
open IxVM.Refinement.Decl (isBaseKey isProjFnShape_of_isBaseKey ne_projTableName_of_isBaseKey
  infer_constsResolve FoldInv FoldStoreInv FullDeclInv CleanInstallStep foldInv_step_defn
  CoreCompanions)
open Ix.Kernel (Env Expr ConstantInfo ConstantVal BinderMeta ReducibilityHint EnvExt
  natOpNames natDivModNames natOpDeps natOpGuard natOpStoredOk natOpTyPinned natOpStored
  natLitSupported natName natZeroName natSuccName boolName boolTrueName boolFalseName eqName
  natPredName natAddName natDivName natBeqName natBleName natOpEquations divModCertStmts
  divModCertApplied divModCertGuard divModCertsGuard)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (DeclDefnRunJ ConstantValRunJ ValueFrontRunJ NatEqsRunJ DivModCertRunJ
  DivModCertsJ CertRowJ)
open Ix.Kernel.Model (rulesJ)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## The definition's own record -/

/-- The typing half of the kernel's record, from the definition's check. The operation's key is
a role key outside the basis, so the name guards hold of it. -/
theorem OpFront.runs {env : Env .anon} {c : KKey} {ty₀ val₀ ty val : KExpr}
    (h : OpFront env ty₀ val₀ ty val) (hS : Ix.Kernel.Open.StoreInv env)
    (hfresh : env.find? c = none) (hc : c ∈ opNames) :
    ConstantValRunJ rulesJ env ⟨c, [], ty₀⟩ ty ∧
      ValueFrontRunJ rulesJ env ⟨c, [], ty₀⟩ val₀ ty val := by
  obtain ⟨s, u, hinf, hred⟩ := h.tySort
  obtain ⟨vt, hvinf, hvde⟩ := h.valTyped
  have htyS :=
    (Ix.Kernel.Model.judgeFrames_rulesJ env).annot_syntax h.tyAnnot h.tyNoFvar h.tyClosed
  have hvalS :=
    (Ix.Kernel.Model.judgeFrames_rulesJ env).annot_syntax h.valAnnot h.valNoFvar h.valClosed
  have hnone : (env.find? c).isNone = true := by rw [hfresh]; rfl
  exact ⟨⟨hnone, notReserved_of_mem_opNames hc,
      isProjFnShape_of_isBaseKey (isBaseKey_of_mem_opNames hc), rfl, h.tyClosed, h.tyNoFvar,
      h.tyAnnot, h.tyLevels, infer_constsResolve hinf hS htyS.1, s, u, hinf, hred⟩,
    ⟨h.valClosed, h.valNoFvar, h.valAnnot, h.valLevels,
      infer_constsResolve hvinf hS hvalS.1, vt, hvinf, hvde⟩⟩

/-! ## A structural operation -/

/-- **A structural operation's check gives the kernel's install record**, in the environment
before the operation is stored. -/
theorem structOp_run {env : Env .anon} {c : KKey} {ty₀ val₀ ty val : KExpr}
    (hint : ReducibilityHint) (hS : Ix.Kernel.Open.StoreInv env) (hc : c ∈ natOpNames)
    (hp : OpPrefix env c) (hk : StructOpCheck env c ty₀ val₀ ty val) :
    DeclDefnRunJ rulesJ env ⟨c, [], ty₀⟩ val₀ hint (installed env c ty val hint) := by
  have hco : c ∈ opNames := mem_opNames.mpr (Or.inl hc)
  have hbase := isBaseKey_of_mem_opNames hco
  obtain ⟨hcv, hvf⟩ := hk.front.runs hS hp.fresh hco
  refine ⟨ty, val, hcv, hvf, rfl, fun _ => ⟨natOpGuard_installed hp hbase ty val hint,
    natOpDeps_storedOk_installed hp hbase hk.tyShape val hint, ?_⟩, fun hdm => ?_⟩
  · unfold NatEqsRunJ
    intro eq heq
    obtain ⟨eq₀, hmem, rfl⟩ := List.mem_map.mp heq
    exact hk.eqs eq₀ hmem
  · have hdm' : (natDivModNames : List KKey).contains c = true := hdm
    rw [not_divMod_of_natOp hc] at hdm'
    exact nomatch hdm'

/-! ## A well-founded operation -/

/-- A term whose constants are stored in an environment that does not store `c` does not name
`c`: replacing `c` in it changes nothing. -/
theorem substConstAll_of_resolves {env : Env .anon} {c : KKey} (val : KExpr)
    (hfresh : env.find? c = none) :
    ∀ {P : KExpr}, P.constsResolve env = true → Expr.substConstAll c val P = P := by
  intro P
  induction P with
  | const k us =>
    intro h
    simp only [Expr.constsResolve] at h
    have hne : ¬ (k = c ∧ us = []) := by
      rintro ⟨hk, -⟩
      rw [hk, hfresh] at h
      exact nomatch h
    simp only [Expr.substConstAll]
    rw [ite_eq_right hne]
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.substConstAll]
    rw [ihf h.1, iha h.2]
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.substConstAll]
    rw [iht h.1, ihb h.2]
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.substConstAll]
    rw [iht h.1, ihb h.2]
  | letE ty v b l iht ihv ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.substConstAll]
    rw [iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i e ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.substConstAll]
    rw [ih h.2]
  | bvar _ => intro _; rfl
  | fvar _ _ _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl

/-- **A component of a certificate statement**: a binder-free application spine over opened
variables typed by a constant, whose constants are the operation `c` at no levels or among
`ks`. -/
def stmtOk (c : KKey) (ks : List KKey) : KExpr → Bool
  | .const k us => (k == c && us.isEmpty) || ks.contains k
  | .app f a => stmtOk c ks f && stmtOk c ks a
  | .fvar _ (.const k _) => ks.contains k
  | _ => false

/-- Such a component, the operation replaced by a value whose constants are stored, names only
stored constants once the constants of `ks` are stored. -/
theorem constsResolve_substConst0 {env : Env .anon} {c : KKey} {val : KExpr} {ks : List KKey}
    (hks : ∀ k ∈ ks, (env.find? k).isSome = true) (hv : val.constsResolve env = true) :
    ∀ (e : KExpr), stmtOk c ks e = true →
      (Expr.substConst0 c val e).constsResolve env = true := by
  intro e
  induction e with
  | const k us =>
    intro h
    simp only [stmtOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    simp only [Expr.substConst0]
    split
    · exact hv
    · next hne =>
      rcases h with hself | hmem
      · exact absurd hself hne
      · simp only [Expr.constsResolve]
        exact hks k (List.contains_iff_mem.mp hmem)
  | app f a ihf iha =>
    intro h
    simp only [stmtOk, Bool.and_eq_true] at h
    simp only [Expr.substConst0, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | fvar i ty _ =>
    intro h
    cases ty with
    | const k us =>
      have h' : ks.contains k = true := h
      show (env.find? k).isSome = true
      exact hks k (List.contains_iff_mem.mp h')
    | _ => exact nomatch h
  | bvar _ => intro h; exact nomatch h
  | sort _ => intro h; exact nomatch h
  | lam _ _ _ _ _ => intro h; exact nomatch h
  | forallE _ _ _ _ _ => intro h; exact nomatch h
  | letE _ _ _ _ _ _ _ => intro h; exact nomatch h
  | lit _ => intro h; exact nomatch h
  | proj _ _ _ _ => intro h; exact nomatch h

/-- The constants a certificate statement of operation `c` names besides `c`: the `Nat` and
`Bool` constructors and types, `Eq`, and the operations `c` depends on. -/
def certKeys (c : KKey) : List KKey :=
  [natName, natZeroName, natSuccName, eqName, boolName, boolTrueName, boolFalseName] ++
    (natOpDeps c).filter (fun n => n != c)

private theorem certStmts_all_ok :
    (natDivModNames : List KKey).all (fun c => (divModCertStmts c).all (fun st =>
      st.1.all (stmtOk c (certKeys c)) && stmtOk c (certKeys c) st.2)) = true := by
  decide +kernel

/-- The constants of a certificate statement are stored in the prefix of a well-founded
operation's install. -/
theorem certKeys_stored {env : Env .anon} {c : KKey} (hS : Ix.Kernel.Open.StoreInv env)
    (hp : WfPrefix env c) :
    ∀ k ∈ certKeys c, (env.find? k).isSome = true := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, -⟩ :=
    Ix.Kernel.natLitSupported_inv hp.op.natLit
  obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF, -⟩⟩ := hp.boolCtorsTyped
  intro k hk
  unfold certKeys at hk
  rcases List.mem_append.mp hk with hk | hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [hfN]
    · simp [hfZ]
    · simp [hfS]
    · simp [hp.eq]
    · exact boolStored_of_ctorsTyped hS hp.boolCtorsTyped
    · simp [hT]
    · simp [hF]
  · obtain ⟨hmem, hne⟩ := List.mem_filter.mp hk
    have hne' : k ≠ c := by simpa using hne
    obtain ⟨cv, v, hint, hf, -, -⟩ := natOpStoredOk_inv (hp.op.deps k hmem hne')
    simp [hf]

/-- The syntactic guards of a certificate on its statement: the hypotheses and the equation, the
operation replaced by its value, name only stored constants. -/
theorem certStmts_resolve {env : Env .anon} {c : KKey} {val : KExpr}
    (hS : Ix.Kernel.Open.StoreInv env) (hc : c ∈ natDivModNames)
    (hp : WfPrefix env c) (hv : val.constsResolve env = true) :
    ∀ st ∈ divModCertStmts c,
      (st.1.map (Expr.substConst0 c val)).all (fun h => h.constsResolve env) = true ∧
        (Expr.substConst0 c val st.2).constsResolve env = true := by
  intro st hst
  have hall : (divModCertStmts c).all (fun st =>
      st.1.all (stmtOk c (certKeys c)) && stmtOk c (certKeys c) st.2) = true :=
    List.all_eq_true.mp certStmts_all_ok c hc
  have hst' : (st.1.all (stmtOk c (certKeys c)) && stmtOk c (certKeys c) st.2) = true :=
    List.all_eq_true.mp hall st hst
  simp only [Bool.and_eq_true] at hst'
  have hks := certKeys_stored hS hp
  refine ⟨List.all_eq_true.mpr ?_, constsResolve_substConst0 hks hv st.2 hst'.2⟩
  intro h hh
  obtain ⟨h₀, hmem, rfl⟩ := List.mem_map.mp hh
  exact constsResolve_substConst0 hks hv h₀ (List.all_eq_true.mp hst'.1 h₀ hmem)

/-- One checked certificate is one row of the kernel's certificate relation, with the proof
term itself as the proof (it does not name the operation). -/
theorem CertFacts.row {env : Env .anon} {c : KKey} {val : KExpr} {st : List KExpr × KExpr}
    {P : KExpr} (hf : CertFacts env c val st P) (hfresh : env.find? c = none)
    (hst : (st.1.map (Expr.substConst0 c val)).all (fun h => h.constsResolve env) = true ∧
      (Expr.substConst0 c val st.2).constsResolve env = true) :
    CertRowJ rulesJ env c val st P := by
  have hsub : Expr.substConstAll c val P = P :=
    substConstAll_of_resolves val hfresh hf.resolves
  obtain ⟨appliedA, tp, hann, hinf, hde⟩ := hf.typed
  refine ⟨?_, appliedA, tp, ?_, hinf, hde⟩
  · unfold Ix.Kernel.divModCertGuard
    rw [hsub]
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨⟨⟨⟨⟨hf.closed, hf.noFvar⟩, hf.levels⟩, hf.resolves⟩, hst.1⟩, hst.2⟩
  · rw [hsub]
    exact hann

theorem certRows_of_facts {env : Env .anon} {c : KKey} {val : KExpr}
    (hfresh : env.find? c = none) :
    ∀ {stmts : List (List KExpr × KExpr)} {proofs : List KExpr},
      List.Forall₂ (CertFacts env c val) stmts proofs →
      (∀ st ∈ stmts,
        (st.1.map (Expr.substConst0 c val)).all (fun h => h.constsResolve env) = true ∧
          (Expr.substConst0 c val st.2).constsResolve env = true) →
      List.Forall₂ (CertRowJ rulesJ env c val) stmts proofs := by
  intro stmts proofs h
  induction h with
  | nil => intro _; exact .nil
  | cons hrow _ ih =>
    intro hst
    exact .cons (hrow.row hfresh (hst _ List.mem_cons_self))
      (ih (fun st hmem => hst st (List.mem_cons_of_mem _ hmem)))

theorem divModCertsJ_of_rows {env : Env .anon} {c : KKey} {val : KExpr} :
    ∀ {stmts : List (List KExpr × KExpr)} {proofs : List KExpr},
      List.Forall₂ (CertRowJ rulesJ env c val) stmts proofs →
      DivModCertsJ rulesJ env c val stmts proofs := by
  intro stmts proofs h
  induction h with
  | nil => exact .nil
  | cons hrow _ ih =>
    obtain ⟨hg, appliedA, tp, hann, hinf, hde⟩ := hrow
    exact .cons hg hann hinf hde ih

theorem certsGuard_of_rows {env : Env .anon} {c : KKey} {val : KExpr} :
    ∀ {stmts : List (List KExpr × KExpr)} {proofs : List KExpr},
      List.Forall₂ (CertRowJ rulesJ env c val) stmts proofs →
      (stmts.zip proofs).all (fun p => divModCertGuard env c val p.1.1 p.1.2 p.2) = true := by
  intro stmts proofs h
  induction h with
  | nil => rfl
  | cons hrow _ ih =>
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨hrow.1, ih⟩

/-- **A well-founded operation's check gives the kernel's install record**, in the environment
before the operation is stored. -/
theorem wfOp_run {env : Env .anon} {c : KKey} {ty₀ val₀ ty val : KExpr}
    (hint : ReducibilityHint) (hS : Ix.Kernel.Open.StoreInv env) (hc : c ∈ natDivModNames)
    (hp : WfPrefix env c) (hk : WfOpCheck env c ty₀ val₀ ty val) :
    DeclDefnRunJ rulesJ env ⟨c, [], ty₀⟩ val₀ hint (installed env c ty val hint) := by
  have hco : c ∈ opNames := mem_opNames.mpr (Or.inr hc)
  have hbase := isBaseKey_of_mem_opNames hco
  obtain ⟨hcv, hvf⟩ := hk.front.runs hS hp.op.fresh hco
  have hvres : val.constsResolve env = true := hvf.2.2.2.2.1
  obtain ⟨proofs, hrows⟩ := hk.certs
  have hrowsJ : List.Forall₂ (CertRowJ rulesJ env c val) (divModCertStmts c) proofs :=
    certRows_of_facts hp.op.fresh hrows (certStmts_resolve hS hc hp hvres)
  refine ⟨ty, val, hcv, hvf, rfl, fun hno => ?_,
    fun _ => ⟨divModEnvGuard_installed hp hbase hk.tyShape val hint, proofs,
      certsGuard_of_rows hrowsJ, divModCertsJ_of_rows hrowsJ⟩⟩
  have hno' : (natOpNames : List KKey).contains c = true := hno
  rw [not_natOp_of_divMod hc] at hno'
  exact nomatch hno'

/-! ## The install and the fold invariant -/

/-- The declared definition is stored: the install step of the public statement, with what the
fold keeps beside it. `tyD`, `valD` are the declared terms, `ty`, `val` the stored ones. -/
theorem op_cleanInstall {env : Env .anon} {c : KKey} {ty val tyD valD : KExpr}
    {hint : ReducibilityHint} (hc : c ∈ opNames) (hfresh : env.find? c = none)
    (hty : IxVM.Consistency.Annotates ty tyD) (hval : IxVM.Consistency.Annotates val valD) :
    CleanInstallStep env (.defnDecl ⟨c, [], tyD⟩ valD hint) (installed env c ty val hint) :=
  CleanInstallStep.single (ci := .defnInfo ⟨c, [], ty⟩ val hint)
    (ci₀ := .defnInfo ⟨c, [], tyD⟩ valD hint) rfl ⟨⟨rfl, rfl, hty⟩, hval, rfl⟩ hfresh
    (isBaseKey_of_mem_opNames hc)

/-- **A structural operation's step.** From its check and its prefix: the declared definition is
installed at the operation's key, and the fold invariant is kept in every set theory. -/
theorem structOp_step {env : Env .anon} {c : KKey} {ty₀ val₀ ty val tyD valD : KExpr}
    (hint : ReducibilityHint) (hc : c ∈ natOpNames) (hp : OpPrefix env c)
    (hk : StructOpCheck env c ty₀ val₀ ty val)
    (hty : IxVM.Consistency.Annotates ty tyD) (hval : IxVM.Consistency.Annotates val valD) :
    IxVM.Consistency.InstallStep env (.defnDecl ⟨c, [], tyD⟩ valD hint)
        (installed env c ty val hint) ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FoldInv V env → FoldInv V (installed env c ty val hint)) ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FullDeclInv V env → FullDeclInv V (installed env c ty val hint) := by
  have hco : c ∈ opNames := mem_opNames.mpr (Or.inl hc)
  have hclean := op_cleanInstall (hint := hint) hco hp.fresh hty hval
  refine ⟨hclean.step,
    fun V _ h => foldInv_step_defn (structOp_run hint h.store.store hc hp hk) V h,
    fun V _ h => ?_⟩
  exact FullDeclInv.step_of_foldInv_clean hclean
    (foldInv_step_defn (structOp_run hint h.toFoldStoreInv.store hc hp hk)) V h

/-- **A well-founded operation's step.** From its check and its prefix: the declared definition
is installed at the operation's key, and the fold invariant is kept in every set theory. -/
theorem wfOp_step {env : Env .anon} {c : KKey} {ty₀ val₀ ty val tyD valD : KExpr}
    (hint : ReducibilityHint) (hc : c ∈ natDivModNames) (hp : WfPrefix env c)
    (hk : WfOpCheck env c ty₀ val₀ ty val)
    (hty : IxVM.Consistency.Annotates ty tyD) (hval : IxVM.Consistency.Annotates val valD) :
    IxVM.Consistency.InstallStep env (.defnDecl ⟨c, [], tyD⟩ valD hint)
        (installed env c ty val hint) ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FoldInv V env → FoldInv V (installed env c ty val hint)) ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FullDeclInv V env → FullDeclInv V (installed env c ty val hint) := by
  have hco : c ∈ opNames := mem_opNames.mpr (Or.inr hc)
  have hclean := op_cleanInstall (hint := hint) hco hp.op.fresh hty hval
  refine ⟨hclean.step,
    fun V _ h => foldInv_step_defn (wfOp_run hint h.store.store hc hp hk) V h,
    fun V _ h => ?_⟩
  exact FullDeclInv.step_of_foldInv_clean hclean
    (foldInv_step_defn (wfOp_run hint h.toFoldStoreInv.store hc hp hk)) V h

/-- `Nat.add`'s step: `structOp_step` at its key. -/
theorem natAdd_step {env : Env .anon} {ty₀ val₀ ty val tyD valD : KExpr}
    (hint : ReducibilityHint) (hp : OpPrefix env natAddName)
    (hk : StructOpCheck env natAddName ty₀ val₀ ty val)
    (hty : IxVM.Consistency.Annotates ty tyD) (hval : IxVM.Consistency.Annotates val valD) :
    IxVM.Consistency.InstallStep env (.defnDecl ⟨natAddName, [], tyD⟩ valD hint)
        (installed env natAddName ty val hint) ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FoldInv V env → FoldInv V (installed env natAddName ty val hint)) ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FullDeclInv V env → FullDeclInv V (installed env natAddName ty val hint) :=
  structOp_step hint (by decide) hp hk hty hval

/-- `Nat.div`'s step: `wfOp_step` at its key. -/
theorem natDiv_step {env : Env .anon} {ty₀ val₀ ty val tyD valD : KExpr}
    (hint : ReducibilityHint) (hp : WfPrefix env natDivName)
    (hk : WfOpCheck env natDivName ty₀ val₀ ty val)
    (hty : IxVM.Consistency.Annotates ty tyD) (hval : IxVM.Consistency.Annotates val valD) :
    IxVM.Consistency.InstallStep env (.defnDecl ⟨natDivName, [], tyD⟩ valD hint)
        (installed env natDivName ty val hint) ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FoldInv V env → FoldInv V (installed env natDivName ty val hint)) ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FullDeclInv V env → FullDeclInv V (installed env natDivName ty val hint) :=
  wfOp_step hint (by decide) hp hk hty hval

end IxVM.Refinement.RoleOps
