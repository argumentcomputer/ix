import IxVMRefinement.Binding.OpEquations
import IxVMRefinement.Binding.TableAdmitsValidate

/-! # The recurrences an operation's validation compares

`KernelRoles::validate_op_equations` (`KernelRoles.lean:1009`) walks the operation's evidence
list. At a structural operation every entry is `Defeq`, and the entry at index `k` opens both
rendered sides of the `k`-th recurrence (`open_two_lams`), replaces the operation by the value
`validate_role` loaded (`subst_const`) and compares the results under the group's role
context (`k_is_def_eq`). This file reads that comparison at the keying of the closure's
environment (`OpRefine.EqObs`).

* `LoadedReads.get_ci_defn_value_exact`: the value pointer of a loaded definition record, its
  raw conversion and its exact representation of the canonical annotation of the value's
  reading.
* `open_two_lams_nat`: `open_two_lams` on a rendered `λ (x y : Nat), L` with no `Let` and no
  `Proj` cell gives the context list of the two `Nat` variables under any keying that keys
  `Nat`'s address as the table does.
* `opEquationLhs_full`, `opEquationRhs_full`: a rendered side is `λ (x y : Nat), L`, with `L`
  opening to the side, exactly under the table's keying and with no `Let` and no `Proj` cell.
* `sidesNamed_all` (decided): every constant a recurrence side names is the operation or a
  walked role of an earlier group.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-- **The value of a held definition record, as `Ingress::get_ci` loads it**: in calls that hash
no collision with the store, the load returns a definition whose value pointer is a raw
conversion of the record's value with no recursion address, and represents, exactly under the
table's keying, the canonical annotation of the value's reading. -/
theorem get_ci_defn_value_exact {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {d : Ixon.Definition} (hrec : recordOf E (Core.ixAddr a) = some c)
    (hinfo : c.info = .defn d) (hlogic : InLogic c) {val₀ : Ix.Kernel.Expr .anon}
    (hval : (exprReader t (fun x => E.blobs.get? x) c id
      (soloSelf t (Core.ixAddr a))).read d.value = .ok val₀)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true) :
    ∃ (tyPtr valPtr hint : SourceValue F) (blobs : List (_root_.Address × ByteArray))
      (val' : Ix.Kernel.Expr .anon),
      canonAnn c (List.range d.lvls.toNat) (0 + 1) d.value val₀ = some val' ∧
      loadValue h' ptr = .ok (L1.defnValShape d tyPtr valPtr hint) ∧
      Decl.TmCExact (Core.keyOf t) h' (Core.posOf (List.range d.lvls.toNat) val') valPtr ∧
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h' 4294967295
        d.value valPtr := by
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := L1.get_ci_trace_spec ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  have hrecur : L1.defnRecurAddrs d (Core.ixAddr a) = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnRecurAddrs, hf]
  rw [hrecur] at htr
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
  subst hv
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    annotation_canon_exact (recurAddrs := []) ht hnlvls (fun _ _ _ _ hx => by simp at hx) hagree
      rval built hpV hlV hval hval_lbb hval_def
  exact ⟨tyPtr, valPtr, hint, blobs, val', hcV, hld, htmV, rval⟩

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role Expr)
open Ix.Kernel.Semantics (NativeFam)

/-! ## Opening a rendered side under the closure's keying -/

/-- **`open_two_lams` on a rendered side, with the context list under another keying**: on a
closed `λ (x y : Nat), L` with no `Let` and no `Proj` cell, the body is `L` opened at depth 2 and
the context list represents the two `Nat` variables under every keying `κ'` that keys the
addresses `κ` keys as `Nat` as `Nat`. -/
theorem open_two_lams_nat {κ κ' : _root_.Address → KKey} {h h' : Heap F}
    {e r : SourceValue F} {cs : List (Call F)} {L : KExpr} {m₁ m₂ : Ix.Kernel.BinderMeta}
    (hE : TmC κ h (.lam OpOpen.natTy (.lam OpOpen.natTy L m₂) m₁) e) (hp : LetProjFree h e)
    (hnat : ∀ x : Bytes.Address, κ (ixAddr x) = (Ix.Kernel.natName : KKey) →
      κ' (ixAddr x) = (Ix.Kernel.natName : KKey))
    (ev : ObsFn W "KernelRoles::open_two_lams" [e] h r h' cs) :
    ∃ body types, r = .tuple [body, types] ∧
      Tm κ 2 (fun _ => OpOpen.natTy) h' 0 (OpOpen.open₂ OpOpen.natTy OpOpen.natTy L) body ∧
      LetProjFree h' body ∧ TypesRep κ' (fun _ => OpOpen.natTy) h' 2 types ∧
      Heap.Extends h h' := by
  let Γ : Nat → KExpr := fun _ => OpOpen.natTy
  match Obs.«KernelRoles::open_two_lams».obs ev with
  | .run (x_t1 := xt1) (x_t2 := xt2) (x_body := xbody) (m84 := m84) (m106 := m106)
      (m128 := m128) (ld12 := ld1) (ld47 := ld2) (he75 := hr) (hm92 := hm84) (hm114 := hm106)
      (hm136 := hm128) (he140 := hh) .. =>
    subst hr
    rw [hh]
    obtain ⟨T, B', ℓ, hEq, ht1, hin, -⟩ := (hE 0 Γ).lam_of_load ld1
    injection hEq with e1 e2 e3
    subst e1 e2
    obtain ⟨T', B'', ℓ', hEq', ht2, hbody, -⟩ := hin.lam_of_load ld2
    injection hEq' with e4 e5 e6
    subst e4 e5
    obtain ⟨p1, pin⟩ := hp.lam_of_load ld1
    obtain ⟨p2, pbody⟩ := pin.lam_of_load ld2
    have hnatP : (OpOpen.natTy : KExpr).constsResolveBy
        (fun n => decide (n = (Ix.Kernel.natName : KKey))) = true := by
      simp [Ix.Kernel.Expr.constsResolveBy]
    have rk : ∀ {k : Nat} {p : SourceValue F}, Tm κ 0 Γ h k OpOpen.natTy p → LetProjFree h p →
        Tm κ' 0 Γ h k OpOpen.natTy p := by
      intro k p rep pp
      refine rep.rekey (fun x hx => ?_) (fun x hx _ => (LetProjFree.not_projIn hx pp).elim)
      have hk := LetProjFree.addrIn_named rep pp x hx _ hnatP
      have hk' : κ (ixAddr x) = (Ix.Kernel.natName : KKey) := by simpa using hk
      rw [hnat x hk', hk']
    have ht1' := rk ht1 p1
    have ht2' := rk ht2 p2
    have c0 : m128[h.length]? = some (.construct kexprListEnum "Nil" []) := by
      rw [hm128]; simp
    have c1 : m106[m128.length]? = some (.construct kexprListEnum "Cons"
        [xt1, .ptr (.enum kexprListEnum) h.length]) := by
      rw [hm106]; simp
    have c2 : m84[m106.length]? = some (.construct kexprListEnum "Cons"
        [xt2, .ptr (.enum kexprListEnum) m128.length]) := by
      rw [hm84]; simp
    have x0 : Heap.Extends h m128 := by rw [hm128]; exact Heap.Extends.snoc _ _
    have x1 : Heap.Extends m128 m106 := by rw [hm106]; exact Heap.Extends.snoc _ _
    have x2 : Heap.Extends m106 m84 := by rw [hm84]; exact Heap.Extends.snoc _ _
    have ext : Heap.Extends h m84 := x0.trans (x1.trans x2)
    have hΓnil : ∀ j, j < 0 → Γ j = Γ j := fun _ _ => rfl
    refine ⟨xbody, _, rfl, ?_, pbody.mono ext, ?_, ext⟩
    · have b1 := hbody.open (d := 0) (Γ' := Γ) (T := OpOpen.natTy) rfl hΓnil 1 rfl
      have b2 := b1.open (d := 1) (Γ' := Γ)
        (T := OpOpen.natTy.instantiate1 (.fvar 0 OpOpen.natTy)) rfl (fun _ _ => rfl) 0 rfl
      exact b2.mono ext
    · refine .cons c2 ?_ (.cons (x2.getElem?_eq c1) ?_ (.nil ((x1.trans x2).getElem?_eq c0)))
      · have b := (ht2'.open (d := 0) (Γ' := Γ) (T := OpOpen.natTy) rfl hΓnil 0 rfl).mono ext
        exact b
      · exact ht1'.mono ext

/-! ## A rendered side, in full -/

/-- **`op_equation_lhs(tbl, r, k)` in full**: a pointer that represents, exactly under the
table's keying, `λ (x y : Nat), L` with `L` opening to the left side, and that reaches no `Let`
and no `Proj` cell. -/
theorem opEquationLhs_full {t : Ix.Kernel.RoleTable} {r : Role} {k : Nat}
    {eq : KExpr × KExpr} (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    (hget : (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k]? = some eq)
    (htwf : t.wf = true) {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::op_equation_lhs"
      [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h res h' cs) :
    Heap.Extends h h' ∧ ∃ L m₁ m₂,
      Decl.TmCExact (keyOf t) h' (.lam OpOpen.natTy (.lam OpOpen.natTy L m₂) m₁) res ∧
      OpOpen.open₂ OpOpen.natTy OpOpen.natTy L = eq.1 ∧ LetProjFree h' res := by
  obtain ⟨hk, hread⟩ := opSide_read opEquationLhsArmsRead_true hmem hget
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_lhs.lookup
    op_equation_lhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.op_equation_lhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_lhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_lhs.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨x1, ⟨T, hT, her⟩, -, hplain⟩ := keyed_renders htwf hk hread htbl d0
  have heq : eq ∈ Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey) :=
    List.mem_of_getElem? hget
  obtain ⟨L, m₁, m₂, rfl, -, hL⟩ :=
    rendered_side_shape (sideShape_all _ hmem eq heq).1 her
  exact ⟨x1, L, m₁, m₂, hT, hL, hplain⟩

/-- **`op_equation_rhs(tbl, r, k)` in full**: as `opEquationLhs_full`, for the right side. -/
theorem opEquationRhs_full {t : Ix.Kernel.RoleTable} {r : Role} {k : Nat}
    {eq : KExpr × KExpr} (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    (hget : (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k]? = some eq)
    (htwf : t.wf = true) {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::op_equation_rhs"
      [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h res h' cs) :
    Heap.Extends h h' ∧ ∃ L m₁ m₂,
      Decl.TmCExact (keyOf t) h' (.lam OpOpen.natTy (.lam OpOpen.natTy L m₂) m₁) res ∧
      OpOpen.open₂ OpOpen.natTy OpOpen.natTy L = eq.2 ∧ LetProjFree h' res := by
  obtain ⟨hk, hread⟩ := opSide_read opEquationRhsArmsRead_true hmem hget
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_rhs.lookup
    op_equation_rhs_noControl ev
  have hp : (IxVM.KernelRoleSpec.op_equation_rhs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["tbl", "r", "k"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_rhs.body =
      .matchValue (.binary .add (.binary .mul (.literal 64) (.var "r")) (.var "k"))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_rhs.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨x1, ⟨T, hT, her⟩, -, hplain⟩ := keyed_renders htwf hk hread htbl d0
  have heq : eq ∈ Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey) :=
    List.mem_of_getElem? hget
  obtain ⟨L, m₁, m₂, rfl, -, hL⟩ :=
    rendered_side_shape (sideShape_all _ hmem eq heq).2 her
  exact ⟨x1, L, m₁, m₂, hT, hL, hplain⟩

/-! ## The constants a side names -/

/-- The constants a side of the operation `r`'s recurrences may name: `r` itself, a walked role
of an earlier group, or, at `Nat.beq` and `Nat.ble`, a `Bool` constructor. -/
def sideNamedOk (r : Role) : KKey → Bool
  | .role r' => decide (r' = r) ||
      (IxVM.Consistency.walkedRole r' &&
        decide (Ix.SpecDigest.groupOf r' < Ix.SpecDigest.groupOf r)) ||
      ((decide (r' = .boolTrue) || decide (r' = .boolFalse)) &&
        (decide (r = .natBeq) || decide (r = .natBle)))
  | _ => false

set_option maxRecDepth 100000 in
/-- **Every constant a recurrence side names is the operation, a walked role of an earlier
group, or a `Bool` constructor of `Nat.beq` and `Nat.ble`** (decided over the seven structural
operations). -/
theorem sidesNamed_all : Role.all.all (fun r =>
    if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames then
      (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)).all (fun eq =>
        eq.1.constsResolveBy (sideNamedOk r) && eq.2.constsResolveBy (sideNamedOk r))
    else true) = true := by
  decide +kernel

theorem sidesNamed {r : Role} (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    {eq : KExpr × KExpr} (heq : eq ∈ Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)) :
    eq.1.constsResolveBy (sideNamedOk r) = true ∧ eq.2.constsResolveBy (sideNamedOk r) = true := by
  have h1 := List.all_eq_true.mp sidesNamed_all r (Role.mem_all r)
  rw [ite_eq_left hmem] at h1
  have h2 := List.all_eq_true.mp h1 eq heq
  simpa only [Bool.and_eq_true] using h2

set_option maxRecDepth 100000 in
/-- **The operations' tables** (decided): at a structural operation `op_evidence_is_proof` is
`0`, `op_equation_count` is the number of recurrences and `Nat` may be named; at a well-founded
one `op_evidence_is_proof` is `1` and `op_equation_count` is the number of certificates. -/
theorem opTables_all : Role.all.all (fun r =>
    (if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames then
      RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
          (roleNum r) == some 0 &&
        RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body)
          (roleNum r) ==
          some (((Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)).length : Nat) : F) &&
        sideNamedOk r (Ix.Kernel.natName : KKey) &&
        decide ((Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)).length < 64)
    else true) &&
    (if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames then
      RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
          (roleNum r) == some 1 &&
        RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body)
          (roleNum r) ==
          some (((Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)).length : Nat) : F)
    else true)) = true := by
  decide +kernel

theorem opTables_struct {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames) :
    RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
        (roleNum r) = some 0 ∧
      RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body)
        (roleNum r) =
        some (((Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)).length : Nat) : F) ∧
      sideNamedOk r (Ix.Kernel.natName : KKey) = true ∧
      (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)).length < 64 := by
  have h1 := List.all_eq_true.mp opTables_all r (Role.mem_all r)
  rw [Bool.and_eq_true, ite_eq_left hmem] at h1
  simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h1.1

theorem opTables_wf {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames) :
    RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
        (roleNum r) = some 1 ∧
      RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body)
        (roleNum r) =
        some (((Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)).length : Nat) : F) := by
  have h1 := List.all_eq_true.mp opTables_all r (Role.mem_all r)
  rw [Bool.and_eq_true] at h1
  have h2 := h1.2
  rw [ite_eq_left hmem] at h2
  simpa only [Bool.and_eq_true, beq_iff_eq] using h2

/-! ## One recurrence -/

set_option maxHeartbeats 1600000 in
/-- **One recurrence, from the comparison `validate_op_equations` makes at its index**: at a
structural operation, the entry at index `k` of the evidence compares the `k`-th recurrence
(`OpRefine.EqObs`), at the keying of the closure's environment `env`. The premises: the role
context, the table, the operation's address `b` (keyed as the operation), the value `x_val`
(the operation's value under the table's keying, its cells stored in `env`), and the constants
the sides name stored in `env` (all but the operation). -/
theorem eqObs_of_seg {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    (hpz : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
      (roleNum r) = some 0)
    (hnatOk : sideNamedOk r (Ix.Kernel.natName : KKey) = true)
    {Ec : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Nat} {val : KExpr}
    {x_rc x_tbl x_a x_val : SourceValue F} {b : Bytes.Address} {h₀ : Heap F}
    (hrc : RCRep t (some lim) h₀ x_rc) (htbl : TableRep t h₀ x_tbl)
    (hb : Bytes.RepAddressRef addrTy h₀ b x_a) (hkb : keyOf t (ixAddr b) = .role r)
    (hv : TmC (keyOf t) h₀ val x_val)
    (hvcells : ∀ h₂, Heap.Extends h₀ h₂ → ∀ x, AddrIn h₂ x_val x →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    (hside : ∀ x : Bytes.Address, sideNamedOk r (keyOf t (ixAddr x)) = true → x ≠ b →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    {e rest x_ev : SourceValue F} {k : Nat} {h : Heap F} {res : SourceValue F} {h' : Heap F}
    {cs : List (Call F)} (ext0 : Heap.Extends h₀ h)
    (sg : Obs.«KernelRoles::validate_op_equations».Seg1 e rest x_rc x_tbl (.field (roleNum r))
      x_a x_val x_ev (.field ((k : Nat) : F)) h res h' cs)
    (hgood : Good ⟨Ec, env, t, none⟩ cs) :
    ∀ eq, (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k]? = some eq →
      OpRefine.EqObs Ec t lim env (.role r) val eq := by
  intro eq hget
  have htwf : t.wf = true := wf_of_check ht
  have heq : eq ∈ Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey) :=
    List.mem_of_getElem? hget
  obtain ⟨hsL, hsR⟩ := sidesNamed hmem heq
  let cx : Ctx := ⟨Ec, env, t, some lim⟩
  let Γ : Nat → KExpr := fun _ => OpOpen.natTy
  have hinj : ∀ b', keyOf t (ixAddr b') = keyOf t (ixAddr b) → b' = b :=
    fun b' hk => Decl.ixAddr_injective (Decl.keyOf_injective htwf hk)
  have hnat : ∀ x : Bytes.Address, keyOf t (ixAddr x) = (Ix.Kernel.natName : KKey) →
      cx.stored.κ (ixAddr x) = (Ix.Kernel.natName : KKey) := by
    intro x hx
    have hne : x ≠ b := by
      intro hxb
      subst hxb
      rw [hkb] at hx
      rw [hx] at hmem
      exact absurd hmem (by decide)
    obtain ⟨ci, hci⟩ := hside x (by rw [hx]; exact hnatOk) hne
    exact (Ctx.stored_key_of_find (c := cx) hci).trans hx
  match sg with
  | .n0_Defeq (m86 := m86) (m101 := m101) (m150 := m150) (m165 := m165) (m251 := m251)
      (m287 := m287) (m228 := m228) (x_lhs := xl) (x_types := xty) (x_rhs := xr) (v240 := vl)
      (v241 := vr) (v225 := v225) (cs236 := cs236) (ev56 := ev56) (ev111 := ev111)
      (ev98 := ev98) (ev175 := ev175) (ev162 := ev162) (ev261 := ev261) (ev297 := ev297)
      (ev238 := ev238) (heq335 := heq335) (hc340 := hc) .. =>
    obtain ⟨-, hm43⟩ := op_evidence_is_proof_val hpz ev56
    subst hm43
    have x111 := ev111.heap_extends
    have x98 := ev98.heap_extends
    have x175 := ev175.heap_extends
    have x162 := ev162.heap_extends
    have x261 := ev261.heap_extends
    have x297 := ev297.heap_extends
    obtain ⟨-, L₁, a₁, a₂, hTL, hLL, hpL0⟩ := opEquationLhs_full hmem hget htwf (htbl.mono ext0) ev111
    obtain ⟨bodyL, typesL, htupL, hbodyL, hpL, htypesL, -⟩ :=
      open_two_lams_nat (κ' := cx.stored.κ) hTL.toTmC hpL0 hnat ev98
    cases htupL
    obtain ⟨-, L₂, b₁, b₂, hTR, hLR, hpR0⟩ := opEquationRhs_full hmem hget htwf
      (htbl.mono (ext0.trans (x111.trans x98))) ev175
    obtain ⟨bodyR, typesR, htupR, hbodyR, hpR, -, -⟩ :=
      open_two_lams_nat (κ' := cx.stored.κ) hTR.toTmC hpR0 hnat ev162
    cases htupR
    have e150 : Heap.Extends h₀ m150 := ext0.trans (x111.trans (x98.trans (x175.trans x162)))
    have hXL : Tm (keyOf t) 2 Γ m150 0 eq.1 xl := by
      have := hbodyL.mono (x175.trans x162)
      rwa [hLL] at this
    have hXR : Tm (keyOf t) 2 Γ m251 0 eq.2 xr := by
      have := hbodyR.mono x261
      rwa [hLR] at this
    have hb150 := Bytes.repAddressRef_heapMono₂ addrTy e150 hb
    have hb251 := Bytes.repAddressRef_heapMono₂ addrTy (e150.trans x261) hb
    obtain ⟨hrL, -⟩ := OpOpen.subst_const_spec hinj hb150 (hv.mono e150) hXL ev261
    obtain ⟨hrR, -⟩ := OpOpen.subst_const_spec hinj hb251 (hv.mono (e150.trans x261)) hXR ev297
    rw [hkb, (OpOpen.substConstAll_eq_substConst0_of_natOpEquations (n := .role r) (r := val)
      heq).1] at hrL
    rw [hkb, (OpOpen.substConstAll_eq_substConst0_of_natOpEquations (n := .role r) (r := val)
      heq).2] at hrR
    have storedL : ∀ x, AddrIn m251 vl x → ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci := by
      intro x hin
      have hpl := hpL.mono (x175.trans (x162.trans x261))
      rcases subst_const_cells (keyOf t) 2 Γ x_a x_val b val hinj _ _ _ _ _ _ ev261 rfl xl 0 eq.1
          rfl hXL hb150 (hv.mono e150) m251 (Heap.Extends.refl _) x hin with h1 | ⟨h1, hne⟩ | h1
      · exact hvcells m251 (e150.trans x261) x h1
      · exact hside x (LetProjFree.addrIn_named (hXL.mono x261) hpl x h1 _ hsL) hne
      · exact (LetProjFree.not_projIn h1 hpl).elim
    have storedR : ∀ x, AddrIn m287 vr x → ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci := by
      intro x hin
      have hpr := hpR.mono (x261.trans x297)
      rcases subst_const_cells (keyOf t) 2 Γ x_a x_val b val hinj _ _ _ _ _ _ ev297 rfl xr 0 eq.2
          rfl hXR hb251 (hv.mono (e150.trans x261)) m287 (Heap.Extends.refl _) x hin
          with h1 | ⟨h1, hne⟩ | h1
      · exact hvcells m287 (e150.trans (x261.trans x297)) x h1
      · exact hside x (LetProjFree.addrIn_named (hXR.mono x297) hpr x h1 _ hsR) hne
      · exact (LetProjFree.not_projIn h1 hpr).elim
    have hlp : Tm cx.stored.κ 2 Γ m287 0 (Expr.substConst0 (.role r) val eq.1) vl :=
      (hrL.rekey
        (fun x hin => by
          obtain ⟨ci, hci⟩ := storedL x hin
          exact Ctx.stored_key_of_find (c := cx) hci)
        (fun x hp _ => by
          obtain ⟨ci, hci⟩ := storedL x hp.addrIn
          exact Ctx.stored_projPermitted_of_find (c := cx) hci)).mono x297
    have hrp : Tm cx.stored.κ 2 Γ m287 0 (Expr.substConst0 (.role r) val eq.2) vr :=
      hrR.rekey
        (fun x hin => by
          obtain ⟨ci, hci⟩ := storedR x hin
          exact Ctx.stored_key_of_find (c := cx) hci)
        (fun x hp _ => by
          obtain ⟨ci, hci⟩ := storedR x hp.addrIn
          exact Ctx.stored_projPermitted_of_find (c := cx) hci)
    rw [heq335] at ev238
    exact ⟨Γ, x_rc, xty, vl, vr, m287, m228, cs236,
      hrc.mono (e150.trans (x261.trans x297)),
      htypesL.mono (x175.trans (x162.trans (x261.trans x297))), OpOpen.ghostScoped_natTy 2,
      ev238, hgood.sub (fun cl hm => by rw [hc]; simp [hm]), hlp, hrp⟩
  | .n0_Proof (heq379 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
  | .other_Defeq (ev56 := ev56) (hne386 := hne) .. =>
    exact (hne (op_evidence_is_proof_val hpz ev56).1).elim
  | .other_Proof_Defn_Theorem (ev56 := ev56) (hne386 := hne) .. =>
    exact (hne (op_evidence_is_proof_val hpz ev56).1).elim
  | .other_Proof_Defn_other (ev56 := ev56) (hne386 := hne) .. =>
    exact (hne (op_evidence_is_proof_val hpz ev56).1).elim
  | .other_Proof_other (ev56 := ev56) (hne386 := hne) .. =>
    exact (hne (op_evidence_is_proof_val hpz ev56).1).elim

/-- **Every recurrence, from the walk of the evidence list** (`validate_op_equations` from index
`k`): at a structural operation, each entry of the evidence list compares the recurrence at its
index. -/
theorem eqObs_of_evidence {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames)
    (hpz : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
      (roleNum r) = some 0)
    (hnatOk : sideNamedOk r (Ix.Kernel.natName : KKey) = true)
    {Ec : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Nat} {val : KExpr}
    {x_rc x_tbl x_a x_val : SourceValue F} {b : Bytes.Address} {h₀ : Heap F}
    (hrc : RCRep t (some lim) h₀ x_rc) (htbl : TableRep t h₀ x_tbl)
    (hb : Bytes.RepAddressRef addrTy h₀ b x_a) (hkb : keyOf t (ixAddr b) = .role r)
    (hv : TmC (keyOf t) h₀ val x_val)
    (hvcells : ∀ h₂, Heap.Extends h₀ h₂ → ∀ x, AddrIn h₂ x_val x →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    (hside : ∀ x : Bytes.Address, sideNamedOk r (keyOf t (ixAddr x)) = true → x ≠ b →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci) :
    ∀ {es : List (Ix.Kernel.Evidence _root_.Address)} (k : Nat) {x_ev res : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      Heap.Extends h₀ h → RepList evListEnum EvRep h es x_ev →
      ObsFn W "KernelRoles::validate_op_equations"
        [x_rc, x_tbl, .field (roleNum r), x_a, x_val, x_ev, .field ((k : Nat) : F)] h res h' cs →
      Good ⟨Ec, env, t, none⟩ cs →
      ∀ i, i < es.length → ∀ eq,
        (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k + i]? = some eq →
        OpRefine.EqObs Ec t lim env (.role r) val eq
  | es, k, x_ev, res, h, h', cs, ext0, hlist, ev, hgood => by
    cases Obs.«KernelRoles::validate_op_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      intro i hi
      cases hi
    | Cons x_e x_rest v2523 m2524 cs2526 cs2535 v2544 ld12 sg2531 op2600 ev2537 hc2602 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have tailMember : (⟨"KernelRoles::validate_op_equations",
          [x_rc, x_tbl, .field (roleNum r), x_a, x_val, x_rest, v2544], m2524⟩ : Call F) ∈
          cs := by
        rw [hc2602]; simp
      have ext1 : Heap.Extends h m2524 := (ev.call_heap_bounds tailMember).1
      obtain rfl := Decl.evalBinOp_add_one k op2600
      have hhead := eqObs_of_seg ht hmem hpz hnatOk hrc htbl hb hkb hv hvcells hside ext0 sg2531
        (hgood.sub (fun cl hm => by rw [hc2602]; simp [hm]))
      have htail := eqObs_of_evidence ht hmem hpz hnatOk hrc htbl hb hkb hv hvcells hside (k + 1)
        (ext0.trans ext1) (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev2537
        (hgood.sub (fun cl hm => by rw [hc2602]; simp [hm]))
      intro i hi eq hget
      cases i with
      | zero => exact hhead eq (by simpa using hget)
      | succ i =>
        exact htail i (by simp at hi; omega) eq
          (by rwa [show k + (i + 1) = k + 1 + i by omega] at hget)

/-! ## The structural half of `OpEquationFacts` -/

private theorem evList_length' {es : List (Ix.Kernel.Evidence _root_.Address)}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<KernelRoles::RoleEvidence>» [l] h r h' cs)
    (hl : RepList evListEnum EvRep h es l) :
    r = .field (es.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [.named "KernelRoles::RoleEvidence" []]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelRoles::RoleEvidence>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.named "KernelRoles::RoleEvidence" []]).symbol
      EvRep h es l := by
    rw [Obs.Names.«Lists::Node<KernelRoles::RoleEvidence>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

/-- A list whose length is `n` in the field, for a small `n`, has at least `n` entries. -/
private theorem le_length_of_cast {n m : Nat} (hn : n < 4294967296)
    (e : ((m : Nat) : F) = ((n : Nat) : F)) : n ≤ m := by
  have hv := congrArg ZMod.val e
  rw [ZMod.val_natCast, Claim.val_of_lt_u32 hn] at hv
  exact hv ▸ Nat.mod_le _ _

set_option maxHeartbeats 3200000 in
/-- **The structural half of `OpEquationFacts`**: at a structural operation, from the observed
`validate_role`, one comparison per recurrence (`OpRefine.EqObs`) at the closure's environment.
The value `validate_op_equations` substitutes is the pointer of `validate_role`'s own load,
which represents the canonical annotation of the value's reading
(`LoadedReads.get_ci_defn_value_exact`); its cells are references the record uses, stored by
`Decl.UsedRefsStored`; the constants the sides name are stored by the closure's coverage
(`WalkedStored`, walked roles of earlier groups) and by the prefix (`Bool`'s constructors). -/
theorem opEquationFacts_struct {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (ht : t.check = .ok ())
    {g : Nat} {r : Role} {a : _root_.Address} {R R₁ R' Ec : Ixon.Env}
    {env₁ : Ix.Kernel.Env .anon} {c : Ixon.Constant} {d : Ixon.Definition} {val₀ val : KExpr}
    (hgrp : IxVM.Consistency.roleGroup g = [r]) (hop : r ∈ RoleOps.opRoles)
    (ha : t.addressOf? r = some a) (hadm : Admits ρ t g R R') (hrd : AdmitsReads ρ t R R')
    (hws : WalkedStored ρ t (· < g) R₁ env₁) (hEc : Typing.RecordsFor R' Ec)
    (hst : Typing.StepStore calls t ρ.E₀ Ec)
    (hcE : IxVM.Consistency.recordOf ρ.E₀ a = some c) (hinfo : c.info = .defn d)
    (hlv0 : d.lvls.toNat = 0) (hlogic : IxVM.Consistency.InLogic c)
    (hvl : (IxVM.Consistency.exprReader t (fun x => ρ.E₀.blobs.get? x) c id
      (IxVM.Consistency.soloSelf t a)).read d.value = .ok val₀)
    (h3 : val₀.looseBVarsBounded 0 = true) (h4 : val₀.allLevelParamsDefined [] = true)
    (hcV : LoadedReads.canonAnn c [] (0 + 1) d.value val₀ = some val)
    (hstored : Decl.UsedRefsStored t env₁ c) (hpre : RoleOps.WfPrefix env₁ (.role r))
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames) :
    ∀ eq ∈ Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey),
      OpRefine.EqObs Ec t (valLimit g) env₁ (.role r) val eq := by
  intro eq heq
  have htwf : t.wf = true := wf_of_check ht
  have hrg : r ∈ IxVM.Consistency.roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := OpInstall.groupOf_of_mem_roleGroup hrg
  obtain ⟨hpz, hcount, hnatOk, h64⟩ := opTables_struct hmem
  obtain ⟨bAddr, tb, -, -, hρ⟩ := hrun.observed
  have hval : RoleVal.ValidateRoleIn calls bAddr t g r := by
    have e : ρ.validated = (observedRun calls bAddr t ρ.E₀ ρ.rank).validated :=
      congrArg BRun.validated hρ
    have h1 := hadm.validated r hrg
    rw [e] at h1
    exact h1
  have hcR' : IxVM.Consistency.recordOf R' a = some c := by
    obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp
      (hadm.kept r hrg (Or.inl (OpInstall.op_kept hop).1) a ha)
    have h1 := recordOf_sub hadm.loaded a c₁ hc₁
    rw [hcE] at h1
    rw [hc₁, Option.some.inj h1]
  have hcEc : IxVM.Consistency.recordOf Ec a = some c :=
    (Typing.recordOf_eq_recordAt_of_decoded hEc.1 a).trans (hEc.2.1 a c hcR')
  have hblobEc : ∀ x b, ρ.E₀.blobs.get? x = some b → Ec.blobs.get? x = some b :=
    fun x b hx => hEc.2.2.1 x b (hrd.blobs x b hx)
  have hgood : Good ⟨Ec, env₁, t, none⟩ calls := hst.good env₁ none
  have hk2 : RoleVal.roleSpecKindNat r = 2 := (specKind_two_iff r).mpr hop
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsubV⟩ := hval
  have htblR : TableRep t h x_tbl := htbl.toTableRep
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n2 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs236
      ev14 ev47 ld41 ev80 ev100 heq109 ev124 ev238 hc279 =>
    have hsub45 : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc279]; simp [hm])
    have hsub236 : ∀ cl ∈ cs236, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc279]; simp [hm])
    obtain ⟨ext_ba, a', ha_m2, had⟩ := RoleVal.role_bound_addr_uncond htblR ev14
    have ea : a' = a := Option.some.inj (had.symm.trans ha)
    subst ea
    obtain ⟨b, hbr, hba⟩ := ha_m2
    subst hba
    have hkb : keyOf t (ixAddr b) = .role r := keyOf_of_addressOf htwf had
    have ext32_111 : Heap.Extends m32 m111 :=
      ev80.heap_extends.trans (ev100.heap_extends.trans ev124.heap_extends)
    have exth_111 : Heap.Extends h m111 := ext_ba.trans (ev47.heap_extends.trans ext32_111)
    -- the value pointer of the role's own load
    have hvlEc := ReaderReads.exprReader_mono hblobEc hvl
    have h4' : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true := by
      rw [hlv0]; exact h4
    obtain ⟨tyPtr, valPtr, hintV, blobs, val', hcV', hldv, htmV, rval⟩ :=
      LoadedReads.get_ci_defn_value_exact ht (hgood.sub hsub45).1 hbr ev47 hcEc hinfo hlogic
        hvlEc h3 h4'
    have hvv : val' = val := by
      rw [hlv0] at hcV'
      exact Option.some.inj (hcV'.symm.trans hcV)
    rw [hvv, hlv0, Decl.posOf_range] at htmV
    have hv31 : v31 = L1.defnValShape d tyPtr valPtr hintV :=
      Except.ok.inj (ld41.symm.trans hldv)
    match Obs.«KernelRoles::validate_op».obs ev238 with
    | .other (heq575 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
    | .Defn (m391 := m391) (m400 := m400) (m443 := m443) (m463 := m463) (v399 := v399)
        (v440 := v440) (v441 := v441) (x_val := x_val) (cs486 := cs486) (hv114 := hci)
        (ev412 := ev412) (ev453 := ev453) (ev473 := ev473) (heq482 := heq482) (ev488 := ev488)
        (hc544 := hca) .. =>
      have memE : (⟨"KernelRoles::validate_op_equations",
          [x_rc, x_tbl, .field (roleNum r), v1, x_val, v399, .field 0], m463⟩ : Call F) ∈
          cs236 := by
        rw [hca]; simp
      have memR : (⟨"KernelRoles::role_evidence", [x_tbl, .field (roleNum r)], m391⟩ :
          Call F) ∈ cs236 := by
        rw [hca]; simp
      have ext111_463 : Heap.Extends m111 m463 := (ev238.call_heap_bounds memE).1
      have ext111_391 : Heap.Extends m111 m391 := (ev238.call_heap_bounds memR).1
      have hsub486 : ∀ cl ∈ cs486, cl ∈ calls := fun cl hm => hsub236 cl (by rw [hca]; simp [hm])
      -- the value pointer is the role's own load's
      rw [hv31] at hci
      have hkind : d.kind = .defn := by
        cases hk : d.kind with
        | defn => rfl
        | opaq => simp [L1.defnValShape, hk, Core.kciEnum] at hci
        | thm => simp [L1.defnValShape, hk, Core.kciEnum] at hci
      have hsh : L1.defnValShape d tyPtr valPtr hintV = .construct Core.kciEnum "Defn"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repDefSafetyVal d.safety, hintV] := by
        simp [L1.defnValShape, hkind]
      rw [hsh] at hci
      have hfl := (Value.construct.inj hci).2.2
      simp only [List.cons.injEq] at hfl
      obtain ⟨-, -, hxval, -, -⟩ := hfl
      -- the evidence list and its length
      let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
      obtain ⟨es, hlist, -⟩ := role_evidence_step (ScopedCtx.unrestricted c₀) ev412 x_tbl r rfl
        (htblR.mono (exth_111.trans ext111_391))
      obtain ⟨hlen, hm443⟩ := evList_length' ev453 hlist
      obtain ⟨hcnt, hm463⟩ := op_equation_count_val hcount ev473
      have hlist463 : RepList evListEnum EvRep m463 es v399 := by
        rw [hm463, hm443]; exact hlist
      have hge : (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)).length ≤
          es.length :=
        le_length_of_cast (by omega) (Value.field.inj (hlen.symm.trans (heq482.trans hcnt)))
      -- the premises of the walk, at the walk's heap
      have ext32_463 : Heap.Extends m32 m463 := ext32_111.trans ext111_463
      have hv463 : TmC (keyOf t) m463 val valPtr := (htmV.mono ext32_463).toTmC
      have hvcells : ∀ h₂, Heap.Extends m463 h₂ → ∀ x, AddrIn h₂ valPtr x →
          ∃ ci, env₁.find? (keyOf t (ixAddr x)) = some ci := by
        intro h₂ e₂ x hin
        have hin32 := TmExact.addrIn_back (htmV 0 (fun _ => .sort .zero)) (ext32_463.trans e₂)
          x hin
        rcases L1.RawConvExpr.addrIn_used rval x hin32 with ⟨i, hi, hr⟩ | hr
        · have hu : i ∈ IxVM.Consistency.usedRefIdxs c := by
            unfold IxVM.Consistency.usedRefIdxs
            rw [hinfo]
            rcases hi with hi | ⟨s, hs, his⟩
            · exact List.mem_append_right _ (List.mem_append_right _ hi)
            · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
          exact hstored i hu (ixAddr x) hr
        · cases hr
      have hside : ∀ x : Bytes.Address, sideNamedOk r (keyOf t (ixAddr x)) = true → x ≠ b →
          ∃ ci, env₁.find? (keyOf t (ixAddr x)) = some ci := by
        intro x hn hne
        cases hk : keyOf t (ixAddr x) with
        | role r' =>
          rw [hk] at hn
          simp only [sideNamedOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hn
          rcases hn with (hrr | ⟨hw, hlt⟩) | ⟨hb', hbr'⟩
          · exfalso
            subst hrr
            exact hne (Decl.ixAddr_injective (Decl.keyOf_injective htwf (hk.trans hkb.symm)))
          · have hs := hws.2 r' (ixAddr x) hw (by rw [← hgr]; exact hlt)
              (addressOf_of_keyOf htwf hk)
            rw [show IxVM.Consistency.keyOf t (ixAddr x) = .role r' from hk] at hs
            exact Option.isSome_iff_exists.mp hs
          · obtain ⟨⟨ci₁, hci₁, -⟩, ⟨ci₂, hci₂, -⟩⟩ := hpre.op.boolCtors (by
              rcases hbr' with rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl))
            rcases hb' with rfl | rfl
            · exact ⟨ci₁, hci₁⟩
            · exact ⟨ci₂, hci₂⟩
        | _ => simp [hk, sideNamedOk] at hn
      have hall := eqObs_of_evidence (Ec := Ec) (env := env₁) (lim := valLimit g) (val := val)
        ht hmem hpz hnatOk
        (Claim.RCFullRep.toRCRep (hrc.mono (exth_111.trans ext111_463)))
        (htblR.mono (exth_111.trans ext111_463))
        (Bytes.repAddressRef_heapMono₂ addrTy (ev47.heap_extends.trans ext32_463) hbr)
        hkb hv463 hvcells hside (es := es) 0 (Heap.Extends.refl _) hlist463
        (by rw [← hxval] at ev488; simpa using ev488) (hgood.sub hsub486)
      obtain ⟨i, hgi⟩ := List.mem_iff_getElem?.mp heq
      have hi : i < (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey)).length := by
        by_contra hge'
        rw [List.getElem?_eq_none (by omega)] at hgi
        cases hgi
      exact hall i (by omega) eq (by simpa using hgi)
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)

/-! ## `OpEquationFacts` from its certificates' half -/

/-- **The certificates' half of `OpEquationFacts`**: under the premises of `OpEquationFacts`, at
a well-founded operation, one proof per certificate statement, closed, with no `let` and no
level parameter, checked against the statement (`OpRefine.CertObs`). -/
def OpCertFacts (calls : List (Call F)) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (ρ : BRun) (Rs : Nat → Ixon.Env), BindingRun calls t ρ Rs →
    t.check = .ok () →
    ∀ (g : Nat) (r : Role) (a : _root_.Address) (R R₁ R' Ec : Ixon.Env)
      (env₁ : Ix.Kernel.Env .anon) (c : Ixon.Constant) (d : Ixon.Definition) (val₀ val : KExpr),
      6 ≤ g → g < 77 → IxVM.Consistency.roleGroup g = [r] → r ∈ RoleOps.opRoles →
      t.addressOf? r = some a →
      Admits ρ t g R R' → AdmitsReads ρ t R R' → AddsAt R₁ R' a →
      WalkedStored ρ t (· < g) R₁ env₁ →
      Typing.RecordsFor R' Ec → Typing.StepStore calls t ρ.E₀ Ec →
      Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁ →
      IxVM.Consistency.recordOf ρ.E₀ a = some c → c.info = .defn d → d.lvls.toNat = 0 →
      IxVM.Consistency.InLogic c →
      (IxVM.Consistency.exprReader t (fun x => ρ.E₀.blobs.get? x) c id
        (IxVM.Consistency.soloSelf t a)).read d.value = .ok val₀ →
      val₀.looseBVarsBounded 0 = true → val₀.allLevelParamsDefined [] = true →
      LoadedReads.canonAnn c [] (0 + 1) d.value val₀ = some val →
      Decl.UsedRefsStored t env₁ c → RoleOps.WfPrefix env₁ (.role r) →
      (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames →
        ∃ proofs : List KExpr, List.Forall₂ (fun st P =>
          P.looseBVarsBounded 0 = true ∧ P.hasFvar = false ∧ Decl.noLetExpr P = true ∧
            P.allLevelParamsDefined [] = true ∧
            OpRefine.CertObs Ec t (valLimit g) env₁ (.role r) val st P)
          (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)) proofs

/-- **`OpEquationFacts` from its certificates' half**: the recurrences are
`opEquationFacts_struct`. -/
theorem opEquationFacts_of_certs {calls : List (Call F)} (hcert : OpCertFacts.{u} calls) :
    OpEquationFacts.{u} calls := by
  intro t ρ Rs hrun ht g r a R R₁ R' Ec env₁ c d val₀ val h6 h77 hgrp hop ha hadm hrd hadds hws
    hEc hst hinv hcE hinfo hlv0 hlogic hvl h3 h4 hcV hstored hpre
  exact ⟨fun hmem => opEquationFacts_struct hrun ht hgrp hop ha hadm hrd hws hEc hst hcE hinfo
      hlv0 hlogic hvl h3 h4 hcV hstored hpre hmem,
    hcert t ρ Rs hrun ht g r a R R₁ R' Ec env₁ c d val₀ val h6 h77 hgrp hop ha hadm hrd hadds hws
      hEc hst hinv hcE hinfo hlv0 hlogic hvl h3 h4 hcV hstored hpre⟩

/-- **`OpValidationFactsW` from the certificates' half.** -/
theorem opValidationFactsW_of_certs (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    {calls : List (Call F)} (hcert : OpCertFacts.{u} calls) : OpValidationFactsW.{u} L calls :=
  opValidationFactsW_of_equations L calls (opEquationFacts_of_certs hcert)

end IxVM.Refinement.Binding
