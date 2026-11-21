import IxVMRefinement.Binding.CertProof
import IxVMRefinement.Binding.OpEquationObs

/-! # A certificate statement, rendered, replaced and opened

`validate_op_equations` checks the `k`-th certificate of a well-founded operation against
`open_foralls(subst_const(op_certificate(tbl, r, k), a, val), Nil)`, with as many variables as the
context list it returns has entries. This file reads that statement at the keying of the closure's
environment.

* `EqUpToBinders`, `eqUpTo_of_erasePw`: a term equal up to binder data to a `∀`-telescope whose
  domains and body are rigid is that telescope with other data at its binders; opening its binders
  (`openPisAtFvars_eqUpTo`) and the constants it names (`constsResolveBy_eqUpTo`) do not see the
  data.
* `openPisAtFvars_substConstAll`: replacing a constant by a closed value commutes with opening
  binders whose domains do not name it.
* `certOk_all` (decided): every certificate statement is such a telescope, opens to its
  hypotheses and equation, names only the operation, walked roles of earlier groups, `Eq` and the
  `Bool` constructors, and its context is scoped.
* `open_foralls_full`: `OpOpen.open_foralls_spec` with the length of the context list.
* `certStmt_open`: the statement and its context list, at the closure's keying.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role Expr)

/-! ## Terms equal up to their first binders' data -/

/-- **`T` is `E` with possibly other data at its first `n` `∀` binders.** -/
inductive EqUpToBinders : Nat → KExpr → KExpr → Prop where
  | zero (T : KExpr) : EqUpToBinders 0 T T
  | succ {n : Nat} (A : KExpr) {B B' : KExpr} (m m' : Ix.Kernel.BinderMeta) :
      EqUpToBinders n B B' → EqUpToBinders (n + 1) (.forallE A B m) (.forallE A B' m')

/-- **The first `n` binders of the term are `∀`s with rigid domains, before a rigid body.** -/
def spineRigid : Nat → KExpr → Bool
  | 0, e => pwRigid e
  | n + 1, .forallE A B _ => pwRigid A && spineRigid n B
  | _ + 1, _ => false

theorem eqUpTo_of_erasePw (n : Nat) : ∀ (E T : KExpr), spineRigid n E = true →
    T.erasePw = E.erasePw → EqUpToBinders n T E := by
  induction n with
  | zero =>
    intro E T hs h
    have e := eq_of_erasePw_rigid E hs T h
    subst e
    exact .zero _
  | succ n ih =>
    intro E T hs h
    cases E with
    | forallE A B m =>
      simp only [spineRigid, Bool.and_eq_true] at hs
      cases T with
      | forallE A' B' m' =>
        simp only [Ix.Kernel.Expr.erasePw] at h
        injection h with hA hB _
        have eA := eq_of_erasePw_rigid A hs.1 A' hA
        subst eA
        exact .succ _ _ _ (ih B B' hs.2 hB)
      | _ => simp only [Ix.Kernel.Expr.erasePw] at h; exact nomatch h
    | _ => simp [spineRigid] at hs

theorem EqUpToBinders.instantiate1 {n : Nat} {T E : KExpr} (h : EqUpToBinders n T E) :
    ∀ (v : KExpr) (j : Nat), EqUpToBinders n (T.instantiate1 v j) (E.instantiate1 v j) := by
  induction h with
  | zero T => intro v j; exact .zero _
  | succ A m m' _ ih =>
    intro v j
    exact .succ _ _ _ (ih v (j + 1))

theorem openPisAtFvars_eqUpTo (n : Nat) : ∀ {T E : KExpr}, EqUpToBinders n T E → ∀ d,
    Ix.Kernel.openPisAtFvars n T d = Ix.Kernel.openPisAtFvars n E d := by
  induction n with
  | zero =>
    intro T E h d
    cases h
    rfl
  | succ n ih =>
    intro T E h d
    cases h with
    | succ A m m' hB =>
      have ih' := ih (hB.instantiate1 (.fvar d A) 0) (d + 1)
      simp only [Ix.Kernel.openPisAtFvars, ih']

theorem constsResolveBy_eqUpTo (P : KKey → Bool) {n : Nat} {T E : KExpr}
    (h : EqUpToBinders n T E) : T.constsResolveBy P = E.constsResolveBy P := by
  induction h with
  | zero T => rfl
  | succ A m m' _ ih => simp only [Ix.Kernel.Expr.constsResolveBy, ih]

/-! ## Replacing a constant and opening binders -/

/-- **A term that does not name the constant is unchanged by its replacement.** -/
theorem substConstAll_of_not_named {n : KKey} {r : KExpr} :
    ∀ e : KExpr, e.constsResolveBy (fun k => k != n) = true → Expr.substConstAll n r e = e := by
  intro e
  induction e with
  | const k us =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolveBy, bne_iff_ne, ne_eq] at h
    simp [Expr.substConstAll, h]
  | app f a ihf iha =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at h
    simp only [Expr.substConstAll, ihf h.1, iha h.2]
  | lam ty b m iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at h
    simp only [Expr.substConstAll, iht h.1, ihb h.2]
  | forallE ty b m iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at h
    simp only [Expr.substConstAll, iht h.1, ihb h.2]
  | letE ty v b l iht ihv ihb =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at h
    simp only [Expr.substConstAll, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i e ih =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolveBy, Bool.and_eq_true] at h
    simp only [Expr.substConstAll, ih h.2]
  | bvar _ => intro _; rfl
  | fvar _ _ _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl

/-- **Replacing a constant by a closed value commutes with instantiating a free variable.** -/
theorem substConstAll_instantiate1_fvar {n : KKey} {r : KExpr}
    (hr : r.looseBVarsBounded 0 = true) (i : Nat) (T : KExpr) :
    ∀ (e : KExpr) (j : Nat),
      Expr.substConstAll n r (e.instantiate1 (.fvar i T) j) =
        (Expr.substConstAll n r e).instantiate1 (.fvar i T) j := by
  intro e
  induction e with
  | bvar k =>
    intro j
    show Expr.substConstAll n r ((Expr.bvar k).instantiate1 (.fvar i T) j) =
      (Expr.bvar k).instantiate1 (.fvar i T) j
    simp only [Ix.Kernel.Expr.instantiate1]
    split_ifs <;> rfl
  | const k us =>
    intro j
    show Expr.substConstAll n r (.const k us) =
      (Expr.substConstAll n r (.const k us)).instantiate1 (.fvar i T) j
    by_cases hc : k = n ∧ us = []
    · simp only [Expr.substConstAll]
      rw [ite_eq_left hc]
      exact (Ix.Kernel.Expr.instantiate1_eq_self
        (Expr.looseBVarsBounded_mono (Nat.zero_le j) hr)).symm
    · simp only [Expr.substConstAll]
      rw [ite_eq_right hc]
      rfl
  | app f a ihf iha =>
    intro j
    simp only [Ix.Kernel.Expr.instantiate1, Expr.substConstAll, ihf, iha]
  | lam ty b m iht ihb =>
    intro j
    simp only [Ix.Kernel.Expr.instantiate1, Expr.substConstAll, iht, ihb]
  | forallE ty b m iht ihb =>
    intro j
    simp only [Ix.Kernel.Expr.instantiate1, Expr.substConstAll, iht, ihb]
  | letE ty v b l iht ihv ihb =>
    intro j
    simp only [Ix.Kernel.Expr.instantiate1, Expr.substConstAll, iht, ihv, ihb]
  | proj s k e ih =>
    intro j
    simp only [Ix.Kernel.Expr.instantiate1, Expr.substConstAll, ih]
  | fvar _ _ _ => intro j; rfl
  | sort _ => intro j; rfl
  | lit _ => intro j; rfl

/-- **Replacing a constant by a closed value commutes with opening binders** whose domains, as
the opened variables carry them, are unchanged by the replacement. -/
theorem openPisAtFvars_substConstAll {c : KKey} {r : KExpr} (hr : r.looseBVarsBounded 0 = true) :
    ∀ (n : Nat) {E body : KExpr} {d : Nat} {fvs : List KExpr},
      Ix.Kernel.openPisAtFvars n E d = some (fvs, body) →
      (∀ i T, Expr.fvar i T ∈ fvs → Expr.substConstAll c r T = T) →
      Ix.Kernel.openPisAtFvars n (Expr.substConstAll c r E) d =
        some (fvs, Expr.substConstAll c r body) := by
  intro n
  induction n with
  | zero =>
    intro E body d fvs hop hfv
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rfl
  | succ n ih =>
    intro E body d fvs hop hfv
    obtain ⟨T, B, m, fvs', rfl, rfl, hop'⟩ := OpOpen.openPisAtFvars_succ_inv hop
    have hT : Expr.substConstAll c r T = T := hfv d T (List.Mem.head _)
    have ih' := ih hop' (fun i T' hm => hfv i T' (List.Mem.tail _ hm))
    rw [substConstAll_instantiate1_fvar hr d T B 0] at ih'
    show Ix.Kernel.openPisAtFvars (n + 1)
      (.forallE (Expr.substConstAll c r T) (Expr.substConstAll c r B) m) d = _
    rw [hT]
    simp only [Ix.Kernel.openPisAtFvars, ih']

/-! ## Scoped contexts, structurally -/

/-- `Expr.wscopedB`, by structural recursion. -/
def fvScoped : Nat → KExpr → Bool
  | d, .fvar idx ty => decide (idx < d) && fvScoped idx ty
  | d, .app f a => fvScoped d f && fvScoped d a
  | d, .lam ty body _ => fvScoped d ty && fvScoped d body
  | d, .forallE ty body _ => fvScoped d ty && fvScoped d body
  | d, .letE ty val body _ => fvScoped d ty && fvScoped d val && fvScoped d body
  | d, .proj _ _ e => fvScoped d e
  | _, .bvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => true

theorem wscopedB_of_fvScoped : ∀ (e : KExpr) (d : Nat), fvScoped d e = true →
    e.wscopedB d = true := by
  intro e
  induction e with
  | fvar idx ty iht =>
    intro d h
    simp only [fvScoped, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1, iht idx h.2⟩
  | app f a ihf iha =>
    intro d h
    simp only [fvScoped, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m iht ihb =>
    intro d h
    simp only [fvScoped, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true]
    exact ⟨iht d h.1, ihb d h.2⟩
  | forallE ty b m iht ihb =>
    intro d h
    simp only [fvScoped, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true]
    exact ⟨iht d h.1, ihb d h.2⟩
  | letE ty v b l iht ihv ihb =>
    intro d h
    simp only [fvScoped, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true]
    exact ⟨⟨iht d h.1.1, ihv d h.1.2⟩, ihb d h.2⟩
  | proj s i e ih =>
    intro d h
    simp only [fvScoped] at h
    simp only [Ix.Kernel.Expr.wscopedB]
    exact ih d h
  | bvar _ => intro d _; simp [Ix.Kernel.Expr.wscopedB]
  | sort _ => intro d _; simp [Ix.Kernel.Expr.wscopedB]
  | const _ _ => intro d _; simp [Ix.Kernel.Expr.wscopedB]
  | lit _ => intro d _; simp [Ix.Kernel.Expr.wscopedB]

/-! ## The certificate statements, decided -/

/-- The context of a certificate statement opened: `x` and `y` of type `Nat`, then the
hypotheses. -/
def ctxOf (st : List KExpr × KExpr) (j : Nat) : KExpr :=
  if j < 2 then OpOpen.natTy else st.1.getD (j - 2) OpOpen.natTy

/-- The constants a certificate of the operation `r` may name: `r` itself, a walked role of an
earlier group, `Eq`, `Bool`, or a `Bool` constructor. -/
def certNamedOk (r : Role) : KKey → Bool
  | .role r' => decide (r' = r) ||
      (IxVM.Consistency.walkedRole r' &&
        decide (Ix.SpecDigest.groupOf r' < Ix.SpecDigest.groupOf r)) ||
      decide (r' = .eq) || decide (r' = .bool) || decide (r' = .boolTrue) ||
      decide (r' = .boolFalse)
  | _ => false

/-- An application. -/
def isApp : KExpr → Bool
  | .app _ _ => true
  | _ => false

/-- **What `validate_op_equations` reads of a certificate statement of the operation `r`.** -/
def certOk (r : Role) (st : List KExpr × KExpr) : Bool :=
  spineRigid (2 + st.1.length) (certRaw st) &&
  decide (Ix.Kernel.openPisAtFvars (2 + st.1.length) (certRaw st) 0 =
    some ((List.range (2 + st.1.length)).map (fun j => .fvar j (ctxOf st j)), st.2)) &&
  (certRaw st).constsResolveBy (certNamedOk r) &&
  (List.range (2 + st.1.length)).all (fun j =>
    (ctxOf st j).constsResolveBy (fun k => k != (Ix.Kernel.Key.role r : KKey)) &&
      fvScoped j (ctxOf st j)) &&
  OpOpen.binderFree st.2 && st.1.all OpOpen.binderFree &&
  (decide (st.1.length = 1) || decide (st.1.length = 2)) && isApp st.2

set_option maxRecDepth 100000 in
/-- **Every certificate statement of every well-founded operation is read so** (decided). -/
theorem certOk_all : Role.all.all (fun r =>
    if (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames then
      (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)).all (certOk r)
    else true) = true := by
  decide +kernel

theorem certOk_spec {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames)
    {st : List KExpr × KExpr}
    (hst : st ∈ Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)) :
    spineRigid (2 + st.1.length) (certRaw st) = true ∧
    Ix.Kernel.openPisAtFvars (2 + st.1.length) (certRaw st) 0 =
      some ((List.range (2 + st.1.length)).map (fun j => .fvar j (ctxOf st j)), st.2) ∧
    (certRaw st).constsResolveBy (certNamedOk r) = true ∧
    (∀ j, j < 2 + st.1.length →
      (ctxOf st j).constsResolveBy (fun k => k != (Ix.Kernel.Key.role r : KKey)) = true ∧
        fvScoped j (ctxOf st j) = true) ∧
    OpOpen.binderFree st.2 = true ∧ (∀ x ∈ st.1, OpOpen.binderFree x = true) ∧
    (st.1.length = 1 ∨ st.1.length = 2) ∧ isApp st.2 = true := by
  have h1 := List.all_eq_true.mp certOk_all r (Role.mem_all r)
  rw [ite_eq_left hmem] at h1
  have h2 := List.all_eq_true.mp h1 st hst
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true,
    List.mem_range] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, ho⟩, hn⟩, hc⟩, hb⟩, hbs⟩, hl⟩, ha⟩ := h2
  exact ⟨hs, ho, hn, fun j hj => (hc j hj), hb, hbs, hl, ha⟩

/-! ## `KernelRoles::open_foralls`, with the length of the context list -/

/-- **`OpOpen.open_foralls_spec` with the length of the context list**: a list of `m` entries
becomes one of `m + n`. -/
theorem open_foralls_full {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {d m : Nat} {E body : KExpr} {fvs : List KExpr} {e acc r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      Ix.Kernel.openPisAtFvars n E d = some (fvs, body) →
      fvs = (List.range n).map (fun j => .fvar (d + j) (Γ (d + j))) →
      (∀ T B m, body ≠ .forallE T B m) →
      OpOpen.ForallSpine h n e → Tm κ d Γ h 0 E e → TypesRep κ Γ h d acc →
      RepList kexprListEnum (fun _ (_ : Unit) _ => True) h (List.replicate m ()) acc →
      ObsFn W "KernelRoles::open_foralls" [e, acc] h r h' cs →
      ∃ bodyp typesp, r = .tuple [bodyp, typesp] ∧ Tm κ (d + n) Γ h' 0 body bodyp ∧
        TypesRep κ Γ h' (d + n) typesp ∧
        RepList kexprListEnum (fun _ (_ : Unit) _ => True) h' (List.replicate (m + n) ()) typesp ∧
        Heap.Extends h h' := by
  intro n
  induction n with
  | zero =>
    intro d m E body fvs e acc r h h' cs hop hfvs hnf sp hE hacc hlist ev
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match Obs.«KernelRoles::open_foralls».obs ev with
    | .Forall (ld12 := ld) .. =>
      obtain ⟨T, B, ℓ, hEq, -⟩ := hE.forallE_of_load ld
      exact (hnf _ _ _ hEq).elim
    | .other (he89 := hr) (he104 := hh) .. =>
      subst hr hh
      exact ⟨e, acc, rfl, hE, hacc, hlist, Heap.Extends.refl _⟩
  | succ n ih =>
    intro d m E body fvs e acc r h h' cs hop hfvs hnf sp hE hacc hlist ev
    obtain ⟨T, B, m', fvs', rfl, rfl, hop'⟩ := OpOpen.openPisAtFvars_succ_inv hop
    rw [List.range_succ_eq_map, List.map_cons, List.map_map] at hfvs
    injection hfvs with hhd hrest
    injection hhd with _ hT
    have hT' : Γ d = T := hT.symm
    have hfvs' : fvs' = (List.range n).map (fun j => .fvar (d + 1 + j) (Γ (d + 1 + j))) := by
      rw [hrest]
      apply List.map_congr_left
      intro j _
      have e' : d + (j + 1) = d + 1 + j := by omega
      simp only [Function.comp_apply, Nat.succ_eq_add_one, e']
    cases sp with
    | succ ld rest =>
      match Obs.«KernelRoles::open_foralls».obs ev with
      | .Forall (x_t := xt) (m52 := m52) (ld12 := l2) (hm60 := hm) (ev41 := er) .. =>
        have hcell := l2.symm.trans ld
        injection hcell with hcell
        injection hcell with _ _ hxs
        injection hxs with ht hxs
        injection hxs with hb
        subst ht hb
        have ext : Heap.Extends h m52 := by rw [hm]; exact Heap.Extends.snoc _ _
        obtain ⟨T₀, B₀, ℓ, hEq, htT, hbB, -⟩ := hE.forallE_of_load ld
        injection hEq with e1 e2 e3
        subst e1 e2
        have rt : Tm κ d Γ (h ++ [.construct kexprListEnum "Cons" [xt, acc]]) 0 (Γ d) xt := by
          rw [hT']; exact htT.mono (Heap.Extends.snoc _ _)
        have hacc' : TypesRep κ Γ m52 (d + 1) (.ptr (.enum kexprListEnum) h.length) := by
          rw [hm]
          exact .cons (by simp) rt (hacc.mono (Heap.Extends.snoc _ _))
        have hlist' : RepList kexprListEnum (fun _ (_ : Unit) _ => True) m52
            (List.replicate (m + 1) ()) (.ptr (.enum kexprListEnum) h.length) := by
          rw [hm]
          have hc : (h ++ [Value.construct kexprListEnum "Cons" [xt, acc]])[h.length]? =
              some (.construct kexprListEnum "Cons" [xt, acc]) := by simp
          have hmono : HeapMono₂ (fun (_ : Heap F) (_ : Unit) (_ : SourceValue F) => True) := by
            unfold HeapMono₂
            intros
            trivial
          exact .cons hc trivial (repList_heapMono₂ _ hmono (Heap.Extends.snoc _ _) hlist)
        have hbody := (hbB.open (d := d) (Γ' := Γ) hT' (fun _ _ => rfl) 0 rfl).mono ext
        obtain ⟨bodyp, typesp, hr, hb, ht, hl, hx⟩ :=
          ih hop' hfvs' hnf (rest.mono ext) hbody hacc' hlist' er
        have e' : d + 1 + n = d + (n + 1) := by omega
        have e'' : m + 1 + n = m + (n + 1) := by omega
        rw [e'] at hb ht
        rw [e''] at hl
        exact ⟨bodyp, typesp, hr, hb, ht, hl, ext.trans hx⟩
      | .other (ld12 := l2) (hne81 := n4) .. =>
        have hcell := l2.symm.trans ld
        injection hcell with hcell
        exact (n4 _ rfl hcell).elim

/-! ## The statement -/

/-- **`op_certificate(tbl, r, k)` in full**: a pointer that represents, exactly under the table's
keying, a term equal to the closed statement up to binder data, along a spine of `Forall`
cells, and that reaches no `Let` and no `Proj` cell. -/
theorem opCertificate_full {t : Ix.Kernel.RoleTable} {r : Role} {k : Nat}
    {st : List KExpr × KExpr}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames)
    (hget : (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey))[k]? = some st)
    (htwf : t.wf = true) {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoleSpec::op_certificate"
      [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h res h' cs) :
    Heap.Extends h h' ∧ ∃ T, Decl.TmCExact (keyOf t) h' T res ∧
      T.erasePw = (certRaw st).erasePw ∧ OpOpen.ForallSpine h' (2 + st.1.length) res ∧
      LetProjFree h' res := by
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
  obtain ⟨x1, ⟨T, hT, her⟩, hsp, hplain⟩ := keyed_renders htwf hk.1 hk.2 htbl d0
  exact ⟨x1, T, hT, her, hsp, hplain⟩

set_option maxHeartbeats 1600000 in
/-- **The `k`-th certificate statement, as `validate_op_equations` opens it**: at the keying of
the closure's environment `env`, the context list of the statement's `2 + n` variables (`x`, `y`
of type `Nat`, then the hypotheses, the operation not among the constants they name) under a
scoped ghost context, and the statement's equation with the operation replaced by `val`. Its
length is `2 + n`. The premises: the table, the operation's address `b` (keyed as the
operation), the value `x_val` (its cells stored in `env`), and the constants the statement names
stored in `env` (all but the operation). -/
theorem certStmt_open {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames)
    {k : Nat} {st : List KExpr × KExpr}
    (hget : (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey))[k]? = some st)
    {Ec : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Nat} {val : KExpr}
    {x_tbl x_a x_val : SourceValue F} {b : Bytes.Address} {h₀ : Heap F}
    (htbl : TableRep t h₀ x_tbl) (hb : Bytes.RepAddressRef addrTy h₀ b x_a)
    (hkb : keyOf t (ixAddr b) = .role r) (hv : TmC (keyOf t) h₀ val x_val)
    (hvcells : ∀ h₂, Heap.Extends h₀ h₂ → ∀ x, AddrIn h₂ x_val x →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    (hnamed : ∀ x : Bytes.Address, certNamedOk r (keyOf t (ixAddr x)) = true → x ≠ b →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    {v1044 v1030 x_eqn x_types v1123 : SourceValue F}
    {h m1048 m1033 m1098 m1017 m1124 : Heap F} {cs1 cs2 cs3 cs4 : List (Call F)}
    (ext0 : Heap.Extends h₀ h)
    (ev1058 : ObsFn W "KernelRoleSpec::op_certificate"
      [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h v1044 m1048 cs1)
    (ev1043 : ObsFn W "KernelSubst::subst_const" [v1044, x_a, x_val] m1048 v1030 m1033 cs2)
    (hm1106 : m1098 = m1033 ++
      [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
    (ev1029 : ObsFn W "KernelRoles::open_foralls"
      [v1030, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m1033.length]
      m1098 (.tuple [x_eqn, x_types]) m1017 cs3)
    (ev1136 : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [x_types] m1017 v1123
      m1124 cs4) :
    Heap.Extends h m1124 ∧ v1123 = .field ((2 + st.1.length : Nat) : F) ∧
    ∃ Γ : Nat → KExpr,
      TypesRep (Ctx.stored ⟨Ec, env, t, some lim⟩).κ Γ m1124 (2 + st.1.length) x_types ∧
      GhostScoped Γ (2 + st.1.length) ∧
      Tm (Ctx.stored ⟨Ec, env, t, some lim⟩).κ (2 + st.1.length) Γ m1124 0
        (Expr.substConst0 (.role r) val st.2) x_eqn ∧
      Γ 0 = OpOpen.natTy ∧ Γ 1 = OpOpen.natTy ∧
      (∀ i (hi : i < (st.1.map (Expr.substConst0 (.role r) val)).length),
        Γ (2 + i) = (st.1.map (Expr.substConst0 (.role r) val))[i]) ∧
      ((st.1.map (Expr.substConst0 (.role r) val)).length = 1 ∨
        (st.1.map (Expr.substConst0 (.role r) val)).length = 2) := by
  have hst : st ∈ Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey) :=
    List.mem_of_getElem? hget
  obtain ⟨hsr, hop, hnm, hctx, hbf2, hbf1, hlen, happ⟩ := certOk_spec hmem hst
  let cx : Ctx := ⟨Ec, env, t, some lim⟩
  have hinj : ∀ b', keyOf t (ixAddr b') = keyOf t (ixAddr b) → b' = b :=
    fun b' hk => Decl.ixAddr_injective (Decl.keyOf_injective htwf hk)
  -- the rendered statement
  obtain ⟨ext1, T, hT, her, hsp, hpl⟩ := opCertificate_full hmem hget htwf (htbl.mono ext0) ev1058
  have hEq := eqUpTo_of_erasePw (2 + st.1.length) (certRaw st) T hsr her
  have hTn : T.constsResolveBy (certNamedOk r) = true := by
    rw [constsResolveBy_eqUpTo _ hEq]; exact hnm
  have ext2 := ev1043.heap_extends
  have hb1 := Bytes.repAddressRef_heapMono₂ addrTy (ext0.trans ext1) hb
  have hv1 := hv.mono (ext0.trans ext1)
  -- the replacement, at the table's keying
  have hS : TmC (keyOf t) m1033 (Expr.substConstAll (.role r) val T) v1030 := by
    intro d Γ'
    have := (OpOpen.subst_const_spec hinj hb1 hv1 ((hT d Γ').toTm) ev1043).1
    rwa [hkb] at this
  have stored : ∀ x, AddrIn m1033 v1030 x → ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci := by
    intro x hin
    rcases subst_const_cells (keyOf t) 0 (fun _ => .sort .zero) x_a x_val b val hinj _ _ _ _ _ _
        ev1043 rfl v1044 0 T rfl ((hT 0 _).toTm) hb1 hv1 m1033 (Heap.Extends.refl _) x hin with
      h1 | ⟨h1, hne⟩ | h1
    · exact hvcells m1033 (ext0.trans (ext1.trans ext2)) x h1
    · exact hnamed x (LetProjFree.addrIn_named (((hT 0 (fun _ => .sort .zero)).toTm).mono ext2)
        (hpl.mono ext2) x h1 _ hTn) hne
    · exact (LetProjFree.not_projIn h1 (hpl.mono ext2)).elim
  -- at the closure's keying
  have hSs : TmC cx.stored.κ m1033 (Expr.substConstAll (.role r) val T) v1030 :=
    hS.rekey
      (fun x hin => by
        obtain ⟨ci, hci⟩ := stored x hin
        exact Ctx.stored_key_of_find (c := cx) hci)
      (fun x hp _ => by
        obtain ⟨ci, hci⟩ := stored x hp.addrIn
        exact Ctx.stored_projPermitted_of_find (c := cx) hci)
  -- opening
  have hvc : val.looseBVarsBounded 0 = true := Tm.looseBVarsBounded (hv 0 (fun _ => .sort .zero))
  have hfvs0 : ∀ i T', Expr.fvar i T' ∈
      (List.range (2 + st.1.length)).map (fun j => Expr.fvar j (ctxOf st j)) →
      Expr.substConstAll (.role r) val T' = T' := by
    intro i T' hm
    obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp hm
    injection hjeq with e1 e2
    subst e2
    exact substConstAll_of_not_named _ (hctx j (List.mem_range.mp hj)).1
  have hopS := openPisAtFvars_substConstAll hvc (2 + st.1.length)
    ((openPisAtFvars_eqUpTo _ hEq 0).trans hop) hfvs0
  have ext3 : Heap.Extends m1033 m1098 := by rw [hm1106]; exact Heap.Extends.snoc _ _
  have hacc : TypesRep cx.stored.κ (ctxOf st) m1098 0
      (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m1033.length) := by
    rw [hm1106]; exact Decl.typesRep_alloc_nil cx.stored.κ (ctxOf st) m1033
  have hlist0 : RepList kexprListEnum (fun _ (_ : Unit) _ => True) m1098 (List.replicate 0 ())
      (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m1033.length) := by
    rw [hm1106]
    have hc : (m1033 ++ [Value.construct kexprListEnum "Nil" []])[m1033.length]? =
        some (.construct kexprListEnum "Nil" []) := by simp
    exact .nil hc
  have hnf : ∀ T₁ B₁ m₁, Expr.substConstAll (.role r) val st.2 ≠ .forallE T₁ B₁ m₁ := by
    intro T₁ B₁ m₁ he
    obtain ⟨f, a, hs2⟩ : ∃ f a, st.2 = .app f a := by
      cases hs : st.2 <;> simp [isApp, hs] at happ ⊢
    rw [hs2] at he
    simp [Expr.substConstAll] at he
  obtain ⟨bodyp, typesp, htup, hbody, htypes, hlist, ext4⟩ :=
    open_foralls_full (κ := cx.stored.κ) (Γ := ctxOf st) (2 + st.1.length) (d := 0) (m := 0)
      hopS (by simp) hnf ((OpOpen.subst_const_forallSpine _ hsp ev1043).mono ext3)
      ((hSs 0 (ctxOf st)).mono ext3) hacc hlist0 ev1029
  have htup' : [x_eqn, x_types] = [bodyp, typesp] := Value.tuple.inj htup
  simp only [List.cons.injEq, and_true] at htup'
  obtain ⟨rfl, rfl⟩ := htup'
  -- the length
  have ev' : ObsFn W (Instance.mk "Lists::length" [.ptr (.named "KernelTypes::KExprNode" [])]).symbol
      [x_types] m1017 v1123 m1124 cs4 := by
    rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev1136
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]).symbol
      (fun _ (_ : Unit) _ => True) m1017 (List.replicate (0 + (2 + st.1.length)) ()) x_types := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hlist
  obtain ⟨hv1123, hm1124⟩ := Lib.Lists.length_spec ev' hl'
  simp only [List.length_replicate, Nat.zero_add] at hv1123
  subst hm1124
  rw [Nat.zero_add] at hbody htypes
  refine ⟨ext1.trans (ext2.trans (ext3.trans ext4)), hv1123, ctxOf st, htypes,
    fun j hj => wscopedB_of_fvScoped _ _ (hctx j hj).2, ?_, by simp [ctxOf], by simp [ctxOf],
    ?_, by simpa using hlen⟩
  · rw [OpOpen.substConstAll_eq_substConst0 _ _ st.2 hbf2] at hbody
    exact hbody
  · intro i hi
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    have hb1' := hbf1 _ (List.getElem_mem hi)
    rw [← OpOpen.substConstAll_eq_substConst0 _ _ _ hb1']
    have hc := (hctx (2 + i) (by omega)).1
    have e : ctxOf st (2 + i) = st.1[i] := by
      unfold ctxOf
      rw [ite_eq_right (show ¬ (2 + i < 2) by omega), show 2 + i - 2 = i by omega,
        List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]
      rfl
    rw [e] at hc ⊢
    exact (substConstAll_of_not_named _ hc).symm

end IxVM.Refinement.Binding
