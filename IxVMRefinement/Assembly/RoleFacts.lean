import IxVMRefinement.Core.Ctx
import Ix.IxVM.Refinement.Claim
import Ix.IxVM.Consistency.Statement
import IxC.Kernel.Verify.Rules.Bridge
import IxC.Kernel.Verify.Abstract
import IxC.Kernel.Rules.Inversion
import IxC.Kernel.Rules.Transport
import IxC.Kernel.Model.StoreCompanions

/-! # Pure kernel role-fact bridges (`TableAdmitted` → `Core.EnvFacts` role fields)

Connects `IxVM.Refinement.TableAdmitted` (`admitBinding`, `LiteralSupportBound`,
`AcceptsIn`, and `BindingSpecs`) and prefix/stored declaration environments to the
role-table-dependent fields of `IxVM.Refinement.Core.EnvFacts`:

* `tableWf_of_admitBinding` and `TableAdmitted.unpack`: extracts `t.wf = true`,
  `LiteralSupportBound t`, `AcceptsRef`, `TheoremsInProp`, `AnchorsTyped`, and
  `eqnsCheck` witnesses from `TableAdmitted V b`;
* `valStored_matchesPin` and `storedAs_matchesPin`: transfers `ConstantVal.matchesPin`
  across `ValStored` / `StoredAs` on `let`-free pins;
* `natLit`, `strLit`, `natOps`, `natAdd`, `eqStored`, and `quotBasis` bridges, both
  from stored/pinned declarations (`AnchorsTyped`, `BasisKind`, `Infer`) and across
  `ThmSim` (`thmToOpaqueDefn` ↔ `ThmTyped`);
* `ThmSim` (`ThmSim.red`, `ThmSim.defEq`, `ThmSim.infer`, `ThmSim.certs`,
  `ThmSim.defEqList`, `ThmSim.etaProjCerts`): full mutual `Ix.Kernel.Rules` transfer
  from an `AcceptsRef` environment where theorems are installed via `thmToOpaqueDefn`
  to a runtime environment storing `.thmInfo` under `Ix.Kernel.Model.ThmTyped`;
* `annotateCore_to_annot`, `eqnsCheck_proof_inv`, `eqnsCheck_proof_thmSim`, and
  `evidence_of_thmSim`: unpacks `Ix.Kernel.eqnsCheck` on proof evidence and transfers
  `DefEq` to `c.env`. -/

namespace IxVM.Refinement.Assembly

open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Section 1: Role-table admission and `TableAdmitted` unpacking -/

/-- `Ix.Kernel.Admission.admitBinding` succeeds only on a well-formed `RoleTable`
(`t.wf = true`). -/
theorem tableWf_of_admitBinding {hash : ByteArray → _root_.Address}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (h : Ix.Kernel.Admission.admitBinding hash b = .ok t) :
    t.wf = true := by
  unfold Ix.Kernel.Admission.admitBinding at h
  by_cases hh : hash b.bytes = b.address
  · simp only [hh, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      pure, Except.pure, Bind.bind, Except.bind, Functor.map, Except.map, Except.mapError] at h
    cases hob : Ix.Kernel.RoleTable.ofBytes b.bytes with
    | none =>
      rw [hob] at h
      cases h
    | some t₀ =>
      rw [hob] at h
      dsimp only at h
      cases hchk : t₀.check with
      | error msg =>
        rw [hchk] at h
        cases h
      | ok u =>
        rw [hchk] at h
        injection h with ht
        subst ht
        simp [Ix.Kernel.RoleTable.wf, hchk, Except.isOk, Except.toBool]
  · simp [hh, decide_false, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h

/-- Unpack `TableAdmitted V b` into `t.wf = true`, `LiteralSupportBound t`,
`AcceptsRef` on `ds_role.map thmToOpaqueDefn`, `TheoremsInProp`, `anchorMismatch? = none`,
`AnchorsTyped`, and per-role `eqnsCheck` witnesses. -/
theorem TableAdmitted.unpack {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    (h : IxVM.Refinement.TableAdmitted V b) :
    ∃ (t : Ix.Kernel.RoleTable)
      (evA : Ix.Kernel.Evidences .anon)
      (ds_role : List (Ix.Kernel.Declaration .anon))
      (envA : Ix.Kernel.Env .anon)
      (ev_eqns : Ix.Kernel.Evidences .anon),
      Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t ∧
      t.wf = true ∧
      IxVM.Refinement.LiteralSupportBound t ∧
      Ix.Kernel.Cached.AcceptsRef .verified evA
        (ds_role.map IxVM.Refinement.thmToOpaqueDefn) envA ∧
      IxVM.Refinement.TheoremsInProp envA ds_role ∧
      (∀ d ∈ ds_role, d.anchorMismatch? = none) ∧
      IxVM.Refinement.AnchorsTyped ds_role ∧
      (∀ r, t.addressOf? r ≠ none → (r.spec (md := .anon)).kind = .eqns →
        ∃ F, Ix.Kernel.eqnsCheck (Ix.Kernel.fueledOps .verified F) envA r ev_eqns = .ok ()) := by
  obtain ⟨t, hadm, hlit, hacc⟩ := h
  obtain ⟨evA, ds_role, envA, href, hthms, hmism, hanch, ev_eqns, heqns⟩ := hacc.acceptsRef
  exact ⟨t, evA, ds_role, envA, ev_eqns, hadm, tableWf_of_admitBinding hadm, hlit,
    href, hthms, hmism, hanch, heqns⟩

/-- Under `LiteralSupportBound c.t`, `c.inForce .string` implies `c.binds r` for every
`r ∈ strLitSupportRoles`. -/
theorem binds_strLitSupportRoles_of_inForce {c : Ctx}
    (hlit : IxVM.Refinement.LiteralSupportBound c.t)
    (hs : c.inForce .string) :
    ∀ r ∈ IxVM.Refinement.strLitSupportRoles, c.binds r :=
  fun r hr => hlit hs.1 r hr

/-- When `c.lim = none`, `c.binds r` and `c.inForce r` coincide. -/
theorem inForce_of_binds_lim_none {c : Ctx} (hlim : c.lim = none) {r : Ix.Kernel.Role}
    (hb : c.binds r) : c.inForce r :=
  ⟨hb, fun _ hn => by rw [hlim] at hn; cases hn⟩

/-! ## Section 2: `exprNoLet`, `erasePw`, and `matchesPin` across `ValStored` / `StoredAs` -/

/-- Structural `let`-freeness predicate descending into all subterms (including `.fvar` types). -/
def exprNoLet : Ix.Kernel.Expr .anon → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => exprNoLet ty
  | .app f a => exprNoLet f && exprNoLet a
  | .lam ty b _ | .forallE ty b _ => exprNoLet ty && exprNoLet b
  | .letE _ _ _ _ => false
  | .proj _ _ e => exprNoLet e

private theorem binderMeta_eq_of_pw_eq {m₁ m₂ : Ix.Kernel.BinderMeta}
    (h : m₁.pw = m₂.pw) : m₁ = m₂ := by
  cases m₁ with
  | mk pw₁ d₁ =>
    cases m₂ with
    | mk pw₂ d₂ =>
      dsimp only at h
      subst h
      congr 1
      exact Subsingleton.elim d₁ d₂

/-- On a `let`-free right-hand term `e₀`, `Annotates e e₀` preserves `Expr.erasePw`. -/
theorem annotates_erasePw_of_noLet {e e₀ : Ix.Kernel.Expr .anon}
    (ha : IxVM.Consistency.Annotates e e₀) (hnl : exprNoLet e₀ = true) :
    e.erasePw = e₀.erasePw := by
  induction ha with
  | bvar | sort | const | lit => rfl
  | fvar _ ih =>
    simp only [exprNoLet] at hnl
    simp [Ix.Kernel.Expr.erasePw, ih hnl]
  | app _ _ ihf iha =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp [Ix.Kernel.Expr.erasePw, ihf hnl.1, iha hnl.2]
  | lam _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp only [Ix.Kernel.Expr.erasePw, iht hnl.1, ihb hnl.2]
    congr 1
    exact binderMeta_eq_of_pw_eq rfl
  | forallE _ _ iht ihb =>
    simp only [exprNoLet, Bool.and_eq_true] at hnl
    simp only [Ix.Kernel.Expr.erasePw, iht hnl.1, ihb hnl.2]
    congr 1
    exact binderMeta_eq_of_pw_eq rfl
  | proj _ ihe =>
    simp only [exprNoLet] at hnl
    simp [Ix.Kernel.Expr.erasePw, ihe hnl]
  | letE _ _ =>
    simp [exprNoLet] at hnl

/-- `Expr.erasePw` preserves `exprNoLet`. -/
theorem exprNoLet_erasePw : ∀ e : Ix.Kernel.Expr .anon, exprNoLet e.erasePw = exprNoLet e
  | .bvar _ | .sort _ | .const _ _ | .lit _ | .letE _ _ _ _ => rfl
  | .fvar _ ty => exprNoLet_erasePw ty
  | .app f a => by simp [Ix.Kernel.Expr.erasePw, exprNoLet, exprNoLet_erasePw f, exprNoLet_erasePw a]
  | .lam ty b _ => by simp [Ix.Kernel.Expr.erasePw, exprNoLet, exprNoLet_erasePw ty, exprNoLet_erasePw b]
  | .forallE ty b _ => by
    simp [Ix.Kernel.Expr.erasePw, exprNoLet, exprNoLet_erasePw ty, exprNoLet_erasePw b]
  | .proj _ _ e => exprNoLet_erasePw e

theorem exprNoLet_of_erasePw_eq {e₀ p : Ix.Kernel.Expr .anon}
    (heq : e₀.erasePw = p.erasePw) (hp : exprNoLet p = true) :
    exprNoLet e₀ = true := by
  rw [← exprNoLet_erasePw e₀, heq, exprNoLet_erasePw p]
  exact hp

/-- `ValStored cv cv₀` preserves `ConstantVal.matchesPin pin` whenever `exprNoLet pin.type = true`. -/
theorem valStored_matchesPin {cv cv₀ pin : Ix.Kernel.ConstantVal .anon}
    (hst : IxVM.Consistency.ValStored cv cv₀)
    (hpin : cv₀.matchesPin pin = true)
    (hnl : exprNoLet pin.type = true) :
    cv.matchesPin pin = true := by
  obtain ⟨hn, hlp, hann⟩ := hst
  unfold Ix.Kernel.ConstantVal.matchesPin at hpin ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpin ⊢
  obtain ⟨⟨hn₀, hlp₀⟩, her₀⟩ := hpin
  have hnl₀ : exprNoLet cv₀.type = true := exprNoLet_of_erasePw_eq her₀ hnl
  exact ⟨⟨hn.trans hn₀, hlp.trans hlp₀⟩, (annotates_erasePw_of_noLet hann hnl₀).trans her₀⟩

/-- `StoredAs ci ci₀` preserves `ConstantVal.matchesPin pin` whenever `exprNoLet pin.type = true`. -/
theorem storedAs_matchesPin {ci ci₀ : Ix.Kernel.ConstantInfo .anon}
    {pin : Ix.Kernel.ConstantVal .anon}
    (hst : IxVM.Consistency.StoredAs ci ci₀)
    (hpin : ci₀.toConstantVal.matchesPin pin = true)
    (hnl : exprNoLet pin.type = true) :
    ci.toConstantVal.matchesPin pin = true :=
  valStored_matchesPin hst.1 hpin hnl

/-! ## Section 3: `erasePw` inversions and role-type shape predicates -/

private theorem erasePw_eq_sort {e : Ix.Kernel.Expr .anon} {u : Ix.Kernel.Level}
    (h : e.erasePw = .sort u) : e = .sort u := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact congrArg Ix.Kernel.Expr.sort h

private theorem erasePw_eq_const {e : Ix.Kernel.Expr .anon} {n : KKey} {us : List KLevel}
    (h : e.erasePw = .const n us) : e = .const n us := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact congrArg₂ Ix.Kernel.Expr.const h.1 h.2

private theorem erasePw_eq_bvar {e : Ix.Kernel.Expr .anon} {i : Nat}
    (h : e.erasePw = .bvar i) : e = .bvar i := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact congrArg Ix.Kernel.Expr.bvar h

private theorem erasePw_eq_app {e d₀ a₀ : Ix.Kernel.Expr .anon}
    (h : e.erasePw = .app d₀ a₀) :
    ∃ f a, e = .app f a ∧ f.erasePw = d₀ ∧ a.erasePw = a₀ := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

private theorem erasePw_eq_forallE {e d₀ b₀ : Ix.Kernel.Expr .anon} {m₀ : Ix.Kernel.BinderMeta}
    (h : e.erasePw = .forallE d₀ b₀ m₀) :
    ∃ d b mb, e = .forallE d b mb ∧ d.erasePw = d₀ ∧ b.erasePw = b₀ := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact ⟨_, _, _, rfl, h.1, h.2.1⟩

/-- `natIndOk` holds of any stored `.indInfo` matching the `Nat` pin. -/
theorem natIndOk_of_matchesPin {cv : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (h : cv.matchesPin ⟨Ix.Kernel.natName, [], .sort (.succ .zero)⟩ = true) :
    Ix.Kernel.natIndOk (some (.indInfo cv caps)) = true := by
  unfold Ix.Kernel.ConstantVal.matchesPin at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨_, hlp⟩, hty⟩ := h
  have hty' := erasePw_eq_sort hty
  simp [Ix.Kernel.natIndOk, hlp, hty']

/-- `natZeroOk` holds of any stored `.ctorInfo` matching the `Nat.zero` pin. -/
theorem natZeroOk_of_matchesPin {cv : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
    (h : cv.matchesPin ⟨Ix.Kernel.natZeroName, [], .const Ix.Kernel.natName []⟩ = true) :
    Ix.Kernel.natZeroOk (some (.ctorInfo cv nP nF)) = true := by
  unfold Ix.Kernel.ConstantVal.matchesPin at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨_, hlp⟩, hty⟩ := h
  have hty' := erasePw_eq_const hty
  simp [Ix.Kernel.natZeroOk, hlp, hty']

/-- `natSuccOk` holds of any stored `.ctorInfo` matching the `Nat.succ` pin. -/
theorem natSuccOk_of_matchesPin {cv : Ix.Kernel.ConstantVal .anon} {nP nF : Nat}
    (h : cv.matchesPin
      ⟨Ix.Kernel.natSuccName, [],
        .forallE (.const Ix.Kernel.natName []) (.const Ix.Kernel.natName []) default⟩ = true) :
    Ix.Kernel.natSuccOk (some (.ctorInfo cv nP nF)) = true := by
  unfold Ix.Kernel.ConstantVal.matchesPin at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨_, hlp⟩, hty⟩ := h
  obtain ⟨d, b, mb, heq, hd, hb⟩ := erasePw_eq_forallE hty
  rw [erasePw_eq_const hd, erasePw_eq_const hb] at heq
  simp [Ix.Kernel.natSuccOk, hlp, heq]

/-- `natLitSupported` holds whenever `BasisKind.declsA .natK` (or `StoredAs` copies of its
`Nat`, `Nat.zero`, `Nat.succ` entries) are stored in `env`. -/
theorem natLitSupported_of_storedBasisNat {env : Ix.Kernel.Env .anon}
    (h : ∀ ci₀ ∈ Ix.Kernel.BasisKind.declsA (md := .anon) .natK,
      ci₀.name ∈ [Ix.Kernel.natName, Ix.Kernel.natZeroName, Ix.Kernel.natSuccName] →
      ∃ ci, env.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    Ix.Kernel.natLitSupported env = true := by
  have h0 : (Ix.Kernel.natA : Ix.Kernel.ConstantInfo .anon) ∈
      Ix.Kernel.BasisKind.declsA (md := .anon) .natK := by
    simp [Ix.Kernel.BasisKind.declsA]
  have h1 : (Ix.Kernel.natZeroA : Ix.Kernel.ConstantInfo .anon) ∈
      Ix.Kernel.BasisKind.declsA (md := .anon) .natK := by
    simp [Ix.Kernel.BasisKind.declsA]
  have h2 : (Ix.Kernel.natSuccA : Ix.Kernel.ConstantInfo .anon) ∈
      Ix.Kernel.BasisKind.declsA (md := .anon) .natK := by
    simp [Ix.Kernel.BasisKind.declsA]
  obtain ⟨ciN, hfN, hstN⟩ := h _ h0 (by decide)
  obtain ⟨ciZ, hfZ, hstZ⟩ := h _ h1 (by decide)
  obtain ⟨ciS, hfS, hstS⟩ := h _ h2 (by decide)
  have hpN : ciN.toConstantVal.matchesPin
      ⟨Ix.Kernel.natName, [], .sort (.succ .zero)⟩ = true :=
    storedAs_matchesPin hstN rfl rfl
  have hpZ : ciZ.toConstantVal.matchesPin
      ⟨Ix.Kernel.natZeroName, [], .const Ix.Kernel.natName []⟩ = true :=
    storedAs_matchesPin hstZ rfl rfl
  have hpS : ciS.toConstantVal.matchesPin
      ⟨Ix.Kernel.natSuccName, [],
        .forallE (.const Ix.Kernel.natName []) (.const Ix.Kernel.natName []) default⟩ = true :=
    storedAs_matchesPin hstS rfl rfl
  cases ciN with
  | indInfo cvN capsN =>
    cases ciZ with
    | ctorInfo cvZ nPZ nFZ =>
      cases ciS with
      | ctorInfo cvS nPS nFS =>
        dsimp only [Ix.Kernel.ConstantInfo.toConstantVal] at hpN hpZ hpS
        unfold Ix.Kernel.natLitSupported
        change (Ix.Kernel.natIndOk (env.find? Ix.Kernel.natName) &&
          Ix.Kernel.natZeroOk (env.find? Ix.Kernel.natZeroName) &&
          Ix.Kernel.natSuccOk (env.find? Ix.Kernel.natSuccName)) = true
        change env.find? Ix.Kernel.natName = some (.indInfo cvN capsN) at hfN
        change env.find? Ix.Kernel.natZeroName = some (.ctorInfo cvZ nPZ nFZ) at hfZ
        change env.find? Ix.Kernel.natSuccName = some (.ctorInfo cvS nPS nFS) at hfS
        rw [hfN, hfZ, hfS,
          natIndOk_of_matchesPin (caps := capsN) hpN,
          natZeroOk_of_matchesPin (nP := nPZ) (nF := nFZ) hpZ,
          natSuccOk_of_matchesPin (nP := nPS) (nF := nFS) hpS]
        rfl
      | _ => exact hstS.2.elim
    | _ => exact hstZ.2.elim
  | _ => exact hstN.2.elim

/-- `EnvFacts.natLit` from `StoredAs` installation of `.nat`, `.natZero`, `.natSucc` when in force. -/
theorem natLit_of_inForce_stored {c : Ctx}
    (h : c.inForce .nat → c.inForce .natZero → c.inForce .natSucc →
      ∀ ci₀ ∈ Ix.Kernel.BasisKind.declsA (md := .anon) .natK,
        ci₀.name ∈ [Ix.Kernel.natName, Ix.Kernel.natZeroName, Ix.Kernel.natSuccName] →
        ∃ ci, c.env.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    c.inForce .nat → c.inForce .natZero → c.inForce .natSucc →
      Ix.Kernel.natLitSupported c.env = true :=
  fun hn hz hs => natLitSupported_of_storedBasisNat (h hn hz hs)

/-! ### String-literal support role pins -/

/-- The seven non-`Nat` string-literal support roles (`String`, `String.ofList`, `List`,
`List.nil`, `List.cons`, `Char`, `Char.ofNat`). -/
def strAnchorRoles : List Ix.Kernel.Role :=
  [.string, .stringOfList, .list, .listNil, .listCons, .char, .charOfNat]

private theorem not_strAnchor_of_mem_basisDeclsA (kind : Ix.Kernel.BasisKind)
    {ci₀ : Ix.Kernel.ConstantInfo .anon} {r : Ix.Kernel.Role}
    (hm : ci₀ ∈ kind.declsA) (hr : r ∈ strAnchorRoles) (hn : ci₀.name = .role r) : False := by
  have hrole : ∀ k : Ix.Kernel.BasisKind,
      ∀ x ∈ k.declsA (md := .anon), ∀ ro ∈ strAnchorRoles, x.name ≠ .role ro := by
    intro k
    cases k <;> decide
  exact hrole kind ci₀ hm r hr hn

/-- Any `ci₀ ∈ installs d` whose name is one of the 7 `strAnchorRoles` appears in `declaredVals d`
(since none of the 6 `BasisKind`s declares any of those 7 roles). -/
theorem declaredVals_of_installs_strAnchor {d : Ix.Kernel.Declaration .anon}
    {ci₀ : Ix.Kernel.ConstantInfo .anon} {r : Ix.Kernel.Role}
    (hi : ci₀ ∈ IxVM.Consistency.installs d)
    (hr : r ∈ strAnchorRoles)
    (hn : ci₀.name = .role r) :
    ci₀.toConstantVal ∈ IxVM.Refinement.declaredVals d := by
  cases d with
  | axiomDecl cv =>
    simp only [IxVM.Consistency.installs] at hi
    split at hi
    · cases hi
    · simp only [List.mem_singleton] at hi
      subst hi
      simp [IxVM.Refinement.declaredVals, Ix.Kernel.ConstantInfo.toConstantVal]
  | defnDecl cv v h =>
    simp only [IxVM.Consistency.installs, List.mem_singleton] at hi
    subst hi
    simp [IxVM.Refinement.declaredVals, Ix.Kernel.ConstantInfo.toConstantVal]
  | thmDecl cv v =>
    simp only [IxVM.Consistency.installs, List.mem_singleton] at hi
    subst hi
    simp [IxVM.Refinement.declaredVals, Ix.Kernel.ConstantInfo.toConstantVal]
  | opaqueDecl cv v =>
    simp only [IxVM.Consistency.installs, List.mem_singleton] at hi
    subst hi
    simp [IxVM.Refinement.declaredVals, Ix.Kernel.ConstantInfo.toConstantVal]
  | basisDecl kind =>
    exact (not_strAnchor_of_mem_basisDeclsA kind hi hr hn).elim
  | indDecl block nP =>
    simp only [IxVM.Consistency.installs] at hi
    split at hi
    · rename_i kind _
      exact (not_strAnchor_of_mem_basisDeclsA kind hi hr hn).elim
    · simp only [IxVM.Refinement.declaredVals]
      exact List.mem_map_of_mem hi
  | quotDecl k cv =>
    simp only [IxVM.Consistency.installs] at hi
    split at hi
    · exact (not_strAnchor_of_mem_basisDeclsA .quotK hi hr hn).elim
    · cases hi

theorem stringTyOk_of_matchesPin {ci : Ix.Kernel.ConstantInfo .anon} {pin : Ix.Kernel.ConstantVal .anon}
    (hp : IxVM.Refinement.anchorPin? (.role .string) = some pin)
    (hm : ci.toConstantVal.matchesPin pin = true) :
    Ix.Kernel.stringTyOk (some ci) = true := by
  injection hp with hp'
  subst hp'
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  obtain ⟨⟨_, hlp⟩, hty⟩ := hm
  have hty' := erasePw_eq_sort hty
  simp [Ix.Kernel.stringTyOk, hlp, hty']

theorem charTyOk_of_matchesPin {ci : Ix.Kernel.ConstantInfo .anon} {pin : Ix.Kernel.ConstantVal .anon}
    (hp : IxVM.Refinement.anchorPin? (.role .char) = some pin)
    (hm : ci.toConstantVal.matchesPin pin = true) :
    Ix.Kernel.charTyOk (some ci) = true := by
  injection hp with hp'
  subst hp'
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  obtain ⟨⟨_, hlp⟩, hty⟩ := hm
  have hty' := erasePw_eq_sort hty
  simp [Ix.Kernel.charTyOk, hlp, hty']

theorem listTyOk_of_matchesPin {ci : Ix.Kernel.ConstantInfo .anon} {pin : Ix.Kernel.ConstantVal .anon}
    (hp : IxVM.Refinement.anchorPin? (.role .list) = some pin)
    (hm : ci.toConstantVal.matchesPin pin = true) :
    Ix.Kernel.listTyOk (some ci) = true := by
  injection hp with hp'
  subst hp'
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  obtain ⟨⟨_, hlp⟩, hty⟩ := hm
  obtain ⟨d, b, mb, heq, hd, hb⟩ := erasePw_eq_forallE hty
  rw [erasePw_eq_sort hd, erasePw_eq_sort hb] at heq
  have hlp' : ci.toConstantVal.levelParams = [0] := hlp
  simp [Ix.Kernel.listTyOk, Ix.Kernel.BasisDSL.u, Ix.Kernel.BasisDSL.uN, hlp', heq]

theorem listNilTyOk_of_matchesPin {ci : Ix.Kernel.ConstantInfo .anon} {pin : Ix.Kernel.ConstantVal .anon}
    (hp : IxVM.Refinement.anchorPin? (.role .listNil) = some pin)
    (hm : ci.toConstantVal.matchesPin pin = true) :
    Ix.Kernel.listNilTyOk (some ci) = true := by
  injection hp with hp'
  subst hp'
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  obtain ⟨⟨_, hlp⟩, hty⟩ := hm
  obtain ⟨d, b, mb, heq, hd, hb⟩ := erasePw_eq_forallE hty
  obtain ⟨bf, ba, hbeq, hbf, hba⟩ := erasePw_eq_app hb
  rw [erasePw_eq_const hbf, erasePw_eq_bvar hba] at hbeq
  rw [erasePw_eq_sort hd, hbeq] at heq
  have hlp' : ci.toConstantVal.levelParams = [0] := hlp
  simp [Ix.Kernel.listNilTyOk, Ix.Kernel.BasisDSL.u, Ix.Kernel.BasisDSL.uN, hlp', heq]

theorem listConsTyOk_of_matchesPin {ci : Ix.Kernel.ConstantInfo .anon} {pin : Ix.Kernel.ConstantVal .anon}
    (hp : IxVM.Refinement.anchorPin? (.role .listCons) = some pin)
    (hm : ci.toConstantVal.matchesPin pin = true) :
    Ix.Kernel.listConsTyOk (some ci) = true := by
  injection hp with hp'
  subst hp'
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  obtain ⟨⟨_, hlp⟩, hty⟩ := hm
  obtain ⟨d1, b1, mb1, heq1, hd1, hb1⟩ := erasePw_eq_forallE hty
  obtain ⟨d2, b2, mb2, heq2, hd2, hb2⟩ := erasePw_eq_forallE hb1
  obtain ⟨d3, b3, mb3, heq3, hd3, hb3⟩ := erasePw_eq_forallE hb2
  obtain ⟨df3, da3, hd3eq, hdf3, hda3⟩ := erasePw_eq_app hd3
  obtain ⟨bf3, ba3, hb3eq, hbf3, hba3⟩ := erasePw_eq_app hb3
  rw [erasePw_eq_const hdf3, erasePw_eq_bvar hda3] at hd3eq
  rw [erasePw_eq_const hbf3, erasePw_eq_bvar hba3] at hb3eq
  rw [hd3eq, hb3eq] at heq3
  rw [erasePw_eq_bvar hd2, heq3] at heq2
  rw [erasePw_eq_sort hd1, heq2] at heq1
  have hlp' : ci.toConstantVal.levelParams = [0] := hlp
  simp [Ix.Kernel.listConsTyOk, Ix.Kernel.BasisDSL.u, Ix.Kernel.BasisDSL.uN, hlp', heq1]

theorem charOfNatTyOk_of_matchesPin {ci : Ix.Kernel.ConstantInfo .anon} {pin : Ix.Kernel.ConstantVal .anon}
    (hp : IxVM.Refinement.anchorPin? (.role .charOfNat) = some pin)
    (hm : ci.toConstantVal.matchesPin pin = true) :
    Ix.Kernel.charOfNatTyOk (some ci) = true := by
  injection hp with hp'
  subst hp'
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  obtain ⟨⟨_, hlp⟩, hty⟩ := hm
  obtain ⟨d, b, mb, heq, hd, hb⟩ := erasePw_eq_forallE hty
  rw [erasePw_eq_const hd, erasePw_eq_const hb] at heq
  simp [Ix.Kernel.charOfNatTyOk, hlp, heq]

theorem stringOfListTyOk_of_matchesPin {ci : Ix.Kernel.ConstantInfo .anon}
    {pin : Ix.Kernel.ConstantVal .anon}
    (hp : IxVM.Refinement.anchorPin? (.role .stringOfList) = some pin)
    (hm : ci.toConstantVal.matchesPin pin = true) :
    Ix.Kernel.stringOfListTyOk (some ci) = true := by
  injection hp with hp'
  subst hp'
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  obtain ⟨⟨_, hlp⟩, hty⟩ := hm
  obtain ⟨d, b, mb, heq, hd, hb⟩ := erasePw_eq_forallE hty
  obtain ⟨df, da, hdeq, hdf, hda⟩ := erasePw_eq_app hd
  rw [erasePw_eq_const hdf, erasePw_eq_const hda] at hdeq
  rw [hdeq, erasePw_eq_const hb] at heq
  simp [Ix.Kernel.stringOfListTyOk, hlp, heq]

/-- `EnvFacts.strLit` from `LiteralSupportBound c.t`, `AnchorsTyped ds_role`, `natLitSupported`
when `.nat`, `.natZero`, `.natSucc` are bound, and `StoredAs` installation of every bound role in
`strAnchorRoles` from `ds_role`. -/
theorem strLit_of_anchorsTyped {c : Ctx}
    {ds_role : List (Ix.Kernel.Declaration .anon)}
    (hlit : IxVM.Refinement.LiteralSupportBound c.t)
    (hanch : IxVM.Refinement.AnchorsTyped ds_role)
    (hnat : c.binds .nat → c.binds .natZero → c.binds .natSucc →
      Ix.Kernel.natLitSupported c.env = true)
    (hstored : ∀ r ∈ strAnchorRoles, c.binds r →
      ∃ d ∈ ds_role, ∃ ci₀ ∈ IxVM.Consistency.installs d, ∃ ci,
        ci₀.name = .role r ∧ c.env.find? (.role r) = some ci ∧
        IxVM.Consistency.StoredAs ci ci₀) :
    c.inForce .string → Ix.Kernel.strLitSupported c.env = true := by
  intro hstr
  have hb := binds_strLitSupportRoles_of_inForce hlit hstr
  have hn : Ix.Kernel.natLitSupported c.env = true :=
    hnat (hb .nat (by simp [IxVM.Refinement.strLitSupportRoles]))
      (hb .natZero (by simp [IxVM.Refinement.strLitSupportRoles]))
      (hb .natSucc (by simp [IxVM.Refinement.strLitSupportRoles]))
  have hgetPin : ∀ r ∈ strAnchorRoles, ∀ pin,
      IxVM.Refinement.anchorPin? (.role r) = some pin →
      exprNoLet pin.type = true →
      ∃ ci, c.env.find? (.role r) = some ci ∧ ci.toConstantVal.matchesPin pin = true := by
    intro r hr pin hpin hnl
    have hbr : c.binds r := by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hb .string (by simp [IxVM.Refinement.strLitSupportRoles])
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hb .stringOfList (by simp [IxVM.Refinement.strLitSupportRoles])
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hb .list (by simp [IxVM.Refinement.strLitSupportRoles])
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hb .listNil (by simp [IxVM.Refinement.strLitSupportRoles])
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hb .listCons (by simp [IxVM.Refinement.strLitSupportRoles])
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hb .char (by simp [IxVM.Refinement.strLitSupportRoles])
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hb .charOfNat (by simp [IxVM.Refinement.strLitSupportRoles])
      · cases hr
    obtain ⟨d, hd, ci₀, hci₀, ci, hname, hf, hst⟩ := hstored r hr hbr
    have hdecl := declaredVals_of_installs_strAnchor hci₀ hr hname
    have hp₀ : ci₀.toConstantVal.matchesPin pin = true :=
      hanch d hd ci₀.toConstantVal hdecl pin (by rw [show ci₀.toConstantVal.name = .role r from hname]; exact hpin)
    exact ⟨ci, hf, storedAs_matchesPin hst hp₀ hnl⟩
  obtain ⟨ci1, hf1, hm1⟩ := hgetPin .string (by simp [strAnchorRoles]) _ rfl rfl
  obtain ⟨ci2, hf2, hm2⟩ := hgetPin .stringOfList (by simp [strAnchorRoles]) _ rfl rfl
  obtain ⟨ci3, hf3, hm3⟩ := hgetPin .list (by simp [strAnchorRoles]) _ rfl rfl
  obtain ⟨ci4, hf4, hm4⟩ := hgetPin .listNil (by simp [strAnchorRoles]) _ rfl rfl
  obtain ⟨ci5, hf5, hm5⟩ := hgetPin .listCons (by simp [strAnchorRoles]) _ rfl rfl
  obtain ⟨ci6, hf6, hm6⟩ := hgetPin .char (by simp [strAnchorRoles]) _ rfl rfl
  obtain ⟨ci7, hf7, hm7⟩ := hgetPin .charOfNat (by simp [strAnchorRoles]) _ rfl rfl
  unfold Ix.Kernel.strLitSupported
  change (Ix.Kernel.natLitSupported c.env &&
    Ix.Kernel.stringTyOk (c.env.find? (.role .string)) &&
    Ix.Kernel.stringOfListTyOk (c.env.find? (.role .stringOfList)) &&
    Ix.Kernel.listTyOk (c.env.find? (.role .list)) &&
    Ix.Kernel.listNilTyOk (c.env.find? (.role .listNil)) &&
    Ix.Kernel.listConsTyOk (c.env.find? (.role .listCons)) &&
    Ix.Kernel.charTyOk (c.env.find? (.role .char)) &&
    Ix.Kernel.charOfNatTyOk (c.env.find? (.role .charOfNat))) = true
  rw [hn, hf1, hf2, hf3, hf4, hf5, hf6, hf7,
    stringTyOk_of_matchesPin rfl hm1,
    stringOfListTyOk_of_matchesPin rfl hm2,
    listTyOk_of_matchesPin rfl hm3,
    listNilTyOk_of_matchesPin rfl hm4,
    listConsTyOk_of_matchesPin rfl hm5,
    charTyOk_of_matchesPin rfl hm6,
    charOfNatTyOk_of_matchesPin rfl hm7]
  rfl

/-! ### `natOps`, `natAdd`, `eqStored`, and `quotBasis` -/

/-- `Red` reduces `.sort u` only to `.sort u`. -/
theorem red_sort_inv {env : Ix.Kernel.Env .anon} {d : Nat} {u : Ix.Kernel.Level}
    {w : Ix.Kernel.Expr .anon} (h : Ix.Kernel.Rules.Red env d (.sort u) w) :
    w = .sort u :=
  Ix.Kernel.Rules.Red.rigid h rfl

/-- `Red` reduces `.forallE ty body mb` only to `.forallE ty body mb`. -/
theorem red_forallE_inv {env : Ix.Kernel.Env .anon} {d : Nat}
    {ty body w : Ix.Kernel.Expr .anon} {mb : Ix.Kernel.BinderMeta}
    (h : Ix.Kernel.Rules.Red env d (.forallE ty body mb) w) :
    w = .forallE ty body mb :=
  Ix.Kernel.Rules.Red.rigid h rfl

/-- `EnvFacts.natOps` when any in-force binary `Nat` operation is stored as `.defnInfo`. -/
theorem natOps_of_defn {c : Ctx}
    (h : ∀ r, c.inForce r → (.role r : KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
      ∃ cv v hint, c.env.find? (.role r) = some (.defnInfo cv v hint)) :
    ∀ r, c.inForce r → (.role r : KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
      Ix.Kernel.natOpStored c.env (.role r) = true := by
  intro r hinf hmem
  obtain ⟨cv, v, hint, hf⟩ := h r hinf hmem
  simp [Ix.Kernel.natOpStored, hf]

/-- Pure derivation of `natAddTyOk` from `matchesPin` (e.g. via `StoredAs` against a `Nat → Nat → Nat`
definition), `natLitSupported`, and `.full`-grade `Infer` on `cv.type` (validating `mb.pw = .never`). -/
theorem natAddTyOk_of_matchesPin_and_infer {env : Ix.Kernel.Env .anon}
    {cv : Ix.Kernel.ConstantVal .anon} {v : Ix.Kernel.Expr .anon}
    {hint : Ix.Kernel.ReducibilityHint} {sty : Ix.Kernel.Expr .anon}
    (hf : env.find? Ix.Kernel.natAddName = some (.defnInfo cv v hint))
    (hnat : Ix.Kernel.natLitSupported env = true)
    (hpin : cv.matchesPin
      ⟨Ix.Kernel.natAddName, [],
        .forallE (.const Ix.Kernel.natName [])
          (.forallE (.const Ix.Kernel.natName []) (.const Ix.Kernel.natName []) default) default⟩
      = true)
    (hinf : Ix.Kernel.Rules.Infer env .full 0 cv.type sty) :
    Ix.Kernel.Rules.natAddTyOk (env.find? Ix.Kernel.natAddName) = true := by
  unfold Ix.Kernel.ConstantVal.matchesPin at hpin
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpin
  obtain ⟨⟨_, hlp⟩, hty⟩ := hpin
  obtain ⟨d1, b1, mb1, heq1, hd1, hb1⟩ := erasePw_eq_forallE hty
  obtain ⟨d2, b2, mb2, heq2, hd2, hb2⟩ := erasePw_eq_forallE hb1
  rw [erasePw_eq_const hd2, erasePw_eq_const hb2] at heq2
  rw [erasePw_eq_const hd1, heq2] at heq1
  rw [heq1] at hinf
  unfold Ix.Kernel.natLitSupported at hnat
  simp only [Bool.and_eq_true] at hnat
  have hnatInd := hnat.1.1
  cases hfN : env.find? Ix.Kernel.natName with
  | none => rw [hfN] at hnatInd; cases hnatInd
  | some ciN =>
    rw [hfN] at hnatInd
    cases ciN with
    | indInfo cvN capsN =>
      simp only [Ix.Kernel.natIndOk, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hnatInd
      cases hinf with
      | forallE _ _ hbs hv hz =>
        simp only [Ix.Kernel.Expr.instantiate1] at hbs
        cases hbs with
        | forallE _ _ hbs2 hv2 _ =>
          simp only [Ix.Kernel.Expr.instantiate1] at hbs2
          cases hbs2 with
          | const hfN' _ _ =>
            rw [hfN] at hfN'
            injection hfN' with hciN_eq
            subst hciN_eq
            simp only [Ix.Kernel.ConstantInfo.toConstantVal, hnatInd.1, hnatInd.2,
              Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst] at hv2
            have hv2_eq := red_sort_inv hv2
            injection hv2_eq with hv2_s
            subst hv2_s
            have hv_eq := red_sort_inv hv
            injection hv_eq with hv_s
            subst hv_s
            have hpw : mb1.pw = .never := by
              rw [← hz]
              rfl
            simp [Ix.Kernel.Rules.natAddTyOk, hf, hlp, heq1, hpw]
    | _ => simp [Ix.Kernel.natIndOk] at hnatInd

/-- `EnvFacts.eqStored` from in-force installation of `.eq`. -/
theorem eqStored_of_inForce {c : Ctx}
    (h : c.inForce .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci) :
    c.inForce .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci :=
  h

/-- `EnvFacts.quotBasis` from in-force installation of `BasisKind.declsA .quotK`. -/
theorem quotBasis_of_inForce {c : Ctx}
    (h : c.inForce .quot → ∀ ci ∈ Ix.Kernel.BasisKind.declsA (md := .anon) .quotK,
      c.env.find? ci.name = some ci) :
    c.inForce .quot → ∀ ci ∈ Ix.Kernel.BasisKind.declsA (md := .anon) .quotK,
      c.env.find? ci.name = some ci :=
  h

/-! ## Section 4: `ThmSim` (`thmToOpaqueDefn` → `ThmTyped` Rules transfer) and `evidence` -/

/-- Simulation relation from an `AcceptsRef` environment `envA` (where theorems were installed
as `.opaque` definitions via `thmToOpaqueDefn`) to a runtime environment `env` (where theorems are
stored as `.thmInfo` and satisfy `Ix.Kernel.Model.ThmTyped env`). -/
structure ThmSim (envA env : Ix.Kernel.Env .anon) : Prop where
  thmTyped : Ix.Kernel.Model.ThmTyped env
  find_sim : ∀ {k : KKey} {ciA : Ix.Kernel.ConstantInfo .anon},
    envA.find? k = some ciA →
    env.find? k = some ciA ∨
      ∃ cv value,
        ciA = .defnInfo cv value .opaque ∧
        k ∉ Ix.Kernel.Rules.natBinOpNames ∧
        k.isProjFnShape = false ∧
        k ≠ Ix.Kernel.punitName ∧
        k ≠ Ix.Kernel.punitRecName ∧
        env.find? k = some (.thmInfo cv value)
  tables_eq : ∀ {T : KKey} {cv : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon},
    envA.find? T = some (.indInfo cv caps) →
    env.find? (Ix.Kernel.projTableName T) = envA.find? (Ix.Kernel.projTableName T)

namespace ThmSim

theorem of_envExt {envA env : Ix.Kernel.Env .anon}
    (hthm : Ix.Kernel.Model.ThmTyped env)
    (hext : Ix.Kernel.EnvExt envA env) : ThmSim envA env where
  thmTyped := hthm
  find_sim := fun hf => Or.inl (hext.find hf)
  tables_eq := fun hT => hext.tables hT

theorem find_nonDefn {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {k : KKey} {ciA : Ix.Kernel.ConstantInfo .anon}
    (hf : envA.find? k = some ciA)
    (hnd : ∀ cv v, ciA ≠ .defnInfo cv v .opaque) :
    env.find? k = some ciA := by
  rcases h.find_sim hf with hf' | ⟨cv, v, heq, -⟩
  · exact hf'
  · exact absurd heq (hnd cv v)

theorem find_projShape {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {k : KKey} {ciA : Ix.Kernel.ConstantInfo .anon}
    (hf : envA.find? k = some ciA) (hsh : k.isProjFnShape = true) :
    env.find? k = some ciA := by
  rcases h.find_sim hf with hf' | ⟨_, _, _, _, hsh', -⟩
  · exact hf'
  · rw [hsh] at hsh'; cases hsh'

theorem findProj? {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {sn : KKey} {i : Nat} {entry : Ix.Kernel.ProjEntry .anon}
    (hp : envA.findProj? sn i = some entry) :
    env.findProj? sn i = some entry := by
  unfold Ix.Kernel.Env.findProj? at hp ⊢
  cases hf : envA.find? (Ix.Kernel.projTableName sn) with
  | none => rw [hf] at hp; cases hp
  | some c =>
    rw [h.find_projShape hf (Ix.Kernel.Semantics.projTableName_isProjFnShape sn)]
    rw [hf] at hp
    exact hp

theorem findProj?_eq {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {T : KKey} {cv : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hT : envA.find? T = some (.indInfo cv caps)) (j : Nat) :
    env.findProj? T j = envA.findProj? T j := by
  unfold Ix.Kernel.Env.findProj?
  rw [h.tables_eq hT]

theorem towerSlotsAll_eq {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {T : KKey} {cv : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hT : envA.find? T = some (.indInfo cv caps)) (nF : Nat) :
    Ix.Kernel.towerSlotsAll env T nF = Ix.Kernel.towerSlotsAll envA T nF := by
  unfold Ix.Kernel.towerSlotsAll
  simp only [h.findProj?_eq hT]

theorem etaProjs_eq {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {T : KKey} {cv : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hT : envA.find? T = some (.indInfo cv caps))
    (us : List KLevel) (targs : List KExpr) (b : KExpr) (nF : Nat) :
    Ix.Kernel.etaProjs env T us targs b nF = Ix.Kernel.etaProjs envA T us targs b nF := by
  unfold Ix.Kernel.etaProjs
  rw [h.towerSlotsAll_eq hT]

theorem etaFabArgsE_eq {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {T : KKey} {cv : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hT : envA.find? T = some (.indInfo cv caps))
    (us : List KLevel) (targs : List KExpr) (b : KExpr) (nF : Nat) :
    Ix.Kernel.etaFabArgsE env T us targs b nF = Ix.Kernel.etaFabArgsE envA T us targs b nF := by
  unfold Ix.Kernel.etaFabArgsE
  rw [h.etaProjs_eq hT]

theorem recSlotsAll_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {T : KKey} {nF : Nat}
    (hs : Ix.Kernel.recSlotsAll envA T nF = true) :
    Ix.Kernel.recSlotsAll env T nF = true := by
  unfold Ix.Kernel.recSlotsAll at hs ⊢
  rw [List.all_eq_true] at hs ⊢
  intro j hj
  have hj' := hs j hj
  cases hf : envA.find? (Ix.Kernel.projFnName T j) with
  | none => rw [hf] at hj'; cases hj'
  | some c =>
    have hsh : (Ix.Kernel.projFnName T j).isProjFnShape = true := rfl
    rw [h.find_projShape hf hsh]
    rw [hf] at hj'
    exact hj'

theorem natLitSupported_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    (hs : Ix.Kernel.natLitSupported envA = true) :
    Ix.Kernel.natLitSupported env = true := by
  unfold Ix.Kernel.natLitSupported at hs ⊢
  simp only [Bool.and_eq_true] at hs ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 := hs.1.1
    cases hf : envA.find? Ix.Kernel.natName with
    | none => rw [hf] at h1; cases h1
    | some ci =>
      cases ci <;> rw [hf] at h1 <;> try cases h1
      rw [h.find_nonDefn hf (fun _ _ heq => nomatch heq)]
      exact h1
  · have h2 := hs.1.2
    cases hf : envA.find? Ix.Kernel.natZeroName with
    | none => rw [hf] at h2; cases h2
    | some ci =>
      cases ci <;> rw [hf] at h2 <;> try cases h2
      rw [h.find_nonDefn hf (fun _ _ heq => nomatch heq)]
      exact h2
  · have h3 := hs.2
    cases hf : envA.find? Ix.Kernel.natSuccName with
    | none => rw [hf] at h3; cases h3
    | some ci =>
      cases ci <;> rw [hf] at h3 <;> try cases h3
      rw [h.find_nonDefn hf (fun _ _ heq => nomatch heq)]
      exact h3

private theorem strTyPred_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {k : KKey} {p : Option (Ix.Kernel.ConstantInfo .anon) → Bool}
    (hp_val : ∀ ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon,
      ci₁.toConstantVal = ci₂.toConstantVal → p (some ci₁) = p (some ci₂))
    (hp_none : p none = false)
    (hok : p (envA.find? k) = true) :
    p (env.find? k) = true := by
  cases hf : envA.find? k with
  | none => rw [hf, hp_none] at hok; cases hok
  | some ciA =>
    rw [hf] at hok
    rcases h.find_sim hf with hf' | ⟨cv, val, rfl, _, _, _, _, hf'⟩
    · rw [hf']; exact hok
    · rw [hf', ← hp_val (.defnInfo cv val .opaque) (.thmInfo cv val) rfl]; exact hok

theorem strLitSupported_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    (hs : Ix.Kernel.strLitSupported envA = true) :
    Ix.Kernel.strLitSupported env = true := by
  unfold Ix.Kernel.strLitSupported at hs ⊢
  simp only [Bool.and_eq_true] at hs ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hs
  exact ⟨⟨⟨⟨⟨⟨⟨h.natLitSupported_mono hn,
    strTyPred_mono h (fun _ _ he => by simp [Ix.Kernel.stringTyOk, he]) rfl h1⟩,
    strTyPred_mono h (fun _ _ he => by simp [Ix.Kernel.stringOfListTyOk, he]) rfl h2⟩,
    strTyPred_mono h (fun _ _ he => by simp [Ix.Kernel.listTyOk, he]) rfl h3⟩,
    strTyPred_mono h (fun _ _ he => by simp [Ix.Kernel.listNilTyOk, he]) rfl h4⟩,
    strTyPred_mono h (fun _ _ he => by simp [Ix.Kernel.listConsTyOk, he]) rfl h5⟩,
    strTyPred_mono h (fun _ _ he => by simp [Ix.Kernel.charTyOk, he]) rfl h6⟩,
    strTyPred_mono h (fun _ _ he => by simp [Ix.Kernel.charOfNatTyOk, he]) rfl h7⟩

theorem natOpStored_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {c : KKey} (hc : c ∈ Ix.Kernel.Rules.natBinOpNames)
    (hs : Ix.Kernel.natOpStored envA c = true) :
    Ix.Kernel.natOpStored env c = true := by
  unfold Ix.Kernel.natOpStored at hs ⊢
  cases hf : envA.find? c with
  | none => rw [hf] at hs; cases hs
  | some ciA =>
    rcases h.find_sim hf with hf' | ⟨_, _, _, hnot, -⟩
    · rw [hf']; rw [hf] at hs; exact hs
    · exact absurd hc hnot

theorem natAddTyOk_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    (ht : Ix.Kernel.Rules.natAddTyOk (envA.find? Ix.Kernel.natAddName) = true) :
    Ix.Kernel.Rules.natAddTyOk (env.find? Ix.Kernel.natAddName) = true := by
  cases hf : envA.find? Ix.Kernel.natAddName with
  | none => rw [hf] at ht; cases ht
  | some ciA =>
    have hmem : (Ix.Kernel.natAddName : KKey) ∈ Ix.Kernel.Rules.natBinOpNames := by
      simp [Ix.Kernel.Rules.natBinOpNames]
    rcases h.find_sim hf with hf' | ⟨_, _, _, hnot, -⟩
    · rw [hf']; rw [hf] at ht; exact ht
    · exact absurd hmem hnot

theorem isUnitLikeTy_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {e : KExpr} (hs : Ix.Kernel.isUnitLikeTy envA e = true) :
    Ix.Kernel.isUnitLikeTy env e = true := by
  cases e with
  | const c us =>
    unfold Ix.Kernel.isUnitLikeTy at hs ⊢
    simp only [Bool.and_eq_true] at hs ⊢
    obtain ⟨⟨hc, h1⟩, h2⟩ := hs
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · cases hf : envA.find? Ix.Kernel.punitName with
      | none => rw [hf] at h1; cases h1
      | some ci =>
        rcases h.find_sim hf with hf' | ⟨_, _, _, _, _, hne, -⟩
        · rw [hf']; rw [hf] at h1; exact h1
        · exact absurd rfl hne
    · cases hf : envA.find? Ix.Kernel.punitRecName with
      | none => rw [hf] at h2; cases h2
      | some ci =>
        rcases h.find_sim hf with hf' | ⟨_, _, _, _, _, _, hne, -⟩
        · rw [hf']; rw [hf] at h2; exact h2
        · exact absurd rfl hne
  | _ => cases hs

theorem headTypePW_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {e : KExpr} {n : Nat} {pw : Ix.Kernel.PropWhen}
    (hs : Ix.Kernel.headTypePW envA.find? e n = some pw) :
    Ix.Kernel.headTypePW env.find? e n = some pw := by
  cases e with
  | const I us =>
    unfold Ix.Kernel.headTypePW at hs ⊢
    dsimp only at hs ⊢
    cases hf : envA.find? I with
    | none => rw [hf] at hs; cases hs
    | some ciA =>
      rcases h.find_sim hf with hf' | ⟨cv, val, rfl, _, _, _, _, hf'⟩
      · rw [hf']; rw [hf] at hs; exact hs
      · rw [hf']; rw [hf] at hs; exact hs
  | fvar => exact hs
  | _ => cases hs

theorem typeSortPW_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {T : KExpr} {pw : Ix.Kernel.PropWhen}
    (hs : Ix.Kernel.typeSortPW envA.find? T = some pw) :
    Ix.Kernel.typeSortPW env.find? T = some pw := by
  by_cases h1 : ∃ ty b m, T = .forallE ty b m
  · obtain ⟨ty, b, m, rfl⟩ := h1; exact hs
  by_cases h2 : ∃ u, T = .sort u
  · obtain ⟨u, rfl⟩ := h2; exact hs
  have h1' : ∀ ty b m, T ≠ .forallE ty b m := fun ty b m e => h1 ⟨ty, b, m, e⟩
  have h2' : ∀ u, T ≠ .sort u := fun u e => h2 ⟨u, e⟩
  rw [Ix.Kernel.typeSortPW_other h1' h2'] at hs ⊢
  exact h.headTypePW_mono hs

theorem headProofPW_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {e : KExpr} {pw : Ix.Kernel.PropWhen}
    (hs : Ix.Kernel.headProofPW envA.find? e = some pw) :
    Ix.Kernel.headProofPW env.find? e = some pw := by
  cases e with
  | const c us =>
    unfold Ix.Kernel.headProofPW at hs ⊢
    dsimp only at hs ⊢
    cases hf : envA.find? c with
    | none => rw [hf] at hs; cases hs
    | some ciA =>
      have hci : ∃ ci, env.find? c = some ci ∧ ci.isTowerEntry = ciA.isTowerEntry ∧
          ci.toConstantVal = ciA.toConstantVal := by
        rcases h.find_sim hf with hf' | ⟨cv, val, rfl, _, _, _, _, hf'⟩
        · exact ⟨ciA, hf', rfl, rfl⟩
        · exact ⟨.thmInfo cv val, hf', rfl, rfl⟩
      obtain ⟨ci, hf', htw_eq, hcv_eq⟩ := hci
      rw [hf']; rw [hf] at hs
      dsimp only at hs ⊢
      rw [htw_eq, hcv_eq]
      by_cases htw : ciA.isTowerEntry = true
      · simp [htw] at hs
      · by_cases hl : us.length = ciA.toConstantVal.levelParams.length
        · simp only [htw, hl, ite_true, ite_false, Bool.false_eq_true] at hs ⊢
          rcases ht : Ix.Kernel.typeSortPW envA.find? ciA.toConstantVal.type with _ | pw'
          · rw [ht] at hs; cases hs
          · rw [h.typeSortPW_mono ht]; rw [ht] at hs; exact hs
        · simp [htw, hl] at hs
  | fvar _ _ => exact h.typeSortPW_mono hs
  | _ => exact hs

theorem isProofFast_mono {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {a : KExpr} (hs : Ix.Kernel.isProofFast envA.find? a = true) :
    Ix.Kernel.isProofFast env.find? a = true := by
  unfold Ix.Kernel.isProofFast at hs ⊢
  have key : ∀ pw, Ix.Kernel.proofPW envA.find? a = some pw →
      Ix.Kernel.proofPW env.find? a = some pw := by
    intro pw hp
    by_cases hl : ∃ ty b m, a = .lam ty b m
    · obtain ⟨ty, b, m, rfl⟩ := hl; exact hp
    have hl' : ∀ ty b m, a ≠ .lam ty b m := fun ty b m e => hl ⟨ty, b, m, e⟩
    rw [Ix.Kernel.proofPW_other hl'] at hp ⊢
    exact h.headProofPW_mono hp
  rcases hp : Ix.Kernel.proofPW envA.find? a with _ | pw
  · rw [hp] at hs; cases hs
  · rw [key pw hp]; rw [hp] at hs; exact hs

private theorem mkAppN_append : ∀ (xs ys : List KExpr) (f : KExpr),
    Ix.Kernel.Expr.mkAppN f (xs ++ ys) = Ix.Kernel.Expr.mkAppN (Ix.Kernel.Expr.mkAppN f xs) ys
  | [], _, _ => rfl
  | x :: xs, ys, f => mkAppN_append xs ys (.app f x)

private theorem eq_mkAppN_getAppFn_getAppArgs : ∀ e : KExpr,
    e = Ix.Kernel.Expr.mkAppN e.getAppFn e.getAppArgs
  | .app f a => by
    show Ix.Kernel.Expr.app f a = Ix.Kernel.Expr.mkAppN f.getAppFn (f.getAppArgs ++ [a])
    rw [mkAppN_append]
    exact congrArg (Ix.Kernel.Expr.app · a) (eq_mkAppN_getAppFn_getAppArgs f)
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

private theorem red_mkAppN_fn {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (args : List KExpr) {f f' : KExpr},
      Ix.Kernel.Rules.Red env d f f' →
      Ix.Kernel.Rules.Red env d (Ix.Kernel.Expr.mkAppN f args) (Ix.Kernel.Expr.mkAppN f' args)
  | [], _, _, hr => hr
  | _ :: args, _, _, hr => red_mkAppN_fn args (.appFn hr)

/-- Unfolding in `envA` becomes either `Red.delta` (when still `.defnInfo` in `env`) or
`Red.deltaThm` + spine `Red.appFn` (when `.thmInfo` in `env` under `ThmTyped env`). -/
theorem delta_sim {envA env : Ix.Kernel.Env .anon} (h : ThmSim envA env)
    {d : Nat} {e e' : KExpr}
    (hu : Ix.Kernel.unfoldDefinition envA e = some e') :
    Ix.Kernel.Rules.Red env d e e' := by
  unfold Ix.Kernel.unfoldDefinition at hu
  split at hu
  · rename_i n us hfn
    cases hf : envA.find? n with
    | none => rw [hf] at hu; cases hu
    | some ciA =>
      rw [hf] at hu
      cases ciA with
      | defnInfo cv value hint =>
        dsimp only at hu
        split at hu
        · next hlen =>
          obtain rfl := Option.some.inj hu
          rcases h.find_sim hf with hf' | ⟨cv', val', heq, _, _, _, _, hf'⟩
          · refine .delta ?_
            unfold Ix.Kernel.unfoldDefinition
            rw [hfn]
            dsimp only
            rw [hf']
            dsimp only
            simp only [hlen, ↓reduceIte]
          · injection heq with hcv_eq hval_eq _
            subst hcv_eq hval_eq
            obtain ⟨hvf, hvb, vt, s, u, hinf, hde, hinfT, hred, hz⟩ := h.thmTyped n cv value hf'
            have hhead_red : Ix.Kernel.Rules.Red env d (.const n us)
                (value.instantiateLevelParams cv.levelParams us) :=
              .deltaThm hf' hlen hvf hvb hinf hde hinfT hred hz
            have hspine := red_mkAppN_fn e.getAppArgs hhead_red
            have he_eq := eq_mkAppN_getAppFn_getAppArgs e
            rw [hfn] at he_eq
            rwa [← he_eq] at hspine
        · cases hu
      | _ => cases hu
  · cases hu

mutual

/-- Transfer `Rules.Red` from `envA` to `env` across `ThmSim`. -/
theorem red {envA env : Ix.Kernel.Env .anon} (hS : ThmSim envA env) :
    ∀ {d : Nat} {e e' : KExpr},
      Ix.Kernel.Rules.Red envA d e e' → Ix.Kernel.Rules.Red env d e e'
  | _, _, _, .refl => .refl
  | _, _, _, .trans h₁ h₂ => .trans (red hS h₁) (red hS h₂)
  | _, _, _, .appFn h => .appFn (red hS h)
  | _, _, _, .projArg h => .projArg (red hS h)
  | _, _, _, .appArg h => .appArg (red hS h)
  | _, _, _, .betaGate hnev => .betaGate hnev
  | _, _, _, .beta hta hd' => .beta (infer hS hta) (defEq hS hd')
  | _, _, _, .delta hu => hS.delta_sim hu
  | _, _, _, .deltaThm hf hlen hvf hvb hinf hde hinfT hred hz =>
    .deltaThm (hS.find_nonDefn hf (fun _ _ heq => nomatch heq)) hlen hvf hvb
      (infer hS hinf) (defEq hS hde) (infer hS hinfT) (red hS hred) hz
  | _, _, _, .eqProof (ci := ciA) hhead hfE hp hwp hbp hlp ha hda hb hdb hTT hred hv => by
    have hfE' : ∃ ci, env.find? Ix.Kernel.eqName = some ci := by
      rcases hS.find_sim hfE with hf' | ⟨cv, val, _, _, _, _, _, hf'⟩
      · exact ⟨ciA, hf'⟩
      · exact ⟨.thmInfo cv val, hf'⟩
    obtain ⟨ci, hfE'⟩ := hfE'
    exact .eqProof hhead hfE' (infer hS hp) hwp hbp hlp
      (infer hS ha) (defEq hS hda) (infer hS hb) (defEq hS hdb)
      (infer hS hTT) (red hS hred) hv
  | _, _, _, .natLit h => .natLit (hS.natLitSupported_mono h)
  | _, _, _, .natZeroLit h => .natZeroLit (hS.natLitSupported_mono h)
  | _, _, _, .strLit h => .strLit (hS.strLitSupported_mono h)
  | _, _, _, .natSucc hsup hw hn => .natSucc (hS.natLitSupported_mono hsup) (red hS hw) hn
  | _, _, _, .natOp hc hst hwa hn₁ hwb hn₂ hr =>
    .natOp hc (hS.natOpStored_mono hc hst) (red hS hwa) hn₁ (red hS hwb) hn₂ hr
  | _, _, _, .natAddSucc hs ht =>
    .natAddSucc (hS.natLitSupported_mono hs) (hS.natAddTyOk_mono ht)
  | _, _, _, .natAddZero hs ht hw hn =>
    .natAddZero (hS.natLitSupported_mono hs) (hS.natAddTyOk_mono ht) (red hS hw) hn
  | _, _, _, .proj hent hhead hi hlen hus hfire hctor hcerts =>
    .proj (hS.findProj? hent) hhead hi hlen hus hfire
      (hS.find_nonDefn hctor (fun _ _ heq => nomatch heq)) (certs hS hcerts)
  | _, _, _, .iota hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv hparams
      hcertR hcertC hres hidx =>
    .iota hhead (hS.find_nonDefn hrec (fun _ _ heq => nomatch heq)) hlen hus (red hS hmajor)
      hmhead (hS.find_nonDefn hctor (fun _ _ heq => nomatch heq)) hrule hmlen hfire hlv
      (fun hc => defEqList hS (hparams hc)) (certs hS hcertR) (certs hS hcertC) hres
      (fun hne => defEqList hS (hidx hne))
  | _, _, _, .rescueK hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws hb hlv'
      hcerts htf hdt hpi =>
    .rescueK (hS.find_nonDefn hrec (fun _ _ heq => nomatch heq)) hk
      (hS.find_nonDefn hctor (fun _ _ heq => nomatch heq)) hres
      (hS.find_nonDefn hind (fun _ _ heq => nomatch heq))
      (infer hS htm) (red hS htmaj) hthead hlv hnP hfab hws hb hlv'
      (certs hS hcerts) (infer hS htf) (defEq hS hdt) (defEq hS hpi)
  | _, _, _, .rescueEta (major := major) (tmaj := tmaj) (ust := ust) (caps := caps)
      hrec heta hctor hres hind htm htmaj hthead hlen hlv hnz hfab hws hb hlv' hcerts hproj hpi => by
    have hfab' : Ix.Kernel.etaFabArgsE env _ ust tmaj.getAppArgs major caps.etaFields =
        Ix.Kernel.etaFabArgsE envA _ ust tmaj.getAppArgs major caps.etaFields :=
      hS.etaFabArgsE_eq hind ust tmaj.getAppArgs major caps.etaFields
    have hcs := certs hS hcerts
    rw [← hfab'] at hcs
    exact .rescueEta (hS.find_nonDefn hrec (fun _ _ heq => nomatch heq)) heta
      (hS.find_nonDefn hctor (fun _ _ heq => nomatch heq)) hres
      (hS.find_nonDefn hind (fun _ _ heq => nomatch heq))
      (infer hS htm) (red hS htmaj) hthead hlen hlv hnz
      (by rw [hfab, ← hfab']) hws hb hlv' hcs
      (fun hno => by
        rw [hS.towerSlotsAll_eq hind] at hno
        exact etaProjCerts hS (hproj hno))
      (defEq hS hpi)
  | _, _, _, .rescueAnd hrec hctor hres hind htm htmaj hthead hlen hlv hslots hfab hws hb hlv'
      hcerts htf hdt hpi =>
    .rescueAnd (hS.find_nonDefn hrec (fun _ _ heq => nomatch heq))
      (hS.find_nonDefn hctor (fun _ _ heq => nomatch heq)) hres
      (hS.find_nonDefn hind (fun _ _ heq => nomatch heq))
      (infer hS htm) (red hS htmaj) hthead hlen hlv
      (fun j hj => by
        obtain ⟨e, hfe, hct, hnP, hnF, hfire⟩ := hslots j hj
        exact ⟨e, hS.findProj? hfe, hct, hnP, hnF, hfire⟩)
      hfab hws hb hlv' (certs hS hcerts) (infer hS htf) (defEq hS hdt) (defEq hS hpi)

/-- Transfer `Rules.DefEq` from `envA` to `env` across `ThmSim`. -/
theorem defEq {envA env : Ix.Kernel.Env .anon} (hS : ThmSim envA env) :
    ∀ {d : Nat} {a b : KExpr},
      Ix.Kernel.Rules.DefEq envA d a b → Ix.Kernel.Rules.DefEq env d a b
  | _, _, _, .refl => .refl
  | _, _, _, .symm h => .symm (defEq hS h)
  | _, _, _, .redL hr h => .redL (red hS hr) (defEq hS h)
  | _, _, _, .sort h => .sort h
  | _, _, _, .fvar => .fvar
  | _, _, _, .const h => .const h
  | _, _, _, .natZero => .natZero
  | _, _, _, .natSucc h => .natSucc (defEq hS h)
  | _, _, _, .natOffset hs ht ha hb h =>
    .natOffset (hS.natLitSupported_mono hs) (fun h' => hS.natAddTyOk_mono (ht h')) ha hb (defEq hS h)
  | _, _, _, .forallE hty hbody hpw => .forallE (defEq hS hty) (defEq hS hbody) hpw
  | _, _, _, .lam hty hbody hpw => .lam (defEq hS hty) (defEq hS hbody) hpw
  | _, _, _, .app hf ha => .app (defEq hS hf) (defEq hS ha)
  | _, _, _, .proj h => .proj (defEq hS h)
  | _, _, _, .eta htb hwtb hty hbody hpw =>
    .eta (infer hS htb) (red hS hwtb) (defEq hS hty) (defEq hS hbody) hpw
  | _, _, _, .proofFast h₁ h₂ =>
    .proofFast (hS.isProofFast_mono h₁) (hS.isProofFast_mono h₂)
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    .proofIrrel (infer hS hta) (infer hS htta) (red hS hu) hu0
      (infer hS htb) (infer hS httb) (red hS hv) hv0
  | _, _, _, .unitLike hta hwta hua htb hwtb hub =>
    .unitLike (infer hS hta) (red hS hwta) (hS.isUnitLikeTy_mono hua)
      (infer hS htb) (red hS hwtb) (hS.isUnitLikeTy_mono hub)
  | _, _, _, .structEta htb hwtb hhead hctor hlen hthead hind heta hetaCtor hresT hresc
      htlen hlv hlps hslots hus hcerts hproj hparams hfields => by
    have hf := defEqList hS hfields
    rw [← hS.etaProjs_eq hind] at hf
    refine .structEta (infer hS htb) (red hS hwtb) hhead
      (hS.find_nonDefn hctor (fun _ _ heq => nomatch heq)) hlen hthead
      (hS.find_nonDefn hind (fun _ _ heq => nomatch heq)) heta hetaCtor hresT hresc
      htlen hlv hlps ?_ hus (certs hS hcerts)
      (fun hno => by
        rw [hS.towerSlotsAll_eq hind] at hno
        exact etaProjCerts hS (hproj hno))
      (defEqList hS hparams) hf
    rw [hS.towerSlotsAll_eq hind]
    rcases Bool.or_eq_true_iff.mp hslots with h | h
    · rw [h]; rfl
    · rw [hS.recSlotsAll_mono h, Bool.or_true]
  | _, _, _, .structUnit hta hwta hthead hind hunit hresT htlen hlv htb hwtb hd' hcerts =>
    .structUnit (infer hS hta) (red hS hwta) hthead
      (hS.find_nonDefn hind (fun _ _ heq => nomatch heq)) hunit hresT htlen hlv
      (infer hS htb) (red hS hwtb) (defEq hS hd') (certs hS hcerts)
  | _, _, _, .proofIrrelTy hta htta hu hu0 htb hd' =>
    .proofIrrelTy (infer hS hta) (infer hS htta) (red hS hu) hu0 (infer hS htb) (defEq hS hd')
  | _, _, _, .unitLikeTy hta hwta hthead hind hunit htlen hcerts hkind htb hd' =>
    .unitLikeTy (infer hS hta) (red hS hwta) hthead
      (hS.find_nonDefn hind (fun _ _ heq => nomatch heq)) hunit htlen (certs hS hcerts)
      (hkind.imp id hS.isUnitLikeTy_mono) (infer hS htb) (defEq hS hd')
  | _, _, _, .structEtaTy hhead hctor hlen hind heta hetaCtor hpos htow hta hwta hcerts
      htb hd' hfields =>
    .structEtaTy hhead (hS.find_nonDefn hctor (fun _ _ heq => nomatch heq)) hlen
      (hS.find_nonDefn hind (fun _ _ heq => nomatch heq)) heta hetaCtor hpos
      (by rw [hS.towerSlotsAll_eq hind]; exact htow) (infer hS hta) (red hS hwta)
      (certs hS hcerts) (infer hS htb) (defEq hS hd') (defEqList hS hfields)

/-- Transfer `Rules.Infer` from `envA` to `env` across `ThmSim`. -/
theorem infer {envA env : Ix.Kernel.Env .anon} (hS : ThmSim envA env) :
    ∀ {g : Ix.Kernel.Rules.Grade} {d : Nat} {e t : KExpr},
      Ix.Kernel.Rules.Infer envA g d e t → Ix.Kernel.Rules.Infer env g d e t
  | _, _, _, _, .sort => .sort
  | _, _, _, _, .fvar h => .fvar h
  | _, _, _, _, .const (ci := ciA) hf htower hus => by
    rcases hS.find_sim hf with hf' | ⟨cv, val, rfl, _, _, _, _, hf'⟩
    · exact .const hf' htower hus
    · exact .const (ci := .thmInfo cv val) hf' rfl hus
  | _, _, _, _, .natLit h => .natLit (hS.natLitSupported_mono h)
  | _, _, _, _, .strLit h => .strLit (hS.strLitSupported_mono h)
  | _, _, _, _, .forallE hs hu hbs hv hz =>
    .forallE (infer hS hs) (red hS hu) (infer hS hbs) (red hS hv) hz
  | _, _, _, _, .lam hs hu hbt hchain hbtt hv hz =>
    .lam (fun hg => infer hS (hs hg)) (fun hg => red hS (hu hg)) (infer hS hbt) hchain
      (fun h => infer hS (hbtt h)) (fun h => red hS (hv h)) hz
  | _, _, _, _, .app htf hw hta hd' =>
    .app (infer hS htf) (red hS hw) (infer hS hta) (defEq hS hd')
  | _, _, _, _, .appSkip htf hw hnev =>
    .appSkip (infer hS htf) (red hS hw) hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop =>
    .proj (infer hS htpe) (red hS hte) hhead (hS.findProj? hent) hlen hus hprop

/-- Transfer `Rules.Certs` from `envA` to `env` across `ThmSim`. -/
theorem certs {envA env : Ix.Kernel.Env .anon} (hS : ThmSim envA env) :
    ∀ {d : Nat} {lic : Bool} {ty : KExpr} {args : List KExpr},
      Ix.Kernel.Rules.Certs envA d lic ty args →
      Ix.Kernel.Rules.Certs env d lic ty args
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .skip hlic hnev hrest => .skip hlic hnev (certs hS hrest)
  | _, _, _, _, .cert hta hd' hrest => .cert (infer hS hta) (defEq hS hd') (certs hS hrest)

/-- Transfer `Rules.DefEqList` from `envA` to `env` across `ThmSim`. -/
theorem defEqList {envA env : Ix.Kernel.Env .anon} (hS : ThmSim envA env) :
    ∀ {d : Nat} {as bs : List KExpr},
      Ix.Kernel.Rules.DefEqList envA d as bs →
      Ix.Kernel.Rules.DefEqList env d as bs
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (defEq hS h) (defEqList hS hs)

/-- Transfer `Rules.EtaProjCerts` from `envA` to `env` across `ThmSim`. -/
theorem etaProjCerts {envA env : Ix.Kernel.Env .anon} (hS : ThmSim envA env) :
    ∀ {d : Nat} {T : KKey} {us' : List KLevel} {targs : List KExpr} {b : KExpr}
      {lpsT : List Ix.Kernel.LevelParam} {idxs : List Nat},
      Ix.Kernel.Rules.EtaProjCerts envA d T us' targs b lpsT idxs →
      Ix.Kernel.Rules.EtaProjCerts env d T us' targs b lpsT idxs
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons hf hlps hstrip hcerts hrest =>
    .cons (hS.find_nonDefn hf (fun _ _ heq => nomatch heq)) hlps hstrip
      (certs hS hcerts) (etaProjCerts hS hrest)

end

end ThmSim

/-! ### `annotateCore` → `Rules.Annot` and `eqnsCheck` inversion -/

/-- Any successful `annotateCore` run produces a `Rules.Annot` derivation. -/
theorem annotateCore_to_annot {mode : Ix.Kernel.CheckMode} {env : Ix.Kernel.Env .anon} :
    ∀ {fuel d : Nat} {e e' : KExpr},
      Ix.Kernel.annotateCore mode env fuel d e = .ok e' →
      Ix.Kernel.Rules.Annot d e e'
  | 0, _, _, _, h => by
    simp [Ix.Kernel.annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, d, .bvar _, e', h => by
    rw [Ix.Kernel.annotateCore_succ] at h
    simp only [Ix.Kernel.annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .bvar
  | fuel + 1, d, .fvar _ _, e', h => by
    rw [Ix.Kernel.annotateCore_succ] at h
    simp only [Ix.Kernel.annotateBody] at h
    split at h
    · rename_i hlt
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .fvar hlt
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, d, .sort _, e', h => by
    rw [Ix.Kernel.annotateCore_succ] at h
    simp only [Ix.Kernel.annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .sort
  | fuel + 1, d, .const _ _, e', h => by
    rw [Ix.Kernel.annotateCore_succ] at h
    simp only [Ix.Kernel.annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .const
  | fuel + 1, d, .lit (.natVal _), e', h => by
    rw [Ix.Kernel.annotateCore_succ] at h
    dsimp only [Ix.Kernel.annotateBody] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact .lit
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, d, .lit (.strVal _), e', h => by
    rw [Ix.Kernel.annotateCore_succ] at h
    dsimp only [Ix.Kernel.annotateBody] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact .lit
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, d, .app f a, e', h => by
    obtain ⟨f', a', hf, ha, rfl⟩ := Ix.Kernel.annotateCore_app_inv h
    exact .app (annotateCore_to_annot hf) (annotateCore_to_annot ha)
  | fuel + 1, d, .proj _ _ pe, e', h => by
    obtain ⟨pe', _, _, hpe, _, _, _, _, _, _, _, _, rfl⟩ := Ix.Kernel.annotateCore_proj_inv h
    exact .proj (annotateCore_to_annot hpe)
  | fuel + 1, d, .forallE ty body mb, e', h => by
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := Ix.Kernel.annotateCore_forallE_inv h
    exact .forallE (annotateCore_to_annot hty) (annotateCore_to_annot hbody)
  | fuel + 1, d, .lam ty body mb, e', h => by
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := Ix.Kernel.annotateCore_lam_inv h
    exact .lam (annotateCore_to_annot hty) (annotateCore_to_annot hbody)
  | fuel + 1, d, .letE _ _ _ _, e', h => by
    obtain ⟨_, _, _, _, hlet, _⟩ := Ix.Kernel.annotateCore_letE_inv h
    exact .letE (annotateCore_to_annot hlet)

private theorem mem_zip_of_getElem? {α β : Type} :
    ∀ {xs : List α} {ys : List β} {i : Nat} {x : α} {y : β},
      xs[i]? = some x → ys[i]? = some y → (x, y) ∈ xs.zip ys
  | [], _, _, _, _, hx, _ => by simp at hx
  | _, [], _, _, _, _, hy => by simp at hy
  | x₀ :: _, y₀ :: _, 0, x, y, hx, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
    subst hx hy
    exact List.mem_cons_self
  | _ :: xs, _ :: ys, i + 1, x, y, hx, hy => by
    simp only [List.getElem?_cons_succ] at hx hy
    exact List.mem_cons_of_mem _ (mem_zip_of_getElem? hx hy)

private theorem list_forIn_step_mem {α ε : Type}
    (step : α → PUnit → Except ε (ForInStep PUnit))
    (hstep : ∀ a r, step a PUnit.unit = .ok r → r = ForInStep.yield PUnit.unit) :
    ∀ {l : List α} {u : PUnit},
      forIn l PUnit.unit step = .ok u →
      ∀ a ∈ l, ∃ r, step a PUnit.unit = .ok r
  | [], _, _, _, ha => nomatch ha
  | x₀ :: xs, u, hfor, a, ha => by
    simp only [forIn, List.forIn'_cons, Bind.bind, Except.bind] at hfor
    cases hs0 : step x₀ PUnit.unit with
    | error e =>
      rw [hs0] at hfor
      cases hfor
    | ok r =>
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact ⟨r, hs0⟩
      · have hr := hstep x₀ r hs0
        rw [hs0, hr] at hfor
        dsimp only at hfor
        exact list_forIn_step_mem step hstep hfor a hmem

/-- Unpack `Ix.Kernel.eqnsCheck (Ix.Kernel.fueledOps .verified F) envA r ev = .ok ()` at a proof
evidence entry `(ev.of r)[i]? = some (.proof (key, val))` and `roleStatement r i = some stmt`. -/
theorem eqnsCheck_proof_inv {F : Nat} {envA : Ix.Kernel.Env .anon}
    {r : Ix.Kernel.Role} {ev : Ix.Kernel.Evidences .anon}
    {i : Nat} {key : KKey} {val stmt : KExpr}
    (hok : Ix.Kernel.eqnsCheck (Ix.Kernel.fueledOps .verified F) envA r ev = .ok ())
    (hev : (ev.of r)[i]? = some (.proof (key, val)))
    (hstmt : roleStatement r i = some stmt) :
    ∃ (levels : Nat) (ciA : Ix.Kernel.ConstantInfo .anon)
      (cvA : Ix.Kernel.ConstantVal .anon) (theoremTypeA stmtA : KExpr),
      envA.find? key = some ciA ∧
      ((∃ v, ciA = .thmInfo cvA v) ∨ (∃ v, ciA = .defnInfo cvA v .opaque)) ∧
      cvA.levelParams.length = levels ∧
      cvA.levelParams.eraseDups = cvA.levelParams ∧
      Ix.Kernel.annotateCore .verified envA F 0
        (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type) =
        .ok theoremTypeA ∧
      Ix.Kernel.annotateCore .verified envA F 0 stmt = .ok stmtA ∧
      Ix.Kernel.Rules.Annot 0
        (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type)
        theoremTypeA ∧
      Ix.Kernel.Rules.Annot 0 stmt stmtA ∧
      Ix.Kernel.Rules.DefEq envA 0 theoremTypeA stmtA := by
  unfold roleStatement at hstmt
  unfold Ix.Kernel.eqnsCheck at hok
  cases hspec : Ix.Kernel.Role.spec (md := .anon) r with
  | block _ | anchor _ _ | ops _ _ | «axiom» _ _ =>
    rw [hspec] at hstmt; cases hstmt
  | eqns levels expectedTy equations =>
    rw [hspec] at hstmt hok
    dsimp only at hstmt hok
    cases heqi : equations[i]? with
    | none => rw [heqi] at hstmt; cases hstmt
    | some eq =>
      rw [heqi] at hstmt
      simp only [Option.map_some, Option.some.injEq] at hstmt
      subst hstmt
      dsimp only [Bind.bind, Except.bind] at hok
      cases hfR : envA.find? (Ix.Kernel.roleKey r) with
      | none => rw [hfR] at hok; cases hok
      | some ciR =>
        rw [hfR] at hok
        cases ciR with
        | defnInfo cvR vR hR =>
          dsimp only at hok
          split at hok
          · cases h1 : Ix.Kernel.checkRoleTerm (m := Ix.Kernel.CheckM .anon) envA cvR.levelParams cvR.type with
            | error _ => rw [h1] at hok; cases hok
            | ok _ =>
              rw [h1] at hok; dsimp only at hok
              cases h2 : Ix.Kernel.checkRoleTerm (m := Ix.Kernel.CheckM .anon) envA (List.range levels) expectedTy with
              | error _ => rw [h2] at hok; cases hok
              | ok _ =>
                rw [h2] at hok; dsimp only at hok
                cases h3 : (Ix.Kernel.fueledOps .verified F).annotate envA 0
                    (Ix.Kernel.Expr.instLevelParams cvR.levelParams ((List.range levels).map .param) cvR.type) with
                | error _ => rw [h3] at hok; cases hok
                | ok actTy =>
                  rw [h3] at hok; dsimp only at hok
                  cases h4 : (Ix.Kernel.fueledOps .verified F).annotate envA 0 expectedTy with
                  | error _ => rw [h4] at hok; cases hok
                  | ok expTy =>
                    rw [h4] at hok; dsimp only at hok
                    cases h5 : (Ix.Kernel.fueledOps .verified F).isDefEq envA 0 actTy expTy with
                    | error _ => rw [h5] at hok; cases hok
                    | ok bde =>
                      rw [h5] at hok; dsimp only at hok
                      cases bde with
                      | false => cases hok
                      | true =>
                        cases hlen_eq : ((ev.of r).length == equations.length) with
                        | false =>
                          rw [hlen_eq] at hok
                          simp [pure, Except.pure, throw, throwThe,
                            MonadExcept.throw, MonadExceptOf.throw, Bind.bind, Except.bind] at hok
                        | true =>
                          rw [hlen_eq] at hok
                          simp only [Bool.not_true, Bool.false_eq_true, eq_self, ↓reduceIte,
                            pure, Except.pure, Bind.bind, Except.bind] at hok
                          split at hok
                          · cases hok
                          · next vfor hfor =>
                            obtain ⟨_, hstep_eq⟩ := list_forIn_step_mem _
                              (fun p r hr => by
                                split at hr
                                · cases hr
                                · injection hr with hr'; exact hr'.symm)
                              hfor (eq, Ix.Kernel.Evidence.proof (key, val))
                              (mem_zip_of_getElem? heqi hev)
                            try dsimp only at hstep_eq
                            cases hrow : Ix.Kernel.checkRoleEquation
                                (Ix.Kernel.fueledOps .verified F) envA levels eq (.proof (key, val)) with
                            | error _ => rw [hrow] at hstep_eq; cases hstep_eq
                            | ok urow =>
                              cases urow
                              unfold Ix.Kernel.checkRoleEquation at hrow
                              dsimp only [Bind.bind, Except.bind, pure, Except.pure] at hrow
                              cases hc1 : Ix.Kernel.checkRoleTerm (m := Ix.Kernel.CheckM .anon) envA (List.range levels) eq.statement with
                              | error _ => rw [hc1] at hrow; cases hrow
                              | ok _ =>
                                rw [hc1] at hrow; try dsimp only at hrow
                                cases hc2 : Ix.Kernel.annotateCore .verified envA F 0 eq.statement with
                                | error _ =>
                                  change (Ix.Kernel.fueledOps .verified F).annotate envA 0 eq.statement = _ at hc2
                                  rw [hc2] at hrow; cases hrow
                                | ok stmtA =>
                                  have hc2' : (Ix.Kernel.fueledOps .verified F).annotate envA 0 eq.statement = .ok stmtA := hc2
                                  rw [hc2'] at hrow; try dsimp only at hrow
                                  cases hc3 : (Ix.Kernel.fueledOps .verified F).inferType envA 0 stmtA with
                                  | error _ => rw [hc3] at hrow; cases hrow
                                  | ok stTy =>
                                    rw [hc3] at hrow; try dsimp only at hrow
                                    cases hc4 : (Ix.Kernel.fueledOps .verified F).ensureSort envA 0 stTy with
                                    | error _ => rw [hc4] at hrow; cases hrow
                                    | ok _ =>
                                      rw [hc4] at hrow; try dsimp only at hrow
                                      cases hfK : envA.find? key with
                                      | none =>
                                        rw [hfK] at hrow
                                        simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hrow
                                      | some ciA =>
                                        rw [hfK] at hrow; try dsimp only at hrow
                                        cases ciA with
                                        | axiomInfo _ | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _ | projInfo _ =>
                                          simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hrow
                                        | thmInfo cvA tval =>
                                          try dsimp only at hrow
                                          cases hlps : (cvA.levelParams.length == levels && cvA.levelParams.eraseDups == cvA.levelParams) with
                                          | false =>
                                            rw [hlps] at hrow
                                            simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hrow
                                          | true =>
                                            rw [hlps] at hrow
                                            simp only [Bool.not_true, Bool.false_eq_true, eq_self, ↓reduceIte] at hrow
                                            try dsimp only at hrow
                                            cases hc5 : Ix.Kernel.checkRoleTerm (m := Ix.Kernel.CheckM .anon) envA cvA.levelParams cvA.type with
                                            | error _ => rw [hc5] at hrow; cases hrow
                                            | ok _ =>
                                              rw [hc5] at hrow; try dsimp only at hrow
                                              cases hc6 : Ix.Kernel.checkRoleTerm (m := Ix.Kernel.CheckM .anon) envA cvA.levelParams val with
                                              | error _ => rw [hc6] at hrow; cases hrow
                                              | ok _ =>
                                                rw [hc6] at hrow; try dsimp only at hrow
                                                cases hc7 : Ix.Kernel.annotateCore .verified envA F 0
                                                    (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type) with
                                                | error _ =>
                                                  change (Ix.Kernel.fueledOps .verified F).annotate envA 0 _ = _ at hc7
                                                  rw [hc7] at hrow; cases hrow
                                                | ok thmTyA =>
                                                  have hc7' : (Ix.Kernel.fueledOps .verified F).annotate envA 0
                                                      (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type) = .ok thmTyA := hc7
                                                  rw [hc7'] at hrow; try dsimp only at hrow
                                                  cases hc8 : Ix.Kernel.isDefEqCore .verified envA F 0 thmTyA stmtA with
                                                  | error _ =>
                                                    change (Ix.Kernel.fueledOps .verified F).isDefEq envA 0 thmTyA stmtA = _ at hc8
                                                    rw [hc8] at hrow; cases hrow
                                                  | ok bthm =>
                                                    have hc8' : (Ix.Kernel.fueledOps .verified F).isDefEq envA 0 thmTyA stmtA = .ok bthm := hc8
                                                    rw [hc8'] at hrow
                                                    cases bthm with
                                                    | false =>
                                                      simp [Bool.not_false, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hrow
                                                    | true =>
                                                      simp only [Bool.and_eq_true, beq_iff_eq] at hlps
                                                      exact ⟨levels, .thmInfo cvA tval, cvA, thmTyA, stmtA, rfl,
                                                        Or.inl ⟨tval, rfl⟩, hlps.1, hlps.2, hc7, rfl,
                                                        annotateCore_to_annot hc7, annotateCore_to_annot hc2,
                                                        Ix.Kernel.Rules.isDefEqCore_bridge hc8⟩
                                        | defnInfo cvA dval hint =>
                                          cases hint with
                                          | «abbrev» | regular _ =>
                                            simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hrow
                                          | «opaque» =>
                                            try dsimp only at hrow
                                            cases hlps : (cvA.levelParams.length == levels && cvA.levelParams.eraseDups == cvA.levelParams) with
                                            | false =>
                                              rw [hlps] at hrow
                                              simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hrow
                                            | true =>
                                              rw [hlps] at hrow
                                              simp only [Bool.not_true, Bool.false_eq_true, eq_self, ↓reduceIte] at hrow
                                              try dsimp only at hrow
                                              cases hc5 : Ix.Kernel.checkRoleTerm (m := Ix.Kernel.CheckM .anon) envA cvA.levelParams cvA.type with
                                              | error _ => rw [hc5] at hrow; cases hrow
                                              | ok _ =>
                                                rw [hc5] at hrow; try dsimp only at hrow
                                                cases hc6 : Ix.Kernel.checkRoleTerm (m := Ix.Kernel.CheckM .anon) envA cvA.levelParams val with
                                                | error _ => rw [hc6] at hrow; cases hrow
                                                | ok _ =>
                                                  rw [hc6] at hrow; try dsimp only at hrow
                                                  cases hc7 : Ix.Kernel.annotateCore .verified envA F 0
                                                      (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type) with
                                                  | error _ =>
                                                    change (Ix.Kernel.fueledOps .verified F).annotate envA 0 _ = _ at hc7
                                                    rw [hc7] at hrow; cases hrow
                                                  | ok thmTyA =>
                                                    have hc7' : (Ix.Kernel.fueledOps .verified F).annotate envA 0
                                                        (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type) = .ok thmTyA := hc7
                                                    rw [hc7'] at hrow; try dsimp only at hrow
                                                    cases hc8 : Ix.Kernel.isDefEqCore .verified envA F 0 thmTyA stmtA with
                                                    | error _ =>
                                                      change (Ix.Kernel.fueledOps .verified F).isDefEq envA 0 thmTyA stmtA = _ at hc8
                                                      rw [hc8] at hrow; cases hrow
                                                    | ok bthm =>
                                                      have hc8' : (Ix.Kernel.fueledOps .verified F).isDefEq envA 0 thmTyA stmtA = .ok bthm := hc8
                                                      rw [hc8'] at hrow
                                                      cases bthm with
                                                      | false =>
                                                        simp [Bool.not_false, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at hrow
                                                      | true =>
                                                        simp only [Bool.and_eq_true, beq_iff_eq] at hlps
                                                        exact ⟨levels, .defnInfo cvA dval .opaque, cvA, thmTyA, stmtA, rfl,
                                                          Or.inr ⟨dval, rfl⟩, hlps.1, hlps.2, hc7, rfl,
                                                          annotateCore_to_annot hc7, annotateCore_to_annot hc2,
                                                          Ix.Kernel.Rules.isDefEqCore_bridge hc8⟩
          · cases hok
        | _ => cases hok

/-- Transfer the unpacked `eqnsCheck` proof equation across `ThmSim envA env` into `Rules.DefEq env`. -/
theorem eqnsCheck_proof_thmSim {F : Nat} {envA env : Ix.Kernel.Env .anon}
    (hS : ThmSim envA env)
    {r : Ix.Kernel.Role} {ev : Ix.Kernel.Evidences .anon}
    {i : Nat} {key : KKey} {val stmt : KExpr}
    (hok : Ix.Kernel.eqnsCheck (Ix.Kernel.fueledOps .verified F) envA r ev = .ok ())
    (hev : (ev.of r)[i]? = some (.proof (key, val)))
    (hstmt : roleStatement r i = some stmt) :
    ∃ (levels : Nat) (cvA : Ix.Kernel.ConstantVal .anon) (v theoremTypeA stmtA : KExpr),
      (env.find? key = some (.thmInfo cvA v) ∨ env.find? key = some (.defnInfo cvA v .opaque)) ∧
      cvA.levelParams.length = levels ∧
      cvA.levelParams.eraseDups = cvA.levelParams ∧
      Ix.Kernel.Rules.Annot 0
        (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type)
        theoremTypeA ∧
      Ix.Kernel.Rules.Annot 0 stmt stmtA ∧
      Ix.Kernel.Rules.DefEq env 0 theoremTypeA stmtA := by
  obtain ⟨levels, ciA, cvA, thmTyA, stmtA, hfK, hkind, hlen, hnodup, _, _, hannT, hannS, hdeA⟩ :=
    eqnsCheck_proof_inv hok hev hstmt
  have hde := hS.defEq hdeA
  rcases hkind with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨levels, cvA, v, thmTyA, stmtA,
      Or.inl (hS.find_nonDefn hfK (fun _ _ heq => nomatch heq)),
      hlen, hnodup, hannT, hannS, hde⟩
  · rcases hS.find_sim hfK with hf' | ⟨cv', v', heq, _, _, _, _, hf'⟩
    · exact ⟨levels, cvA, v, thmTyA, stmtA, Or.inr hf', hlen, hnodup, hannT, hannS, hde⟩
    · injection heq with hcv hv _
      subst hcv hv
      exact ⟨levels, cvA, v, thmTyA, stmtA, Or.inl hf', hlen, hnodup, hannT, hannS, hde⟩

/-- Discharge `EnvFacts.evidence` from `ThmSim envA c.env`, `BindingSpecs`'s `eqnsCheck`,
theorem storage at `c.κ a`, and endpoint conversion alignment for `cv.type` and `stmt`. -/
theorem evidence_of_thmSim {c : Ctx} {envA : Ix.Kernel.Env .anon}
    {ev_eqns : Ix.Kernel.Evidences .anon}
    (hS : ThmSim envA c.env)
    (heqns : ∀ r, c.t.addressOf? r ≠ none → (r.spec (md := .anon)).kind = .eqns →
      ∃ F, Ix.Kernel.eqnsCheck (Ix.Kernel.fueledOps .verified F) envA r ev_eqns = .ok ())
    (hev_lookup : ∀ r es (i : Nat) a, c.inForce r → (r, es) ∈ c.t.evidence.toList →
      es[i]? = some (Ix.Kernel.Evidence.proof a) →
      ∃ val, (ev_eqns.of r)[i]? = some (Ix.Kernel.Evidence.proof (c.κ a, val)))
    (hthm_stored : ∀ r es (i : Nat) a cvA v,
      c.inForce r → (r, es) ∈ c.t.evidence.toList → es[i]? = some (Ix.Kernel.Evidence.proof a) →
      (c.env.find? (c.κ a) = some (.thmInfo cvA v) ∨
        c.env.find? (c.κ a) = some (.defnInfo cvA v .opaque)) →
      ∃ v', c.env.find? (c.κ a) = some (.thmInfo cvA v'))
    (halign : ∀ r (i : Nat) (a : _root_.Address) levels cvA v theoremTypeA stmt stmtA,
      c.inForce r → roleStatement r i = some stmt →
      c.env.find? (c.κ a) = some (.thmInfo cvA v) →
      cvA.levelParams.length = levels →
      Ix.Kernel.Rules.Annot 0
        (Ix.Kernel.Expr.instLevelParams cvA.levelParams ((List.range levels).map .param) cvA.type)
        theoremTypeA →
      Ix.Kernel.Rules.Annot 0 stmt stmtA →
      Ix.Kernel.Rules.DefEq c.env 0 theoremTypeA stmtA →
      Ix.Kernel.Rules.DefEq c.env 0 cvA.type stmt) :
    ∀ r es (i : Nat) a, c.inForce r → (r, es) ∈ c.t.evidence.toList →
      es[i]? = some (Ix.Kernel.Evidence.proof a) →
      ∀ stmt, roleStatement r i = some stmt →
        ∃ cv v, c.env.find? (c.κ a) = some (.thmInfo cv v) ∧
          Ix.Kernel.Rules.DefEq c.env 0 cv.type stmt := by
  intro r es i a hinf hmem hes stmt hstmt
  have haddr : c.t.addressOf? r ≠ none := Option.isSome_iff_ne_none.mp hinf.1
  have hkind : (r.spec (md := .anon)).kind = .eqns := by
    unfold roleStatement at hstmt
    cases hs : Ix.Kernel.Role.spec (md := .anon) r with
    | eqns _ _ _ => simp [Ix.Kernel.Spec.kind]
    | _ => rw [hs] at hstmt; cases hstmt
  obtain ⟨F, hok⟩ := heqns r haddr hkind
  obtain ⟨val, hev⟩ := hev_lookup r es i a hinf hmem hes
  obtain ⟨levels, cvA, v₀, thmTyA, stmtA, hfind_or, hlen, _, hannT, hannS, hde⟩ :=
    eqnsCheck_proof_thmSim hS hok hev hstmt
  obtain ⟨v, hf_thm⟩ := hthm_stored r es i a cvA v₀ hinf hmem hes hfind_or
  exact ⟨cvA, v, hf_thm, halign r i a levels cvA v thmTyA stmt stmtA hinf hstmt hf_thm hlen hannT hannS hde⟩

end IxVM.Refinement.Assembly
