import IxVMRefinement.Binding.RenderedArms
import IxVMRefinement.Binding.AxiomInstall
import IxVMRefinement.Assembly.NativeBlockFormer

/-! # The pinned type of a bound role

A role validation compares the bound record's loaded type with the role's specified type:
`assert_type_pinned(ty, role_type(tbl, r))` asserts `kexpr_struct_eq(ty, spec) = 1`
(`KernelRoles.lean:781`; called by `validate_member`, `validate_anchor`,
`validate_standard_axiom`, `validate_inert_axiom`, `validate_op`). `Decl.kexpr_struct_eq_one`
turns that answer into equality of the two terms when both pointers represent their terms
exactly under one keying. `role_type` builds, exactly under the table's keying, a term that is
the specified type up to binder data (`roleTypeRenders`). This file supplies the other side,
the loaded type exactly under the table's keying, and the forms the users read the pin in.

* `typePinned_erasePw`: **the pin.** A pointer that represents `E` exactly under the table's
  keying, found structurally equal to `role_type(tbl, r)`, has `E.erasePw = T₀.erasePw` for the
  role's specified type `T₀`.
* `specLevels`, `role_levels_spec`: `role_levels(r)` is the specified level count;
  `const_num_lvls_exact`, `const_type_of_exact`, `levels_pinned`: the level count and the type
  field of a loaded constant, read off its exact representation, so that
  `const_num_lvls(ci) == role_levels(r)` fixes the stored level parameters.
* `LoadedReads.get_ci_defn_canon_exact`, `LoadedReads.get_ci_axio_canon_exact`: the exact
  variants of `get_ci_defn_canon` and `get_ci_axio_canon` (through `annotation_canon_exact`):
  the loaded constant is the canonical one, represented exactly under the table's keying.
* `annotates_erasePw_eq`: two annotations of one term are equal up to binder data, so a stored
  constant and the loaded one, both annotating one reading, agree on the pin.
* The users' forms: `anchorPin_spec` with `matchesPin_of_fields` (an anchor's stored type
  matches `anchorPin?`), `stdAxiom_matchesPin` (a standard axiom matches the kernel's pin), and
  `opTyShape_of_erasePw` (an operation's stored type has `RoleOps.OpTyShape`).
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-! ## The exact variants of the canonical loads -/

/-- A level count and an exactly represented type are an exactly represented constant value. -/
theorem valRepExact_range {κ : _root_.Address → Core.KKey} {h : Heap F} {n : Nat}
    {tyPtr : SourceValue F} {key : Ix.Kernel.Key .anon} {ty' : Ix.Kernel.Expr .anon}
    (hn : n < 4294967296) (hty : Decl.TmCExact κ h (Core.posOf (List.range n) ty') tyPtr) :
    Decl.ValRepExact κ h (.field (n : F)) tyPtr ⟨key, List.range n, ty'⟩ := by
  have hlen : n = (List.range n).length := by simp
  exact ⟨congrArg (fun m : Nat => Value.field (m : F)) hlen, by simpa using hn, by simp, hty⟩

/-- **A converted definition value represents, exactly, a constant whose type and value its
two heap terms represent exactly**, under any keying and every hint. -/
theorem ciRepExact_defnValShape {κ : _root_.Address → Core.KKey} {h : Heap F}
    {d : Ixon.Definition} {tyPtr valPtr hint : SourceValue F} {key : Ix.Kernel.Key .anon}
    {ty' val' : Ix.Kernel.Expr .anon} (hnlvls : d.lvls.toNat < 4294967296)
    (hty : Decl.TmCExact κ h (Core.posOf (List.range d.lvls.toNat) ty') tyPtr)
    (hval : Decl.TmCExact κ h (Core.posOf (List.range d.lvls.toNat) val') valPtr)
    (hn : Ix.Kernel.ReducibilityHint) :
    Decl.CIRepExact κ h (L1.defnValShape d tyPtr valPtr hint)
      (defnConst d.kind ⟨key, List.range d.lvls.toNat, ty'⟩ val' hn) := by
  have hvr : Decl.ValRepExact κ h (.field (d.lvls.toNat : F)) tyPtr
      ⟨key, List.range d.lvls.toNat, ty'⟩ := valRepExact_range hnlvls hty
  cases hk : d.kind with
  | defn =>
    simp only [L1.defnValShape, hk]
    exact .defn hvr hval
  | thm =>
    simp only [L1.defnValShape, hk]
    exact .thm hvr hval
  | opaq =>
    simp only [L1.defnValShape, hk]
    exact .opaq hvr hval

section Exact

variable {t : Ix.Kernel.RoleTable}

/-- **`get_ci_defn_canon`, exactly**: a load of a held standalone definition, theorem or opaque
record, in calls that hash no collision with the store, returns a pointer that represents the
canonical constant exactly under the table's keying, under every hint. -/
theorem get_ci_defn_canon_exact (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {d : Ixon.Definition} (hrec : recordOf E (Core.ixAddr a) = some c)
    (hinfo : c.info = .defn d) (hlogic : InLogic c) {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id
      (soloSelf t (Core.ixAddr a))).read d.typ = .ok ty₀)
    (hval : (exprReader t (fun x => E.blobs.get? x) c id
      (soloSelf t (Core.ixAddr a))).read d.value = .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true) :
    ∃ ty' val' : Ix.Kernel.Expr .anon,
      canonAnn c (List.range d.lvls.toNat) 0 d.typ ty₀ = some ty' ∧
      canonAnn c (List.range d.lvls.toNat) (0 + 1) d.value val₀ = some val' ∧
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint, Decl.CIPtrRepExact (Core.keyOf t) h' ptr
        (defnConst d.kind ⟨keyOf t (Core.ixAddr a), List.range d.lvls.toNat, ty'⟩ val' hn) := by
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
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon_exact (recurAddrs := []) ht hnlvls (fun _ _ _ _ hx => by simp at hx) hagree
      rty built hpT hlT hty hty_lbb hty_def
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    annotation_canon_exact (recurAddrs := []) ht hnlvls (fun _ _ _ _ hx => by simp at hx) hagree
      rval built hpV hlV hval hval_lbb hval_def
  exact ⟨ty', val', hcT, hcV, hannT, hannV,
    fun hn => ⟨_, hld, ciRepExact_defnValShape hnlvls htmT htmV hn⟩⟩

/-- **`get_ci_axio_canon`, exactly**: a load of a held axiom record, in calls that hash no
collision with the store, returns a pointer that represents the axiom with the canonical
annotation of its read type exactly under the table's keying. -/
theorem get_ci_axio_canon_exact (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {ax : Ixon.Axiom} (hrec : recordOf E (Core.ixAddr a) = some c)
    (hinfo : c.info = .axio ax) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id (fun _ => none)).read ax.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ax.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn c (List.range ax.lvls.toNat) 0 ax.typ ty₀ = some ty' ∧ Annotates ty' ty₀ ∧
      Decl.CIPtrRepExact (Core.keyOf t) h' ptr
        (.axiomInfo ⟨keyOf t (Core.ixAddr a), List.range ax.lvls.toNat, ty'⟩) := by
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
  obtain ⟨hnlvls, tyPtr, plan, hv, rty, hp, hl⟩ := htr
  subst hv
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon_exact (recurAddrs := []) ht hnlvls (fun _ _ _ _ hx => by simp at hx) hagree
      rty built hp hl hty hty_lbb hty_def
  exact ⟨ty', hcT, hannT, _, hld, .axio (valRepExact_range hnlvls htmT)⟩

end Exact

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)

/-! ## The pin -/

/-- **The pin.** At a well-formed table, a pointer `typ` that represents `E` exactly under the
table's keying, which `assert_type_pinned` accepts against `role_type(tbl, r)`, has the role's
specified type up to binder data: `E.erasePw = T₀.erasePw`. -/
theorem typePinned_erasePw {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {r : Role}
    {T₀ : KExpr} (hT : specTypeRaw r = some T₀) {x_tbl typ spec u : SourceValue F}
    {h₀ h₁ h₂ : Heap F} {cs₁ cs₂ : List (Call F)} {E : KExpr}
    (htbl : TableRep t h₀ x_tbl) (hE : Decl.TmCExact (keyOf t) h₀ E typ)
    (evT : ObsFn W "KernelRoleSpec::role_type" [x_tbl, .field (roleNum r)] h₀ spec h₁ cs₁)
    (evP : ObsFn W "KernelRoles::assert_type_pinned" [typ, spec] h₁ u h₂ cs₂) :
    E.erasePw = T₀.erasePw := by
  obtain ⟨ext, T, hTrep, hTe⟩ := roleTypeRenders t r T₀ hT htwf htbl evT
  obtain ⟨v12, m15, cs23, ev25, heq48, -, -, -⟩ := Obs.«KernelRoles::assert_type_pinned».obs evP
  subst heq48
  have e := Decl.kexpr_struct_eq_one ((hE.mono ext) 0 (fun _ => .sort .zero))
    (hTrep 0 (fun _ => .sort .zero)) ev25
  rw [e]
  exact hTe

/-! ## The level count -/

/-- **The level count the specification set declares for a role**, where it declares one. -/
def specLevels (r : Role) : Option Nat := (specDecl r).map fun d => d.1.length

/-- Every arm of `role_levels` at a role with a specified level count returns that count, and
the counts are below `8`. -/
def roleLevelsTable : Bool :=
  Role.all.all fun r =>
    match specLevels r with
    | none => true
    | some n => decide (n < 8) &&
      RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_levels.body)
        (roleNum r) == some (n : F)

set_option maxRecDepth 1000000 in
theorem roleLevelsTable_true : roleLevelsTable = true := by decide +kernel

/-- **`KernelRoleSpec::role_levels(r)` returns the specified level count**, without
allocating. -/
theorem role_levels_spec {r : Role} {n : Nat} (hn : specLevels r = some n)
    {v : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::role_levels" [.field (roleNum r)] h v h' cs) :
    v = .field (n : F) ∧ h' = h ∧ n < 8 := by
  have hall : (match specLevels r with
      | none => true
      | some n => decide (n < 8) &&
        RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_levels.body)
          (roleNum r) == some (n : F)) = true :=
    List.all_eq_true.mp roleLevelsTable_true r (Role.mem_all r)
  simp only [hn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
  obtain ⟨hlt, htab⟩ := hall
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_levels.lookup
    (by simp [IxVM.KernelRoleSpec.role_levels, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.role_levels.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_levels.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_levels.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨v1, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable htab sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl, hlt⟩

/-! ## The fields of a loaded constant -/

/-- **A loaded constant's level count and type are its first two fields**, exactly represented. -/
theorem ciRepExact_typeField {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (hci : Decl.CIRepExact κ h v ci) :
    ∃ (tag : String) (nl ty : SourceValue F) (rest : List (SourceValue F)),
      v = .construct kciEnum tag (nl :: ty :: rest) ∧
        Decl.ValRepExact κ h nl ty ci.toConstantVal := by
  cases hci with
  | axio hv => exact ⟨_, _, _, _, rfl, hv⟩
  | opaq hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | defn hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | thm hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | quot hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | induct hv _ _ => exact ⟨_, _, _, _, rfl, hv⟩
  | ctor hv _ _ _ _ => exact ⟨_, _, _, _, rfl, hv⟩
  | recr hv _ _ _ _ _ _ _ _ _ _ => exact ⟨_, _, _, _, rfl, hv⟩

/-- **`KernelInfer::const_num_lvls` on an exactly represented constant** returns its level
count. -/
theorem const_num_lvls_exact {κ : _root_.Address → KKey} {h₀ h h' : Heap F}
    {v r : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon} {cs : List (Call F)}
    (hci : Decl.CIRepExact κ h₀ v ci)
    (ev : ObsFn W "KernelInfer::const_num_lvls" [v] h r h' cs) :
    r = .field (ci.toConstantVal.levelParams.length : F) ∧ h' = h := by
  obtain ⟨tag, nl, ty, rest, hvv, hval⟩ := ciRepExact_typeField hci
  rcases Obs.«KernelInfer::const_num_lvls».obs ev with
    ⟨x_n, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals
    rw [hvv] at hv
    have hl := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq] at hl
    exact ⟨he.trans (hl.1.symm.trans hval.1), hh⟩

/-- **`KernelInfer::const_type_of` on an exactly represented constant** returns a pointer that
represents its type exactly. -/
theorem const_type_of_exact {κ : _root_.Address → KKey} {h h' : Heap F}
    {v r : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon} {cs : List (Call F)}
    (hci : Decl.CIRepExact κ h v ci)
    (ev : ObsFn W "KernelInfer::const_type_of" [v] h r h' cs) :
    h' = h ∧ Decl.TmCExact κ h
      (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) r := by
  obtain ⟨tag, nl, ty, rest, hvv, hval⟩ := ciRepExact_typeField hci
  rcases Obs.«KernelInfer::const_type_of».obs ev with
    ⟨_, x_ty, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals
    rw [hvv] at hv
    have hl := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq] at hl
    refine ⟨hh, ?_⟩
    rw [he, ← hl.2.1]
    exact hval.2.2.2

/-- **`const_num_lvls(ci) == role_levels(r)` fixes the level count**: the loaded constant has
the role's specified number of level parameters. -/
theorem levels_pinned {κ : _root_.Address → KKey} {r : Role} {n : Nat}
    (hn : specLevels r = some n) {v v₁ v₂ : SourceValue F} {h₀ h₁ h₂ h₃ : Heap F}
    {ci : Ix.Kernel.ConstantInfo .anon} {cs₁ cs₂ : List (Call F)}
    (hci : Decl.CIRepExact κ h₀ v ci)
    (ev₁ : ObsFn W "KernelInfer::const_num_lvls" [v] h₁ v₁ h₂ cs₁)
    (ev₂ : ObsFn W "KernelRoleSpec::role_levels" [.field (roleNum r)] h₂ v₂ h₃ cs₂)
    (he : v₁ = v₂) :
    ci.toConstantVal.levelParams.length = n := by
  obtain ⟨e₁, -⟩ := const_num_lvls_exact hci ev₁
  obtain ⟨e₂, -, hlt⟩ := role_levels_spec hn ev₂
  have hlen : ci.toConstantVal.levelParams.length < 4294967296 := by
    obtain ⟨_, _, _, _, -, hv⟩ := ciRepExact_typeField hci
    exact hv.2.1
  have hf : ((ci.toConstantVal.levelParams.length : Nat) : F) = ((n : Nat) : F) :=
    Value.field.inj (e₁.symm.trans (he.trans e₂))
  have hv := congrArg ZMod.val hf
  rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hv
  exact hv

/-! ## Annotations of one term -/

private theorem bm_never_eq (m₁ m₂ : Ix.Kernel.BinderMeta) :
    ({ m₁ with pw := .never } : Ix.Kernel.BinderMeta) = { m₂ with pw := .never } := by
  show Ix.Kernel.BinderMeta.mk .never m₁.display = Ix.Kernel.BinderMeta.mk .never m₂.display
  rw [Subsingleton.elim m₁.display m₂.display]

/-- **Two annotations of one term are equal up to binder data.** -/
theorem annotates_erasePw_eq {e₁ e₀ : KExpr} (h₁ : IxVM.Consistency.Annotates e₁ e₀) :
    ∀ {e₂ : KExpr}, IxVM.Consistency.Annotates e₂ e₀ → e₁.erasePw = e₂.erasePw := by
  induction h₁ with
  | bvar => intro e₂ h₂; cases h₂; rfl
  | fvar _ ih =>
    intro e₂ h₂
    cases h₂ with
    | fvar h => simp only [Ix.Kernel.Expr.erasePw, ih h]
  | sort => intro e₂ h₂; cases h₂; rfl
  | const => intro e₂ h₂; cases h₂; rfl
  | lit => intro e₂ h₂; cases h₂; rfl
  | app _ _ ihf iha =>
    intro e₂ h₂
    cases h₂ with
    | app hf ha => simp only [Ix.Kernel.Expr.erasePw, ihf hf, iha ha]
  | lam _ _ iht ihb =>
    intro e₂ h₂
    cases h₂ with
    | lam ht hb =>
      simp only [Ix.Kernel.Expr.erasePw]
      rw [iht ht, ihb hb]
      exact congrArg (Ix.Kernel.Expr.lam _ _) (bm_never_eq _ _)
  | forallE _ _ iht ihb =>
    intro e₂ h₂
    cases h₂ with
    | forallE ht hb =>
      simp only [Ix.Kernel.Expr.erasePw]
      rw [iht ht, ihb hb]
      exact congrArg (Ix.Kernel.Expr.forallE _ _) (bm_never_eq _ _)
  | proj _ ih =>
    intro e₂ h₂
    cases h₂ with
    | proj h => simp only [Ix.Kernel.Expr.erasePw, ih h]
  | letE _ ih =>
    intro e₂ h₂
    cases h₂ with
    | letE h => exact ih h

/-! ## The users' forms -/

/-- A constant value matches a pin when its name, level parameters and type up to binder data
are the pin's. -/
theorem matchesPin_of_fields {cv pin : Ix.Kernel.ConstantVal .anon} (hn : cv.name = pin.name)
    (hl : cv.levelParams = pin.levelParams) (he : cv.type.erasePw = pin.type.erasePw) :
    cv.matchesPin pin = true := by
  unfold Ix.Kernel.ConstantVal.matchesPin
  simp [hn, hl, he]

/-- **An anchor's pin is its specification**: the specified type and level count of a role
whose `anchorPin?` is `pin` are the pin's, and the pin names its level parameters by position
and is at the role's key. -/
theorem anchorPin_spec {r : Role} {pin : Ix.Kernel.ConstantVal .anon}
    (hp : anchorPin? (.role r) = some pin) :
    specTypeRaw r = some pin.type ∧ specLevels r = some pin.levelParams.length ∧
      pin.levelParams = List.range pin.levelParams.length ∧ pin.name = .role r := by
  have hp' : (match (Ix.Kernel.Role.spec (md := .anon)) r with
      | .anchor n ty => some ({ name := .role r, levelParams := List.range n, type := ty } :
          Ix.Kernel.ConstantVal .anon)
      | _ => none) = some pin := hp
  have hd : ∀ n ty, (Ix.Kernel.Role.spec (md := .anon)) r = .anchor n ty →
      specDecl r = some (List.range n, ty) := by
    intro n ty hs
    simp only [specDecl, hs]
  generalize hs : (Ix.Kernel.Role.spec (md := .anon)) r = s at hp'
  cases s with
  | anchor n ty =>
    simp only [Option.some.injEq] at hp'
    subst hp'
    have hd' := hd n ty hs
    refine ⟨?_, ?_, by simp, rfl⟩
    · rw [specTypeRaw, hd']
      exact congrArg some (Decl.posOf_range n ty)
    · rw [specLevels, hd']
      simp
  | _ => simp at hp'

set_option maxRecDepth 100000 in
/-- The two standard axioms' kernel pins are their specifications, up to binder data. -/
theorem stdAxiomPin_spec :
    (specTypeRaw .propext).map Ix.Kernel.Expr.erasePw =
        some (AxiomInstall.stdAxiomPin .propext).type.erasePw ∧
      specLevels .propext = some (AxiomInstall.stdAxiomPin .propext).levelParams.length ∧
      (AxiomInstall.stdAxiomPin .propext).levelParams =
        List.range (AxiomInstall.stdAxiomPin .propext).levelParams.length ∧
      (AxiomInstall.stdAxiomPin .propext).name = .role .propext ∧
    (specTypeRaw .choice).map Ix.Kernel.Expr.erasePw =
        some (AxiomInstall.stdAxiomPin .choice).type.erasePw ∧
      specLevels .choice = some (AxiomInstall.stdAxiomPin .choice).levelParams.length ∧
      (AxiomInstall.stdAxiomPin .choice).levelParams =
        List.range (AxiomInstall.stdAxiomPin .choice).levelParams.length ∧
      (AxiomInstall.stdAxiomPin .choice).name = .role .choice := by
  decide +kernel

/-- **A standard axiom's pinned type matches the kernel's pin**: a type equal up to binder data
to the specified type, with the specified level count, at the axiom's key. -/
theorem stdAxiom_matchesPin {r : Role} (hr : r ∈ IxVM.Consistency.standardAxioms)
    {T₀ ty : KExpr} {n : Nat}
    (hT : specTypeRaw r = some T₀) (hn : specLevels r = some n) (he : ty.erasePw = T₀.erasePw) :
    Ix.Kernel.ConstantVal.matchesPin ⟨.role r, List.range n, ty⟩ (AxiomInstall.stdAxiomPin r) =
      true := by
  obtain ⟨p1, p2, p3, p4, c1, c2, c3, c4⟩ := stdAxiomPin_spec
  rcases AxiomInstall.std_cases hr with rfl | rfl
  · have e1 : T₀.erasePw = (AxiomInstall.stdAxiomPin .propext).type.erasePw := by
      simpa [hT] using p1
    have hn' : n = (AxiomInstall.stdAxiomPin .propext).levelParams.length := by
      simpa [hn] using p2
    refine matchesPin_of_fields p4.symm ?_ (he.trans e1)
    show List.range n = _
    rw [p3, ← hn']
  · have e1 : T₀.erasePw = (AxiomInstall.stdAxiomPin .choice).type.erasePw := by
      simpa [hT] using c1
    have hn' : n = (AxiomInstall.stdAxiomPin .choice).levelParams.length := by
      simpa [hn] using c2
    refine matchesPin_of_fields c4.symm ?_ (he.trans e1)
    show List.range n = _
    rw [c3, ← hn']

/-- **The type an operation is pinned to**: `Nat → Nat` for `Nat.pred`, `Nat → Nat → Bool` for
the comparisons, `Nat → Nat → Nat` otherwise (`RoleOps.OpTyShape`'s shapes). -/
def opShapeE (c : KKey) : KExpr :=
  if c = Ix.Kernel.natPredName then
    .forallE (.const Ix.Kernel.natName []) (.const Ix.Kernel.natName []) default
  else
    .forallE (.const Ix.Kernel.natName [])
      (.forallE (.const Ix.Kernel.natName []) (.const (RoleOps.opCod c) []) default) default

set_option maxRecDepth 100000 in
/-- Every operation is specified at its pinned shape, up to binder data. -/
theorem opShape_spec : ∀ r ∈ RoleOps.opRoles,
    (specTypeRaw r).map Ix.Kernel.Expr.erasePw = some (opShapeE (.role r)).erasePw := by
  decide +kernel

private theorem erasePw_const_inv {e : KExpr} {n : KKey} {us : List KLevel}
    (h : e.erasePw = .const n us) : e = .const n us := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact congrArg₂ Ix.Kernel.Expr.const h.1 h.2

private theorem erasePw_forallE_inv {e d₀ b₀ : KExpr} {m₀ : Ix.Kernel.BinderMeta}
    (h : e.erasePw = .forallE d₀ b₀ m₀) :
    ∃ d b mb, e = .forallE d b mb ∧ d.erasePw = d₀ ∧ b.erasePw = b₀ := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact ⟨_, _, _, rfl, h.1, h.2.1⟩

/-- **A type equal up to binder data to an operation's pinned shape has that shape.** -/
theorem opTyShape_of_erasePw {c : KKey} {ty : KExpr} (he : ty.erasePw = (opShapeE c).erasePw) :
    RoleOps.OpTyShape c ty := by
  unfold RoleOps.OpTyShape
  unfold opShapeE at he
  by_cases hc : c = Ix.Kernel.natPredName
  · simp only [hc, ↓reduceIte] at he ⊢
    simp only [Ix.Kernel.Expr.erasePw] at he
    obtain ⟨d, b, mb, rfl, hd, hb⟩ := erasePw_forallE_inv he
    rw [erasePw_const_inv hd, erasePw_const_inv hb]
    exact ⟨mb, rfl⟩
  · simp only [hc, ↓reduceIte] at he ⊢
    simp only [Ix.Kernel.Expr.erasePw] at he
    obtain ⟨d₁, b₁, mb₁, rfl, hd₁, hb₁⟩ := erasePw_forallE_inv he
    obtain ⟨d₂, b₂, mb₂, rfl, hd₂, hb₂⟩ := erasePw_forallE_inv hb₁
    rw [erasePw_const_inv hd₁, erasePw_const_inv hd₂, erasePw_const_inv hb₂]
    exact ⟨mb₁, mb₂, rfl⟩

/-- **An operation's pinned type has the operation's shape.** -/
theorem opTyShape_of_pinned {r : Role} (hr : r ∈ RoleOps.opRoles) {T₀ ty : KExpr}
    (hT : specTypeRaw r = some T₀) (he : ty.erasePw = T₀.erasePw) :
    RoleOps.OpTyShape (.role r) ty := by
  have hs := opShape_spec r hr
  have e1 : T₀.erasePw = (opShapeE (.role r)).erasePw := by simpa [hT] using hs
  exact opTyShape_of_erasePw (he.trans e1)

end IxVM.Refinement.Binding
