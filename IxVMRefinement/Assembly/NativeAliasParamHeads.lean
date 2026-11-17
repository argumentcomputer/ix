import IxVMRefinement.Subst.Steps
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.KernelCheck1
import IxC.Kernel.Semantics.Inductives.DeclNativeJ

/-! # The actual alias parameter-head checks

The new source check follows only Pi/application heads and substitutes lets. Its observation
produces absence of the family head in the kernel reading. Binder descent uses opened free
variables; a let is substituted only after its value is read at local depth zero. Thus the
existing substitution refinement applies without identifying raw lifting substitution with
unrestricted non-lifting substitution.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (Expr)
open Ix.Kernel.Semantics (famHead)

set_option maxHeartbeats 1600000

private theorem famHead_instantiate_fvar (T : KKey) (d : Nat) (A : KExpr) :
    ∀ (E : KExpr) (k : Nat), famHead T (E.instantiate1 (.fvar d A) k) = famHead T E := by
  intro E
  induction E with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1]
    split <;> first | rfl | (split <;> rfl)
  | forallE ty body bm _ ih =>
    intro k
    exact ih (k + 1)
  | app f a ih _ =>
    intro k
    exact ih k
  | _ => intro k; rfl

private theorem alias_parameter_head_go (κ : _root_.Address → KKey) (T : KKey)
    (target : Bytes.Address) (hinj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = target) :
    ∀ (fuel : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {p pt r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → IxVM.Consistency.Bounded cs → Tm κ d Γ h 0 E p →
      Bytes.RepAddressRef addrTy h target pt →
      ObsFn W "KernelCheck::assert_alias_parameter_head" [p, pt] h r h' cs →
      famHead T E = false := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro d Γ E p pt r h h' cs hlen hbound hE ht ev
    match Obs.«KernelCheck::assert_alias_parameter_head».obs ev with
    | .Forall (cs40 := children) (ld12 := ld) (ev42 := child) (hc59 := hc) .. =>
      obtain ⟨D, B, level, rfl, -, hB, -⟩ := hE.forallE_of_load ld
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
      have hb := hB.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
      have hr := ih children.length hlt (Nat.le_refl _) (bounded_sub hsub hbound) hb ht child
      simpa only [famHead, famHead_instantiate_fvar] using hr
    | .App (cs81 := children) (ld12 := ld) (ev83 := child) (hc100 := hc) .. =>
      obtain ⟨f, a, rfl, hf, -⟩ := hE.app_of_load ld
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
      exact ih children.length hlt (Nat.le_refl _) (bounded_sub hsub hbound) hf ht child
    | .Let (cs127 := children) (cs141 := subCalls) (ld12 := ld) (ev143 := inst)
        (ev129 := child) (hc174 := hc) .. =>
      obtain ⟨D, V, B, rfl, -, hV, hB⟩ := hE.letE_of_load ld
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hisub : ∀ cl ∈ subCalls, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hlt : children.length < fuel := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have hi := SubstAux.gall κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub hisub hbound) d Γ B V (by simpa only [ZMod.val_zero, Nat.zero_add] using hB) hV
      simp only [ZMod.val_zero, Nat.zero_add] at hi
      have hr := ih children.length hlt (Nat.le_refl _) (bounded_sub hsub hbound)
        hi (Bytes.repAddressRef_heapMono₂ addrTy inst.heap_extends ht) child
      rw [instShift_eq_instantiate1 hV.looseBVarsBounded 0 B]
      exact hr
    | .Const (ld12 := ld) (ev217 := eqRun) (heq240 := eqZero) .. =>
      obtain ⟨a, us, rfl, ha, -⟩ := hE.const_of_load ld
      obtain ⟨heq, -⟩ := Lib.address_eq_spec eqRun ha ht
      rw [eqZero] at heq
      have hne : a ≠ target := by
        intro he
        subst he
        simp at heq
      exact beq_eq_false_iff_ne.mpr fun he => hne (hinj a he)
    | .other (ld12 := ld) (hne60 := noPi) (hne101 := noApp)
        (hne175 := noLet) (hne246 := noConst) .. =>
      cases hE with
      | forallE cell _ _ _ =>
        exact (noPi [_, _, _] rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))).elim
      | app cell _ _ =>
        exact (noApp [_, _] rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))).elim
      | letE cell _ _ _ =>
        exact (noLet [_, _, _] rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))).elim
      | const cell _ _ _ =>
        exact (noConst [_, _] rfl (Except.ok.inj (ld.symm.trans (loadValue_enum_cell cell)))).elim
      | _ => rfl

/-- An accepted actual head check excludes the family head from the read expression. -/
theorem alias_parameter_head_spec {κ : _root_.Address → KKey} {T : KKey}
    {target : Bytes.Address} {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
    {p pt r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hinj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = target)
    (hbound : IxVM.Consistency.Bounded cs) (hE : Tm κ d Γ h 0 E p)
    (ht : Bytes.RepAddressRef addrTy h target pt)
    (ev : ObsFn W "KernelCheck::assert_alias_parameter_head" [p, pt] h r h' cs) :
    famHead T E = false :=
  alias_parameter_head_go κ T target hinj cs.length (Nat.le_refl _) hbound hE ht ev

/-- The first `n` parameter domains are not headed by the family. Occurrences elsewhere in a
parameter are permitted. -/
def ParamHeadsFree (T : KKey) : Nat → KExpr → Prop
  | 0, _ => True
  | n + 1, .forallE D B _ => famHead T D = false ∧ ParamHeadsFree T n B
  | _ + 1, _ => False

private theorem paramHeadsFree_of_instantiate_fvar (T : KKey) (d : Nat) (A : KExpr) :
    ∀ (n : Nat) (E : KExpr) (k : Nat),
      ParamHeadsFree T n (E.instantiate1 (.fvar d A) k) → ParamHeadsFree T n E := by
  intro n
  induction n with
  | zero => intro E k _; trivial
  | succ n ih =>
    intro E k hs
    cases E with
    | bvar i =>
      simp only [Expr.instantiate1] at hs
      split at hs <;> first | exact hs | (split at hs <;> exact hs)
    | forallE D B bm =>
      simp only [Expr.instantiate1, ParamHeadsFree, famHead_instantiate_fvar] at hs
      exact ⟨hs.1, ih B (k + 1) hs.2⟩
    | _ => exact hs

private theorem alias_count_succ_ne_zero {n : Nat} (hn : n + 1 < 18446744069414584321) :
    (.field ((n + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
  intro he
  have hv := congrArg ZMod.val (Value.field.inj he)
  rw [ZMod.val_natCast_of_lt hn, ZMod.val_zero] at hv
  omega

private theorem alias_count_pred (n : Nat) {v : SourceValue F}
    (op : evalBinOp .sub (.field ((n + 1 : Nat) : F) : SourceValue F) (.field 1) = .ok v) :
    v = .field (n : F) := by
  simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
    Except.ok.injEq] at op
  rw [← op]
  congr 1
  simp [Nat.cast_add]

/-- The actual parameter-loop check supplies every parameter's head condition. -/
theorem alias_parameter_heads_spec {κ : _root_.Address → KKey} {T : KKey}
    {target : Bytes.Address} (hinj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = target) :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {p pt r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 → IxVM.Consistency.Bounded cs → Tm κ d Γ h 0 E p →
      Bytes.RepAddressRef addrTy h target pt →
      ObsFn W "KernelCheck::assert_alias_parameter_heads" [p, .field (n : F), pt] h r h' cs →
      ParamHeadsFree T n E
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, d, Γ, E, p, pt, r, h, h', cs, hn, hbound, hE, ht, ev => by
    match Obs.«KernelCheck::assert_alias_parameter_heads».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd hv (alias_count_succ_ne_zero hn)
    | .other (cs66 := heads) (cs88 := rest) (ld34 := ld) (ev68 := hcheck)
        (op114 := op) (ev90 := hrest) (hc123 := hc) .. =>
      obtain ⟨D, B, level, rfl, hD, hB, -⟩ := hE.forallE_of_load ld
      have hs : ∀ cl ∈ heads, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hr : ∀ cl ∈ rest, cl ∈ cs := by intro cl hm; rw [hc]; simp [hm]
      have hd := alias_parameter_head_spec hinj (bounded_sub hs hbound) hD ht hcheck
      have hb := (hB.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)).mono
        hcheck.heap_extends
      rw [alias_count_pred n op] at hrest
      have htail := alias_parameter_heads_spec hinj n (by omega) (bounded_sub hr hbound) hb
        (Bytes.repAddressRef_heapMono₂ addrTy hcheck.heap_extends ht) hrest
      exact ⟨hd, paramHeadsFree_of_instantiate_fvar T d D n B 0 htail⟩

/-- The generated parameter predicate supplies the indexed domain facts consumed by the
constructor-zero loop. -/
theorem ParamHeadsFree.domains {T : KKey} :
    ∀ {n : Nat} {E body : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      ParamHeadsFree T n E → E.stripPis n = some (bs, body) →
      ∀ i < n, famHead T (bs.getD i default).1 = false
  | 0, _, _, _, _, _, _, hi => by omega
  | n + 1, E, body, bs, hp, hs, i, hi => by
    cases E <;> simp only [ParamHeadsFree] at hp
    rename_i D B bm
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨tail, rest⟩, hs, he⟩ := hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    cases i with
    | zero => exact hp.1
    | succ i => simpa only [List.getD_cons_succ] using ParamHeadsFree.domains hp.2 hs i (by omega)

end IxVM.Refinement.Decl
