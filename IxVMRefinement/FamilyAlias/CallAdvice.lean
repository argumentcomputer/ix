import IxVMRefinement.FamilyAlias.CheckFamilyReads
import IxVMRefinement.FamilyAlias.CallScoped
import IxVMRefinement.FamilyAlias.FamilyCall
import IxVMRefinement.Assembly.FamilyAdviceWalk
import IxVMRefinement.Assembly.NativeBlockFormer
import IxVMRefinement.Claim.TopDefn
import IxVMRefinement.Decl.FamilyAdvice

/-! # Advice records validated by `check_family`, exact rekeying, and projection absence

Reads `KernelModeled::check_advice_records` and `KernelModeled::check_advice_record` for the
models (`Defn`) and iota theorems (`Thm`) that `member_val` and `check_iota_rule` consult:

* `tmExact_rekey_of_tm`: transfers `TmExact` from `Core.keyOf c.t` to `c.stored.κ` whenever the
  same heap pointer already satisfies `Tm` at `c.stored.κ`;
* `noProjIn_of_renameAll_infer`: derives `NoProjIn bad E = true` from a full-grade `Rules.Infer`
  judgement on `renameAll g E` when every `b ∈ bad` renames to a stored `.defnInfo` in `env`
  (whose projection tables only index `.indInfo` structures);
* `AdvChecked` and `check_advice_records_checked`: every address in the `aset` built by
  `check_advice_records` lies in `advAs`, satisfies `AdviceIn`, and had `check_advice_record`
  run on it;
* `advice_defn_record`, `advice_checked_type`, `advice_stored_defn_facts`,
  `advice_stored_thm_facts`: for any `a` in `aset` loaded by `Ingress::get_ci` as `Defn` or
  `Thm`, extracts the canonical type `ty'`, its exact representation at both `Core.keyOf t` and
  `Ctx.stored`, its level scope, its level-equivalence to the stored constant's positional type,
  and (from `check_advice_record`'s `run_check` → `check_const` → `k_ensure_sort`) its typing
  judgement `Infer env .full 0 ty' stype ∧ Red env 0 stype (.sort u)`. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal ReducibilityHint)
open Ix.Kernel.Semantics (NativeFam)

set_option linter.unusedVariables false

/-! ## Rekeying `TmExact` from `Tm` at `Ctx.stored` -/

/-- **Rekey an exact term to `c.stored.κ`** when the same heap pointer is already represented by
`Tm` at `c.stored.κ`: every `Const` and `Proj` cell carries `Resolved` (and `ProjPermitted`) from
`Tm`, forcing `c.stored.κ = Core.keyOf c.t` on every cell of the term. -/
theorem tmExact_rekey_of_tm {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E₁ E₂ : KExpr} {p : SourceValue F}
    (r1 : Decl.TmExact (Core.keyOf c.t) d Γ h k E₁ p)
    (r2 : Tm c.stored.κ d Γ h k E₂ p) :
    Decl.TmExact c.stored.κ d Γ h k E₁ p := by
  induction r1 generalizing E₂ with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl => exact .sort cell rl
  | @const k addr ap lsp a ls _ cell ra rls =>
    cases r2 with
    | @const _ _ _ _ a' _ _ res2 cell' ra' _ _ =>
      have hv := cell_eq cell cell'
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
      obtain ⟨rfl, rfl⟩ := hv
      have ha : a = a' := addr_det ra ra'
      subst ha
      have hκ : c.stored.κ (ixAddr a) = Core.keyOf c.t (ixAddr a) := by
        rcases resKey_spec c.t (c.resolvesOver c.env) (ixAddr a) with hEq | hUn
        · exact hEq
        · exact absurd hUn res2.ne
      rw [← hκ]
      exact .const cell ra rls
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have hv := cell_eq cell cell'; simp at hv
  | app cell _ _ ihf iha =>
    cases r2 with
    | app cell' rf' ra' =>
      have hv := cell_eq cell cell'
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .app cell (ihf rf') (iha ra')
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have hv := cell_eq cell cell'; simp at hv
  | lam cell _ _ rl iht ihb =>
    cases r2 with
    | lam cell' rt' rb' _ =>
      have hv := cell_eq cell cell'
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact .lam cell (iht rt') (ihb rb') rl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _
    | app cell' _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have hv := cell_eq cell cell'; simp at hv
  | forallE cell _ _ rl iht ihb =>
    cases r2 with
    | forallE cell' rt' rb' _ =>
      have hv := cell_eq cell cell'
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact .forallE cell (iht rt') (ihb rb') rl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _
    | app cell' _ _ | lam cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have hv := cell_eq cell cell'; simp at hv
  | letE cell _ _ _ iht ihv ihb =>
    cases r2 with
    | letE cell' rt' rv' rb' =>
      have hv := cell_eq cell cell'
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact .letE cell (iht rt') (ihv rv') (ihb rb')
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _
    | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have hv := cell_eq cell cell'; simp at hv
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | @proj k addr ap ep a i E _ _ cell ra _ ih =>
    cases r2 with
    | @proj _ _ _ _ a' _ _ res2 perm2 cell' ra' re' =>
      have hv := cell_eq cell cell'
      simp only [Value.construct.injEq, List.cons.injEq, Value.field.injEq, and_true, true_and] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      have ha : a = a' := addr_det ra ra'
      subst ha
      have hκ : c.stored.κ (ixAddr a) = Core.keyOf c.t (ixAddr a) := by
        rcases resKey_spec c.t (c.resolvesOver c.env) (ixAddr a) with hEq | hUn
        · exact hEq
        · exact absurd hUn res2.ne
      rw [← hκ]
      exact .proj cell ra (ih re')
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _
    | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _
    | litNat cell' _ _ | litStr cell' _ _ =>
      have hv := cell_eq cell cell'; simp at hv

theorem tmCExact_rekey_of_tmC {c : Ctx} {h : Heap F} {E₁ E₂ : KExpr} {p : SourceValue F}
    (r1 : Decl.TmCExact (Core.keyOf c.t) h E₁ p) (r2 : TmC c.stored.κ h E₂ p) :
    Decl.TmCExact c.stored.κ h E₁ p :=
  fun d Γ => tmExact_rekey_of_tm (r1 d Γ) (r2 d Γ)

/-! ## `NoProjIn` from `Rules.Infer` on a renamed term -/

theorem hasFvar_renameAll (f : KKey → KKey) :
    ∀ e : KExpr, (Decl.renameAll f e).hasFvar = e.hasFvar
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ _ => rfl
  | .app a b => by simp [Decl.renameAll, Ix.Kernel.Expr.hasFvar, hasFvar_renameAll f a,
      hasFvar_renameAll f b]
  | .lam t b _ | .forallE t b _ => by simp [Decl.renameAll, Ix.Kernel.Expr.hasFvar,
      hasFvar_renameAll f t, hasFvar_renameAll f b]
  | .letE t v b _ => by simp [Decl.renameAll, Ix.Kernel.Expr.hasFvar, hasFvar_renameAll f t,
      hasFvar_renameAll f v, hasFvar_renameAll f b]
  | .proj _ _ e => by simp [Decl.renameAll, Ix.Kernel.Expr.hasFvar, hasFvar_renameAll f e]

private theorem noProjIn_of_renameAll_map {bad : List KKey} {g : KKey → KKey} :
    ∀ e : KExpr, Decl.NoProjIn (bad.map g) (Decl.renameAll g e) = true →
      Decl.NoProjIn bad e = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ ty, h => noProjIn_of_renameAll_map ty h
  | .app a b, h => by
    simp only [Decl.renameAll, Decl.NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨noProjIn_of_renameAll_map a h.1, noProjIn_of_renameAll_map b h.2⟩
  | .lam t b _, h | .forallE t b _, h => by
    simp only [Decl.renameAll, Decl.NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨noProjIn_of_renameAll_map t h.1, noProjIn_of_renameAll_map b h.2⟩
  | .letE t v b _, h => by
    simp only [Decl.renameAll, Decl.NoProjIn, Bool.and_eq_true] at h ⊢
    exact ⟨⟨noProjIn_of_renameAll_map t h.1.1, noProjIn_of_renameAll_map v h.1.2⟩,
      noProjIn_of_renameAll_map b h.2⟩
  | .proj s _ e, h => by
    simp only [Decl.renameAll, Decl.NoProjIn, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    refine ⟨?_, noProjIn_of_renameAll_map e h.2⟩
    by_cases hs : bad.contains s = true
    · have hmem : g s ∈ bad.map g := List.mem_map.mpr ⟨s, List.contains_iff_mem.mp hs, rfl⟩
      have hct : (bad.map g).contains (g s) = true := List.contains_iff_mem.mpr hmem
      rw [h.1] at hct
      exact nomatch hct
    · exact Bool.eq_false_iff.mpr hs

/-- **Projection absence from typing of the renamed term**: if every `b ∈ bad` is renamed to a
stored definition in `env` and `renameAll g E` types in `env` (at full grade), then `E` contains
no projection at any structure in `bad`. -/
theorem noProjIn_of_renameAll_infer {env : Ix.Kernel.Env .anon} {bad : List KKey}
    {g : KKey → KKey} {d : Nat} {E t' : KExpr}
    (hstore : Ix.Kernel.Open.StoreInv env)
    (hdef : ∀ b ∈ bad, ∃ cvm mval hint, env.find? (g b) = some (.defnInfo cvm mval hint))
    (hfv : E.hasFvar = false)
    (hinf : Ix.Kernel.Rules.Infer env .full d (Decl.renameAll g E) t') :
    Decl.NoProjIn bad E = true := by
  have hproj : ∀ sn i entry, env.findProj? sn i = some entry →
      (bad.map g).contains sn = false := by
    intro sn i entry hent
    obtain ⟨tbl, hfP, hi, _⟩ := Ix.Kernel.Env.findProj?_some hent
    obtain ⟨_, _, _, ⟨cvT, caps, hT, _, _⟩, _⟩ := hstore.proj_ok _ tbl hfP i hi
    have hsn : tbl.structName = sn := by
      have hf' : env.consts.find? (fun x => x.name == Ix.Kernel.projTableName sn) =
          some (.projInfo tbl) := hfP
      have hbeq : (ConstantInfo.projInfo tbl : ConstantInfo .anon).name ==
          Ix.Kernel.projTableName sn :=
        List.find?_some (p := fun x : ConstantInfo .anon => x.name == Ix.Kernel.projTableName sn)
          hf'
      exact Ix.Kernel.projTableName_inj (beq_iff_eq.mp hbeq)
    simp only [Ix.Kernel.ProjTable.entry, hsn] at hT
    by_cases hm : (bad.map g).contains sn = true
    · obtain ⟨b, hb, hgb⟩ := List.mem_map.mp (List.contains_iff_mem.mp hm)
      obtain ⟨cvm, mval, hint, hfd⟩ := hdef b hb
      rw [hgb, hT] at hfd
      exact nomatch hfd
    · exact Bool.eq_false_iff.mpr hm
  have hnp := Decl.infer_noProjIn hinf hproj ((hasFvar_renameAll g E).trans hfv)
  exact noProjIn_of_renameAll_map E hnp

/-! ## `check_advice_records` with full `check_advice_record` witness -/

/-- **One advice address validated by `check_advice_records`**: it is listed in `advAs`, recorded
as `AdviceIn`, and had an observed `KernelModeled::check_advice_record` call under the check's
role context with all child calls in `calls`. -/
def AdvChecked (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (lim : Option Nat) (cs : List (Call F)) (advAs : List Bytes.Address) (a : Bytes.Address) :
    Prop :=
  a ∈ advAs ∧
  AdviceIn cs (ixAddr a) ∧
  ∃ (h h' : Heap F) (rc xa seen wset r : SourceValue F) (cs₁ : List (Call F)),
    Claim.RCLimRep t bAddr lim h rc ∧ Bytes.RepAddressRef addrTy h a xa ∧
    ObsFn Obs.W "KernelModeled::check_advice_record" [rc, xa, seen, wset] h r h' cs₁ ∧
    ∀ cl ∈ cs₁, cl ∈ calls

theorem AdvChecked.mono {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {cs₁ cs₂ : List (Call F)}
    {advAs₁ advAs₂ : List Bytes.Address} {a : Bytes.Address}
    (hcs : ∀ cl ∈ cs₁, cl ∈ cs₂) (hadv : ∀ x ∈ advAs₁, x ∈ advAs₂)
    (h : AdvChecked calls bAddr t lim cs₁ advAs₁ a) :
    AdvChecked calls bAddr t lim cs₂ advAs₂ a := by
  obtain ⟨hmem, ⟨rc, xa, seen, wset, hh, hcl, haddr⟩, hobs⟩ := h
  exact ⟨hadv a hmem, ⟨rc, xa, seen, wset, hh, hcs _ hcl, haddr⟩, hobs⟩

/-- **`KernelModeled::check_advice_records`**: every address in the resulting set satisfies
`seenSet` or `AdvChecked`. -/
theorem check_advice_records_checked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {rc wset : SourceValue F} :
    ∀ (advAs : List Bytes.Address) (seenSet : Bytes.Address → Prop)
      {x_advice x_seen r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Claim.RCLimRep t bAddr lim h rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h advAs x_advice →
      AddrMapAll addrMapEnum (fun _ b _ => seenSet b) h x_seen →
      ObsFn Obs.W "KernelModeled::check_advice_records" [rc, x_advice, x_seen, wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      AddrMapAll addrMapEnum
        (fun _ b _ => seenSet b ∨ AdvChecked calls bAddr t lim cs advAs b) h' r ∧
      Heap.Extends h h'
  | [], seenSet, x_advice, x_seen, r, h, h', cs, hrc, hadv_rep, hseen, ev, hsub => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (he21 := he21) (he22 := he22) .. =>
      rw [he21, he22]
      exact ⟨Decl.addrSet_mono_imp (Heap.Extends.refl h) (fun _ hp => Or.inl hp) hseen,
        Heap.Extends.refl h⟩
    | .Cons (ld12 := ld12) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hadv_rep ld12
      cases he
  | a :: rest, seenSet, x_advice, x_seen, r, h, h', cs, hrc, hadv_rep, hseen, ev, hsub => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (ld12 := ld12) .. => cases Lib.rep_nil_of_load hadv_rep ld12
    | .Cons (x_a := x_a) (x_rest := x_rest) (m_cnmrgvie := m_a1) (cs_jxqtckhn := csA1)
        (m_aiikskik := m55) (cs_eiizeeve := csA2) (m90 := m90) (cs100 := cs100) (cs138 := cs138)
        (v143 := v143) (m160 := m160) (cs168 := csIns) (ld12 := ld12) (ev_mfihupbr := ev65)
        (heq_sefkntmx := heq88) (ev_xzbngsxs := ev65w) (heq_xyxoxrbw := heq88w)
        (ev102 := ev102) (ev170 := ev170) (ev140 := ev140) (hc201 := hc201) .. =>
      subst heq88 heq88w
      obtain ⟨a', rest', heq_cons, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load hadv_rep ld12
      injection heq_cons with ha_eq hrest_eq
      subst ha_eq hrest_eq
      have ext_55 : Heap.Extends h m55 := ev65.heap_extends.trans ev65w.heap_extends
      have ext_90 : Heap.Extends h m90 := ext_55.trans ev102.heap_extends
      have ext_160 : Heap.Extends m90 m160 := ev170.heap_extends
      have ext_h_160 : Heap.Extends h m160 := ext_90.trans ext_160
      have hseen1 : AddrMapAll addrMapEnum (fun _ b _ => seenSet b ∨ b = a) m160 v143 :=
        Decl.rbtree_map_insert_field_addrMapAll
          (Bytes.repAddressRef_heapMono₂ addrTy ext_90 ha_rep)
          (Decl.addrSet_mono_imp ext_90 (fun _ hp => hp) hseen) ev170
      obtain ⟨hout, ext_rest⟩ :=
        check_advice_records_checked rest (fun b => seenSet b ∨ b = a)
          (hrc.mono ext_h_160)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_160 hrest_rep)
          hseen1 ev140 (fun cl hcl => hsub cl (by rw [hc201]; simp [hcl]))
      have ha_chk : AdvChecked calls bAddr t lim cs (a :: rest) a :=
        ⟨List.mem_cons_self,
         ⟨rc, x_a, x_seen, wset, m55, by rw [hc201]; simp,
          ⟨a, Bytes.repAddressRef_heapMono₂ addrTy ext_55 ha_rep, rfl⟩⟩,
         m55, m90, rc, x_a, x_seen, wset, _, cs100,
         hrc.mono ext_55, Bytes.repAddressRef_heapMono₂ addrTy ext_55 ha_rep, ev102,
         fun cl hcl => hsub cl (by rw [hc201]; simp [hcl])⟩
      refine ⟨Decl.addrSet_mono_imp (Heap.Extends.refl h') ?_ hout, ext_h_160.trans ext_rest⟩
      intro b hb
      rcases hb with (hs | rfl) | hrm
      · exact Or.inl hs
      · exact Or.inr ha_chk
      · exact Or.inr (hrm.mono (fun cl hcl => by rw [hc201]; simp [hcl])
          (fun x hx => List.mem_cons_of_mem _ hx))

/-! ## `check_advice_record` and `check_const` for advice `Defn`/`Thm` records -/

private theorem is_unsafe_ci_defnValShape_safe {d : Ixon.Definition}
    {tyPtr valPtr hint v1 : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (hsafe : Ix.Kernel.Reader.safetyDecline d = none)
    (ev : ObsFn Obs.W "KernelCheck::is_unsafe_ci"
      [L1.defnValShape d tyPtr valPtr hint] h v1 m2 cs) :
    v1 = .field 0 ∧ m2 = h := by
  cases hk : d.kind with
  | defn =>
    have hs : d.safety = .safe := by
      rw [Ix.Kernel.Reader.safetyDecline, hk] at hsafe
      cases hds : d.safety with
      | safe => rfl
      | unsaf => rw [hds] at hsafe; exact absurd hsafe (by decide)
      | part => rw [hds] at hsafe; exact absurd hsafe (by decide)
    simp only [L1.defnValShape, hk, hs] at ev
    cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | Defn_Safe _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Defn_other _ _ _ _ _ _ hv hne _ _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      exact (hne [] rfl (by simpa [L1.repDefSafetyVal] using hs_eq.symm)).elim
    | Axiom _ _ _ hv | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | thm =>
    simp only [L1.defnValShape, hk] at ev
    cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | Thm _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | opaq =>
    have hns : (d.safety == .unsaf) = false := by
      simpa [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk] using hsafe
    simp only [L1.defnValShape, hk, hns] at ev
    cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | Opaque _ _ _ _ _ _ _ hv he hr _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hu_eq⟩
      rw [← hu_eq] at he
      exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Thm _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv

/-- **An advice record validated by `check_advice_record` and loaded by `get_ci` as `Defn` or
`Thm`** is a standalone safe definition or theorem in `E₀`, so it has `ConstAddrOf`, `InLogic`,
and a `CheckedLimAt` witness from `check_advice_record`'s `run_check`. -/
theorem advice_defn_record {calls : List (Call F)} {E₀ : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {lim : Option Nat} {cs : List (Call F)}
    {advAs : List Bytes.Address} {a : Bytes.Address}
    (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hAdv : AdvChecked calls bAddr t lim cs advAs a)
    {xa ptr : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)}
    (ha : Bytes.RepAddressRef addrTy h₁ a xa)
    (ev_ci : ObsFn Obs.W "Ingress::get_ci" [xa] h₁ ptr h₂ cs_ci)
    (hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls)
    {tag : String} {args : List (SourceValue F)}
    (htag : tag = "Defn" ∨ tag = "Thm")
    (hld : loadValue h₂ ptr = .ok (.construct kciEnum tag args)) :
    ∃ (c : Ixon.Constant) (d : Ixon.Definition),
      recordOf E₀ (ixAddr a) = some c ∧ c.info = .defn d ∧
      (tag = "Defn" → d.kind = .defn) ∧ (tag = "Thm" → d.kind = .thm) ∧
      InLogic c ∧ ConstAddrOf (ixAddr a) c (ixAddr a) ∧
      Claim.CheckedLimAt calls bAddr t (ixAddr a) lim := by
  obtain ⟨-, -, h0, h0', rc0, xa0, seen0, wset0, r0, cs1, hrc0, ha0, ev_car, hsub1⟩ := hAdv
  match Obs.«KernelModeled::check_advice_record».obs ev_car with
  | .run (cs12 := csLd) (cs947 := csSg) (ev_yqjbwijz := evOrd) (ev14 := evLd) (sg952 := sg)
      (hc1011 := hc) .. =>
    have hsubLd : ∀ cl ∈ csLd, cl ∈ calls := fun cl hcl => hsub1 cl (by rw [hc]; simp [hcl])
    have hsubSg : ∀ cl ∈ csSg, cl ∈ calls := fun cl hcl => hsub1 cl (by rw [hc]; simp [hcl])
    obtain ⟨extLd, bytes, c, hsz, hh, hb, hde, hex, hcp, -⟩ :=
      Claim.load_verified_constant_de
        ⟨a, Bytes.repAddressRef_heapMono₂ addrTy evOrd.heap_extends ha0, rfl⟩ evLd
    have hrec : recordOf E₀ (ixAddr a) = some c := by
      rw [← hb]
      exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsubLd hh) hsz hde hex
    -- `get_ci` loads the same record `c`
    obtain ⟨-, bytes2, c2, blobs2, hh2, hb2, hex2, _, _, _, hraw⟩ :=
      L1.get_ci_spec (RomBound.bounded_mono hbound hsub_ci) ha ev_ci
    have hrecAt : Ix.Cert.recordAt E₀ (ixAddr a) = some c :=
      (hS.recordOf_eq_recordAt (ixAddr a)).symm.trans hrec
    have hc2 : c2 = c := hS.record_eq hrecAt (Core.hashed_mono hsub_ci hh2) hb2 hex2
    subst c2
    -- Identify `infoVal` from `hcp`
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfoRep, -⟩ := hcp
    injection hv_c with _ _ hargs_c
    simp only [List.cons.injEq] at hargs_c
    rw [← hargs_c.1] at hinfoRep
    unfold L1.GetCIRawResult at hraw
    -- Case split on `sg`: only `Defn_Definition_Safe` and `Defn_Theorem` match `tag ∈ {Defn, Thm}`
    match sg with
    | .Defn_Definition_Safe (hv81 := hv81) (ev210 := evRc) (hc227 := hcsg) .. =>
      rw [hv81] at hinfoRep
      cases hinfo : c.info with
      | defn d =>
        rw [hinfo] at hinfoRep hraw
        obtain ⟨dv, hdv, hdefRep⟩ := hinfoRep
        injection hdv with _ _ hdvargs
        injection hdvargs with hdv'
        subst hdv'
        obtain ⟨kindV, safetyV, -, -, -, -, hdv2, hkindRep, hsafRep, -, -, -, -⟩ := hdefRep
        injection hdv2 with _ _ hargs2
        simp only [List.cons.injEq] at hargs2
        have hdk : d.kind = .defn := by
          rw [← hargs2.1] at hkindRep
          cases hk : d.kind <;> simp [L1.RepDefKind, hk] at hkindRep ⊢
        have hds : d.safety = .safe := by
          rw [← hargs2.2.1] at hsafRep
          cases hs : d.safety <;> simp [L1.RepDefSafety, hs] at hsafRep ⊢
        obtain ⟨v, hld', -, tyPtr, valPtr, hintVal, rfl, -, -⟩ := hraw
        rw [hld] at hld'
        injection hld' with hveq
        have htagEq : tag = "Defn" := by
          simp [L1.defnValShape, hdk, Core.kciEnum] at hveq
          exact hveq.1
        have hlog : InLogic c := by
          unfold InLogic
          rw [hinfo]
          simp [Ix.Kernel.Reader.safetyDecline, hdk, hds]
        have hrc_lim := (Claim.run_check_lim_spec (hrc0.mono (evOrd.heap_extends.trans extLd))
          ⟨a, Bytes.repAddressRef_heapMono₂ addrTy (evOrd.heap_extends.trans extLd) ha0, rfl⟩
          evRc).2.mono (fun cl hcl => hsubSg cl (by rw [hcsg]; simp [hcl]))
        exact ⟨c, d, hrec, hinfo, fun _ => hdk, fun ht => absurd (htagEq.symm.trans ht) (by decide),
          hlog, Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩, hrc_lim⟩
      | axio _ | quot _ | recr _ | muts _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
        rw [hinfo] at hinfoRep; obtain ⟨_, hv, _⟩ := hinfoRep; simp at hv
    | .Defn_Definition_other (heq258 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    | .Defn_Theorem (hv81 := hv81) (ev321 := evRc) (hc338 := hcsg) .. =>
      rw [hv81] at hinfoRep
      cases hinfo : c.info with
      | defn d =>
        rw [hinfo] at hinfoRep hraw
        obtain ⟨dv, hdv, hdefRep⟩ := hinfoRep
        injection hdv with _ _ hdvargs
        injection hdvargs with hdv'
        subst hdv'
        obtain ⟨kindV, safetyV, -, -, -, -, hdv2, hkindRep, -, -, -, -, -⟩ := hdefRep
        injection hdv2 with _ _ hargs2
        simp only [List.cons.injEq] at hargs2
        have hdk : d.kind = .thm := by
          rw [← hargs2.1] at hkindRep
          cases hk : d.kind <;> simp [L1.RepDefKind, hk] at hkindRep ⊢
        obtain ⟨v, hld', -, tyPtr, valPtr, hintVal, rfl, -, -⟩ := hraw
        rw [hld] at hld'
        injection hld' with hveq
        have htagEq : tag = "Thm" := by
          simp [L1.defnValShape, hdk, Core.kciEnum] at hveq
          exact hveq.1
        have hlog : InLogic c := by
          unfold InLogic
          rw [hinfo]
          simp [Ix.Kernel.Reader.safetyDecline, hdk]
        have hrc_lim := (Claim.run_check_lim_spec (hrc0.mono (evOrd.heap_extends.trans extLd))
          ⟨a, Bytes.repAddressRef_heapMono₂ addrTy (evOrd.heap_extends.trans extLd) ha0, rfl⟩
          evRc).2.mono (fun cl hcl => hsubSg cl (by rw [hcsg]; simp [hcl]))
        exact ⟨c, d, hrec, hinfo, fun ht => absurd (htagEq.symm.trans ht) (by decide), fun _ => hdk,
          hlog, Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩, hrc_lim⟩
      | axio _ | quot _ | recr _ | muts _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
        rw [hinfo] at hinfoRep; obtain ⟨_, hv, _⟩ := hinfoRep; simp at hv
    | .Defn_Opaque (heq372 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    | .Recr (hv403 := hv403) .. =>
      rw [hv403] at hinfoRep
      cases hinfo : c.info with
      | recr rc =>
        rw [hinfo] at hraw
        obtain ⟨v, hld', hval⟩ := hraw
        obtain ⟨-, -, -, -, -, -, _, _, _, _, -, -, hveq, -⟩ := hval
        rw [hld] at hld'
        injection hld' with hvv
        rw [← hvv] at hveq
        rcases htag with rfl | rfl <;> simp [Core.kciEnum] at hveq
      | axio _ | defn _ | quot _ | muts _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
        rw [hinfo] at hinfoRep; obtain ⟨_, hv, _⟩ := hinfoRep; simp at hv
    | .Muts (hv598 := hv598) .. =>
      rw [hv598] at hinfoRep
      cases hinfo : c.info with
      | muts _ => rw [hinfo] at hraw; exact hraw.elim
      | axio _ | defn _ | quot _ | recr _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
        rw [hinfo] at hinfoRep; obtain ⟨_, hv, _⟩ := hinfoRep; simp at hv
    | .IPrj (hv790 := hv790) .. =>
      rw [hv790] at hinfoRep
      cases hinfo : c.info with
      | iPrj p =>
        rw [hinfo] at hraw
        obtain ⟨-, _, _, _, _, v, -, -, -, -, -, -, hld', hval⟩ := hraw
        obtain ⟨-, -, -, -, -, _, _, _, -, -, hveq, -⟩ := hval
        rw [hld] at hld'
        injection hld' with hvv
        rw [← hvv] at hveq
        rcases htag with rfl | rfl <;> simp [Core.kciEnum] at hveq
      | axio _ | defn _ | quot _ | recr _ | muts _ | dPrj _ | cPrj _ | rPrj _ =>
        rw [hinfo] at hinfoRep; obtain ⟨_, hv, _⟩ := hinfoRep; simp at hv
    | .CPrj (hv869 := hv869) .. =>
      rw [hv869] at hinfoRep
      cases hinfo : c.info with
      | cPrj p =>
        rw [hinfo] at hraw
        obtain ⟨-, -, _, _, _, _, _, v, -, -, -, -, -, -, -, hld', hval⟩ := hraw
        obtain ⟨-, -, -, -, -, _, _, _, -, -, hveq, -⟩ := hval
        rw [hld] at hld'
        injection hld' with hvv
        rw [← hvv] at hveq
        rcases htag with rfl | rfl <;> simp [Core.kciEnum] at hveq
      | axio _ | defn _ | quot _ | recr _ | muts _ | dPrj _ | iPrj _ | rPrj _ =>
        rw [hinfo] at hinfoRep; obtain ⟨_, hv, _⟩ := hinfoRep; simp at hv

/-- **Type-checking witness extracted from `CheckedLimAt` on a safe standalone `Defn` or `Thm`**:
gives the canonical annotated type `ty'`, its level scope, its exact representation at the second
`Ingress::get_ci` call, and the `k_ensure_sort` observation (together with its `get_ci` load) so
any `FamilyStepEnv` can read `Infer` and `Red` off it. -/
structure AdviceTypeWitness (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (a : Bytes.Address) (nlvls : Nat) (h₂ : Heap F) (nl mty : SourceValue F)
    (ty' : KExpr) where
  nlvls_lt : nlvls < 4294967296
  nl_eq : nl = .field (nlvls : F)
  ty_levels : ty'.allLevelParamsDefined (List.range nlvls) = true
  mty_scoped : HeapExprScoped h₂ nlvls 0 mty
  tm_ci : Decl.TmCExact (Core.keyOf t) h₂ ty' mty
  -- Witness from `check_advice_record`'s `run_check` (`get_ci` + `k_ensure_sort`)
  h_pre : Heap F
  m_chk : Heap F
  m_pre : Heap F
  m_es : Heap F
  m_es' : Heap F
  x_a : SourceValue F
  ptr₁ : SourceValue F
  v₁ : SourceValue F
  x_rc : SourceValue F
  x_ty₁ : SourceValue F
  v_sort : SourceValue F
  cs_ld : List (Call F)
  cs_es : List (Call F)
  ha₁ : Bytes.RepAddressRef addrTy h_pre a x_a
  ev_ld : ObsFn Obs.W "Ingress::get_ci" [x_a] h_pre ptr₁ m_chk cs_ld
  sub_ld : ∀ cl ∈ cs_ld, cl ∈ calls
  hld₁ : loadValue m_chk ptr₁ = .ok v₁
  hv₁ : (∃ w1 w2 w3, v₁ = .construct kciEnum "Defn" [.field (nlvls : F), x_ty₁, w1, w2, w3]) ∨
    (∃ w1, v₁ = .construct kciEnum "Thm" [.field (nlvls : F), x_ty₁, w1])
  ext_chk_es : Heap.Extends m_chk m_es
  hm_es : m_es = m_pre ++ [.construct kexprListEnum "Nil" []]
  hrc_es : Core.RCRep t lim m_es x_rc
  tm_chk : Decl.TmCExact (Core.keyOf t) m_chk ty' x_ty₁
  ev_es : ObsFn Obs.W "KernelInfer::k_ensure_sort"
    [x_rc, x_ty₁, .ptr (.enum kexprListEnum) m_pre.length] m_es v_sort m_es' cs_es
  sub_es : ∀ cl ∈ cs_es, cl ∈ calls

/-- Extract `AdviceTypeWitness` from `CheckedLimAt` and a second `get_ci` returning `Defn`/`Thm`. -/
theorem advice_checked_type {calls : List (Call F)} {E₀ : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {lim : Option Nat} {a : Bytes.Address}
    {c : Ixon.Constant} {d : Ixon.Definition}
    (ht : t.check = .ok ()) (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : recordOf E₀ (ixAddr a) = some c) (hinfo : c.info = .defn d)
    (hkind : d.kind = .defn ∨ d.kind = .thm) (hlogic : InLogic c)
    (hchk : Claim.CheckedLimAt calls bAddr t (ixAddr a) lim)
    {xa ptr nl mty : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)}
    (ha : Bytes.RepAddressRef addrTy h₁ a xa)
    (ev_ci : ObsFn Obs.W "Ingress::get_ci" [xa] h₁ ptr h₂ cs_ci)
    (hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls)
    (hld : (∃ w1 w2 w3, loadValue h₂ ptr = .ok (.construct kciEnum "Defn" [nl, mty, w1, w2, w3])) ∨
      (∃ w1, loadValue h₂ ptr = .ok (.construct kciEnum "Thm" [nl, mty, w1]))) :
    ∃ ty' : KExpr, Nonempty (AdviceTypeWitness calls t lim a d.lvls.toNat h₂ nl mty ty') := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic; unfold InLogic at hl; rw [hinfo] at hl; exact hl
  have hrecAt : Ix.Cert.recordAt E₀ (ixAddr a) = some c :=
    (hS.recordOf_eq_recordAt (ixAddr a)).symm.trans hrec
  -- Unpack `CheckedLimAt`
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr₁, v₁, r_chk, cs_ld, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld₁, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, hix'⟩ := ha_pre
  have ha_eq : a' = a := Decl.ixAddr_injective hix'
  subst a'
  obtain ⟨raw1, c1, hh1, hba1, hex1, hres1⟩ := L1.get_ci_trace_spec ha'_ref ev_ld
  have hc1 : c = c1 := (hS.record_eq hrecAt (Core.hashed_mono hsub_ld hh1) hba1 hex1).symm
  subst hc1
  unfold L1.GetCITraceResult at hres1
  rw [hinfo] at hres1
  obtain ⟨blobs1, tree1, v1', hhp1, built1, hld1', htr1⟩ := hres1
  rw [hld₁] at hld1'; injection hld1' with hvv1; subst hvv1
  have hblob1 : ∀ x bs, (x, bs) ∈ blobs1 → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp1 (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx)
    rwa [hxa] at hrun
  obtain ⟨raw1', ty₀, val₀, hty, hval, -, -⟩ :=
    LoadedReads.defn_reading (store := recordOf E₀) (blob := fun x => E₀.blobs.get? x) ht
      hrec hinfo hlogic hblob1 htr1.toRaw
  have hrecur : L1.defnRecurAddrs d (ixAddr a) = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnRecurAddrs, hf]
  rw [hrecur] at htr1
  obtain ⟨hnlvls, tyPtr1, valPtr1, hint1, planT1, planV1, hv1_eq, rty1, rval1, hpT1, hpV1, hlT1,
    hlV1⟩ := htr1
  subst hv1_eq
  -- Invert `ev_chk : KernelCheck::check_const` for both `Defn` and `Thm`
  have hchk_res :
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      ∃ (m_ws m_pre m_es m_es' : Heap F) (v_ws v_sort : SourceValue F)
        (cs_ws cs_es : List (Call F)),
        ObsFn Obs.W "KernelCheck::validate_expr_well_scoped"
          [tyPtr1, .field 0, .field (d.lvls.toNat : F)] m_chk v_ws m_ws cs_ws ∧
        Heap.Extends m_chk m_es ∧
        m_es = m_pre ++ [.construct kexprListEnum "Nil" []] ∧
        ObsFn Obs.W "KernelInfer::k_ensure_sort"
          [rc, tyPtr1, .ptr (.enum kexprListEnum) m_pre.length] m_es v_sort m_es' cs_es ∧
        ∀ cl ∈ cs_es, cl ∈ calls := by
    rcases hkind with hk | hk
    · have hv_shape : L1.defnValShape d tyPtr1 valPtr1 hint1 =
          .construct kciEnum "Defn"
            [.field (d.lvls.toNat : F), tyPtr1, valPtr1, L1.repDefSafetyVal d.safety, hint1] := by
        simp [L1.defnValShape, hk]
      cases Obs.«KernelCheck::check_const».obs ev_chk with
      | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Thm | Opaque | Quot
      | Induct_n0 | Induct_other_n0 | Induct_other_other
      | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
      | Rec_n0 | Rec_other => simp_all [L1.defnValShape, kciEnum]
      | Defn v1 m2 cs12 x_nlvls x_ty x_val _ _ _ m299 cs309 _ m336 cs346 v372 m373 cs383 m404
          _ m417 cs427 _ m447 cs457 cs479 m508
          ev14 _ hv269 ev311 ev348 hm412 ev385 _ _ _ _ hc520 =>
        obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe ev14
        subst v1; subst m2
        rw [hv_shape] at hv269
        simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv269
        obtain ⟨hxn, hxt, hxv, -, -⟩ := hv269
        subst x_nlvls; subst x_ty; subst x_val
        have hcl_v1 : (⟨"KernelCheck::validate_expr_well_scoped",
            [tyPtr1, .field 0, .field (d.lvls.toNat : F)], m_chk⟩ : Call F) ∈ calls :=
          hsub_chk _ (by rw [hc520]; simp)
        have hsub_es : ∀ cl ∈ cs383, cl ∈ calls := fun cl hcl => hsub_chk cl (by rw [hc520]; simp [hcl])
        obtain ⟨_, hty_lbb, hty_def⟩ :=
          Assembly.validate_expr_well_scoped_spec (cx := readCtx t (fun x => E₀.blobs.get? x))
            (self := soloSelf t (ixAddr a)) hbound hnlvls rty1 (Heap.Extends.refl m_chk) hty ev311
            hcl_v1
        have ext_m_404 : Heap.Extends m_chk m404 :=
          ev311.heap_extends.trans (ev348.heap_extends.trans (by rw [hm412]; exact Heap.Extends.snoc _ _))
        exact ⟨hty_lbb, hty_def, m299, m336, m404, m373, _, v372, cs309, cs383,
          ev311, ext_m_404, hm412, ev385, hsub_es⟩
    · have hv_shape : L1.defnValShape d tyPtr1 valPtr1 hint1 =
          .construct kciEnum "Thm" [.field (d.lvls.toNat : F), tyPtr1, valPtr1] := by
        simp [L1.defnValShape, hk]
      cases Obs.«KernelCheck::check_const».obs ev_chk with
      | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn | Opaque | Quot
      | Induct_n0 | Induct_other_n0 | Induct_other_other
      | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
      | Rec_n0 | Rec_other => simp_all [L1.defnValShape, kciEnum]
      | Thm v1 m2 cs12 x_nlvls x_ty x_val _ m544 cs554 _ m581 cs591 v617 m618 cs628 m649
          _ _ _ _ _ _ _ _ _ _ _ _
          ev14 _ _ hv526 ev556 ev593 hm657 ev630 _ _ _ _ _ _ _ hc819 =>
        obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe ev14
        subst v1; subst m2
        rw [hv_shape] at hv526
        simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv526
        obtain ⟨hxn, hxt, hxv⟩ := hv526
        subst x_nlvls; subst x_ty; subst x_val
        have hcl_v1 : (⟨"KernelCheck::validate_expr_well_scoped",
            [tyPtr1, .field 0, .field (d.lvls.toNat : F)], m_chk⟩ : Call F) ∈ calls :=
          hsub_chk _ (by rw [hc819]; simp)
        have hsub_es : ∀ cl ∈ cs628, cl ∈ calls := fun cl hcl => hsub_chk cl (by rw [hc819]; simp [hcl])
        obtain ⟨_, hty_lbb, hty_def⟩ :=
          Assembly.validate_expr_well_scoped_spec (cx := readCtx t (fun x => E₀.blobs.get? x))
            (self := soloSelf t (ixAddr a)) hbound hnlvls rty1 (Heap.Extends.refl m_chk) hty ev556
            hcl_v1
        have ext_m_649 : Heap.Extends m_chk m649 :=
          ev556.heap_extends.trans (ev593.heap_extends.trans (by rw [hm657]; exact Heap.Extends.snoc _ _))
        exact ⟨hty_lbb, hty_def, m544, m581, m649, m618, _, v617, cs554, cs628,
          ev556, ext_m_649, hm657, ev630, hsub_es⟩
  obtain ⟨hty_lbb, hty_def, m_ws, m_pre, m_es, m_es', v_ws, v_sort, cs_ws, cs_es,
    ev_ws, ext_chk_es, hm_es, ev_es, hsub_es⟩ := hchk_res
  -- Canonical exact annotation at `ev_ld`
  have hagree1 : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs1 :=
    L1.BlobReadAgreement.of_mem hblob1
  obtain ⟨ty', hcT1, -, htm1⟩ :=
    LoadedReads.annotation_canon_exact (recurAddrs := []) ht hnlvls
      (fun _ _ _ _ hx => by simp at hx) hagree1 rty1 built1 hpT1 hlT1 hty hty_lbb hty_def
  rw [Decl.posOf_range] at htm1
  have hty'_def : ty'.allLevelParamsDefined (List.range d.lvls.toNat) = true :=
    Decl.validate_expr_well_scoped_spec hnlvls (htm1 0 (fun _ => .sort .zero)) ev_ws
  -- Second `get_ci` (`ev_ci`): same canonical annotation `ty'`!
  obtain ⟨raw2, c2, hh2, hba2, hex2, hres2⟩ := L1.get_ci_trace_spec ha ev_ci
  have hc2 : c = c2 := (hS.record_eq hrecAt (Core.hashed_mono hsub_ci hh2) hba2 hex2).symm
  subst hc2
  unfold L1.GetCITraceResult at hres2
  rw [hinfo] at hres2
  obtain ⟨blobs2, tree2, v2, hhp2, built2, hld2', htr2⟩ := hres2
  have hblob2 : ∀ x bs, (x, bs) ∈ blobs2 → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp2 (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ci hhx)
    rwa [hxa] at hrun
  rw [hrecur] at htr2
  obtain ⟨-, tyPtr2, valPtr2, hint2, planT2, planV2, hv2_eq, rty2, -, hpT2, -, hlT2, -⟩ := htr2
  subst hv2_eq
  have hagree2 : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs2 :=
    L1.BlobReadAgreement.of_mem hblob2
  obtain ⟨ty'', hcT2, -, htm2⟩ :=
    LoadedReads.annotation_canon_exact (recurAddrs := []) ht hnlvls
      (fun _ _ _ _ hx => by simp at hx) hagree2 rty2 built2 hpT2 hlT2 hty hty_lbb hty_def
  have hty_eq : ty'' = ty' := Option.some.inj (hcT2.symm.trans hcT1)
  subst hty_eq
  rw [Decl.posOf_range] at htm2
  -- Match `nl` and `mty` with `.field d.lvls.toNat` and `tyPtr2`
  have hnm : nl = .field (d.lvls.toNat : F) ∧ mty = tyPtr2 := by
    rcases hld with ⟨w1, w2, w3, hld2⟩ | ⟨w1, hld2⟩
    · rw [hld2] at hld2'
      injection hld2' with hvv
      rcases hkind with hk | hk
      · simp [L1.defnValShape, hk, kciEnum] at hvv
        exact ⟨hvv.1, hvv.2.1⟩
      · simp [L1.defnValShape, hk, kciEnum] at hvv
    · rw [hld2] at hld2'
      injection hld2' with hvv
      rcases hkind with hk | hk
      · simp [L1.defnValShape, hk, kciEnum] at hvv
      · simp [L1.defnValShape, hk, kciEnum] at hvv
        exact ⟨hvv.1, hvv.2.1⟩
  obtain ⟨hnl_eq, hmty_eq⟩ := hnm
  subst hmty_eq
  have hv1_cases :
      (∃ w1 w2 w3, L1.defnValShape d tyPtr1 valPtr1 hint1 =
        .construct kciEnum "Defn" [.field (d.lvls.toNat : F), tyPtr1, w1, w2, w3]) ∨
      (∃ w1, L1.defnValShape d tyPtr1 valPtr1 hint1 =
        .construct kciEnum "Thm" [.field (d.lvls.toNat : F), tyPtr1, w1]) := by
    rcases hkind with hk | hk
    · exact Or.inl ⟨valPtr1, L1.repDefSafetyVal d.safety, hint1, by simp [L1.defnValShape, hk]⟩
    · exact Or.inr ⟨valPtr1, by simp [L1.defnValShape, hk]⟩
  exact ⟨ty',
    ⟨{ nlvls_lt := hnlvls
       nl_eq := hnl_eq
       ty_levels := hty'_def
       mty_scoped := heapExprScoped_of_rawConvExpr rty2 hty hty_lbb hty_def
       tm_ci := htm2
       h_pre := h_pre
       m_chk := m_chk
       m_pre := m_pre
       m_es := m_es
       m_es' := m_es'
       x_a := ap
       ptr₁ := ptr₁
       v₁ := L1.defnValShape d tyPtr1 valPtr1 hint1
       x_rc := rc
       x_ty₁ := tyPtr1
       v_sort := v_sort
       cs_ld := cs_ld
       cs_es := cs_es
       ha₁ := ha'_ref
       ev_ld := ev_ld
       sub_ld := hsub_ld
       hld₁ := hld₁
       hv₁ := hv1_cases
       ext_chk_es := ext_chk_es
       hm_es := hm_es
       hrc_es := (hrc_m.mono ext_chk_es).toRCRep
       tm_chk := htm1
       ev_es := ev_es
       sub_es := hsub_es }⟩⟩

/-- **Stored model definition facts at any `FamilyStepEnv`**: combines `AdviceTypeWitness` with
`PrefixInv.loads.getCI` and `scoped_core_ensure_sort` to produce the stored `.defnInfo`, level
parameter permutation, level equivalence, exact stored representation, and sort typing judgement. -/
theorem advice_stored_defn_facts {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {adv : _root_.Address → Prop}
    {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env)
    {a : Bytes.Address} {c : Ixon.Constant} {nlvls : Nat}
    {xa ptr nl mty w1 w2 w3 : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)}
    {ty' : KExpr}
    (hadv : adv (ixAddr a)) (hrec : recordOf E₀ (ixAddr a) = some c)
    (hca : ConstAddrOf (ixAddr a) c (ixAddr a))
    (ha : Bytes.RepAddressRef addrTy h₁ a xa)
    (ev_ci : ObsFn Obs.W "Ingress::get_ci" [xa] h₁ ptr h₂ cs_ci)
    (hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls)
    (hld : loadValue h₂ ptr = .ok (.construct kciEnum "Defn" [nl, mty, w1, w2, w3]))
    (W : AdviceTypeWitness calls t lim a nlvls h₂ nl mty ty') :
    ∃ (cvm : ConstantVal .anon) (mval : KExpr) (hint : ReducibilityHint),
      env.find? (Core.keyOf t (ixAddr a)) = some (.defnInfo cvm mval hint) ∧
      cvm.levelParams.Perm (List.range nlvls) ∧
      ExprLvEq ty' (posOf cvm.levelParams cvm.type) ∧
      Decl.TmCExact (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h₂ ty' mty ∧
      ∃ stype u, Ix.Kernel.Rules.Infer env .full 0 ty' stype ∧
        Ix.Kernel.Rules.Red env 0 stype (.sort u) := by
  let sc := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hst : (env.find? (Core.keyOf t (ixAddr a))).isSome = true :=
    hE.advStored (ixAddr a) hadv c hrec (ixAddr a) hca
  obtain ⟨ci₀, hfind₀⟩ := Option.isSome_iff_exists.mp hst
  have hκa : sc.κ (ixAddr a) = Core.keyOf t (ixAddr a) :=
    Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hfind₀
  have hne_a : sc.κ (ixAddr a) ≠ unresolvedKey := by
    rw [hκa]; exact Resolved.ne
  have hgood := hE.store.good env lim
  -- `getCI` at `ev_ci`
  obtain ⟨ci2, hfind2, hptr2⟩ := hE.prefixInv.loads.getCI xa ptr h₁ h₂ cs_ci a ev_ci trivial
    hne_a (CoreGood.ofRaw (hgood.sub hsub_ci) (fun _ _ => trivial)) ha
  rw [hκa] at hfind2
  obtain ⟨v2, hld2, hci2⟩ := hptr2
  rw [hld] at hld2; injection hld2 with hv2
  cases hci2 with
  | @defn _ _ _ _ _ cvm mval hint hval2 _ =>
    injection hv2 with _ _ hargs2
    simp only [List.cons.injEq, and_true] at hargs2
    obtain ⟨rfl, rfl, -, -, -⟩ := hargs2
    obtain ⟨hnl2, hlt2, hperm2, htm2⟩ := hval2
    have hlen_eq : cvm.levelParams.length = nlvls := by
      have hfeq : (cvm.levelParams.length : F) = (nlvls : F) :=
        Value.field.inj (hnl2.symm.trans W.nl_eq)
      have hv1 : ZMod.val (cvm.levelParams.length : F) = cvm.levelParams.length :=
        SubstAux.val_natCast (Nat.lt_trans hlt2 (by decide))
      have hv2' : ZMod.val (nlvls : F) = nlvls :=
        SubstAux.val_natCast (Nat.lt_trans W.nlvls_lt (by decide))
      rw [← hv1, hfeq, hv2']
    have hperm_n : cvm.levelParams.Perm (List.range nlvls) := hlen_eq ▸ hperm2
    have htm2_ex : Decl.TmCExact sc.κ h₂ ty' mty := tmCExact_rekey_of_tmC W.tm_ci htm2
    have hlvEq : ExprLvEq ty' (posOf cvm.levelParams cvm.type) :=
      Tm.det ((htm2_ex 0 (fun _ => .sort .zero)).toTm) (htm2 0 (fun _ => .sort .zero))
    -- `getCI` at `W.ev_ld` → `scoped_core_ensure_sort` on `W.ev_es`
    obtain ⟨ci1, hfind1, hptr1⟩ := hE.prefixInv.loads.getCI W.x_a W.ptr₁ W.h_pre W.m_chk W.cs_ld a
      W.ev_ld trivial hne_a (CoreGood.ofRaw (hgood.sub W.sub_ld) (fun _ _ => trivial)) W.ha₁
    rw [hκa, hfind2] at hfind1
    obtain rfl := Option.some.inj hfind1
    obtain ⟨v1', hld1', hci1⟩ := hptr1
    rw [W.hld₁] at hld1'; injection hld1' with hv1'
    cases hci1 with
    | defn hval1 _ =>
      rcases W.hv₁ with ⟨_, _, _, hv1eq⟩ | ⟨_, hv1eq⟩
      · rw [hv1eq] at hv1'
        injection hv1' with _ _ hargs1
        simp only [List.cons.injEq] at hargs1
        rw [← hargs1.2.1] at hval1
        have htm1_ex : Decl.TmCExact sc.κ W.m_chk ty' W.x_ty₁ :=
          tmCExact_rekey_of_tmC W.tm_chk hval1.2.2.2
        have hnil : TypesRep sc.κ (fun _ => .sort .zero) W.m_es 0
            (.ptr (.enum kexprListEnum) W.m_pre.length) := by
          rw [W.hm_es]
          exact Decl.typesRep_alloc_nil sc.κ (fun _ => .sort .zero) W.m_pre
        have hscf := hE.prefixInv.scopedCoreFacts
        obtain ⟨stype, u, -, hinf, hred, -, -⟩ := Decl.scoped_core_ensure_sort (c := sc)
          W.hrc_es hnil (Decl.ghostScoped_zero _) hscf.1 hscf.2
          (CoreGood.ofRaw (hgood.sub W.sub_es) (fun _ _ => trivial)) W.ev_es
          ((htm1_ex 0 (fun _ => .sort .zero)).mono W.ext_chk_es).toTm
        exact ⟨cvm, mval, hint, hfind2, hperm_n, hlvEq, htm2_ex, stype, u, hinf, hred⟩
      · rw [hv1eq] at hv1'
        injection hv1' with _ htag _; exact absurd htag (by decide)
    | quot _ _ =>
      rcases W.hv₁ with ⟨_, _, _, hv1eq⟩ | ⟨_, hv1eq⟩ <;>
        (rw [hv1eq] at hv1'; injection hv1' with _ htag _; exact absurd htag (by decide))
  | _ => simp [kciEnum] at hv2

/-- **Stored iota-theorem facts at any `FamilyStepEnv`**: combines `AdviceTypeWitness` with
`PrefixInv.loads.getCI` to produce the stored `.thmInfo`, level parameter permutation, level
equivalence, and exact stored representation of `ty'` at `mty`. -/
theorem advice_stored_thm_facts {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {adv : _root_.Address → Prop}
    {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env)
    {a : Bytes.Address} {c : Ixon.Constant} {nlvls : Nat}
    {xa ptr nl mty w1 : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)}
    {ty' : KExpr}
    (hadv : adv (ixAddr a)) (hrec : recordOf E₀ (ixAddr a) = some c)
    (hca : ConstAddrOf (ixAddr a) c (ixAddr a))
    (ha : Bytes.RepAddressRef addrTy h₁ a xa)
    (ev_ci : ObsFn Obs.W "Ingress::get_ci" [xa] h₁ ptr h₂ cs_ci)
    (hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls)
    (hld : loadValue h₂ ptr = .ok (.construct kciEnum "Thm" [nl, mty, w1]))
    (W : AdviceTypeWitness calls t lim a nlvls h₂ nl mty ty') :
    ∃ (cvt : ConstantVal .anon) (vt : KExpr),
      env.find? (Core.keyOf t (ixAddr a)) = some (.thmInfo cvt vt) ∧
      cvt.levelParams.Perm (List.range nlvls) ∧
      ExprLvEq ty' (posOf cvt.levelParams cvt.type) ∧
      Decl.TmCExact (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h₂ ty' mty := by
  let sc := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hst : (env.find? (Core.keyOf t (ixAddr a))).isSome = true :=
    hE.advStored (ixAddr a) hadv c hrec (ixAddr a) hca
  obtain ⟨ci₀, hfind₀⟩ := Option.isSome_iff_exists.mp hst
  have hκa : sc.κ (ixAddr a) = Core.keyOf t (ixAddr a) :=
    Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hfind₀
  have hne_a : sc.κ (ixAddr a) ≠ unresolvedKey := by
    rw [hκa]; exact Resolved.ne
  have hgood := hE.store.good env lim
  obtain ⟨ci2, hfind2, hptr2⟩ := hE.prefixInv.loads.getCI xa ptr h₁ h₂ cs_ci a ev_ci trivial
    hne_a (CoreGood.ofRaw (hgood.sub hsub_ci) (fun _ _ => trivial)) ha
  rw [hκa] at hfind2
  obtain ⟨v2, hld2, hci2⟩ := hptr2
  rw [hld] at hld2; injection hld2 with hv2
  cases hci2 with
  | @thm _ _ _ cvt vt hval2 _ =>
    injection hv2 with _ _ hargs2
    simp only [List.cons.injEq, and_true] at hargs2
    obtain ⟨rfl, rfl, -⟩ := hargs2
    obtain ⟨hnl2, hlt2, hperm2, htm2⟩ := hval2
    have hlen_eq : cvt.levelParams.length = nlvls := by
      have hfeq : (cvt.levelParams.length : F) = (nlvls : F) :=
        Value.field.inj (hnl2.symm.trans W.nl_eq)
      have hv1 : ZMod.val (cvt.levelParams.length : F) = cvt.levelParams.length :=
        SubstAux.val_natCast (Nat.lt_trans hlt2 (by decide))
      have hv2' : ZMod.val (nlvls : F) = nlvls :=
        SubstAux.val_natCast (Nat.lt_trans W.nlvls_lt (by decide))
      rw [← hv1, hfeq, hv2']
    have hperm_n : cvt.levelParams.Perm (List.range nlvls) := hlen_eq ▸ hperm2
    have htm2_ex : Decl.TmCExact sc.κ h₂ ty' mty := tmCExact_rekey_of_tmC W.tm_ci htm2
    have hlvEq : ExprLvEq ty' (posOf cvt.levelParams cvt.type) :=
      Tm.det ((htm2_ex 0 (fun _ => .sort .zero)).toTm) (htm2 0 (fun _ => .sort .zero))
    exact ⟨cvt, vt, hfind2, hperm_n, hlvEq, htm2_ex⟩
  | _ => simp [kciEnum] at hv2

end IxVM.Refinement.Typing.FamilyAlias
