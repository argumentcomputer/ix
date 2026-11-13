import IxVMRefinement.Whnf.Basic
import IxVMRefinement.Nat.PrimStr
import IxVMRefinement.Nat.PrimNat

/-! # Step lemmas of `KernelWhnf`: the native dispatch hooks and `Nat` literals

`prim_family` looks the head's address up in the role table twice: its index (any bound role,
`role_index_of`), whose native rule the specification table gives (`role_prim_family`,
`Ix.SpecDigest.nativeOp`), and its role in force (`role_of`); the table binds no address twice,
so the two roles are one. `try_prim_dispatch` fires the `Nat` natives (family `1`) at an empty
level list; `try_nat_dispatch_prewhnf` head-normalizes the spine first (`Red.appArg` under
`Red.appFn`) and hands it to `KernelNatPrim::try_nat_dispatch`. `nat_lit_to_ctor_or_self` takes
one constructor layer off a `Nat` literal (`Red.natLit`, the literal support from `Nat.zero` or
`Nat.succ` in force). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

namespace WhnfAux

theorem field_two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  have h2 : ZMod.val ((2 : Nat) : F) = 2 := NatAux.val_natCast (by norm_num)
  rw [Nat.cast_ofNat, h, ZMod.val_zero] at h2
  exact absurd h2 (by decide)

theorem tag12_ne_zero {t : F} (ht : t = 1 ∨ t = 2) : t ≠ 0 := by
  rcases ht with rfl | rfl
  · exact one_ne_zero
  · exact field_two_ne_zero

/-- A result tagged `1` or `2` is not one tagged `0`. -/
theorem tag12_absurd {t : F} {x y : SourceValue F} (ht : t = 1 ∨ t = 2)
    (he : (Value.tuple [.field t, x] : SourceValue F) = .tuple [.field 0, y]) : False := by
  simp only [Value.tuple.injEq, List.cons.injEq] at he
  exact tag12_ne_zero ht (Value.field.inj he.1)

/-- The native rule table at a `Nat` operation (family `1`) names the operation `natOpOf`
reads. -/
theorem natOpOf_nativeOp (ro : Ix.Kernel.Role) (h1 : (Ix.SpecDigest.nativeOp ro).1 = 1) :
    Specs.Whnf.natOpOf (Ix.SpecDigest.nativeOp ro).2 = some ro := by
  cases ro <;> first | rfl | exact absurd h1 (by decide)

theorem nativeOp_lt (ro : Ix.Kernel.Role) :
    (Ix.SpecDigest.nativeOp ro).1 < 7 ∧ (Ix.SpecDigest.nativeOp ro).2 < 17 := by
  cases ro <;> decide

/-- The operation code `natOpOf` reads is the role's `Nat` primitive code. -/
theorem natPrimOp_of_natOpOf {k : Nat} {ro : Ix.Kernel.Role}
    (h : Specs.Whnf.natOpOf k = some ro) : Specs.Nat.natPrimOp ro = some k := by
  unfold Specs.Whnf.natOpOf at h
  split at h <;> first | (cases h; rfl) | cases h

/-- **A spine of reducts**: an application's arguments reduce pointwise (`Red.appArg` under
`Red.appFn`). -/
theorem red_mkAppN_args {env : Ix.Kernel.Env .anon} {d : Nat} {As Bs : List KExpr}
    (hab : List.Forall₂ (Red env d) As Bs) :
    ∀ f : KExpr, Red env d (Ix.Kernel.Expr.mkAppN f As) (Ix.Kernel.Expr.mkAppN f Bs) := by
  induction hab with
  | nil => intro f; exact .refl
  | @cons a b l₁ l₂ hab _ ih =>
    intro f
    show Red env d (Ix.Kernel.Expr.mkAppN (.app f a) l₁) (Ix.Kernel.Expr.mkAppN (.app f b) l₂)
    exact .trans (red_mkAppN l₁ (.appArg hab)) (ih _)

/-- A level list whose cell loads as `Nil` is empty. -/
theorem lvListRep_nil {h : Heap F} {us : List KLevel} {lp : SourceValue F} (hus : LvListRep h us lp)
    (ld : loadValue h lp = .ok (.construct klevelListEnum "Nil" [])) : us = [] := by
  obtain ⟨ls, hls, hEq⟩ := hus
  have ld' : loadValue h lp =
      .ok (.construct IxVM.Refinement.KernelLevels.klevelListEnum "Nil" []) := by
    rw [← klevelListEnum_eq]; exact ld
  obtain rfl := RepList.nil_of_load hls ld'
  cases us with
  | nil => rfl
  | cons u us =>
    have h0 := hEq (fun _ => 0)
    simp [Ix.Kernel.Level.EvalEqList] at h0

/-- **`prim_family`, with its result's shape**: a pair of field elements, and the registered
claim. -/
theorem prim_family_full (c : Ctx) (hc : CoreFacts c) {rc ap : SourceValue F} {a : Bytes.Address}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::prim_family" [rc, ap] h r h' calls) (ih : IH c calls)
    (good : Good c calls) (hrc : c.rc h rc) (ha : RepAddr h a ap) :
    ∃ f o : F, r = .tuple [.field f, .field o] ∧ (f ≠ 0 →
      (∃ role, c.t.addressOf? role = some (ixAddr a) ∧ c.inForce role) ∧
      (f = 1 → ∃ role, Specs.Whnf.natOpOf (ZMod.val o) = some role ∧
        c.t.addressOf? role = some (ixAddr a) ∧ c.inForce role)) := by
  rcases Obs.«KernelWhnf::prim_family».obs ev with
    ⟨v1, m2, cs12, m92, cs94, x_op, ev14, sg99, he131, he144, hc145⟩ |
    ⟨v1, m2, cs12, m92, cs94, x_f, x_op, m151, cs162, ev14, sg99, hne146, ev164, he189, he202,
      hc203⟩ |
    ⟨v1, m2, cs12, m92, cs94, x_f, x_op, v150, m151, cs162, ev14, sg99, hne146, ev164, hne204,
      he212, he227, hc228⟩
  · exact ⟨0, 0, he131, fun h0 => (h0 rfl).elim⟩
  · exact ⟨0, 0, he189, fun h0 => (h0 rfl).elim⟩
  · subst hc228 he212
    rcases sg99 with ⟨hv44, he49, he62, hc63⟩ |
      ⟨cs71, v74, hne64, op88, ev73, hc90⟩
    · simp only [Value.tuple.injEq, List.cons.injEq] at he49
      exact (hne146 he49.1).elim
    · subst hc90
      rcases ih.get (.roles .role_index_of) (by lt_calls) ev14 rc ap a rfl
          (good.sub fun x hx => by simp [hx]) hrc ha with h0 | ⟨ro, rfl, hb⟩
      · exact (hne64 h0).elim
      obtain rfl := Lib.sub_one_inv op88
      obtain ⟨hpf, rfl⟩ := ih.get (.roles .role_prim_family) (by lt_calls) ev73 ro
        (by rw [add_sub_cancel_right])
      have e0 := ObsFn.heap_extends ev14
      rcases ih.get (.roles .role_of) (by lt_calls) ev164 rc ap a rfl
          (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc)
          (Bytes.repAddressRef_heapMono₂ addrTy e0 ha) with h0 | ⟨ro', rfl, hb', hf'⟩
      · exact (hne204 h0).elim
      have hro : ro = ro' := by
        have e := (keyOf_of_addressOf hc.env.tableWf hb).symm.trans
          (keyOf_of_addressOf hc.env.tableWf hb')
        simpa using e
      subst hro
      refine ⟨((Ix.SpecDigest.nativeOp ro).1 : F), ((Ix.SpecDigest.nativeOp ro).2 : F), hpf,
        fun _ => ⟨⟨ro, hb', hf'⟩, fun h1 => ⟨ro, ?_, hb', hf'⟩⟩⟩
      obtain ⟨hl1, hl2⟩ := nativeOp_lt ro
      have h1' : (Ix.SpecDigest.nativeOp ro).1 = 1 := by
        have := congrArg ZMod.val h1
        rwa [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).1) (by omega), NatAux.val_one]
          at this
      rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).2) (by omega)]
      exact natOpOf_nativeOp ro h1'

end WhnfAux

/-- `KernelWhnf::prim_family`: a nonzero family is a role bound to the address and in force;
family `1` is the `Nat` operation `natOpOf op`. -/
theorem prim_family_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::prim_family" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.prim_family c args h r h' calls := by
  intro rc ap hargs good hrc a f op ha hr hf
  subst hargs
  obtain ⟨f', o', hr', hspec⟩ := WhnfAux.prim_family_full c hc ev ih good hrc ha
  rw [hr] at hr'
  simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq, and_true] at hr'
  obtain ⟨rfl, rfl⟩ := hr'
  exact hspec hf

/-- `KernelWhnf::try_nat_dispatch_prewhnf`: the spine head-normalized (`whnf_spine`, a reduct
argument by argument), then `KernelNatPrim::try_nat_dispatch`. -/
theorem try_nat_dispatch_prewhnf_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_nat_dispatch_prewhnf" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.try_nat_dispatch_prewhnf c args h r h' calls := by
  intro rc ha op sp types hargs good hrc d Γ htypes a o role As hha hop hnat haddr hforce hAs t x
    hr ht
  subst hargs hop
  obtain ⟨v1, m2, cs12, cs42, ev14, ev44, hc85⟩ := Obs.«KernelWhnf::try_nat_dispatch_prewhnf».obs ev
  subst hc85
  obtain ⟨Bs, hBs, hreds⟩ := ih.get (.whnf .whnf_spine) (by lt_calls) ev14 rc sp types rfl
    (good.sub fun x hx => by simp [hx]) hrc d Γ htypes As hAs
  have e0 := ObsFn.heap_extends ev14
  obtain ⟨E', hE', hred⟩ := ih.get (.nat .try_nat_dispatch) (by lt_calls) ev44 rc ha o v1 types
    rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) a
    (Bytes.repAddressRef_heapMono₂ addrTy e0 hha)
    ⟨role, WhnfAux.natPrimOp_of_natOpOf hnat, haddr, hforce⟩ d Γ (types_mono e0 htypes) Bs hBs t
    x hr (WhnfAux.tag12_ne_zero ht)
  exact ⟨E', hE', .trans (WhnfAux.red_mkAppN_args hreds _) hred⟩

/-- `KernelWhnf::try_prim_dispatch`: at an empty level list, a head the role table binds to a
`Nat` operation in force (`prim_family`'s family `1`) goes to `try_nat_dispatch_prewhnf`; any
other head answers `0`. -/
theorem try_prim_dispatch_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_prim_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.try_prim_dispatch c args h r h' calls := by
  intro rc addr lvls sp types hargs good hrc d Γ htypes a us As ha hus hAs t x hr ht
  subst hargs
  rcases Obs.«KernelWhnf::try_prim_dispatch».obs ev with
    ⟨m21, cs31, x_op, cs80, ld12, ev33, ev82, hc123⟩ |
    ⟨m21, cs31, x_fam, x_op, m140, ld12, ev33, hne124, he132, hm148, he159, hc160⟩ |
    ⟨v1, m177, ld12, hne161, he169, hm185, he196, hc197⟩
  · subst hc123
    obtain rfl := WhnfAux.lvListRep_nil hus ld12
    obtain ⟨f, o, hfo, hspec⟩ := WhnfAux.prim_family_full c hc ev33 (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) hrc ha
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hfo
    obtain ⟨hf, rfl⟩ := hfo
    have hf1 : f = 1 := (Value.field.inj hf).symm
    obtain ⟨-, hnat⟩ := hspec (by rw [hf1]; exact one_ne_zero)
    obtain ⟨role, hrole, haddr, hforce⟩ := hnat hf1
    have e0 := ObsFn.heap_extends ev33
    exact ih.get (.whnf .try_nat_dispatch_prewhnf) (by lt_calls) ev82 rc addr _ sp types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) a o role
      As (Bytes.repAddressRef_heapMono₂ addrTy e0 ha) rfl hrole haddr hforce (tml_mono e0 hAs) t x
      hr ht
  · exact (WhnfAux.tag12_absurd ht (hr.symm.trans he132)).elim
  · exact (WhnfAux.tag12_absurd ht (hr.symm.trans he169)).elim

/-- `KernelWhnf::nat_lit_to_ctor_or_self`: a `Nat` literal becomes `Nat.zero` or `Nat.succ` of
its predecessor (`Red.natLit`); any other term is returned. -/
theorem nat_lit_to_ctor_or_self_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::nat_lit_to_ctor_or_self" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.nat_lit_to_ctor_or_self c args h r h' calls := by
  intro rc e hargs good hrc d Γ E hE
  subst hargs
  rcases Obs.«KernelWhnf::nat_lit_to_ctor_or_self».obs ev with
    ⟨x_klimbs, m47, cs58, v81, m84, cs92, v96, m105, cs113, m117, ld12, ev60, he77, hm76, ev115,
      ev94, hm125, hc129⟩ |
    ⟨x_klimbs, v46, m47, cs58, v134, m135, cs145, v148, m150, cs158, m170, m203, v217, m220, cs228,
      v232, m241, cs249, m253, ld12, ev60, hne130, ev160, ev147, hm180, hm213, ev251, ev230, hm261,
      he269, hm268, hc289⟩ |
    ⟨x_lit, ld12, hne290, he295, he296, hc297⟩ |
    ⟨v1, ld12, hne298, he303, he304, hc305⟩
  · -- the literal `0`: `Nat.zero`
    subst hc129 hm76 he77
    rcases hE.lit_of_load ld12 with ⟨lp, limbs, hx, hrep, hcan, rfl⟩ | ⟨bp, bytes, s, hx, -, -, -⟩
    · simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hx
      subst hx
      have hz := ih.get (.nat .klimbs_is_zero) (by lt_calls) ev60 x_klimbs rfl
        (good.sub fun x hx => by simp [hx]) _ ⟨limbs, hrep, rfl⟩
      have h0 : limbsVal limbs = 0 := by
        by_contra hne
        rw [ite_eq_right hne] at hz
        exact field_one_ne_zero hz
      have e0 := ObsFn.heap_extends ev60
      obtain ⟨hv96, e1⟩ := ih.get (.roles .role_nat_zero) (by lt_calls) ev115 rfl
      subst hv96 e1
      obtain ⟨a, ha, hb, hf⟩ := ih.get (.roles .role_addr) (by lt_calls) ev94 rc .natZero rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc)
      have htmc := PrimStrAux.tmc_role_const_nil hc ha hb hm125 rfl
      refine ⟨_, htmc d Γ, ?_⟩
      rw [h0]
      exact .natLit (PrimNat.natLit_of_natBlock hc hf (by decide) (by decide) (by decide))
    · simp at hx
  · -- a nonzero literal: `Nat.succ` of the predecessor
    subst hc289 hm268 he269
    rcases hE.lit_of_load ld12 with ⟨lp, limbs, hx, hrep, hcan, rfl⟩ | ⟨bp, bytes, s, hx, -, -, -⟩
    · simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hx
      subst hx
      have hz := ih.get (.nat .klimbs_is_zero) (by lt_calls) ev60 x_klimbs rfl
        (good.sub fun x hx => by simp [hx]) _ ⟨limbs, hrep, rfl⟩
      have hn0 : limbsVal limbs ≠ 0 := fun h0 => hne130 (by rw [hz, ite_eq_left h0])
      have e0 := ObsFn.heap_extends ev60
      obtain ⟨l1, hl1, hv1, -⟩ := ih.get (.nat .klimbs_dec) (by lt_calls) ev160 x_klimbs rfl
        (good.sub fun x hx => by simp [hx]) _
        ⟨limbs, repList_heapMono₂ _ repU64_heapMono₂ e0 hrep, rfl⟩
      obtain ⟨l2, hl2, hv2, hc2⟩ := ih.get (.nat .klimbs_normalize) (by lt_calls) ev147 v148 rfl
        (good.sub fun x hx => by simp [hx]) _ ⟨l1, hl1, hv1⟩
      have esn : Heap.Extends m135 m170 := by rw [hm180]; exact Heap.Extends.snoc _ _
      have hlit : Tm c.κ d Γ m170 0 (.lit (.natVal (limbsVal l2)))
          (.ptr (.enum kexprEnum) m135.length) := by
        subst hm180
        exact .litNat List.getElem?_concat_length
          (repList_heapMono₂ _ repU64_heapMono₂ (Heap.Extends.snoc _ _) hl2) hc2
      obtain ⟨hv232, e1⟩ := ih.get (.roles .role_nat_succ) (by lt_calls) ev251 rfl
      subst hv232 e1
      have ext := e0.trans ((ObsFn.heap_extends ev160).trans ((ObsFn.heap_extends ev147).trans esn))
      obtain ⟨a, ha, hb, hf⟩ := ih.get (.roles .role_addr) (by lt_calls) ev230 rc .natSucc rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc)
      have htmc := PrimStrAux.tmc_role_const_nil hc ha hb hm261 hm213
      have e3 : Heap.Extends m220 m203 := by
        rw [hm213, hm261]; exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
      have e2 := (ObsFn.heap_extends ev230).trans e3
      refine ⟨.app (.const (.role .natSucc) []) (.lit (.natVal (limbsVal l2))),
        Tm.store_app (htmc d Γ) (hlit.mono e2), ?_⟩
      rw [hv2]
      obtain ⟨k, hk⟩ : ∃ k, limbsVal limbs = k + 1 := ⟨limbsVal limbs - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel]
      exact .natLit (PrimNat.natLit_of_natBlock hc hf (by decide) (by decide) (by decide))
    · simp at hx
  · subst he295 he296; exact ⟨E, hE, .refl⟩
  · subst he303 he304; exact ⟨E, hE, .refl⟩

end IxVM.Refinement.Core
