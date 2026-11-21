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

/-- The native rule table at a `String`/`Char` operation (family `2`) names the operation `strOpOf`
reads. -/
theorem strOpOf_nativeOp (ro : Ix.Kernel.Role) (h2 : (Ix.SpecDigest.nativeOp ro).1 = 2) :
    Specs.Whnf.strOpOf (Ix.SpecDigest.nativeOp ro).2 = some ro := by
  cases ro <;> first | rfl | exact absurd h2 (by decide)

/-- The native rule table at a `BitVec` operation (family `3`) names the operation `bvOpOf`
reads. -/
theorem bvOpOf_nativeOp (ro : Ix.Kernel.Role) (h3 : (Ix.SpecDigest.nativeOp ro).1 = 3) :
    Specs.Whnf.bvOpOf (Ix.SpecDigest.nativeOp ro).2 = some ro := by
  cases ro <;> first | rfl | exact absurd h3 (by decide)

/-- The native rule table at an `Int` operation (family `6`) names the operation `intOpOf`
reads. -/
theorem intOpOf_nativeOp (ro : Ix.Kernel.Role) (h6 : (Ix.SpecDigest.nativeOp ro).1 = 6) :
    Specs.Whnf.intOpOf (Ix.SpecDigest.nativeOp ro).2 = some ro := by
  cases ro <;> first | rfl | exact absurd h6 (by decide)

theorem nativeOp_lt (ro : Ix.Kernel.Role) :
    (Ix.SpecDigest.nativeOp ro).1 < 7 ∧ (Ix.SpecDigest.nativeOp ro).2 < 17 := by
  cases ro <;> decide

theorem role_idx_lt (ro : Ix.Kernel.Role) : ro.idx < 1024 := by
  cases ro <;> decide

theorem role_of_num_plus_one_101 {ro : Ix.Kernel.Role} (h : roleNum ro + 1 = 101) :
    ro = .charUtf8Size := by
  have hsub : (ro.idx : F) = (100 : Nat) := by
    have := congrArg (· - (1 : F)) h
    simpa [roleNum] using this.trans (by norm_num : (101 : F) - 1 = (100 : Nat))
  have hidx : ro.idx = 100 := IxVM.natCast_inj (role_idx_lt ro) (by decide) hsub
  cases ro <;> first | rfl | exact absurd hidx (by decide)

/-- The operation code `natOpOf` reads is the role's `Nat` primitive code. -/
theorem natPrimOp_of_natOpOf {k : Nat} {ro : Ix.Kernel.Role}
    (h : Specs.Whnf.natOpOf k = some ro) : Specs.Nat.natPrimOp ro = some k := by
  unfold Specs.Whnf.natOpOf at h
  split at h <;> first | (cases h; rfl) | cases h

/-- The operation code `strOpOf` reads is the role's `String`/`Char` primitive code. -/
theorem strPrimOp_of_strOpOf {k : Nat} {ro : Ix.Kernel.Role}
    (h : Specs.Whnf.strOpOf k = some ro) : Specs.Nat.strPrimOp ro = some k := by
  unfold Specs.Whnf.strOpOf at h
  split at h <;> first | (cases h; rfl) | cases h

/-- The operation code `bvOpOf` reads is the role's `BitVec` primitive code. -/
theorem bvPrimOp_of_bvOpOf {k : Nat} {ro : Ix.Kernel.Role}
    (h : Specs.Whnf.bvOpOf k = some ro) : Specs.Nat.bvPrimOp ro = some k := by
  unfold Specs.Whnf.bvOpOf at h
  split at h <;> first | (cases h; rfl) | cases h

/-- The operation code `intOpOf` reads is the role's `Int` primitive code. -/
theorem intPrimOp_of_intOpOf {k : Nat} {ro : Ix.Kernel.Role}
    (h : Specs.Whnf.intOpOf k = some ro) : Specs.Nat.intPrimOp ro = some k := by
  unfold Specs.Whnf.intOpOf at h
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

end WhnfAux

/-- `KernelWhnf::prim_family`: returns a field pair `(f, op)`; a nonzero family witnesses
`PrimAt c a f op`. -/
theorem prim_family_step (c : ScopedCtx) (hc : ScopedCoreBase c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::prim_family" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.prim_family c args h r h' calls := by
  intro rc ap hargs good hrc a ha
  subst hargs
  rcases Obs.«KernelWhnf::prim_family».obs ev with
    ⟨v1, m2, cs12, m92, cs94, x_op, ev14, sg99, he131, he144, hc145⟩ |
    ⟨v1, m2, cs12, m92, cs94, x_op, ev14, sg99, he_r5, he_h5, hc_c5⟩ |
    ⟨v1, m2, cs12, m92, cs94, x_f, x_op, m151, cs162, ev14, sg99, hne146, hne5, ev164, he189,
      he202, hc203⟩ |
    ⟨v1, m2, cs12, m92, cs94, x_f, x_op, v150, m151, cs162, ev14, sg99, hne146, hne5, ev164,
      hne204, he212, he227, hc228⟩
  · exact ⟨0, 0, he131, fun h0 => (h0 rfl).elim⟩
  · exact ⟨0, 0, he_r5, fun h0 => (h0 rfl).elim⟩
  · exact ⟨0, 0, he189, fun h0 => (h0 rfl).elim⟩
  · subst hc228 he212
    rcases sg99 with ⟨hv44, he49, he62, hc63⟩ |
      ⟨hne64, hv101, he101, he_h101, hc_c101⟩ |
      ⟨cs71, v74, hne64, hne101, op88, ev73, hc90⟩
    · simp only [Value.tuple.injEq, List.cons.injEq] at he49
      exact (hne146 he49.1).elim
    · -- `r1 = 101` (`Char.utf8Size`): `(2, 7)`
      subst hc_c101 he_h101
      rcases ih.get (.roles .role_index_of) (by lt_calls) ev14 rc ap a rfl
          (good.sub fun x hx => by simp [hx]) hrc ha with h0 | ⟨ro, hro_eq, hb⟩
      · exact (hne64 h0).elim
      have hro_char : ro = .charUtf8Size :=
        WhnfAux.role_of_num_plus_one_101 (Value.field.inj (hro_eq.symm.trans hv101))
      subst hro_char
      have e0 := ObsFn.heap_extends ev14
      rcases ih.get (.roles .role_of) (by lt_calls) ev164 rc ap a rfl
          (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc)
          (Bytes.repAddressRef_heapMono₂ addrTy e0 ha) with h0 | ⟨ro', rfl, hb', hf'⟩
      · exact (hne204 h0).elim
      have hro : Ix.Kernel.Role.charUtf8Size = ro' := by
        have e := (keyOf_of_addressOf hc.env.tableWf hb).symm.trans
          (keyOf_of_addressOf hc.env.tableWf hb')
        simpa using e
      subst hro
      refine ⟨2, 7, he101, fun _ => ⟨⟨.charUtf8Size, hb', hf'⟩,
        fun h1 => absurd h1 (by decide),
        fun _ => ⟨.charUtf8Size, by
          have hv7 : ZMod.val (7 : F) = 7 := NatAux.val_natCast (by norm_num)
          rw [hv7]; rfl, hb', hf'⟩,
        fun h3 => absurd h3 (by decide),
        fun h6 => absurd h6 (by decide)⟩⟩
    · -- general role from `role_prim_family`
      subst hc90
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
        fun _ => ⟨⟨ro, hb', hf'⟩, fun h1 => ⟨ro, ?_, hb', hf'⟩,
          fun h2 => ⟨ro, ?_, hb', hf'⟩, fun h3 => ⟨ro, ?_, hb', hf'⟩,
          fun h6 => ⟨ro, ?_, hb', hf'⟩⟩⟩
      · obtain ⟨hl1, hl2⟩ := WhnfAux.nativeOp_lt ro
        have h1' : (Ix.SpecDigest.nativeOp ro).1 = 1 := by
          have := congrArg ZMod.val h1
          rwa [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).1) (by omega), NatAux.val_one]
            at this
        rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).2) (by omega)]
        exact WhnfAux.natOpOf_nativeOp ro h1'
      · obtain ⟨hl1, hl2⟩ := WhnfAux.nativeOp_lt ro
        have h2' : (Ix.SpecDigest.nativeOp ro).1 = 2 := by
          have := congrArg ZMod.val h2
          rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).1) (by omega)] at this
          have h2v : ZMod.val ((2 : Nat) : F) = 2 := NatAux.val_natCast (by norm_num)
          simpa using this.trans h2v
        rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).2) (by omega)]
        exact WhnfAux.strOpOf_nativeOp ro h2'
      · obtain ⟨hl1, hl2⟩ := WhnfAux.nativeOp_lt ro
        have h3' : (Ix.SpecDigest.nativeOp ro).1 = 3 := by
          have := congrArg ZMod.val h3
          rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).1) (by omega)] at this
          have h3v : ZMod.val ((3 : Nat) : F) = 3 := NatAux.val_natCast (by norm_num)
          simpa using this.trans h3v
        rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).2) (by omega)]
        exact WhnfAux.bvOpOf_nativeOp ro h3'
      · obtain ⟨hl1, hl2⟩ := WhnfAux.nativeOp_lt ro
        have h6' : (Ix.SpecDigest.nativeOp ro).1 = 6 := by
          have := congrArg ZMod.val h6
          rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).1) (by omega)] at this
          have h6v : ZMod.val ((6 : Nat) : F) = 6 := NatAux.val_natCast (by norm_num)
          simpa using this.trans h6v
        rw [NatAux.val_natCast (n := (Ix.SpecDigest.nativeOp ro).2) (by omega)]
        exact WhnfAux.intOpOf_nativeOp ro h6'

/-- `KernelWhnf::try_nat_dispatch_prewhnf`: the spine head-normalized (`whnf_spine`, a reduct
argument by argument), then `KernelNatPrim::try_nat_dispatch`. -/
theorem try_nat_dispatch_prewhnf_step (c : ScopedCtx) {args : List (SourceValue F)} {h h' : Heap F}
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

/-- `KernelWhnf::try_prim_dispatch`: at an empty level list, dispatches families `1` (`Nat`),
`2` (`String`/`Char`), `3` (`BitVec`), and `6` (`Int`) using the `(fam, op)` witness from
`prim_family`. -/
theorem try_prim_dispatch_step (c : ScopedCtx) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_prim_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.try_prim_dispatch c args h r h' calls := by
  intro rc f o addr lvls sp types hargs good hrc d Γ htypes a us As ha hprim hus hAs t x hr ht
  subst hargs
  rcases Obs.«KernelWhnf::try_prim_dispatch».obs ev with
    ⟨cs80, ld12, hf1, ev82, hc123⟩ |
    ⟨cs_str, ld12, _, hf2, ev_str, hc_str⟩ |
    ⟨cs_bv, ld12, _, _, hf3, ev_bv, hc_bv⟩ |
    ⟨cs_int, ld12, _, _, _, hf6, ev_int, hc_int⟩ |
    ⟨m140, ld12, _, _, _, _, he132, hm148, he159, hc160⟩ |
    ⟨v1, m177, ld12, hne161, he169, hm185, he196, hc197⟩
  · -- family 1 (`Nat`)
    subst hc123
    obtain rfl := WhnfAux.lvListRep_nil hus ld12
    have hf1' : f = 1 := Value.field.inj hf1
    obtain ⟨-, hnat, -, -, -⟩ := hprim (by rw [hf1']; exact one_ne_zero)
    obtain ⟨role, hrole, haddr, hforce⟩ := hnat hf1'
    exact ih.get (.whnf .try_nat_dispatch_prewhnf) (by lt_calls) ev82 rc addr _ sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes a o role As ha rfl hrole haddr hforce
      hAs t x hr ht
  · -- family 2 (`String` / `Char`)
    subst hc_str
    obtain rfl := WhnfAux.lvListRep_nil hus ld12
    have hf2' : f = 2 := Value.field.inj hf2
    obtain ⟨-, -, hstr, -, -⟩ := hprim (by rw [hf2']; exact WhnfAux.field_two_ne_zero)
    obtain ⟨role, hrole, haddr, hforce⟩ := hstr hf2'
    exact ih.get (.nat .try_str_dispatch) (by lt_calls) ev_str rc o sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc a
      ⟨role, WhnfAux.strPrimOp_of_strOpOf hrole, haddr, hforce⟩ d Γ htypes As hAs t x hr
      (WhnfAux.tag12_ne_zero ht)
  · -- family 3 (`BitVec`)
    subst hc_bv
    obtain rfl := WhnfAux.lvListRep_nil hus ld12
    have hf3' : f = 3 := Value.field.inj hf3
    have h3nz : (3 : F) ≠ 0 := by decide
    obtain ⟨-, -, -, hbv, -⟩ := hprim (by rw [hf3']; exact h3nz)
    obtain ⟨role, hrole, haddr, hforce⟩ := hbv hf3'
    exact ih.get (.nat .try_bitvec_dispatch) (by lt_calls) ev_bv rc o sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc a
      ⟨role, WhnfAux.bvPrimOp_of_bvOpOf hrole, haddr, hforce⟩ d Γ htypes As hAs t x hr
      (WhnfAux.tag12_ne_zero ht)
  · -- family 6 (`Int`)
    subst hc_int
    obtain rfl := WhnfAux.lvListRep_nil hus ld12
    have hf6' : f = 6 := Value.field.inj hf6
    have h6nz : (6 : F) ≠ 0 := by decide
    obtain ⟨-, -, -, -, hint⟩ := hprim (by rw [hf6']; exact h6nz)
    obtain ⟨role, hrole, haddr, hforce⟩ := hint hf6'
    exact ih.get (.nat .try_int_prim_dispatch) (by lt_calls) ev_int rc o sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc a
      ⟨role, WhnfAux.intPrimOp_of_intOpOf hrole, haddr, hforce⟩ d Γ htypes As hAs t x hr
      (WhnfAux.tag12_ne_zero ht)
  · exact (WhnfAux.tag12_absurd ht (hr.symm.trans he132)).elim
  · exact (WhnfAux.tag12_absurd ht (hr.symm.trans he169)).elim

/-- `KernelWhnf::nat_lit_to_ctor_or_self`: a `Nat` literal becomes `Nat.zero` or `Nat.succ` of
its predecessor (`Red.natLit`); any other term is returned. -/
theorem nat_lit_to_ctor_or_self_step (c : ScopedCtx) (hc : ScopedCoreBase c) {args : List (SourceValue F)}
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
      have htmc := PrimStrAux.tmc_role_const_nil hc ha hb (by resolve_key) hm125 rfl
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
      have htmc := PrimStrAux.tmc_role_const_nil hc ha hb (by resolve_key) hm261 hm213
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

/-- `KernelWhnf::lit_to_ctor_or_self`: a `Nat` or `String` literal becomes constructor form; any
other term is returned. -/
theorem lit_to_ctor_or_self_step (c : ScopedCtx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::lit_to_ctor_or_self" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.lit_to_ctor_or_self c args h r h' calls := by
  intro rc e hargs good hrc d Γ E hE
  subst hargs
  rcases Obs.«KernelWhnf::lit_to_ctor_or_self».obs ev with
    ⟨_, cs_n, _, ev_n, hc_c⟩ |
    ⟨_, cs_s, _, ev_s, hc_c⟩ |
    ⟨_, _, _, he_r, he_h, _⟩
  · subst hc_c
    exact ih.get (.whnf .nat_lit_to_ctor_or_self) (by lt_calls) ev_n rc e rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ E hE
  · subst hc_c
    exact ih.get (.nat .str_lit_to_ctor_app_or_self) (by lt_calls) ev_s rc e rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ E hE
  · subst he_r he_h; exact ⟨E, hE, .refl⟩

end IxVM.Refinement.Core
