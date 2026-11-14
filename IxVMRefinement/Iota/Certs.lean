import IxVMRefinement.Iota.Basic

/-! # ι's telescope certificates (`iota_certs`)

`KernelWhnf::iota_certs` gives `Red.iota`'s two licensed walks: a walk whose slots all have a
`never` datum (`slots_never`) is all `Certs.skip`s; otherwise every argument is certified
(`certs_all`, an unlicensed walk, which is also a licensed one).

`slots_never` is told the walk's length as a field element, and on that path the argument list
is not an argument of any call, so its length is not bounded by the derivation: the spec
takes the bound (`< 2^39`) as a hypothesis. The caller (`red_iota`) passes both lists to
`iota_certs`, so the bound follows from its own calls (`RomBound.bounded_length_lt`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

/-- Instantiating a bound variable keeps the binder data of a telescope. -/
theorem forallsNever_instantiate1 (a : KExpr) :
    ∀ (n : Nat) (b : KExpr) (k : Nat),
      Specs.Whnf.forallsNever n b → Specs.Whnf.forallsNever n (b.instantiate1 a k) := by
  intro n
  induction n with
  | zero => intro _ _ _; trivial
  | succ n ih =>
    intro b k hb
    cases b with
    | forallE ty body m =>
      obtain ⟨hm, hb'⟩ := hb
      exact ⟨hm, ih body (k + 1) hb'⟩
    | _ => exact (hb : False).elim

/-- **A walk whose slots all have the datum `never`** is a licensed certificate of skips. -/
theorem certsR_of_forallsNever {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) (T : KExpr),
      Specs.Whnf.forallsNever As.length T → Specs.Whnf.CertsR env d true T As
  | [], _, _ => .nil
  | A :: As, T, hT => by
    cases T with
    | forallE ty body m =>
      obtain ⟨hm, hb⟩ := hT
      exact .skip rfl hm (certsR_of_forallsNever As _ (forallsNever_instantiate1 A _ body 0 hb))
    | _ => exact (hT : False).elim

/-- An unlicensed certificate is a licensed one (it uses no skip). -/
theorem CertsR.lic_true {env : Ix.Kernel.Env .anon} {d : Nat} {T : KExpr} {As : List KExpr}
    (hc : Specs.Whnf.CertsR env d false T As) : Specs.Whnf.CertsR env d true T As := by
  induction hc with
  | nil => exact .nil
  | skip hl _ _ _ => exact absurd hl (by decide)
  | cert hi hd _ ih => exact .cert hi hd ih
  | red hr _ ih => exact .red hr ih

/-- The first walk of `iota_certs` (the recursor's), from its `let`-bound segment. -/
theorem iota_certs_seg {c : Ctx} {calls cs99 : List (Call F)} (ih : IH c calls)
    (good : Good c calls) (hsub : ∀ z ∈ cs99, z ∈ calls) (hle : cs99.length ≤ calls.length)
    {rc rt ra cty clvls ma nc types : SourceValue F} {h m97 : Heap F} {d : Nat}
    {Γ : Nat → KExpr} {RT : KExpr} {RA : List KExpr}
    (sg : Obs.«KernelWhnf::iota_certs».Seg1 rc rt ra (.field (RA.length : F)) cty clvls ma nc
      types h (.field 1) m97 cs99)
    (hrc : c.rc h rc) (htypes : c.types Γ h d types) (hRT : c.tmc h RT rt)
    (hRA : c.tml d Γ h RA ra) (hRAb : RA.length < 2 ^ 39) :
    Specs.Whnf.CertsR c.env d true RT RA ∧ Heap.Extends h m97 := by
  rcases sg with ⟨m2, cs13, ev15, he36, he37, hc38⟩ |
    ⟨v1, m2, cs13, cs46, m76, ev15, hne39, hm84, ev48, hc95⟩
  · subst he37 hc38
    have hn := ih.get (.whnf .slots_never)
      (by simp only [List.length_cons] at hle; omega) ev15 rt _ rfl
      (good.sub fun z hz => hsub z (by simp [hz])) d Γ 0 RT _ (hRT d Γ) rfl
      NatAux.field_one_ne_zero
    rw [NatAux.val_natCast (n := RA.length) (by omega)] at hn
    exact ⟨certsR_of_forallsNever RA RT hn, ObsFn.heap_extends ev15⟩
  · subst hm84 hc95
    have ext : Heap.Extends h (m2 ++ [.construct kexprListEnum "Nil" []]) :=
      (ObsFn.heap_extends ev15).trans (Heap.Extends.snoc _ _)
    have hcr := ih.get (.whnf .certs_all)
      (by simp only [List.length_cons, List.length_append] at hle; omega) ev48 rc rt ra _ types
      rfl (good.sub fun z hz => hsub z (by simp [hz])) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) RT [] RA ((hRT d Γ).mono ext) (TmL.store_nil m2) (tml_mono ext hRA)
      NatAux.field_one_ne_zero
    rw [Ix.Kernel.Expr.instantiateList_nil] at hcr
    exact ⟨CertsR.lic_true hcr, ext.trans (ObsFn.heap_extends ev48)⟩

/-- **`KernelWhnf::iota_certs`**: the recursor's walk, then the constructor's, each all skips at `never` slots or certified. -/
theorem iota_certs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::iota_certs" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.iota_certs c args h r h' calls := by
  intro rc rt ra nr cty clvls ma nc types hargs good hrc d Γ htypes RT RA CT cus MA hRT hRA hnr
    hCT hcus hMA hnc hRAb hMAb hr0
  subst hargs hnr hnc
  rcases Obs.«KernelWhnf::iota_certs».obs ev with
    ⟨m97, cs99, v119, m120, cs130, m150, cs161, sg104, ev132, ev163, he184, he185, hc186⟩ |
    ⟨m97, cs99, v119, m120, cs130, v149, m150, cs161, cs194, m224, sg104, ev132, ev163, hne187,
      hm232, ev196, hc243⟩ |
    ⟨v96, m97, cs99, sg104, hne244, he248, he249, hc250⟩
  · subst hc186
    obtain ⟨h1, e0⟩ := iota_certs_seg ih good (fun z hz => by simp [hz])
      (by simp only [List.length_append]; omega) sg104 hrc htypes hRT hRA hRAb
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev132 cty clvls rfl
      (good.sub fun z hz => by simp [hz]) Γ 0 CT cus ((hCT 0 Γ).mono e0) (LvListRep.mono e0 hcus)
    have hn := ih.get (.whnf .slots_never) (by lt_calls) ev163 v119 _ rfl
      (good.sub fun z hz => by simp [hz]) 0 Γ 0 _ _ hinst rfl NatAux.field_one_ne_zero
    rw [NatAux.val_natCast (n := MA.length) (by omega)] at hn
    exact ⟨h1, certsR_of_forallsNever MA _ hn⟩
  · subst hm232 hc243
    obtain ⟨h1, e0⟩ := iota_certs_seg ih good (fun z hz => by simp [hz])
      (by simp only [List.length_append]; omega) sg104 hrc htypes hRT hRA hRAb
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev132 cty clvls rfl
      (good.sub fun z hz => by simp [hz]) Γ 0 CT cus ((hCT 0 Γ).mono e0) (LvListRep.mono e0 hcus)
    have e1 := ObsFn.heap_extends ev132
    have ext2 : Heap.Extends m120 (m150 ++ [.construct kexprListEnum "Nil" []]) :=
      (ObsFn.heap_extends ev163).trans (Heap.Extends.snoc _ _)
    have ext := e0.trans (e1.trans ext2)
    have hcr := ih.get (.whnf .certs_all) (by lt_calls) ev196 rc v119 ma _ types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) _ []
      MA ((hinst.of_depth_zero d).mono ext2) (TmL.store_nil m150) (tml_mono ext hMA) hr0
    rw [Ix.Kernel.Expr.instantiateList_nil] at hcr
    exact ⟨h1, CertsR.lic_true hcr⟩
  · exact absurd he248 hr0

/-! ## `iota_cmp` -/

/-- **`KernelWhnf::iota_cmp`**: peels the recursor's telescope to the major premise's domain
(`pi_peel`), reads its constant head (`collect_spine`), compares the constructor's levels against
its levels (`level_list_eq`) and the constructor's parameters against its leading arguments
(`de_args`), and when the family has indices (`nix ≠ 0`), computes the constructor's residual type
(`expr_inst_levels`, `pi_residual`), reads its constant head, and compares the trailing index
arguments (`de_args`). -/
theorem iota_cmp_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::iota_cmp" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.iota_cmp c args h r h' calls := by
  intro rc rt pre mi cty clvls cnp ma ni types hargs good hrc d Γ htypes
    RT PRE m CT cus np MA nix hRT hPRE hmi hCT hcus hcnp hMA hni hr0
  subst hargs hmi hcnp hni
  match Obs.«KernelWhnf::iota_cmp».obs ev with
  | .n1_bind_Const_n1_n1_other_n1_bind_other (he529 := he0) .. => exact absurd he0 hr0
  | .n1_bind_Const_n1_n1_other_other (he536 := he0) .. => exact absurd he0 hr0
  | .n1_bind_Const_n1_other (he543 := he0) .. => exact absurd he0 hr0
  | .n1_bind_Const_other (he550 := he0) .. => exact absurd he0 hr0
  | .n1_bind_other (he557 := he0) .. => exact absurd he0 hr0
  | .other (he564 := he0) .. => exact absurd he0 hr0
  | .n1_bind_Const_n1_n1_n0 m2 cs13 m35 x_md m73 cs84 x_mdh x_mda w130 x_mlvls m142 cs153 m177
      cs188 v192 v193 m203 cs211 m231 cs239 hm43 ev15 ev86 ld122 ev155 ev213 ev241 ev190 hv282
      he283 he284 hc285 =>
    subst hm43 hc285
    have hn0 : nix = 0 := Value.field.inj hv282
    have e0 : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
    have e15 := ObsFn.heap_extends ev15
    have e86 := ObsFn.heap_extends ev86
    have e155 := ObsFn.heap_extends ev155
    have e213 := ObsFn.heap_extends ev213
    have e241 := ObsFn.heap_extends ev241
    have H73 := e0.trans (e15.trans e86)
    have H142 := H73.trans e155
    have H231 := H142.trans (e213.trans e241)
    obtain ⟨MD, hMD, hpi⟩ := ih.get (.whnf .pi_peel) (by lt_calls) ev15 rt pre _ (.field m) rfl
      (good.sub fun z hz => by simp [hz]) d Γ RT [] PRE m
      (by simp [List.length_nil]; exact (hRT d Γ).mono e0) (TmL.store_nil h) (tml_mono e0 hPRE)
      rfl x_md rfl
    rw [Ix.Kernel.Expr.instantiateList_nil] at hpi
    obtain ⟨hd0, sp0, MDH, MDA, he1, hMDH, hMDA, rfl⟩ := ih.get (.subst .collect_spine)
      (by lt_calls) ev86 x_md rfl (good.sub fun z hz => by simp [hz]) d Γ 0 MD hMD
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨ma0, mus, rfl, -, hmus⟩ := hMDH.const_of_load ld122
    have hlveq := ih.get (.defEq .level_list_eq) (by lt_calls) ev155 clvls x_mlvls rfl
      (good.sub fun z hz => by simp [hz]) cus mus (LvListRep.mono H73 hcus) hmus
      NatAux.field_one_ne_zero
    obtain ⟨-, htakeMA⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev213)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono H142 hMA)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at htakeMA
    obtain ⟨-, htakeMDA⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev241)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono (e155.trans e213) hMDA)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at htakeMDA
    have hdeP := ih.get (.defEq .de_args) (by lt_calls) ev190 rc v192 v193 types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono H231 hrc) d Γ (types_mono H231 htypes)
      (MA.take (ZMod.val np)) (MDA.take (ZMod.val np)) (tml_mono e241 htakeMA) htakeMDA
      NatAux.field_one_ne_zero
    refine ⟨_, c.κ (ixAddr ma0), mus, hpi, by rw [getAppFn_mkAppN]; rfl, hlveq, ?_,
      fun hne => (hne hn0).elim⟩
    rw [getAppArgs_mkAppN]
    exact hdeP
  | .n1_bind_Const_n1_n1_other_n1_bind_Const m2 cs13 m35 x_md m73 cs84 x_mdh x_mda w130 x_mlvls
      m142 cs153 m177 cs188 v192 v193 m203 cs211 m231 cs239 m291 cs302 v305 m309 cs317 m344 x_res
      m375 cs386 x_rh x_ra w432 w433 cs447 v451 v452 m462 cs470 m490 cs498 hm43 ev15 ev86 ld122
      ev155 ev213 ev241 ev190 hne286 ev319 hm352 ev304 ev388 ld424 ev472 ev500 ev449 hc524 =>
    subst hm43 hm352 hc524
    have e0 : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
    have e15 := ObsFn.heap_extends ev15
    have e86 := ObsFn.heap_extends ev86
    have e155 := ObsFn.heap_extends ev155
    have e213 := ObsFn.heap_extends ev213
    have e241 := ObsFn.heap_extends ev241
    have e190 := ObsFn.heap_extends ev190
    have e319 := ObsFn.heap_extends ev319
    have e352 : Heap.Extends m309 (m309 ++ [.construct kexprListEnum "Nil" []]) :=
      Heap.Extends.snoc _ _
    have e304 := ObsFn.heap_extends ev304
    have e388 := ObsFn.heap_extends ev388
    have e472 := ObsFn.heap_extends ev472
    have e500 := ObsFn.heap_extends ev500
    have H73 := e0.trans (e15.trans e86)
    have H142 := H73.trans e155
    have H231 := H142.trans (e213.trans e241)
    have H177 := H231.trans e190
    have H344 := H177.trans (e319.trans e352)
    have F462 := e155.trans (e213.trans (e241.trans (e190.trans
      (e319.trans (e352.trans (e304.trans (e388.trans e472)))))))
    have H490 := H344.trans (e304.trans (e388.trans (e472.trans e500)))
    obtain ⟨MD, hMD, hpi⟩ := ih.get (.whnf .pi_peel) (by lt_calls) ev15 rt pre _ (.field m) rfl
      (good.sub fun z hz => by simp [hz]) d Γ RT [] PRE m
      (by simp [List.length_nil]; exact (hRT d Γ).mono e0) (TmL.store_nil h) (tml_mono e0 hPRE)
      rfl x_md rfl
    rw [Ix.Kernel.Expr.instantiateList_nil] at hpi
    obtain ⟨hd0, sp0, MDH, MDA, he1, hMDH, hMDA, rfl⟩ := ih.get (.subst .collect_spine)
      (by lt_calls) ev86 x_md rfl (good.sub fun z hz => by simp [hz]) d Γ 0 MD hMD
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨ma0, mus, rfl, -, hmus⟩ := hMDH.const_of_load ld122
    have hlveq := ih.get (.defEq .level_list_eq) (by lt_calls) ev155 clvls x_mlvls rfl
      (good.sub fun z hz => by simp [hz]) cus mus (LvListRep.mono H73 hcus) hmus
      NatAux.field_one_ne_zero
    obtain ⟨-, htakeMA⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev213)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono H142 hMA)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at htakeMA
    obtain ⟨-, htakeMDA⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev241)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono (e155.trans e213) hMDA)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at htakeMDA
    have hdeP := ih.get (.defEq .de_args) (by lt_calls) ev190 rc v192 v193 types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono H231 hrc) d Γ (types_mono H231 htypes)
      (MA.take (ZMod.val np)) (MDA.take (ZMod.val np)) (tml_mono e241 htakeMA) htakeMDA
      NatAux.field_one_ne_zero
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev319 cty clvls rfl
      (good.sub fun z hz => by simp [hz]) Γ 0 CT cus ((hCT 0 Γ).mono H177) (LvListRep.mono H177 hcus)
    obtain ⟨RES, hRES, hres⟩ := ih.get (.whnf .pi_residual) (by lt_calls) ev304 v305 ma _ rfl
      (good.sub fun z hz => by simp [hz]) d Γ
      (CT.instantiateLevelParams (List.range cus.length) cus) [] MA
      (by simp [List.length_nil]; exact (hinst.of_depth_zero d).mono e352)
      (TmL.store_nil m309) (tml_mono H344 hMA) x_res rfl
    rw [Ix.Kernel.Expr.instantiateList_nil] at hres
    obtain ⟨hd1, sp1, RH, RA, he2, hRH, hRA, rfl⟩ := ih.get (.subst .collect_spine)
      (by lt_calls) ev388 x_res rfl (good.sub fun z hz => by simp [hz]) d Γ 0 RES hRES
    obtain ⟨rfl, rfl⟩ := tuple2_inj he2
    obtain ⟨ra0, rus, rfl, -, -⟩ := hRH.const_of_load ld424
    obtain ⟨-, hdropRA, -⟩ := Lib.Lists.drop_spec (ZMod.val np) (t := kexprTy) (R := TmE c.κ d Γ)
      rfl (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev472)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hRA)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hdropRA
    obtain ⟨-, hdropMDA, -⟩ := Lib.Lists.drop_spec (ZMod.val np) (t := kexprTy) (R := TmE c.κ d Γ)
      rfl (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev500)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono F462 hMDA)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hdropMDA
    have hdeI := ih.get (.defEq .de_args) (by lt_calls) ev449 rc v451 v452 types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono H490 hrc) d Γ (types_mono H490 htypes)
      (RA.drop (ZMod.val np)) (MDA.drop (ZMod.val np)) (tml_mono (e472.trans e500) hdropRA)
      (tml_mono e500 hdropMDA) hr0
    refine ⟨_, c.κ (ixAddr ma0), mus, hpi, by rw [getAppFn_mkAppN]; rfl, hlveq, ?_,
      fun _ => ⟨_, hres, ?_⟩⟩
    · rw [getAppArgs_mkAppN]; exact hdeP
    · rw [getAppArgs_mkAppN, getAppArgs_mkAppN]; exact hdeI

end IxVM.Refinement.Core
