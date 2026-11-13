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

end IxVM.Refinement.Core
