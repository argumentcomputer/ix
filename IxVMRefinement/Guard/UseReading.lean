import IxVMRefinement.Guard.UseStore
import IxVMRefinement.Guard.UseWalk

/-! # A use's observation over the run's store, from the traced walk

`Core.GuardWalk.proj_guard_traced_ih` gives, for a `KernelInfer::proj_guard` run that took the
checked walk: the guard level as the fold of the field levels under the flags, the flags against
the stored constructor type, the run's constructor load, the raw telescope behind its type
pointer, and the classifier's field traces of that telescope with the zero-set agreement.

* `projGuardUse_runStore`: over a run store that holds the run's hashed records, those data are
  the use-site observation `Ix.Kernel.ProjGuardUse` over the store's raw dictionary, at the
  constructor's raw telescope read from the store. The trace answers are read in the store as
  for the install (`typeAnswer_runStore`, `valueAnswer_runStore`), and the telescope by
  `ctorRaw_runStore`.

The statement takes the traced data as hypotheses, so it does not depend on which facts of the
context the walk was read from.

* `peelRed_stripPis_sort_any`: a head reduction of a `∀`-telescope that strips to a sort, peeled
  to a sort, reaches that sort, whatever the number of binders peeled.
* `isInductiveProp_one_of_table`: at a stored projection table whose sort tests zero, the run's
  own `is_inductive_prop` call answers `1`. The table's tower head (the store invariant's
  `ProjOkT`) names the member's inductive and its declared sort, the run's `get_ci_iprj` load
  reads that inductive, and the call's spec (from the registry's induction hypothesis) reads the
  declared sort, which is zero at every assignment.
* `projGuardUse_of_run`: **the use, read inside the registry's induction**: from the facts stated
  before the registry and the induction hypothesis, a `proj_guard` run at a stored table whose
  sort tests zero is the use observation over every run store of the run.
-/

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (RawExprRep RawTypeAt RawDeltaAt RawFieldTraces)

/-- **The use-site observation over the run's store** (module docstring). -/
theorem projGuardUse_runStore {c : ScopedCtx} {calls : List (Call F)} {E' : Ixon.Env}
    (hS : LoadedReads.RunStore calls E') (hcov : LoadedReads.HashedRecordsStored calls E')
    (hbound : IxVM.Consistency.Bounded calls)
    {b : Bytes.Address} {bp : SourceValue F} {i : F} {h : Heap F}
    (hb : Bytes.RepAddressRef addrTy h b bp)
    {T : KExpr} {nP f : Nat} {g : KLevel}
    {lus : List KLevel} {flags : List Bool} {sigs : List KLevel} {S : KExpr}
    {ptr x_cty w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F} {m : Heap F} {cs₀ : List (Call F)}
    (hfold : g = (List.range f).foldl
      (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero)
        else acc) (lus.getD f .zero))
    (hflags : ∀ j, j < f → Ix.Kernel.structUsedLater T nP j = true →
      flags.getD j false = true)
    (load : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h ptr m cs₀)
    (inside : ∀ cl ∈ cs₀, cl ∈ calls)
    (ld : loadValue m ptr = .ok (.construct kciEnum "Ctor" [w₁, x_cty, w₃, w₄, w₅, w₆, w₇, w₈]))
    (physical : RawExprRep (Core.keyOf GuardRaw.addressTable) m 0 S x_cty)
    (traces : RawFieldTraces (RawTypeAt c (Core.keyOf GuardRaw.addressTable) calls)
      (RawDeltaAt c (Core.keyOf GuardRaw.addressTable) calls) nP (f + 1) [] S sigs)
    (zeros : ∀ j, j ≤ f → ∀ φ : Ix.Kernel.LevelParam → Nat,
      Ix.Kernel.Level.eval φ (lus.getD j .zero) = 0 ↔
        Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0) :
    ∃ raw, Guard.ctorRaw E' (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.ProjGuardUse (GuardRaw.ofStore E') raw T nP f g := by
  have hpar := loadParentsHeld_of_runStore hS hcov
  obtain ⟨fuel, walked⟩ := traces.fieldSignatures_erased (look := GuardRaw.ofStore E')
    (fun _ _ _ answer =>
      typeAnswer_runStore hS hcov hpar hbound (fun _ member => member) answer)
    (fun _ _ _ answer =>
      valueAnswer_runStore hS hcov hpar hbound (fun _ member => member) answer)
  exact ⟨S.eraseMeta,
    ctorRaw_runStore hS hcov (bounded_sub inside hbound) inside load hb ld
      (Heap.Extends.refl m) physical,
    ⟨lus, sigs, fuel, fun j => flags.getD j false, walked, zeros, hflags, hfold⟩⟩

end IxVM.Refinement.Guard

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- **A head reduction, peeled to a sort, of a `∀`-telescope that strips to a sort reaches that
sort**, at any number of peeled binders: a reduct of a sort or of a `∀` is itself. -/
theorem peelRed_stripPis_sort_any {env : Ix.Kernel.Env .anon} {Γ' : Nat → KExpr} (n : Nat) :
    ∀ {T : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {σ u : KLevel} {d k : Nat},
      T.stripPis n = some (bs, .sort σ) →
      Specs.Infer.PeelRed env Γ' d T k (.sort u) → u = σ := by
  induction n with
  | zero =>
    intro T bs σ u d k hs hpeel
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    cases hpeel with
    | done hred => exact Ix.Kernel.Rules.Red.sort_eq hred
    | step hred hrest =>
      have hrig := Ix.Kernel.Rules.Red.rigid hred rfl
      exact nomatch hrig
  | succ n ih =>
    intro T bs σ u d k hs hpeel
    cases T with
    | forallE dom body m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs0, res0⟩, hs0, heq⟩ := hs
      obtain ⟨-, rfl⟩ : (dom, m) :: bs0 = bs ∧ res0 = .sort σ := by simpa using heq
      cases hpeel with
      | done hred =>
        have hrig := Ix.Kernel.Rules.Red.rigid hred rfl
        exact nomatch hrig
      | @step _ k' _ body' _ m' hred hrest =>
        have hrig := Ix.Kernel.Rules.Red.rigid hred rfl
        obtain ⟨-, rfl, -⟩ := Ix.Kernel.Expr.forallE.inj hrig
        obtain ⟨bs', hs', -⟩ :=
          Ix.Kernel.stripPis_instantiate1_full (v := .fvar d (Γ' d)) n 0 hs0
        exact ih hs' hrest
    | _ => exact nomatch hs

/-- **At a stored projection table whose sort tests zero, a `proj_guard` run's own
`is_inductive_prop` call answers `1`** (module docstring). The data are those of the first
disjunct of `Core.GuardWalk.proj_guard_traced_ih`. -/
theorem isInductiveProp_one_of_table {c : ScopedCtx} (hc : ScopedCoreBase c)
    {calls : List (Call F)} (good : CoreGood c calls) (ihc : IH c calls)
    {x_rc bp ptr ity np ni n v w₁ w₅ w₆ w₇ w₈ : SourceValue F} {i : F}
    {h m₀ m₁ m₂ : Heap F} {cs₁ cs₂ : List (Call F)} {b : Bytes.Address}
    (hrc : c.rc h x_rc) (hb : Bytes.RepAddressRef addrTy h b bp)
    (hres : c.FamAt (ixAddr b) (ZMod.val i)) (e0 : Heap.Extends h m₀)
    (l1 : ObsFn W "Ingress::get_ci_iprj" [bp, .field i] m₀ ptr m₁ cs₁)
    (s1 : ∀ cl ∈ cs₁, cl ∈ calls)
    (ld : loadValue m₁ ptr = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [w₁, ity, np, ni, w₅, w₆, w₇, w₈]))
    (op : evalBinOp .add np ni = .ok n)
    (l2 : ObsFn W "KernelInfer::is_inductive_prop" [x_rc, ity, n] m₁ v m₂ cs₂)
    (s2 : ∀ cl ∈ cs₂, cl ∈ calls)
    (mem : (⟨"Ingress::get_ci_iprj", [bp, .field i], m₀⟩ : Call F) ∈ calls)
    (lt : cs₂.length < calls.length)
    {tbl : Ix.Kernel.ProjTable .anon}
    (htbl : c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
      some (.projInfo tbl))
    (hfields : 0 < tbl.numFields)
    (hprop : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true) : v = .field 1 := by
  -- the table's tower head: the structure's inductive and its declared sort
  obtain ⟨-, -, -, ⟨cvT, capsT, hTf, -, bsT, hsT⟩, -⟩ := hc.env.store.proj_ok _ tbl htbl 0 hfields
  have hname : tbl.structName = c.κ (iprjAddr (ixAddr b) (ZMod.val i)) :=
    Ix.Kernel.projTableName_inj (T := tbl.structName) (WhnfAux.name_of_find htbl)
  have hTf' : c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) =
      some (.indInfo cvT capsT) := by
    rw [← hname]
    exact hTf
  -- the run's load of the member reads that inductive
  obtain ⟨ci, hfind, vI, hldI, hciI⟩ := hc.loads.getIprj bp ptr i m₀ m₁ cs₁ b l1
    (good.allowedTop mem) hres (good.sub s1) (Bytes.repAddressRef_heapMono₂ addrTy e0 hb)
  rw [hTf'] at hfind
  injection hfind with hci
  subst hci
  rw [ld] at hldI
  injection hldI with hvI
  subst hvI
  obtain ⟨cv, caps, nP, nI, nC, hci_eq, hval, hnp, hni, -, -, -, -, -⟩ := WhnfAux.ind_inv hciI
  injection hci_eq with hcv hcaps
  subst hcv hnp hni
  have hn : n = .field ((nP : F) + (nI : F)) := NatAux.add_ok op
  have hI : c.tmc m₁ (posOf cvT.levelParams cvT.type) ity := hval.2.2.2
  have hrc₁ : c.rc m₁ x_rc := RCRep.mono (e0.trans l1.heap_extends) hrc
  obtain ⟨k, Γ', u, -, hpeel, h01, -, h0⟩ :=
    ihc.get (.infer .is_inductive_prop) lt l2 x_rc ity n rfl (good.sub s2) hrc₁ _ hn _ hI
  -- the declared sort, at positional levels, is what the call peeled to
  have hsP := Decl.ilp_stripPis cvT.levelParams (posLevels cvT.levelParams) _ hsT
  have hu : u = Ix.Kernel.Level.subst cvT.levelParams (posLevels cvT.levelParams)
      tbl.structSort :=
    peelRed_stripPis_sort_any (T := posOf cvT.levelParams cvT.type)
      (σ := Ix.Kernel.Level.subst cvT.levelParams (posLevels cvT.levelParams) tbl.structSort)
      _ hsP hpeel
  have hz0 : ∀ ψ, Ix.Kernel.Level.eval ψ tbl.structSort = 0 :=
    fun ψ => (Ix.Kernel.Level.isEquiv_sound hprop ψ).trans rfl
  rcases h01 with h1 | h0'
  · exact h1
  · exfalso
    refine h0 h0' (fun φ => ?_)
    rw [hu, Ix.Kernel.Level.eval_subst]
    exact hz0 _

/-- **The use, read inside the registry's induction** (module docstring): from the facts stated
before the registry and the registry's induction hypothesis over the run's calls, a run of
`KernelInfer::proj_guard` at member `i` of the block `b`, whose stored projection table's sort
tests zero and whose parameter and field counts are the stored constructor's, is the use
observation over the raw dictionary of every run store of the run, at the constructor's raw
telescope read from that store. -/
theorem projGuardUse_of_run {c : ScopedCtx} (hc : ScopedCoreBase c)
    {calls0 : List (Call F)} (ih : IH c calls0)
    {x_rc x_block r : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {i f : F}
    (hlt0 : calls.length < calls0.length) (good : CoreGood c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, x_block, .field i, .field f] h r h' calls)
    {b : Bytes.Address} (hrc : c.rc h x_rc)
    (hb : Bytes.RepAddressRef addrTy h b x_block)
    (hres : c.FamAt (ixAddr b) (ZMod.val i))
    {cvC : Ix.Kernel.ConstantVal .anon} {nP nF : Nat} {tbl : Ix.Kernel.ProjTable .anon}
    (hctor : c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvC nP nF))
    (htbl : c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
      some (.projInfo tbl))
    (hprop : Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true)
    (hnP : tbl.numParams = nP) (hnF : tbl.numFields = nF)
    (hf : ZMod.val f < nF) {g : KLevel} (hg : RepKLevel h' g r)
    {E' : Ixon.Env} (hS : LoadedReads.RunStore calls E')
    (hcov : LoadedReads.HashedRecordsStored calls E') :
    ∃ raw, Guard.ctorRaw E' (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.ProjGuardUse (GuardRaw.ofStore E') raw cvC.type tbl.numParams (ZMod.val f) g := by
  have ihc : IH c calls := ih.mono (Nat.le_of_lt hlt0)
  have hload : ∀ (ptr : SourceValue F) (m : Heap F) (cs : List (Call F)),
      ObsFn W "Ingress::get_ci_cprj" [x_block, .field i, .field 0] h ptr m cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      (⟨"Ingress::get_ci_cprj", [x_block, .field i, .field 0], h⟩ : Call F) ∈ calls →
      CIPtrRep c.κ m ptr (.ctorInfo cvC nP nF) := by
    intro ptr m cs evC sC memC
    refine (hc.loads.getCprj x_block ptr i 0 h m cs b evC (good.allowedTop memC) hres
      (good.sub sC) hb).2 cvC nP nF ?_
    rw [ZMod.val_zero]
    exact hctor
  rcases GuardWalk.proj_guard_traced_ih (Core.keyOf GuardRaw.addressTable) c hc good ihc ev hrc
      hload hf hg with
    ⟨ptr, ity, np, ni, n, v, w₁, w₅, w₆, w₇, w₈, m₀, m₁, m₂, cs₁, cs₂, e0, l1, s1, ld, op, l2,
      s2, hne, mem, lt⟩ |
    ⟨lus, flags, sigs, S, ptr, x_cty, w₁, w₃, w₄, w₅, w₆, w₇, w₈, m, cs₀, hfold, hflags, load,
      inside, ld, physical, traces, zeros⟩
  · exact absurd (isInductiveProp_one_of_table hc good ihc hrc hb hres e0 l1 s1 ld op l2 s2 mem
      lt htbl (by omega) hprop) hne
  · rw [hnP]
    exact projGuardUse_runStore hS hcov good.bounded hb hfold hflags load inside ld physical
      traces zeros

end IxVM.Refinement.Guard
