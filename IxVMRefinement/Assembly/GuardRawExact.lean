import IxVMRefinement.Subst.Steps
import IxVMRefinement.Core.LoadedExact
import IxVMRefinement.Guard.RawLevels

/-! # Metadata-preserving exact raw substitution

The structural guard substitutes universe syntax without normalization. Both the retained raw
expression and its semantic reading follow the same literal positional substitution; binder
metadata follows the exact zeroness substitution identity. This is a data specification only.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (Expr Level)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000

private theorem raw_ilp_nil {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) : R.instantiateLevelParams [] [] = R := by
  induction rep with
  | bvarLocal => rfl
  | bvarFree _ _ _ hd => omega
  | sort cell level => simp only [Expr.instantiateLevelParams, SubstAux.level_subst_nil]
  | const cell address levels =>
    have hid : Level.subst [] [] = id := funext SubstAux.level_subst_nil
    simp [Expr.instantiateLevelParams, hid]
  | app cell _ _ ihf iha => simp only [Expr.instantiateLevelParams, ihf, iha]
  | lam cell _ _ level iht ihb | forallE cell _ _ level iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, SubstAux.bmeta_subst_nil]
  | letE cell _ _ _ iht ihv ihb => simp only [Expr.instantiateLevelParams, iht, ihv, ihb]
  | litNat | litStr => rfl
  | proj cell address _ ih => simp only [Expr.instantiateLevelParams, ih]

private theorem raw_bmeta_subst (params : List Level) (u : Level) :
    ({ bmeta u with pw := Level.substPW (List.range params.length) params (bmeta u).pw } :
      Ix.Kernel.BinderMeta) = bmeta (Level.subst (List.range params.length) params u) := by
  unfold bmeta
  rw [Level.zeronessOf_subst]

private theorem raw_forallE_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p tp bp lp : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp])) :
    ∃ RT RB T B ℓ,
      R = .forallE RT RB (bmeta ℓ) ∧
      E = .forallE T B (bmeta ℓ) ∧
      RawTmExact κ d Γ h k RT T tp ∧
      RawTmExact κ d Γ h (k + 1) RB B bp ∧
      RepKLevel h ℓ lp := by
  cases rep with
  | forallE cell rt rb rl =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3
    subst h1 h2 h3
    exact ⟨_, _, _, _, _, rfl, rfl, rt, rb, rl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem raw_app_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p fp ap : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ Rf Ra Ef Ea,
      R = .app Rf Ra ∧
      E = .app Ef Ea ∧
      RawTmExact κ d Γ h k Rf Ef fp ∧
      RawTmExact κ d Γ h k Ra Ea ap := by
  cases rep with
  | app cell rf ra =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2
    subst h1 h2
    exact ⟨_, _, _, _, rfl, rfl, rf, ra⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem raw_const_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p ap lsp : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    ∃ a ls,
      R = .const (κ (ixAddr a)) ls ∧
      E = .const (κ (ixAddr a)) ls ∧
      Bytes.RepAddressRef addrTy h a ap ∧
      RepKLevelList h ls lsp := by
  cases rep with
  | const cell ra rls =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2
    subst h1 h2
    exact ⟨_, _, rfl, rfl, ra, rls⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem raw_sort_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p level : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Srt" [level])) :
    ∃ u, R = .sort u ∧ E = .sort u ∧ RepKLevel h u level := by
  cases rep with
  | sort cell represented =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with same
    subst same
    exact ⟨_, rfl, rfl, represented⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_lam_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p dom body level : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Lam" [dom, body, level])) :
    ∃ RD RB D B u, R = .lam RD RB (bmeta u) ∧ E = .lam D B (bmeta u) ∧
      RawTmExact κ d Γ h k RD D dom ∧ RawTmExact κ d Γ h (k + 1) RB B body ∧
      RepKLevel h u level := by
  cases rep with
  | lam cell domain bodyRep represented =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with one fields; injection fields with two fields; injection fields with three
    subst one two three
    exact ⟨_, _, _, _, _, rfl, rfl, domain, bodyRep, represented⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _ | app cell _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_let_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p ty val body : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Let" [ty, val, body])) :
    ∃ RT RV RB T V B, R = .letE RT RV RB default ∧ E = instShift V 0 B ∧
      RawTmExact κ d Γ h k RT T ty ∧ RawTmExact κ d Γ h k RV V val ∧
      RawTmExact κ d Γ h (k + 1) RB B body := by
  cases rep with
  | letE cell typeRep valueRep bodyRep =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with one fields; injection fields with two fields; injection fields with three
    subst one two three
    exact ⟨_, _, _, _, _, _, rfl, rfl, typeRep, valueRep, bodyRep⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_proj_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p ap i inner : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Proj" [ap, i, inner])) :
    ∃ (a : Bytes.Address) (index : F) (RI I : KExpr), R = .proj (κ (ixAddr a)) index.val RI ∧
      E = .proj (κ (ixAddr a)) index.val I ∧ i = .field index ∧
      Bytes.RepAddressRef addrTy h a ap ∧ RawTmExact κ d Γ h k RI I inner := by
  cases rep with
  | proj cell address represented =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with one fields; injection fields with two fields; injection fields with three
    subst one two three
    exact ⟨_, _, _, _, rfl, rfl, rfl, address, represented⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_leaf_ilp {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F} {fields : List (SourceValue F)}
    (rep : RawTmExact κ 0 Γ h k R E p) (params : List Level)
    (leaf : loadValue h p = .ok (.construct kexprEnum "BVar" fields) ∨
      loadValue h p = .ok (.construct kexprEnum "Lit" fields)) :
    R.instantiateLevelParams (List.range params.length) params = R ∧
      E.instantiateLevelParams (List.range params.length) params = E := by
  cases rep with
  | bvarLocal | litNat | litStr => exact ⟨rfl, rfl⟩
  | bvarFree _ _ _ hd => omega
  | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | proj cell _ _ =>
    rcases leaf with loaded | loaded <;> exact (load_cell_ne cell loaded (by decide)).elim

private def rawExprNameExact (walk : Bool) : String :=
  if walk then "KernelGuard::expr_inst_raw_walk" else "KernelGuard::expr_inst_raw"

private theorem raw_expr_go (κ : _root_.Address → KKey) :
    ∀ fuel : Nat, ∀ (walk : Bool) {k : Nat} {Γ : Nat → KExpr} {R E : KExpr}
      {ps : List Level} {p params r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → RawTmExact κ 0 Γ h k R E p → RepKLevelList h ps params →
      ObsFn W (rawExprNameExact walk) [p, params] h r h' cs →
      RawTmExact κ 0 Γ h' k
        (R.instantiateLevelParams (List.range ps.length) ps)
        (E.instantiateLevelParams (List.range ps.length) ps) r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro walk k Γ R E ps p params r h h' cs hlen hE hp ev
    cases walk with
    | false =>
      change ObsFn W "KernelGuard::expr_inst_raw" [p, params] h r h' cs at ev
      match Obs.«KernelGuard::expr_inst_raw».obs ev with
      | .Nil (ld12 := loaded) (he21 := hr) (he22 := hh) .. =>
        rw [← Levels.klevelList_names] at loaded
        obtain rfl := Lib.rep_nil_of_load hp loaded
        subst hr hh
        simp only [List.length_nil, List.range_zero, raw_ilp_nil hE,
          SubstAux.tm_ilp_nil hE.toTmExact.toTm]
        exact hE
      | .other (cs31 := children) (ev33 := child) (hc50 := hc) .. =>
        have hlt : children.length < fuel := by
          rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
        exact ih children.length hlt true (Nat.le_refl _) hE hp child
    | true =>
      change ObsFn W "KernelGuard::expr_inst_raw_walk" [p, params] h r h' cs at ev
      match Obs.«KernelGuard::expr_inst_raw_walk».obs ev with
      | .BVar (ld12 := loaded) (he27 := hr) (he28 := hh) .. =>
        obtain ⟨rawEq, semEq⟩ := raw_leaf_ilp hE ps (.inl loaded)
        subst hr hh
        rw [rawEq, semEq]
        exact hE
      | .Lit (ld12 := loaded) (he595 := hr) (he596 := hh) .. =>
        obtain ⟨rawEq, semEq⟩ := raw_leaf_ilp hE ps (.inr loaded)
        subst hr hh
        rw [rawEq, semEq]
        exact hE
      | .Srt (ld12 := loaded) (he46 := hr) (hm45 := hh) (ev62 := child) .. =>
        obtain ⟨u, rfl, rfl, represented⟩ := raw_sort_view hE loaded
        have exactLevel := (Guard.level_inst_raw_spec child represented hp).2
        rw [Guard.rawSubst_eq] at exactLevel
        subst hr hh
        exact .sort (by simp) (exactLevel.mono (Heap.Extends.snoc _ _))
      | .Const (ld12 := loaded) (he101 := hr) (hm100 := hh) (ev125 := child) .. =>
        have semantic := hE.toTmExact.toTm
        obtain ⟨a, levels, rfl, rfl, address, represented⟩ := raw_const_view hE loaded
        have : Resolved (κ (ixAddr a)) := ⟨semantic.const_key_ne⟩
        have exactLevels := (Guard.levels_inst_raw_spec child represented hp).2
        have substitution : Guard.rawSubst ps = Level.subst (List.range ps.length) ps :=
          funext (Guard.rawSubst_eq ps)
        rw [substitution] at exactLevels
        subst hr hh
        exact .const (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (child.heap_extends.trans (Heap.Extends.snoc _ _)) address)
          (exactLevels.mono (Heap.Extends.snoc _ _))
      | .App (cs179 := first) (cs207 := second) (ld12 := loaded) (he164 := hr) (hm163 := hh)
          (ev181 := e1) (ev209 := e2) (hc226 := hc) .. =>
        obtain ⟨Rf, Ra, Ef, Ea, rfl, rfl, hf, ha⟩ := raw_app_view hE loaded
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have sf := ih first.length h1 false (Nat.le_refl _) hf hp e1
        have sa := ih second.length h2 false (Nat.le_refl _)
          (ha.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        subst hr hh
        exact .app (by simp) (sf.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _)))
          (sa.mono (Heap.Extends.snoc _ _))
      | .Lam (cs269 := first) (cs297 := second) (ld12 := loaded) (he253 := hr) (hm252 := hh)
          (ev271 := e1) (ev299 := e2) (ev327 := e3) (hc344 := hc) .. =>
        obtain ⟨RT, RB, T, B, u, rfl, rfl, hT, hB, level⟩ := raw_lam_view hE loaded
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have st := ih first.length h1 false (Nat.le_refl _) hT hp e1
        have sb := ih second.length h2 false (Nat.le_refl _)
          (hB.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        have ext := e1.heap_extends.trans e2.heap_extends
        have exactLevel := (Guard.level_inst_raw_spec e3 (level.mono ext) (hp.mono ext)).2
        rw [Guard.rawSubst_eq] at exactLevel
        subst hr hh
        simp only [Expr.instantiateLevelParams, raw_bmeta_subst]
        exact .lam (by simp) (st.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
          (sb.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _))) (exactLevel.mono (Heap.Extends.snoc _ _))
      | .Forall (cs387 := first) (cs415 := second) (ld12 := loaded) (he371 := hr) (hm370 := hh)
          (ev389 := e1) (ev417 := e2) (ev445 := e3) (hc462 := hc) .. =>
        obtain ⟨RT, RB, T, B, u, rfl, rfl, hT, hB, level⟩ := raw_forallE_view hE loaded
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have st := ih first.length h1 false (Nat.le_refl _) hT hp e1
        have sb := ih second.length h2 false (Nat.le_refl _)
          (hB.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        have ext := e1.heap_extends.trans e2.heap_extends
        have exactLevel := (Guard.level_inst_raw_spec e3 (level.mono ext) (hp.mono ext)).2
        rw [Guard.rawSubst_eq] at exactLevel
        subst hr hh
        simp only [Expr.instantiateLevelParams, raw_bmeta_subst]
        exact .forallE (by simp) (st.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
          (sb.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _))) (exactLevel.mono (Heap.Extends.snoc _ _))
      | .Let (cs505 := first) (cs533 := second) (cs561 := third) (ld12 := loaded)
          (he489 := hr) (hm488 := hh) (ev507 := e1) (ev535 := e2) (ev563 := e3) (hc580 := hc) .. =>
        obtain ⟨RT, RV, RB, T, V, B, rfl, rfl, hT, hV, hB⟩ := raw_let_view hE loaded
        have h1 : first.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h2 : second.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have h3 : third.length < fuel := by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
        have st := ih first.length h1 false (Nat.le_refl _) hT hp e1
        have sv := ih second.length h2 false (Nat.le_refl _)
          (hV.mono e1.heap_extends) (hp.mono e1.heap_extends) e2
        have ext := e1.heap_extends.trans e2.heap_extends
        have sb := ih third.length h3 false (Nat.le_refl _)
          (hB.mono ext) (hp.mono ext) e3
        subst hr hh
        simp only [Expr.instantiateLevelParams, SubstAux.ilp_instShift]
        exact .letE (by simp) (st.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
          (sv.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _))) (sb.mono (Heap.Extends.snoc _ _))
      | .Proj (cs654 := children) (ld12 := loaded) (he624 := hr) (hm623 := hh)
          (ev656 := child) (hc673 := hc) .. =>
        have semantic := hE.toTmExact.toTm
        obtain ⟨a, index, RI, I, rfl, rfl, rfl, address, inner⟩ := raw_proj_view hE loaded
        have : Resolved (κ (ixAddr a)) := ⟨semantic.proj_key_ne⟩
        have : ProjPermitted κ (ixAddr a) := semantic.proj_permitted loaded address
        have hlt : children.length < fuel := by rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
        have sub := ih children.length hlt false (Nat.le_refl _) inner hp child
        subst hr hh
        exact .proj (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (child.heap_extends.trans (Heap.Extends.snoc _ _)) address)
          (sub.mono (Heap.Extends.snoc _ _))

/-- The actual raw universe-instantiation operation preserves the complete raw syntax and its
semantic reading, including exact instantiated binder metadata. -/
theorem expr_inst_raw_exact {κ : _root_.Address → KKey} {k : Nat} {Γ : Nat → KExpr}
    {R E : KExpr} {ps : List Level} {p params r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (represented : RawTmExact κ 0 Γ h k R E p) (parameters : RepKLevelList h ps params)
    (observed : ObsFn W "KernelGuard::expr_inst_raw" [p, params] h r h' cs) :
    RawTmExact κ 0 Γ h' k
      (R.instantiateLevelParams (List.range ps.length) ps)
      (E.instantiateLevelParams (List.range ps.length) ps) r :=
  raw_expr_go κ cs.length false (Nat.le_refl _) represented parameters observed


end IxVM.Refinement.Decl
