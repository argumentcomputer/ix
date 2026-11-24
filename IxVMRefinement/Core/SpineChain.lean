import IxVM.Obs.KernelTypes
import Aiur.Generic.Refinement.Obs
import Aiur.Library.List.Correctness

/-! # Application-spine characterization of `KernelTypes::collect_spine`

`SpineChain h e hd ps` records the left-nested chain of `KExprNode::App` cells in heap `h` from
`e` down to the non-`App` head `hd`, collecting arguments `ps` in left-to-right order.

`collect_spine_chain` relates any observed derivation of `KernelTypes::collect_spine` (implemented
via the tail-recursive accumulator `collect_spine_acc`) to `SpineChain h e hd ps` on the initial
heap `h`, with `ps.length = cs.length` and `sp` representing `ps` in `h'`. Every caller in
`IxVMRefinement` can then induct on `SpineChain` without depending on the internal accumulator
implementation. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option linter.unusedVariables false

private theorem loadValue_mono {h₁ h₂ : Heap F} {p v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (ld : loadValue h₁ p = .ok v) : loadValue h₂ p = .ok v := by
  cases p with
  | ptr target addr =>
    simp only [loadValue] at ld ⊢
    cases hget : h₁[addr]? with
    | none => simp [hget] at ld
    | some val =>
      rw [hget] at ld
      rw [ext.getElem?_eq hget]
      exact ld
  | _ => simp [loadValue] at ld

/-- A left-nested chain of `KernelTypes::KExprNode::App` cells in `h` from `e` to a non-`App`
head `hd`, with arguments `ps` in left-to-right order. -/
inductive SpineChain (h : Heap F) :
    SourceValue F → SourceValue F → List (SourceValue F) → Prop where
  | head {e v : SourceValue F}
      (ld : loadValue h e = .ok v)
      (hne : ∀ vs : List (SourceValue F), vs.length = 2 →
        v ≠ .construct "KernelTypes::KExprNode" "App" vs) :
      SpineChain h e e []
  | app {e f a hd : SourceValue F} {ps : List (SourceValue F)}
      (ld : loadValue h e = .ok (.construct "KernelTypes::KExprNode" "App" [f, a]))
      (rest : SpineChain h f hd ps) :
      SpineChain h e hd (ps ++ [a])

theorem SpineChain.mono {h₁ h₂ : Heap F} {e hd : SourceValue F} {ps : List (SourceValue F)}
    (ext : Heap.Extends h₁ h₂) (sc : SpineChain h₁ e hd ps) : SpineChain h₂ e hd ps := by
  induction sc with
  | head ld hne => exact .head (loadValue_mono ext ld) hne
  | app ld _ ih => exact .app (loadValue_mono ext ld) ih

theorem SpineChain.head_load {h : Heap F} {e hd : SourceValue F} {ps : List (SourceValue F)}
    (sc : SpineChain h e hd ps) :
    ∃ v, loadValue h hd = .ok v ∧
      ∀ vs : List (SourceValue F), vs.length = 2 →
        v ≠ .construct "KernelTypes::KExprNode" "App" vs := by
  induction sc with
  | head ld hne => exact ⟨_, ld, hne⟩
  | app _ _ ih => exact ih

theorem SpineChain.det {h₁ h₂ : Heap F} {e hd₁ hd₂ : SourceValue F}
    {ps₁ ps₂ : List (SourceValue F)} (ext : Heap.Extends h₁ h₂)
    (s₁ : SpineChain h₁ e hd₁ ps₁) (s₂ : SpineChain h₂ e hd₂ ps₂) :
    hd₁ = hd₂ ∧ ps₁ = ps₂ := by
  induction s₁ generalizing hd₂ ps₂ with
  | head ld₁ hne₁ =>
    cases s₂ with
    | head _ _ => exact ⟨rfl, rfl⟩
    | app ld₂ _ =>
      have hsame := Except.ok.inj ((loadValue_mono ext ld₁).symm.trans ld₂)
      exact (hne₁ _ rfl hsame).elim
  | app ld₁ _ ih =>
    cases s₂ with
    | head ld₂ hne₂ =>
      have hsame := Except.ok.inj ((loadValue_mono ext ld₁).symm.trans ld₂)
      exact (hne₂ _ rfl hsame.symm).elim
    | app ld₂ rest₂ =>
      have hsame := Except.ok.inj ((loadValue_mono ext ld₁).symm.trans ld₂)
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hsame
      obtain ⟨rfl, rfl⟩ := hsame
      obtain ⟨rfl, rfl⟩ := ih rest₂
      exact ⟨rfl, rfl⟩

/-- Append two `List.Forall₂` witnesses. -/
theorem forall₂_append {α β : Type*} {R : α → β → Prop} {l₁ l₂ : List α} {r₁ r₂ : List β}
    (h₁ : List.Forall₂ R l₁ r₁) (h₂ : List.Forall₂ R l₂ r₂) :
    List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hab _ ih => exact .cons hab ih

/-- Lift a pointer-identity `RepList` along any element-wise relation `List.Forall₂`. -/
theorem repList_of_eq_forall₂ {enumName : String} {α : Type}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F}
    {xs : List α} {ps : List (SourceValue F)} {l : SourceValue F}
    (hr : RepList enumName (fun _ x y => x = y) h ps l)
    (hf : List.Forall₂ (fun x p => R h x p) xs ps) :
    RepList enumName R h xs l := by
  induction hr generalizing xs with
  | nil cell =>
    cases hf
    exact .nil cell
  | cons cell hEq _ ih =>
    cases hf with
    | cons h1 h2 =>
      subst hEq
      exact .cons cell h1 (ih h2)

private theorem loadValue_snoc_listCell {h : Heap F} {x_e v : SourceValue F} {ctor : String}
    {vs : List (SourceValue F)}
    (hty : x_e.type = .ptr (.enum "KernelTypes::KExprNode"))
    (hld : loadValue (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» ctor vs]) x_e = .ok v) :
    loadValue h x_e = .ok v := by
  cases x_e with
  | ptr target addr =>
    simp only [Value.type, Aiur.Ty.ptr.injEq] at hty
    subst hty
    simp only [loadValue] at hld ⊢
    by_cases hlt : addr < h.length
    · rwa [List.getElem?_append_left hlt] at hld
    · by_cases heq : addr = h.length
      · subst heq
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Value.type] at hld
        have hne : (Aiur.Ty.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» ≠
            Aiur.Ty.enum "KernelTypes::KExprNode") := by
          intro h; injection h with h; exact absurd h (by decide)
        simp [hne] at hld
      · have hnone :
            (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» ctor vs])[addr]? =
              none := List.getElem?_eq_none (by simp; omega)
        simp [hnone] at hld
  | _ => simp [Value.type] at hty

private theorem loadValue_kexpr_type {h : Heap F} {x_e : SourceValue F} {ctor : String}
    {vs : List (SourceValue F)}
    (hld : loadValue h x_e = .ok (.construct "KernelTypes::KExprNode" ctor vs)) :
    x_e.type = .ptr (.enum "KernelTypes::KExprNode") := by
  cases x_e with
  | ptr target addr =>
    simp only [loadValue] at hld
    cases hg : h[addr]? with
    | none => simp [hg] at hld
    | some val =>
      simp only [hg] at hld
      split at hld
      · cases hld
      · rename_i hne
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hld
        subst hld
        simp only [Value.type, ne_eq, not_not] at hne ⊢
        rw [hne]
  | _ => simp [loadValue] at hld

private theorem SpineChain.unextend_listCell {h : Heap F} {ctor : String}
    {vs : List (SourceValue F)} {e hd : SourceValue F} {ps : List (SourceValue F)}
    (hhty : hd.type = .ptr (.enum "KernelTypes::KExprNode"))
    (sc : SpineChain (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» ctor vs])
      e hd ps) : SpineChain h e hd ps := by
  induction sc with
  | head ld hne => exact .head (loadValue_snoc_listCell hhty ld) hne
  | app ld _ ih =>
    exact .app (loadValue_snoc_listCell (loadValue_kexpr_type ld) ld) (ih hhty)

private theorem collect_spine_acc_arg0_type {x_e x_acc r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine_acc" [x_e, x_acc] h r h' cs) :
    x_e.type = .ptr (.enum "KernelTypes::KExprNode") := by
  have hprep :
      ∃ t l e, W.prepare "KernelTypes::collect_spine_acc" [x_e, x_acc] = .ok (t, l, e) := by
    cases ev with
    | intro p _ => exact ⟨_, _, _, p⟩
    | returned p _ => exact ⟨_, _, _, p⟩
  obtain ⟨t, l, e, hp⟩ := hprep
  have hlk : IxVM.source.program.sourceFunction? "KernelTypes::collect_spine_acc" =
      some { types := [],
             params := IxVM.KernelTypes.collect_spine_acc.params.map fun (n, ty) => (n, (ty.subst []).toCore),
             body := IxVM.KernelTypes.collect_spine_acc.body } :=
    IxVM.KernelTypes.collect_spine_acc.lookup
  simp only [Obs.W, Source.world, sourceWorld, hlk, SourceFunction.prepare] at hp
  split at hp
  · rename_i hcond
    have h0 : ((IxVM.KernelTypes.collect_spine_acc.params.map fun (n, ty) =>
        (n, (ty.subst []).toCore)).map Prod.snd).head? =
        some (.ptr (.enum "KernelTypes::KExprNode")) := by decide +kernel
    have h1 := h0.symm.trans (congrArg List.head? hcond.1)
    simp only [List.map_cons, List.head?_cons, Option.some.injEq] at h1
    exact h1.symm
  · cases hp

private theorem collect_spine_acc_chain :
    ∀ (n : Nat) {e acc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {accPs : List (SourceValue F)},
      cs.length ≤ n →
      RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» (fun _ x y => x = y) h accPs acc →
      ObsFn W "KernelTypes::collect_spine_acc" [e, acc] h r h' cs →
      ∃ hd sp ps,
        r = .tuple [hd, sp] ∧
        hd.type = .ptr (.enum "KernelTypes::KExprNode") ∧
        SpineChain h e hd ps ∧
        ps.length = cs.length ∧
        RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» (fun _ x y => x = y) h'
          (ps ++ accPs) sp
  | n, e, acc, r, h, h', cs, accPs, hle, hacc, ev => by
    match Obs.«KernelTypes::collect_spine_acc».obs ev with
    | .other (ld_bolbylmd := ld) (hne_ebjedqqk := hne) (he_jjavcari := hr) (he_yrjjshnd := hh)
        (hc_kjrxaxhl := hc) .. =>
      subst hr hh hc
      exact ⟨e, acc, [], rfl, collect_spine_acc_arg0_type ev, .head ld hne, rfl, hacc⟩
    | .App (x_f := xf) (x_a := xa) (cs_mwgycbpe := cs1) (ld_bolbylmd := ld)
        (hm_kuahfmom := hm) (ev_yhtuifcw := ev1) (hc_xkhdrnsx := hc) .. =>
      subst hm hc
      cases n with
      | zero => simp at hle
      | succ n' =>
        have ext :
            Heap.Extends h
              (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Cons" [xa, acc]]) :=
          Heap.Extends.snoc _ _
        have hacc' :
            RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» (fun _ x y => x = y)
              (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Cons" [xa, acc]])
              (xa :: accPs)
              (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») h.length) :=
          .cons (by simp) rfl (hacc.mono (fun _ _ _ _ _ r => r) ext)
        obtain ⟨hd, sp, ps, rfl, hhty, hch1, hplen, hrep⟩ :=
          collect_spine_acc_chain n' (by simp at hle; omega) hacc' ev1
        have hch : SpineChain h xf hd ps := hch1.unextend_listCell hhty
        refine ⟨hd, sp, ps ++ [xa], rfl, hhty, .app ld hch, by simp [hplen], ?_⟩
        simpa [List.append_assoc] using hrep

/-- **Universal specification of `KernelTypes::collect_spine`**: returns `(hd, sp)` where
`SpineChain h e hd ps` walks the `App` chain in the initial heap `h`, `ps.length = cs.length`,
and `sp` is a linked list of `ps` in the final heap `h'`. -/
theorem collect_spine_chain {e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" [e] h r h' cs) :
    ∃ hd sp ps,
      r = .tuple [hd, sp] ∧
      SpineChain h e hd ps ∧
      ps.length = cs.length ∧
      RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» (fun _ x y => x = y) h' ps sp := by
  match Obs.«KernelTypes::collect_spine».obs ev with
  | .other (ld12 := ld) (hne107 := hne) (he115 := hr) (hm132 := hm) (he136 := hh)
      (hc137 := hc) .. =>
    subst hr hm hh hc
    exact ⟨e, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») h.length, [],
      rfl, .head ld hne, rfl, .nil (by simp)⟩
  | .App (x_f := xf) (x_a := xa) (cs_mwgycbpe := cs1) (ld12 := ld)
      (hm_kuahfmom := hm2) (hm_ximulagv := hm1) (ev_yhtuifcw := ev1) (hc106 := hc) .. =>
    subst hm1 hm2 hc
    have hnil :
        RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» (fun _ x y => x = y)
          (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
          [] (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») h.length) :=
      .nil (by simp)
    have ext2 :
        Heap.Extends
          (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
          ((h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) ++
            [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Cons"
              [xa, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») h.length]]) :=
      Heap.Extends.snoc _ _
    have hcons :
        RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» (fun _ x y => x = y)
          ((h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) ++
            [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Cons"
              [xa, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») h.length]])
          [xa]
          (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>»)
            (h ++ ([Value.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []] : List (SourceValue F))).length) :=
      .cons (by simp) rfl (hnil.mono (fun _ _ _ _ _ r => r) ext2)
    obtain ⟨hd, sp, ps, rfl, hhty, hch2, hplen, hrep⟩ :=
      collect_spine_acc_chain cs1.length (Nat.le_refl _) hcons ev1
    have hch1 := hch2.unextend_listCell hhty
    have hch := hch1.unextend_listCell hhty
    exact ⟨hd, sp, ps ++ [xa], rfl, .app ld hch, by simp [hplen], hrep⟩

/-- Convenience specialization of `collect_spine_chain` when the result is already `.tuple [hd, sp]`. -/
theorem collect_spine_chain_tup {e hd sp : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" [e] h (.tuple [hd, sp]) h' cs) :
    ∃ ps,
      SpineChain h e hd ps ∧
      ps.length = cs.length ∧
      RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» (fun _ x y => x = y) h' ps sp := by
  obtain ⟨hd', sp', ps, htup, hch, hplen, hrep⟩ := collect_spine_chain ev
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  obtain ⟨rfl, rfl⟩ := htup
  exact ⟨ps, hch, hplen, hrep⟩

end IxVM.Refinement.Core
