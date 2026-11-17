import IxVMRefinement.Assembly.TypingRecLateElim

/-! # The telescope length `get_result_sort_level` accepts

`get_result_sort_level(rc, ty, n, types)` head-normalizes before each of `n` binders and at the
end, where it must find a sort. A syntactic telescope into a sort is already head normal at
every position (`Red.forallE_eq`, `Red.sort_eq`: neither a `∀` nor a sort reduces), so the walk
accepts one only at its own length: `get_result_sort_level_tele_len`. This refutes the third case
of `formerAt_cases` (`FormerTeleOther`) wherever the walked check's shape stage is read at a
scoped context.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam)
open Ix.Kernel.Rules (Red DefEq Infer)

/-- **A syntactic telescope into a sort that `get_result_sort_level` accepts has the walk's
length.** -/
theorem get_result_sort_level_tele_len {c : ScopedCtx} :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {rc pe types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx →
      ScopedLoadFacts c →
      CoreGood c cs →
      Tm c.κ d Γ h 0 E pe →
      ObsFn W "KernelCheck::get_result_sort_level" [rc, pe, .field (n : F), types] h r h' cs →
      ∀ k bs s, E.stripPis k = some (bs, .sort s) → k = n
  | 0, d, Γ, E, rc, pe, types, r, h, h', cs, _, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (cs12 := cs12) (ev14 := ev_w) (ld64 := ld) (he78 := hr) (he79 := hh) (hc80 := hc) .. =>
      subst hc hr hh
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hred⟩ := scoped_core_whnf hrc hty hsc hef hlf hg1 ev_w hE
      obtain ⟨u, rfl, ℓ, hℓ, huℓ⟩ := hE'.sort_of_load ld
      intro k bs s hst
      cases k with
      | zero => rfl
      | succ k =>
        cases E with
        | forallE dom₀ bo₀ m₀ =>
          have h1 := Red.forallE_eq hred
          cases h1
        | _ => simp [Expr.stripPis] at hst
    | .other (hne82 := hne) .. => exact absurd rfl hne
  | m + 1, d, Γ, E, rc, pe, types, r, h, h', cs, hlt, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (hv52 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other (cs12 := cs12) (x_body := xbody) (cs124 := cs2) (m161 := m3) (ev14 := ev_w)
        (ld97 := ld) (op158 := op) (hm169 := hm3) (ev126 := ev_rec) (hc189 := hc) .. =>
      subst hc
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      have hg2 : CoreGood c cs2 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hred⟩ := scoped_core_whnf hrc hty hsc hef hlf hg1 ev_w hE
      obtain ⟨T, B, _, rfl, hT, hB, _⟩ := hE'.forallE_of_load ld
      have ext_w := ev_w.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm3] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m3 0 (B.instantiate1 (.fvar d T)) xbody :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ m op] at ev_rec
      have hlen := get_result_sort_level_tele_len m (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hef hlf hg2 hB_open ev_rec
      intro k bs s hst
      cases E with
      | forallE dom₀ bo₀ m₀ =>
        obtain ⟨rfl, rfl, rfl⟩ := Red.forallE_eq hred
        cases k with
        | zero => simp [Expr.stripPis] at hst
        | succ k =>
          simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
          obtain ⟨⟨bs₁, body₁⟩, hst₁, hst⟩ := hst
          simp only [Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          obtain ⟨bs₂, hst₂⟩ := stripPis_instantiate1_sort k (v := .fvar d T) (k := 0) hst₁
          have := hlen k bs₂ s hst₂
          omega
      | sort u' =>
        cases k with
        | zero =>
          have h1 := Red.sort_eq hred
          cases h1
        | succ k => simp [Expr.stripPis] at hst
      | _ => cases k <;> simp [Expr.stripPis] at hst

end IxVM.Refinement.Decl
