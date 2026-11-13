import IxVMRefinement.DefEq.Basic
import IxVMRefinement.Core.Roles

/-! # Step lemmas of `KernelDefEq`: literals, `Nat` offsets and η-expansion

* **String literals** (`try_string_lit_one`): a string literal reduces to its constructor form
  (`Red.strLit`, under the guard `str_lit_to_ctor` establishes), and one δ step on
  (`str_lit_delta_step`); the comparison of that reduct with the other side is carried back by
  `DefEq.redL`. `try_string_lit_pair` runs it both ways, the second by `DefEq.symm`.
* **η-expansion** (`try_eta_expand`, `DefEq.eta`): the `λ`'s body is compared under the context
  list with the left domain pushed, against `b` lifted past the new binder and applied to the
  stored `BVar 0`. One depth further in, under the ghost context extended by the left domain,
  the lifted `b` reads as `b` and the `BVar 0` as the new opened variable, so the stored
  application reads as `b` applied to it. `try_eta_swap` puts the `λ` on the left
  (`DefEq.symm` when it is on the right).
* **`Nat` zero readings and offsets** (`is_nat_zero`, `try_def_eq_nat`): two zero readings
  compare by `DefEq.refl`/`DefEq.natZero`; two splits at one offset (`nat_offset_of`'s spec,
  `klimbs_eq`) with definitionally equal bases reduce to successor towers over their bases
  (`Red.natLit`, `Red.natAddSucc`, `Red.natAddZero` under `Red.appArg`), which compare by
  congruence, carried back by `DefEq.redBoth`; the guards come from the roles in force. -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq)

set_option linter.unusedVariables false

private theorem fval_zero : ZMod.val (0 : F) = 0 := ZMod.val_zero

private theorem fval_one : ZMod.val (1 : F) = 1 := ZMod.val_one _

/-- The constructor form of a string literal is an application of `String.ofList`. -/
private theorem strLitToConstructor_app (s : String) :
    ∃ L : KExpr, (Ix.Kernel.strLitToConstructor s : KExpr) =
      .app (.const Ix.Kernel.stringOfListName []) L :=
  ⟨_, rfl⟩

/-- **The new opened variable as IxVM stores it**: a `BVar 0` cell stored at the end of the heap
reads, one depth further in under the ghost context extended at `d`, as the opened variable
`d`. -/
private theorem tm_store_bvar0 {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {T : KExpr} (h : Heap F) :
    c.tm (d + 1) (Ghost.extend Γ d T) (h ++ [.construct kexprEnum "BVar" [.field 0]])
      (.fvar d T) (.ptr (.enum kexprEnum) h.length) := by
  have hv : Tm c.κ (d + 1) (Ghost.extend Γ d T) (h ++ [.construct kexprEnum "BVar" [.field 0]]) 0
      (.fvar (fvIdx (d + 1) 0 (ZMod.val (0 : F)))
        (Ghost.extend Γ d T (fvIdx (d + 1) 0 (ZMod.val (0 : F)))))
      (.ptr (.enum kexprEnum) h.length) :=
    Tm.bvarFree (by simp) (by have := fval_zero; omega) (Nat.zero_le _)
      (by have := fval_zero; omega)
  have e : fvIdx (d + 1) 0 (ZMod.val (0 : F)) = d := by
    have := fval_zero
    show d + 1 - 1 - (ZMod.val (0 : F) - 0) = d
    omega
  rw [e, Ghost.extend_at] at hv
  exact hv

/-! ## Products of answers -/

private theorem evalBinOp_mul_inv' {x y r : SourceValue F} (h : evalBinOp .mul x y = .ok r) :
    ∃ a b, x = .field a ∧ y = .field b ∧ r = .field (a * b) := by
  cases x <;> cases y <;> simp [evalBinOp] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-- A product other than `0` has both factors other than `0`. -/
private theorem mul_field_ne_zero {x y r : SourceValue F} (op : evalBinOp .mul x y = .ok r)
    (hr : r ≠ .field 0) : x ≠ .field 0 ∧ y ≠ .field 0 := by
  obtain ⟨a, b, rfl, rfl, rfl⟩ := evalBinOp_mul_inv' op
  refine ⟨fun e => hr ?_, fun e => hr ?_⟩
  · injection e with e
    subst e
    simp
  · injection e with e
    subst e
    simp

private theorem tuple_zero_ne {x y : SourceValue F} :
    (Value.tuple [.field 0, x] : SourceValue F) ≠ .tuple [.field 1, y] := by
  intro e
  injection e with e
  injection e with e _
  injection e with e
  exact zero_ne_one e

/-! ## `Nat` offsets as successor towers -/

/-- `n` `Nat.succ` layers over `x`, at no levels. -/
private def succTower : Nat → KExpr → KExpr
  | 0, x => x
  | n + 1, x => .app (.const Ix.Kernel.natSuccName []) (succTower n x)

private theorem succTower_add (k : Nat) (x : KExpr) :
    ∀ m, succTower m (succTower k x) = succTower (k + m) x
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc]
    exact congrArg (Ix.Kernel.Expr.app (.const Ix.Kernel.natSuccName [])) (succTower_add k x m)

private theorem red_succTower {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (n : Nat) {x y : KExpr}, Red env d x y → Red env d (succTower n x) (succTower n y)
  | 0, _, _, h => h
  | n + 1, _, _, h => .appArg (red_succTower n h)

private theorem defEq_succTower {env : Ix.Kernel.Env .anon} {d : Nat} {x y : KExpr}
    (h : DefEq env d x y) : ∀ n, DefEq env d (succTower n x) (succTower n y)
  | 0 => h
  | n + 1 => .app .refl (defEq_succTower h n)

/-- A literal unfolds to its successor tower over the literal `0` (`Red.natLit`, one layer at a
time, under `Red.appArg`). -/
private theorem red_lit_tower {env : Ix.Kernel.Env .anon} {d : Nat}
    (hlit : Ix.Kernel.natLitSupported env = true) :
    ∀ n, Red env d (.lit (.natVal n)) (succTower n (.lit (.natVal 0)))
  | 0 => .refl
  | n + 1 => by
    have h1 : Red env d (.lit (.natVal (n + 1)))
        (.app (.const Ix.Kernel.natSuccName []) (.lit (.natVal n))) := Red.natLit hlit
    exact .trans h1 (.appArg (red_lit_tower hlit n))

private theorem natAddLit_zero' (B : KExpr) : Ix.Kernel.Rules.natAddLit B 0 = B := by
  simp [Ix.Kernel.Rules.natAddLit]

private theorem natAddLit_ne' {B : KExpr} {n : Nat} (hn : n ≠ 0) :
    Ix.Kernel.Rules.natAddLit B n =
      .app (.app (.const Ix.Kernel.natAddName []) B) (.lit (.natVal n)) := by
  simp [Ix.Kernel.Rules.natAddLit, hn]

/-- `Nat.add b (lit m)` unfolds to the successor tower of height `m` over `b`
(`Red.natAddSucc`, then `Red.natAddZero`), at any level list of the head. -/
private theorem red_natAdd_tower {env : Ix.Kernel.Env .anon} {d : Nat}
    (hlit : Ix.Kernel.natLitSupported env = true)
    (hadd : Ix.Kernel.Rules.natAddTyOk (env.find? Ix.Kernel.natAddName) = true) (b : KExpr) :
    ∀ (m : Nat) (us : List KLevel),
      Red env d (.app (.app (.const Ix.Kernel.natAddName us) b) (.lit (.natVal m)))
        (succTower m b)
  | 0, us => .natAddZero hlit hadd .refl rfl
  | m + 1, us => by
    refine .trans (.natAddSucc hlit hadd) (.appArg ?_)
    by_cases hm : m = 0
    · subst hm
      rw [natAddLit_zero']
      exact .refl
    · rw [natAddLit_ne' hm]
      exact red_natAdd_tower hlit hadd b m []

/-- **An offset split reduces to its successor tower** over the base. -/
private theorem red_offsetSplit {env : Ix.Kernel.Env .anon} {d : Nat} {ps pa : Prop}
    (hlit : Ix.Kernel.natLitSupported env = true)
    (hadd : pa → Ix.Kernel.Rules.natAddTyOk (env.find? Ix.Kernel.natAddName) = true)
    {E B : KExpr} {k : Nat} (hs : Specs.DefEq.OffsetSplit ps pa E B k) :
    Red env d E (succTower k B) := by
  induction hs with
  | lit => exact red_lit_tower hlit _
  | succStop _ => exact .refl
  | succ _ _ ih => exact .appArg ih
  | addStop ha => exact red_natAdd_tower hlit (hadd ha) _ _ _
  | @add us x B m k ha _ ih =>
    have h1 := red_natAdd_tower (d := d) hlit (hadd ha) x m us
    have h2 := red_succTower (env := env) (d := d) m ih
    rw [succTower_add] at h2
    exact .trans h1 h2

/-- The outermost step of a split: a literal, or a step carrying its role guard. -/
private theorem split_cases {ps pa : Prop} {E B : KExpr} {k : Nat}
    (h : Specs.DefEq.OffsetSplit ps pa E B k) : E = .lit (.natVal k) ∨ ps ∨ pa := by
  cases h with
  | lit => exact .inl rfl
  | succStop hs => exact .inr (.inl hs)
  | succ hs _ => exact .inr (.inl hs)
  | addStop ha => exact .inr (.inr ha)
  | add ha _ => exact .inr (.inr ha)

/-- `natLitSupported` from a role in force whose block holds `Nat`, `Nat.zero` and `Nat.succ`. -/
private theorem natLit_of_natBlock {c : Ctx} (hc : CoreFacts c) {r : Ix.Kernel.Role}
    (hr : c.inForce r) (h0 : Ix.Kernel.Role.nat ∈ r.block)
    (h1 : Ix.Kernel.Role.natZero ∈ r.block) (h2 : Ix.Kernel.Role.natSucc ∈ r.block) :
    Ix.Kernel.natLitSupported c.env = true :=
  hc.env.natLit (Ctx.inForce_of_block_or_dep hc.env.tableWf hr (.inl h0))
    (Ctx.inForce_of_block_or_dep hc.env.tableWf hr (.inl h1))
    (Ctx.inForce_of_block_or_dep hc.env.tableWf hr (.inl h2))

private theorem natLit_of_natAdd {c : Ctx} (hc : CoreFacts c) (hr : c.inForce .natAdd) :
    Ix.Kernel.natLitSupported c.env = true :=
  natLit_of_natBlock hc
    (Ctx.inForce_of_block_or_dep (s := .nat) hc.env.tableWf hr (.inr (by decide)))
    (by decide) (by decide) (by decide)

private theorem natLit_of_natSucc {c : Ctx} (hc : CoreFacts c) (hr : c.inForce .natSucc) :
    Ix.Kernel.natLitSupported c.env = true :=
  natLit_of_natBlock hc
    (Ctx.inForce_of_block_or_dep (s := .nat) hc.env.tableWf hr (.inl (by decide)))
    (by decide) (by decide) (by decide)

/-- **Two splits at one offset with definitionally equal bases are definitionally equal**: two
literals at one offset are one term; otherwise a step's role is in force, which gives the
guards, and both sides reduce to successor towers over their bases (`DefEq.redBoth`), which
compare by congruence. -/
private theorem defEq_of_offsets {c : Ctx} (hc : CoreFacts c) {d : Nat} {A B BA BB : KExpr}
    {k : Nat} (ha : Specs.DefEq.OffsetSplit (c.inForce .natSucc) (c.inForce .natAdd) A BA k)
    (hb : Specs.DefEq.OffsetSplit (c.inForce .natSucc) (c.inForce .natAdd) B BB k)
    (hab : DefEq c.env d BA BB) : DefEq c.env d A B := by
  by_cases hboth : A = .lit (.natVal k) ∧ B = .lit (.natVal k)
  · obtain ⟨rfl, rfl⟩ := hboth
    exact .refl
  · have hg : c.inForce .natSucc ∨ c.inForce .natAdd := by
      rcases split_cases ha with h1 | h1 | h1
      · rcases split_cases hb with h2 | h2 | h2
        · exact absurd ⟨h1, h2⟩ hboth
        · exact .inl h2
        · exact .inr h2
      · exact .inl h1
      · exact .inr h1
    have hlit : Ix.Kernel.natLitSupported c.env = true :=
      hg.elim (natLit_of_natSucc hc) (natLit_of_natAdd hc)
    exact DefEq.redBoth (red_offsetSplit hlit hc.env.natAdd ha)
      (red_offsetSplit hlit hc.env.natAdd hb) (defEq_succTower hab k)

end IxVM.Refinement.Core.DefEqAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel.Rules (Red DefEq)
open IxVM.Refinement.Core.DefEqAux

set_option linter.unusedVariables false

/-! ## String literals -/

/-- `KernelDefEq::try_string_lit_one`: a string literal `t`, expanded to its constructor form and
δ-reduced once, compared with `s` (`Red.strLit`, the δ step, `DefEq.redL`). -/
theorem try_string_lit_one_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_string_lit_one" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_string_lit_one c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_string_lit_one».obs ev with
    ⟨x_bs, cs49, v53, m64, cs72, v76, m86, cs94, ld12, ev96, ev74, ev51, hc134⟩ |
    ⟨x_lit, ld12, hne135, he139, he140, hc141⟩ | ⟨v1, ld12, hne142, he146, he147, hc148⟩
  · subst hc134
    rcases hA.lit_of_load ld12 with ⟨lp, limbs, hx, -, -, -⟩ | ⟨bp, bytes, s, hx, hb, hs, rfl⟩
    · injection hx with _ hx'
      exact absurd hx' (by decide)
    · injection hx with _ _ hx'
      injection hx' with hx''
      subst hx''
      have e1 := ObsFn.heap_extends ev96
      have e2 := ObsFn.heap_extends ev74
      obtain ⟨hsup, hctor⟩ := ih.get (.nat .str_lit_to_ctor) (by lt_calls) ev96 rc _ rfl
        (good.sub fun x hx => by simp [hx]) hrc bytes s hb hs
      obtain ⟨L, hL⟩ := strLitToConstructor_app s
      rw [hL] at hctor
      obtain ⟨E', hE', hred⟩ := ih.get (.nat .str_lit_delta_step) (by lt_calls) ev74 rc v76 types
        rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hsup d Γ
        (types_mono e1 htypes) L (hctor d Γ)
      have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev51 rc v53 b types rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans e2) hrc) d Γ
        (types_mono (e1.trans e2) htypes) E' B hE' (Tm.mono (e1.trans e2) hB) hr
      have hs1 :
          Red c.env d (.lit (.strVal s)) (.app (.const Ix.Kernel.stringOfListName []) L) := by
        rw [← hL]
        exact .strLit hsup
      exact .redL (.trans hs1 hred) hde
  · exact absurd he139 hr
  · exact absurd he146 hr

/-- `KernelDefEq::try_string_lit_pair`: `try_string_lit_one` both ways (the second by
`DefEq.symm`). -/
theorem try_string_lit_pair_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_string_lit_pair" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_string_lit_pair c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_string_lit_pair».obs ev with
    ⟨m2, cs13, ev15, he52, he53, hc54⟩ | ⟨v1, m2, cs13, cs62, ev15, hne55, ev64, hc97⟩
  · subst hc54
    exact ih.get (.defEq .try_string_lit_one) (by lt_calls) ev15 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB field_one_ne_zero
  · subst hc97
    have ext := ObsFn.heap_extends ev15
    exact .symm (ih.get (.defEq .try_string_lit_one) (by lt_calls) ev64 rc b a types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) B A
      (Tm.mono ext hB) (Tm.mono ext hA) hr)

/-! ## η-expansion -/

/-- `KernelDefEq::try_eta_expand`: `DefEq.eta`. `b`'s io-inferred type head-normalizes to a `∀`
of the same binder datum (`pw_eq`) whose domain compares with the `λ`'s; the `λ`'s body, opened
under the left domain, compares with `b` applied to the opened variable (the stored
`App(lift(b, 1, 0), BVar 0)` under the context list with the left domain pushed). -/
theorem try_eta_expand_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_eta_expand" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_eta_expand c args h r h' calls := by
  intro rc ta ba la b types hargs good hrc d Γ htypes TA BA ℓ B hTA hBA hℓ hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_eta_expand».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, x_dom_b, w96, x_lb, m113, cs124, m148, cs159, ev14, ev52, ld88,
      ev126, ev161, he198, he199, hc200⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, x_dom_b, w96, x_lb, m113, cs124, v147, m148, cs159, v205, m206,
      cs216, m242, m264, m295, cs328, ev14, ev52, ld88, ev126, ev161, hne201, ev218, hm252, hm274,
      hm305, ev330, hc363⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, x_dom_b, w96, x_lb, v112, m113, cs124, ev14, ev52, ld88, ev126,
      hne364, he368, he369, hc370⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, ev14, ev52, ld88, hne371, he375, he376, hc377⟩
  · exact absurd he198 hr
  · subst hc363
    have e1 := ObsFn.heap_extends ev14
    have e2 := ObsFn.heap_extends ev52
    have e3 := ObsFn.heap_extends ev126
    have e4 := ObsFn.heap_extends ev161
    have e5 := ObsFn.heap_extends ev218
    have e6 : Heap.Extends m206 m242 := by rw [hm252]; exact Heap.Extends.snoc _ _
    have e7 : Heap.Extends m242 m264 := by rw [hm274]; exact Heap.Extends.snoc _ _
    have e8 : Heap.Extends m264 m295 := by rw [hm305]; exact Heap.Extends.snoc _ _
    have E40 : Heap.Extends h m40 := e1.trans e2
    have E113 : Heap.Extends h m113 := E40.trans e3
    have E148 : Heap.Extends h m148 := E113.trans e4
    have E264 : Heap.Extends h m264 := (E148.trans e5).trans (e6.trans e7)
    have E295 : Heap.Extends h m295 := E264.trans e8
    -- `b`'s io-inferred type, head-normalized to a `∀`
    obtain ⟨TB, hTB, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes B hB
    obtain ⟨WB, hWB, hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc v1 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) TB hTB
    obtain ⟨D, BD, ℓb, rfl, hD, -, hℓb⟩ := hWB.forallE_of_load ld88
    -- the binder data agree
    obtain ⟨hpw, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev126 la x_lb rfl
      (good.sub fun x hx => by simp [hx]) ℓ ℓb (hℓ.mono E40) hℓb
    have hz : ℓ.zeronessOf = ℓb.zeronessOf := of_ite_field_ne_zero hpw field_one_ne_zero
    -- the domains
    have hdom := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev161 rc ta x_dom_b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E113 hrc) d Γ (types_mono E113 htypes) TA D
      (Tm.mono E113 hTA) (Tm.mono e3 hD) hne201
    -- `b` lifted past the new binder: the same image, one depth further in
    have hlift := ih.get (.subst .expr_lift) (by lt_calls) ev218 b 1 0 rfl
      (good.sub fun x hx => by simp [hx]) (by have := fval_one; omega) 0 1
      (by have := fval_one; omega) d (Ghost.extend Γ d TA) B
      (by rw [fval_zero]; exact tm_extend (Tm.mono E148 hB))
    simp only [fval_zero, Nat.add_zero] at hlift
    -- the stored `App(b↑, BVar 0)`: `b` applied to the new opened variable
    have happ : c.tm (d + 1) (Ghost.extend Γ d TA) m264 (.app B (.fvar d TA))
        (.ptr (.enum kexprEnum) m242.length) := by
      have hv : c.tm (d + 1) (Ghost.extend Γ d TA) m242 (.fvar d TA)
          (.ptr (.enum kexprEnum) m206.length) := by
        rw [hm252]
        exact tm_store_bvar0 m206
      rw [hm274]
      exact Tm.store_app (Tm.mono e6 hlift) hv
    -- the context list with the left domain pushed, and the body opened under it
    have hinner : c.types (Ghost.extend Γ d TA) m295 (d + 1)
        (.ptr (.enum kexprListEnum) m264.length) := by
      rw [hm305]
      exact types_store_cons (types_mono E264 htypes) (Tm.mono E264 hTA)
    have hbody := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev330 rc ba _ _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E295 hrc) (d + 1) (Ghost.extend Γ d TA)
      hinner _ _ (tmk_open (Tm.mono E295 hBA)) (Tm.mono e8 happ) hr
    exact .eta hinf hred (.symm hdom) hbody (by unfold bmeta; exact hz)
  · exact absurd he368 hr
  · exact absurd he375 hr

/-- `KernelDefEq::try_eta_swap`: exactly one side a `λ`, η-expanded against the other
(`try_eta_expand`; `DefEq.symm` when the `λ` is on the right). -/
theorem try_eta_swap_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_eta_swap" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_eta_swap c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_eta_swap».obs ev with
    ⟨x_ta, x_ba, x_la, w54, w55, w56, ld12, ld46, he72, he73, hc74⟩ |
    ⟨x_ta, x_ba, x_la, v35, cs82, ld12, ld46, hne75, ev84, hc133⟩ |
    ⟨v1, x_tb, x_bb, x_lb, cs175, ld12, hne134, ld149, ev177, hc226⟩ |
    ⟨v1, v138, ld12, hne134, ld149, hne227, he231, he232, hc233⟩
  · exact absurd he72 hr
  · subst hc133
    obtain ⟨TA, BA, ℓ, rfl, hTA, hBA, hℓ⟩ := hA.lam_of_load ld12
    exact ih.get (.defEq .try_eta_expand) (by lt_calls) ev84 rc x_ta x_ba x_la b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TA BA ℓ B hTA hBA hℓ hB hr
  · subst hc226
    obtain ⟨TB, BB, ℓ, rfl, hTB, hBB, hℓ⟩ := hB.lam_of_load ld149
    exact .symm (ih.get (.defEq .try_eta_expand) (by lt_calls) ev177 rc x_tb x_bb x_lb a types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes TB BB ℓ A hTB hBB hℓ hA hr)
  · exact absurd he231 hr

/-! ## `Nat` literals and offsets -/

/-- `KernelDefEq::is_nat_zero`: a literal whose limbs are zero (`klimbs_is_zero`), or a
constant at an address the table binds to `Nat.zero`, in force (`role_is`), at no levels
(`lvls_empty`); the key of that address is the role's (`keyOf_of_addressOf`). -/
theorem is_nat_zero_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::is_nat_zero" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.is_nat_zero c args h r h' calls := by
  intro rc e hargs good hrc hr d Γ E hE
  subst hargs
  rcases Obs.«KernelDefEq::is_nat_zero».obs ev with
    ⟨x_limbs, cs49, ld12, ev51, hc60⟩ | ⟨x_lit, ld12, hne61, he65, he66, hc67⟩ |
    ⟨x_caddr, x_clvls, x85, y86, m87, cs96, v101, m117, cs125, cs131, ld12, ev127, ev98, ev133,
      op92, hc142⟩ |
    ⟨v1, ld12, hne68, hne143, he147, he148, hc149⟩
  · subst hc60
    rcases hE.lit_of_load ld12 with ⟨lp, limbs, hx, hrl, -, rfl⟩ | ⟨bp, bytes, s, hx, -, -, -⟩
    · injection hx with _ _ hx'
      injection hx' with hx''
      subst hx''
      have hz := ih.get (.nat .klimbs_is_zero) (by lt_calls) ev51 _ rfl
        (good.sub fun x hx => by simp [hx]) (limbsVal limbs)
        (by unfold RepLimbs; exact ⟨limbs, hrl, rfl⟩)
      have h0 : limbsVal limbs = 0 := of_ite_field_ne_zero hz hr
      rw [h0]
      exact .inl rfl
    · injection hx with _ hx'
      exact absurd hx' (by decide)
  · exact absurd he65 hr
  · subst hc142
    obtain ⟨a, us, rfl, ha, hus⟩ := hE.const_of_load ld12
    obtain ⟨rfl, rfl⟩ := ih.get (.roles .role_nat_zero) (by lt_calls) ev127 rfl
    obtain ⟨hx85, hy86⟩ := mul_field_ne_zero op92 hr
    obtain ⟨haddr, -⟩ := ih.get (.roles .role_is) (by lt_calls) ev98 rc x_caddr a .natZero rfl
      (good.sub fun x hx => by simp [hx]) hrc ha hx85
    have e1 := ObsFn.heap_extends ev98
    obtain ⟨hy, -⟩ := ih.get (.nat .lvls_empty) (by lt_calls) ev133 x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us (LvListRep.mono e1 hus)
    have hus0 : us = [] := of_ite_field_ne_zero hy hy86
    subst hus0
    have hk : c.κ (ixAddr a) = .role .natZero := keyOf_of_addressOf hc.env.tableWf haddr
    rw [hk]
    exact .inr rfl
  · exact absurd he147 hr

/-- `KernelDefEq::try_def_eq_nat`: both sides zero readings (`DefEq.refl`, `DefEq.natZero`,
`DefEq.symm`), or both split at one offset (`nat_offset_of`, `klimbs_eq`) with definitionally
equal bases, carried back through successor towers (`defEq_of_offsets`). -/
theorem try_def_eq_nat_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_def_eq_nat" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_def_eq_nat c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB y hy hy0
  subst hargs
  rcases Obs.«KernelDefEq::try_def_eq_nat».obs ev with
    ⟨v1, m2, cs12, v31, m32, cs42, ev14, ev44, op77, he88, he101, hc102⟩ |
    ⟨v1, m2, cs12, v31, m32, cs42, v61, m108, cs119, x_ma, x_ba, x_oa, m160, cs171, x_mb, x_bb,
      x_ob, ev14, ev44, op77, hne103, ev121, ev173, op227, he238, he251, hc252⟩ |
    ⟨v1, m2, cs12, v31, m32, cs42, v61, m108, cs119, x_ma, x_ba, x_oa, m160, cs171, x_mb, x_bb,
      x_ob, v211, m258, cs269, ev14, ev44, op77, hne103, ev121, ev173, op227, hne253, ev271, he296,
      he309, hc310⟩ |
    ⟨v1, m2, cs12, v31, m32, cs42, v61, m108, cs119, x_ma, x_ba, x_oa, m160, cs171, x_mb, x_bb,
      x_ob, v211, v257, m258, cs269, v318, m327, cs335, ev14, ev44, op77, hne103, ev121, ev173,
      op227, hne253, ev271, hne311, he319, ev337, he370, hc371⟩
  · -- both zero readings
    subst hc102
    obtain ⟨hz1, hz2⟩ := mul_field_ne_zero op77 field_one_ne_zero
    have e1 := ObsFn.heap_extends ev14
    have hA0 := ih.get (.defEq .is_nat_zero) (by lt_calls) ev14 rc a rfl
      (good.sub fun x hx => by simp [hx]) hrc hz1 d Γ A hA
    have hB0 := ih.get (.defEq .is_nat_zero) (by lt_calls) ev44 rc b rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hz2 d Γ B (Tm.mono e1 hB)
    rcases hA0 with rfl | rfl <;> rcases hB0 with rfl | rfl
    · exact .refl
    · exact .natZero
    · exact .symm .natZero
    · exact .refl
  · subst he238
    exact absurd hy tuple_zero_ne
  · subst he296
    exact absurd hy tuple_zero_ne
  · -- equal offsets, definitionally equal bases
    subst hc371 he319
    have hyv : v318 = y := by simpa using hy
    subst hyv
    obtain ⟨hma, hmb⟩ := mul_field_ne_zero op227 hne253
    have e1 := ObsFn.heap_extends ev14
    have e2 := ObsFn.heap_extends ev44
    have e3 := ObsFn.heap_extends ev121
    have e4 := ObsFn.heap_extends ev173
    have E32 : Heap.Extends h m32 := e1.trans e2
    have E108 : Heap.Extends h m108 := E32.trans e3
    have E160 : Heap.Extends h m160 := E108.trans e4
    obtain ⟨BA, ka, hsa, hBA, hka⟩ := (ih.get (.defEq .nat_offset_of) (by lt_calls) ev121 rc a rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E32 hrc)).2 x_ma x_ba x_oa rfl hma d Γ A
      (Tm.mono E32 hA)
    obtain ⟨BB, kb, hsb, hBB, hkb⟩ := (ih.get (.defEq .nat_offset_of) (by lt_calls) ev173 rc b
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E108 hrc)).2 x_mb x_bb x_ob rfl hmb d Γ
      B (Tm.mono E108 hB)
    obtain ⟨la, hla, rfl⟩ := hka
    obtain ⟨lb, hlb, rfl⟩ := hkb
    obtain ⟨hkeq, rfl⟩ := ih.get (.levels .klimbs_eq) (by lt_calls) ev271 x_oa x_ob rfl
      (good.sub fun x hx => by simp [hx]) la lb (repList_heapMono₂ _ repU64_heapMono₂ e4 hla) hlb
    have hll : la = lb := of_ite_field_ne_zero hkeq hne311
    subst hll
    have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev337 rc x_ba x_bb types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E160 hrc) d Γ (types_mono E160 htypes) BA BB
      (Tm.mono e4 hBA) hBB hy0
    exact defEq_of_offsets hc hsa hsb hde

end IxVM.Refinement.Core
