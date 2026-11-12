import IxVMRefinement.Lib.Lists
import Ix.IxVM.Consistency.Statement
import Mathlib.Data.List.Forall2

/-! # Counted chains: a count IxVM keeps as a field element is small

IxVM measures lists and counts with field elements (`Lists::length`, the counters of
`Lists::drop`/`take`, telescope and spine walks), so reasoning about such a count needs it
below the field's characteristic. The circuit bounds *distinct calls of each memoized
callee* (`MemoCallsAtMost … (2^39)` in a valid ROM), not calls counted with repetition.
The bridge is `chain_bound_gen`: if a memoized callee is called once for each
`j ≤ n`, and no two of those calls can share a key (their arguments are never
represented by one ROM value list), then the calls need `n + 1` distinct keys, so
`n + 1 ≤ N`.

`spine_length_eq` supplies the separation for list arguments: in a valid ROM, one value
represents lists of one length only. `length_lt_gen` applies both to `Lists::length`,
whose derivation on a list of length `n` calls itself on suffixes of every length
`j ≤ n`. -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List
open IxVM.Refinement.Obs (W)
open IxVM (F)
open IxVM.Consistency (MemoCallsAtMost memoCall)

/-! ## Distinct keys -/

/-- **A chain of calls that pairwise need different keys has as many keys as calls**: for
a memoized callee `name` under the bound `MemoCallsAtMost … N`, if for every `j ≤ n` some
call of `name` satisfies `P j`, and two calls satisfying `P j` and `P j'` whose argument
lists are represented by one ROM value list have `j = j'`, then `n + 1 ≤ N`. -/
theorem chain_bound_gen {rom : ROM F} {calls : List (Call F)} {N : Nat}
    (bound : MemoCallsAtMost IxVM.source rom calls N) {name : String}
    (memoized : memoCall IxVM.source name = true) {n : Nat} {P : Nat → Call F → Prop}
    (chain : ∀ j ≤ n, ∃ c ∈ calls, c.name = name ∧ P j c)
    (sep : ∀ j j' (c c' : Call F) (w : List (Value F)), P j c → P j' c' →
      List.Forall₂ (Represents rom c.heap) c.args w →
      List.Forall₂ (Represents rom c'.heap) c'.args w → j = j') :
    n + 1 ≤ N := by
  obtain ⟨keys, hlen, cover⟩ := bound name memoized
  have pick : ∀ j : Fin (n + 1), ∃ k, k ∈ keys ∧ ∃ c : Call F, P j c ∧
      List.Forall₂ (Represents rom c.heap) c.args k := by
    intro j
    obtain ⟨c, hc, hname, hp⟩ := chain j (Nat.lt_succ_iff.mp j.isLt)
    obtain ⟨k, hk, hfa⟩ := cover c hc hname
    exact ⟨k, hk, c, hp, hfa⟩
  let f : Fin (n + 1) → List (Value F) := fun j => Classical.choose (pick j)
  have hf : ∀ j, f j ∈ keys ∧ ∃ c : Call F, P j c ∧
      List.Forall₂ (Represents rom c.heap) c.args (f j) :=
    fun j => Classical.choose_spec (pick j)
  have inj : Function.Injective f := by
    intro j j' heq
    obtain ⟨_, c, hp, hc⟩ := hf j
    obtain ⟨_, c', hp', hc'⟩ := hf j'
    rw [heq] at hc
    exact Fin.ext (sep _ _ c c' _ hp hp' hc hc')
  have hnd : ((List.finRange (n + 1)).map f).Nodup := (List.nodup_finRange _).map inj
  have hsub : (List.finRange (n + 1)).map f ⊆ keys := by
    intro k hk
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hk
    exact (hf j).1
  have hle := (hnd.subperm hsub).length_le
  simp only [List.length_map, List.length_finRange] at hle
  omega

/-! ## Spines -/

/-- The cells of a list, whatever its elements. -/
abbrev Spine (en : String) (h : Heap F) (xs : List Unit) (p : SourceValue F) : Prop :=
  RepLinkedList en "Nil" "Cons" (fun _ _ _ => True) h xs p

theorem RepLinkedList.spine {α : Type} {en : String} {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {p : SourceValue F}
    (rep : RepLinkedList en "Nil" "Cons" R h xs p) : Spine en h (xs.map fun _ => ()) p := by
  induction rep with
  | nil cell => exact .nil cell
  | cons cell _ _ ih => exact .cons cell trivial ih

theorem represents_ptr_inv {rom : ROM F} {h : Heap F} {t : Aiur.Ty} {loc : Nat} {w : Value F}
    (r : Represents rom h (.ptr t loc) w) :
    ∃ stored address encoded, h[loc]? = some stored ∧ (address, encoded) ∈ rom.entries ∧
      Represents rom h stored encoded ∧ w = .ptr encoded.type address := by
  generalize hp : (Value.ptr t loc : SourceValue F) = p at r
  cases r with
  | ptr source cell contents =>
    injection hp with _ hl
    subst hl
    exact ⟨_, _, _, source, cell, contents, rfl⟩
  | field => cases hp
  | tuple _ => cases hp
  | construct _ => cases hp

theorem represents_construct_inv {rom : ROM F} {h : Heap F} {e c : String}
    {vs : List (SourceValue F)} {w : Value F} (r : Represents rom h (.construct e c vs) w) :
    ∃ ws, w = .construct e c ws ∧ List.Forall₂ (Represents rom h) vs ws := by
  generalize hp : (Value.construct e c vs : SourceValue F) = p at r
  cases r with
  | construct items =>
    injection hp with h1 h2 h3
    subst h1 h2 h3
    exact ⟨_, rfl, items⟩
  | field => cases hp
  | tuple _ => cases hp
  | ptr _ _ _ => cases hp

theorem forall₂_pair {α β : Type} {R : α → β → Prop} {a b : α} {ws : List β}
    (h : List.Forall₂ R [a, b] ws) : ∃ wa wb, ws = [wa, wb] ∧ R a wa ∧ R b wb := by
  obtain ⟨wa, u, ha, hu, rfl⟩ := List.forall₂_cons_left_iff.mp h
  obtain ⟨wb, u', hb, hu', rfl⟩ := List.forall₂_cons_left_iff.mp hu
  rw [List.forall₂_nil_left_iff] at hu'
  subst hu'
  exact ⟨wa, wb, rfl, ha, hb⟩

/-- The value a list cell is represented by, at a represented pointer. -/
theorem cell_represented {rom : ROM F} {h : Heap F} {en c : String} {addr : Nat}
    {vs : List (SourceValue F)} {w : Value F}
    (cell : h[addr]? = some (.construct en c vs)) (r : Represents rom h (.ptr (.enum en) addr) w) :
    ∃ address ws, (address, .construct en c ws) ∈ rom.entries ∧
      List.Forall₂ (Represents rom h) vs ws ∧ w = .ptr (.enum en) address := by
  obtain ⟨stored, address, encoded, src, mem, rep, rfl⟩ := represents_ptr_inv r
  rw [cell] at src
  cases src
  obtain ⟨ws, rfl, items⟩ := represents_construct_inv rep
  exact ⟨address, ws, mem, items, by simp [Value.type]⟩

/-- **In a valid ROM, a value represents lists of one length only**, whatever the heaps
the two lists live in. -/
theorem spine_length_eq {rom : ROM F} (valid : rom.Valid) {en : String} {h₁ h₂ : Heap F}
    {xs₁ xs₂ : List Unit} {p₁ p₂ : SourceValue F} {w : Value F}
    (s₁ : Spine en h₁ xs₁ p₁) (s₂ : Spine en h₂ xs₂ p₂)
    (r₁ : Represents rom h₁ p₁ w) (r₂ : Represents rom h₂ p₂ w) : xs₁.length = xs₂.length := by
  induction s₁ generalizing xs₂ p₂ w with
  | nil cell₁ =>
    obtain ⟨a₁, ws₁, mem₁, items₁, rfl⟩ := cell_represented cell₁ r₁
    cases s₂ with
    | nil _ => rfl
    | cons cell₂ _ _ =>
      obtain ⟨a₂, ws₂, mem₂, items₂, hw⟩ := cell_represented cell₂ r₂
      injection hw with _ ha
      have := valid _ mem₁ _ mem₂ ha (by simp [Value.type])
      injection this with _ hc _
      exact absurd hc (by decide)
  | cons cell₁ _ tail₁ ih =>
    obtain ⟨a₁, ws₁, mem₁, items₁, rfl⟩ := cell_represented cell₁ r₁
    obtain ⟨wh₁, wt₁, rfl, -, rt₁⟩ := forall₂_pair items₁
    cases s₂ with
    | nil cell₂ =>
      obtain ⟨a₂, ws₂, mem₂, items₂, hw⟩ := cell_represented cell₂ r₂
      injection hw with _ ha
      have := valid _ mem₁ _ mem₂ ha (by simp [Value.type])
      injection this with _ hc _
      exact absurd hc (by decide)
    | cons cell₂ _ tail₂ =>
      obtain ⟨a₂, ws₂, mem₂, items₂, hw⟩ := cell_represented cell₂ r₂
      obtain ⟨wh₂, wt₂, rfl, -, rt₂⟩ := forall₂_pair items₂
      injection hw with _ ha
      have := valid _ mem₁ _ mem₂ ha (by simp [Value.type])
      injection this with _ _ hws
      injection hws with _ hrest
      injection hrest with hwt _
      subst hwt
      simp only [List.length_cons]
      rw [ih tail₂ rt₁ rt₂]

/-- **Calls on single list arguments of different lengths need different keys** (the
separation `chain_bound_gen` asks for, for list-length chains). -/
theorem spine_sep {rom : ROM F} (valid : rom.Valid) {en : String} :
    ∀ j j' (c c' : Call F) (w : List (Value F)),
      (∃ p ys, c.args = [p] ∧ Spine en c.heap ys p ∧ ys.length = j) →
      (∃ p ys, c'.args = [p] ∧ Spine en c'.heap ys p ∧ ys.length = j') →
      List.Forall₂ (Represents rom c.heap) c.args w →
      List.Forall₂ (Represents rom c'.heap) c'.args w → j = j' := by
  intro j j' c c' w ⟨p, ys, hargs, hs, hys⟩ ⟨p', ys', hargs', hs', hys'⟩ hw hw'
  rw [hargs] at hw
  rw [hargs'] at hw'
  obtain ⟨w₀, u, hr, hu, rfl⟩ := List.forall₂_cons_left_iff.mp hw
  rw [List.forall₂_nil_left_iff] at hu
  subst hu
  obtain ⟨w₀', u', hr', hu', hw₀⟩ := List.forall₂_cons_left_iff.mp hw'
  injection hw₀ with hw₀ _
  subst hw₀
  rw [← hys, ← hys']
  exact spine_length_eq valid hs hs' hr hr'

/-! ## The chain of `Lists::length` -/

/-- **The calls of `Lists::length` on a list of length `n`**: for every `j ≤ n` one of them,
counting the derivation's own entry, is on a list of length `j`. -/
theorem length_chain (t : Generic.Ty) (n : Nat) :
    ∀ {l : SourceValue F} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
      {xs : List Unit},
      ObsFn W (Instance.mk "Lists::length" [t]).symbol [l] h r h' cs →
      Spine (Instance.mk "Lists::Node" [t]).symbol h xs l → xs.length = n →
      ∀ j ≤ n, ∃ c ∈ (⟨(Instance.mk "Lists::length" [t]).symbol, [l], h⟩ : Call F) :: cs,
        c.name = (Instance.mk "Lists::length" [t]).symbol ∧ ∃ p ys, c.args = [p] ∧
          Spine (Instance.mk "Lists::Node" [t]).symbol c.heap ys p ∧ ys.length = j := by
  induction n with
  | zero =>
    intro l h h' r cs xs ev hs hn j hj
    exact ⟨⟨(Instance.mk "Lists::length" [t]).symbol, [l], h⟩, by simp, rfl, l, xs, rfl, hs,
      by omega⟩
  | succ n ih =>
    intro l h h' r cs xs ev hs hn j hj
    rcases Obs.«Lists::length».obs ev with ⟨ld, -, -, -⟩ |
      ⟨w, rest, x, m, cs', ld, ev', -, -, rfl⟩
    · cases hs with
      | nil _ => simp at hn
      | cons cell _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        injection hv with _ hc _
        exact absurd hc (by decide)
    · cases hs with
      | nil _ => simp at hn
      | @cons _ xs' _ _ _ cell _ tail =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        injection hv with _ _ hargs
        injection hargs with _ htail
        injection htail with hrest _
        subst hrest
        by_cases hjn : j = n + 1
        · subst hjn
          exact ⟨⟨(Instance.mk "Lists::length" [t]).symbol, [_], h⟩, by simp, rfl, _, _, rfl,
            .cons cell trivial tail, hn⟩
        · simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
          obtain ⟨c, hc, rest⟩ := ih ev' tail hn j (by omega)
          exact ⟨c, List.mem_cons_of_mem _ hc, rest⟩

/-- **The list `Lists::length` measures is shorter than `2^39`**, at every element type
whose `Lists::length` instance is memoized (`memoized`, decided per instance with
`decide +kernel`), in a run whose calls, the derivation's own entry included, have at most
`2^39` distinct calls of each memoized callee in a valid ROM. -/
theorem length_lt_gen (t : Generic.Ty)
    (memoized : memoCall IxVM.source (Instance.mk "Lists::length" [t]).symbol = true)
    {rom : ROM F} (valid : rom.Valid) {calls : List (Call F)}
    (bound : MemoCallsAtMost IxVM.source rom calls (2 ^ 39))
    {l : SourceValue F} {m m' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn W (Instance.mk "Lists::length" [t]).symbol [l] m r m' cs)
    (hsub : ∀ x ∈ (⟨(Instance.mk "Lists::length" [t]).symbol, [l], m⟩ : Call F) :: cs, x ∈ calls)
    {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    (hl : RepLinkedList (Instance.mk "Lists::Node" [t]).symbol "Nil" "Cons" R m xs l) :
    xs.length < 2 ^ 39 := by
  have chain := length_chain t _ ev (RepLinkedList.spine hl) rfl
  have := chain_bound_gen bound memoized (n := (xs.map fun _ => ()).length)
    (P := fun j c => ∃ p ys, c.args = [p] ∧
      Spine (Instance.mk "Lists::Node" [t]).symbol c.heap ys p ∧ ys.length = j)
    (fun j hj => by
      obtain ⟨c, hc, hcn, rest⟩ := chain j hj
      exact ⟨c, hsub c hc, hcn, rest⟩)
    (spine_sep valid)
  simp only [List.length_map] at this
  omega

/-- `Lists::length` on IxVM's term lists is memoized. -/
theorem length_kexpr_memoized :
    memoCall IxVM.source (Instance.mk "Lists::length" [.ptr (.named "KernelTypes::KExprNode" [])]).symbol
      = true := by
  decide +kernel

/-- **`length_lt_gen` at IxVM's term lists** (`Lists::List<&KernelTypes::KExprNode>`). -/
theorem length_lt_kexpr {rom : ROM F} (valid : rom.Valid) {calls : List (Call F)}
    (bound : MemoCallsAtMost IxVM.source rom calls (2 ^ 39))
    {l : SourceValue F} {m m' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] m r m' cs)
    (hsub : ∀ x ∈ (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [l], m⟩ : Call F) :: cs,
      x ∈ calls)
    {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    (hl : RepLinkedList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" "Cons" R m xs l) :
    xs.length < 2 ^ 39 := by
  rw [← Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol] at ev hsub
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  exact length_lt_gen _ length_kexpr_memoized valid bound ev hsub hl

end IxVM.Refinement.Lib
