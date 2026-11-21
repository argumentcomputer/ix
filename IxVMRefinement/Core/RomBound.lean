import Ix.IxVM.Consistency.Statement
import Aiur.HeapMono
import Mathlib.Data.List.Forall2
import Mathlib.Data.Finset.Card

/-! # Sizes from the trace's memory

IxVM counts with field elements (`Lists::length`, the index arithmetic of `Lists::lookup`,
`take` and `drop`, a level's successor offsets, de Bruijn depths), and a count is faithful
only below the field's characteristic. The consistency statement bounds the trace's memory,
not the calls: a bounded derivation's calls are carried by a valid ROM of at most `2^39`
addresses (`IxVM.Consistency.Bounded`, `ROMAddressesAtMost`). This module turns that into
sizes.

* **Counting addresses.** `length_le_of_nodup`, `finset_card_le`: pairwise different
  addresses that hold cells are at most the bound; `sum_length_le`: so is the total over
  address lists that share no address.
* **Descents.** A `HeapDescent h t p d` is a walk of `d` steps from the pointer `p` down
  through heap cells of one type `t`, each step to a pointer among the cell's arguments (a
  list's tail, a level's successor or operand, a term's body). If `p` is represented in a
  valid ROM, the walk's cells sit at `d + 1` pairwise different addresses (`HeapDescent.toROM`,
  `ROMDescent.nodup`): validity gives each address one cell of each type, and a represented
  pointer has no cycle of cells below it (`descentBound_of_represents`). So `d` is below the
  bound (`HeapDescent.lt`). This covers the depth of a path through any represented
  tree-shaped structure, whatever its constructors.
* **Lists.** `HeapDescent.of_list`, `length_lt`: a list a valid ROM of at most `n` addresses
  represents has fewer than `n` elements. `sum_length_le_of_descents`: descents whose cells
  are at pairwise different addresses have at most `n` cells in total.
* **Bounded derivations.** `bounded_mono`; `bounded_descent_lt`, `bounded_length_lt`: a
  descent, or a list, from an argument of any call of a bounded derivation is shorter than
  `2^39`. `chain_le` is the form for a size given by a relation on addresses.

What the memory bound does not give is a bound on calls: a memoized callee may be called on
more than `2^39` argument lists that differ only in field values, with no structure in the ROM
behind them (a recursion on a field counter). The counts the layers bound are not numbers of
calls: they are sizes of structures the run reads from its memory (lists, levels, terms,
application spines, indices into them), or values it decoded. -/

namespace IxVM.Refinement.RomBound

open Aiur
open Aiur.Generic.SourceSemantics (Call CallsInROM)
open IxVM.Consistency (ROMAddressesAtMost Bounded)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {F : Type} {rom : ROM F} {n : Nat}

/-! ## Counting addresses -/

/-- **Pairwise different addresses that hold cells of a ROM are at most its address bound.** -/
theorem length_le_of_nodup (bound : ROMAddressesAtMost rom n) {A : List F} (nodup : A.Nodup)
    (present : ∀ a ∈ A, ∃ v, (a, v) ∈ rom.entries) : A.length ≤ n := by
  obtain ⟨addrs, small, cover⟩ := bound
  have sub : A ⊆ addrs := by
    intro a member
    obtain ⟨v, entry⟩ := present a member
    exact cover (a, v) entry
  exact (nodup.subperm sub).length_le.trans small

/-- **A set of addresses that hold cells of a ROM has at most its address bound.** -/
theorem finset_card_le (bound : ROMAddressesAtMost rom n) (S : Finset F)
    (present : ∀ a ∈ S, ∃ v, (a, v) ∈ rom.entries) : S.card ≤ n := by
  have := length_le_of_nodup bound S.nodup_toList
    (fun a member => present a (Finset.mem_toList.mp member))
  simpa using this

/-- **Address lists that share no address total at most the ROM's address bound.** -/
theorem sum_length_le (bound : ROMAddressesAtMost rom n) {As : List (List F)}
    (nodup : ∀ A ∈ As, A.Nodup) (disjoint : As.Pairwise List.Disjoint)
    (present : ∀ A ∈ As, ∀ a ∈ A, ∃ v, (a, v) ∈ rom.entries) :
    (As.map List.length).sum ≤ n := by
  rw [← List.length_flatten]
  apply length_le_of_nodup bound (List.nodup_flatten.mpr ⟨nodup, disjoint⟩)
  intro a member
  obtain ⟨A, inAs, inA⟩ := List.mem_flatten.mp member
  exact present A inAs a inA

/-- **Cells whose sizes `0 … k` their addresses determine need `k + 1` addresses.** `Size a j`
says the cell at `a` holds a structure of size `j`; it must be functional. -/
theorem chain_le (bound : ROMAddressesAtMost rom n) (Size : F → Nat → Prop)
    (functional : ∀ a i j, Size a i → Size a j → i = j) {k : Nat}
    (chain : ∀ j ≤ k, ∃ a, (∃ v, (a, v) ∈ rom.entries) ∧ Size a j) : k + 1 ≤ n := by
  have pick : ∀ j : Fin (k + 1), ∃ a, (∃ v, (a, v) ∈ rom.entries) ∧ Size a j :=
    fun j => chain j (Nat.lt_succ_iff.mp j.isLt)
  let f : Fin (k + 1) → F := fun j => Classical.choose (pick j)
  have hf : ∀ j, (∃ v, (f j, v) ∈ rom.entries) ∧ Size (f j) j :=
    fun j => Classical.choose_spec (pick j)
  have inj : Function.Injective f := by
    intro i j same
    have sized : Size (f i) j := by rw [same]; exact (hf j).2
    exact Fin.ext (functional _ _ _ (hf i).2 sized)
  have := length_le_of_nodup bound ((List.nodup_finRange (k + 1)).map inj) (by
    intro a member
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp member
    exact (hf j).1)
  simpa using this

/-! ## Descents -/

/-- The arguments of a value: a tuple's items, a constructor's arguments. -/
def cellArgs {α A : Type} : Value α A → List (Value α A)
  | .field _ => []
  | .tuple items => items
  | .ptr _ _ => []
  | .construct _ _ args => args

/-- **A descent through heap cells of one type**: `HeapDescent h t p d` when `p` points (to
type `t`) at a cell of the heap and, if `d > 0`, one of the cell's arguments starts a descent
of `d - 1` further steps. -/
inductive HeapDescent (h : Heap F) (t : Ty) : SourceValue F → Nat → Prop where
  | here {loc : Nat} {v : SourceValue F} (cell : h[loc]? = some v) (typed : v.type = t) :
      HeapDescent h t (.ptr t loc) 0
  | down {loc : Nat} {v child : SourceValue F} {d : Nat} (cell : h[loc]? = some v)
      (typed : v.type = t) (arg : child ∈ cellArgs v) (rest : HeapDescent h t child d) :
      HeapDescent h t (.ptr t loc) (d + 1)

/-- **A descent through ROM cells of one type**, with the addresses of its cells in order. -/
inductive ROMDescent (rom : ROM F) (t : Ty) : Value F → List F → Prop where
  | here {a : F} {v : Value F} (cell : (a, v) ∈ rom.entries) (typed : v.type = t) :
      ROMDescent rom t (.ptr t a) [a]
  | down {a : F} {v w : Value F} {A : List F} (cell : (a, v) ∈ rom.entries) (typed : v.type = t)
      (arg : w ∈ cellArgs v) (rest : ROMDescent rom t w A) : ROMDescent rom t (.ptr t a) (a :: A)

/-- Every descent of type `t` from `w` has at most `H` cells. -/
abbrev DescentBound (rom : ROM F) (t : Ty) (w : Value F) (H : Nat) : Prop :=
  ∀ A, ROMDescent rom t w A → A.length ≤ H

/-- Every address of a descent holds a cell of the ROM. -/
theorem ROMDescent.present {t : Ty} {w : Value F} {A : List F} (descent : ROMDescent rom t w A) :
    ∀ a ∈ A, ∃ v, (a, v) ∈ rom.entries := by
  induction descent with
  | @here a v cell typed =>
    intro b member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨v, cell⟩
  | @down a v w A cell typed arg rest ih =>
    intro b member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨v, cell⟩
    · exact ih b member

/-- A descent through one of its addresses can continue with any descent from there. -/
theorem ROMDescent.graft {t : Ty} {w : Value F} {A : List F} (descent : ROMDescent rom t w A) :
    ∀ b ∈ A, ∀ D, ROMDescent rom t (.ptr t b) D →
      ∃ E, ROMDescent rom t w E ∧ D.length ≤ E.length ∧ ∀ x ∈ D, x ∈ E := by
  induction descent with
  | @here a v cell typed =>
    intro b member D below
    obtain rfl := List.mem_singleton.mp member
    exact ⟨D, below, Nat.le_refl _, fun _ m => m⟩
  | @down a v w A cell typed arg rest ih =>
    intro b member D below
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨D, below, Nat.le_refl _, fun _ m => m⟩
    · obtain ⟨E, desc, longer, sub⟩ := ih b member D below
      exact ⟨a :: E, .down cell typed arg desc, by simp only [List.length_cons]; omega,
        fun x m => List.mem_cons_of_mem _ (sub x m)⟩

/-- A descent from a pointer whose descents are bounded never returns to its first cell:
repeating the loop would give descents of every length. -/
theorem ROMDescent.no_return {t : Ty} {a : F} {A : List F} {H : Nat}
    (bound : DescentBound rom t (.ptr t a) H) (descent : ROMDescent rom t (.ptr t a) (a :: A))
    (back : a ∈ A) : False := by
  have grow : ∀ m : Nat, ∃ B, ROMDescent rom t (.ptr t a) (a :: B) ∧ a ∈ B ∧ m ≤ B.length := by
    intro m
    induction m with
    | zero => exact ⟨A, descent, back, Nat.zero_le _⟩
    | succ m ih =>
      obtain ⟨B, desc, inB, long⟩ := ih
      cases desc with
      | here cell typed => cases inB
      | down cell typed arg rest =>
        obtain ⟨E, descE, longer, sub⟩ := rest.graft a inB (a :: B) (.down cell typed arg rest)
        refine ⟨E, .down cell typed arg descE, sub a (List.mem_cons_self ..), ?_⟩
        simp only [List.length_cons] at longer
        omega
  obtain ⟨B, desc, -, long⟩ := grow (H + 1)
  have := bound _ desc
  simp only [List.length_cons] at this
  omega

/-- **A descent from a pointer whose descents are bounded has its cells at pairwise
different addresses.** -/
theorem ROMDescent.nodup {t : Ty} {w : Value F} {A : List F} (descent : ROMDescent rom t w A) :
    ∀ {H : Nat}, DescentBound rom t w H → A.Nodup := by
  induction descent with
  | here => intro H bound; exact List.nodup_singleton _
  | @down a v w A cell typed arg rest ih =>
    intro H bound
    have below : DescentBound rom t w H := by
      intro B d
      have := bound _ (.down cell typed arg d)
      simp only [List.length_cons] at this
      omega
    exact List.nodup_cons.mpr
      ⟨fun back => ROMDescent.no_return bound (.down cell typed arg rest) back, ih below⟩

/-- **The descents from a value represented in a valid ROM are bounded**: the representation
is a finite derivation, and validity makes every descent follow it. -/
theorem descentBound_of_represents (valid : rom.Valid) {h : Heap F} {p : SourceValue F}
    {w : Value F} (rep : Represents rom h p w) : ∃ H, ∀ t, DescentBound rom t w H := by
  suffices key : ∃ H, (∀ t, DescentBound rom t w H) ∧
      ∀ w' ∈ cellArgs w, ∀ t, DescentBound rom t w' H by
    obtain ⟨H, bounded, -⟩ := key
    exact ⟨H, bounded⟩
  induction rep using Represents.rec
    (motive_2 := fun _ targets _ => ∃ H, ∀ w' ∈ targets, ∀ t, DescentBound rom t w' H) with
  | field => exact ⟨0, (fun t A d => by cases d), fun w' m => by simp [cellArgs] at m⟩
  | tuple _ ih =>
    obtain ⟨H, args⟩ := ih
    exact ⟨H, (fun t A d => by cases d), args⟩
  | construct _ ih =>
    obtain ⟨H, args⟩ := ih
    exact ⟨H, (fun t A d => by cases d), args⟩
  | ptr source cell contents ih =>
    obtain ⟨H, -, args⟩ := ih
    refine ⟨H + 1, ?_, fun w' m => by simp [cellArgs] at m⟩
    intro t A d
    cases d with
    | here cell' typed' =>
      simp only [List.length_cons, List.length_nil]
      omega
    | @down _ v' _ _ cell' typed' arg rest =>
      obtain rfl : _ = v' := valid _ cell _ cell' rfl typed'.symm
      have := args _ arg _ _ rest
      simp only [List.length_cons]
      omega
  | nil => exact ⟨0, fun w' m => by cases m⟩
  | cons _ _ head tail =>
    obtain ⟨H₁, here, -⟩ := head
    obtain ⟨H₂, rest⟩ := tail
    refine ⟨max H₁ H₂, fun w' m t A d => ?_⟩
    rcases List.mem_cons.mp m with rfl | m
    · exact (here t A d).trans (le_max_left _ _)
    · exact (rest w' m t A d).trans (le_max_right _ _)

private theorem represents_ptr_inv {h : Heap F} {t : Ty} {loc : Nat} {w : Value F}
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

private theorem forall₂_mem {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (related : List.Forall₂ R l₁ l₂) : ∀ {x : α}, x ∈ l₁ → ∃ y, y ∈ l₂ ∧ R x y := by
  induction related with
  | nil => intro x member; cases member
  | @cons a b l₁ l₂ head _ ih =>
    intro x member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨b, List.mem_cons_self .., head⟩
    · obtain ⟨y, inY, related⟩ := ih member
      exact ⟨y, List.mem_cons_of_mem _ inY, related⟩

private theorem represents_arg {h : Heap F} {v : SourceValue F} {encoded : Value F}
    (rep : Represents rom h v encoded) {child : SourceValue F} (arg : child ∈ cellArgs v) :
    ∃ w, w ∈ cellArgs encoded ∧ Represents rom h child w := by
  cases rep with
  | field => simp [cellArgs] at arg
  | tuple items => exact forall₂_mem items arg
  | construct items => exact forall₂_mem items arg
  | ptr _ _ _ => simp [cellArgs] at arg

/-- **A heap descent from a represented pointer is a ROM descent** with one cell per step,
plus the first. -/
theorem HeapDescent.toROM {h : Heap F} {t : Ty} {p : SourceValue F} {d : Nat}
    (descent : HeapDescent h t p d) :
    ∀ {w : Value F}, Represents rom h p w → ∃ A, ROMDescent rom t w A ∧ A.length = d + 1 := by
  induction descent with
  | @here loc v cell typed =>
    intro w rep
    obtain ⟨stored, address, encoded, src, mem, contents, rfl⟩ := represents_ptr_inv rep
    rw [cell] at src
    cases src
    have htype : encoded.type = t := contents.type.symm.trans typed
    subst htype
    exact ⟨[address], .here mem rfl, rfl⟩
  | @down loc v child d cell typed arg rest ih =>
    intro w rep
    obtain ⟨stored, address, encoded, src, mem, contents, rfl⟩ := represents_ptr_inv rep
    rw [cell] at src
    cases src
    have htype : encoded.type = t := contents.type.symm.trans typed
    obtain ⟨w', arg', rep'⟩ := represents_arg contents arg
    obtain ⟨A, below, counted⟩ := ih rep'
    subst htype
    exact ⟨address :: A, .down mem rfl arg' below, by simp [counted]⟩

/-- **A descent from a pointer a valid ROM of at most `n` addresses represents takes fewer
than `n` steps.** -/
theorem HeapDescent.lt (valid : rom.Valid) (bound : ROMAddressesAtMost rom n) {h : Heap F}
    {t : Ty} {p : SourceValue F} {w : Value F} {d : Nat} (rep : Represents rom h p w)
    (descent : HeapDescent h t p d) : d < n := by
  obtain ⟨A, path, counted⟩ := descent.toROM rep
  obtain ⟨H, bounded⟩ := descentBound_of_represents valid rep
  have := length_le_of_nodup bound (path.nodup (bounded t)) path.present
  omega

/-- **Descents whose cells are at pairwise different addresses have at most `n` cells in
total**, from values represented in a valid ROM of at most `n` addresses (for descents of one
type: descents that share no cell). -/
theorem sum_length_le_of_descents (valid : rom.Valid) (bound : ROMAddressesAtMost rom n)
    {As : List (List F)}
    (descents : ∀ A ∈ As, ∃ (t : Ty) (h : Heap F) (p : SourceValue F) (w : Value F),
      Represents rom h p w ∧ ROMDescent rom t w A)
    (disjoint : As.Pairwise List.Disjoint) : (As.map List.length).sum ≤ n :=
  sum_length_le bound
    (fun A member => by
      obtain ⟨t, h, p, w, rep, descent⟩ := descents A member
      obtain ⟨H, bounded⟩ := descentBound_of_represents valid rep
      exact descent.nodup (bounded t))
    disjoint
    (fun A member => by
      obtain ⟨_, _, _, _, _, descent⟩ := descents A member
      exact descent.present)

/-! ## Lists -/

/-- **A represented list's spine is a descent** of one step per element. -/
theorem HeapDescent.of_list {α : Type*} {en nil cons : String}
    {R : Heap F → α → SourceValue F → Prop} {h : Heap F} {xs : List α} {p : SourceValue F}
    (list : RepLinkedList en nil cons R h xs p) : HeapDescent h (.enum en) p xs.length := by
  induction list with
  | nil cell => exact .here cell (by simp [Value.type])
  | cons cell _ _ ih => exact .down cell (by simp [Value.type]) (by simp [cellArgs]) ih

/-- **A list a valid ROM of at most `n` addresses represents has fewer than `n` elements**,
whatever its elements and their representation. -/
theorem length_lt {α : Type*} {en nil cons : String} {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {p : SourceValue F} {w : Value F}
    (valid : rom.Valid) (bound : ROMAddressesAtMost rom n) (rep : Represents rom h p w)
    (list : RepLinkedList en nil cons R h xs p) : xs.length < n :=
  (HeapDescent.of_list list).lt valid bound rep

/-! ## Bounded derivations -/

/-- A sub-derivation of a bounded derivation is bounded: its calls are among the
derivation's. -/
theorem bounded_mono {calls₁ calls₂ : List (Call IxVM.F)} (bounded : Bounded calls₂)
    (sub : ∀ c ∈ calls₁, c ∈ calls₂) : Bounded calls₁ := by
  obtain ⟨rom, valid, bound, carried⟩ := bounded
  exact ⟨rom, valid, bound, fun c member => carried c (sub c member)⟩

/-- **A descent from an argument of a call of a bounded derivation takes fewer than `2^39`
steps.** -/
theorem bounded_descent_lt {calls : List (Call IxVM.F)} (bounded : Bounded calls)
    {c : Call IxVM.F} (called : c ∈ calls) {p : SourceValue IxVM.F} (argument : p ∈ c.args)
    {t : Ty} {d : Nat} (descent : HeapDescent c.heap t p d) : d < 2 ^ 39 := by
  obtain ⟨rom, valid, bound, carried⟩ := bounded
  obtain ⟨w, rep⟩ := carried c called p argument
  exact descent.lt valid bound rep

/-- **A list an argument of a call of a bounded derivation represents has fewer than `2^39`
elements.** -/
theorem bounded_length_lt {calls : List (Call IxVM.F)} (bounded : Bounded calls)
    {c : Call IxVM.F} (called : c ∈ calls) {p : SourceValue IxVM.F} (argument : p ∈ c.args)
    {α : Type*} {en nil cons : String} {R : Heap IxVM.F → α → SourceValue IxVM.F → Prop}
    {xs : List α} (list : RepLinkedList en nil cons R c.heap xs p) : xs.length < 2 ^ 39 :=
  bounded_descent_lt bounded called argument (HeapDescent.of_list list)

end IxVM.Refinement.RomBound
