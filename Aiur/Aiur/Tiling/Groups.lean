import Aiur.Tiling.Sound

/-!
# Soundness of chunked message groups

`Template.checkGroups` splits the message rows of a template into one group
per lookup. A group of one row is an unchunked message (`MessageSound`). A
group of `J ≥ 2` rows is a keyed chunk group (`ChunkSound`): every row is
`[mult, key, chunk_c, …]` with a shared selector, tag and multiplicity slot,
`sub_c = chunkSub rom sub c`, and the chunks concatenate to the payload
(after the address, for a ROM lookup, whose key is the address). A call
receive's key is the invocation id, a ROM receive's address is a constant;
a send's multiplicity is 0 or 1.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

theorem keyedCells_eq (W mult key : Nat) (chunk : List Nat) :
    keyedCells W mult key chunk = messageCells W mult (key :: chunk) := by
  simp only [keyedCells, messageCells, List.map_cons, List.cons_append, List.length_cons]
  rw [show W - 1 - (chunk.length + 1) = W - 2 - chunk.length by omega]

/-- What a checked chunk group carries. -/
def ChunkSound (W : Nat) (val : Nat → F) (a : Var → F) (receive : Bool) (idv : Nat)
    (group : List (F × F × F × List (Option Nat))) (lookup : Lookup F) : Prop :=
  ∃ (sel tag sub : F) (mult key : Nat) (rom : Bool) (chunks : List (List Nat)),
    group = chunks.zipIdx.map (fun x => (sel, tag, chunkSub rom sub x.2, keyedCells W mult key x.1)) ∧
    2 ≤ chunks.length ∧ (∀ ch ∈ chunks, ch.length + 2 ≤ W) ∧
    lookup.multiplicity.denote a = sel * val mult ∧
    lookup.tuple a = tag :: sub :: ((if rom then [val key] else []) ++ chunks.flatten.map val) ∧
    (receive = true → rom = false → val key = val idv) ∧
    (receive = true → rom = true → ∃ k, lookup.args[2]? = some (.const k)) ∧
    (receive = false → sel * val mult = 0 ∨ sel * val mult = 1) ∧
    rom = (tag == 2)

theorem zero_or_one_of_sq {x : F} (h : x * x = x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

section Template

variable {T : Template F} {C : Circuit F} (checked : T.Checked C) {val : Nat → F}
  (holds : T.RelationsHold val)
include checked holds

theorem Template.Checked.values {ss : List Nat} {es : List (ArithExpr F)}
    (h : allPairs (fun s expr => T.wideSlot s && Poly.Identical (T.meaning s) (Poly.ofExpr expr)) ss es = true) :
    es.map (ArithExpr.denote (T.wide val)) = ss.map val := by
  replace h := (allPairs_iff _ ss es).mp h
  induction h with
  | nil => rfl
  | @cons s e _ _ step _ ih =>
      simp only [Bool.and_eq_true] at step
      have := Poly.Identical.denote (T.wide val) step.2
      rw [checked.meaning_val holds s step.1, Poly.denote_ofExpr] at this
      simp only [List.map_cons, this, ih]

theorem Template.Checked.chunk_sound {receive : Bool} {group : List (F × F × F × List (Option Nat))}
    {lookup : Lookup F} (check : T.checkChunked receive group lookup = true) :
    ChunkSound T.width val (T.wide val) receive T.idVar group lookup := by
  rcases lookup with ⟨multExpr, args⟩
  rcases args with _ | ⟨tagExpr, _ | ⟨subExpr, payload⟩⟩ <;>
    rcases group with _ | ⟨⟨sel, tag, sub0, _ | ⟨_ | mult, _ | ⟨_ | key, rest⟩⟩⟩, more⟩ <;>
    simp only [Template.checkChunked, Bool.false_eq_true] at check
  set group := (sel, tag, sub0, some mult :: some key :: rest) :: more with hgroup
  set rom := tag == 2
  set sub := sub0 - chunkSub rom 0 0
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at check
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨two, tagOk⟩, subOk⟩, rowsOk⟩, multWide⟩, multOk⟩, pairs⟩, keyOk⟩, recvOk⟩ := check
  have tagEq := Poly.Identical.denote (T.wide val) tagOk
  have subEq := Poly.Identical.denote (T.wide val) subOk
  rw [Poly.denote_ofExpr, Poly.denote_const] at tagEq subEq
  have row : ∀ c (hc : c < group.length), group[c] =
      (sel, tag, chunkSub rom sub c, keyedCells T.width mult key (Template.chunkCells group[c])) ∧
      (Template.chunkCells group[c]).length + 2 ≤ T.width := by
    intro c hc
    have := rowsOk (group[c], c) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hc]))
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨⟨⟨s1, s2⟩, s3⟩, len⟩, cells⟩ := this
    exact ⟨Prod.ext s1 (Prod.ext s2 (Prod.ext s3 cells)), len⟩
  refine ⟨sel, tag, sub, mult, key, rom, group.map Template.chunkCells, ?_, by simpa using two,
    ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · apply List.ext_getElem (by simp)
    intro c h1 h2
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    exact (row c h1).1
  · intro ch hch
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hch
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hm
    exact (row c hc).2
  · have := Poly.Identical.denote (T.wide val) multOk
    rw [Poly.denote_scale, checked.meaning_val holds mult multWide, Poly.denote_ofExpr] at this
    exact this.symm
  · simp only [Lookup.tuple, List.map_cons, tagEq, subEq, List.cons.injEq, true_and]
    cases hrom : rom
    · simp only [hrom, Bool.false_eq_true, ↓reduceIte, List.nil_append] at pairs ⊢
      exact checked.values holds pairs
    · have keyAddr : ∃ a payload', payload = a :: payload' ∧
          Poly.Identical (T.meaning key) (Poly.ofExpr a) = true ∧ T.wideSlot key = true := by
        simp only [hrom, ↓reduceIte, Bool.and_eq_true] at keyOk
        obtain ⟨wk, m⟩ := keyOk
        cases payload with
        | nil => simp at m
        | cons a p => exact ⟨a, p, rfl, m, wk⟩
      obtain ⟨a, payload', rfl, keyEq, wk⟩ := keyAddr
      have := Poly.Identical.denote (T.wide val) keyEq
      rw [checked.meaning_val holds key wk, Poly.denote_ofExpr] at this
      simp only [hrom, ↓reduceIte, List.drop_succ_cons, List.drop_zero] at pairs
      simp only [↓reduceIte, List.map_cons, List.singleton_append, this, checked.values holds pairs,
        List.flatMap_def]
  · intro hr hrom
    subst hr
    simp only [hrom, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at keyOk
    exact checked.invocation holds keyOk
  · intro hr hrom
    subst hr
    simp only [hrom, ↓reduceIte] at recvOk
    cases payload with
    | nil => simp at recvOk
    | cons a _ => cases a <;> simp at recvOk ⊢
  · intro hr
    subst hr
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at recvOk
    obtain ⟨rel, hrel, role, boolOk⟩ := recvOk
    have := Poly.Identical.denote val boolOk
    rw [holds rel hrel] at this
    simp [boolPoly] at this
    apply zero_or_one_of_sq
    linear_combination -this

end Template

end Aiur.Tiling

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

/-- What a checked message group carries: one unchunked row, or a chunk group. -/
def GroupSound (W : Nat) (val : Nat → F) (a : Var → F) (receive : Bool) (idv : Nat)
    (group : List (F × F × F × List (Option Nat))) (lookup : Lookup F) : Prop :=
  (∃ m, group = [m] ∧ MessageSound W val a m lookup) ∨ ChunkSound W val a receive idv group lookup

/-- A message row's cells: the multiplicity slot, then payload slots (key first
in a chunk row), then unused cells. -/
def RowShaped (W : Nat) (m : F × F × F × List (Option Nat)) : Prop :=
  ∃ mult ps, m.2.2.2 = messageCells W mult ps ∧ ps.length + 1 ≤ W

theorem forall₂_mem' {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons r _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self .., r⟩
      · obtain ⟨y, hy, ry⟩ := ih hx
        exact ⟨y, List.mem_cons_of_mem _ hy, ry⟩

theorem splitGroups_length (W : Nat) :
    ∀ (ms : List (F × F × F × List (Option Nat))) (ls : List (Lookup F)),
      (Template.splitGroups W ms ls).length = ls.length
  | _, [] => rfl
  | ms, _ :: ls => by simp [Template.splitGroups, splitGroups_length W _ ls]

theorem GroupSound.rowShaped {W : Nat} {val : Nat → F} {a : Var → F} {receive : Bool} {idv : Nat}
    {group : List (F × F × F × List (Option Nat))} {lookup : Lookup F}
    (h : GroupSound W val a receive idv group lookup) : ∀ m ∈ group, RowShaped W m := by
  rcases h with ⟨m, rfl, mult, ps, cells, len, _⟩ | ⟨sel, tag, sub, mult, key, rom, chunks, rfl, _, lens, _⟩
  · intro m' hm
    rw [List.mem_singleton.mp hm]
    exact ⟨mult, ps, cells, len⟩
  · intro m hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    have := lens x.1 (List.fst_mem_of_mem_zipIdx hx)
    exact ⟨mult, key :: x.1, keyedCells_eq _ _ _ _, by simp; omega⟩

section Template

variable {T : Template F} {C : Circuit F} (checked : T.Checked C) {val : Nat → F}
  (holds : T.RelationsHold val)
include checked holds

theorem Template.Checked.grouped (grouped : T.checkGroups C = true) :
    (Template.splitGroups T.width T.messages C.lookups).flatten = T.messages ∧
      ∀ l (hl : l < C.lookups.length),
        GroupSound T.width val (T.wide val) (l == 0) T.idVar
          ((Template.splitGroups T.width T.messages C.lookups)[l]'(by
            rw [splitGroups_length]; exact hl)) C.lookups[l] := by
  simp only [Template.checkGroups, Bool.and_eq_true, beq_iff_eq] at grouped
  obtain ⟨flat, pairs⟩ := grouped
  refine ⟨flat, fun l hl => ?_⟩
  have pairs := (allPairs_iff _ _ _).mp pairs
  have len := pairs.length_eq
  have step := (List.forall₂_iff_get.mp pairs).2 l (by simp at len ⊢; omega) hl
  simp only [List.get_eq_getElem, List.getElem_zipIdx, Nat.zero_add] at step
  unfold Template.checkGroup at step
  split at step
  · rename_i m single
    exact Or.inl ⟨m, single, checked.message_sound holds step⟩
  · exact Or.inr (checked.chunk_sound holds step)

/-- Every message row of a checked template is laid out as `messageCells`. -/
theorem Template.Checked.rowShaped : ∀ m ∈ T.messages, RowShaped T.width m := by
  intro m hm
  rcases checked.messages with unchunked | grouped
  · obtain ⟨l, _, sound⟩ := forall₂_mem' ((Template.Checked.unchunked T checked unchunked).imp
      fun {_ _} check => checked.message_sound holds check) hm
    obtain ⟨mult, ps, cells, len, _⟩ := sound
    exact ⟨mult, ps, cells, len⟩
  · obtain ⟨flat, sound⟩ := checked.grouped holds grouped
    rw [← flat] at hm
    obtain ⟨g, hg, hm⟩ := List.mem_flatten.mp hm
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
    have hl' : l < C.lookups.length := by rwa [splitGroups_length] at hl
    exact (sound l hl').rowShaped m hm

end Template

end Aiur.Tiling
