import Ix.CompileCert.Canon.Loop
import Ix.Compile.Canon.Nested

/-!
# M7 L1, Lean's nested positions against the canonical auxiliaries (`computePerm`)

`Ix.Compile.Canon.computePerm addr? canon source all o2c` maps each of Lean's source
auxiliaries (`source`, discovery order over the block `all`) to a canonical position of the
component (`canon`, the canonical signatures), with every member of the component renamed to its
representative (`o2c`). `computePerm_spec`, against the code as it is:

* `perm` has one entry per source position;
* a source position mapped to `some i` matches the canonical signature `i` (`matchSig`): an exact
  spelling (constants by name) when there is one, else equality up to compiled addresses; a match
  has the same head and its parameters equal under `auxSpecEq` (`matchSig_spec`), members outside
  the component compared strictly by name;
* a source position mapped to `none` matches no canonical signature, and mentions a block member
  outside the component or has its owner outside the component (otherwise the function fails);
* **every canonical position is the image of some source position** (`perm` is onto the canonical
  auxiliaries).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr)

/-- The component's members (the keys of `o2c`), as `computePerm` collects them. -/
abbrev inCompOf (o2c : Std.HashMap Name Name) : Std.HashSet Name := o2c.fold (fun s k _ => s.insert k) ∅

/-- The block's members outside the component, compared strictly by name. -/
abbrev strictOf (all : Array Name) (o2c : Std.HashMap Name Name) : Std.HashSet Name :=
  all.foldl (fun s n => if (inCompOf o2c).contains n = true then s else s.insert n) ∅

/-- The block's members. -/
abbrev originalsOf (all : Array Name) : Std.HashSet Name := all.foldl (fun x1 x2 => x1.insert x2) ∅

/-- What `computePerm` records for one source signature. -/
def PermEntry (addr? : Name → Option Address) (canon : Array Sig) (all : Array Name)
    (o2c : Std.HashMap Name Name) (s : Sig) (p : Option Nat) : Prop :=
  let specs := s.specs.map (replaceConstNames o2c)
  (∃ i, p = some i ∧
    (matchSig (fun _ => none) (strictOf all o2c) canon s.head s.levels specs = some i ∨
      (matchSig (fun _ => none) (strictOf all o2c) canon s.head s.levels specs = none ∧
        matchSig addr? (strictOf all o2c) canon s.head s.levels specs = some i))) ∨
  (p = none ∧ matchSig (fun _ => none) (strictOf all o2c) canon s.head s.levels specs = none ∧
    matchSig addr? (strictOf all o2c) canon s.head s.levels specs = none ∧
    (s.specs.any (mentionsOutside (originalsOf all) (inCompOf o2c)) ||
      !(inCompOf o2c).contains s.owner) = true)

theorem option_orElse_some {α : Type} (a : α) (b : Option α) : (some a <|> b) = some a := rfl

theorem option_orElse_none {α : Type} (b : Option α) : (none <|> b) = b := rfl

theorem except_throw_bind_ne {α β ε : Type} (e : ε) (k : α → Except ε β) (r : β) :
    (throw e >>= k : Except ε β) ≠ .ok r := by
  intro h; cases h

/-- **`computePerm`, against the code**: one entry per source position, each as `PermEntry` says,
and every canonical position hit. -/
theorem computePerm_spec {addr? : Name → Option Address} {canon source : Array Sig}
    {all : Array Name} {o2c : Std.HashMap Name Name} {perm : Array (Option Nat)}
    (h : computePerm addr? canon source all o2c = .ok perm) :
    Pointwise (fun (sj : Sig × Nat) p => PermEntry addr? canon all o2c sj.1 p)
      source.zipIdx.toList perm.toList ∧
    ∀ i, i < canon.size → some i ∈ perm := by
  unfold computePerm at h
  dsimp only at h
  obtain ⟨perm', h1, h⟩ := except_bind_ok.1 h
  obtain ⟨u, h2, h⟩ := except_bind_ok.1 h
  cases except_pure_ok h
  refine ⟨forIn_push_array source.zipIdx _ _ ?_ h1, ?_⟩
  · intro x r st hs
    obtain ⟨s, j⟩ := x
    dsimp only at hs
    split at hs
    · rename_i i hm
      have hm' : (matchSig (fun _ => none) (strictOf all o2c) canon s.head s.levels
          (s.specs.map (replaceConstNames o2c)) <|> matchSig addr? (strictOf all o2c) canon s.head
            s.levels (s.specs.map (replaceConstNames o2c))) = some i := hm
      cases except_pure_ok hs
      refine ⟨some i, rfl, .inl ⟨i, rfl, ?_⟩⟩
      cases hm1 : matchSig (fun _ => none) (strictOf all o2c) canon s.head s.levels
          (s.specs.map (replaceConstNames o2c)) with
      | some i' =>
        rw [hm1, option_orElse_some] at hm'
        exact .inl hm'
      | none =>
        rw [hm1, option_orElse_none] at hm'
        exact .inr ⟨rfl, hm'⟩
    · rename_i hm
      have hm' : (matchSig (fun _ => none) (strictOf all o2c) canon s.head s.levels
          (s.specs.map (replaceConstNames o2c)) <|> matchSig addr? (strictOf all o2c) canon s.head
            s.levels (s.specs.map (replaceConstNames o2c))) = none := hm
      split at hs
      · rename_i hc
        cases except_pure_ok hs
        cases hm1 : matchSig (fun _ => none) (strictOf all o2c) canon s.head s.levels
            (s.specs.map (replaceConstNames o2c)) with
        | some i' => rw [hm1, option_orElse_some] at hm'; cases hm'
        | none =>
          rw [hm1, option_orElse_none] at hm'
          exact ⟨none, rfl, .inr ⟨rfl, hm1, hm', hc⟩⟩
      · exact absurd hs (except_throw_bind_ne _ _ _)
  · -- the check loop: every canonical position is in `perm'`
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h2
    have := forIn_except_list _ (fun pre (_ : PUnit) => ∀ i ∈ pre, some i ∈ perm)
      (by
        intro pre x r st hp hs
        split at hs
        · exact absurd hs (except_throw_bind_ne _ _ _)
        · rename_i hc
          cases except_pure_ok hs
          refine ⟨PUnit.unit, rfl, fun i hi => ?_⟩
          rcases List.mem_append.1 hi with hi | hi
          · exact hp i hi
          · rw [List.mem_singleton] at hi
            subst hi
            simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hc
            exact Array.contains_iff_mem.1 (by simpa using hc))
      _ [] PUnit.unit u (fun _ h => by cases h) h2
    intro i hi
    apply this i
    rw [List.nil_append, List.mem_range'_1]
    simp only [Std.Legacy.Range.size]
    omega

/-- **A match is a match**: `matchSig` returns a position of `canon` whose signature has the
head asked for and parameters equal one by one under `auxSpecEq`. -/
theorem matchSig_spec {a : Name → Option Address} {strict : Std.HashSet Name} {canon : Array Sig}
    {head : Name} {levels : Array Level} {specs : Array Expr} {i : Nat}
    (h : matchSig a strict canon head levels specs = some i) :
    ∃ c, canon[i]? = some c ∧ (c.head == head) = true ∧ (c.specs.size == specs.size) = true ∧
      (c.specs.zip specs).all (fun p => auxSpecEq a strict p.1 p.2) = true := by
  unfold matchSig at h
  dsimp only at h
  have hc : ∀ q, q ∈ (canon.zipIdx.filter fun x => x.1.head == head).toList →
      canon[q.2]? = some q.1 ∧ (q.1.head == head) = true := by
    intro q hq
    rw [Array.mem_toList_iff, Array.mem_filter] at hq
    exact ⟨Array.mem_zipIdx_iff_getElem?.1 hq.1, hq.2⟩
  split at h
  · rename_i c i' hf
    cases h
    have hm := hc _ (List.mem_of_find?_eq_some hf)
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true] at hp
    exact ⟨c, hm.1, hm.2, hp.2.1, hp.2.2⟩
  · obtain ⟨⟨c, i'⟩, hf, rfl⟩ := Option.map_eq_some_iff.1 h
    have hm := hc _ (List.mem_of_find?_eq_some hf)
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true] at hp
    exact ⟨c, hm.1, hm.2, hp.1, hp.2⟩

/-- **The canonical positions of a component are all used**: every canonical auxiliary is the image
of a source position. -/
theorem computePerm_onto {addr? : Name → Option Address} {canon source : Array Sig}
    {all : Array Name} {o2c : Std.HashMap Name Name} {perm : Array (Option Nat)}
    (h : computePerm addr? canon source all o2c = .ok perm) (i : Nat) (hi : i < canon.size) :
    ∃ j : Nat, perm[j]? = some (some i) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (Array.mem_toList_iff.2 ((computePerm_spec h).2 i hi))
  exact ⟨j, by rw [← Array.getElem?_toList]; exact hj⟩

/-- **Each source position**: mapped to a canonical signature that matches it (same head,
parameters equal under `auxSpecEq` after renaming the component's members to their
representatives), or to `none` when none matches and it mentions a member outside the component
or its owner is outside the component. -/
theorem computePerm_entry {addr? : Name → Option Address} {canon source : Array Sig}
    {all : Array Name} {o2c : Std.HashMap Name Name} {perm : Array (Option Nat)}
    (h : computePerm addr? canon source all o2c = .ok perm) {j : Nat} {s : Sig}
    (hs : source[j]? = some s) :
    ∃ p : Option Nat, perm[j]? = some p ∧ PermEntry addr? canon all o2c s p := by
  have hs' : source.zipIdx.toList[j]? = some (s, j) := by
    rw [Array.toList_zipIdx, List.getElem?_zipIdx, Array.getElem?_toList, hs]; simp
  obtain ⟨p, hp, he⟩ := (computePerm_spec h).1.get' hs'
  exact ⟨p, by rw [← Array.getElem?_toList]; exact hp, he⟩

theorem computePerm_size {addr? : Name → Option Address} {canon source : Array Sig}
    {all : Array Name} {o2c : Std.HashMap Name Name} {perm : Array (Option Nat)}
    (h : computePerm addr? canon source all o2c = .ok perm) : perm.size = source.size := by
  have := (computePerm_spec h).1.length
  rw [Array.toList_zipIdx, List.length_zipIdx] at this
  simpa using this.symm

/-- A position mapped to `some i` has `i` a canonical position whose signature matches. -/
theorem computePerm_some {addr? : Name → Option Address} {canon source : Array Sig}
    {all : Array Name} {o2c : Std.HashMap Name Name} {perm : Array (Option Nat)}
    (h : computePerm addr? canon source all o2c = .ok perm) {j i : Nat} {s : Sig}
    (hs : source[j]? = some s) (hp : perm[j]? = some (some i)) :
    ∃ c, canon[i]? = some c ∧ (c.head == s.head) = true ∧
      ((c.specs.zip (s.specs.map (replaceConstNames o2c))).all
          (fun p => auxSpecEq (fun _ => none) (strictOf all o2c) p.1 p.2) = true ∨
        (c.specs.zip (s.specs.map (replaceConstNames o2c))).all
          (fun p => auxSpecEq addr? (strictOf all o2c) p.1 p.2) = true) := by
  obtain ⟨p, hp', he⟩ := computePerm_entry h hs
  rw [hp] at hp'; cases hp'
  rcases he with ⟨i', hi', hm | ⟨-, hm⟩⟩ | ⟨hn, -⟩
  · cases hi'
    obtain ⟨c, hc, hh, -, ha⟩ := matchSig_spec hm
    exact ⟨c, hc, hh, .inl ha⟩
  · cases hi'
    obtain ⟨c, hc, hh, -, ha⟩ := matchSig_spec hm
    exact ⟨c, hc, hh, .inr ha⟩
  · cases hn

end Ix.CompileCert.Canon
