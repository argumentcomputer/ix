import IxSharingVerify.TieredTier
import IxSharingVerify.SharingExactCanon
import IxC.Kernel.Audit.Axioms

/-!
# The Kahn priority order is a dependency order

The slot allocation orders the terms outside the first tier by `kahnOrder`:
it repeatedly places a ready term (every dependency among the terms already
placed), the largest weight first, and appends whatever it did not place.
When each term's dependencies among the terms are smaller term IDs, nothing
is left over: the result is a permutation of its input that places every
dependency before its user (`kahnOrder_spec`).
-/

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact

/-! ## Positions in a duplicate-free array -/

theorem foldl_insert_get_notin :
    ∀ (l : List (Nat × Nat)) (mp : Std.HashMap Nat Nat) (k : Nat), k ∉ l.map Prod.fst →
      (l.foldl (fun r x => r.insert x.fst x.snd) mp).get? k = mp.get? k
  | [], _, _, _ => rfl
  | x :: l, mp, k, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, foldl_insert_get_notin l _ k h.2, Std.HashMap.get?_insert]
    have ne : (x.fst == k) = false := beq_eq_false_iff_ne.mpr (fun e => h.1 e.symm)
    simp only [ne, Bool.false_eq_true, ↓reduceIte]

theorem foldl_insert_get_mem :
    ∀ (l : List (Nat × Nat)) (mp : Std.HashMap Nat Nat), (l.map Prod.fst).Nodup →
      ∀ k v, (k, v) ∈ l → (l.foldl (fun r x => r.insert x.fst x.snd) mp).get? k = some v
  | [], _, _, _, _, h => by simp at h
  | x :: l, mp, nd, k, v, h => by
    rw [List.foldl_cons]
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp h with e | h
    · subst e
      rw [foldl_insert_get_notin l _ k (by simpa using nd.1), Std.HashMap.get?_insert]
      simp
    · exact foldl_insert_get_mem l _ nd.2 k v h

/-- The rank map of a duplicate-free array: each entry's position. -/
theorem rank_spec (sorted : Array Nat) (nodup : sorted.toList.Nodup) :
    (∀ x i, (Array.foldl (fun r x => r.insert x.fst x.snd) (∅ : Std.HashMap Nat Nat)
        sorted.zipIdx).get? x = some i → i < sorted.size ∧ sorted[i]! = x) ∧
    (∀ i, i < sorted.size → (Array.foldl (fun r x => r.insert x.fst x.snd)
        (∅ : Std.HashMap Nat Nat) sorted.zipIdx).get? sorted[i]! = some i) := by
  rw [← Array.foldl_toList, Array.toList_zipIdx]
  constructor
  · intro x i h
    have := posMap_spec sorted _ ∅ (fun d j h => by simp at h)
      (fun y hy => by
        have := Array.mem_zipIdx_iff_getElem?.mp (by rw [← Array.mem_toList_iff, Array.toList_zipIdx]; exact hy)
        exact this) x i h
    obtain ⟨lt, eq⟩ := Array.getElem?_eq_some_iff.mp this
    exact ⟨lt, by rw [getElem!_pos sorted i lt]; exact eq⟩
  · intro i hi
    apply foldl_insert_get_mem _ ∅ (by rw [List.zipIdx_map_fst]; exact nodup)
    rw [getElem!_pos sorted i hi]
    have : (sorted[i], i) ∈ sorted.zipIdx := Array.mem_zipIdx_iff_getElem?.mpr (by simp [hi])
    rw [← Array.mem_toList_iff, Array.toList_zipIdx] at this
    exact this

theorem nodup_eraseDups : ∀ (l : List Nat), l.eraseDups.Nodup := by
  intro l
  induction h : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [List.mem_eraseDups]
        simp
      · apply ih _ _ _ rfl
        have := List.length_filter_le (fun b => !b == a) as
        simp at h
        omega

/-! ## The setup loop -/

/-- The dependency ranks of the `i`-th sorted term, without repeats. -/
abbrev kahnDs (rank : Std.HashMap Nat Nat) (deps : Nat → List Nat) (sorted : Array Nat)
    (i : Nat) : List Nat :=
  (List.filterMap rank.get? (deps sorted[i]!)).eraseDups

theorem pushAll_spec (k : Nat) :
    ∀ (L : List Nat) (users : Array (Array Nat)), L.Nodup →
      (L.foldl (fun b a => b.modify a fun x => x.push k) users).size = users.size ∧
      ∀ r, (L.foldl (fun b a => b.modify a fun x => x.push k) users)[r]! =
        if r ∈ L ∧ r < users.size then users[r]!.push k else users[r]!
  | [], users, _ => ⟨rfl, fun r => by simp⟩
  | a :: L, users, nd => by
    rw [List.nodup_cons] at nd
    obtain ⟨size, get⟩ := pushAll_spec k L (users.modify a fun x => x.push k) nd.2
    simp only [Array.size_modify] at size
    refine ⟨by simpa using size, fun r => ?_⟩
    rw [List.foldl_cons, get r]
    by_cases hr : r = a
    · subst hr
      by_cases lt : r < users.size
      · have lt' : r < (users.modify r fun x => x.push k).size := by simpa using lt
        simp only [List.mem_cons, true_or, true_and, nd.1, false_and, ↓reduceIte, lt, lt']
        rw [getElem!_pos _ r lt', getElem!_pos _ r lt]
        simp [Array.getElem_modify]
      · have lt' : ¬ r < (users.modify r fun x => x.push k).size := by simpa using lt
        simp only [List.mem_cons, true_or, true_and, nd.1, false_and, ↓reduceIte, lt, lt']
        rw [getElem!_neg _ r lt', getElem!_neg _ r lt]
    · simp only [Array.size_modify, List.mem_cons, hr, false_or]
      have : (users.modify a fun x => x.push k)[r]! = users[r]! := by
        by_cases lt : r < users.size
        · rw [getElem!_pos _ r (by simpa using lt), getElem!_pos _ r lt, Array.getElem_modify]
          simp [Ne.symm hr]
        · rw [getElem!_neg _ r (by simpa using lt), getElem!_neg _ r lt]
      split <;> rw [this]

theorem kahnSetup_spec (sorted : Array Nat) (rank : Std.HashMap Nat Nat) (deps : Nat → List Nat) :
    ∀ n, n ≤ sorted.size →
      (List.foldl (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
        (b.fst.set! i (kahnDs rank deps sorted i).length,
          List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
        (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range n)).fst.size =
          sorted.size ∧
      (∀ i, i < n → (List.foldl (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
        (b.fst.set! i (kahnDs rank deps sorted i).length,
          List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
        (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range n)).fst[i]! =
          (kahnDs rank deps sorted i).length) ∧
      (List.foldl (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
        (b.fst.set! i (kahnDs rank deps sorted i).length,
          List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
        (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range n)).snd.size =
          sorted.size ∧
      (∀ r, r < sorted.size → ∀ u, u ∈ (List.foldl
        (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
          (b.fst.set! i (kahnDs rank deps sorted i).length,
            List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
          (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range n)).snd[r]!.toList ↔
        u < n ∧ r ∈ kahnDs rank deps sorted u) ∧
      (∀ r, r < sorted.size → (List.foldl
        (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
          (b.fst.set! i (kahnDs rank deps sorted i).length,
            List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
          (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range n)).snd[r]!.toList.Nodup) ∧
      (∀ r, r < sorted.size → ∀ u ∈ (List.foldl
        (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
          (b.fst.set! i (kahnDs rank deps sorted i).length,
            List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
          (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range n)).snd[r]!.toList,
        u < n) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨by simp, fun i h => absurd h (Nat.not_lt_zero _), by simp, fun r hr u => ?_, fun r hr => ?_,
      fun r hr u hu => ?_⟩
    · rw [getElem!_pos _ r (by simpa using hr)]; simp
    · rw [getElem!_pos _ r (by simpa using hr)]; simp
    · rw [getElem!_pos _ r (by simpa using hr)] at hu; simp at hu
  | succ n ih =>
    intro le
    obtain ⟨s1, g1, s2, mem, nd, lt⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize List.foldl (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
        (b.fst.set! i (kahnDs rank deps sorted i).length,
          List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
        (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range n) = old
      at s1 g1 s2 mem nd lt ⊢
    obtain ⟨push1, push2⟩ := pushAll_spec n (kahnDs rank deps sorted n) old.snd (nodup_eraseDups _)
    dsimp only
    refine ⟨by simp [s1], fun i hi => ?_, by rw [push1, s2], fun r hr u => ?_, fun r hr => ?_,
      fun r hr u hu => ?_⟩
    · rw [Ix.Sharing.Verify.SharingExact.setBang_getElem!]
      by_cases hin : i = n
      · subst hin; simp [s1]; omega
      · rw [ite_eq_right (fun h => hin h.1.symm)]; exact g1 i (by omega)
    · rw [push2 r]
      by_cases hd : r ∈ kahnDs rank deps sorted n ∧ r < old.snd.size
      · rw [ite_eq_left hd, Array.toList_push, List.mem_append, List.mem_singleton, mem r hr]
        constructor
        · rintro (⟨h1, h2⟩ | rfl)
          · exact ⟨by omega, h2⟩
          · exact ⟨by omega, hd.1⟩
        · rintro ⟨h1, h2⟩
          by_cases hu : u = n
          · exact Or.inr hu
          · exact Or.inl ⟨by omega, h2⟩
      · rw [ite_eq_right hd, mem r hr]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          by_cases hu : u = n
          · subst hu; exact absurd ⟨h2, by rw [s2]; exact hr⟩ hd
          · exact ⟨by omega, h2⟩
    · rw [push2 r]
      split
      · rw [Array.toList_push, List.nodup_append]
        refine ⟨nd r hr, (by simp), fun a ha b hb => ?_⟩
        simp only [List.mem_singleton] at hb
        have := lt r hr a ha
        omega
      · exact nd r hr
    · rw [push2 r] at hu
      split at hu
      · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | hu
        · have := lt r hr u hu; omega
        · omega
      · have := lt r hr u hu; omega

/-- Releasing the users of a placed term: each loses one pending
dependency, and those left with none become ready. -/
theorem release_spec (U : List Nat) (nodup : U.Nodup) :
    ∀ (pend : Array Nat) (ready : Std.TreeSet Nat compare), (∀ u ∈ U, u < pend.size) →
      (U.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
          (b.fst.modify a fun x => x - 1, b.snd.insert a)
        else (b.fst.modify a fun x => x - 1, b.snd)) (pend, ready)).fst.size = pend.size ∧
      (∀ u, (U.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
          (b.fst.modify a fun x => x - 1, b.snd.insert a)
        else (b.fst.modify a fun x => x - 1, b.snd)) (pend, ready)).fst[u]! =
          if u ∈ U then pend[u]! - 1 else pend[u]!) ∧
      (∀ u, u ∈ (U.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
          (b.fst.modify a fun x => x - 1, b.snd.insert a)
        else (b.fst.modify a fun x => x - 1, b.snd)) (pend, ready)).snd ↔
          u ∈ ready ∨ (u ∈ U ∧ pend[u]! - 1 = 0)) := by
  induction U with
  | nil => intro pend ready _; simp
  | cons a U ih =>
    intro pend ready bound
    rw [List.nodup_cons] at nodup
    have aLt := bound a List.mem_cons_self
    have modGet : ∀ u, (pend.modify a fun x => x - 1)[u]! = if u = a then pend[u]! - 1 else pend[u]! := by
      intro u
      by_cases lt : u < pend.size
      · rw [getElem!_pos _ u (by simpa using lt), getElem!_pos _ u lt, Array.getElem_modify]
        by_cases h : u = a
        · subst h; simp
        · simp [h, Ne.symm h]
      · have ne : u ≠ a := fun h => lt (h ▸ aLt)
        rw [getElem!_neg _ u (by simpa using lt), getElem!_neg _ u lt]
        simp [ne]
    rw [List.foldl_cons]
    have step : (if ((pend.modify a fun x => x - 1)[a]! == 0) = true then
        ((pend.modify a fun x => x - 1), ready.insert a) else ((pend.modify a fun x => x - 1), ready)) =
        ((pend.modify a fun x => x - 1), if pend[a]! - 1 = 0 then ready.insert a else ready) := by
      rw [modGet a]
      simp only [↓reduceIte, beq_iff_eq]
      split <;> rfl
    rw [step]
    obtain ⟨size, get, mem⟩ := ih nodup.2 (pend.modify a fun x => x - 1)
      (if pend[a]! - 1 = 0 then ready.insert a else ready)
      (fun u hu => by simpa using bound u (List.mem_cons_of_mem _ hu))
    refine ⟨by rw [size]; simp, fun u => ?_, fun u => ?_⟩
    · rw [get u, modGet u]
      by_cases hu : u = a
      · subst hu; simp [nodup.1]
      · simp [hu]
    · rw [mem u]
      by_cases hu : u = a
      · subst hu
        simp only [nodup.1, false_and, or_false, List.mem_cons, true_and]
        split
        · rename_i zero
          simp [Std.TreeSet.mem_insert, zero]
        · rename_i nonzero
          simp [nonzero]
      · rw [modGet u]
        simp only [hu, ↓reduceIte, List.mem_cons, false_or]
        split
        · simp [Std.TreeSet.mem_insert, Ne.symm hu]
        · rfl

/-- A loop in `Id` with an invariant on the steps taken; it may stop early
in a final state. -/
theorem forIn_id_inv {α β : Type} (f : α → β → Id (ForInStep β)) (I : Nat → β → Prop)
    (D : β → Prop)
    (step : ∀ k a b, I k b → (∃ b', f a b = pure (.done b') ∧ D b') ∨
      (∃ b', f a b = pure (.yield b') ∧ I (k + 1) b')) :
    ∀ (l : List α) (k : Nat) (b : β), I k b → D (forIn l b f) ∨ I (k + l.length) (forIn l b f)
  | [], _, _, h => Or.inr h
  | a :: l, k, b, h => by
    rw [List.forIn_cons]
    rcases step k a b h with ⟨b', hf, hd⟩ | ⟨b', hf, hi⟩
    · rw [hf]
      exact Or.inl hd
    · rw [hf]
      have := forIn_id_inv f I D step l (k + 1) b' hi
      simp only [List.length_cons]
      rw [show k + (l.length + 1) = k + 1 + l.length by omega]
      exact this

theorem release_spec_array (users : Array Nat) (nodup : users.toList.Nodup) (pend : Array Nat)
    (ready : Std.TreeSet Nat compare) (bound : ∀ u ∈ users.toList, u < pend.size) :
    (Array.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
          (b.fst.modify a fun x => x - 1, b.snd.insert a)
        else (b.fst.modify a fun x => x - 1, b.snd)) (pend, ready) users).fst.size = pend.size ∧
      (∀ u, (Array.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
          (b.fst.modify a fun x => x - 1, b.snd.insert a)
        else (b.fst.modify a fun x => x - 1, b.snd)) (pend, ready) users).fst[u]! =
          if u ∈ users.toList then pend[u]! - 1 else pend[u]!) ∧
      (∀ u, u ∈ (Array.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
          (b.fst.modify a fun x => x - 1, b.snd.insert a)
        else (b.fst.modify a fun x => x - 1, b.snd)) (pend, ready) users).snd ↔
          u ∈ ready ∨ (u ∈ users.toList ∧ pend[u]! - 1 = 0)) := by
  rw [← Array.foldl_toList]
  exact release_spec users.toList nodup pend ready bound

/-- Marking one term placed removes exactly it from the unplaced
dependencies of a list without repeats. -/
theorem filter_length_place (p q : Nat → Bool) (r : Nat) (agree : ∀ d, d ≠ r → q d = p d)
    (qr : q r = false) :
    ∀ (L : List Nat), L.Nodup →
      (L.filter q).length + (if r ∈ L ∧ p r = true then 1 else 0) = (L.filter p).length
  | [], _ => by simp
  | x :: L, nd => by
    rw [List.nodup_cons] at nd
    by_cases hx : x = r
    · subst hx
      have same : L.filter q = L.filter p := by
        apply List.filter_congr
        intro d hd
        exact agree d (fun e => nd.1 (e ▸ hd))
      rw [List.filter_cons, List.filter_cons, qr, same]
      cases p x <;> simp
    · have inner := filter_length_place p q r agree qr L nd.2
      rw [List.filter_cons, List.filter_cons, agree x hx]
      simp only [List.mem_cons, Ne.symm hx, false_or]
      cases p x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

/-- The state of the placement loop after `k` placements. -/
structure KahnInv (m : Nat) (ds : Nat → List Nat) (sorted : Array Nat) (k : Nat)
    (b : Array Nat × Std.TreeSet Nat compare × Array Bool × Array Nat) : Prop where
  pendSize : b.1.size = m
  pend : ∀ u, u < m → b.1[u]! = ((ds u).filter (fun d => !b.2.2.1[d]!)).length
  placedSize : b.2.2.1.size = m
  ready : ∀ u, u ∈ b.2.1 ↔ u < m ∧ b.2.2.1[u]! = false ∧ b.1[u]! = 0
  seq : ∃ s : List Nat, s.length = k ∧ s.Nodup ∧ (∀ r, r ∈ s ↔ r < m ∧ b.2.2.1[r]! = true) ∧
    b.2.2.2.toList = s.map (sorted[·]!) ∧
    ∀ j (hj : j < s.length), ∀ d ∈ ds s[j], d ∈ s.take j

theorem foldl_all_placed {L : List Nat} (sorted : Array Nat) (placed : Array Bool) :
    ∀ (l : List {x // x ∈ L}) (out : Array Nat), (∀ x ∈ l, placed[x.val]! = true) →
      l.foldl (fun b x => if (!placed[x.val]!) = true then b.push sorted[x.val]! else b) out = out
  | [], _, _ => rfl
  | x :: l, out, h => by
    rw [List.foldl_cons, h x List.mem_cons_self]
    exact foldl_all_placed sorted placed l out (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **The placement loop places every term**, each after its dependencies. -/
theorem kahn_core (deps : Nat → List Nat) (rest sorted : Array Nat) (rank : Std.HashMap Nat Nat)
    (setup : Array Nat × Array (Array Nat))
    (f : Nat → Array Nat × Std.TreeSet Nat compare × Array Bool × Array Nat →
      Id (ForInStep (Array Nat × Std.TreeSet Nat compare × Array Bool × Array Nat)))
    (hf : ∀ x b, f x b = match b.snd.fst.min? with
      | none => pure (ForInStep.done (b.fst, b.snd.fst, b.snd.snd.fst, b.snd.snd.snd))
      | some r => pure (ForInStep.yield
          ((Array.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
                (b.fst.modify a fun x => x - 1, b.snd.insert a)
              else (b.fst.modify a fun x => x - 1, b.snd)) (b.fst, b.snd.fst.erase r) setup.snd[r]!).fst,
            (Array.foldl (fun b a => if ((b.fst.modify a fun x => x - 1)[a]! == 0) = true then
                (b.fst.modify a fun x => x - 1, b.snd.insert a)
              else (b.fst.modify a fun x => x - 1, b.snd)) (b.fst, b.snd.fst.erase r) setup.snd[r]!).snd,
            b.snd.snd.fst.set! r true, b.snd.snd.snd.push sorted[r]!)))
    (perm : sorted.toList.Perm rest.toList)
    (rank1 : ∀ x i, rank.get? x = some i → i < sorted.size ∧ sorted[i]! = x)
    (pendSize : setup.fst.size = sorted.size)
    (pendInit : ∀ i, i < sorted.size → setup.fst[i]! = (kahnDs rank deps sorted i).length)
    (usersMem : ∀ r, r < sorted.size → ∀ u,
      u ∈ setup.snd[r]!.toList ↔ u < sorted.size ∧ r ∈ kahnDs rank deps sorted u)
    (usersNodup : ∀ r, r < sorted.size → setup.snd[r]!.toList.Nodup)
    (acyclic : ∀ t ∈ rest.toList, ∀ d ∈ deps t, d ∈ rest.toList → d < t) :
    ∃ s : List Nat, (Id.run (do
      let st ← forIn (List.range' 0 sorted.size)
        (setup.fst, Std.TreeSet.ofList (List.filter (fun x => setup.fst[x]! == 0)
          (List.range sorted.size)) compare, Array.replicate sorted.size false, #[]) f
      pure (List.foldl (fun b x => if (!st.snd.snd.fst[x.val]!) = true then b.push sorted[x.val]! else b)
        st.snd.snd.snd (List.range' 0 sorted.size).attach)) : Array Nat).toList =
        s.map (sorted[·]!) ∧ s.Perm (List.range sorted.size) ∧
      ∀ j (hj : j < s.length), ∀ d ∈ kahnDs rank deps sorted s[j], d ∈ s.take j := by
  let m := sorted.size
  let ds := kahnDs rank deps sorted
  have dsBound : ∀ u, ∀ d ∈ ds u, d < m := by
    intro u d hd
    simp only [ds, kahnDs, List.mem_eraseDups, List.mem_filterMap] at hd
    obtain ⟨x, _, hx⟩ := hd
    exact (rank1 x d hx).1
  have dsLt : ∀ u, u < m → ∀ d ∈ ds u, sorted[d]! < sorted[u]! := by
    intro u hu d hd
    simp only [ds, kahnDs, List.mem_eraseDups, List.mem_filterMap] at hd
    obtain ⟨x, hx, hrank⟩ := hd
    obtain ⟨dlt, deq⟩ := rank1 x d hrank
    rw [deq]
    have uIn : sorted[u]! ∈ rest.toList :=
      perm.subset (by rw [getElem!_pos sorted u hu]; exact Array.getElem_mem_toList hu)
    have xIn : x ∈ rest.toList :=
      perm.subset (by rw [← deq, getElem!_pos sorted d dlt]; exact Array.getElem_mem_toList dlt)
    exact acyclic _ uIn x hx xIn
  have dsNodup : ∀ u, (ds u).Nodup := fun u => nodup_eraseDups _
  -- one step of the loop
  have step : ∀ k (a : Nat) b, KahnInv m ds sorted k b →
      (∃ b', f a b = pure (.done b') ∧
        ((∃ k, KahnInv m ds sorted k b') ∧ ∀ r, r < m → b'.2.2.1[r]! = true)) ∨
      (∃ b', f a b = pure (.yield b') ∧ KahnInv m ds sorted (k + 1) b') := by
    intro k a b inv
    rw [hf]
    cases hmin : b.snd.fst.min? with
    | none =>
      left
      refine ⟨b, rfl, ⟨k, inv⟩, ?_⟩
      have empty : ∀ u, u ∉ b.snd.fst :=
        Std.TreeSet.isEmpty_iff_forall_not_mem.mp (Std.TreeSet.min?_eq_none_iff.mp hmin)
      have claim : ∀ v r, r < m → sorted[r]! = v → b.2.2.1[r]! = false → False := by
        intro v
        induction v using Nat.strongRecOn with
        | _ v ih =>
          intro r hr hv hun
          by_cases hp : b.1[r]! = 0
          · exact empty r ((inv.ready r).mpr ⟨hr, hun, hp⟩)
          · rw [inv.pend r hr] at hp
            have ne : (ds r).filter (fun d => !b.2.2.1[d]!) ≠ [] := fun h => hp (by rw [h]; rfl)
            obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ ne
            obtain ⟨hd, hdun⟩ := List.mem_filter.mp hd
            exact ih _ (hv ▸ dsLt r hr d hd) d (dsBound r d hd) rfl (by simpa using hdun)
      intro r hr
      cases h : b.2.2.1[r]! with
      | true => rfl
      | false => exact (claim _ r hr rfl h).elim
    | some r =>
      right
      refine ⟨_, rfl, ?_⟩
      have rIn : r ∈ b.snd.fst := Std.TreeSet.contains_iff_mem.mp (Std.TreeSet.contains_min? hmin)
      obtain ⟨rLt, rUn, rPend⟩ := (inv.ready r).mp rIn
      have depsPlaced : ∀ d ∈ ds r, b.2.2.1[d]! = true := by
        rw [inv.pend r rLt, List.length_eq_zero_iff] at rPend
        intro d hd
        cases hpd : b.2.2.1[d]! with
        | true => rfl
        | false =>
          have : d ∈ (ds r).filter (fun d => !b.2.2.1[d]!) := List.mem_filter.mpr ⟨hd, by simp [hpd]⟩
          rw [rPend] at this
          cases this
      obtain ⟨s, slen, snd, smem, sout, sresp⟩ := inv.seq
      have placedOf : ∀ u, b.2.2.1[u]! = true → u < m → ∀ d ∈ ds u, b.2.2.1[d]! = true := by
        intro u hu um d hd
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((smem u).mpr ⟨um, hu⟩)
        have := sresp j hj d hd
        exact ((smem d).mp (List.mem_of_mem_take this)).2
      have bound : ∀ u ∈ (setup.snd[r]!).toList, u < b.1.size := by
        intro u hu
        rw [inv.pendSize]
        exact ((usersMem r rLt u).mp hu).1
      obtain ⟨rsize, rget, rmem⟩ :=
        release_spec_array setup.snd[r]! (usersNodup r rLt) b.1 (b.2.1.erase r) bound
      have placedSet : ∀ d, (b.2.2.1.set! r true)[d]! = if d = r then true else b.2.2.1[d]! := by
        intro d
        rw [Ix.Sharing.Verify.SharingExact.setBang_getElem!]
        by_cases hd : d = r
        · subst hd; simp [inv.placedSize, rLt]
        · simp [Ne.symm hd, hd]
      have count : ∀ u, ((ds u).filter (fun d => !(b.2.2.1.set! r true)[d]!)).length +
          (if r ∈ ds u then 1 else 0) = ((ds u).filter (fun d => !b.2.2.1[d]!)).length := by
        intro u
        have := filter_length_place (fun d => !b.2.2.1[d]!) (fun d => !(b.2.2.1.set! r true)[d]!) r
          (fun d hd => by
            show (!(b.2.2.1.set! r true)[d]!) = (!b.2.2.1[d]!)
            rw [placedSet d, ite_eq_right hd])
          (by show (!(b.2.2.1.set! r true)[r]!) = false; rw [placedSet r]; simp) (ds u)
          (dsNodup u)
        simp only [rUn, Bool.not_false, and_true] at this
        exact this
      have usersIff : ∀ u, u ∈ (setup.snd[r]!).toList ↔ u < m ∧ r ∈ ds u := usersMem r rLt
      have rNotUser : r ∉ (setup.snd[r]!).toList := by
        intro h
        have := dsLt r rLt r ((usersIff r).mp h).2
        omega
      refine ⟨by rw [rsize, inv.pendSize], fun u hu => ?_, by simp [inv.placedSize], fun u => ?_, ?_⟩
      · -- pending counts
        dsimp only
        rw [rget u, inv.pend u hu, ← count u]
        by_cases hU : u ∈ (setup.snd[r]!).toList
        · have rd := ((usersIff u).mp hU).2
          rw [ite_eq_left hU, ite_eq_left rd]
          omega
        · have rd : r ∉ ds u := fun h => hU ((usersIff u).mpr ⟨hu, h⟩)
          rw [ite_eq_right hU, ite_eq_right rd]
          omega
      · -- the ready set
        dsimp only
        rw [rmem u, Std.TreeSet.mem_erase, placedSet u, rget u]
        by_cases hur : u = r
        · subst hur
          simp only [↓reduceIte, Bool.true_eq_false, false_and, and_false, iff_false, not_or]
          exact ⟨fun ⟨ne, _⟩ => ne (by simp), fun ⟨h, _⟩ => rNotUser h⟩
        · have cmp : compare r u ≠ .eq := fun h => hur (Nat.compare_eq_eq.mp h).symm
          simp only [hur, ↓reduceIte, ne_eq, cmp, not_false_eq_true, true_and]
          by_cases hU : u ∈ (setup.snd[r]!).toList
          · obtain ⟨um, rd⟩ := (usersIff u).mp hU
            have uUn : b.2.2.1[u]! = false := by
              cases h : b.2.2.1[u]! with
              | false => rfl
              | true => exact absurd (placedOf u h um r rd) (by simp [rUn])
            have pos : b.1[u]! ≠ 0 := by
              rw [inv.pend u um, ← count u, ite_eq_left rd]
              omega
            have notReady : u ∉ b.2.1 := fun h => pos ((inv.ready u).mp h).2.2
            simp only [hU, ↓reduceIte, notReady, false_or, true_and, um, uUn]
          · simp only [hU, ↓reduceIte, false_and, or_false]
            exact inv.ready u
      · -- the placement sequence
        dsimp only
        refine ⟨s ++ [r], by simp [slen], ?_, fun r' => ?_, ?_, fun j hj d hd => ?_⟩
        · rw [List.nodup_append]
          refine ⟨snd, by simp, fun x hx y hy => ?_⟩
          simp only [List.mem_singleton] at hy
          subst hy
          intro same
          subst same
          rw [((smem x).mp hx).2] at rUn
          cases rUn
        · rw [List.mem_append, List.mem_singleton, smem r', placedSet r']
          by_cases hr' : r' = r
          · subst hr'; simp [rLt]
          · simp [hr']
        · simp [sout]
        · by_cases old : j < s.length
          · rw [List.getElem_append_left old] at hd
            rw [List.take_append_of_le_length (by omega)]
            exact sresp j old d hd
          · have last : j = s.length := by simp at hj; omega
            subst last
            simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
              List.getElem_cons_zero] at hd
            rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
            exact (smem d).mpr ⟨dsBound r d hd, depsPlaced d hd⟩
  -- the initial state
  have init : KahnInv m ds sorted 0
      (setup.fst, Std.TreeSet.ofList (List.filter (fun x => setup.fst[x]! == 0)
        (List.range sorted.size)) compare, Array.replicate sorted.size false, #[]) := by
    have noneSet : ∀ d : Nat, (Array.replicate sorted.size false)[d]! = false := by
      intro d
      by_cases hd : d < sorted.size
      · rw [getElem!_pos _ d (by simpa using hd)]; simp
      · rw [getElem!_neg _ d (by simpa using hd)]; rfl
    refine ⟨pendSize, fun u hu => ?_, by simp [m], fun u => ?_, ⟨[], rfl, List.nodup_nil, ?_, rfl, ?_⟩⟩
    · simp only [noneSet, Bool.not_false]
      rw [List.filter_eq_self.mpr (fun _ _ => rfl), pendInit u hu]
    · rw [Std.TreeSet.mem_ofList, List.contains_iff_mem, List.mem_filter, List.mem_range, noneSet]
      simp [m]
    · intro r; simp [noneSet]
    · intro j hj; simp at hj
  have loop := forIn_id_inv f (KahnInv m ds sorted)
    (fun b => (∃ k, KahnInv m ds sorted k b) ∧ ∀ r, r < m → b.2.2.1[r]! = true) step
    (List.range' 0 sorted.size) 0 _ init
  generalize forIn (List.range' 0 sorted.size)
    (setup.fst, Std.TreeSet.ofList (List.filter (fun x => setup.fst[x]! == 0)
      (List.range sorted.size)) compare, Array.replicate sorted.size false, #[]) f = fin at loop
  have done : (∃ k, KahnInv m ds sorted k fin) ∧ ∀ r, r < m → fin.2.2.1[r]! = true := by
    rcases loop with d | inv
    · exact d
    · refine ⟨⟨_, inv⟩, fun r hr => ?_⟩
      obtain ⟨s, slen, snd, smem, -, -⟩ := inv.seq
      simp only [List.length_range', Nat.zero_add] at slen
      cases h : fin.2.2.1[r]! with
      | true => rfl
      | false =>
        exfalso
        have sub : s ⊆ (List.range m).erase r := by
          intro x hx
          obtain ⟨xlt, xp⟩ := (smem x).mp hx
          rw [List.mem_erase_of_ne (fun e => by subst e; rw [h] at xp; cases xp)]
          exact List.mem_range.mpr xlt
        have := List.Nodup.length_le_of_subset snd sub
        rw [List.length_erase_of_mem (List.mem_range.mpr hr), List.length_range] at this
        omega
  obtain ⟨⟨k, inv⟩, allPlaced⟩ := done
  obtain ⟨s, slen, snd, smem, sout, sresp⟩ := inv.seq
  refine ⟨s, ?_, ?_, sresp⟩
  · show (List.foldl _ fin.snd.snd.snd (List.range' 0 sorted.size).attach).toList = _
    rw [foldl_all_placed sorted fin.2.2.1 _ _ (fun x _ => allPlaced x.val
      (by have := x.property; simp only [List.mem_range'] at this; omega)), sout]
  · rw [List.perm_ext_iff_of_nodup snd List.nodup_range]
    intro r
    rw [smem r, List.mem_range]
    exact ⟨fun h => h.1, fun h => ⟨h, allPlaced r h⟩⟩


theorem kahn_final (deps : Nat → List Nat) (rest sorted : Array Nat) (rank : Std.HashMap Nat Nat)
    (perm : sorted.toList.Perm rest.toList)
    (rank2 : ∀ i, i < sorted.size → rank.get? sorted[i]! = some i) (out : Array Nat)
    (h : ∃ s : List Nat, out.toList = s.map (sorted[·]!) ∧ s.Perm (List.range sorted.size) ∧
      ∀ j (hj : j < s.length), ∀ d ∈ kahnDs rank deps sorted s[j], d ∈ s.take j) :
    out.toList.Perm rest.toList ∧
      ∀ k (hk : k < out.size), ∀ d ∈ deps out[k], d ∈ rest.toList →
        ∃ j, j < k ∧ out[j]? = some d := by
  obtain ⟨s, hout, hperm, hresp⟩ := h
  have rangeMap : (List.range sorted.size).map (sorted[·]!) = sorted.toList := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    exact getElem!_pos sorted i (by simpa using h1)
  have sizeEq : out.size = s.length := by
    rw [← Array.length_toList, hout, List.length_map]
  refine ⟨?_, fun k hk d hd dIn => ?_⟩
  · rw [hout]
    exact ((hperm.map _).trans (by rw [rangeMap])).trans perm
  · have hk' : k < s.length := by omega
    have outAt : ∀ j (hj : j < out.size), out[j] = sorted[s[j]'(by omega)]! := by
      intro j hj
      rw [← Array.getElem_toList, List.getElem_of_eq hout, List.getElem_map]
    rw [outAt k hk] at hd
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp (perm.symm.subset dIn))
    have rankI := rank2 i hi
    rw [getElem!_pos sorted i hi] at rankI
    have mem : i ∈ kahnDs rank deps sorted s[k] := by
      simp only [kahnDs, List.mem_eraseDups, List.mem_filterMap]
      exact ⟨_, hd, rankI⟩
    obtain ⟨j, hj, atJ⟩ := List.getElem_of_mem (hresp k hk' i mem)
    have hjk : j < k := by simp at hj; omega
    refine ⟨j, hjk, ?_⟩
    rw [Array.getElem?_eq_getElem (by omega), outAt j (by omega)]
    simp only [List.getElem_take] at atJ
    rw [atJ, getElem!_pos sorted i hi]

theorem ite_yield {β : Type} (c : Prop) [Decidable c] (x y : β) :
    (if c then (pure (ForInStep.yield x) : Id (ForInStep β)) else pure (ForInStep.yield y)) =
      pure (ForInStep.yield (if c then x else y)) := by
  split <;> rfl

theorem arrayNat_getElem_eq (a : Array Nat) (i : Nat) (h : i < a.size) : a[i] = a[i]! :=
  (getElem!_pos a i h).symm

/-- **The Kahn priority order** of duplicate-free terms whose dependencies
among them are smaller terms is a permutation of them that places every
dependency before its user. -/
theorem kahnOrder_spec (weight : Nat → Nat) (deps : Nat → List Nat) (rest : Array Nat)
    (nodup : rest.toList.Nodup)
    (acyclic : ∀ t ∈ rest.toList, ∀ d ∈ deps t, d ∈ rest.toList → d < t) :
    (kahnOrder weight deps rest).toList.Perm rest.toList ∧
      ∀ k (hk : k < (kahnOrder weight deps rest).size), ∀ d ∈ deps (kahnOrder weight deps rest)[k],
        d ∈ rest.toList → ∃ j, j < k ∧ (kahnOrder weight deps rest)[j]? = some d := by
  have permS : (rest.toList.mergeSort (tierOrder weight)).toArray.toList.Perm rest.toList := by
    simpa using List.mergeSort_perm rest.toList (tierOrder weight)
  have sortedNodup := permS.nodup_iff.mpr nodup
  obtain ⟨rank1, rank2⟩ := rank_spec _ sortedNodup
  apply kahn_final deps rest _ _ permS rank2
  unfold kahnOrder
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, List.forIn'_pure_yield_eq_foldl, pure_bind, ite_yield,
    Array.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, arrayNat_getElem_eq]
  generalize (rest.toList.mergeSort (tierOrder weight)).toArray = sorted
    at permS sortedNodup rank1 rank2 ⊢
  generalize Array.foldl (fun r x => r.insert x.fst x.snd) (∅ : Std.HashMap Nat Nat) sorted.zipIdx = rank
    at rank1 rank2 ⊢
  have attachEq : List.foldl (fun (b : Array Nat × Array (Array Nat))
        (x : {x // x ∈ List.range' 0 sorted.size}) =>
        (b.fst.set! x.val (List.filterMap rank.get? (deps sorted[x.val]!)).eraseDups.length,
          List.foldl (fun b a => b.modify a fun x_1 => x_1.push x.val) b.snd
            (List.filterMap rank.get? (deps sorted[x.val]!)).eraseDups))
        (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range' 0 sorted.size).attach =
      List.foldl (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
        (b.fst.set! i (kahnDs rank deps sorted i).length,
          List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
        (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range sorted.size) := by
    rw [List.range_eq_range']
    exact List.foldl_attach (l := List.range' 0 sorted.size)
      (f := fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
        (b.fst.set! i (kahnDs rank deps sorted i).length,
          List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
      (b := (Array.replicate sorted.size 0, Array.replicate sorted.size #[]))
  rw [attachEq]
  obtain ⟨pendSize, pendInit, -, usersMem, usersNodup, -⟩ :=
    kahnSetup_spec sorted rank deps sorted.size (Nat.le_refl _)
  generalize List.foldl (fun (b : Array Nat × Array (Array Nat)) (i : Nat) =>
      (b.fst.set! i (kahnDs rank deps sorted i).length,
        List.foldl (fun b a => b.modify a fun x => x.push i) b.snd (kahnDs rank deps sorted i)))
      (Array.replicate sorted.size 0, Array.replicate sorted.size #[]) (List.range sorted.size) = setup
    at pendSize pendInit usersMem usersNodup ⊢
  exact kahn_core deps rest sorted rank setup _ (fun x b => rfl) permS rank1 pendSize pendInit
    usersMem usersNodup acyclic

end Ix.Sharing.Verify.Tiered

#guard_kernel_axioms Ix.Sharing.Verify.Tiered.kahnOrder_spec [propext, Classical.choice, Quot.sound]
