import Ix.CompileCert.Canon.CliqueMap
import Ix.CompileCert.Canon.Evaporate
import Ix.Compile.Canon.NameMap

/-!
# M7 L1, the block name map is well defined

`Ix.Compile.Canon.blockNameMap const? b` maps every Lean name of the block `b` to its canonical
position: each member, and its `rec`, `recOn`, `casesOn`, `below`, `brecOn`, to its component and
class; each constructor to its member's position and its index; each of Lean's nested names
`all₀.rec_{j+1}`, `all₀.below_{j+1}`, `all₀.brecOn_{j+1}` to the canonical auxiliary a component
maps position `j` to, or `evaporated`, or `outside`.

The map is two phases of insertions (`blockNameMap_eq`): the member phase inserts the pairs
`memberPairs`, the nested phase processes `nestedEvents` (`nestedStep`: a canonical or evaporated
position is inserted; `outside` only where the name is not mapped yet). Names are compared by `==`
(hash equality), so the statements assume what Lean's names satisfy (`NameMapKeys`): the member
phase's names are pairwise distinct, the nested names of distinct positions and suffixes are
distinct, and no member-phase name is a nested name. Then:

* every member, its suffix names and its constructors are mapped as the member phase says
  (`blockNameMap_memberPairs`, `blockNameMap_member`, `blockNameMap_suffix`,
  `blockNameMap_ctor`);
* a nested name of position `j` is mapped to `nestedVal b j`, the fold of the positions the
  components give `j` (`blockNameMap_nested`): the last canonical or evaporated position, else
  `outside` when some component has nested data at `j`, else nothing (`nestedVal_aux`,
  `nestedVal_evaporated`, `nestedVal_outside`, `nestedVal_none`); with
  `canonBlock_evaporated_perm`, a position a component evaporates has no canonical position there;
* no other name is mapped (`blockNameMap_other`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name ConstantInfo)

/-! ## Loops of insertions -/

/-- A `for` loop in `Id` whose body folds a list of items into the state is the fold of all the
items. -/
theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem forIn_id_flat {α γ β : Type} (step : β → γ → β) (g : α → List γ)
    (body : α → β → Id (ForInStep β)) (h : ∀ x r, body x r = .yield ((g x).foldl step r)) :
    ∀ (l : List α) (init : β), forIn (m := Id) l init body = (l.flatMap g).foldl step init := by
  intro l init
  rw [forIn_id_list body (fun x r => by rw [h x r]; rfl)]
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, List.flatMap_cons, List.foldl_append, ← ih]
    rw [h x init]; rfl

theorem forIn_id_flat_array {α γ β : Type} (step : β → γ → β) (g : α → List γ)
    (body : α → β → Id (ForInStep β)) (h : ∀ x r, body x r = .yield ((g x).foldl step r))
    (xs : Array α) (init : β) :
    forIn (m := Id) xs init body = (xs.toList.flatMap g).foldl step init := by
  rw [← Array.forIn_toList, forIn_id_flat step g body h]

theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

/-- Insert a pair. -/
abbrev insStep (m : Std.HashMap Name CanonPos) (p : Name × CanonPos) : Std.HashMap Name CanonPos :=
  m.insert p.1 p.2

/-- The nested phase's step: a position is inserted; a name with no position is marked `outside`
unless it is already mapped. -/
def nestedStep (m : Std.HashMap Name CanonPos) (e : Name × Option CanonPos) :
    Std.HashMap Name CanonPos :=
  match e.2 with
  | some p => m.insert e.1 p
  | none => if (!m.contains e.1) = true then m.insert e.1 .outside else m

/-! ## The two phases -/

/-- The pairs the member phase inserts for the name `n` of class `k` of component `ci`. -/
def namePairs (const? : Name → Option ConstantInfo) (ci k : Nat) (n : Name) :
    List (Name × CanonPos) :=
  (n, .member ci k) :: ((memberSuffixes.flatMap fun s => [(n.mkStr s, .member ci k)]) ++
    (match const? n with
      | some (.inductInfo v) => v.ctors.zipIdx.toList.flatMap fun p => [(p.1, .ctor ci k p.2)]
      | _ => []))

/-- The pairs the member phase inserts, in order. -/
def memberPairs (const? : Name → Option ConstantInfo) (b : BlockCanon) : List (Name × CanonPos) :=
  b.components.zipIdx.toList.flatMap fun cc =>
    cc.1.classes.zipIdx.toList.flatMap fun kk =>
      kk.1.toList.flatMap (namePairs const? cc.2 kk.2)

/-- The position the nested phase records for Lean's position `j` of component `ci`. -/
def nposOf (n : NestedCanon) (ci : Nat) (p : Option Nat) (j : Nat) : Option CanonPos :=
  match p with
  | some a => some (.aux ci a)
  | none => if n.evaporated[j]?.getD false = true then some .evaporated else none

/-- The three nested suffixes. -/
def nestedSuffixes : List String := ["rec", "below", "brecOn"]

/-- Lean's nested name of suffix `s` at position `j`. -/
abbrev nestedName (all0 : Name) (s : String) (j : Nat) : Name := all0.mkStr s!"{s}_{j + 1}"

/-- The nested phase's events, in order: per component with nested data, per Lean position, the
three nested names with the component's position. -/
def nestedEvents (all0 : Name) (b : BlockCanon) : List (Name × Option CanonPos) :=
  b.components.zipIdx.toList.flatMap fun cc =>
    match cc.1.nested with
    | some n => n.perm.zipIdx.toList.flatMap fun pj =>
        nestedSuffixes.flatMap fun s => [(nestedName all0 s pj.2, nposOf n cc.2 pj.1 pj.2)]
    | none => []

/-- **`blockNameMap` is the member phase, then the nested phase.** -/
theorem blockNameMap_eq (const? : Name → Option ConstantInfo) (b : BlockCanon) :
    blockNameMap const? b =
      match b.all[0]? with
      | some all0 => (nestedEvents all0 b).foldl nestedStep ((memberPairs const? b).foldl insStep ∅)
      | none => (memberPairs const? b).foldl insStep ∅ := by
  unfold blockNameMap
  dsimp only [Id.run]
  rw [forIn_id_flat_array insStep (fun cc => cc.1.classes.zipIdx.toList.flatMap fun kk =>
      kk.1.toList.flatMap (namePairs const? cc.2 kk.2))]
  · cases hall : b.all[0]? with
    | none => rfl
    | some all0 =>
      simp only [id_bind_eq]
      rw [forIn_id_flat_array nestedStep (fun cc => match cc.1.nested with
        | some n => n.perm.zipIdx.toList.flatMap fun pj =>
            nestedSuffixes.flatMap fun s => [(nestedName all0 s pj.2, nposOf n cc.2 pj.1 pj.2)]
        | none => [])]
      · rfl
      · intro x r
        obtain ⟨c, ci⟩ := x
        dsimp only
        cases hn : c.nested with
        | none => rfl
        | some n =>
          dsimp only
          rw [forIn_id_flat_array nestedStep (fun pj =>
            nestedSuffixes.flatMap fun s => [(nestedName all0 s pj.2, nposOf n ci pj.1 pj.2)])]
          · rfl
          · intro x r
            obtain ⟨p, j⟩ := x
            dsimp only
            cases p with
            | some a =>
              dsimp only
              rw [forIn_id_flat nestedStep (fun s => [(nestedName all0 s j, nposOf n ci (some a) j)])]
              · rfl
              · intro s r; rfl
            | none =>
              dsimp only
              by_cases hev : n.evaporated[j]?.getD false = true
              · simp only [hev, ↓reduceIte]
                rw [forIn_id_flat nestedStep (fun s => [(nestedName all0 s j, nposOf n ci none j)])]
                · rfl
                · intro s r
                  simp only [nposOf, hev, ↓reduceIte]; rfl
              · simp only [hev, Bool.false_eq_true, ↓reduceIte]
                rw [forIn_id_flat nestedStep (fun s => [(nestedName all0 s j, nposOf n ci none j)])]
                · rfl
                · intro s r
                  simp only [nposOf, hev, Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, nestedStep]
                  by_cases hc : (!r.contains (nestedName all0 s j)) = true
                  · simp only [hc, ↓reduceIte]; rfl
                  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl
  · intro x r
    obtain ⟨c, ci⟩ := x
    dsimp only
    rw [forIn_id_flat_array insStep (fun kk => kk.1.toList.flatMap (namePairs const? ci kk.2))]
    · rfl
    · intro x r
      obtain ⟨cls, k⟩ := x
      dsimp only
      rw [forIn_id_flat_array insStep (namePairs const? ci k)]
      · rfl
      · intro n r
        try dsimp only
        rw [forIn_id_flat insStep (fun s => [(n.mkStr s, CanonPos.member ci k)])]
        · cases hc : const? n with
          | none =>
            simp only [namePairs, hc, List.append_nil, List.foldl_cons]; rfl
          | some cinfo =>
            cases cinfo with
            | inductInfo v =>
              simp only [id_bind_eq]
              rw [forIn_id_flat_array insStep (fun (p : Name × Nat) => [(p.1, CanonPos.ctor ci k p.2)])]
              · simp only [namePairs, hc, List.foldl_cons, List.foldl_append]; rfl
              · intro x r; obtain ⟨cn, j⟩ := x; rfl
            | _ => simp only [namePairs, hc, List.append_nil, List.foldl_cons]; rfl
        · intro s r; rfl

/-! ## Lookups -/

/-- The value the nested phase leaves for one name: each event of that name in turn. -/
def stepVal (v : Option CanonPos) (e : Option CanonPos) : Option CanonPos :=
  match e with
  | some p => some p
  | none => match v with
    | some q => some q
    | none => some .outside

theorem nestedFold_getElem? : ∀ (L : List (Name × Option CanonPos)) (m : Std.HashMap Name CanonPos)
    (x : Name), (L.foldl nestedStep m)[x]? =
      ((L.filter fun e => e.1 == x).map (·.2)).foldl stepVal m[x]?
  | [], _, _ => rfl
  | e :: L, m, x => by
    rw [List.foldl_cons, nestedFold_getElem? L _ x, List.filter_cons]
    obtain ⟨k, pos⟩ := e
    by_cases hk : (k == x) = true
    · simp only [hk, ↓reduceIte, List.map_cons, List.foldl_cons]
      congr 1
      cases pos with
      | some p =>
        simp only [nestedStep, stepVal]
        rw [Std.HashMap.getElem?_insert, ite_eq_left hk]
      | none =>
        simp only [nestedStep, stepVal]
        rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_congr hk]
        cases hm : m[x]? with
        | none =>
          simp only [Option.isSome_none, Bool.not_false, ↓reduceIte]
          rw [Std.HashMap.getElem?_insert, ite_eq_left hk]
        | some q => simp [hm]
    · have hk' : (k == x) = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      congr 1
      cases pos with
      | some p =>
        simp only [nestedStep]
        rw [Std.HashMap.getElem?_insert, hk']; rfl
      | none =>
        simp only [nestedStep]
        split
        · rw [Std.HashMap.getElem?_insert, hk']; rfl
        · rfl

theorem foldl_stepVal_none_iff : ∀ (L : List (Option CanonPos)) (v : Option CanonPos),
    L.foldl stepVal v = none ↔ v = none ∧ L = []
  | [], v => by simp
  | e :: L, v => by
    rw [List.foldl_cons, foldl_stepVal_none_iff L]
    constructor
    · rintro ⟨h, -⟩
      cases e <;> cases v <;> simp [stepVal] at h
    · rintro ⟨-, h⟩; cases h

/-- A value the fold leaves is the start value, an element, or `outside`. -/
theorem foldl_stepVal_mem : ∀ (L : List (Option CanonPos)) (v : Option CanonPos) (p : CanonPos),
    L.foldl stepVal v = some p → v = some p ∨ some p ∈ L ∨ p = .outside
  | [], v, p, h => .inl h
  | e :: L, v, p, h => by
    rw [List.foldl_cons] at h
    rcases foldl_stepVal_mem L _ p h with h | h | h
    · cases e with
      | some q =>
        simp only [stepVal, Option.some.injEq] at h
        exact .inr (.inl (by rw [h]; exact List.mem_cons_self ..))
      | none =>
        cases v with
        | some q => simp only [stepVal] at h; exact .inl h
        | none => simp only [stepVal, Option.some.injEq] at h; exact .inr (.inr h.symm)
    · exact .inr (.inl (List.mem_cons_of_mem _ h))
    · exact .inr (.inr h)

/-- `outside` is left only when no element is a position. -/
theorem foldl_stepVal_outside : ∀ (L : List (Option CanonPos)),
    (∀ e ∈ L, e ≠ some .outside) → L.foldl stepVal none = some .outside → ∀ e ∈ L, e = none
  | [], _, _ => by simp
  | e :: L, hL, h => by
    intro e' he'
    rw [List.foldl_cons] at h
    cases e with
    | some p =>
      exfalso
      -- once a position is set, the fold never returns to `outside` unless an element is `outside`
      have key : ∀ (L : List (Option CanonPos)) (q : CanonPos), q ≠ .outside →
          (∀ e ∈ L, e ≠ some .outside) → L.foldl stepVal (some q) ≠ some .outside := by
        intro L
        induction L with
        | nil => intro q hq _ h; simp only [List.foldl_nil, Option.some.injEq] at h; exact hq h
        | cons e L ih =>
          intro q hq hL h
          rw [List.foldl_cons] at h
          cases e with
          | some r =>
            exact ih r (fun hr => hL (some r) (List.mem_cons_self ..) (by rw [hr]))
              (fun e he => hL e (List.mem_cons_of_mem _ he)) h
          | none => exact ih q hq (fun e he => hL e (List.mem_cons_of_mem _ he)) h
      exact key L p (fun hp => hL (some p) (List.mem_cons_self ..) (by rw [hp]))
        (fun e he => hL e (List.mem_cons_of_mem _ he)) h
    | none =>
      rcases List.mem_cons.1 he' with rfl | he'
      · rfl
      · -- after a `none`, the fold continues from `outside`
        have key : ∀ (L : List (Option CanonPos)), (∀ e ∈ L, e ≠ some .outside) →
            L.foldl stepVal (some .outside) = some .outside → ∀ e ∈ L, e = none := by
          intro L
          induction L with
          | nil => simp
          | cons e L ih =>
            intro hL h e' he'
            rw [List.foldl_cons] at h
            cases e with
            | some r =>
              exfalso
              have hr : r ≠ .outside := fun hr => hL (some r) (List.mem_cons_self ..) (by rw [hr])
              have := foldl_stepVal_mem L (some r) .outside h
              rcases this with h1 | h1 | -
              · simp only [Option.some.injEq] at h1; exact hr h1
              · exact hL _ (List.mem_cons_of_mem _ h1) rfl
              · -- the fold from `some r` returning `outside` needs an `outside` element
                have key2 : ∀ (L : List (Option CanonPos)) (q : CanonPos), q ≠ .outside →
                    (∀ e ∈ L, e ≠ some .outside) → L.foldl stepVal (some q) ≠ some .outside := by
                  intro L
                  induction L with
                  | nil => intro q hq _ h; simp only [List.foldl_nil, Option.some.injEq] at h; exact hq h
                  | cons e L ih =>
                    intro q hq hL h
                    rw [List.foldl_cons] at h
                    cases e with
                    | some r =>
                      exact ih r (fun hr => hL (some r) (List.mem_cons_self ..) (by rw [hr]))
                        (fun e he => hL e (List.mem_cons_of_mem _ he)) h
                    | none => exact ih q hq (fun e he => hL e (List.mem_cons_of_mem _ he)) h
                exact key2 L r hr (fun e he => hL e (List.mem_cons_of_mem _ he)) h
            | none =>
              rcases List.mem_cons.1 he' with rfl | he'
              · rfl
              · exact ih (fun e he => hL e (List.mem_cons_of_mem _ he)) h e' he'
        exact key L (fun e he => hL e (List.mem_cons_of_mem _ he)) h e' he'

/-! ## The name map -/

/-- The positions the components give Lean's position `j`, in component order. -/
def nestedVals (b : BlockCanon) (j : Nat) : List (Option CanonPos) :=
  b.components.zipIdx.toList.flatMap fun cc =>
    match cc.1.nested with
    | some n => (match n.perm[j]? with
      | some p => [nposOf n cc.2 p j]
      | none => [])
    | none => []

/-- The value of the nested names of position `j`. -/
def nestedVal (b : BlockCanon) (j : Nat) : Option CanonPos := (nestedVals b j).foldl stepVal none

/-- What `==` must not confuse (Lean's names are distinct): the member phase's names pairwise, the
nested names of distinct positions or suffixes (below `J`, a bound of every component's position
count), and a member-phase name with a nested name. -/
structure NameMapKeys (const? : Name → Option ConstantInfo) (b : BlockCanon) (all0 : Name) (J : Nat) :
    Prop where
  bound : ∀ c ∈ b.components, ∀ n, c.nested = some n → n.perm.size ≤ J
  members : ((memberPairs const? b).map (·.1)).Pairwise fun a b => (a == b) = false
  nested : ∀ s ∈ nestedSuffixes, ∀ s' ∈ nestedSuffixes, ∀ j < J, ∀ j' < J,
    (nestedName all0 s j == nestedName all0 s' j') = true → s = s' ∧ j = j'
  disjoint : ∀ p ∈ memberPairs const? b, ∀ s ∈ nestedSuffixes, ∀ j < J,
    (p.1 == nestedName all0 s j) = false

theorem nposOf_ne_outside (n : NestedCanon) (ci : Nat) (p : Option Nat) (j : Nat) :
    nposOf n ci p j ≠ some .outside := by
  unfold nposOf
  cases p with
  | some a => simp
  | none => split <;> simp

theorem mem_nestedEvents {all0 : Name} {b : BlockCanon} {e : Name × Option CanonPos}
    (he : e ∈ nestedEvents all0 b) :
    ∃ (ci : Nat) (c : ComponentCanon) (n : NestedCanon) (j : Nat) (p : Option Nat) (s : String), b.components[ci]? = some c ∧ c.nested = some n ∧ n.perm[j]? = some p ∧
      s ∈ nestedSuffixes ∧ e = (nestedName all0 s j, nposOf n ci p j) := by
  unfold nestedEvents at he
  obtain ⟨⟨c, ci⟩, hc, he⟩ := List.mem_flatMap.1 he
  have hci : b.components[ci]? = some c := by
    exact Array.mem_zipIdx_iff_getElem?.1 (Array.mem_toList_iff.1 hc)
  dsimp only at he
  cases hn : c.nested with
  | none => rw [hn] at he; simp at he
  | some n =>
    rw [hn] at he
    obtain ⟨⟨p, j⟩, hp, he⟩ := List.mem_flatMap.1 he
    have hpj : n.perm[j]? = some p := by
      exact Array.mem_zipIdx_iff_getElem?.1 (Array.mem_toList_iff.1 hp)
    obtain ⟨s, hs, he⟩ := List.mem_flatMap.1 he
    rw [List.mem_singleton] at he
    exact ⟨ci, c, n, j, p, s, hci, hn, hpj, hs, he⟩

/-- The member phase's lookups survive the nested phase: a name `==` to no nested name keeps its
value. -/
theorem nested_preserves {all0 : Name} {b : BlockCanon} {m : Std.HashMap Name CanonPos} {x : Name}
    (hx : ∀ e ∈ nestedEvents all0 b, (e.1 == x) = false) :
    ((nestedEvents all0 b).foldl nestedStep m)[x]? = m[x]? := by
  rw [nestedFold_getElem?]
  rw [List.filter_eq_nil_iff.2 (fun e he => by simp [hx e he])]
  rfl

theorem nestedName_lt {b : BlockCanon} {J : Nat} (hb : ∀ c ∈ b.components, ∀ n,
    c.nested = some n → n.perm.size ≤ J) {ci : Nat} {c : ComponentCanon} {n : NestedCanon} {j : Nat}
    {p : Option Nat} (hci : b.components[ci]? = some c) (hn : c.nested = some n)
    (hpj : n.perm[j]? = some p) : j < J := by
  have := hb c (Array.mem_of_getElem? hci) n hn
  have hj : j < n.perm.size := by
    rcases Nat.lt_or_ge j n.perm.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hpj; cases hpj
  omega

/-- **The member phase's names are mapped as it says.** -/
theorem blockNameMap_memberPairs {const? : Name → Option ConstantInfo} {b : BlockCanon} {all0 : Name}
    {J : Nat} (hall : b.all[0]? = some all0) (hk : NameMapKeys const? b all0 J)
    {p : Name × CanonPos} (hp : p ∈ memberPairs const? b) :
    (blockNameMap const? b)[p.1]? = some p.2 := by
  rw [blockNameMap_eq]
  simp only [hall]
  rw [nested_preserves (all0 := all0) (fun e he => ?_)]
  · rw [foldl_insert_getElem?' _ _ hk.members]
    exact .inl ⟨p, hp, name_beq_refl _, rfl⟩
  · obtain ⟨ci, c, n, j, q, s, hci, hn, hpj, hs, rfl⟩ := mem_nestedEvents he
    have := hk.disjoint p hp s hs j (nestedName_lt hk.bound hci hn hpj)
    rw [name_beq_comm]; exact this

theorem nestedVals_filter {all0 : Name} {b : BlockCanon} {J : Nat}
    (hb : ∀ c ∈ b.components, ∀ n, c.nested = some n → n.perm.size ≤ J)
    (hnest : ∀ s ∈ nestedSuffixes, ∀ s' ∈ nestedSuffixes, ∀ j < J, ∀ j' < J,
      (nestedName all0 s j == nestedName all0 s' j') = true → s = s' ∧ j = j')
    {s : String} (hs : s ∈ nestedSuffixes) {j : Nat} (hj : j < J) :
    ((nestedEvents all0 b).filter fun e => e.1 == nestedName all0 s j).map (·.2) = nestedVals b j := by
  unfold nestedEvents nestedVals
  rw [List.filter_flatMap, List.map_flatMap]
  apply flatMap_congr'
  intro cc hcc
  obtain ⟨c, ci⟩ := cc
  have hci : b.components[ci]? = some c := by
    exact Array.mem_zipIdx_iff_getElem?.1 (Array.mem_toList_iff.1 hcc)
  dsimp only
  cases hn : c.nested with
  | none => rfl
  | some n =>
    dsimp only
    rw [List.filter_flatMap, List.map_flatMap]
    -- position by position: only `j` survives, with exactly the suffix `s`
    have hpos : ∀ (pj : Option Nat × Nat), pj ∈ n.perm.zipIdx.toList →
        ((nestedSuffixes.flatMap fun s' => [(nestedName all0 s' pj.2, nposOf n ci pj.1 pj.2)]).filter
          (fun e => e.1 == nestedName all0 s j)).map (·.2) =
        if pj.2 = j then [nposOf n ci pj.1 pj.2] else [] := by
      intro pj hpj
      have hpj' : n.perm[pj.2]? = some pj.1 := by
        exact Array.mem_zipIdx_iff_getElem?.1 (Array.mem_toList_iff.1 hpj)
      have hlt : pj.2 < J := nestedName_lt hb hci hn hpj'
      have hiff : ∀ s' ∈ nestedSuffixes,
          (nestedName all0 s' pj.2 == nestedName all0 s j) = true ↔ s' = s ∧ pj.2 = j := by
        intro s' hs'
        constructor
        · exact hnest s' hs' s hs pj.2 hlt j hj
        · rintro ⟨rfl, h⟩; rw [h]; exact name_beq_refl _
      unfold nestedSuffixes at hiff hs ⊢
      simp only [List.flatMap_cons, List.flatMap_nil, List.singleton_append, List.filter_cons,
        List.filter_nil, List.mem_cons, List.mem_nil_iff, or_false] at hiff hs ⊢
      have h1 := hiff "rec" (.inl rfl)
      have h2 := hiff "below" (.inr (.inl rfl))
      have h3 := hiff "brecOn" (.inr (.inr rfl))
      by_cases hjj : pj.2 = j
      · simp only [hjj, and_true] at h1 h2 h3
        rcases hs with rfl | rfl | rfl <;> simp_all
      · simp only [hjj, and_false, iff_false, Bool.not_eq_true] at h1 h2 h3
        simp [h1, h2, h3, hjj]
    rw [flatMap_congr' hpos]
    -- the positions `pj` of the list with `pj.2 = j`
    have hz : ∀ (l : List (Option Nat)) (k : Nat),
        (l.zipIdx k).flatMap (fun pj => if pj.2 = j then [nposOf n ci pj.1 pj.2] else []) =
          match l[j - k]? with
          | some p => if k ≤ j then [nposOf n ci p j] else []
          | none => [] := by
      intro l
      induction l with
      | nil => intro k; simp
      | cons a l ih =>
        intro k
        rw [List.zipIdx_cons, List.flatMap_cons, ih (k + 1)]
        by_cases hkj : k = j
        · subst hkj
          simp only [↓reduceIte, Nat.sub_self, List.getElem?_cons_zero, Nat.le_refl]
          have : k - (k + 1) = 0 := by omega
          rw [this]
          cases l <;> simp
        · simp only [hkj, ↓reduceIte, List.nil_append]
          by_cases hkj' : k < j
          · have : j - k = (j - (k + 1)) + 1 := by omega
            rw [this, List.getElem?_cons_succ]
            have h1 : k + 1 ≤ j := by omega
            have h2 : k ≤ j := by omega
            cases l[j - (k + 1)]? <;> simp [h1, h2]
          · have h1 : ¬ k + 1 ≤ j := by omega
            have h2 : ¬ k ≤ j := by omega
            cases l[j - (k + 1)]? <;> cases (a :: l)[j - k]? <;> simp [h1, h2]
    rw [Array.toList_zipIdx, hz n.perm.toList 0, Nat.sub_zero, Array.getElem?_toList]
    cases n.perm[j]? <;> simp

/-- **A nested name is mapped to the fold of the positions the components give it.** -/
theorem blockNameMap_nested {const? : Name → Option ConstantInfo} {b : BlockCanon} {all0 : Name}
    {J : Nat} (hall : b.all[0]? = some all0) (hk : NameMapKeys const? b all0 J)
    {s : String} (hs : s ∈ nestedSuffixes) {j : Nat} (hj : j < J) :
    (blockNameMap const? b)[nestedName all0 s j]? = nestedVal b j := by
  rw [blockNameMap_eq]
  simp only [hall]
  rw [nestedFold_getElem?, nestedVals_filter hk.bound hk.nested hs hj]
  unfold nestedVal
  congr 1
  cases h : ((memberPairs const? b).foldl insStep ∅)[nestedName all0 s j]? with
  | none => rfl
  | some i =>
    exfalso
    rcases (foldl_insert_getElem?' _ _ hk.members _ i).1 h with ⟨p, hp, hpx, -⟩ | ⟨-, h0⟩
    · rw [hk.disjoint p hp s hs j hj] at hpx; cases hpx
    · simp at h0

/-- **No other name is mapped.** -/
theorem blockNameMap_other {const? : Name → Option ConstantInfo} {b : BlockCanon} {all0 : Name}
    {J : Nat} (hall : b.all[0]? = some all0) (hk : NameMapKeys const? b all0 J) {x : Name}
    (hm : ∀ p ∈ memberPairs const? b, (p.1 == x) = false)
    (hn : ∀ s ∈ nestedSuffixes, ∀ j < J, (nestedName all0 s j == x) = false) :
    (blockNameMap const? b)[x]? = none := by
  rw [blockNameMap_eq]
  simp only [hall]
  rw [nested_preserves (all0 := all0) (fun e he => ?_)]
  · cases h : ((memberPairs const? b).foldl insStep ∅)[x]? with
    | none => rfl
    | some i =>
      exfalso
      rcases (foldl_insert_getElem?' _ _ hk.members _ i).1 h with ⟨p, hp, hpx, -⟩ | ⟨-, h0⟩
      · rw [hm p hp] at hpx; cases hpx
      · simp at h0
  · obtain ⟨ci, c, n, j, q, s, hci, hn', hpj, hs, rfl⟩ := mem_nestedEvents he
    exact hn s hs j (nestedName_lt hk.bound hci hn' hpj)

/-- The member phase holds a member's pairs. -/
theorem mem_memberPairs_member {const? : Name → Option ConstantInfo} {b : BlockCanon} {ci k : Nat}
    {c : ComponentCanon} {cls : Array Name} {n : Name} (hc : b.components[ci]? = some c)
    (hcls : c.classes[k]? = some cls) (hn : n ∈ cls) :
    (n, CanonPos.member ci k) ∈ memberPairs const? b ∧
    (∀ s ∈ memberSuffixes, (n.mkStr s, CanonPos.member ci k) ∈ memberPairs const? b) ∧
    (∀ v, const? n = some (.inductInfo v) → ∀ j cn, v.ctors[j]? = some cn →
      (cn, CanonPos.ctor ci k j) ∈ memberPairs const? b) := by
  have h1 : (c, ci) ∈ b.components.zipIdx.toList :=
    Array.mem_toList_iff.2 (Array.mem_zipIdx_iff_getElem?.2 hc)
  have h2 : (cls, k) ∈ c.classes.zipIdx.toList :=
    Array.mem_toList_iff.2 (Array.mem_zipIdx_iff_getElem?.2 hcls)
  have h3 : n ∈ cls.toList := Array.mem_toList_iff.2 hn
  have key : ∀ q ∈ namePairs const? ci k n, q ∈ memberPairs const? b := fun q hq =>
    List.mem_flatMap.2 ⟨(c, ci), h1, List.mem_flatMap.2 ⟨(cls, k), h2, List.mem_flatMap.2 ⟨n, h3, hq⟩⟩⟩
  refine ⟨key _ (List.mem_cons_self ..), fun s hs => key _ ?_, fun v hv j cn hj => key _ ?_⟩
  · unfold namePairs
    exact List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_flatMap.2 ⟨s, hs, List.mem_singleton.2 rfl⟩))
  · unfold namePairs
    rw [hv]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨(cn, j),
      Array.mem_toList_iff.2 (Array.mem_zipIdx_iff_getElem?.2 hj),
      List.mem_singleton.2 rfl⟩))

/-- **A member is mapped to its component and class.** -/
theorem blockNameMap_member {const? : Name → Option ConstantInfo} {b : BlockCanon} {all0 : Name}
    {J : Nat} (hall : b.all[0]? = some all0) (hk : NameMapKeys const? b all0 J) {ci k : Nat}
    {c : ComponentCanon} {cls : Array Name} {n : Name} (hc : b.components[ci]? = some c)
    (hcls : c.classes[k]? = some cls) (hn : n ∈ cls) :
    (blockNameMap const? b)[n]? = some (.member ci k) :=
  blockNameMap_memberPairs hall hk (mem_memberPairs_member hc hcls hn).1

/-- **A member's `rec`, `recOn`, `casesOn`, `below`, `brecOn` are mapped to its position.** -/
theorem blockNameMap_suffix {const? : Name → Option ConstantInfo} {b : BlockCanon} {all0 : Name}
    {J : Nat} (hall : b.all[0]? = some all0) (hk : NameMapKeys const? b all0 J) {ci k : Nat}
    {c : ComponentCanon} {cls : Array Name} {n : Name} (hc : b.components[ci]? = some c)
    (hcls : c.classes[k]? = some cls) (hn : n ∈ cls) {s : String} (hs : s ∈ memberSuffixes) :
    (blockNameMap const? b)[n.mkStr s]? = some (.member ci k) :=
  blockNameMap_memberPairs hall hk ((mem_memberPairs_member hc hcls hn).2.1 s hs)

/-- **A constructor is mapped to its member's position and its index.** -/
theorem blockNameMap_ctor {const? : Name → Option ConstantInfo} {b : BlockCanon} {all0 : Name}
    {J : Nat} (hall : b.all[0]? = some all0) (hk : NameMapKeys const? b all0 J) {ci k : Nat}
    {c : ComponentCanon} {cls : Array Name} {n : Name} (hc : b.components[ci]? = some c)
    (hcls : c.classes[k]? = some cls) (hn : n ∈ cls) {v : Ix.InductiveVal}
    (hv : const? n = some (.inductInfo v)) {j : Nat} {cn : Name} (hj : v.ctors[j]? = some cn) :
    (blockNameMap const? b)[cn]? = some (.ctor ci k j) :=
  blockNameMap_memberPairs hall hk ((mem_memberPairs_member hc hcls hn).2.2 v hv j cn hj)

theorem mem_nestedVals {b : BlockCanon} {j : Nat} {e : Option CanonPos} (he : e ∈ nestedVals b j) :
    ∃ (ci : Nat) (c : ComponentCanon) (n : NestedCanon) (p : Option Nat), b.components[ci]? = some c ∧ c.nested = some n ∧ n.perm[j]? = some p ∧
      e = nposOf n ci p j := by
  unfold nestedVals at he
  obtain ⟨⟨c, ci⟩, hc, he⟩ := List.mem_flatMap.1 he
  have hci : b.components[ci]? = some c := by
    exact Array.mem_zipIdx_iff_getElem?.1 (Array.mem_toList_iff.1 hc)
  dsimp only at he
  cases hn : c.nested with
  | none => rw [hn] at he; simp at he
  | some n =>
    rw [hn] at he
    dsimp only at he
    cases hp : n.perm[j]? with
    | none => rw [hp] at he; simp at he
    | some p =>
      rw [hp] at he
      exact ⟨ci, c, n, p, hci, hn, hp, List.mem_singleton.1 he⟩

theorem nposOf_mem_nestedVals {b : BlockCanon} {j ci : Nat} {c : ComponentCanon} {n : NestedCanon}
    {p : Option Nat} (hc : b.components[ci]? = some c) (hn : c.nested = some n)
    (hp : n.perm[j]? = some p) : nposOf n ci p j ∈ nestedVals b j := by
  unfold nestedVals
  refine List.mem_flatMap.2 ⟨(c, ci), Array.mem_toList_iff.2 (Array.mem_zipIdx_iff_getElem?.2 hc), ?_⟩
  dsimp only
  rw [hn]; dsimp only; rw [hp]
  exact List.mem_singleton.2 rfl

/-- **A nested name mapped to a canonical auxiliary**: the component maps the position there. -/
theorem nestedVal_aux {b : BlockCanon} {j ci a : Nat} (h : nestedVal b j = some (.aux ci a)) :
    ∃ (c : ComponentCanon) (n : NestedCanon), b.components[ci]? = some c ∧ c.nested = some n ∧ n.perm[j]? = some (some a) := by
  rcases foldl_stepVal_mem _ none _ h with h | h | h
  · cases h
  · obtain ⟨ci', c, n, p, hc, hn, hp, he⟩ := mem_nestedVals h
    cases p with
    | some a' =>
      simp only [nposOf, Option.some.injEq, CanonPos.aux.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨c, n, hc, hn, hp⟩
    | none => simp only [nposOf] at he; split at he <;> simp at he
  · cases h

/-- **A nested name mapped to `evaporated`**: some component has no canonical position for it and
flags it evaporated. -/
theorem nestedVal_evaporated {b : BlockCanon} {j : Nat} (h : nestedVal b j = some .evaporated) :
    ∃ (ci : Nat) (c : ComponentCanon) (n : NestedCanon), b.components[ci]? = some c ∧ c.nested = some n ∧ n.perm[j]? = some none ∧
      n.evaporated[j]? = some true := by
  rcases foldl_stepVal_mem _ none _ h with h | h | h
  · cases h
  · obtain ⟨ci, c, n, p, hc, hn, hp, he⟩ := mem_nestedVals h
    cases p with
    | some a' => simp [nposOf] at he
    | none =>
      simp only [nposOf] at he
      split at he
      · rename_i hev
        refine ⟨ci, c, n, hc, hn, hp, ?_⟩
        cases hq : n.evaporated[j]? with
        | none => rw [hq] at hev; cases hev
        | some v => rw [hq] at hev; simp only [Option.getD_some] at hev; rw [hev]
      · cases he
  · cases h

/-- **A nested name mapped to `outside`**: some component has nested data at the position, and no
component gives it a canonical or evaporated position. -/
theorem nestedVal_outside {b : BlockCanon} {j : Nat} (h : nestedVal b j = some .outside) :
    (∃ (ci : Nat) (c : ComponentCanon) (n : NestedCanon) (p : Option Nat), b.components[ci]? = some c ∧ c.nested = some n ∧ n.perm[j]? = some p) ∧
    ∀ (ci : Nat) (c : ComponentCanon) (n : NestedCanon) (p : Option Nat), b.components[ci]? = some c → c.nested = some n → n.perm[j]? = some p →
      nposOf n ci p j = none := by
  have hall := foldl_stepVal_outside (nestedVals b j) (fun e he => by
    obtain ⟨ci, c, n, p, -, -, -, rfl⟩ := mem_nestedVals he
    exact nposOf_ne_outside n ci p j) h
  constructor
  · cases hL : nestedVals b j with
    | nil => unfold nestedVal at h; rw [hL] at h; cases h
    | cons e L =>
      obtain ⟨ci, c, n, p, hc, hn, hp, -⟩ := mem_nestedVals (hL ▸ List.mem_cons_self .. : e ∈ nestedVals b j)
      exact ⟨ci, c, n, p, hc, hn, hp⟩
  · intro ci c n p hc hn hp
    exact hall _ (nposOf_mem_nestedVals hc hn hp)

/-- **A nested name is unmapped exactly when no component has nested data at the position.** -/
theorem nestedVal_none {b : BlockCanon} {j : Nat} :
    nestedVal b j = none ↔
      ∀ (ci : Nat) (c : ComponentCanon) (n : NestedCanon), b.components[ci]? = some c → c.nested = some n → n.perm[j]? = none := by
  unfold nestedVal
  rw [foldl_stepVal_none_iff]
  constructor
  · rintro ⟨-, hL⟩ ci c n hc hn
    cases hp : n.perm[j]? with
    | none => rfl
    | some p =>
      have := nposOf_mem_nestedVals hc hn hp
      rw [hL] at this; cases this
  · intro h
    refine ⟨rfl, ?_⟩
    cases hL : nestedVals b j with
    | nil => rfl
    | cons e L =>
      exfalso
      obtain ⟨ci, c, n, p, hc, hn, hp, -⟩ := mem_nestedVals (hL ▸ List.mem_cons_self .. : e ∈ nestedVals b j)
      rw [h ci c n hc hn] at hp; cases hp

end Ix.CompileCert.Canon
