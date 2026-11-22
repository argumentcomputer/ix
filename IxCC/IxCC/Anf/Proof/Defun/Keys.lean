import IxCC.Anf.Defun
import IxCC.Src.Proof.NatMap
import IxCC.Anf.Proof.Defun.Scope

/-! # P8's closure sources have distinct keys

`Defun.firstEqualKeys` buckets keys by `GKey.bucket` and compares them within
a bucket. When it finds no equal pair, the keys are pairwise distinct
(`firstEqualKeys_none`): every key seen so far sits in its bucket's list, so a
later equal key would have been found there. `checkSources` runs it on the
keys of the globals whose closures the program builds, and they are then
pairwise distinct (`checkSources_ownerKeys`). The pass runs the linear
`firstEqualKeysT`, which files each key in a trie under a prefix-free code of
the key and compares it only with the keys filed there; it finds the same
pair (`firstEqualKeysT_eq`).

From this, every closure source of a successful run has its own key
(`sources_keys`), so a dispatcher's alternatives for one source are never
shadowed by another's (`docs/closures-design.md`, "Proof obligation"):

* an escaping global is an owner, so the escaping globals' keys are distinct
  (`escape_sublist`);
* the walk keys the `i`-th local function of a global keyed `K` as
  `lam K [i]`, numbering from 0 in each global (`Grows`, `global_grows`), and
  only a global that lifts something becomes a parent, which is an owner; so
  the lifted functions' keys differ by their parent's key or by their index
  (`globalsGo_keys`, `ran_lifted_keys`);
* no input global is keyed `lam` (`checkInput_ok`), so a lifted function's key
  is never an escaping global's.

`Ran` collects what a successful run is made of (`run_ran`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

/-- Every pair seen so far is in its key's bucket. -/
def Seen (m : Src.NatMap (List (Key.GKey × GlobalId))) (seen : List (Key.GKey × GlobalId)) : Prop :=
  ∀ p ∈ seen, p ∈ m.getD p.1.bucket []

theorem firstEqualKeys_none_go : ∀ (ks : List (Key.GKey × GlobalId)) (m : Src.NatMap (List (Key.GKey × GlobalId)))
    (seen : List (Key.GKey × GlobalId)), Seen m seen → firstEqualKeys ks m = none →
    (ks.map (·.1)).Nodup ∧ ∀ p ∈ ks, ∀ q ∈ seen, p.1 ≠ q.1
  | [], _, _, _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | (k, g) :: ks, m, seen, hs, h => by
    simp only [firstEqualKeys] at h
    split at h
    · cases h
    · rename_i hf
      have hnot : ∀ q ∈ seen, k ≠ q.1 := by
        intro ⟨q1, q2⟩ hq hkq
        have hq' := hs (q1, q2) hq
        have hb : (q1, q2) ∈ m.getD k.bucket [] := by rw [hkq]; exact hq'
        have := List.find?_eq_none.1 hf (q1, q2) hb
        simp [hkq] at this
      have hs' : Seen (m.insert k.bucket ((k, g) :: m.getD k.bucket [])) ((k, g) :: seen) := by
        intro p hp
        show p ∈ ((m.insert k.bucket ((k, g) :: m.getD k.bucket [])).get? p.1.bucket).getD []
        rcases List.mem_cons.1 hp with rfl | hp
        · rw [Src.NatMap.get?_insert_self]
          exact List.mem_cons_self
        · by_cases hb : p.1.bucket = k.bucket
          · have h1 := hs p hp
            rw [hb] at h1
            rw [Src.NatMap.get?_insert, ite_eq_left hb]
            exact List.mem_cons_of_mem _ h1
          · rw [Src.NatMap.get?_insert, ite_eq_right hb]
            exact hs p hp
      obtain ⟨hnd, hall⟩ := firstEqualKeys_none_go ks _ _ hs' h
      refine ⟨List.nodup_cons.2 ⟨?_, hnd⟩, ?_⟩
      · intro hk
        obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hk
        exact hall p hp (k, g) List.mem_cons_self hpk
      · intro p hp q hq
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hnot q hq
        · exact hall p hp q (List.mem_cons_of_mem _ hq)

/-- **The key check is sound**: no equal pair found, the keys are pairwise
distinct. -/
theorem firstEqualKeys_none {ks : List (Key.GKey × GlobalId)} (h : firstEqualKeys ks .leaf = none) :
    (ks.map (·.1)).Nodup :=
  (firstEqualKeys_none_go ks .leaf [] (fun _ h => absurd h List.not_mem_nil) h).1

/-- The globals whose closures the program builds, with their keys, as
`checkSources` lists them. -/
def ownerKeys (P : Program) (acc : Acc) (parents : List GlobalId) : List (Key.GKey × GlobalId) :=
  let owners := Src.NatSet.ofList ((escapeSources P acc).map (·.id) ++ parents)
  (List.range P.size).filterMap fun h =>
    if owners.contains h then (P.global? h).map fun hd => (hd.key, h) else none

/-! ## The linear check finds what the bucketed one finds -/

theorem keyTrie_find_empty : ∀ q : List Nat, KeyTrie.empty.find q = []
  | [] => rfl
  | _ :: _ => rfl

theorem keyTrie_find_add : ∀ (t : KeyTrie) (p q : List Nat) (x : Key.GKey × GlobalId),
    (t.add p x).find q = if q = p then x :: t.find q else t.find q
  | .node h k, [], [], x => rfl
  | .node h k, [], _ :: _, x => rfl
  | .node h k, _ :: _, [], x => rfl
  | .node h k, c :: cs, c' :: cs', x => by
    simp only [KeyTrie.add, KeyTrie.find, Src.NatMap.get?_insert, List.cons.injEq]
    by_cases hc : c' = c
    · subst hc
      simp only [ite_true, true_and]
      rw [keyTrie_find_add _ cs cs' x]
      cases k.get? c' with
      | none => simp only [Option.getD_none, keyTrie_find_empty]
      | some t => rfl
    · simp only [hc, ite_false, false_and]

/-- The two checks see the same first earlier pair with each key. -/
def SameFirst (t : KeyTrie) (m : Src.NatMap (List (Key.GKey × GlobalId))) : Prop :=
  ∀ k : Key.GKey, (t.find (gkeyCode k)).find? (fun p => decide (p.1 = k)) =
    (m.getD k.bucket []).find? (fun p => decide (p.1 = k))

theorem sameFirst_add {t : KeyTrie} {m : Src.NatMap (List (Key.GKey × GlobalId))} (h : SameFirst t m)
    (k0 : Key.GKey) (g0 : GlobalId) :
    SameFirst (t.add (gkeyCode k0) (k0, g0)) (m.insert k0.bucket ((k0, g0) :: m.getD k0.bucket [])) := by
  intro k
  rw [keyTrie_find_add]
  have hm : (m.insert k0.bucket ((k0, g0) :: m.getD k0.bucket [])).getD k.bucket [] =
      if k.bucket = k0.bucket then (k0, g0) :: m.getD k0.bucket [] else m.getD k.bucket [] := by
    unfold Src.NatMap.getD
    rw [Src.NatMap.get?_insert]
    split <;> rfl
  rw [hm]
  by_cases hk : k0 = k
  · subst hk
    rw [ite_eq_left rfl, ite_eq_left rfl, List.find?_cons_of_pos (by simp), List.find?_cons_of_pos (by simp)]
  · have hne : ¬ (fun p : Key.GKey × GlobalId => decide (p.1 = k)) (k0, g0) = true := fun h0 =>
      hk (of_decide_eq_true h0)
    have e1 : (if gkeyCode k = gkeyCode k0 then (k0, g0) :: t.find (gkeyCode k) else t.find (gkeyCode k)).find?
        (fun p => decide (p.1 = k)) = (t.find (gkeyCode k)).find? (fun p => decide (p.1 = k)) := by
      split
      · exact List.find?_cons_of_neg hne
      · rfl
    rw [e1, h k]
    split
    · rename_i hb
      rw [List.find?_cons_of_neg (p := fun p : Key.GKey × GlobalId => decide (p.1 = k)) hne, hb]
    · rfl

theorem firstEqualKeysT_go : ∀ (ks : List (Key.GKey × GlobalId)) (t : KeyTrie)
    (m : Src.NatMap (List (Key.GKey × GlobalId))), SameFirst t m → firstEqualKeysT ks t = firstEqualKeys ks m
  | [], _, _, _ => rfl
  | (k, g) :: ks, t, m, h => by
    have e1 : (t.find (gkeyCode k)).find? (fun (k', _) => decide (k' = k)) =
        (t.find (gkeyCode k)).find? (fun p => decide (p.1 = k)) := rfl
    have e2 : (m.getD k.bucket []).find? (fun (k', _) => decide (k' = k)) =
        (m.getD k.bucket []).find? (fun p => decide (p.1 = k)) := rfl
    simp only [firstEqualKeysT, firstEqualKeys]
    rw [e1, e2, h k]
    split
    · rfl
    · exact firstEqualKeysT_go ks _ _ (sameFirst_add h k g)

/-- **The linear key check is the bucketed one**: on every list of keys it
finds the same pair. -/
theorem firstEqualKeysT_eq (ks : List (Key.GKey × GlobalId)) :
    firstEqualKeysT ks .empty = firstEqualKeys ks .leaf :=
  firstEqualKeysT_go ks _ _ fun k => by
    rw [keyTrie_find_empty]
    rfl

/-- **Passing `checkSources`, the owners' keys are pairwise distinct.** -/
theorem checkSources_ownerKeys {P : Program} {acc : Acc} {parents : List GlobalId} {u : Unit}
    (h : checkSources P acc parents = .ok u) : ((ownerKeys P acc parents).map (·.1)).Nodup := by
  unfold checkSources at h
  cases hf : firstEqualKeysT (ownerKeys P acc parents) .empty with
  | none => exact firstEqualKeys_none (by rw [← firstEqualKeysT_eq]; exact hf)
  | some r =>
    obtain ⟨g', h'⟩ := r
    simp only [ownerKeys] at hf
    simp only [hf] at h
    cases h



/-! ## Lists -/

theorem nodup_map_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj hf h.2⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.1 hm
    exact h.1 (by rw [← hf b a he]; exact hb)

theorem eq_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · rw [ha'] at he; exact absurd (List.mem_map.2 ⟨b, hb', he.symm⟩) h.1
    · rw [hb'] at he; exact absurd (List.mem_map.2 ⟨a, ha', he⟩) h.1
    · exact eq_of_nodup_map h.2 ha' hb' he

theorem filterMap_sublist {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, f a = some b → g a = some b) → (l.filterMap f).Sublist (l.filterMap g)
  | [], _ => List.Sublist.slnil
  | a :: l, h => by
    have ih := filterMap_sublist l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    rw [List.filterMap_cons, List.filterMap_cons]
    cases hf : f a with
    | none =>
      cases g a with
      | none => exact ih
      | some b => exact ih.cons b
    | some b =>
      rw [h a List.mem_cons_self b hf]
      exact ih.cons_cons b

theorem mem_ite_cons {c : Prop} [Decidable c] {g x : Nat} {l : List Nat} (h : x ∈ l) :
    x ∈ (if c then g :: l else l) := by
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

theorem natSet_contains_ofList {xs : List Nat} {x : Nat} (h : x ∈ xs) :
    (Src.NatSet.ofList xs).contains x = true := by
  unfold Src.NatSet.ofList Src.NatMap.contains Src.NatMap.ofList
  exact foldl_insert_isSome _ _ (.inr (by simp [h]))

theorem natSet_contains_insert {s : Src.NatSet} {h x : Nat} (hx : s.contains x = true) :
    (s.insert h).contains x = true := by
  unfold Src.NatSet.insert Src.NatMap.contains at *
  rw [Src.NatMap.get?_insert]
  split
  · rfl
  · exact hx

theorem globalList_ids_nodup (P : Program) : (P.globalList.map (·.1)).Nodup := by
  have hp : P.globalList.Pairwise fun p p' => p.1 < p'.1 := by
    unfold Program.globalList
    refine List.Pairwise.filterMap _ (fun a a' h b hb b' hb' => ?_) List.pairwise_lt_range
    simp only [Option.map_eq_some_iff] at hb hb'
    obtain ⟨_, _, rfl⟩ := hb
    obtain ⟨_, _, rfl⟩ := hb'
    exact h
  exact (List.pairwise_map.2 hp).imp Nat.ne_of_lt

/-! ## The keys of lifted local functions -/

/-- The keys `lam K [a + n - 1], …, lam K [a]` (newest first) of the `n`
local functions of a global keyed `K` numbered from `a`. -/
def lamKeys (K : Key.GKey) (a : Nat) : Nat → List Key.GKey
  | 0 => []
  | n + 1 => .lam K [a + n] :: lamKeys K a n

theorem lamKeys_add (K : Key.GKey) (a n : Nat) :
    ∀ m, lamKeys K a (n + m) = lamKeys K (a + n) m ++ lamKeys K a n
  | 0 => rfl
  | m + 1 => by
    show Key.GKey.lam K [a + (n + m)] :: lamKeys K a (n + m) =
      Key.GKey.lam K [a + n + m] :: (lamKeys K (a + n) m ++ lamKeys K a n)
    rw [lamKeys_add K a n m, Nat.add_assoc]

theorem mem_lamKeys {K : Key.GKey} {a : Nat} : ∀ {n : Nat} {x : Key.GKey}, x ∈ lamKeys K a n →
    ∃ i, a ≤ i ∧ i < a + n ∧ x = .lam K [i]
  | 0, _, h => absurd h List.not_mem_nil
  | n + 1, x, h => by
    rcases List.mem_cons.1 h with h | h
    · exact ⟨a + n, Nat.le_add_right _ _, by omega, h⟩
    · obtain ⟨i, h1, h2, h3⟩ := mem_lamKeys h
      exact ⟨i, h1, by omega, h3⟩

theorem lamKeys_nodup (K : Key.GKey) (a : Nat) : ∀ n, (lamKeys K a n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    refine List.nodup_cons.2 ⟨fun h => ?_, lamKeys_nodup K a n⟩
    obtain ⟨i, -, h2, h3⟩ := mem_lamKeys h
    injection h3 with _ h4
    injection h4 with h5
    omega

/-! ## What the walk collects -/

/-- What the walk does to what it collects, in a global keyed `K`: it puts
the local functions it lifts in front, keyed `lam K [i]` for the next
indices, keeps every one already there, and only adds escapes and raises
the largest arity. -/
def Grows (K : Key.GKey) (a b : Acc) : Prop :=
  ∃ n, b.next = a.next + n ∧ b.lifted.map (·.key) = lamKeys K a.next n ++ a.lifted.map (·.key) ∧
    (∀ l ∈ a.lifted, l ∈ b.lifted) ∧ (∀ h, a.escapes.contains h = true → b.escapes.contains h = true) ∧
    a.maxApp ≤ b.maxApp

theorem Grows.refl (K : Key.GKey) (a : Acc) : Grows K a a :=
  ⟨0, rfl, rfl, fun _ h => h, fun _ h => h, Nat.le_refl _⟩

theorem Grows.trans {K : Key.GKey} {a b c : Acc} (h1 : Grows K a b) (h2 : Grows K b c) : Grows K a c := by
  obtain ⟨n1, hn1, hk1, hl1, he1, hm1⟩ := h1
  obtain ⟨n2, hn2, hk2, hl2, he2, hm2⟩ := h2
  refine ⟨n1 + n2, by rw [hn2, hn1, Nat.add_assoc], ?_, fun l hl => hl2 l (hl1 l hl),
    fun h hh => he2 h (he1 h hh), Nat.le_trans hm1 hm2⟩
  rw [hk2, hk1, hn1, ← List.append_assoc, ← lamKeys_add]

mutual

theorem exp_grows {C : Ctx} : ∀ (Γ : Nat) (acc : Acc) (e : Exp) (e' : Exp) (acc' : Acc),
    Defun.exp C Γ acc e = .ok (e', acc') → Grows C.key acc acc'
  | Γ, acc, .bind c b e, e', acc', h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨e1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact (bind_grows Γ acc b b' acc1 hb).trans (exp_grows (Γ + 1) acc1 e e1 acc2 he)
  | Γ, acc, .join n r b e, e', acc', h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨e1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact (exp_grows (Γ + n) acc b b' acc1 hb).trans (exp_grows Γ acc1 e e1 acc2 he)
  | _, acc, .jump j as, e', acc', h => by
    simp only [Defun.exp] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | Γ, acc, .case x as d, e', acc', h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨as', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨d', acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact (alts_grows Γ acc as as' acc1 hb).trans (opt_grows Γ acc1 d d' acc2 he)
  | _, acc, .ret a, e', acc', h => by
    simp only [Defun.exp] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | Γ, acc, .tick e, e', acc', h => by
    simp only [Defun.exp] at h
    obtain ⟨⟨e1, acc1⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact exp_grows Γ acc e e1 acc1 he
  | _, acc, .trap, e', acc', h => by
    simp only [Defun.exp] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _

theorem bind_grows {C : Ctx} : ∀ (Γ : Nat) (acc : Acc) (b : Bind) (b' : Bind) (acc' : Acc),
    Defun.bind C Γ acc b = .ok (b', acc') → Grows C.key acc acc'
  | _, acc, .glob g, b', acc', h => by
    simp only [Defun.bind] at h
    by_cases hlt : g < C.prog.size
    · rw [ite_eq_left hlt] at h
      cases hg : C.prog.global? g with
      | some hd =>
        simp only [hg] at h
        cases hps : hd.ps with
        | nil =>
          simp only [hps] at h
          obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
          rw [← hq2]
          exact Grows.refl _ _
        | cons p ps =>
          simp only [hps] at h
          obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
          rw [← hq2]
          exact ⟨0, rfl, rfl, fun _ h => h, fun _ h => natSet_contains_insert h, Nat.le_refl _⟩
      | none =>
        simp only [hg] at h
        obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
        rw [← hq2]
        exact Grows.refl _ _
    · rw [ite_eq_right hlt] at h
      exact (throw_ok h).elim
  | _, acc, .app f as, b', acc', h => by
    simp only [Defun.bind] at h
    cases as with
    | nil =>
      obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq2]
      exact Grows.refl _ _
    | cons a as =>
      obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq2]
      exact ⟨0, rfl, rfl, fun _ h => h, fun _ h => h, Nat.le_max_left _ _⟩
  | Γ, acc, .fn ps fb, b', acc', h => by
    cases ps with
    | nil =>
      simp only [Defun.bind] at h
      exact (throw_ok h).elim
    | cons p ps =>
      simp only [Defun.bind] at h
      obtain ⟨⟨fb', acc1⟩, hb, h⟩ := bind_ok h
      dsimp only at h
      split at h
      case isFalse => exact (throw_ok h).elim
      obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
      rw [← hq2]
      obtain ⟨n, hn, hk, hl, he, hm⟩ := exp_grows _ acc fb fb' acc1 hb
      refine ⟨n + 1, by show acc1.next + 1 = acc.next + (n + 1); omega, ?_,
        fun l hl' => List.mem_cons_of_mem _ (hl l hl'), he, hm⟩
      simp only [List.map_cons, hk, hn, lamKeys, List.cons_append]
  | _, acc, .atom _, b', acc', h => by
    simp only [Defun.bind] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | _, acc, .con .., b', acc', h => by
    simp only [Defun.bind] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | _, acc, .proj .., b', acc', h => by
    simp only [Defun.bind] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | _, acc, .prim .., b', acc', h => by
    simp only [Defun.bind] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | _, acc, .call .., b', acc', h => by
    simp only [Defun.bind] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _

theorem alts_grows {C : Ctx} : ∀ (Γ : Nat) (acc : Acc) (as : List Alt) (as' : List Alt) (acc' : Acc),
    Defun.alts C Γ acc as = .ok (as', acc') → Grows C.key acc acc'
  | _, acc, [], as', acc', h => by
    simp only [Defun.alts] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | Γ, acc, .mk k n b :: as, as', acc', h => by
    simp only [Defun.alts] at h
    obtain ⟨⟨b', acc1⟩, hb, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨as1, acc2⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact (exp_grows (Γ + n) acc b b' acc1 hb).trans (alts_grows Γ acc1 as as1 acc2 he)

theorem opt_grows {C : Ctx} : ∀ (Γ : Nat) (acc : Acc) (o : Option Exp) (o' : Option Exp) (acc' : Acc),
    Defun.opt C Γ acc o = .ok (o', acc') → Grows C.key acc acc'
  | _, acc, none, o', acc', h => by
    simp only [Defun.opt] at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact Grows.refl _ _
  | Γ, acc, some e, o', acc', h => by
    simp only [Defun.opt] at h
    obtain ⟨⟨e1, acc1⟩, he, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
    rw [← hq2]
    exact exp_grows Γ acc e e1 acc1 he

end

/-- One global's walk numbers its local functions from 0. -/
theorem global_grows {P : Program} {g : GlobalId} {gd gd' : GDef} {acc acc' : Acc}
    (h : Defun.global P g gd acc = .ok (gd', acc')) : Grows gd.key { acc with next := 0 } acc' := by
  simp only [Defun.global] at h
  obtain ⟨⟨body, acc1⟩, hb, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨-, hq2⟩ := Prod.mk.inj (pure_ok h)
  rw [← hq2]
  exact exp_grows (C := { prog := P, g, key := gd.key }) _ _ _ _ _ hb

/-! ## The walk over the globals -/

theorem globalsGo_parents {P : Program} : ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId)
    (out : List (GlobalId × GDef)) {gs : List (GlobalId × GDef)} {accF : Acc} {PF : List GlobalId},
    globalsGo P l acc parents out = .ok (gs, accF, PF) →
    (∀ g ∈ parents, g ∈ PF) ∧ ∀ g ∈ PF, g ∈ parents ∨ g ∈ l.map (·.1)
  | [], _, _, _, _, _, _, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact ⟨fun _ h => h, fun _ h => .inl h⟩
  | (g, gd) :: rest, acc, parents, out, gs, accF, PF, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      obtain ⟨h1, h2⟩ := globalsGo_parents rest _ _ _ h
      refine ⟨fun x hx => h1 x (mem_ite_cons hx), fun x hx => ?_⟩
      rcases h2 x hx with hx | hx
      · by_cases hc : acc1.next > 0
        · rw [ite_eq_left hc] at hx
          rcases List.mem_cons.1 hx with hx | hx
          · exact .inr (by rw [hx]; exact List.mem_cons_self)
          · exact .inl hx
        · rw [ite_eq_right hc] at hx
          exact .inl hx
      · exact .inr (List.mem_cons_of_mem _ hx)

/-- Every lifted function so far is keyed `lam (key g) [i]` for a global `g`
among `parents`. -/
def LamFrom (P : Program) (parents : List GlobalId) (ks : List Key.GKey) : Prop :=
  ∀ k ∈ ks, ∃ g ∈ parents, ∃ gd, P.global? g = some gd ∧ ∃ i, k = .lam gd.key [i]

/-- Distinct globals among `PF` have distinct keys. -/
def KeysApart (P : Program) (PF : List GlobalId) : Prop :=
  ∀ g ∈ PF, ∀ g' ∈ PF, ∀ gd gd', P.global? g = some gd → P.global? g' = some gd' → gd.key = gd'.key → g = g'

/-- The lifted functions' keys are distinct when their parents' keys are. -/
theorem globalsGo_keys {P : Program} {PF : List GlobalId} (hD : KeysApart P PF) :
    ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId) (out : List (GlobalId × GDef))
    {gs : List (GlobalId × GDef)} {accF : Acc},
    (l.map (·.1)).Nodup → (∀ p ∈ l, P.global? p.1 = some p.2) → (∀ g ∈ parents, g ∉ l.map (·.1)) →
    (acc.lifted.map (·.key)).Nodup → LamFrom P parents (acc.lifted.map (·.key)) →
    globalsGo P l acc parents out = .ok (gs, accF, PF) →
    (accF.lifted.map (·.key)).Nodup ∧ LamFrom P PF (accF.lifted.map (·.key))
  | [], acc, parents, out, gs, accF, _, _, _, hnd, hfrom, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨hnd, hfrom⟩
  | (g, gd) :: rest, acc, parents, out, gs, accF, hl, hP, hpar, hnd, hfrom, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      have hPF := (globalsGo_parents rest _ _ _ h).1
      obtain ⟨n, hn, hk, -, -, -⟩ := global_grows hg
      have hn' : acc1.next = n := by rw [hn]; exact Nat.zero_add n
      rw [List.map_cons, List.nodup_cons] at hl
      have hgd : P.global? g = some gd := hP (g, gd) List.mem_cons_self
      have hgpar : g ∉ parents := fun hm => hpar g hm List.mem_cons_self
      have hgin : 0 < n → g ∈ (if acc1.next > 0 then g :: parents else parents) := fun hpos => by
        rw [ite_eq_left (show acc1.next > 0 by omega)]; exact List.mem_cons_self
      refine globalsGo_keys hD rest acc1 _ _ hl.2 (fun p hp => hP p (List.mem_cons_of_mem _ hp)) ?_ ?_ ?_ h
      · intro x hx hxr
        by_cases hc : acc1.next > 0
        · rw [ite_eq_left hc] at hx
          rcases List.mem_cons.1 hx with hx | hx
          · rw [hx] at hxr; exact hl.1 hxr
          · exact hpar x hx (List.mem_cons_of_mem _ hxr)
        · rw [ite_eq_right hc] at hx
          exact hpar x hx (List.mem_cons_of_mem _ hxr)
      · show (acc1.lifted.map (·.key)).Nodup
        rw [hk, List.nodup_append]
        refine ⟨lamKeys_nodup _ _ _, hnd, fun a ha b hb hab => ?_⟩
        obtain ⟨i, -, hi, rfl⟩ := mem_lamKeys ha
        obtain ⟨g'', hg'', gd'', hgd'', i'', rfl⟩ := hfrom b hb
        injection hab with hkey _
        have := hD g (hPF g (hgin (by omega))) g'' (hPF g'' (mem_ite_cons hg'')) gd gd'' hgd hgd'' hkey
        exact hgpar (by rw [this]; exact hg'')
      · intro k hk'
        rw [hk] at hk'
        rcases List.mem_append.1 hk' with hk' | hk'
        · obtain ⟨i, -, hi, rfl⟩ := mem_lamKeys hk'
          exact ⟨g, hgin (by omega), gd, hgd, i, rfl⟩
        · obtain ⟨g'', hg'', gd'', hgd'', i, rfl⟩ := hfrom k hk'
          exact ⟨g'', mem_ite_cons hg'', gd'', hgd'', i, rfl⟩

/-! ## A successful run -/

/-- What a successful run is made of: the input checks, the walk over the
globals, and the checks on the sources. -/
structure Ran (P : Program) (gs : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId) : Prop where
  input : checkInput P = .ok ()
  walk : globalsGo P P.globalList {} [] [] = .ok (gs, acc, parents)
  sources : checkSources P acc parents = .ok ()

theorem run_ran {P Q : Program} (h : run P = .ok Q) :
    ∃ gs acc parents, Ran P gs acc parents ∧ Q = assemble P gs acc := by
  simp only [run] at h
  obtain ⟨u, hin, h⟩ := bind_ok h
  obtain ⟨⟨gs, acc, parents⟩, hgo, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨u', hcs, h⟩ := bind_ok h
  cases u
  cases u'
  exact ⟨gs, acc, parents, ⟨hin, hgo, hcs⟩, (pure_ok h).symm⟩

/-- The input checks: no global keyed as P8 keys them, no closure key in the
table or among the pinned constructors. -/
theorem checkInput_ok {P : Program} (h : checkInput P = .ok ()) :
    (∀ p ∈ P.globalList, reservedKey p.2.key = false) ∧ (∀ r ∈ P.ctors, closureKey r.key = false) ∧
      knownClosure P.known = false := by
  unfold checkInput at h
  cases hf : P.globalList.find? (fun (_, gd) => reservedKey gd.key) with
  | some p =>
    obtain ⟨g, gd⟩ := p
    simp only [hf] at h
    obtain ⟨_, h, -⟩ := bind_ok h
    exact (throw_ok h).elim
  | none =>
    simp only [hf] at h
    cases hc : (P.ctors.any (fun r => closureKey r.key) || knownClosure P.known) with
    | true =>
      simp only [hc, ↓reduceIte] at h
      obtain ⟨_, h, -⟩ := bind_ok h
      exact (throw_ok h).elim
    | false =>
      rw [Bool.or_eq_false_iff] at hc
      refine ⟨fun p hp => ?_, fun r hr => ?_, hc.2⟩
      · have := List.find?_eq_none.1 hf p hp
        simpa using this
      · have := List.any_eq_false.1 hc.1 r hr
        simpa using this

theorem ran_parents {P : Program} {gs acc parents} (hr : Ran P gs acc parents) :
    ∀ g ∈ parents, g < P.size ∧ ∃ gd, P.global? g = some gd := by
  intro g hg
  rcases (globalsGo_parents _ _ _ _ hr.walk).2 g hg with h | h
  · exact absurd h List.not_mem_nil
  · obtain ⟨⟨g', gd⟩, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨hlt, hgd⟩ := mem_globalList.1 hm
    exact ⟨hlt, gd, hgd⟩

theorem mem_ownerKeys {P : Program} {acc : Acc} {parents : List GlobalId} {x : GlobalId} {y : GDef}
    (hx : x < P.size) (hown : x ∈ (escapeSources P acc).map (·.id) ++ parents) (hy : P.global? x = some y) :
    (y.key, x) ∈ ownerKeys P acc parents := by
  unfold ownerKeys
  dsimp only
  refine List.mem_filterMap.2 ⟨x, List.mem_range.2 hx, ?_⟩
  rw [ite_eq_left (natSet_contains_ofList hown), hy]
  rfl

theorem ran_keysApart {P : Program} {gs acc parents} (hr : Ran P gs acc parents) : KeysApart P parents := by
  intro g hg g' hg' gd gd' hgd hgd' hk
  have h1 := mem_ownerKeys (acc := acc) (ran_parents hr g hg).1 (List.mem_append_right _ hg) hgd
  have h2 := mem_ownerKeys (acc := acc) (ran_parents hr g' hg').1 (List.mem_append_right _ hg') hgd'
  exact (Prod.mk.inj (eq_of_nodup_map (checkSources_ownerKeys hr.sources) h1 h2 hk)).2

/-- The lifted functions' keys are distinct. -/
theorem ran_lifted_keys {P : Program} {gs acc parents} (hr : Ran P gs acc parents) :
    (acc.lifted.map (·.key)).Nodup ∧ LamFrom P parents (acc.lifted.map (·.key)) :=
  globalsGo_keys (ran_keysApart hr) P.globalList ({} : Acc) [] [] (globalList_ids_nodup P)
    (fun _ hp => (mem_globalList.1 hp).2) (fun _ h => absurd h List.not_mem_nil) List.nodup_nil
    (fun _ h => absurd h List.not_mem_nil) hr.walk

theorem escape_sublist {P : Program} {acc : Acc} {parents : List GlobalId} :
    ((escapeSources P acc).map fun s => (s.key, s.id)).Sublist (ownerKeys P acc parents) := by
  unfold escapeSources ownerKeys
  dsimp only
  rw [List.map_filterMap]
  refine filterMap_sublist _ fun h hh p hp => ?_
  by_cases he : acc.escapes.contains h = true
  · rw [ite_eq_left he] at hp
    cases hg : P.global? h with
    | none => rw [hg] at hp; cases hp
    | some hd =>
      rw [hg] at hp
      have hp' : (hd.key, h) = p := Option.some.inj hp
      have hown : h ∈ (escapeSources P acc).map (·.id) ++ parents := by
        unfold escapeSources
        refine List.mem_append_left _ (List.mem_map.2 ⟨{ key := hd.key, id := h, caps := 0, arity := hd.ps.length },
          List.mem_filterMap.2 ⟨h, hh, ?_⟩, rfl⟩)
        rw [ite_eq_left he, hg]
        rfl
      rw [ite_eq_left (natSet_contains_ofList hown), ← hp']
      rfl
  · rw [ite_eq_right he] at hp
    cases hp

theorem numbered_map_key {f : GlobalId × Lifted → Source} (hf : ∀ i l, (f (i, l)).key = l.key) :
    ∀ (k : Nat) (xs : List Lifted), ((numbered k xs).map f).map (·.key) = xs.map (·.key)
  | _, [] => rfl
  | k, x :: xs => by
    simp only [numbered, List.map_cons, hf, numbered_map_key hf (k + 1) xs]

theorem sources_keys_eq (P : Program) (acc : Acc) :
    (sources P acc).map (·.key) = (escapeSources P acc).map (·.key) ++ (acc.lifted.map (·.key)).reverse := by
  unfold sources liftedAt
  rw [List.map_append, numbered_map_key (fun _ _ => rfl), List.map_reverse]

/-- **The closure sources' keys are distinct**: the escaping globals' keys by
the key check, the lifted functions' by their parents' keys and their
indices, and the two apart because no input global is keyed `lam`. -/
theorem sources_keys {P : Program} {gs acc parents} (hr : Ran P gs acc parents) :
    ((sources P acc).map (·.key)).Nodup := by
  have hesc : ((escapeSources P acc).map (·.key)).Nodup := by
    have := (escape_sublist (P := P) (acc := acc) (parents := parents)).map (·.1)
    rw [List.map_map] at this
    exact this.nodup (checkSources_ownerKeys hr.sources)
  obtain ⟨hlift, hfrom⟩ := ran_lifted_keys hr
  have hres := (checkInput_ok hr.input).1
  rw [sources_keys_eq, List.nodup_append]
  refine ⟨hesc, (List.reverse_perm _).nodup_iff.2 hlift, fun a ha b hb hab => ?_⟩
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
  obtain ⟨g, -, gd, -, i, rfl⟩ := hfrom b (List.mem_reverse.1 hb)
  unfold escapeSources at hs
  obtain ⟨h, hh, hsh⟩ := List.mem_filterMap.1 hs
  by_cases he : acc.escapes.contains h = true
  · rw [ite_eq_left he] at hsh
    cases hg : P.global? h with
    | none => rw [hg] at hsh; cases hsh
    | some hd =>
      rw [hg] at hsh
      cases hsh
      have := hres (h, hd) (mem_globalList.2 ⟨List.mem_range.1 hh, hg⟩)
      dsimp only at hab this
      rw [hab] at this
      cases this
  · rw [ite_eq_right he] at hsh
    cases hsh

end IxCC.Anf.Defun.Proof
